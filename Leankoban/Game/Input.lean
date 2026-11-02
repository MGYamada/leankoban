import Leankoban.Spec

/-!
# 入力

* raw モード：1 キーごとに反応する。Lean には termios の API がないため、
  `stty` コマンドで端末を非カノニカル・エコーなしに切り替える（このゲームが使う唯一の外部コマンド）。
* line モード：1 行ずつ読む（Lean だけで動く）。`ddss` のように複数のキーをまとめて入力できる。
  `:` で始まる行は LURD 記法の手順として扱う（例：`:rrDDlu`）。
-/

namespace Leankoban.Game

/-- プレイヤーの操作。 -/
inductive Cmd where
  | move (d : Dir)
  | undo
  | restart
  | next
  | prev
  | goto (n : Nat)
  | help
  | quit
  deriving Repr, Inhabited, BEq

/-- 1 キー（ASCII バイト）を操作に変換する。
移動は WASD / hjkl（矢印キーは raw モードで別途処理する）。 -/
def cmdOfKey (b : UInt8) : Option Cmd :=
  match Char.ofNat b.toNat with
  | 'w' | 'k' | 'W' | 'K' => some (.move .U)
  | 's' | 'j' | 'S' | 'J' => some (.move .D)
  | 'a' | 'h' | 'A' | 'H' => some (.move .L)
  | 'd' | 'l' | 'D' | 'L' => some (.move .R)
  | 'u' | 'z' | 'U' | 'Z' => some .undo
  | 'r' | 'R' => some .restart
  | 'n' | 'N' => some .next
  | 'p' | 'P' => some .prev
  | '?' => some .help
  | 'q' | 'Q' => some .quit
  | _ => none

/-- LURD 記法の 1 文字を移動に変換する。 -/
def cmdOfLurd (c : Char) : Option Cmd :=
  match c with
  | 'u' | 'U' => some (.move .U)
  | 'd' | 'D' => some (.move .D)
  | 'l' | 'L' => some (.move .L)
  | 'r' | 'R' => some (.move .R)
  | _ => none

/-- line モードの 1 行を操作の列に変換する。 -/
def parseLine (line : String) : List Cmd :=
  let line := line.trimAscii.toString
  if line.startsWith ":" then
    (line.drop 1).toString.toList.filterMap cmdOfLurd
  else if line.startsWith "g" || line.startsWith "G" then
    match (line.drop 1).trimAscii.toNat? with
    | some n => [.goto n]
    | none => []
  else
    line.toUTF8.data.toList.filterMap cmdOfKey

/-! ## 端末の raw モード -/

/-- `stty` を実行する。標準入力は端末を引き継ぐ（`IO.Process.output` は stdin を閉じてしまうので使わない）。 -/
def stty (args : Array String) : IO (Option String) := do
  try
    let child ← IO.Process.spawn
      { cmd := "stty", args := args, stdin := .inherit, stdout := .piped, stderr := .null }
    let out ← child.stdout.readToEnd
    let code ← child.wait
    return if code == 0 then some out.trimAscii.toString else none
  catch _ =>
    return none

/-- raw モードに入る。成功したら、元に戻すための設定文字列を返す。

`-isig` で Ctrl-C / Ctrl-\ / Ctrl-Z によるシグナルの発生を止め、ただのバイトとして読む。
シグナルで終了すると `main` の `finally` が走らず、端末が raw モードのまま残ってしまうため、
これらのキーは `isQuitKey` で受けて、通常の終了処理（端末設定の復元）を通す。 -/
def enterRaw : IO (Option String) := do
  let some saved ← stty #["-g"] | return none
  let some _ ← stty #["-icanon", "-echo", "-isig", "min", "1", "time", "0"] | return none
  return some saved

/-- 端末の設定を元に戻す。戻せたら `true`。 -/
def leaveRaw (saved : String) : IO Bool :=
  return (← stty #[saved]).isSome

/-- 終了として扱う制御キー：Ctrl-C（3）、Ctrl-D（4）、Ctrl-\（28）。 -/
def isQuitKey (b : UInt8) : Bool :=
  b.toNat == 3 || b.toNat == 4 || b.toNat == 28

/-- 1 バイト読む。入力の終わりなら `none`。 -/
def readByte (stdin : IO.FS.Stream) : IO (Option UInt8) := do
  let bs ← stdin.read 1
  return bs.data[0]?

/-! ## エスケープ列

矢印キーなどは `ESC [ A`（CSI）や `ESC O A`（SS3）のようなバイト列で届く。1 バイトずつ読み、
次の状態機械で解釈する。状態を持ち越すので、列が何回かの読み込みに分かれて届いても壊れない。

* `ESC [` または `ESC O` の後は、パラメータ・中間バイト（0x20〜0x3F）を読み飛ばし、
  終端バイト（0x40〜0x7E）で列を閉じる。終端が `A`〜`D` なら矢印（`ESC [1;5A` のような修飾付きも含む）。
  それ以外の列（Home、Delete、F キーなど）は、列全体を読み捨てる。
* 列の途中で列に属さないバイト（Ctrl-C などの制御文字、新しい ESC など）が来たら、そこで列を打ち切り、
  そのバイトを通常の入力として処理し直す。`ESC` の次が `[` `O` 以外のときも同じ。
  単独の Esc は何もしない操作なので、その後の `q` や Ctrl-C は 1 回で効く。

待ち時間（タイムアウト）は設けない。単独の Esc は何もしないので、次のバイトが来るまで判定を保留しても
見た目は変わらないからである。その代わり、Esc の直後に手で打った `[` / `O` は、エスケープ列の始まりとして読む。
-/

/-- エスケープ列の読み取り状態。 -/
inductive EscState where
  | ground  -- 列の外
  | esc     -- `ESC` を読んだ
  | seq     -- `ESC [` か `ESC O` を読み、終端バイトを待っている
  deriving BEq, Repr, Inhabited

/-- 1 バイトを読んだ結果。 -/
inductive Decoded where
  | more (st : EscState)  -- 列の途中。次のバイトを読む
  | key (b : UInt8)       -- 通常のキー（制御文字を含む）
  | arrow (d : Dir)       -- 矢印キー
  | ignored               -- 矢印以外のキーの列（列全体を読み捨てた）
  deriving BEq, Repr

/-- 列の外でバイト `b` を読む。 -/
def decodeGround (b : UInt8) : Decoded :=
  if b.toNat == 27 then .more .esc else .key b

/-- 状態 `st` でバイト `b` を読む。 -/
def decodeByte (st : EscState) (b : UInt8) : Decoded :=
  let n := b.toNat
  match st with
  | .ground => decodeGround b
  | .esc => if n == 91 || n == 79 then .more .seq else decodeGround b  -- '[' または 'O'
  | .seq =>
    if 0x20 ≤ n && n ≤ 0x3F then .more .seq
    else if 0x40 ≤ n && n ≤ 0x7E then
      match n with
      | 65 => .arrow .U  -- 'A'
      | 66 => .arrow .D  -- 'B'
      | 67 => .arrow .R  -- 'C'
      | 68 => .arrow .L  -- 'D'
      | _ => .ignored
    else decodeGround b

/-! ## raw モードの入力 -/

/-- 面番号の入力結果。 -/
inductive NumberInput where
  | num (n : Nat)
  | cancel  -- 数字を入れずに Enter
  | escape  -- Esc で取消。ESC の後に続くバイトは、エスケープ列として読む
  | quit

/-- raw モードで数字の列を読む（`g` で面番号を指定するとき用）。
Enter で確定、Esc で取消、Ctrl-C などで終了。 -/
partial def readNumber (stdin stdout : IO.FS.Stream) (acc : String := "") : IO NumberInput := do
  let finish (s : String) : NumberInput := match s.toNat? with
    | some n => .num n
    | none => .cancel
  let some b ← readByte stdin | return .quit
  let n := b.toNat
  if isQuitKey b then return .quit
  else if n == 10 || n == 13 then return finish acc
  else if n == 27 then return .escape
  else if n == 127 || n == 8 then
    if acc.isEmpty then readNumber stdin stdout acc
    else
      stdout.putStr "\x08 \x08"; stdout.flush
      readNumber stdin stdout (acc.dropEnd 1).toString
  else if 48 ≤ n && n ≤ 57 then
    let c := Char.ofNat n
    stdout.putStr c.toString; stdout.flush
    readNumber stdin stdout (acc.push c)
  else readNumber stdin stdout acc

/-- raw モードで 1 操作を読む。`st` はエスケープ列の読み取り状態。
入力の終わりは、エスケープ列の途中であっても終了として扱う。 -/
partial def readRawCmd (stdin stdout : IO.FS.Stream) (st : EscState := .ground) : IO Cmd := do
  let some b ← readByte stdin | return .quit
  match decodeByte st b with
  | .more st => readRawCmd stdin stdout st
  | .arrow d => return .move d
  | .ignored => readRawCmd stdin stdout
  | .key k =>
    if isQuitKey k then return .quit
    else if k.toNat == 103 || k.toNat == 71 then  -- 'g'
      stdout.putStr "\n面番号: "; stdout.flush
      match ← readNumber stdin stdout with
      | .num n => return .goto n
      | .cancel => readRawCmd stdin stdout
      -- 矢印キーも ESC で始まるので、取り消した後は列の残りを読む（矢印なら、そのまま移動になる）
      | .escape => readRawCmd stdin stdout .esc
      | .quit => return .quit
    else
      match cmdOfKey k with
      | some c => return c
      | none => readRawCmd stdin stdout

end Leankoban.Game
