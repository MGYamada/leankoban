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
  deriving Repr, Inhabited

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

/-- 端末の設定を元に戻す。 -/
def leaveRaw (saved : String) : IO Unit := do
  let _ ← stty #[saved]

/-- 終了として扱う制御キー：Ctrl-C（3）、Ctrl-D（4）、Ctrl-\（28）。 -/
def isQuitKey (b : UInt8) : Bool :=
  b.toNat == 3 || b.toNat == 4 || b.toNat == 28

/-- 1 バイト読む。入力の終わりなら `none`。 -/
def readByte (stdin : IO.FS.Stream) : IO (Option UInt8) := do
  let bs ← stdin.read 1
  return bs.data[0]?

/-- 面番号の入力結果。 -/
inductive NumberInput where
  | num (n : Nat)
  | cancel
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
  else if n == 27 then return .cancel
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

/-- raw モードで 1 操作を読む。矢印キーは `ESC [ A` などの 3 バイトで届く。 -/
partial def readRawCmd (stdin stdout : IO.FS.Stream) : IO Cmd := do
  let some b ← readByte stdin | return .quit
  if isQuitKey b then return .quit
  if b.toNat == 27 then
    let some b1 ← readByte stdin | return .quit
    if b1.toNat == 91 || b1.toNat == 79 then  -- '[' または 'O'
      let some b2 ← readByte stdin | return .quit
      match b2.toNat with
      | 65 => return .move .U
      | 66 => return .move .D
      | 67 => return .move .R
      | 68 => return .move .L
      | _ => readRawCmd stdin stdout
    else readRawCmd stdin stdout
  else if b.toNat == 103 || b.toNat == 71 then  -- 'g'
    stdout.putStr "\n面番号: "; stdout.flush
    match ← readNumber stdin stdout with
    | .num n => return .goto n
    | .cancel => readRawCmd stdin stdout
    | .quit => return .quit
  else
    match cmdOfKey b with
    | some c => return c
    | none => readRawCmd stdin stdout

end Leankoban.Game
