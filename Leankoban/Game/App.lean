import Leankoban.Engine
import Leankoban.Levels.Data
import Leankoban.Game.Render
import Leankoban.Game.Input

/-!
# ゲーム本体

移動の判定には `Engine.step` をそのまま使う。この関数は `Soundness.step_sound` と
`Soundness.step_complete` により仕様 `Spec.Step` と完全に一致することが証明されている。
また、盤面データは証明が言及するのと同じ定数 `Levels.all` から読む。
-/

namespace Leankoban.Game

open Engine

/-- プレイ中の状態。 -/
structure Session where
  levels   : Array (List String)
  idx      : Nat                     -- 0 始まりの面番号
  rows     : List String
  level    : Level
  inner    : List Pos
  state    : State
  history  : List (State × Nat)      -- 直前までの局面と、その時点の押し数
  pushes   : Nat
  cleared  : List Nat                -- クリア済みの面番号（1 始まり）
  message  : String

namespace Session

def moves (s : Session) : Nat := s.history.length

def solved (s : Session) : Bool := isSolved s.level s.state

/-- `idx` 番目の面を読み込む。 -/
def load (levels : Array (List String)) (idx : Nat) (cleared : List Nat) (message := "") : Session :=
  let rows := levels[idx]?.getD []
  let L := Level.ofRows rows
  { levels, idx, rows, level := L, inner := Game.interior L, state := L.init,
    history := [], pushes := 0, cleared, message }

/-- 操作を 1 つ適用する。 -/
def apply (s : Session) : Cmd → Session
  | .move d =>
    if s.solved then s
    else
      match step s.level s.state d with
      | none => { s with message := "" }
      | some st =>
        let p := if Engine.pushes s.state d then s.pushes + 1 else s.pushes
        { s with state := st, history := (s.state, s.pushes) :: s.history, pushes := p, message := "" }
  | .undo =>
    match s.history with
    | [] => { s with message := "これ以上戻せません" }
    | (st, p) :: rest => { s with state := st, history := rest, pushes := p, message := "" }
  | .restart => load s.levels s.idx s.cleared "やり直し"
  | .next =>
    if s.idx + 1 < s.levels.size then load s.levels (s.idx + 1) s.cleared
    else { s with message := "最後の面です" }
  | .prev =>
    if s.idx > 0 then load s.levels (s.idx - 1) s.cleared
    else { s with message := "最初の面です" }
  | .goto n =>
    if 1 ≤ n && n ≤ s.levels.size then load s.levels (n - 1) s.cleared
    else { s with message := s!"面番号は 1〜{s.levels.size} です" }
  | .help => { s with message := "help" }
  | .quit => s

end Session

/-! ## 進捗の保存 -/

def progressPath : IO (Option System.FilePath) := do
  match ← IO.getEnv "HOME" with
  | some home => return some (System.FilePath.mk home / ".leankoban" / "progress")
  | none => return none

def loadProgress : IO (List Nat) := do
  try
    let some path ← progressPath | return []
    let text ← IO.FS.readFile path
    return (text.split (fun c => c == ' ' || c == '\n')).toList.filterMap (·.toString.toNat?)
  catch _ => return []

def saveProgress (cleared : List Nat) : IO Unit := do
  try
    let some path ← progressPath | return
    if let some dir := path.parent then IO.FS.createDirAll dir
    IO.FS.writeFile path (" ".intercalate (cleared.map toString) ++ "\n")
  catch _ => return

/-! ## 画面 -/

def helpText : String :=
  "移動: 矢印 / WASD / hjkl   u,z: 1手戻す   r: やり直し   n/p: 次/前の面   g: 面番号へ   ?: ヘルプ   q: 終了"

def lineHelpText : String :=
  "line モード: キーを並べて Enter（例: ddss）。:rrDDlu のように : で始めると LURD 記法。g12 で 12 面へ。q で終了。"

def screen (plain line : Bool) (s : Session) : String :=
  let total := s.levels.size
  let num := s.idx + 1
  let mark := if s.cleared.contains num then " [クリア済]" else ""
  let header := s!"Leankoban  面 {num}/{total}{mark}   手数 {s.moves}   押し {s.pushes}   クリア {s.cleared.length}/{total}"
  let board := renderBoard plain s.rows s.level s.inner s.state
  let status :=
    if s.solved then
      if num < total then "*** クリア！ n で次の面へ ***" else "*** クリア！ 全 100 面の最後の面です ***"
    else if s.message == "help" then (if line then lineHelpText else helpText)
    else s.message
  let clear := if plain then "" else "\x1b[2J\x1b[H"
  s!"{clear}{header}\n\n{board}\n\n{status}\n{if line then lineHelpText else helpText}\n"

/-! ## メインループ -/

/-- クリアした面を記録する。 -/
def recordClear (s : Session) : IO Session := do
  let num := s.idx + 1
  if s.solved && !s.cleared.contains num then
    let cleared := (num :: s.cleared).mergeSort (· ≤ ·)
    saveProgress cleared
    return { s with cleared }
  else return s

partial def rawLoop (stdin stdout : IO.FS.Stream) (plain : Bool) (s : Session) : IO Unit := do
  stdout.putStr (screen plain false s); stdout.flush
  let cmd ← readRawCmd stdin stdout
  match cmd with
  | .quit => return
  | c =>
    let s ← recordClear (s.apply c)
    rawLoop stdin stdout plain s

partial def lineLoop (stdin stdout : IO.FS.Stream) (plain : Bool) (s : Session) : IO Unit := do
  stdout.putStr (screen plain true s)
  stdout.putStr "> "; stdout.flush
  let line ← stdin.getLine
  if line.isEmpty then return  -- 入力の終わり
  let cmds := parseLine line
  if cmds.any (fun c => match c with | .quit => true | _ => false) then return
  let mut s := s
  for c in cmds do
    s ← recordClear (s.apply c)
  lineLoop stdin stdout plain s

/-! ## raw モードの後始末 -/

def hideCursor : String := "\x1b[?25l"
def showCursor : String := "\x1b[?25h\n"

/-- 標準エラーに 1 行書く。標準エラーにも書けなければ諦める。 -/
def warn (msg : String) : IO Unit :=
  try IO.eprintln msg catch _ => pure ()

/-- `act` を実行し、失敗したらその例外を返す（ここでは投げない）。 -/
def attempt (act : IO Unit) : IO (Option IO.Error) :=
  try act; return none catch e => return some e

/-- raw モードにした端末で `body` を実行し、終わったら、失敗したときも含めて必ず端末を元に戻す。

* 端末設定の復元 `restore` は、画面への出力より先に、出力の成否とは無関係に実行する。
  標準出力への書込みや flush が失敗しても、端末が非カノニカル・エコーなしのまま残らない。
* `body` や出力の失敗は、端末を戻してカーソルの再表示を試みた後で、例外として投げ直す。
* 復元自体の失敗は、出力の失敗とは別に標準エラーへ報告し（`stty sane` での回復を案内する）、
  終了コードを 1 にする。 -/
def withRawMode (stdout : IO.FS.Stream) (restore : IO Bool) (body : IO Unit) : IO UInt32 := do
  let failed ← attempt do
    stdout.putStr hideCursor
    body
  let restored ← try restore catch _ => pure false
  -- 出力先が壊れていればここも失敗するが、端末の設定はもう戻してある
  let failedShow ← attempt do
    stdout.putStr showCursor
    stdout.flush
  unless restored do
    warn "leankoban: 端末の設定を元に戻せませんでした。`stty sane` を実行すると戻ります。"
  if let some e := failed <|> failedShow then throw e
  return if restored then 0 else 1

def usage : String :=
  "使い方: leankoban [面番号] [--line] [--plain]\n" ++
  "  面番号   1〜100（省略時は未クリアの最初の面）\n" ++
  "  --line   行入力モード（Enter で確定。端末を raw モードにしない）\n" ++
  "  --plain  色を使わず XSB 形式の文字で描く\n"

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  if args.contains "--help" || args.contains "-h" then
    stdout.putStr usage
    return 0
  let levels := Levels.all.toArray
  if levels.isEmpty then
    IO.eprintln "盤面データがありません"
    return 1
  let plain := args.contains "--plain"
  let cleared ← loadProgress
  let firstOpen := ((List.range levels.size).find? fun i => !cleared.contains (i + 1)).getD 0
  let idx := match args.findSome? String.toNat? with
    | some n => if 1 ≤ n && n ≤ levels.size then n - 1 else firstOpen
    | none => firstOpen
  let s := Session.load levels idx cleared
  let tty ← stdin.isTty
  if args.contains "--line" || !tty then
    lineLoop stdin stdout plain s
    return 0
  match ← enterRaw with
  | none =>
    lineLoop stdin stdout plain s
    return 0
  | some saved => withRawMode stdout (leaveRaw saved) (rawLoop stdin stdout plain s)

end Leankoban.Game
