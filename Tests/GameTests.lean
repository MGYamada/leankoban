import Leankoban.Game.App

/-!
# ゲームの入力処理と後始末のテスト

`#guard` と、失敗すると例外を投げる `#eval` はビルド時に評価され、失敗するとビルドが止まる。
端末そのもの（`stty`）は使わず、メモリ上のストリームや、失敗するストリームを差し込んで調べる。
-/

namespace Leankoban.Tests.Game

open Leankoban Game

/-- `ok` でなければ例外を投げる。`#eval` の中で失敗すると、ビルドが止まる。 -/
def expect (what : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"テスト失敗: {what}")

/-! ## raw モードの後始末：出力が失敗しても端末を戻す -/

/-- 出力の試みを `log` に順に記録する標準出力。`putFails` なら書込みが、`flushFails` なら flush が失敗する。 -/
def recordingOut (log : IO.Ref (List String)) (putFails flushFails : Bool) : IO.FS.Stream where
  flush := do
    log.modify (· ++ ["flush"])
    if flushFails then throw (IO.userError "flush に失敗")
  read _ := pure .empty
  write _ := pure ()
  getLine := pure ""
  putStr s := do
    log.modify (· ++ [s])
    if putFails then throw (IO.userError "書込みに失敗")
  isTty := pure false

/-- `withRawMode` を実行し、出力と端末の復元が起きた順序、結果、標準エラーへの出力を返す。
`body` には、画面を描くときと同じ「書いて flush する」処理などを渡す。 -/
def runCleanup (putFails flushFails restoreOk : Bool) (body : IO.FS.Stream → IO Unit) :
    IO (List String × Except IO.Error UInt32 × String) := do
  let log ← IO.mkRef []
  let out := recordingOut log putFails flushFails
  let restore := do log.modify (· ++ ["restore"]); return restoreOk
  let (err, r) ← IO.FS.withIsolatedStreams (withRawMode out restore (body out)).toBaseIO
  return (← log.get, r, err)

/-- 画面を 1 回描く（`rawLoop` と同じく、書いてから flush する）。 -/
def draw (out : IO.FS.Stream) : IO Unit := do
  out.putStr "画面"; out.flush

def mentionsStty (err : String) : Bool := (err.splitOn "stty sane").length > 1

-- 正常な終了（q・Ctrl-C・入力の終わりは、どれも本体が正常に戻る）：端末を戻してからカーソルを再表示する
#eval do
  let (log, r, err) ← runCleanup false false true draw
  expect "正常終了" <| log == [hideCursor, "画面", "flush", "restore", showCursor, "flush"] &&
    r matches .ok 0 && err.isEmpty

-- 書込みはできても flush で失敗する（読み手のいないパイプなど）：それでも端末は戻し、失敗は投げ直す
#eval do
  let (log, r, err) ← runCleanup false true true draw
  expect "flush の失敗" <| log == [hideCursor, "画面", "flush", "restore", showCursor, "flush"] &&
    r matches .error _ && err.isEmpty

-- 書込みも失敗する：本体は動かないが、端末は戻す
#eval do
  let (log, r, _) ← runCleanup true true true draw
  expect "書込みの失敗" <| log == [hideCursor, "restore", showCursor] && r matches .error _

-- 出力以外の失敗でも端末は戻す
#eval do
  let (log, r, _) ← runCleanup false false true fun _ => throw (IO.userError "本体の失敗")
  expect "本体の失敗" <| log == [hideCursor, "restore", showCursor, "flush"] && r matches .error _

-- 復元そのものの失敗は、出力の失敗とは別に報告し、終了コード 1 にする
#eval do
  let (_, r, err) ← runCleanup false false false draw
  expect "復元の失敗" <| r matches .ok 1 && mentionsStty err

-- 復元の失敗と出力の失敗が重なったら、両方を報告する（前者は標準エラー、後者は例外）
#eval do
  let (_, r, err) ← runCleanup false true false draw
  expect "復元と出力の失敗" <| r matches .error _ && mentionsStty err

/-! ## raw モードのキー入力 -/

/-- `readRawCmd` で操作を読み、`quit` が出るまで集める（`fuel` 回まで）。 -/
def collectCmds (stdin stdout : IO.FS.Stream) : Nat → IO (List Cmd)
  | 0 => return []
  | fuel + 1 => do
    let c ← readRawCmd stdin stdout
    if c == .quit then return [c] else return c :: (← collectCmds stdin stdout fuel)

/-- 文字列のバイト列を raw モードの入力として与え、読めた操作の列を返す。入力の終わりは `quit` になる。 -/
def rawCmds (input : String) : IO (List Cmd) := do
  let inBuf ← IO.mkRef ({ data := input.toUTF8 } : IO.FS.Stream.Buffer)
  let outBuf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  -- 1 操作は 1 バイト以上を読むか、入力の終わりで quit になるので、バイト数 + 1 回で必ず止まる
  collectCmds (.ofBuffer inBuf) (.ofBuffer outBuf) (input.toUTF8.size + 1)

def expectRaw (input : String) (expected : List Cmd) : IO Unit := do
  let got ← rawCmds input
  expect s!"raw 入力 {repr input} → {repr got}（期待 {repr expected}）" (got == expected)

-- 矢印キー（CSI / SS3）と WASD
#eval expectRaw "\x1b[A\x1b[B\x1b[C\x1b[D" [.move .U, .move .D, .move .R, .move .L, .quit]
#eval expectRaw "\x1bOA\x1bOB\x1bOC\x1bOD" [.move .U, .move .D, .move .R, .move .L, .quit]
#eval expectRaw "wasd" [.move .U, .move .L, .move .D, .move .R, .quit]
-- 修飾付きの矢印（Ctrl+← = ESC [1;5D）は列全体で 1 つの矢印。末尾の D が右移動に化けない
#eval expectRaw "\x1b[1;5D" [.move .L, .quit]
-- 矢印以外のキーの列（Delete、Home、F5、F1）は列全体を読み捨て、後ろのキーは効く
#eval expectRaw "\x1b[3~\x1b[H\x1b[15~\x1bOPa" [.move .L, .quit]

-- 単独の Esc の後の通常キー・終了キーは、そのまま 1 回で効く
#eval expectRaw "\x1bqa" [.quit]                -- Esc → q
#eval expectRaw "\x1b\x03a" [.quit]             -- Esc → Ctrl-C
#eval expectRaw "\x1b\x1ca" [.quit]             -- Esc → Ctrl-\
#eval expectRaw "\x1ba" [.move .L, .quit]       -- Esc → a は左へ 1 手
#eval expectRaw "\x1b\x1b[A" [.move .U, .quit]  -- Esc → 矢印

-- 未完成のエスケープ列の途中で終了キーを押したら、列を打ち切って終了する
#eval expectRaw "\x1b[\x03a" [.quit]
#eval expectRaw "\x1b[1;\x03a" [.quit]
#eval expectRaw "\x1bO\x04a" [.quit]
-- 未完成の列の途中に新しい ESC が来たら、そこから読み直す
#eval expectRaw "\x1b[1\x1b[B" [.move .D, .quit]

-- 入力の終わりは、エスケープ列の途中でも終了
#eval expectRaw "" [.quit]
#eval expectRaw "\x1b" [.quit]
#eval expectRaw "\x1b[" [.quit]
#eval expectRaw "\x1b[1;5" [.quit]

-- g：面番号の入力
#eval expectRaw "g12\r" [.goto 12, .quit]
#eval expectRaw "g\ra" [.move .L, .quit]                    -- 数字なしの Enter は取消
#eval expectRaw "g1\x03a" [.quit]                           -- 入力中の Ctrl-C は終了
#eval expectRaw "g1\x1bq" [.quit]                           -- Esc で取り消し、q で終了
#eval expectRaw "g1\x1bda" [.move .R, .move .L, .quit]      -- Esc で取り消した後のキーは効く
#eval expectRaw "g1\x1b[Aa" [.move .U, .move .L, .quit]     -- 矢印で取り消すと、その矢印で動く

end Leankoban.Tests.Game
