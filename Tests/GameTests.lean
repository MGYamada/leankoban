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

end Leankoban.Tests.Game
