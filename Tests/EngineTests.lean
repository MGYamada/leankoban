import Leankoban.Engine
import Leankoban.Soundness
import Leankoban.Game.App

/-!
# 実行系とゲームの単体テスト

`#guard` はビルド時に評価され、失敗するとビルドが止まる。
-/

namespace Leankoban.Tests

open Leankoban Engine

/-- テスト用の小さな盤面。 -/
def room : List String := [
  "#######",
  "#  .  #",
  "# $$  #",
  "#@ $ .#",
  "#.  ###",
  "#####"]

def L : Level := Level.ofRows room

-- 読み込み：床・ゴール・箱・人
#guard L.goals.length == 3
#guard L.boxes.length == 3
#guard L.player == (3, 1)
#guard mem (1, 1) L.floor && !mem (0, 0) L.floor && !mem (5, 5) L.floor
#guard wellFormed L

-- 歩く・押す・止まる
#guard (step L L.init .U).map (·.player) == some (2, 1)
#guard (step L L.init .L).isNone                                  -- 壁
#guard (step L ⟨(2, 1), L.boxes⟩ .R).map (·.player) == none         -- 箱 2 個は押せない
#guard (step L ⟨(3, 2), L.boxes⟩ .R).map (·.player) == some (3, 3)  -- 押せる
#guard (step L ⟨(3, 2), L.boxes⟩ .R).map (fun s => mem (3, 4) s.boxes) == some true
#guard pushes ⟨(3, 2), L.boxes⟩ .R && !pushes L.init .U

-- 手順の読み込み
#guard parseMoves "uDlR".toUTF8.data.toList == some [.U, .D, .L, .R]
#guard parseMoves "ux".toUTF8.data.toList == none

-- 検査関数：正しい手順だけを受け付ける
#guard check ["#####", "#@$.#", "#####"] "R"
#guard !check ["#####", "#@$.#", "#####"] ""
#guard !check ["#####", "#@$.#", "#####"] "L"
#guard !check ["#####", "#@ .#", "#####"] ""          -- 箱がない盤面は WellFormed でない
#guard !check ["#####", "#@$$#", "#..##", "####"] "" -- 未クリア

-- カーネルでも同じ計算ができる（証明ファイルと同じ仕組み）
example : WellFormed (Level.ofRows ["#####", "#@$.#", "#####"]) ∧
    Solvable (Level.ofRows ["#####", "#@$.#", "#####"]) :=
  Soundness.certify _ "R" (by decide +kernel)

-- ゲーム：押し数、1 手戻す、やり直し
open Game in
#guard
  let s := Session.load #[room] 0 []
  let s1 := (s.apply (.move .R)).apply (.move .R)
  s1.moves == 2 && s1.pushes == 1 &&
  (s1.apply .undo).pushes == 0 && (s1.apply .undo).moves == 1 &&
  (s1.apply .restart).moves == 0

-- line モードの入力
open Game in
#guard (parseLine ":rRuL").length == 4 && (parseLine "wasd").length == 4 &&
  (match parseLine "g12" with | [.goto 12] => true | _ => false)

end Leankoban.Tests
