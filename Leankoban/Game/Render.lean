import Leankoban.Engine

/-!
# 描画

ANSI エスケープシーケンスで盤面を描く。1 マスを半角 2 文字で表し、正方形に近い見た目にする。
端末の「曖昧幅」文字は環境によって幅が変わるので使わず、ASCII と背景色だけで描く。
`plain` モードでは XSB 形式の文字だけを出力する（パイプやテスト用）。
-/

namespace Leankoban.Game

open Engine

/-- マスの種類。 -/
inductive Cell where
  | outside | wall | floor | goal | box | boxOnGoal | player | playerOnGoal
  deriving BEq, Repr

/-- 盤面の幅（最長の行のバイト数）。 -/
def boardWidth (rows : List String) : Nat :=
  rows.foldl (fun m r => max m r.utf8ByteSize) 0

/-- 行 `r` に実際に `'#'` が書かれているか（行の右端より外は壁ではなく「外」として描く）。 -/
def isWallChar (rows : List String) (p : Pos) : Bool :=
  match rows[p.1]? with
  | none => false
  | some row =>
    match row.toByteArray.data[p.2]? with
    | some b => b.toNat == 35
    | none => false

/-- 人の初期位置から床をたどって行けるマス（部屋の内側）。外側の空白と区別して描くために使う。 -/
partial def interior (L : Level) : List Pos :=
  let rec go (todo : List Pos) (seen : List Pos) : List Pos :=
    match todo with
    | [] => seen
    | p :: rest =>
      if mem p seen || !mem p L.floor then go rest seen
      else
        let ns := [Dir.U, .D, .L, .R].filterMap p.next
        go (ns ++ rest) (p :: seen)
  go [L.player] []

/-- 位置 `p` のマスの種類。 -/
def cellAt (rows : List String) (L : Level) (inner : List Pos) (s : State) (p : Pos) : Cell :=
  let g := mem p L.goals
  if p == s.player then (if g then .playerOnGoal else .player)
  else if mem p s.boxes then (if g then .boxOnGoal else .box)
  else if g then .goal
  else if mem p inner then .floor
  else if isWallChar rows p then .wall
  else .outside

/-- XSB 形式の 1 文字。 -/
def Cell.toXsb : Cell → String
  | .outside => " "
  | .wall => "#"
  | .floor => " "
  | .goal => "."
  | .box => "$"
  | .boxOnGoal => "*"
  | .player => "@"
  | .playerOnGoal => "+"

/-- カラー表示の 1 マス（半角 2 文字）。 -/
def Cell.toAnsi : Cell → String
  | .outside => "  "
  | .wall => "\x1b[48;5;244m  \x1b[0m"
  | .floor => "\x1b[48;5;236m  \x1b[0m"
  | .goal => "\x1b[48;5;236;38;5;203m()\x1b[0m"
  | .box => "\x1b[48;5;236;38;5;220m[]\x1b[0m"
  | .boxOnGoal => "\x1b[48;5;236;1;38;5;84m[]\x1b[0m"
  | .player => "\x1b[48;5;236;1;38;5;45m@ \x1b[0m"
  | .playerOnGoal => "\x1b[48;5;236;1;38;5;45m@\x1b[0;48;5;236;38;5;203m)\x1b[0m"

/-- 盤面全体を文字列にする。 -/
def renderBoard (plain : Bool) (rows : List String) (L : Level) (inner : List Pos) (s : State) : String :=
  let w := boardWidth rows
  let lines := (List.range rows.length).map fun r =>
    let cells := (List.range w).map fun c =>
      let cell := cellAt rows L inner s (r, c)
      if plain then cell.toXsb else cell.toAnsi
    let line := String.join cells
    if plain then line.trimAsciiEnd.toString else line
  "\n".intercalate lines

end Leankoban.Game
