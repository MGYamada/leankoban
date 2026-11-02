import Leankoban.Spec

/-!
# 実行系

`Spec` の関係を計算できる形で書いたもの。ゲームの移動処理も、証明でカーネルが
評価する検査関数 `check` も、すべてこのファイルの関数を使う。
仕様との一致は `Leankoban.Soundness` で証明する（健全性と完全性）。

カーネルでの評価を速く保つため、文字列はバイト列として読み、`Nat` の比較だけで処理する。
-/

namespace Leankoban.Engine

/-- 位置 `x` がリスト `l` に含まれるか。
（`List.contains` と同じだが、公理を使わずに性質を証明できるよう自前で定義する。） -/
def mem (x : Pos) : List Pos → Bool
  | [] => false
  | y :: l => (x == y) || mem x l

/-- `xs` のすべての要素が `ys` に含まれるか。 -/
def allIn : List Pos → List Pos → Bool
  | [], _ => true
  | x :: xs, ys => mem x ys && allIn xs ys

/-- 1 手進める。動けないときは `none`。`Spec.Step` の二つの規則をそのまま写したもの。 -/
def step (L : Level) (s : State) (d : Dir) : Option State :=
  match s.player.next d with
  | none => none
  | some t =>
    bif mem t L.floor then
      bif mem t s.boxes then
        match t.next d with
        | none => none
        | some u =>
          bif mem u L.floor && !mem u s.boxes then
            some ⟨t, u :: s.boxes.erase t⟩
          else none
      else some ⟨t, s.boxes⟩
    else none

/-- 手の列を順に実行する。途中で 1 手でも動けなければ `none`。 -/
def run (L : Level) : State → List Dir → Option State
  | s, [] => some s
  | s, d :: ds =>
    match step L s d with
    | none => none
    | some s' => run L s' ds

/-- クリア判定。 -/
def isSolved (L : Level) (s : State) : Bool :=
  allIn s.boxes L.goals && allIn L.goals s.boxes

/-- `WellFormed` の判定。 -/
def wellFormed (L : Level) : Bool :=
  decide (0 < L.goals.length) && decide (L.goals.length = L.boxes.length) &&
  decide L.boxes.Nodup && decide L.goals.Nodup &&
  mem L.player L.floor && !mem L.player L.boxes

/-- LURD 記法の 1 文字（ASCII バイト）を方向に変換する。大文字は押す手を表す慣習だが、意味は同じ。 -/
def dirOfByte (b : UInt8) : Option Dir :=
  let n := b.toNat
  -- 117 'u'  85 'U'  100 'd'  68 'D'  108 'l'  76 'L'  114 'r'  82 'R'
  if n == 117 || n == 85 then some .U
  else if n == 100 || n == 68 then some .D
  else if n == 108 || n == 76 then some .L
  else if n == 114 || n == 82 then some .R
  else none

/-- LURD 文字列（のバイト列）を手の列に変換する。知らない文字があれば `none`。
（重なりのあるパターン `| _, _ =>` は match の補助定理が `propext` を持ち込むので使わない。） -/
def parseMoves : List UInt8 → Option (List Dir)
  | [] => some []
  | b :: bs =>
    match dirOfByte b with
    | none => none
    | some d =>
      match parseMoves bs with
      | none => none
      | some ds => some (d :: ds)

/-- 盤面が `WellFormed` で、手順 `sol` を初期局面から実行するとクリア状態になるか。
証明ファイルではこの関数をカーネルに評価させる（`decide +kernel`）。 -/
def check (rows : List String) (sol : String) : Bool :=
  let L := Level.ofRows rows
  wellFormed L &&
    match parseMoves sol.toByteArray.data.toList with
    | none => false
    | some ds =>
      match run L L.init ds with
      | none => false
      | some s => isSolved L s

/-- 1 手の結果、箱を押したかどうか（ゲームの押し数表示用）。 -/
def pushes (s : State) (d : Dir) : Bool :=
  match s.player.next d with
  | none => false
  | some t => mem t s.boxes

end Leankoban.Engine
