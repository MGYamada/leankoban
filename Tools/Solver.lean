import Tools.Grid

/-!
# ソルバー（信頼しない）

押す手の回数で幅優先探索し、押し数が最小の解を求める。局面は「箱の配置 + 人の到達領域」
（人の位置は到達領域の最小番号に正規化）。箱を死に床へ押す手は枝刈りする。
見つけた押し手の列に、人の歩行経路を補って LURD 文字列にする。

このソルバーの正しさは信頼しない。出力された手順は `Engine.check` で検査され、
証明ファイルではカーネルが同じ検査を行う。
-/

namespace Leankoban.Tools

open Leankoban

structure Solution where
  pushes   : Nat
  moves    : Nat
  lurd     : String
  explored : Nat
  deriving Inhabited

def allOnGoals (g : Grid) (bs : Array Nat) : Bool := bs.all g.isGoal

/-- 押し手の列（押す前の箱の位置と方向）から LURD 文字列を作る。 -/
def pushesToLurd (g : Grid) (boxes0 : Array Nat) (player0 : Nat) (seq : List (Nat × Dir)) :
    Option String := Id.run do
  let mut occ := g.occOf boxes0
  let mut player := player0
  let mut out : String := ""
  for (b, d) in seq do
    let stand := g.nb b d.opp
    match g.walkPath occ player stand with
    | none => return none
    | some path =>
      for e in path do
        out := out.push (e.toLurd false)
      out := out.push (d.toLurd true)
      occ := (occ.set! b false).set! (g.nb b d) true
      player := b
  return some out

/-- 押し数最小の解を探す。`cap` は訪問する局面数の上限。 -/
def solve (g : Grid) (boxes0 : Array Nat) (player0 : Nat) (cap : Nat := 4000000) : Option Solution := Id.run do
  let k := boxes0.size
  if k == 0 || k > 7 || g.size > 256 then return none
  let live := g.liveCells
  let b0 := boxes0.insertionSort (· < ·)
  let (_, n0) := g.reach (g.occOf b0) player0
  let key0 := packKey n0 b0
  -- 親の局面、押す前の箱の位置、押した方向
  let mut parent : Std.HashMap UInt64 (UInt64 × UInt16 × UInt8) := Std.HashMap.emptyWithCapacity 4096
  parent := parent.insert key0 (key0, 0, 255)
  let mut queue : Array UInt64 := #[key0]
  let mut head := 0
  let mut found : Option UInt64 := if allOnGoals g b0 then some key0 else none
  while found.isNone && head < queue.size && parent.size < cap do
    let key := queue[head]!
    head := head + 1
    let (pn, bs) := unpackKey k key
    let occ := g.occOf bs
    let (rch, _) := g.reach occ pn
    for j in [0:k] do
      if found.isSome then break
      let b := bs[j]!
      for d in allDirs do
        let stand := g.nb b d.opp
        let t := g.nb b d
        if rch[stand]! && g.isFloor t && !occ[t]! && live[t]! then
          let nbs := replaceSorted bs j t
          let occ2 := (occ.set! b false).set! t true
          let (_, mn) := g.reach occ2 b
          let nk := packKey mn nbs
          if !parent.contains nk then
            parent := parent.insert nk (key, b.toUInt16, d.toIdx)
            queue := queue.push nk
            if allOnGoals g nbs then
              found := some nk
              break
  match found with
  | none => return none
  | some goalKey =>
    -- 親をたどって押し手の列を復元する
    let mut seq : List (Nat × Dir) := []
    let mut cur := goalKey
    let mut fuel := parent.size + 1
    while cur != key0 && fuel > 0 do
      fuel := fuel - 1
      match parent.get? cur with
      | some (pk, b, di) =>
        seq := (b.toNat, Dir.ofIdx di) :: seq
        cur := pk
      | none => fuel := 0
    match pushesToLurd g b0 player0 seq with
    | none => return none
    | some lurd =>
      return some { pushes := seq.length, moves := lurd.length, lurd, explored := parent.size }

/-- XSB の行から直接解く。 -/
def solveRows (rows : List String) (cap : Nat := 4000000) : Option Solution :=
  let (g, boxes, player) := Grid.ofLevel (Level.ofRows rows)
  solve g boxes player cap

end Leankoban.Tools
