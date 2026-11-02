import Tools.Rng
import Tools.Grid
import Tools.Solver
import Leankoban.Engine

/-!
# 盤面生成器（信頼しない）

1. **部屋**：内側を全部床にしてから、小さな壁の欠片をランダムに置く（床がつながったままのときだけ採用）。
   行き止まりの床を壁で埋め、広すぎる空き地（3×4 以上）がある部屋は捨てる。
2. **逆引き探索**：箱をすべてゴールに置いた状態から、箱を「引く」手で幅優先探索する。
   引く手の逆は押す手なので、見つかった局面はどれも**構成上クリア可能**で、探索の深さが最小押し数になる。
3. 最も深い局面（箱がすべてゴールから外れているもの）を初期配置に採用する。
-/

namespace Leankoban.Tools

open Leankoban

/-- 壁の欠片（相対座標）。 -/
def pieces : Array (List (Nat × Nat)) := #[
  [(0, 0)],
  [(0, 0)],
  [(0, 0), (0, 1)],
  [(0, 0), (1, 0)],
  [(0, 0), (0, 1), (1, 0)],
  [(0, 0), (1, 0), (1, 1)],
  [(0, 0), (0, 1), (1, 1)],
  [(0, 1), (1, 0), (1, 1)],
  [(0, 0), (0, 1), (0, 2)],
  [(0, 0), (1, 0), (2, 0)]
]

namespace Grid

/-- 床がすべて 1 つにつながっているか。 -/
def connected (g : Grid) : Bool := Id.run do
  let none := Array.replicate g.size false
  let mut start : Option Nat := Option.none
  let mut count := 0
  for i in [0:g.size] do
    if g.isFloor i then
      count := count + 1
      if start.isNone then start := some i
  match start with
  | Option.none => return false
  | some s =>
    let (seen, _) := g.reach none s
    return (seen.filter id).size == count

/-- 床の数。 -/
def floorCount (g : Grid) : Nat := (g.floor.filter id).size

/-- 行き止まり（壁に 3 方向以上囲まれた床）を壁で埋める。 -/
def fillDeadEnds (g : Grid) : Grid := Id.run do
  let mut floor := g.floor
  let mut changed := true
  let mut fuel := g.size
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    for i in [0:g.size] do
      if floor[i]! then
        let walls := allDirs.foldl (fun n d => if floor[g.nb i d]! then n else n + 1) 0
        if walls ≥ 3 then
          floor := floor.set! i false
          changed := true
  return { g with floor }

/-- `rh × rw` の長方形がすべて床になっている場所があるか。 -/
def hasOpenArea (g : Grid) (rh rw : Nat) : Bool := Id.run do
  for r in [0:g.h] do
    for c in [0:g.w] do
      if r + rh ≤ g.h && c + rw ≤ g.w then
        let mut all := true
        for dr in [0:rh] do
          for dc in [0:rw] do
            if !g.isFloor ((r + dr) * g.w + (c + dc)) then all := false
        if all then return true
  return false

end Grid

/-- 内側 `ih × iw` の部屋を作る（外周 1 マスは壁）。 -/
def makeRoom (ih iw nPieces : Nat) : RandM (Option Grid) := do
  let h := ih + 2
  let w := iw + 2
  let mut floor := Array.replicate (h * w) false
  for r in [1:ih + 1] do
    for c in [1:iw + 1] do
      floor := floor.set! (r * w + c) true
  let mut g : Grid := { h, w, floor, goal := Array.replicate (h * w) false }
  for _ in [0:nPieces] do
    let piece ← randPick pieces
    let r ← randRange 1 ih
    let c ← randRange 1 iw
    let mut f := g.floor
    for (dr, dc) in piece do
      let rr := r + dr
      let cc := c + dc
      if rr ≤ ih && cc ≤ iw then
        f := f.set! (rr * w + cc) false
    let g' := { g with floor := f }
    if g'.connected then g := g'
  g := g.fillDeadEnds
  if !g.connected then return none
  if g.hasOpenArea 3 4 || g.hasOpenArea 4 3 then return none
  return some g

/-- 逆引き探索の結果。 -/
structure Reverse where
  boxes    : Array Nat
  player   : Nat
  depth    : Nat
  explored : Nat

/-- 箱をゴールに置いた状態から「引く」手で幅優先探索し、最も深い局面を返す。 -/
def reverseSearch (g : Grid) (goals : Array Nat) (cap : Nat) : Option Reverse := Id.run do
  let k := goals.size
  let b0 := goals.insertionSort (· < ·)
  let occ0 := g.occOf b0
  -- 箱のないマスの連結成分ごとに、人の初期位置の候補を作る
  let mut info : Std.HashMap UInt64 (UInt32 × UInt16) := Std.HashMap.emptyWithCapacity 4096
  let mut queue : Array UInt64 := #[]
  let mut covered := Array.replicate g.size false
  for i in [0:g.size] do
    if g.isFloor i && !occ0[i]! && !covered[i]! then
      let (seen, mn) := g.reach occ0 i
      for j in [0:g.size] do
        if seen[j]! then covered := covered.set! j true
      let key := packKey mn b0
      if !info.contains key then
        info := info.insert key (0, mn.toUInt16)
        queue := queue.push key
  let mut head := 0
  let mut best : Option (UInt64 × Nat × Nat) := none   -- キー、深さ、ゴールから外れた箱の数
  while head < queue.size && info.size < cap do
    let key := queue[head]!
    head := head + 1
    let (depth, _) := info.getD key (0, 0)
    let (pn, bs) := unpackKey k key
    let off := (bs.filter (fun b => !g.isGoal b)).size
    let better := match best with
      | none => true
      | some (_, bd, boff) => (off == k && boff != k) || (off == k) == (boff == k) && depth.toNat > bd
    if better then best := some (key, depth.toNat, off)
    let occ := g.occOf bs
    let (rch, _) := g.reach occ pn
    for j in [0:k] do
      let b := bs[j]!
      for d in allDirs do
        let p := g.nb b d      -- 人が立つマス（箱の隣）
        if rch[p]! then
          let q := g.nb p d    -- 人が下がる先
          if g.isFloor q && !occ[q]! then
            let nbs := replaceSorted bs j p
            let occ2 := (occ.set! b false).set! p true
            let (_, mn) := g.reach occ2 q
            let nk := packKey mn nbs
            if !info.contains nk then
              info := info.insert nk (depth + 1, q.toUInt16)
              queue := queue.push nk
  match best with
  | none => return none
  | some (key, depth, _) =>
    let (_, bs) := unpackKey k key
    let (_, player) := info.getD key (0, 0)
    return some { boxes := bs, player := player.toNat, depth, explored := info.size }

/-! ## XSB への書き出し -/

/-- 盤面を XSB の行にする。床の外接矩形の 1 マス外側までを切り出し、
床に（斜めも含めて）接する壁だけを `#` で描き、それ以外の外側は空白にする。 -/
def toRows (g : Grid) (boxes : Array Nat) (player : Nat) : List String := Id.run do
  let occ := g.occOf boxes
  let mut r0 := g.h
  let mut r1 := 0
  let mut c0 := g.w
  let mut c1 := 0
  for i in [0:g.size] do
    if g.isFloor i then
      let r := i / g.w
      let c := i % g.w
      r0 := min r0 r; r1 := max r1 r; c0 := min c0 c; c1 := max c1 c
  let mut rows : List String := []
  for r in [r0 - 1:r1 + 2] do
    let mut line := ""
    for c in [c0 - 1:c1 + 2] do
      let i := r * g.w + c
      let ch :=
        if g.isFloor i then
          let gl := g.isGoal i
          if i == player then (if gl then '+' else '@')
          else if occ[i]! then (if gl then '*' else '$')
          else if gl then '.' else ' '
        else
          let touches := Id.run do
            for dr in [0:3] do
              for dc in [0:3] do
                let rr := r + dr
                let cc := c + dc
                if rr ≥ 1 && cc ≥ 1 && rr - 1 < g.h && cc - 1 < g.w then
                  if g.isFloor ((rr - 1) * g.w + (cc - 1)) then return true
            return false
          if touches then '#' else ' '
      line := line.push ch
    rows := rows ++ [line.trimAsciiEnd.toString]
  return rows

/-- 回転・鏡映で同じになる盤面を同一視するための正規形。 -/
def canonical (rows : List String) : String :=
  let grid : Array (Array Char) := rows.toArray.map (fun r => r.toList.toArray)
  let h := grid.size
  let w := grid.foldl (fun m r => max m r.size) 0
  let cellAt (r c : Nat) : Char := (grid[r]?.bind (·[c]?)).getD ' '
  let render (hh ww : Nat) (f : Nat → Nat → Char) : String :=
    "\n".intercalate ((List.range hh).map fun r => String.ofList ((List.range ww).map (f r)))
  let variants := [
    render h w (fun r c => cellAt r c),
    render h w (fun r c => cellAt r (w - 1 - c)),
    render h w (fun r c => cellAt (h - 1 - r) c),
    render h w (fun r c => cellAt (h - 1 - r) (w - 1 - c)),
    render w h (fun r c => cellAt c r),
    render w h (fun r c => cellAt c (w - 1 - r)),
    render w h (fun r c => cellAt (h - 1 - c) r),
    render w h (fun r c => cellAt (h - 1 - c) (w - 1 - r))]
  variants.foldl (fun m v => if v < m then v else m) (variants.head!)

/-! ## 1 面の生成 -/

structure Params where
  boxes    : Nat
  hMin     : Nat
  hMax     : Nat
  wMin     : Nat
  wMax     : Nat
  pieces   : Nat
  minPush  : Nat
  floorMin : Nat
  floorMax : Nat
  cap      : Nat := 300000

structure Generated where
  rows     : List String
  boxes    : Nat
  depth    : Nat        -- 最小押し数
  moves    : Nat        -- ソルバーの解の手数
  explored : Nat        -- 逆引き探索で訪れた局面数
  score    : Nat

/-- 1 面を試しに作る。条件を満たさなければ `none`。 -/
def tryGenerate (p : Params) : RandM (Option Generated) := do
  let ih ← randRange p.hMin p.hMax
  let iw ← randRange p.wMin p.wMax
  let some g ← makeRoom ih iw p.pieces | return none
  let fc := g.floorCount
  if fc < p.floorMin || fc > p.floorMax || fc < p.boxes + 4 then return none
  -- ゴールを置く
  let cells := (List.range g.size).filter g.isFloor |>.toArray
  let cells ← shuffle cells
  let goals := cells.extract 0 p.boxes
  let g := { g with goal := goals.foldl (fun a i => a.set! i true) g.goal }
  let some rev := reverseSearch g goals p.cap | return none
  if rev.depth < p.minPush then return none
  if rev.boxes.any g.isGoal then return none
  let rows := toRows g rev.boxes rev.player
  -- 生成した行から解き直し、実行系の検査で確認する
  let some sol := solveRows rows | return none
  if !Engine.check rows sol.lurd then return none
  let score := sol.pushes * 10 + Nat.log2 (rev.explored + 1) * 3 + sol.moves / 10
  return some { rows, boxes := p.boxes, depth := sol.pushes, moves := sol.moves,
                explored := rev.explored, score }

end Leankoban.Tools
