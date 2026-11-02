import Leankoban.Spec
import Std.Data.HashMap

/-!
# 探索用の盤面表現

外周に 1 マスの壁を足した長方形で、各マスを `r * w + c` の番号で表す。
床のマスの隣は必ず配列の範囲内にあるので、範囲外の心配なく隣を計算できる。
局面（人の正規化位置 + 箱の位置の昇順）は 8 ビットずつ `UInt64` に詰めて、ハッシュ表のキーにする。
-/

namespace Leankoban.Tools

open Leankoban

structure Grid where
  h     : Nat
  w     : Nat
  floor : Array Bool
  goal  : Array Bool
  deriving Inhabited

def allDirs : Array Dir := #[.U, .D, .L, .R]

def _root_.Leankoban.Dir.opp : Dir → Dir
  | .U => .D | .D => .U | .L => .R | .R => .L

def _root_.Leankoban.Dir.toIdx : Dir → UInt8
  | .U => 0 | .D => 1 | .L => 2 | .R => 3

def _root_.Leankoban.Dir.ofIdx : UInt8 → Dir
  | 0 => .U | 1 => .D | 2 => .L | _ => .R

/-- LURD 記法の文字。押す手は大文字。 -/
def _root_.Leankoban.Dir.toLurd (d : Dir) (push : Bool) : Char :=
  match d, push with
  | .U, false => 'u' | .D, false => 'd' | .L, false => 'l' | .R, false => 'r'
  | .U, true => 'U' | .D, true => 'D' | .L, true => 'L' | .R, true => 'R'

namespace Grid

def size (g : Grid) : Nat := g.h * g.w

@[inline] def isFloor (g : Grid) (i : Nat) : Bool := g.floor[i]!
@[inline] def isGoal (g : Grid) (i : Nat) : Bool := g.goal[i]!

/-- 隣のマス。床のマスに対してだけ呼ぶ（外周が壁なので範囲内に収まる）。 -/
@[inline] def nb (g : Grid) (i : Nat) : Dir → Nat
  | .U => i - g.w
  | .D => i + g.w
  | .L => i - 1
  | .R => i + 1

/-- 番号を仕様の位置 `(行, 列)` に戻す（外周の分を引く）。 -/
def toPos (g : Grid) (i : Nat) : Pos := (i / g.w - 1, i % g.w - 1)

/-- 仕様の位置を番号にする。 -/
def ofPos (g : Grid) (p : Pos) : Nat := (p.1 + 1) * g.w + (p.2 + 1)

/-- 仕様の盤面から探索用の盤面を作る。戻り値は（盤面, 箱の番号, 人の番号）。 -/
def ofLevel (L : Level) : Grid × Array Nat × Nat :=
  let maxR := L.floor.foldl (fun m p => max m p.1) 0
  let maxC := L.floor.foldl (fun m p => max m p.2) 0
  let h := maxR + 3
  let w := maxC + 3
  let g0 : Grid := { h, w, floor := Array.replicate (h * w) false, goal := Array.replicate (h * w) false }
  let floor := L.floor.foldl (fun a p => a.set! (g0.ofPos p) true) g0.floor
  let goal := L.goals.foldl (fun a p => a.set! (g0.ofPos p) true) g0.goal
  let g := { g0 with floor, goal }
  (g, (L.boxes.map g.ofPos).toArray, g.ofPos L.player)

/-- 箱の番号の配列から、占有表を作る。 -/
def occOf (g : Grid) (boxes : Array Nat) : Array Bool :=
  boxes.foldl (fun a b => a.set! b true) (Array.replicate g.size false)

/-- `start` から、床で箱のないマスをたどって行ける範囲と、その中の最小番号（正規化位置）。 -/
def reach (g : Grid) (occ : Array Bool) (start : Nat) : Array Bool × Nat := Id.run do
  let mut seen := (Array.replicate g.size false).set! start true
  let mut stack := #[start]
  let mut mn := start
  while !stack.isEmpty do
    let i := stack.back!
    stack := stack.pop
    if i < mn then mn := i
    for d in allDirs do
      let j := g.nb i d
      if g.isFloor j && !occ[j]! && !seen[j]! then
        seen := seen.set! j true
        stack := stack.push j
  return (seen, mn)

/-- 箱が置かれても、まだどれかのゴールへ押していける可能性のあるマス（それ以外は「死に床」）。
ゴールから箱を「引く」逆向きの探索で求める（他の箱は無視する）。 -/
def liveCells (g : Grid) : Array Bool := Id.run do
  let mut live := Array.replicate g.size false
  let mut stack : Array Nat := #[]
  for i in [0:g.size] do
    if g.isGoal i then
      live := live.set! i true
      stack := stack.push i
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    for d in allDirs do
      let y := g.nb x d
      if g.isFloor y && !live[y]! then
        let z := g.nb y d
        if g.isFloor z then
          live := live.set! y true
          stack := stack.push y
  return live

/-- 人が `src` から `dst` へ、箱を避けて歩く最短経路。 -/
def walkPath (g : Grid) (occ : Array Bool) (src dst : Nat) : Option (List Dir) := Id.run do
  if src == dst then return some []
  let mut prev : Array (Option (Nat × Dir)) := Array.replicate g.size none
  let mut seen := (Array.replicate g.size false).set! src true
  let mut queue := #[src]
  let mut head := 0
  let mut found := false
  while head < queue.size && !found do
    let i := queue[head]!
    head := head + 1
    for d in allDirs do
      let j := g.nb i d
      if g.isFloor j && !occ[j]! && !seen[j]! then
        seen := seen.set! j true
        prev := prev.set! j (some (i, d))
        queue := queue.push j
        if j == dst then found := true
  if !found then return none
  let mut path : List Dir := []
  let mut cur := dst
  let mut fuel := g.size
  while cur != src && fuel > 0 do
    fuel := fuel - 1
    match prev[cur]! with
    | some (i, d) =>
      path := d :: path
      cur := i
    | none => fuel := 0
  return some path

end Grid

/-! ## 局面のキー -/

/-- 人の正規化位置と、昇順に並べた箱の番号を `UInt64` に詰める（各 8 ビット、箱は 7 個まで）。 -/
@[inline] def packKey (player : Nat) (boxes : Array Nat) : UInt64 :=
  boxes.foldl (fun acc b => (acc <<< 8) ||| b.toUInt64) player.toUInt64

/-- `packKey` の逆。 -/
@[inline] def unpackKey (k : Nat) (key : UInt64) : Nat × Array Nat := Id.run do
  let mut bs := Array.replicate k 0
  let mut x := key
  for i in [0:k] do
    bs := bs.set! (k - 1 - i) (x &&& 255).toNat
    x := x >>> 8
  return (x.toNat, bs)

/-- 昇順の配列の `j` 番目を `t` に置き換えて、昇順を保つ。 -/
def replaceSorted (bs : Array Nat) (j t : Nat) : Array Nat :=
  (bs.set! j t).insertionSort (· < ·)

end Leankoban.Tools
