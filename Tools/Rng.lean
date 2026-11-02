/-!
# 乱数（SplitMix64）

seed を固定すれば、どの環境でも同じ盤面が生成される。
-/

namespace Leankoban.Tools

structure Rng where
  state : UInt64
  deriving Inhabited

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

abbrev RandM := StateM Rng

/-- `[0, n)` の一様乱数（`n = 0` なら 0）。 -/
def randBelow (n : Nat) : RandM Nat := do
  if n == 0 then return 0
  let (x, g) := (← get).next
  set g
  return x.toNat % n

/-- `[lo, hi]` の一様乱数。 -/
def randRange (lo hi : Nat) : RandM Nat := do
  return lo + (← randBelow (hi + 1 - lo))

/-- 配列からランダムに 1 つ選ぶ。 -/
def randPick {α : Type} [Inhabited α] (xs : Array α) : RandM α := do
  return xs[← randBelow xs.size]!

/-- Fisher–Yates シャッフル。 -/
def shuffle {α : Type} [Inhabited α] (xs : Array α) : RandM (Array α) := do
  let mut a := xs
  let n := a.size
  for i in [0:n] do
    let j := i + (← randBelow (n - i))
    let x := a[i]!
    a := (a.set! i a[j]!).set! j x
  return a

end Leankoban.Tools
