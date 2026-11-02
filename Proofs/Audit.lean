import Proofs
import Lean

/-!
# 公理監査

`lake build` のたびに次を検査し、1 つでも違反があればビルドを失敗させる。

1. 盤面 `Levels.levelNNN` のそれぞれに証明 `Proofs.LevelNNN.solvable` があり、その主張が
   ちょうど `WellFormed (Level.ofRows Levels.levelNNN) ∧ Solvable (Level.ofRows Levels.levelNNN)` である。
2. 全面をまとめた `all_levels_solvable` の主張が
   `∀ rows ∈ Levels.all, WellFormed (Level.ofRows rows) ∧ Solvable (Level.ofRows rows)` である。
3. これらの定理と、健全性・完全性の定理が、**公理を 1 つも使っていない**
   （`sorryAx` も、`native_decide` が使う `Lean.ofReduceBool` も、`propext` などの標準公理も含めて）。
-/

open Lean Elab Command Meta

namespace Leankoban.Audit

def pad3 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (3 - s.length) ++ s

/-- 定理 `thm` の主張が `expected` と（reducible な展開だけで）一致するか確かめる。 -/
def checkStatement (thm : Name) (expected : Expr) : TermElabM Unit := do
  let some info := (← getEnv).find? thm | throwError "定理 {thm} が見つかりません"
  unless info matches .thmInfo _ do throwError "{thm} は定理ではありません"
  unless ← withReducible (isDefEq info.type expected) do
    throwError "{thm} の主張が期待と異なります:{indentExpr info.type}\n期待:{indentExpr expected}"

/-- 定理 `thm` が公理に依存していないことを確かめる。 -/
def checkNoAxioms (thm : Name) : CommandElabM Unit := do
  let axs ← collectAxioms thm
  unless axs.isEmpty do
    throwError "{thm} が公理に依存しています: {axs}"

run_cmd do
  let env ← getEnv
  -- 盤面の数を数える（level001, level002, … と続く限り）
  let mut n := 0
  while env.contains (Name.mkStr `Leankoban.Levels s!"level{pad3 (n + 1)}") do
    n := n + 1
  if n == 0 then throwError "盤面がありません"
  -- 1. 各面の定理
  for i in [1:n + 1] do
    let lvl := Name.mkStr `Leankoban.Levels s!"level{pad3 i}"
    let thm := Name.mkStr (Name.mkStr `Leankoban.Proofs s!"Level{pad3 i}") "solvable"
    let level := mkApp (mkConst ``Leankoban.Level.ofRows) (mkConst lvl)
    let expected := mkAnd (mkApp (mkConst ``Leankoban.WellFormed) level)
      (mkApp (mkConst ``Leankoban.Solvable) level)
    liftTermElabM (checkStatement thm expected)
    checkNoAxioms thm
  -- 2. 全面をまとめた定理
  liftTermElabM do
    let stx ← `(∀ rows ∈ Leankoban.Levels.all,
      Leankoban.WellFormed (Leankoban.Level.ofRows rows) ∧ Leankoban.Solvable (Leankoban.Level.ofRows rows))
    let expected ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    checkStatement ``Leankoban.all_levels_solvable (← instantiateMVars expected)
  checkNoAxioms ``Leankoban.all_levels_solvable
  -- 3. 健全性・完全性の定理
  let core := [``Leankoban.Soundness.step_sound, ``Leankoban.Soundness.step_complete,
    ``Leankoban.Soundness.run_sound, ``Leankoban.Soundness.certify]
  for thm in core do
    checkNoAxioms thm
  logInfo m!"監査 OK: 面ごとの定理 {n} 個と all_levels_solvable の主張は期待どおりで、\
    これらと {core.length} 個の健全性・完全性の定理はすべて公理に依存しない。"

end Leankoban.Audit
