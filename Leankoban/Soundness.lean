import Leankoban.Engine

/-!
# 実行系の健全性と完全性

`Engine.step` が `Spec.Step` と完全に一致すること、そして `Engine.check` が `true` を返せば
その盤面が `WellFormed` かつ `Solvable` であることを証明する。

**公理を一切使わない**ことを方針とする。core の補題の多くは `propext` に依存するため、
`simp` や `List.mem_cons` などは使わず、`Bool` と `List` についての小さな補題を自前で証明する。
-/

namespace Leankoban.Soundness

open Engine

/-! ## `Bool` の補題 -/

theorem and_left : ∀ {a b : Bool}, (a && b) = true → a = true
  | true, _, _ => rfl
  | false, _, h => nomatch h

theorem and_right : ∀ {a b : Bool}, (a && b) = true → b = true
  | _, true, _ => rfl
  | true, false, h => nomatch h
  | false, false, h => nomatch h

theorem and_intro : ∀ {a b : Bool}, a = true → b = true → (a && b) = true
  | true, true, _, _ => rfl

theorem or_true_right : ∀ (a : Bool), (a || true) = true
  | true => rfl
  | false => rfl

theorem not_eq_true : ∀ {a : Bool}, (!a) = true → a = false
  | false, _ => rfl
  | true, h => nomatch h

theorem not_intro : ∀ {a : Bool}, a = false → (!a) = true
  | false, _ => rfl

/-! ## 位置の等号判定 -/

theorem pos_eq_of_beq : ∀ {a b : Pos}, (a == b) = true → a = b
  | (a₁, a₂), (b₁, b₂), h => by
    have h₁ : decide (a₁ = b₁) = true := and_left h
    have h₂ : decide (a₂ = b₂) = true := and_right h
    cases of_decide_eq_true h₁
    cases of_decide_eq_true h₂
    rfl

theorem beq_self : ∀ (a : Pos), (a == a) = true
  | (a₁, a₂) => and_intro (decide_eq_true (Eq.refl a₁)) (decide_eq_true (Eq.refl a₂))

/-! ## `mem` と `allIn` -/

theorem mem_sound {x : Pos} : ∀ {l : List Pos}, mem x l = true → x ∈ l
  | [], h => nomatch h
  | y :: l, h => by
    cases hxy : (x == y) with
    | true =>
      cases pos_eq_of_beq hxy
      exact List.Mem.head l
    | false =>
      have h' : ((x == y) || mem x l) = true := h
      rw [hxy] at h'
      exact List.Mem.tail y (mem_sound h')

theorem mem_complete {x : Pos} : ∀ {l : List Pos}, x ∈ l → mem x l = true
  | _, .head l => by
    show ((x == x) || mem x l) = true
    rw [beq_self x]
    rfl
  | _, .tail y h => by
    show ((x == y) || mem x _) = true
    rw [mem_complete h]
    exact or_true_right _

theorem not_mem_of_mem_false {x : Pos} {l : List Pos} (h : mem x l = false) : x ∉ l :=
  fun hm => by
    rw [mem_complete hm] at h
    exact nomatch h

theorem mem_false_of_not_mem {x : Pos} {l : List Pos} (h : x ∉ l) : mem x l = false := by
  cases hm : mem x l with
  | false => rfl
  | true => exact absurd (mem_sound hm) h

theorem allIn_sound : ∀ {xs ys : List Pos}, allIn xs ys = true → ∀ x ∈ xs, x ∈ ys
  | [], _, _, _, hx => nomatch hx
  | z :: zs, ys, h, x, hx => by
    have h₁ : mem z ys = true := and_left h
    have h₂ : allIn zs ys = true := and_right h
    cases hx with
    | head => exact mem_sound h₁
    | tail _ hx' => exact allIn_sound h₂ x hx'

/-! ## 1 手の健全性・完全性 -/

/-- 実行系で動けた手は、仕様上も正しい 1 手である。 -/
theorem step_sound {L : Level} {s s' : State} {d : Dir}
    (h : step L s d = some s') : Step L s s' := by
  unfold step at h
  cases hn : s.player.next d with
  | none =>
    rw [hn] at h
    exact nomatch h
  | some t =>
    rw [hn] at h
    dsimp only at h
    cases hf : mem t L.floor with
    | false =>
      rw [hf] at h
      exact nomatch h
    | true =>
      rw [hf] at h
      cases hb : mem t s.boxes with
      | false =>
        rw [hb] at h
        cases h
        exact Step.walk hn (mem_sound hf) (not_mem_of_mem_false hb)
      | true =>
        rw [hb] at h
        cases hu : t.next d with
        | none =>
          rw [hu] at h
          exact nomatch h
        | some u =>
          rw [hu] at h
          dsimp only at h
          cases hc : (mem u L.floor && !mem u s.boxes) with
          | false =>
            rw [hc] at h
            exact nomatch h
          | true =>
            rw [hc] at h
            cases h
            exact Step.push hn (mem_sound hf) (mem_sound hb) hu (mem_sound (and_left hc))
              (not_mem_of_mem_false (not_eq_true (and_right hc)))

/-- 仕様上正しい 1 手は、実行系でもその向きに動ける。（ゲームのルール＝仕様） -/
theorem step_complete {L : Level} {s s' : State} (h : Step L s s') :
    ∃ d, step L s d = some s' := by
  cases h with
  | @walk p bs d t hn hf hb =>
    refine ⟨d, ?_⟩
    unfold step
    dsimp only
    rw [hn]
    dsimp only
    rw [mem_complete hf, mem_false_of_not_mem hb]
    rfl
  | @push p bs d t u hn hf hb hu hf' hnb =>
    refine ⟨d, ?_⟩
    unfold step
    dsimp only
    rw [hn]
    dsimp only
    rw [mem_complete hf, mem_complete hb, hu]
    dsimp only
    rw [mem_complete hf', mem_false_of_not_mem hnb]
    rfl

/-! ## 手順の健全性 -/

theorem run_sound {L : Level} :
    ∀ {s s' : State} {ds : List Dir}, run L s ds = some s' → Reachable L s s'
  | _, _, [], h => by
    cases h
    exact Reachable.refl
  | s, s', d :: ds, h => by
    unfold run at h
    cases hs : step L s d with
    | none =>
      rw [hs] at h
      exact nomatch h
    | some t =>
      rw [hs] at h
      dsimp only at h
      exact Reachable.step (step_sound hs) (run_sound h)

theorem isSolved_sound {L : Level} {s : State} (h : isSolved L s = true) : Solved L s :=
  ⟨allIn_sound (and_left h), allIn_sound (and_right h)⟩

theorem wellFormed_sound {L : Level} (h : wellFormed L = true) : WellFormed L := by
  have h₅ := and_left h
  have h₆ := and_right h
  have h₄ := and_left h₅
  have hp := and_right h₅
  have h₃ := and_left h₄
  have hg := and_right h₄
  have h₂ := and_left h₃
  have hb := and_right h₃
  have h₁ := and_left h₂
  have hl := and_right h₂
  exact ⟨of_decide_eq_true h₁, of_decide_eq_true hl, of_decide_eq_true hb, of_decide_eq_true hg,
    mem_sound hp, not_mem_of_mem_false (not_eq_true h₆)⟩

/-! ## 証明書の検査 -/

/-- **主定理**：`check rows sol = true` なら、盤面 `rows` は `WellFormed` かつ `Solvable`。
各面の証明は、解の手順 `sol` を与えて `check rows sol = true` をカーネルに計算させるだけである。 -/
theorem certify (rows : List String) (sol : String) (h : Engine.check rows sol = true) :
    WellFormed (Level.ofRows rows) ∧ Solvable (Level.ofRows rows) := by
  have hw := and_left h
  have hr := and_right h
  refine ⟨wellFormed_sound hw, ?_⟩
  cases hp : parseMoves sol.toByteArray.data.toList with
  | none =>
    rw [hp] at hr
    exact nomatch hr
  | some ds =>
    rw [hp] at hr
    dsimp only at hr
    cases hrun : run (Level.ofRows rows) (Level.ofRows rows).init ds with
    | none =>
      rw [hrun] at hr
      exact nomatch hr
    | some s =>
      rw [hrun] at hr
      dsimp only at hr
      exact ⟨s, run_sound hrun, isSolved_sound hr⟩

/-! ## 全面をまとめるための補題（`List.forall_mem_cons` 等の代わり。公理を使わない） -/

theorem forall_mem_cons_intro {α : Type} {P : α → Prop} {a : α} {l : List α}
    (ha : P a) (hl : ∀ x ∈ l, P x) : ∀ x ∈ a :: l, P x
  | _, .head _ => ha
  | x, .tail _ h => hl x h

theorem forall_mem_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x :=
  fun _ h => nomatch h

end Leankoban.Soundness
