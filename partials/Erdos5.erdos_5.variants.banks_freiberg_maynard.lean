import FormalConjectures.ErdosProblems.«5»

-- Problem: Erdős Problem 5 — banks freiberg maynard
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/5.lean:153 (declaration Erdos5.erdos_5.variants.banks_freiberg_maynard)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.BFMNine

open Filter Real Set Erdos5
open scoped Topology

/-- Banks-Freiberg-Maynard, Theorem 1.1, for strictly increasing nonnegative shifts.
Sole remaining gap: needs the Maynard-Tao sieve combined with Erdos-Rankin. -/
lemma nine_point_strict (β : Fin 9 → ℝ) (hβ : ∀ i, 0 ≤ β i) (hs : StrictMono β) :
    ∃ i j, i < j ∧ β j - β i ∈ limitPointSet := by
  sorry

/-- Zero is a limit point, from the strict case applied to an arithmetic progression
of shifts with small step, plus closedness of the limit point set. -/
lemma zero_mem_of_strict
    (h : ∀ β : Fin 9 → ℝ, (∀ i, 0 ≤ β i) → StrictMono β →
      ∃ i j, i < j ∧ β j - β i ∈ limitPointSet) :
    (0 : ℝ) ∈ limitPointSet := by
  rw [← isClosed_limitPointSet.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  have hδ : 0 < ε / 9 := by positivity
  obtain ⟨i, j, hij, hmem⟩ := h (fun k : Fin 9 => ((k : ℕ) : ℝ) * (ε / 9))
    (fun k => by positivity)
    (fun a b hab => mul_lt_mul_of_pos_right (by exact_mod_cast hab) hδ)
  refine ⟨_, hmem, ?_⟩
  have hlt : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
  have hj : ((j : ℕ) : ℝ) ≤ 8 := by exact_mod_cast (Nat.lt_succ_iff.mp j.isLt)
  have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (by nlinarith)]
  nlinarith

/-- Monotone case from the strict case. -/
theorem main_of_strict
    (h : ∀ β : Fin 9 → ℝ, (∀ i, 0 ≤ β i) → StrictMono β →
      ∃ i j, i < j ∧ β j - β i ∈ limitPointSet) :
    type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard := by
  intro β hβ hmono
  by_cases hs : StrictMono β
  · exact h β hβ hs
  · simp only [StrictMono, not_forall, not_lt] at hs
    obtain ⟨i, j, hij, hle⟩ := hs
    have heq : β j - β i = 0 := by linarith [hmono hij.le]
    exact ⟨i, j, hij, heq ▸ zero_mem_of_strict h⟩

end OMA.BFMNine

theorem OMA.solution : type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard := by
  exact OMA.BFMNine.main_of_strict OMA.BFMNine.nine_point_strict
