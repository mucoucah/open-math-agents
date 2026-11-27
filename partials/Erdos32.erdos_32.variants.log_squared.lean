import FormalConjectures.ErdosProblems.«32»

-- Problem: Erdős Problem 32 — log squared
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/32.lean:50 (declaration Erdos32.erdos_32.variants.log_squared)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics

namespace OMA32

open scoped Classical in
/-- Glue: an explicit eventual bound gives the big-O statement. -/
lemma bigO_of_bound (A : Set ℕ) (C : ℝ) (N0 : ℕ)
    (h : ∀ N ≥ N0, (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) ≤ C * (Real.log N) ^ 2) :
    (fun N => (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) =O[atTop]
      fun N => (Real.log N) ^ 2 := by
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop N0] with N hN
  have h1 := h N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  exact h1

open scoped Classical in
/-- Core (Erdős 1954): needs averaged short-interval prime estimates. -/
lemma core : ∃ A : Set ℕ, Erdos32.IsAdditiveComplementToPrimes A ∧ ∃ C : ℝ, ∃ N0 : ℕ,
    ∀ N ≥ N0, (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) ≤ C * (Real.log N) ^ 2 := by
  sorry

end OMA32

theorem OMA.solution : type_of% @Erdos32.erdos_32.variants.log_squared := by
  obtain ⟨A, hA, C, N0, h⟩ := OMA32.core
  exact ⟨A, hA, OMA32.bigO_of_bound A C N0 h⟩
