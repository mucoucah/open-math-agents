import FormalConjectures.ErdosProblems.«787»

-- Problem: Erdős Problem 787 — sanders
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/787.lean:136 (declaration Erdos787.erdos_787.variants.sanders)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

namespace OMA

/-- Core combinatorial statement of Sanders 2021 (the open leaf): every n-element set of reals
contains a sum-avoiding subset of size at least the ceiling of (log n)^(1+c). -/
theorem sanders_core : ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, ⌈Real.log n ^ (1 + c)⌉₊ ≤ B.card ∧ Disjoint B.restrictedSumset A := by
  sorry

/-- Glue: the combinatorial core gives the lower bound on g. -/
theorem sanders_of_core
    (h : ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ, A.card = n →
      ∃ B ⊆ A, ⌈Real.log n ^ (1 + c)⌉₊ ≤ B.card ∧ Disjoint B.restrictedSumset A) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Real.log n ^ (1 + c) ≤ (Erdos787.g ℝ n : ℝ) := by
  obtain ⟨c, hc, hev⟩ := h
  refine ⟨c, hc, hev.mono fun n hn => ?_⟩
  have h1 : ⌈Real.log n ^ (1 + c)⌉₊ ≤ Erdos787.g ℝ n := Erdos787.le_g hn
  calc Real.log n ^ (1 + c) ≤ (⌈Real.log n ^ (1 + c)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (Erdos787.g ℝ n : ℝ) := by exact_mod_cast h1

end OMA

theorem OMA.solution : type_of% @Erdos787.erdos_787.variants.sanders := by
  exact OMA.sanders_of_core OMA.sanders_core
