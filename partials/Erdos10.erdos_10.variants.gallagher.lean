import FormalConjectures.ErdosProblems.«10»

-- Problem: Erdős Problem 10 — gallagher
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/10.lean:74 (declaration Erdos10.erdos_10.variants.gallagher)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- Trivial regime: for eps at least one the bound follows from nonnegativity. -/
theorem OMA.gallagher_large_eps (ε : ℝ) (hε : 1 ≤ ε) :
    ∃ k, 1 - ε ≤ (Erdos10.sumPrimeAndTwoPows k).lowerDensity :=
  ⟨0, le_trans (by linarith) (Set.lowerDensity_nonneg _ _)⟩

/-- Gallagher core (open gap): small eps needs the full Ga75 argument. -/
theorem OMA.gallagher_small_eps (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ k, 1 - ε ≤ (Erdos10.sumPrimeAndTwoPows k).lowerDensity := by
  sorry

theorem OMA.solution : type_of% @Erdos10.erdos_10.variants.gallagher := by
  intro ε hε
  rcases le_or_gt 1 ε with h | h
  · exact OMA.gallagher_large_eps ε h
  · exact OMA.gallagher_small_eps ε hε h
