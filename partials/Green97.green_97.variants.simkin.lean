import FormalConjectures.GreensOpenProblems.«97»

-- Problem: Simkin's theorem.
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/97.lean:137 (declaration Green97.green_97.variants.simkin)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Topology

namespace OMA.Simkin

/-- Core (Simkin 2023, Thm 1.1): the normalised queens rate converges to a limit
strictly between exp(-1.9449) and exp(-1.94). Open gap of this partial. -/
theorem rate_limit : ∃ L : ℝ, Real.exp (-1.9449) < L ∧ L < Real.exp (-1.94) ∧
    Tendsto (fun n : ℕ ↦ (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) / n) atTop (𝓝 L) := by
  sorry

/-- Glue: a limit in the window determines alpha = -log L. -/
theorem glue (L : ℝ) (h1 : Real.exp (-1.9449) < L) (h2 : L < Real.exp (-1.94))
    (h3 : Tendsto (fun n : ℕ ↦ (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) / n) atTop (𝓝 L)) :
    ∃ α : ℝ, 1.94 < α ∧ α < 1.9449 ∧
      Tendsto (fun n : ℕ ↦ (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) / n) atTop
        (𝓝 (Real.exp (-α))) := by
  have hL : 0 < L := lt_trans (Real.exp_pos _) h1
  refine ⟨-Real.log L, ?_, ?_, ?_⟩
  · have := (Real.log_lt_log hL h2)
    rw [Real.log_exp] at this
    linarith
  · have := (Real.log_lt_log (Real.exp_pos _) h1)
    rw [Real.log_exp] at this
    linarith
  · rwa [neg_neg, Real.exp_log hL]

end OMA.Simkin

theorem OMA.solution : type_of% @Green97.green_97.variants.simkin := by
  obtain ⟨L, h1, h2, h3⟩ := OMA.Simkin.rate_limit
  exact OMA.Simkin.glue L h1 h2 h3
