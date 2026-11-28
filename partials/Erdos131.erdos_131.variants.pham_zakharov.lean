import FormalConjectures.ErdosProblems.«131»

-- Problem: Erdős Problem 131 — pham zakharov
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/131.lean:93 (declaration Erdos131.erdos_131.variants.pham_zakharov)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Topology

namespace OMA.Erdos131PZ

/-- Glue: an epsilon-form bound gives the o(1)-exponent form. -/
theorem glue (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (Erdos131.F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε)) :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, (Erdos131.F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + f N) := by
  refine ⟨fun N => max 0 (Real.logb N (Erdos131.F N) - 1 / 4), ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := eventually_atTop.mp (h (ε / 2) (by linarith))
    refine ⟨max M 2, fun N hN => ?_⟩
    have hNM : M ≤ N := le_trans (le_max_left _ _) hN
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
    have hb := hM N hNM
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _)]
    have key : Real.logb N (Erdos131.F N) ≤ 1 / 4 + ε / 2 := by
      rcases Nat.eq_zero_or_pos (Erdos131.F N) with h0 | hpos
      · rw [h0]; simp; linarith
      · have hpos' : (0 : ℝ) < Erdos131.F N := by exact_mod_cast hpos
        rw [Real.logb_le_iff_le_rpow (by linarith) hpos']
        exact hb
    apply max_lt hε; linarith
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    rcases Nat.eq_zero_or_pos (Erdos131.F N) with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero]; positivity
    · have hpos' : (0 : ℝ) < Erdos131.F N := by exact_mod_cast hpos
      calc (Erdos131.F N : ℝ) = (N : ℝ) ^ (Real.logb N (Erdos131.F N)) := by
            rw [Real.rpow_logb (by linarith) (by linarith) hpos']
        _ ≤ _ := by
            apply Real.rpow_le_rpow_of_exponent_le (by linarith)
            have := le_max_right 0 (Real.logb N (Erdos131.F N) - 1 / 4)
            linarith

/-- Core: the Pham-Zakharov bound in epsilon form (open: needs arXiv 2410.14624). -/
theorem core : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (Erdos131.F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

end OMA.Erdos131PZ

theorem OMA.solution : type_of% @Erdos131.erdos_131.variants.pham_zakharov := by
  exact OMA.Erdos131PZ.glue OMA.Erdos131PZ.core
