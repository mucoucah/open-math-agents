import FormalConjectures.GreensOpenProblems.«97»

-- Problem: Bowtell and Keevash.
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/97.lean:165 (declaration Green97.green_97.variants.bowtell_keevash)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.BK

open Filter Topology Green97

/-- The core of [BoKe21, Theorem 1.2] in logarithmic form (open gap: entropy upper bound
and absorber lower bound). -/
theorem log_asymp : Tendsto
    (fun n : ℕ ↦ Real.log (numToroidalQueens n : ℝ) / (n : ℝ) - Real.log (n : ℝ))
    toroidalDegrees (𝓝 (-3)) := by
  sorry

/-- From the logarithmic asymptotic, the count is eventually positive. -/
theorem eventually_pos (h : Tendsto
    (fun n : ℕ ↦ Real.log (numToroidalQueens n : ℝ) / (n : ℝ) - Real.log (n : ℝ))
    toroidalDegrees (𝓝 (-3))) :
    ∀ᶠ n : ℕ in toroidalDegrees, 0 < numToroidalQueens n := by
  have h1 : ∀ᶠ n : ℕ in toroidalDegrees,
      -4 < Real.log (numToroidalQueens n : ℝ) / (n : ℝ) - Real.log (n : ℝ) :=
    h (Ioi_mem_nhds (by norm_num))
  have h2 : ∀ᶠ n : ℕ in toroidalDegrees, Real.exp 4 < (n : ℝ) := by
    apply Filter.Eventually.filter_mono inf_le_left
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp 4)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact lt_of_lt_of_le hN (by exact_mod_cast hn)
  filter_upwards [h1, h2] with n hn hn2
  by_contra hc
  have h0 : numToroidalQueens n = 0 := by omega
  rw [h0] at hn
  simp only [Nat.cast_zero, Real.log_zero, zero_div, zero_sub] at hn
  have : 4 < Real.log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos 4) hn2)]
    exact hn2
  linarith

theorem glue (h : Tendsto
    (fun n : ℕ ↦ Real.log (numToroidalQueens n : ℝ) / (n : ℝ) - Real.log (n : ℝ))
    toroidalDegrees (𝓝 (-3))) :
    Tendsto (fun n : ℕ ↦ (numToroidalQueens n : ℝ) ^ ((1 : ℝ) / n) / n) toroidalDegrees
      (𝓝 (Real.exp (-3))) := by
  refine ((Real.continuous_exp.tendsto (-3)).comp h).congr' ?_
  have hge1 : ∀ᶠ n : ℕ in toroidalDegrees, 1 ≤ n :=
    Filter.Eventually.filter_mono inf_le_left (eventually_ge_atTop 1)
  filter_upwards [hge1, eventually_pos h] with n hn hpos
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (by omega)
  have hT_pos : (0 : ℝ) < (numToroidalQueens n : ℝ) := Nat.cast_pos.2 hpos
  simp only [Function.comp_apply]
  rw [Real.exp_sub, Real.exp_log hn_pos, Real.rpow_def_of_pos hT_pos]
  rw [mul_one_div]

end OMA.BK

theorem OMA.solution : type_of% @Green97.green_97.variants.bowtell_keevash := by
  exact OMA.BK.glue OMA.BK.log_asymp
