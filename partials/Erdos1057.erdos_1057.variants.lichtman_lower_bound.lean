import FormalConjectures.ErdosProblems.«1057»

-- Problem: Erdős Problem 1057 — lichtman lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1057.lean:111 (declaration Erdos1057.erdos_1057.variants.lichtman_lower_bound)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Lichtman1057

open Filter Real

/-- Sanity: Lichtman threshold 15/(32 sqrt e) is below 0.2844. -/
lemma lichtman_beta_lt : 15 / (32 * Real.sqrt (Real.exp 1)) < (0.2844 : ℝ) := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hs : (1.6483 : ℝ) < Real.sqrt (Real.exp 1) := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num at he ⊢
    linarith
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- Harman level times (1 - beta) exceeds the target exponent. -/
lemma exponent_margin : (0.3389 : ℝ) < (0.4736 : ℝ) * (1 - 0.2844) - 1 / 1000000 := by
  norm_num

/-- OPEN CORE (Lichtman Thm 1.1 with beta = 0.2844, fed into the AGP/Harman
construction at level 0.4736). This is the whole deep content. -/
lemma core : ∀ᶠ x : ℝ in atTop,
    x ^ ((0.4736 : ℝ) * (1 - 0.2844) - 1 / 1000000) ≤ Erdos1057.carmichaelCounting x := by
  sorry

end OMA.Lichtman1057

theorem OMA.solution : type_of% @Erdos1057.erdos_1057.variants.lichtman_lower_bound := by
  filter_upwards [OMA.Lichtman1057.core, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact lt_of_lt_of_le
    (Real.rpow_lt_rpow_of_exponent_lt hx1 OMA.Lichtman1057.exponent_margin) hx
