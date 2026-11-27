import FormalConjectures.ErdosProblems.«1057»

-- Problem: Erdős Problem 1057 — harman lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1057.lean:103 (declaration Erdos1057.erdos_1057.variants.harman_lower_bound)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Harman1057

open Filter Real

/-- Smooth shifted primes at exponent beta: the count of primes x < p <= 2x with p - 1
having all prime factors at most x ^ beta is at least c x / (log x) ^ C. -/
def SmoothShifted (β : ℝ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
    c * x / Real.log x ^ C ≤
      (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ β}.ncard : ℕ) : ℝ)

lemma threshold : 15 / (32 * Real.sqrt (Real.exp 1)) < (0.2844 : ℝ) := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hs : (1.6483 : ℝ) < Real.sqrt (Real.exp 1) := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num at he ⊢
    linarith
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

lemma exponent_gap : (0.33336704 : ℝ) < 0.4736 * (1 - 0.2844) - 1 / 1000000 := by
  norm_num

/-- The single open core: Lichtman Theorem 1.1 at beta = 0.2844 combined with the
Alford-Granville-Pomerance construction at Harman level 0.4736. -/
lemma core : ∀ᶠ x : ℝ in atTop,
    x ^ ((0.4736 : ℝ) * (1 - 0.2844) - 1 / 1000000) ≤ Erdos1057.carmichaelCounting x := by
  sorry

lemma of_core
    (h : ∀ᶠ x : ℝ in atTop,
      x ^ ((0.4736 : ℝ) * (1 - 0.2844) - 1 / 1000000) ≤ Erdos1057.carmichaelCounting x) :
    ∀ᶠ x in atTop, Erdos1057.carmichaelCounting x > x ^ (0.33336704 : ℝ) := by
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact lt_of_lt_of_le (Real.rpow_lt_rpow_of_exponent_lt hx1 exponent_gap) hx

end OMA.Harman1057

theorem OMA.solution : type_of% @Erdos1057.erdos_1057.variants.harman_lower_bound := by
  exact OMA.Harman1057.of_core OMA.Harman1057.core
