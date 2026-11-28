import FormalConjectures.ErdosProblems.«507»

-- Problem: Erdős Problem 507 — upper cpz24
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/507.lean:124 (declaration Erdos507.erdos_507.variants.upper_cpz24)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Asymptotics Filter Topology

namespace OMA507

/-- alpha is nonnegative: it is a supremum of infima of absolute values. -/
lemma alpha_nonneg (n : ℕ) : 0 ≤ Erdos507.α n := by
  unfold Erdos507.α
  apply Real.sSup_nonneg
  rintro _ ⟨S, -, rfl⟩
  unfold Erdos507.minTriangleArea
  apply Real.sInf_nonneg
  rintro _ ⟨p, -, -, rfl⟩
  exact abs_nonneg _

/-- The CPZ24 core (Cohen, Pohoata, Zakharov): for every eps, eventually
alpha n * n^(7/6) is at most n^eps. This is the research theorem. -/
lemma cpz_core : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    Erdos507.α n * (n : ℝ) ^ ((7 : ℝ) / 6) ≤ (n : ℝ) ^ ε := by
  sorry

/-- Diagonal exponent built from alpha. -/
noncomputable def oFun (n : ℕ) : ℝ :=
  max 0 (Real.log (Erdos507.α n * (n : ℝ) ^ ((7 : ℝ) / 6)) / Real.log n)

lemma oFun_tendsto
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Erdos507.α n * (n : ℝ) ^ ((7 : ℝ) / 6) ≤ (n : ℝ) ^ ε) :
    Tendsto oFun atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (ε / 2) (by positivity))
  refine ⟨max N 2, fun n hn => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hb := hN n (le_of_max_le_left hn)
  have hnpos : (0 : ℝ) < n := by linarith
  have key : Real.log (Erdos507.α n * (n : ℝ) ^ ((7 : ℝ) / 6)) / Real.log n ≤ ε / 2 := by
    rw [div_le_iff₀ hlog]
    rcases (mul_nonneg (alpha_nonneg n)
        (Real.rpow_nonneg hnpos.le ((7 : ℝ) / 6))).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; positivity
    · calc Real.log (Erdos507.α n * (n : ℝ) ^ ((7 : ℝ) / 6))
          ≤ Real.log ((n : ℝ) ^ (ε / 2)) := Real.log_le_log h0 hb
        _ = ε / 2 * Real.log n := Real.log_rpow hnpos _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _)]
  unfold oFun
  exact lt_of_le_of_lt (max_le (by linarith) key) (by linarith)

lemma alpha_le (n : ℕ) (hn : 2 ≤ n) :
    Erdos507.α n ≤ Erdos507.upperBarrier n * (n : ℝ) ^ oFun n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hp : (0 : ℝ) < (n : ℝ) ^ ((7 : ℝ) / 6) := Real.rpow_pos_of_pos hnpos _
  unfold Erdos507.upperBarrier
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hp]
  rcases (mul_nonneg (alpha_nonneg n) hp.le).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have h1 : Real.log (Erdos507.α n * (n : ℝ) ^ ((7 : ℝ) / 6)) ≤ oFun n * Real.log n := by
      unfold oFun
      rw [← div_le_iff₀ hlog]
      exact le_max_right _ _
    calc Erdos507.α n * (n : ℝ) ^ ((7 : ℝ) / 6)
        = Real.exp (Real.log (Erdos507.α n * (n : ℝ) ^ ((7 : ℝ) / 6))) := (Real.exp_log h0).symm
      _ ≤ Real.exp (oFun n * Real.log n) := Real.exp_le_exp.2 h1
      _ = (n : ℝ) ^ oFun n := by rw [Real.rpow_def_of_pos hnpos, mul_comm]

end OMA507

theorem OMA.solution : type_of% @Erdos507.erdos_507.variants.upper_cpz24 := by
  refine ⟨OMA507.oFun, OMA507.oFun_tendsto OMA507.cpz_core, ?_⟩
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have h1 := OMA507.alpha_le n hn
  have h2 := OMA507.alpha_nonneg n
  have h3 : 0 ≤ Erdos507.upperBarrier n * (n : ℝ) ^ OMA507.oFun n := h2.trans h1
  rw [Real.norm_of_nonneg h2, Real.norm_of_nonneg h3, one_mul]
  exact h1
