import FormalConjectures.ErdosProblems.«968»

-- Problem: Erdős Problem 968 — infinite increasingTriples
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/968.lean:103 (declaration Erdos968.erdos_968.variants.infinite_increasingTriples)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Strategy. u n = p_n / (n+1). Chebyshev gives u n at most 2 log p_n for n at least 18.
If the gap p_(n+1) - p_n exceeds 3 log p_n, then p_(n+1) exceeds p_n + u n, which is
exactly u n < u (n+1). So two consecutive gaps above 3 log p give an increasing triple.
The only missing input is the existence of infinitely many such pairs of gaps
(Ford, Maynard, Tao 2018, chains of large gaps, k = 2; Erdős 1949 / Maier for this case). -/

namespace OMA.E968

open Real

/-- Chebyshev: the normalized n-th prime is at most twice the log of the n-th prime. -/
lemma u_le_two_log (n : ℕ) (hn : 18 ≤ n) :
    Erdos968.u n ≤ 2 * Real.log (Nat.nth Nat.Prime n) := by
  set m := Nat.nth Nat.Prime n with hm
  have hmn : n ≤ m := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).le_apply
  have hm18 : (18:ℝ) ≤ m := by exact_mod_cast le_trans hn hmn
  have hpi : Nat.primeCounting m = n + 1 :=
    Nat.count_nth_succ (fun hf => absurd hf Nat.infinite_setOfPred_prime)
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hcheb := Chebyshev.pi_ge m
  rw [div_le_iff₀ hlogm, hpi] at hcheb
  push_cast at hcheb
  have hl2 := Real.log_two_gt_d9
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h1 : Real.log ((m:ℝ) + 1) ≤ ((m:ℝ) + 1) / 8 - 1 + Real.log 8 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < ((m:ℝ) + 1) / 8)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith
  have h2 : (m:ℝ) * 0.6931471803 ≤ m * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le (by linarith)
  simp only [Erdos968.u]
  rw [div_le_iff₀ (by positivity)]
  have hl2' := Real.log_two_lt_d9
  nlinarith

/-- A gap above 3 log p_n forces u n < u (n+1). -/
lemma step_of_gap (n : ℕ) (hn : 18 ≤ n)
    (hg : 3 * Real.log (Nat.nth Nat.Prime n) ≤
      (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n) :
    Erdos968.u n < Erdos968.u (n + 1) := by
  have hu := u_le_two_log n hn
  have hp : (2 : ℝ) ≤ Nat.nth Nat.Prime n := by exact_mod_cast (Nat.prime_nth_prime n).two_le
  have hl : 0 < Real.log (Nat.nth Nat.Prime n) := Real.log_pos (by linarith)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [Erdos968.u, Nat.cast_add, Nat.cast_one] at hu ⊢
  rw [div_le_iff₀ hn1] at hu
  rw [div_lt_div_iff₀ hn1 (by positivity)]
  nlinarith

/-- Two consecutive prime gaps above 3 log p, infinitely often
(Ford, Maynard, Tao 2018 with k = 2; the case k = 2 goes back to Erdős and Maier).
This is the only missing input. -/
lemma two_large_gaps (N : ℕ) : ∃ n ≥ N,
    3 * Real.log (Nat.nth Nat.Prime n) ≤
      (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ∧
    3 * Real.log (Nat.nth Nat.Prime (n + 1)) ≤
      (Nat.nth Nat.Prime (n + 1 + 1) : ℝ) - Nat.nth Nat.Prime (n + 1) := by
  sorry

end OMA.E968

theorem OMA.solution : type_of% @Erdos968.erdos_968.variants.infinite_increasingTriples := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro M
  obtain ⟨n, hn, h1, h2⟩ := OMA.E968.two_large_gaps (M + 19)
  refine ⟨n, ⟨OMA.E968.step_of_gap n (by omega) h1, ?_⟩, by omega⟩
  exact OMA.E968.step_of_gap (n + 1) (by omega) h2
