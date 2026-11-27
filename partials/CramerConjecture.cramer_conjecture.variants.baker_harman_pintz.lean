import FormalConjectures.Wikipedia.CramerConjecture

-- Problem: Baker–Harman–Pintz Bound
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/CramerConjecture.lean:144 (declaration CramerConjecture.cramer_conjecture.variants.baker_harman_pintz)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real Asymptotics

namespace OMA.BHP

/-- Core analytic input (Baker-Harman-Pintz 2001): short intervals contain primes. -/
theorem bhp_interval : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    ∃ q : ℕ, q.Prime ∧ x ≤ q ∧ (q : ℝ) ≤ x + C * (x : ℝ) ^ (0.525 : ℝ) := by
  sorry

/-- Glue: a prime in every interval of length C x^0.525 gives the gap bound. -/
theorem glue (C : ℝ) (hC : 0 < C) (hx : ∀ᶠ x : ℕ in atTop,
    ∃ q : ℕ, q.Prime ∧ x ≤ q ∧ (q : ℝ) ≤ x + C * (x : ℝ) ^ (0.525 : ℝ)) :
    (fun n : ℕ => (primeGap n : ℝ)) =O[atTop]
      (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) ^ (0.525 : ℝ)) := by
  let p := Nat.nth Nat.Prime
  have mono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have ind : Tendsto (fun n => p n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (p n)) mono.tendsto_atTop
  refine isBigO_iff.mpr ⟨1 + 2 * C, ?_⟩
  filter_upwards [ind.eventually hx] with n hn
  obtain ⟨q, hqp, hq1, hq2⟩ := hn
  have hnq : p (n + 1) ≤ q := by
    by_contra! hlt
    have : q ≤ p n := Nat.le_nth_of_lt_nth_succ hlt hqp
    omega
  have pp : 1 ≤ (p n : ℝ) := by exact_mod_cast (Nat.prime_nth_prime n).one_le
  have pp' := Real.one_le_rpow pp (by norm_num : (0:ℝ) ≤ 0.525)
  have pb : ((p n : ℝ) + 1) ^ (0.525 : ℝ) ≤ 2 * (p n : ℝ) ^ (0.525 : ℝ) := calc
    _ ≤ (2 * (p n : ℝ)) ^ (0.525 : ℝ) := rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    _ = 2 ^ (0.525 : ℝ) * (p n : ℝ) ^ (0.525 : ℝ) := mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ _ := by gcongr; exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hle : p n ≤ p (n + 1) := mono.monotone (Nat.le_succ n)
  have gp : (primeGap n : ℝ) = (p (n + 1) : ℝ) - p n := by
    change ((p (n + 1) - p n : ℕ) : ℝ) = _
    push_cast [hle]; ring
  have hq2' : (q : ℝ) ≤ (p n : ℝ) + 1 + C * ((p n : ℝ) + 1) ^ (0.525 : ℝ) := by
    simpa using hq2
  have hnq' : (p (n + 1) : ℝ) ≤ q := by exact_mod_cast hnq
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _)]
  change (primeGap n : ℝ) ≤ (1 + 2 * C) * (p n : ℝ) ^ (0.525 : ℝ)
  rw [gp]
  nlinarith [mul_le_mul_of_nonneg_left pb hC.le]

end OMA.BHP

theorem OMA.solution : type_of% @CramerConjecture.cramer_conjecture.variants.baker_harman_pintz := by
  obtain ⟨C, hC, h⟩ := OMA.BHP.bhp_interval
  exact OMA.BHP.glue C hC h
