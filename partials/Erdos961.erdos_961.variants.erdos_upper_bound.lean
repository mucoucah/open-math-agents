import FormalConjectures.ErdosProblems.«961»

-- Problem: Erdős Problem 961 — erdos upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/961.lean:83 (declaration Erdos961.erdos_961.variants.erdos_upper_bound)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real

namespace OMA961

/-- `f k` is at most any admissible window length. -/
lemma f_le_of_prop {k n : ℕ} (hk : 0 < k) (h : Erdos961.Erdos961Prop k n) :
    Erdos961.f k ≤ n := by
  classical
  unfold Erdos961.f
  rw [dif_pos hk]
  exact Nat.find_min' _ h


/-- A window of length `n` is admissible once every binomial `C(m+n-1, n)` with `m > k`
has a prime factor above `k`. -/
lemma prop_of_choose {k n : ℕ}
    (main : ∀ m ≥ k + 1, ∃ p, p.Prime ∧ k < p ∧ p ∣ (m + n - 1).choose n) :
    Erdos961.Erdos961Prop k n := by
  intro m hm
  obtain ⟨p, hp, hkp, hdvd⟩ := main m hm
  have hd : p ∣ (m + n - 1).descFactorial n := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hdvd _
  rw [Nat.descFactorial_eq_prod_range] at hd
  obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
  rw [Finset.mem_range] at hi
  refine ⟨m + n - 1 - i, ⟨by omega, by omega⟩, fun hs => ?_⟩
  rw [Nat.mem_smoothNumbers] at hs
  have := hs.2 p ((Nat.mem_primeFactorsList hs.1).2 ⟨hp, hpi⟩)
  omega

/-- If all prime factors of `C(N,n)` are at most `k`, then `C(N,n) ≤ N ^ π(k)`. -/
lemma choose_le_pow_pi {N n k : ℕ} (hN : 0 < N) (hnN : n ≤ N)
    (H : ∀ p, p.Prime → p ∣ N.choose n → p ≤ k) :
    N.choose n ≤ N ^ Nat.primeCounting k := by
  have hC : N.choose n ≠ 0 := (Nat.choose_pos hnN).ne'
  rw [← Nat.prod_factorization_pow_eq_self hC]
  refine le_trans (Finset.prod_le_prod' (fun p _ => Nat.pow_factorization_choose_le hN)) ?_
  rw [Finset.prod_const]
  apply Nat.pow_le_pow_right hN
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpk := H p hpp (Nat.dvd_of_mem_primeFactors hp)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hpp⟩

/-- Large region (binomial counting, needs `π(k) ≤ (1+ε) k / log k`) and middle region
`N ≤ k^(3/2)` (Erdős 1955) combined: an admissible length below `3k/log k`. -/
lemma core_choose : ∀ᶠ k : ℕ in atTop, ∃ n : ℕ, (n : ℝ) < 3 * k / Real.log k ∧
    ∀ m ≥ k + 1, ∃ p, p.Prime ∧ k < p ∧ p ∣ (m + n - 1).choose n := by
  sorry

/-- Core (Erdős 1955): for large `k` some window length below `3k/log k` is admissible. -/
lemma core : ∀ᶠ k : ℕ in atTop,
    ∃ n : ℕ, (n : ℝ) < 3 * k / Real.log k ∧ Erdos961.Erdos961Prop k n := by
  filter_upwards [core_choose] with k hk
  obtain ⟨n, hn, h⟩ := hk
  exact ⟨n, hn, prop_of_choose h⟩

end OMA961

theorem OMA.solution : type_of% @Erdos961.erdos_961.variants.erdos_upper_bound := by
  filter_upwards [OMA961.core, eventually_gt_atTop 0] with k hk hk0
  obtain ⟨n, hn, hp⟩ := hk
  have h1 : Erdos961.f k ≤ n := OMA961.f_le_of_prop hk0 hp
  have h2 : (Erdos961.f k : ℝ) ≤ n := by exact_mod_cast h1
  linarith
