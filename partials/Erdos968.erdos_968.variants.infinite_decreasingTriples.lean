import FormalConjectures.ErdosProblems.«968»

-- Problem: Erdős Problem 968 — infinite decreasingTriples
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/968.lean:115 (declaration Erdos968.erdos_968.variants.infinite_decreasingTriples)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA968D

open Filter Erdos968


/-- Maynard 2015: infinitely often three consecutive primes lie in a window of bounded length. -/
lemma maynard_three : ∃ B : ℕ, ∀ X : ℕ, ∃ i > X, Nat.nth Nat.Prime (i + 2) ≤ Nat.nth Nat.Prime i + B := by
  sorry

lemma prime_recip_unbounded (c : ℝ) : ∃ K : ℕ,
    c ≤ ∑ p ∈ Nat.primesBelow K, (1 : ℝ) / p := by
  by_contra h
  push Not at h
  apply not_summable_one_div_on_primes
  refine summable_of_sum_range_le (c := c) (fun n => ?_) (fun n => ?_)
  · unfold Set.indicator; split_ifs <;> positivity
  · have := h n
    rw [Nat.primesBelow, Finset.sum_filter] at this
    refine le_trans (le_of_eq ?_) this.le
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Set.indicator]

lemma totient_small (δ : ℝ) (hδ : 0 < δ) : ∃ a : ℕ, a ≠ 0 ∧ (Nat.totient a : ℝ) ≤ δ * a := by
  obtain ⟨K, hK⟩ := prime_recip_unbounded (Real.log (1 / δ))
  refine ⟨(primorial K), primorial_ne_zero K, ?_⟩
  have hpos : (0 : ℝ) < (primorial K) := by exact_mod_cast primorial_pos K
  have e := Nat.totient_mul_prod_primeFactors (primorial K)
  rw [primeFactors_primorial, ← primorial_eq_prod_primesLE, mul_comm ((primorial K))] at e
  have e2 : Nat.totient (primorial K) = ∏ p ∈ Nat.primesLE K, (p - 1) :=
    Nat.eq_of_mul_eq_mul_right (primorial_pos K) e
  have key : (Nat.totient (primorial K) : ℝ) / (primorial K)
      = ∏ p ∈ Nat.primesLE K, (1 - (1 : ℝ) / p) := by
    rw [e2, primorial_eq_prod_primesLE]
    push_cast
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have pp := Nat.prime_of_mem_primesLE hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast pp.one_lt.le
    rw [Nat.cast_sub pp.one_lt.le]
    field_simp
    push_cast; ring
  have bound : ∏ p ∈ Nat.primesLE K, (1 - (1 : ℝ) / p)
      ≤ Real.exp (- ∑ p ∈ Nat.primesLE K, (1 : ℝ) / p) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => Real.one_sub_le_exp_neg _)
    have pp := Nat.prime_of_mem_primesLE hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast pp.one_lt.le
    rw [sub_nonneg]; exact div_le_one_of_le₀ this (by positivity)
  have sub : ∑ p ∈ Nat.primesBelow K, (1 : ℝ) / p ≤ ∑ p ∈ Nat.primesLE K, (1 : ℝ) / p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have : Real.exp (- ∑ p ∈ Nat.primesLE K, (1 : ℝ) / p) ≤ δ := by
    calc Real.exp (- ∑ p ∈ Nat.primesLE K, (1 : ℝ) / p) ≤ Real.exp (- Real.log (1 / δ)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = δ := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  rw [← div_le_iff₀ hpos]
  linarith


lemma nth_prime_superlinear (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, (B : ℝ) * ((n : ℝ) + 1) < Nat.nth Nat.Prime n := by
  have hB : (0 : ℝ) < 2 * ((B : ℝ) + 1) := by positivity
  obtain ⟨a, ha0, ha⟩ := totient_small (1 / (2 * ((B : ℝ) + 1))) (by positivity)
  set C := Nat.primeCounting' (a + 1)
  have mono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  rw [Filter.eventually_atTop]
  refine ⟨2 * (B + 1) * (C + a) + B + 1 + (a + 1), fun n hn => ?_⟩
  have hp : a + 1 ≤ Nat.nth Nat.Prime n := by
    have : n ≤ Nat.nth Nat.Prime n := mono.id_le n
    omega
  obtain ⟨m, hm⟩ : ∃ m, Nat.nth Nat.Prime n = a + 1 + m := ⟨_, (Nat.add_sub_cancel' hp).symm⟩
  have h1 := Nat.primeCounting'_add_le (k := a + 1) ha0 (by omega) m
  rw [← hm, Nat.primeCounting'_nth_eq] at h1
  have h2 : (n : ℝ) ≤ C + (Nat.totient a : ℝ) * ((m / a : ℕ) : ℝ) + Nat.totient a := by
    have : ((n : ℕ) : ℝ) ≤ ((C + Nat.totient a * (m / a + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have hta : (Nat.totient a : ℝ) ≤ a := by exact_mod_cast Nat.totient_le a
  have hdiv : ((m / a : ℕ) : ℝ) * a ≤ m := by exact_mod_cast Nat.div_mul_le_self m a
  have h3 : (Nat.totient a : ℝ) * ((m / a : ℕ) : ℝ) ≤ 1 / (2 * ((B : ℝ) + 1)) * m := by
    calc (Nat.totient a : ℝ) * ((m / a : ℕ) : ℝ) ≤ 1 / (2 * ((B : ℝ) + 1)) * a * ((m / a : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right ha (by positivity)
      _ ≤ 1 / (2 * ((B : ℝ) + 1)) * m := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpm : (Nat.nth Nat.Prime n : ℝ) = a + 1 + m := by exact_mod_cast hm
  have h4 : 2 * ((B : ℝ) + 1) * n ≤ 2 * ((B : ℝ) + 1) * (C + a) + m := by
    have := mul_le_mul_of_nonneg_left (show (n : ℝ) ≤ C + a + 1 / (2 * ((B : ℝ) + 1)) * m by linarith)
      hB.le
    have e : 2 * ((B : ℝ) + 1) * (C + a + 1 / (2 * ((B : ℝ) + 1)) * m)
        = 2 * ((B : ℝ) + 1) * (C + a) + m := by field_simp
    linarith
  have hn' : (2 * (B + 1) * (C + a) + B + 1 : ℝ) ≤ n := by exact_mod_cast le_trans (by omega) hn
  rw [hpm]
  nlinarith [Nat.cast_nonneg (α := ℝ) B, Nat.cast_nonneg (α := ℝ) n]

lemma step (i B : ℕ) (h1 : Nat.nth Nat.Prime (i + 1) ≤ Nat.nth Nat.Prime i + B) (h2 : (B : ℝ) * ((i : ℝ) + 1) < Nat.nth Nat.Prime i) :
    u (i + 1) < u i := by
  unfold u
  have h1' : (Nat.nth Nat.Prime (i + 1) : ℝ) ≤ Nat.nth Nat.Prime i + B := by exact_mod_cast h1
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

end OMA968D

open OMA968D in
theorem OMA.solution : type_of% @Erdos968.erdos_968.variants.infinite_decreasingTriples := by
  obtain ⟨B, hB⟩ := maynard_three
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (nth_prime_superlinear B)
  have mono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  refine Set.infinite_of_forall_exists_gt fun X => ?_
  obtain ⟨i, hi, hle⟩ := hB (X + N)
  have a0 : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) := mono (by omega)
  have a1 : Nat.nth Nat.Prime (i + 1) < Nat.nth Nat.Prime (i + 2) := mono (by omega)
  refine ⟨i, ?_, by omega⟩
  refine ⟨step i B (by omega) (hN i (by omega)), ?_⟩
  have := step (i + 1) B (by rw [show i + 1 + 1 = i + 2 by rfl]; omega) (by have := hN (i + 1) (by omega); push_cast at this ⊢; linarith)
  simpa [add_assoc] using this
