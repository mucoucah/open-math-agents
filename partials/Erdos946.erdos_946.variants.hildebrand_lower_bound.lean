import FormalConjectures.ErdosProblems.«946»
import Mathlib

/-!
# Hildebrand's Lower Bound for Erdős Problem 946

We prove that `fun x => x / (Real.log (Real.log x)) ^ 3` is `O(erdos946Count)` as `x -> atTop`,
i.e. `# {n <= x : tau(n) = tau(n + 1)} >> x / (log log x)^3`.

Credits for adapted building blocks:
- Heath-Brown 7-point construction (`OMA946.HBSeven`): adapted from @marcusbuffett,
  `proofs/Erdos946.erdos_946.variants.heathbrown_lower_bound.R1.H2.lean` (PR #4914).
- Reconstruction & pigeonhole lemmas: adapted from @Javi (`reductions/Erdos946.erdos_946.variants.heathbrown_lower_bound.R1.lean`, PR #4680)
  and @physbuzz (`reductions/Erdos946.erdos_946.variants.hildebrand_lower_bound.R1.lean`, PR #12698).
- Mertens first-theorem upper bound style: adapted from @sebastianbachmaier (PR #1431) and
  `proofs/Erdos420.erdos_420.variants.rankin_frequently_lt_two.lean`.
-/

open Filter Real Erdos946 Finset
open scoped ArithmeticFunction.sigma BigOperators

namespace OMA946

/-! ## Module 0: Real-to-Nat wrapper (existing compiled lemmas) -/

lemma loglog_pos {y : ℝ} (hy : 16 ≤ y) : 0 < Real.log (Real.log y) := by
  apply Real.log_pos
  have h1 : Real.exp 1 < 16 := by
    have := Real.exp_one_lt_d9; linarith
  have : Real.log (Real.exp 1) < Real.log y :=
    Real.log_lt_log (Real.exp_pos 1) (by linarith)
  simpa using this

lemma loglog_mono {y z : ℝ} (hy : 16 ≤ y) (hyz : y ≤ z) :
    Real.log (Real.log y) ≤ Real.log (Real.log z) := by
  have hl : 0 < Real.log y := Real.log_pos (by linarith)
  exact Real.log_le_log hl (Real.log_le_log (by linarith) hyz)

theorem of_nat_core
    (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * ((N : ℝ) / (Real.log (Real.log N)) ^ 3) ≤
        (((Finset.range (N + 1)).filter (fun n => σ 0 n = σ 0 (n + 1))).card : ℝ)) :
    (fun x => x / (x.log.log)^3) =O[atTop] erdos946Count := by
  obtain ⟨c, hc, hN⟩ := h
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hN
  apply Asymptotics.IsBigO.of_bound (2 / c)
  filter_upwards [eventually_ge_atTop ((N0 : ℝ) + 16)] with x hx
  set N := ⌊x⌋₊ with hNdef
  have hx0 : 0 ≤ x := by have : (0:ℝ) ≤ N0 := Nat.cast_nonneg _; linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hN16 : (16 : ℝ) ≤ N := by
    have : (N0 : ℝ) + 16 ≤ N := by
      have h2 : ((N0 + 16 : ℕ) : ℝ) ≤ N := by
        rw [hNdef]; exact_mod_cast Nat.le_floor (by push_cast; linarith)
      push_cast at h2; linarith
    have : (0:ℝ) ≤ N0 := Nat.cast_nonneg _
    linarith
  have hN0le : N0 ≤ N := by
    have : (N0 : ℝ) ≤ N := by have : (0:ℝ) ≤ N0 := Nat.cast_nonneg _; linarith
    exact_mod_cast this
  have key := hN0 N hN0le
  have hLN := loglog_pos hN16
  have hLx := loglog_pos (le_trans hN16 hNx)
  have hmono := loglog_mono hN16 hNx
  have hcount : erdos946Count x =
      (((Finset.range (N + 1)).filter (fun n => σ 0 n = σ 0 (n + 1))).card : ℝ) := rfl
  rw [hcount, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx0 (pow_nonneg hLx.le 3)),
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hx2 : x ≤ 2 * N := by linarith
  have step1 : x / (Real.log (Real.log x)) ^ 3 ≤ 2 * N / (Real.log (Real.log N)) ^ 3 := by
    apply div_le_div₀ (by positivity) hx2 (by positivity)
    exact pow_le_pow_left₀ hLN.le hmono 3
  have step2 : 2 * (N : ℝ) / (Real.log (Real.log N)) ^ 3 =
      2 / c * (c * ((N : ℝ) / (Real.log (Real.log N)) ^ 3)) := by
    field_simp
  rw [step2] at step1
  calc x / (Real.log (Real.log x)) ^ 3 ≤ _ := step1
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)

/-! ## Module 1: Elementary Mertens 1 & 2 and Inverse-Square Tail -/

noncomputable def primeLogSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)

noncomputable def primeInvSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)

lemma inv_sq_tail_le (B T : ℕ) (hB : 0 < B) :
    (∑ p ∈ Finset.Ioc B T, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (B : ℝ) := by
  let shift : ℕ ↪ ℕ := ⟨fun k => B + k + 1, fun x y h => by dsimp at h; omega⟩
  have hIoc : (Finset.range (T - B)).map shift = Finset.Ioc B T := by
    ext p
    simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Ioc]
    change (∃ k : ℕ, k < T - B ∧ B + k + 1 = p) ↔ B < p ∧ p ≤ T
    exact ⟨by rintro ⟨k, hk, rfl⟩; omega, fun hp => ⟨p - B - 1, by omega, by omega⟩⟩
  rw [← hIoc, Finset.sum_map]
  change (∑ k ∈ Finset.range (T - B), (1 : ℝ) / ((B + k + 1 : ℕ) : ℝ) ^ 2) ≤ _
  let f (k : ℕ) : ℝ := 1 / ((B + k : ℕ) : ℝ)
  calc
    (∑ k ∈ Finset.range (T - B), (1 : ℝ) / ((B + k + 1 : ℕ) : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.range (T - B), (f k - f (k + 1)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        let c : ℝ := ((B + k : ℕ) : ℝ)
        have hc : 0 < c := by dsimp [c]; exact_mod_cast (show 0 < B + k by omega)
        have hshift : ((B + k + 1 : ℕ) : ℝ) = c + 1 := by simp [c]
        rw [hshift]
        change 1 / (c + 1) ^ 2 ≤ 1 / c - 1 / ((B + (k + 1) : ℕ) : ℝ)
        have hshift2 : ((B + (k + 1) : ℕ) : ℝ) = c + 1 := by
          rw [← Nat.add_assoc]; exact hshift
        rw [hshift2]
        calc
          1 / (c + 1) ^ 2 ≤ 1 / (c * (c + 1)) :=
            one_div_le_one_div_of_le (by positivity) (by nlinarith)
          _ = 1 / c - 1 / (c + 1) := by field_simp; ring
    _ = f 0 - f (T - B) := Finset.sum_range_sub' f _
    _ ≤ 1 / (B : ℝ) := by
        simpa [f] using sub_le_self (f 0) (show 0 ≤ f (T - B) by dsimp [f]; positivity)

lemma log_fact_ge (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤ Real.log (N.factorial : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (x := ((N : ℝ) + 1) / (N : ℝ)) (by positivity)
    rw [Real.log_div (by positivity) hNp.ne'] at h1
    have h2 : ((N : ℝ) + 1) / (N : ℝ) - 1 = 1 / (N : ℝ) := by field_simp; ring
    rw [h2] at h1
    have h3 : (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 hNp.le
      rw [mul_one_div_cancel hNp.ne'] at this
      exact this
    push_cast
    linarith

lemma log_fact_le_std (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N.factorial : ℝ) ≤ ((N : ℝ) + 1) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.one_sub_inv_le_log_of_pos (x := ((N : ℝ) + 1) / (N : ℝ)) (by positivity)
    rw [Real.log_div (by positivity) hNp.ne', inv_div] at h1
    have h2 : 1 - (N : ℝ) / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) := by field_simp; ring
    rw [h2] at h1
    have h3 : 1 ≤ ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    push_cast
    linarith

lemma sum_log_prime_divisors_le_log {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hprod : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hpos : ∀ p ∈ n.primeFactors, (p : ℝ) ≠ 0 := fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Real.log_prod hpos]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
  · rw [← Nat.cast_prod]; exact_mod_cast hprod

lemma mertens1_upper (N : ℕ) (hN : 1 ≤ N) :
    primeLogSum N ≤ Real.log (N : ℝ) + 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      ((N / p : ℕ) : ℝ) * Real.log (p : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) := by
    have h1 : ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((N / p : ℕ) : ℝ) * Real.log (p : ℝ) =
        ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
      have hcomm :
          ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
            ((Finset.Icc 1 N).filter (fun n => p ∣ n)).card • Real.log (p : ℝ) =
          ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
            if p ∣ n then Real.log (p : ℝ) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [← Finset.sum_filter, Finset.sum_const]
      have hcard (p : ℕ) (hp : p ∈ (Finset.range (N + 1)).filter Nat.Prime) :
          ((Finset.Icc 1 N).filter (fun n => p ∣ n)).card = N / p := by
        have hpp := (Finset.mem_filter.mp hp).2
        have hbij : (Finset.Icc 1 N).filter (fun n => p ∣ n) =
            (Finset.Icc 1 (N / p)).image (fun k => p * k) := by
          ext n
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
          constructor
          · rintro ⟨⟨hn1, hnN⟩, ⟨k, rfl⟩⟩
            have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun hk0 => by simp [hk0] at hn1
            exact ⟨k, ⟨hk1, (Nat.le_div_iff_mul_le hpp.pos).mpr (by rw [Nat.mul_comm]; exact hnN)⟩, rfl⟩
          · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
            refine ⟨⟨?_, ?_⟩, dvd_mul_right p k⟩
            · have := hpp.pos; nlinarith
            · rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hpp.pos).mp hkN
        rw [hbij, Finset.card_image_of_injective _ (mul_right_injective₀ hpp.ne_zero)]
        simp
      have hinner (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
          (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
            if p ∣ n then Real.log (p : ℝ) else 0) =
          ∑ p ∈ n.primeFactors, Real.log (p : ℝ) := by
        rw [← Finset.sum_filter]
        congr 1
        ext p
        simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
        constructor
        · rintro ⟨⟨_, hp⟩, hdvd⟩; exact ⟨hp, hdvd, by omega⟩
        · rintro ⟨hp, hdvd, _⟩
          exact ⟨⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) hdvd).trans hnN), hp⟩, hdvd⟩
      have hcomm2 :
          ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
            ((N / p : ℕ) : ℝ) * Real.log (p : ℝ) =
          ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
            ((Finset.Icc 1 N).filter (fun n => p ∣ n)).card • Real.log (p : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hcard p hp, nsmul_eq_mul]
      rw [hcomm2, hcomm]
      exact Finset.sum_congr rfl fun n hn => hinner n hn
    rw [h1]
    calc
      ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.primeFactors, Real.log (p : ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 N, Real.log (N : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 := (Finset.mem_Icc.mp hn).1
          have hnN := (Finset.mem_Icc.mp hn).2
          exact (sum_log_prime_divisors_le_log (by omega)).trans
            (Real.log_le_log (by positivity) (by exact_mod_cast hnN))
      _ = (N : ℝ) * Real.log (N : ℝ) := by simp
  have hlower : (N : ℝ) * primeLogSum N -
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) ≤
      (N : ℝ) * Real.log (N : ℝ) := by
    apply le_trans _ hsum
    unfold primeLogSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hlt := Nat.lt_mul_div_succ N hpp.pos
    have hle : (N : ℝ) / (p : ℝ) - 1 ≤ ((N / p : ℕ) : ℝ) := by
      have h1 : (N : ℝ) ≤ (p : ℝ) * (((N / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt.le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      rw [sub_le_iff_le_add, div_le_iff₀ hp0]
      linarith
    have hl : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    calc
      (N : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ)
        = ((N : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) := by ring
      _ ≤ ((N / p : ℕ) : ℝ) * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right hle hl
  have htheta : ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) ≤
      Real.log 4 * (N : ℝ) := by
    have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
    rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range] at h
    exact h
  have hlog4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have key : (N : ℝ) * primeLogSum N ≤ (N : ℝ) * (Real.log (N : ℝ) + 2) := by
    nlinarith
  exact le_of_mul_le_mul_left key hNr

lemma log_div_mul_pred_le (n : ℕ) (hn : 2 ≤ n) :
    Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      8 * (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnm1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsn1 : 0 < Real.sqrt ((n - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hnm1
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have h1 : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt (n : ℝ)) := by
      rw [Real.log_sqrt hn0.le]; ring
    have h2 := Real.log_le_sub_one_of_pos hsn
    linarith
  have hsub : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
  have hdiff : (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) *
      (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ)) = 1 := by
    have hsq1 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
    have hsq2 : Real.sqrt ((n - 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) - 1 := by
      rw [Real.sq_sqrt hnm1.le, hcast]
    nlinarith
  have hle_sqrt : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by rw [hcast]; linarith)
  have htel : 1 / (2 * (n : ℝ) * Real.sqrt (n : ℝ)) ≤
      1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ) := by
    have hlhs : 1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ) =
        1 / (Real.sqrt ((n - 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) *
          (Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ))) := by
      have hsum_pos : 0 < Real.sqrt (n : ℝ) + Real.sqrt ((n - 1 : ℕ) : ℝ) := by positivity
      field_simp [hsn.ne', hsn1.ne', hsum_pos.ne']
      nlinarith
    rw [hlhs]
    apply one_div_le_one_div_of_le (by positivity)
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
    nlinarith
  calc
    Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
      ≤ (2 * Real.sqrt (n : ℝ)) / ((n : ℝ) * ((n : ℝ) / 2)) := by
        apply div_le_div₀ (by positivity) hlog (by positivity) (by nlinarith)
    _ = 4 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
        have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
        field_simp [hn0.ne', hsn.ne']
        nlinarith
    _ = 8 * (1 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) := by ring
    _ ≤ 8 * (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left htel (by norm_num)

lemma sum_prime_log_div_mul_pred_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 8 := by
  have hsub : (Finset.range (N + 1)).filter Nat.Prime ⊆ Finset.Icc 2 N := by
    intro p hp
    obtain ⟨hr, hpp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.two_le, Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)⟩
  have hnn : ∀ n ∈ Finset.Icc 2 N, 0 ≤ Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact div_nonneg (Real.log_natCast_nonneg n) (by nlinarith)
  calc
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ n ∈ Finset.Icc 2 N, Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hnn n hn
    _ ≤ ∑ n ∈ Finset.Icc 2 N,
        8 * (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ)) :=
        Finset.sum_le_sum fun n hn => log_div_mul_pred_le n (Finset.mem_Icc.mp hn).1
    _ = 8 * ∑ n ∈ Finset.Icc 2 N,
        (1 / Real.sqrt ((n - 1 : ℕ) : ℝ) - 1 / Real.sqrt (n : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ 8 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rcases lt_or_ge N 2 with hN | hN
        · have hempty : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty (by omega)
          rw [hempty]; norm_num
        · let g (k : ℕ) : ℝ := 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)
          let shift : ℕ ↪ ℕ := ⟨fun k => k + 2, fun x y h => by dsimp at h; omega⟩
          have hIcc : (Finset.range (N - 1)).map shift = Finset.Icc 2 N := by
            ext n
            simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Icc]
            change (∃ k : ℕ, k < N - 1 ∧ k + 2 = n) ↔ 2 ≤ n ∧ n ≤ N
            exact ⟨by rintro ⟨k, hk, rfl⟩; omega, fun hn => ⟨n - 2, by omega, by omega⟩⟩
          rw [← hIcc, Finset.sum_map]
          have hcongr : ∑ k ∈ Finset.range (N - 1),
              (1 / Real.sqrt ((shift k - 1 : ℕ) : ℝ) - 1 / Real.sqrt ((shift k : ℕ) : ℝ)) =
              ∑ k ∈ Finset.range (N - 1), (g k - g (k + 1)) := by
            apply Finset.sum_congr rfl
            intro k _
            change 1 / Real.sqrt ((k + 2 - 1 : ℕ) : ℝ) - 1 / Real.sqrt ((k + 2 : ℕ) : ℝ) =
              1 / Real.sqrt ((k + 1 : ℕ) : ℝ) - 1 / Real.sqrt ((k + 1 + 1 : ℕ) : ℝ)
            have h1 : k + 2 - 1 = k + 1 := by omega
            have h2 : k + 1 + 1 = k + 2 := by omega
            rw [h1, h2]
          rw [hcongr, Finset.sum_range_sub' g (N - 1)]
          have hg0 : g 0 = 1 := by simp [g]
          have hgN : 0 ≤ g (N - 1) := by dsimp [g]; positivity
          linarith
    _ = 8 := by ring

lemma geom_tail_le {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    ∑ k ∈ Finset.Ico 2 (m + 1), (1 : ℝ) / (p : ℝ) ^ k ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rcases lt_or_ge m 2 with hm | hm
  · have : Finset.Ico 2 (m + 1) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this]; simp; positivity
  · let shift : ℕ ↪ ℕ := ⟨fun j => j + 2, fun x y h => by dsimp at h; omega⟩
    have hIco : (Finset.range (m - 1)).map shift = Finset.Ico 2 (m + 1) := by
      ext k
      simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Ico]
      change (∃ j : ℕ, j < m - 1 ∧ j + 2 = k) ↔ 2 ≤ k ∧ k < m + 1
      exact ⟨by rintro ⟨j, hj, rfl⟩; omega, fun hk => ⟨k - 2, by omega, by omega⟩⟩
    rw [← hIco, Finset.sum_map]
    have heq : ∑ j ∈ Finset.range (m - 1), (1 : ℝ) / (p : ℝ) ^ (shift j) =
        ((1 : ℝ) / (p : ℝ) ^ 2) * ∑ j ∈ Finset.range (m - 1), ((1 : ℝ) / (p : ℝ)) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (1 : ℝ) / (p : ℝ) ^ (j + 2) = (1 : ℝ) / (p : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ)) ^ j
      rw [pow_add, one_div, one_div, one_div, inv_pow, mul_inv, mul_comm]
    rw [heq, geom_sum_eq (show (1 : ℝ) / (p : ℝ) ≠ 1 by
      rw [ne_eq, div_eq_one_iff_eq hp0.ne']; linarith)]
    have hpow_nonneg : 0 ≤ ((1 : ℝ) / (p : ℝ)) ^ (m - 1) := by positivity
    have hfrac : (((1 : ℝ) / (p : ℝ)) ^ (m - 1) - 1) / ((1 : ℝ) / (p : ℝ) - 1) ≤
        1 / (1 - 1 / (p : ℝ)) := by
      rw [show (((1 : ℝ) / (p : ℝ)) ^ (m - 1) - 1) / ((1 : ℝ) / (p : ℝ) - 1) =
          (1 - ((1 : ℝ) / (p : ℝ)) ^ (m - 1)) / (1 - 1 / (p : ℝ)) by
        rw [← neg_div_neg_eq]; ring_nf]
      apply div_le_div_of_nonneg_right (by linarith)
      have : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
      linarith
    calc
      (1 : ℝ) / (p : ℝ) ^ 2 *
          ((((1 : ℝ) / (p : ℝ)) ^ (m - 1) - 1) / ((1 : ℝ) / (p : ℝ) - 1))
        ≤ (1 : ℝ) / (p : ℝ) ^ 2 * (1 / (1 - 1 / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
          field_simp [hp0.ne', hpm1.ne']

lemma mertens1_lower (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) - 9 ≤ primeLogSum N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfact := log_fact_ge N hN
  have hlogfact : Real.log (N.factorial : ℝ) ≤
      (N : ℝ) * primeLogSum N +
        (N : ℝ) * ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
    have hsub : (N.factorial).factorization.support ⊆ (Finset.range (N + 1)).filter Nat.Prime := by
      intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hdvd, _⟩ := hp
      have hle : p ≤ N := hpp.dvd_factorial.mp hdvd
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩
    calc
      ∑ p ∈ (N.factorial).factorization.support,
          ((N.factorial).factorization p : ℝ) * Real.log (p : ℝ)
        ≤ ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
            ((N.factorial).factorization p : ℝ) * Real.log (p : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p _ _
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
      _ ≤ ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
            ((N : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) +
              (N : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpp := (Finset.mem_filter.mp hp).2
          have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
          have hv : ((N.factorial).factorization p : ℝ) ≤
              (N : ℝ) / (p : ℝ) + (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
            rw [Nat.factorization_factorial hpp (Nat.lt_succ_of_le (Nat.log_le_self p N))]
            push_cast
            have h1 : ∑ k ∈ Finset.Ico 1 (N + 1), ((N / p ^ k : ℕ) : ℝ) ≤
                ∑ k ∈ Finset.Ico 1 (N + 1), (N : ℝ) / (p : ℝ) ^ k := by
              apply Finset.sum_le_sum
              intro k _
              have := Nat.cast_div_le (α := ℝ) (m := N) (n := p ^ k)
              push_cast at this
              exact this
            have hsplit : Finset.Ico 1 (N + 1) = insert 1 (Finset.Ico 2 (N + 1)) := by
              ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
            rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at h1
            simp only [pow_one] at h1
            have htail : ∑ k ∈ Finset.Ico 2 (N + 1), (N : ℝ) / (p : ℝ) ^ k ≤
                (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
              have heq : ∑ k ∈ Finset.Ico 2 (N + 1), (N : ℝ) / (p : ℝ) ^ k =
                  (N : ℝ) * ∑ k ∈ Finset.Ico 2 (N + 1), (1 : ℝ) / (p : ℝ) ^ k := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
              rw [heq, show (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) =
                  (N : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) by ring]
              exact mul_le_mul_of_nonneg_left (geom_tail_le hpp.two_le N) hNr.le
            rw [hsplit, Finset.sum_insert (by simp)]
            simp only [pow_one]
            linarith
          calc
            ((N.factorial).factorization p : ℝ) * Real.log (p : ℝ)
              ≤ ((N : ℝ) / (p : ℝ) + (N : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) * Real.log (p : ℝ) :=
                mul_le_mul_of_nonneg_right hv hlogp
            _ = (N : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) +
                (N : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by ring
      _ = (N : ℝ) * primeLogSum N +
            (N : ℝ) * ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
  have htail8 := sum_prime_log_div_mul_pred_le N
  have key : (N : ℝ) * (Real.log (N : ℝ) - 9) ≤ (N : ℝ) * primeLogSum N := by
    nlinarith
  exact le_of_mul_le_mul_left key hNr

lemma mertens1_abs (N : ℕ) (hN : 1 ≤ N) :
    |primeLogSum N - Real.log (N : ℝ)| ≤ 9 := by
  rw [abs_le]
  exact ⟨by linarith [mertens1_lower N hN], by linarith [mertens1_upper N hN]⟩

lemma primeLogSum_succ (n : ℕ) :
    primeLogSum (n + 1) - primeLogSum n =
      if (n + 1).Prime then Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) else 0 := by
  unfold primeLogSum
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · rw [Finset.sum_insert (by simp)]; ring
  · ring

lemma primeInvSum_succ (n : ℕ) :
    primeInvSum (n + 1) - primeInvSum n =
      if (n + 1).Prime then (1 : ℝ) / ((n + 1 : ℕ) : ℝ) else 0 := by
  unfold primeInvSum
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · rw [Finset.sum_insert (by simp)]; ring
  · ring

lemma primeInvSum_eq_abel (N : ℕ) (hN : 2 ≤ N) :
    primeInvSum N = primeLogSum N / Real.log (N : ℝ) +
      ∑ n ∈ Finset.Ico 2 N, primeLogSum n *
        (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
    unfold primeInvSum primeLogSum
    rw [show (Finset.range (2 + 1)).filter Nat.Prime = {2} by decide]
    simp only [Finset.sum_singleton, Nat.cast_ofNat]
    have hl2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hl2]
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN]
    have hstep : primeInvSum (N + 1) - primeInvSum N =
        (primeLogSum (N + 1) - primeLogSum N) / Real.log ((N + 1 : ℕ) : ℝ) := by
      rw [primeInvSum_succ, primeLogSum_succ]
      split_ifs
      · have hl : Real.log ((N + 1 : ℕ) : ℝ) ≠ 0 :=
          (Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))).ne'
        field_simp [hl]
      · simp
    have hl1 : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    have hl2 : Real.log ((N + 1 : ℕ) : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))).ne'
    have halg : primeLogSum (N + 1) / Real.log ((N + 1 : ℕ) : ℝ) +
        primeLogSum N * (1 / Real.log (N : ℝ) - 1 / Real.log ((N + 1 : ℕ) : ℝ)) =
        primeLogSum N / Real.log (N : ℝ) +
        (primeLogSum (N + 1) - primeLogSum N) / Real.log ((N + 1 : ℕ) : ℝ) := by
      field_simp [hl1, hl2]; ring
    linarith

lemma mertens2_abs (N : ℕ) (hN : 2 ≤ N) :
    |primeInvSum N - Real.log (Real.log (N : ℝ))| ≤ 32 := by
  rw [primeInvSum_eq_abel N hN]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlog2 : (0.69 : ℝ) < Real.log (2 : ℝ) := by
    have := Real.log_two_gt_d9; linarith
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by linarith
  have hlog2_le : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN2
  let E (n : ℕ) : ℝ := primeLogSum n - Real.log (n : ℝ)
  have hE : ∀ n, 1 ≤ n → |E n| ≤ 9 := fun n hn => mertens1_abs n hn
  have hmain :
      ∑ n ∈ Finset.Ico 2 N, primeLogSum n *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
        (∑ n ∈ Finset.Ico 2 N, Real.log (n : ℝ) *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ))) +
        (∑ n ∈ Finset.Ico 2 N, E n *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [E]; ring
  rw [hmain]
  have hdiff_nonneg (n : ℕ) (hn : 2 ≤ n) :
      0 ≤ 1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ) := by
    have hl1 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hl2 : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show n ≤ n + 1 by omega))
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hl1 hl2)
  have htel_inv :
      ∑ n ∈ Finset.Ico 2 N, (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
        1 / Real.log (2 : ℝ) - 1 / Real.log (N : ℝ) := by
    let f (k : ℕ) : ℝ := 1 / Real.log ((k + 2 : ℕ) : ℝ)
    let shift : ℕ ↪ ℕ := ⟨fun k => k + 2, fun x y h => by dsimp at h; omega⟩
    have hIco : (Finset.range (N - 2)).map shift = Finset.Ico 2 N := by
      ext n
      simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Ico]
      change (∃ k : ℕ, k < N - 2 ∧ k + 2 = n) ↔ 2 ≤ n ∧ n < N
      exact ⟨by rintro ⟨k, hk, rfl⟩; omega, fun hn => ⟨n - 2, by omega, by omega⟩⟩
    rw [← hIco, Finset.sum_map]
    have hc : ∑ k ∈ Finset.range (N - 2),
        (1 / Real.log ((shift k : ℕ) : ℝ) - 1 / Real.log ((shift k + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.range (N - 2), (f k - f (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      change 1 / Real.log ((k + 2 : ℕ) : ℝ) - 1 / Real.log ((k + 2 + 1 : ℕ) : ℝ) =
        1 / Real.log ((k + 2 : ℕ) : ℝ) - 1 / Real.log ((k + 1 + 2 : ℕ) : ℝ)
      have : k + 1 + 2 = k + 2 + 1 := by omega
      rw [this]
    rw [hc, Finset.sum_range_sub' f (N - 2)]
    dsimp only [f]
    rw [zero_add, show N - 2 + 2 = N by omega]
    norm_num
  have htel_loglog :
      ∑ n ∈ Finset.Ico 2 N, (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) -
          Real.log (Real.log (n : ℝ))) =
        Real.log (Real.log (N : ℝ)) - Real.log (Real.log (2 : ℝ)) := by
    let f (k : ℕ) : ℝ := Real.log (Real.log ((k + 2 : ℕ) : ℝ))
    let shift : ℕ ↪ ℕ := ⟨fun k => k + 2, fun x y h => by dsimp at h; omega⟩
    have hIco : (Finset.range (N - 2)).map shift = Finset.Ico 2 N := by
      ext n
      simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Ico]
      change (∃ k : ℕ, k < N - 2 ∧ k + 2 = n) ↔ 2 ≤ n ∧ n < N
      exact ⟨by rintro ⟨k, hk, rfl⟩; omega, fun hn => ⟨n - 2, by omega, by omega⟩⟩
    rw [← hIco, Finset.sum_map]
    have hc : ∑ k ∈ Finset.range (N - 2),
        (Real.log (Real.log ((shift k + 1 : ℕ) : ℝ)) - Real.log (Real.log ((shift k : ℕ) : ℝ))) =
        ∑ k ∈ Finset.range (N - 2), (f (k + 1) - f k) := by
      apply Finset.sum_congr rfl
      intro k _
      change Real.log (Real.log ((k + 2 + 1 : ℕ) : ℝ)) - Real.log (Real.log ((k + 2 : ℕ) : ℝ)) =
        Real.log (Real.log ((k + 1 + 2 : ℕ) : ℝ)) - Real.log (Real.log ((k + 2 : ℕ) : ℝ))
      have : k + 1 + 2 = k + 2 + 1 := by omega
      rw [this]
    rw [hc, Finset.sum_range_sub f (N - 2)]
    dsimp only [f]
    rw [zero_add, show N - 2 + 2 = N by omega]
    norm_num
  have hstep_cmp (n : ℕ) (hn : 2 ≤ n) :
      Real.log (n : ℝ) * (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
        Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ)) ∧
      Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ)) ≤
        Real.log (n : ℝ) * (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) +
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by
    have hl1 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hl2 : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
    have hrat_pos : 0 < Real.log ((n + 1 : ℕ) : ℝ) / Real.log (n : ℝ) := div_pos hl2 hl1
    have hlo := Real.one_sub_inv_le_log_of_pos hrat_pos
    have hhi := Real.log_le_sub_one_of_pos hrat_pos
    rw [Real.log_div hl2.ne' hl1.ne', inv_div] at hlo
    rw [Real.log_div hl2.ne' hl1.ne'] at hhi
    have hstep_log : Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 := by
      have h1 := Real.log_le_sub_one_of_pos (x := ((n + 1 : ℕ) : ℝ) / (n : ℝ)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h1
      have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have h2 : ((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1 = 1 / (n : ℝ) := by push_cast; field_simp; ring
      rw [h2] at h1
      have h3 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have he1 : Real.log (n : ℝ) * (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
        1 - Real.log (n : ℝ) / Real.log ((n + 1 : ℕ) : ℝ) := by
      field_simp [hl1.ne', hl2.ne']
    have he2 : Real.log ((n + 1 : ℕ) : ℝ) / Real.log (n : ℝ) - 1 -
        (1 - Real.log (n : ℝ) / Real.log ((n + 1 : ℕ) : ℝ)) =
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by
      field_simp [hl1.ne', hl2.ne']
    have hd_nn := hdiff_nonneg n hn
    constructor
    · rw [he1]; exact hlo
    · rw [he1]
      have hmul : (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
          1 * (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hstep_log hd_nn
      linarith
  have hsum_lo :
      ∑ n ∈ Finset.Ico 2 N, Real.log (n : ℝ) *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
        Real.log (Real.log (N : ℝ)) - Real.log (Real.log (2 : ℝ)) := by
    rw [← htel_loglog]
    exact Finset.sum_le_sum fun n hn => (hstep_cmp n (Finset.mem_Ico.mp hn).1).1
  have hsum_hi :
      Real.log (Real.log (N : ℝ)) - Real.log (Real.log (2 : ℝ)) ≤
        (∑ n ∈ Finset.Ico 2 N, Real.log (n : ℝ) *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ))) +
        (1 / Real.log (2 : ℝ) - 1 / Real.log (N : ℝ)) := by
    rw [← htel_loglog, ← htel_inv, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun n hn => (hstep_cmp n (Finset.mem_Ico.mp hn).1).2
  have hE_sum :
      |∑ n ∈ Finset.Ico 2 N, E n *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ))| ≤
        9 / Real.log (2 : ℝ) := by
    calc
      |∑ n ∈ Finset.Ico 2 N, E n *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ))|
        ≤ ∑ n ∈ Finset.Ico 2 N, |E n *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ico 2 N, 9 *
          (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [abs_mul, abs_of_nonneg (hdiff_nonneg n (Finset.mem_Ico.mp hn).1)]
          exact mul_le_mul_of_nonneg_right (hE n (by have := (Finset.mem_Ico.mp hn).1; omega))
            (hdiff_nonneg n (Finset.mem_Ico.mp hn).1)
      _ = 9 * (1 / Real.log (2 : ℝ) - 1 / Real.log (N : ℝ)) := by
          rw [← Finset.mul_sum, htel_inv]
      _ ≤ 9 / Real.log (2 : ℝ) := by
          have h1 : 0 ≤ 9 / Real.log (N : ℝ) := by positivity
          have h2 : 9 * (1 / Real.log (2 : ℝ) - 1 / Real.log (N : ℝ)) =
              9 / Real.log (2 : ℝ) - 9 / Real.log (N : ℝ) := by ring
          linarith
  have hhead : |primeLogSum N / Real.log (N : ℝ)| ≤ 1 + 9 / Real.log (2 : ℝ) := by
    have h1 : primeLogSum N / Real.log (N : ℝ) = 1 + E N / Real.log (N : ℝ) := by
      dsimp [E]; field_simp [hlogN.ne']; ring
    rw [h1]
    calc
      |1 + E N / Real.log (N : ℝ)| ≤ |1| + |E N / Real.log (N : ℝ)| := abs_add_le _ _
      _ = 1 + |E N| / Real.log (N : ℝ) := by
          rw [abs_one, abs_div, abs_of_pos hlogN]
      _ ≤ 1 + 9 / Real.log (2 : ℝ) := by
          have hEN : |E N| ≤ 9 := hE N (by omega)
          have hdiv : |E N| / Real.log (N : ℝ) ≤ 9 / Real.log (2 : ℝ) :=
            div_le_div₀ (by norm_num) hEN hlog2_pos hlog2_le
          linarith
  have hll2 : |Real.log (Real.log (2 : ℝ))| ≤ 1 := by
    rw [abs_le]
    have h2 : Real.log (2 : ℝ) ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have hupper : Real.log (Real.log (2 : ℝ)) ≤ 0 := Real.log_nonpos hlog2_pos.le h2
    have hlower : -1 ≤ Real.log (Real.log (2 : ℝ)) := by
      have h1 := Real.one_sub_inv_le_log_of_pos hlog2_pos
      have hinv : (Real.log (2 : ℝ))⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hlog2_pos (by norm_num)]; linarith
      linarith
    exact ⟨hlower, by linarith⟩
  have hinv2 : 1 / Real.log (2 : ℝ) ≤ 1.5 := by
    rw [div_le_iff₀ hlog2_pos]; linarith
  have h9inv2 : 9 / Real.log (2 : ℝ) ≤ 13.5 := by
    rw [div_le_iff₀ hlog2_pos]; linarith
  have hinvN : 0 ≤ 1 / Real.log (N : ℝ) := by positivity
  rw [abs_le] at hE_sum hhead hll2 ⊢
  constructor <;> linarith

/-! ## Module 2: Heath-Brown 7-Point Construction, Pigeonhole, and Disjoint Reconstruction -/

namespace HBSeven

private def num : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: l => p ^ e * num l

private def cnt : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (_, e) :: l => (e + 1) * cnt l

private def valid : List (ℕ × ℕ) → Bool
  | [] => true
  | (p, e) :: l => decide p.Prime && decide ((p ^ e).Coprime (num l)) && valid l

private theorem count_factors (l : List (ℕ × ℕ)) (h : valid l = true) : σ 0 (num l) = cnt l := by
  induction l with
  | nil => simp [num, cnt]
  | cons entry l ih =>
    obtain ⟨p, e⟩ := entry
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [num, cnt, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h.1.2,
      ArithmeticFunction.sigma_zero_apply_prime_pow h.1.1, ih h.2]

private def perm : Fin 7 → ℕ := ![4, 1, 0, 5, 2, 3, 6]
private def primes : Fin 8 → ℕ := ![2, 3, 5, 7, 11, 13, 17, 19]
private def factors (i : Fin 7) (j : Option (Fin 7)) : List (ℕ × ℕ) :=
  List.ofFn fun h : Fin 8 =>
    let e := (perm i) ^^^ h.val
    (primes h, match j with | none => e | some k => e - ((perm k) ^^^ h.val))

private def part (i : Fin 7) := num (factors i none)
private def cofactor (i j : Fin 7) := num (factors i (some j))

private theorem divisor_balance (i j : Fin 7) :
    σ 0 (part i) * σ 0 (cofactor j i) = σ 0 (part j) * σ 0 (cofactor i j) := by
  have hv : ∀ (a : Fin 7) (b : Option (Fin 7)), valid (factors a b) = true := by decide +kernel
  simp only [part, cofactor, count_factors _ (hv _ _)]
  exact (show ∀ (a b : Fin 7), cnt (factors a none) * cnt (factors b (some a)) =
    cnt (factors b none) * cnt (factors a (some b)) from by decide +kernel) i j

private def shift : ℕ :=
  54293842776972455825610115246506857935407049442876485652587138012176197082363848973554568012581081827954864143527210512938933489767457530604277755014021315536257675889875856367945106079919662563014127674578992178723872970335872100925430927720457406693350569276823257365284362443006630129704144511962118462291104914955408003372875141121624418101503642821350647842907928268690580084906604888035965316138404279493095257134509918541137864534943561550794369402096222596150394455160059058953217298544590998125598185796832629109892005212820910117967862854146987213746066420750477479722837593144154610950156864012238889525018273310353119783150036757029237425659673275861230853898376237600628019292815889704196124192996825798597824822703431526904911463602730558907099515579759300099298464185970555616211086404359182601995655034323955503390770129057984204606463996493798516859652130992412530124133397604877068692508104247154554534836892118736190835613779723932902958353710909260476791982089838630920793942842306993389940269452424494848267739230228638998023588104815340649268742217725857500174050311423085334934277896809642035288295759874805353895560140979280224676483666067700033338650803153437485439508855751958403906358326017110943693026615909669169156690847093985881233901893229702887820215130978488844439471972456419940958404602072356450737039948662546043495035836446172006098625119764119954835234345226701601815995162586333907319972491572661369128910614668197591575144019038772864091185985577459818348260091912791873705117927670700227266886703500766346159498021235927261818219153500000000

private def offsets : Fin 7 → ℕ :=
  ![1289242341647646750000, 1087769754549337068139257076750,
    3017252254998615707186270832675,
    78354300210436852307898467208663359629652331708067500000,
    78354300210436852307898467226043170707260260150637903788,
    156708600420873704615796934423592430221811711620882837880,
    391771501052184261539492336043316795831721061998053080000]

def pt (i : Fin 7) : ℕ := shift + offsets i

private def cert (a b u v u' v' : ℕ) : Bool :=
  let d := b - a
  let f := d / (u.gcd v)
  let x := a / (u * f)
  let y := b / (v * f)
  decide (d = a.gcd b ∧ (u * f) * x = a ∧ (v * f) * y = b ∧ u' * x = a / d ∧ v' * y = b / d ∧
    u.Coprime f ∧ v.Coprime f ∧ (u * f).Coprime x ∧ (v * f).Coprime y ∧
    u'.Coprime x ∧ v'.Coprime y)

private theorem cert_sound {a b u v u' v' : ℕ} (h : cert a b u v u' v' = true)
    (balance : σ 0 u * σ 0 v' = σ 0 v * σ 0 u') :
    b - a = a.gcd b ∧ σ 0 a * σ 0 (b / (b - a)) = σ 0 b * σ 0 (a / (b - a)) := by
  let f := (b - a) / (u.gcd v)
  let x := a / (u * f)
  let y := b / (v * f)
  change decide ((b - a) = a.gcd b ∧ (u * f) * x = a ∧ (v * f) * y = b ∧
    u' * x = a / (b - a) ∧ v' * y = b / (b - a) ∧ u.Coprime f ∧ v.Coprime f ∧
    (u * f).Coprime x ∧ (v * f).Coprime y ∧ u'.Coprime x ∧ v'.Coprime y) = true at h
  obtain ⟨g, ax, by', qx, qy, uf, vf, ux, vy, ux', vy'⟩ := of_decide_eq_true h
  refine ⟨g, ?_⟩
  rw [← qy, ← qx, ← ax, ← by']
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ux,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime vy,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime uf,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime vf,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ux',
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime vy']
  calc
    _ = (σ 0 u * σ 0 v') * (σ 0 f * σ 0 x * σ 0 y) := by ring
    _ = _ := by rw [balance]; ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem seven_spec :
    StrictMono pt ∧ (∀ i, 0 < pt i) ∧
      ∀ i j, i < j →
        pt j - pt i = (pt i).gcd (pt j) ∧
        σ 0 (pt i) * σ 0 (pt j / (pt j - pt i)) = σ 0 (pt j) * σ 0 (pt i / (pt j - pt i)) := by
  have checked : ∀ i j : Fin 7, i < j →
      cert (pt i) (pt j) (part i) (part j) (cofactor i j) (cofactor j i) = true := by
    decide +kernel
  refine ⟨?_, ?_, fun i j h => cert_sound (checked i j h) (divisor_balance i j)⟩
  · exact fun i j h => Nat.add_lt_add_left
      ((show ∀ a b : Fin 7, a < b → offsets a < offsets b from by decide +kernel) i j h) _
  · intro i
    exact Nat.add_pos_left (show 0 < shift from by decide +kernel) _

end HBSeven

lemma tau_squarefree {q : ℕ} (hq : Squarefree q) : σ 0 q = 2 ^ q.primeFactors.card := by
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hq.ne_zero]
  calc
    _ = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hq
        (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := by simp

lemma seven_collision (c : Fin 7 → ℕ) (hpos : ∀ i, 0 < c i) (hsum : (∑ i, c i) ≤ 27) :
    ∃ i j, i < j ∧ c i = c j := by
  by_contra fail
  have inj : Function.Injective c := by
    intro i j eqn
    rcases lt_trichotomy i j with h | h | h
    · exact (fail ⟨i, j, h, eqn⟩).elim
    · exact h
    · exact (fail ⟨j, i, h, eqn.symm⟩).elim
  let S := (Finset.univ : Finset (Fin 7)).image c
  have card : S.card = 7 := by simp [S, Finset.card_image_of_injective _ inj]
  let f := S.orderEmbOfFin card
  have base (i : Fin 7) : 0 < f i := by
    have hm := S.orderEmbOfFin_mem card i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact hj ▸ hpos j
  have bound (j : ℕ) (hj : j < 7) : j + 1 ≤ f ⟨j, hj⟩ := by
    induction j with
    | zero => exact base _
    | succ j ih =>
      have hlt : f ⟨j, by omega⟩ < f ⟨j + 1, hj⟩ := f.strictMono (Nat.lt_succ_self j)
      have hh := ih (by omega)
      omega
  have total : (∑ i, f i) = ∑ i, c i := by
    calc
      (∑ i, f i) = ∑ a ∈ S, a := by
        rw [← S.image_orderEmbOfFin_univ card, Finset.sum_image]
        exact f.injective.injOn
      _ = _ := Finset.sum_image inj.injOn
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 7)))
    (fun i _ => bound i.val i.isLt)
  have ex : (∑ i : Fin 7, ((i : ℕ) + 1)) = 28 := by decide +kernel
  rw [ex, total] at hh
  omega

lemma adjacent_consec {a b d n p q u v : ℕ} (ab : a < b) (ddef : d = b - a)
    (dg : d = a.gcd b)
    (key : σ 0 a * σ 0 (b / d) = σ 0 b * σ 0 (a / d))
    (pv : p * v = a * n + 1) (qu : q * u = b * n + 1)
    (pt : σ 0 p = σ 0 a) (qt : σ 0 q = σ 0 b) (uv : σ 0 u = σ 0 v)
    (bp : (b / d).Coprime p) (aq : (a / d).Coprime q)
    (vc : ((b / d) * p).Coprime v) (uc : ((a / d) * q).Coprime u) :
    σ 0 ((a / d) * (b * n + 1)) = σ 0 ((a / d) * (b * n + 1) + 1) := by
  have ad : d ∣ a := dg ▸ Nat.gcd_dvd_left a b
  have bd : d ∣ b := dg ▸ Nat.gcd_dvd_right a b
  have dp : 0 < d := by omega
  have da := Nat.div_mul_cancel ad
  have db := Nat.div_mul_cancel bd
  have quot : a / d + 1 = b / d := by
    apply Nat.eq_of_mul_eq_mul_right dp
    rw [Nat.add_mul, one_mul, da, db]
    omega
  have cross : a / d * b = b / d * a := by
    calc
      _ = a / d * ((b / d) * d) := by rw [db]
      _ = b / d * ((a / d) * d) := by ring
      _ = _ := by rw [da]
  have consec : (a / d) * (b * n + 1) + 1 = (b / d) * (a * n + 1) := by
    simp only [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc]
    rw [cross]
    omega
  rw [consec, ← qu, ← pv, ← Nat.mul_assoc, ← Nat.mul_assoc]
  have mul := ArithmeticFunction.isMultiplicative_sigma (k := 0)
  rw [mul.map_mul_of_coprime uc, mul.map_mul_of_coprime vc,
    mul.map_mul_of_coprime aq, mul.map_mul_of_coprime bp, pt, qt, uv]
  nlinarith only [congrArg (fun x => x * σ 0 v) key]

/-- Given a fixed cutoff `z0` above `pt 6` and the 7 fixed primes `q_i`, if `m` and `m'`
both decompose `a_i * n + 1 = b_i * m_i * v_i` with `m_i` squarefree on `(z0, z1]` and
`v_i` having all prime factors `> z1`, then `m = m'`. -/
lemma multiplier_unique_of_decomp {a b z0 z1 n : ℕ} {m₁ m₂ v₁ v₂ : ℕ}
    (hb : ∀ p ∈ b.primeFactors, p ≤ z0)
    (hm₁ : Squarefree m₁ ∧ ∀ p ∈ m₁.primeFactors, z0 < p ∧ p ≤ z1)
    (hm₂ : Squarefree m₂ ∧ ∀ p ∈ m₂.primeFactors, z0 < p ∧ p ≤ z1)
    (hv₁ : ∀ p ∈ v₁.primeFactors, z1 < p)
    (hv₂ : ∀ p ∈ v₂.primeFactors, z1 < p)
    (heq₁ : b * m₁ * v₁ = a * n + 1)
    (heq₂ : b * m₂ * v₂ = a * n + 1) :
    m₁ = m₂ := by
  have hne : a * n + 1 ≠ 0 := Nat.succ_ne_zero _
  have hb0 : b ≠ 0 := by intro h; rw [h, zero_mul, zero_mul] at heq₁; exact hne heq₁.symm
  have hv₁0 : v₁ ≠ 0 := by intro h; rw [h, mul_zero] at heq₁; exact hne heq₁.symm
  have hv₂0 : v₂ ≠ 0 := by intro h; rw [h, mul_zero] at heq₂; exact hne heq₂.symm
  have hpf_eq : m₁.primeFactors = m₂.primeFactors := by
    ext p
    have hmem (m v : ℕ) (hm : Squarefree m ∧ ∀ q ∈ m.primeFactors, z0 < q ∧ q ≤ z1)
        (hv : ∀ q ∈ v.primeFactors, z1 < q) (hv0 : v ≠ 0) (heq : b * m * v = a * n + 1) :
        p ∈ m.primeFactors ↔
          p ∈ (a * n + 1).primeFactors ∧ z0 < p ∧ p ≤ z1 := by
      rw [← heq, Nat.primeFactors_mul (mul_ne_zero hb0 hm.1.ne_zero) hv0,
        Nat.primeFactors_mul hb0 hm.1.ne_zero]
      simp only [Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inl (Or.inr hp), hm.2 p hp⟩
      · rintro ⟨(hp | hp) | hp, hz0, hz1⟩
        · exact absurd (hb p hp) (not_le.mpr hz0)
        · exact hp
        · exact absurd (hv p hp) (not_lt.mpr hz1)
    rw [hmem m₁ v₁ hm₁ hv₁ hv₁0 heq₁, hmem m₂ v₂ hm₂ hv₂ hv₂0 heq₂]
  have h1 : ∏ p ∈ m₁.primeFactors, p = m₁ := Nat.prod_primeFactors_of_squarefree hm₁.1
  have h2 : ∏ p ∈ m₂.primeFactors, p = m₂ := Nat.prod_primeFactors_of_squarefree hm₂.1
  rw [← h1, ← h2, hpf_eq]

/-- Reconstruct consecutive equal-tau integers from a family of disjoint multiplier tuples. -/
theorem card_family_le_erdos946Count
    {a b : Fin 7 → ℕ} {z0 z1 K : ℕ} {x : ℝ}
    (hmono : StrictMono a) (hapos : ∀ i, 0 < a i)
    (hkey : ∀ i j, i < j →
      a j - a i = (a i).gcd (a j) ∧
      σ 0 (a i) * σ 0 (a j / (a j - a i)) = σ 0 (a j) * σ 0 (a i / (a j - a i)))
    (hbpos : ∀ i, 0 < b i) (hbtau : ∀ i, σ 0 (b i) = σ 0 (a i))
    (hbcop : ∀ i j, (a i).Coprime (b j))
    (hb_le : ∀ i, ∀ p ∈ (b i).primeFactors, p ≤ z0)
    (ha_le : ∀ i, a i ≤ z0) (hz : z0 ≤ z1)
    (hK : K = a (Fin.last 6) * (a (Fin.last 6) + 1))
    (M : Finset (Fin 7 → ℕ)) (T : (Fin 7 → ℕ) → Finset ℕ)
    (hM : ∀ m ∈ M, (∃ k : ℕ, ∀ i, (m i).primeFactors.card = k) ∧
      ∀ i, Squarefree (m i) ∧ ∀ p ∈ (m i).primeFactors, z0 < p ∧ p ≤ z1)
    (hT : ∀ m ∈ M, ∀ n ∈ T m, 0 < n ∧ (K : ℝ) * (n : ℝ) ≤ x ∧
      ∃ v : Fin 7 → ℕ,
        (∀ i, b i * m i * v i = a i * n + 1 ∧ 1 < v i ∧ Squarefree (v i) ∧
          ∀ p ∈ (v i).primeFactors, z1 < p) ∧
        (∑ i, (v i).primeFactors.card) ≤ 27) :
    (M : Set (Fin 7 → ℕ)).PairwiseDisjoint T ∧
      ((∑ m ∈ M, (T m).card : ℕ) : ℝ) ≤ 49 * erdos946Count x := by
  classical
  have hdisj : (M : Set (Fin 7 → ℕ)).PairwiseDisjoint T := by
    intro m₁ hm₁ m₂ hm₂ hne
    change Disjoint (T m₁) (T m₂)
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    apply hne
    funext i
    obtain ⟨_, _, v₁, hv₁, _⟩ := hT m₁ hm₁ n hn₁
    obtain ⟨_, _, v₂, hv₂, _⟩ := hT m₂ hm₂ n hn₂
    exact multiplier_unique_of_decomp (hb_le i) ((hM m₁ hm₁).2 i) ((hM m₂ hm₂).2 i)
      (hv₁ i).2.2.2 (hv₂ i).2.2.2 (hv₁ i).1 (hv₂ i).1
  refine ⟨hdisj, ?_⟩
  let U := M.biUnion T
  have hcardU : U.card = ∑ m ∈ M, (T m).card := Finset.card_biUnion hdisj
  let V := (Finset.range (⌊x⌋₊ + 1)).filter (fun z => σ 0 z = σ 0 (z + 1))
  let zf (i j : Fin 7) (n : ℕ) := (a i / (a j - a i)) * (a j * n + 1)
  have htop (i : Fin 7) : a i ≤ a (Fin.last 6) := hmono.monotone (Fin.le_last i)
  have hget (n : ℕ) (hn : n ∈ U) : ∃ i j : Fin 7, i < j ∧ zf i j n ∈ V := by
    obtain ⟨m, hm, hnT⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨⟨k, hmk⟩, hmspec⟩ := hM m hm
    obtain ⟨hnpos, hKnx, v, hv, hsum⟩ := hT m hm n hnT
    obtain ⟨i, j, hij, hveq⟩ := seven_collision (fun i => (v i).primeFactors.card)
      (fun i => Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (hv i).2.1)) hsum
    have hmv_cop (t : Fin 7) : (m t).Coprime (v t) := by
      apply Nat.coprime_of_dvd
      intro p hpp hpm hpv
      have hp1 : p ≤ z1 := ((hmspec t).2 p (Nat.mem_primeFactors.mpr
        ⟨hpp, hpm, (hmspec t).1.ne_zero⟩)).2
      have hp2 : z1 < p := (hv t).2.2.2 p (Nat.mem_primeFactors.mpr
        ⟨hpp, hpv, by have := (hv t).2.1; omega⟩)
      omega
    have htau_mv (t : Fin 7) : σ 0 (m t * v t) = 2 ^ k * 2 ^ (v t).primeFactors.card := by
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hmv_cop t),
        tau_squarefree (hmspec t).1, tau_squarefree (hv t).2.2.1, hmk t]
    have hmveq : σ 0 (m j * v j) = σ 0 (m i * v i) := by
      rw [htau_mv j, htau_mv i, hveq]
    let d := a j - a i
    have hda : d ∣ a i := by simpa only [d, (hkey i j hij).1] using Nat.gcd_dvd_left (a i) (a j)
    have hdb : d ∣ a j := by simpa only [d, (hkey i j hij).1] using Nat.gcd_dvd_right (a i) (a j)
    have hcop_mv (h t : Fin 7) (hd : d ∣ a h) : ((a h / d) * b t).Coprime (m t * v t) := by
      apply Nat.coprime_of_dvd
      intro p hpp hpL hpR
      have hp_le : p ≤ z0 := by
        rcases hpp.dvd_mul.mp hpL with hp1 | hp2
        · have hdiv_pos : 0 < a h / d :=
            Nat.div_pos (Nat.le_of_dvd (hapos h) hd) (Nat.sub_pos_of_lt (hmono hij))
          exact ((Nat.le_of_dvd hdiv_pos hp1).trans (Nat.div_le_self _ _)).trans (ha_le h)
        · exact hb_le t p (Nat.mem_primeFactors.mpr ⟨hpp, hp2, (hbpos t).ne'⟩)
      rcases hpp.dvd_mul.mp hpR with hpm | hpv
      · have := ((hmspec t).2 p (Nat.mem_primeFactors.mpr ⟨hpp, hpm, (hmspec t).1.ne_zero⟩)).1
        omega
      · have hp1 : z1 < p := (hv t).2.2.2 p (Nat.mem_primeFactors.mpr
          ⟨hpp, hpv, by have := (hv t).2.1; omega⟩)
        omega
    have hhit := adjacent_consec (hmono hij) (d := d) rfl (hkey i j hij).1 (hkey i j hij).2
      (by rw [← Nat.mul_assoc]; exact (hv i).1)
      (by rw [← Nat.mul_assoc]; exact (hv j).1)
      (hbtau i) (hbtau j) hmveq
      ((hbcop j i).of_dvd_left (Nat.div_dvd_of_dvd hdb))
      ((hbcop i j).of_dvd_left (Nat.div_dvd_of_dvd hda))
      (hcop_mv j i hdb) (hcop_mv i j hda)
    have hlimit : zf i j n ≤ K * n := by
      dsimp [zf]
      calc
        (a i / (a j - a i)) * (a j * n + 1)
          ≤ a (Fin.last 6) * (a (Fin.last 6) * n + 1) :=
            Nat.mul_le_mul ((Nat.div_le_self _ _).trans (htop i))
              (by have := Nat.mul_le_mul_right n (htop j); omega)
        _ ≤ a (Fin.last 6) * ((a (Fin.last 6) + 1) * n) :=
            Nat.mul_le_mul_left _ (by nlinarith)
        _ = K * n := by rw [hK]; ring
    have hreal : (zf i j n : ℝ) ≤ x := by
      calc
        (zf i j n : ℝ) ≤ (K : ℝ) * (n : ℝ) := by exact_mod_cast hlimit
        _ ≤ x := hKnx
    exact ⟨i, j, hij, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hreal)), hhit⟩⟩
  choose I J IJ hmem using (fun n : U => hget n n.property)
  let map (n : U) : Fin 7 × Fin 7 × V := (I n, J n, ⟨_, hmem n⟩)
  have hinj : Function.Injective map := by
    intro n m h
    have hi : I n = I m := congrArg Prod.fst h
    have hj : J n = J m := congrArg (fun u => u.2.1) h
    have hz' : zf (I n) (J n) n = zf (I m) (J m) m := congrArg (fun u => u.2.2.val) h
    rw [hi, hj] at hz'
    let d := a (J m) - a (I m)
    have hdvd : d ∣ a (I m) := by
      simpa only [d, (hkey _ _ (IJ m)).1] using Nat.gcd_dvd_left (a (I m)) (a (J m))
    have hdp : 0 < d := Nat.sub_pos_of_lt (hmono (IJ m))
    have hcoeff := Nat.div_pos (Nat.le_of_dvd (hapos _) hdvd) hdp
    have hz'' := Nat.eq_of_mul_eq_mul_left hcoeff hz'
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left (hapos _) (Nat.add_right_cancel hz''))
  have hnn := Fintype.card_le_of_injective map hinj
  simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] at hnn
  rw [← hcardU]
  change (U.card : ℝ) ≤ 49 * (V.card : ℝ)
  exact_mod_cast (show U.card ≤ 49 * V.card by omega)

/-! ## Remaining Analytic Core (Modules 3, 4, 5 — to be filled in next) -/

theorem hildebrand_nat_core : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    c * ((N : ℝ) / (Real.log (Real.log N)) ^ 3) ≤
      (((Finset.range (N + 1)).filter (fun n => σ 0 n = σ 0 (n + 1))).card : ℝ) := by
  sorry

end OMA946

theorem OMA.solution : type_of% @Erdos946.erdos_946.variants.hildebrand_lower_bound := by
  exact OMA946.of_nat_core OMA946.hildebrand_nat_core
