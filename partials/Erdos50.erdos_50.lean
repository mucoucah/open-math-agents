import FormalConjectures.ErdosProblems.«50»
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- Problem: Erdős Problem 50 — erdos 50
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/50.lean:79 (declaration Erdos50.erdos_50)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Estimates for the totient-ratio distribution at the endpoints and at its finite products. -/

open Filter Set Topology
open scoped BigOperators

namespace Erdos50Proof

private lemma phi_product (n : ℕ) :
    (n.totient : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  exact h

private lemma prime_factor_estimate {p : ℕ} (hp : p.Prime) :
    1 ≤ (1 + 6 / (p : ℝ)) * (1 - (p : ℝ)⁻¹) ^ 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let u : ℝ := (p : ℝ)⁻¹
  have hu : 0 ≤ u := by positivity
  have hu' : u ≤ 1 / 2 := by
    simpa [u, one_div] using (one_div_le_one_div_of_le (by norm_num) hp')
  have hpoly : 0 ≤ u * (1 - 2 * u) * (4 - 3 * u) :=
    mul_nonneg (mul_nonneg hu (by linarith)) (by linarith)
  have h : 1 ≤ (1 + 6 * u) * (1 - u) ^ 2 := by nlinarith only [hpoly]
  simpa [u, div_eq_mul_inv] using h

private lemma phi_weight_bound {n : ℕ} (hn : n ≠ 0) :
    1 ≤ (∏ p ∈ n.primeFactors, (1 + 6 / (p : ℝ))) *
      ((n.totient : ℝ) / n) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [phi_product, mul_div_cancel_left₀ _ hn', ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  simpa using (Finset.prod_le_prod (f := fun _ : ℕ => (1 : ℝ))
    (fun _ _ => zero_le_one)
    (fun p hp => prime_factor_estimate (Nat.mem_primeFactors.mp hp).1))

private lemma prime_subset_dvd (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p)
    {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  refine ⟨fun h p hp => (Finset.dvd_prod_of_mem id hp).trans h, fun h => ?_⟩
  exact (Finset.prod_dvd_prod_of_subset s n.primeFactors id
    (fun p hp => Nat.mem_primeFactors.mpr ⟨hs p hp, h p hp, hn⟩)).trans
    (Nat.prod_primeFactors_dvd n)

private lemma finite_prime_average (N : ℕ) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≠ 0),
      ∏ p ∈ n.primeFactors, (1 + 6 / (p : ℝ))) ≤
      (N : ℝ) * Real.exp (∑' p : ℕ, 6 / (p : ℝ) ^ 2) := by
  classical
  let P := (Finset.range (N + 1)).filter Nat.Prime
  let S := (Finset.range (N + 1)).filter (fun n => n ≠ 0)
  let w (p : ℕ) : ℝ := 6 / (p : ℝ)
  have hfactor (n : ℕ) (hn : n ∈ S) :
      n.primeFactors = P.filter (fun p => p ∣ n) := by
    obtain ⟨hnN, hn0⟩ := Finset.mem_filter.mp hn
    ext p
    simp only [Nat.mem_primeFactors, P, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hp, hd, _⟩
      exact ⟨⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd).trans_lt
        (Finset.mem_range.mp hnN), hp⟩, hd⟩
    · rintro ⟨⟨_, hp⟩, hd⟩
      exact ⟨hp, hd, hn0⟩
  have hexpand (n : ℕ) (hn : n ∈ S) :
      (∏ p ∈ n.primeFactors, (1 + w p)) =
        ∑ s ∈ P.powerset, if (∏ p ∈ s, p) ∣ n then ∏ p ∈ s, w p else 0 := by
    rw [hfactor n hn, Finset.prod_filter]
    have hterm (p : ℕ) : (if p ∣ n then 1 + w p else 1) =
        (if p ∣ n then w p else 0) + 1 := by split_ifs <;> simp [add_comm]
    simp_rw [hterm]
    rw [Finset.prod_add_one]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.prod_ite_zero]
    simp only [prime_subset_dvd s
      (fun p hp => (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).2)
      (Finset.mem_filter.mp hn).2]
  have hcount (s : Finset ℕ) :
      (∑ n ∈ S, if (∏ p ∈ s, p) ∣ n then ∏ p ∈ s, w p else 0) =
        ((N / ∏ p ∈ s, p : ℕ) : ℝ) * ∏ p ∈ s, w p := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter,
      Nat.card_multiples']
  change (∑ n ∈ S, ∏ p ∈ n.primeFactors, (1 + w p)) ≤ _
  calc
    _ = ∑ s ∈ P.powerset, ((N / ∏ p ∈ s, p : ℕ) : ℝ) * ∏ p ∈ s, w p := by
      rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => hcount s
    _ ≤ ∑ s ∈ P.powerset, (N : ℝ) * ∏ p ∈ s, (6 / (p : ℝ) ^ 2) := by
      refine Finset.sum_le_sum fun s _ => ?_
      calc
        _ ≤ ((N : ℝ) / (∏ p ∈ s, p : ℕ)) * ∏ p ∈ s, w p :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (Finset.prod_nonneg fun p _ => by
            dsimp [w]
            positivity)
        _ = _ := by
          rw [Nat.cast_prod, div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib]
          refine congrArg ((N : ℝ) * ·) (Finset.prod_congr rfl fun p _ => ?_)
          simp [w, div_div, pow_two]
    _ = (N : ℝ) * ∏ p ∈ P, (6 / (p : ℝ) ^ 2 + 1) := by
      rw [Finset.prod_add_one, Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      calc
        _ ≤ ∏ p ∈ P, Real.exp (6 / (p : ℝ) ^ 2) :=
          Finset.prod_le_prod (fun _ _ => by positivity) (fun _ _ => Real.add_one_le_exp _)
        _ = Real.exp (∑ p ∈ P, 6 / (p : ℝ) ^ 2) := (Real.exp_sum _ _).symm
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hsum : Summable (fun p : ℕ => 1 / (p : ℝ) ^ 2) :=
            Real.summable_one_div_nat_pow.mpr (by decide)
          have hsum' : Summable (fun p : ℕ => 6 / (p : ℝ) ^ 2) := by
            simpa [div_eq_mul_inv, mul_assoc] using hsum.mul_left (6 : ℝ)
          exact hsum'.sum_le_tsum P (fun _ _ => by positivity)

private lemma quadratic_density_bound {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    f c ≤ Real.exp (∑' p : ℕ, 6 / (p : ℝ) ^ 2) * c ^ 2 := by
  classical
  let K := Real.exp (∑' p : ℕ, 6 / (p : ℝ) ^ 2)
  let A : Set ℕ := {n | (n.totient : ℝ) < c * n}
  have hlim : A.HasDensity (f c) := hf c hc
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  let B := (Finset.range (N + 1)).filter (fun n => n ∈ A)
  let S := (Finset.range (N + 1)).filter (fun n => n ≠ 0)
  let W (n : ℕ) := ∏ p ∈ n.primeFactors, (1 + 6 / (p : ℝ))
  have hsub : B ⊆ S := by
    intro n hn
    have ⟨hb, hA⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hb, ?_⟩
    rintro rfl
    simp [A] at hA
  have hW (n : ℕ) : 0 ≤ W n := Finset.prod_nonneg fun p _ => by positivity
  have hterm (n : ℕ) (hn : n ∈ B) : 1 ≤ c ^ 2 * W n := by
    have hn0 : n ≠ 0 := (Finset.mem_filter.mp (hsub hn)).2
    have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hratio : (n.totient : ℝ) / n < c := (div_lt_iff₀ hnp).mpr
      (Finset.mem_filter.mp hn).2
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (n.totient : ℝ) / n) hratio.le 2
    rw [mul_comm]
    exact (phi_weight_bound hn0).trans (mul_le_mul_of_nonneg_left hsq (hW n))
  have hcount : (B.card : ℝ) ≤ (K * c ^ 2) * (N + 1 : ℕ) := calc
    _ = ∑ _n ∈ B, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ B, c ^ 2 * W n := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ S, c ^ 2 * W n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => mul_nonneg (sq_nonneg c) (hW n)
    _ ≤ c ^ 2 * ((N : ℝ) * K) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (finite_prime_average N) (sq_nonneg c)
    _ = (K * c ^ 2) * (N : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ N) (by dsimp [K]; positivity)
  have hB : A ∩ Iio (N + 1) = (B : Set ℕ) := by
    ext n
    simp [B, and_comm]
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  simpa only [Set.partialDensity, Set.inter_univ, Set.univ_inter, hB, Set.ncard_coe_finset,
    Nat.ncard_Iio] using (div_le_iff₀ hpos).mpr hcount

private lemma derivative_at_zero_nonpos {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {y : ℝ} (hd : HasDerivWithinAt f y (Icc 0 1) 0) : y ≤ 0 := by
  have hz : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hf0 : f 0 = 0 :=
    le_antisymm (by simpa using quadratic_density_bound hf hz) (hf 0 hz).nonneg
  let K := Real.exp (∑' p : ℕ, 6 / (p : ℝ) ^ 2)
  have hs : Tendsto (slope f 0) (𝓝[Ioo 0 1] 0) (𝓝 y) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hd).mono_left (nhdsWithin_mono 0 (by
      intro z hz
      exact ⟨Ioo_subset_Icc_self hz, by simpa using hz.1.ne'⟩))
  have ht : Tendsto (fun z : ℝ => K * z) (𝓝[Ioo 0 1] 0) (𝓝 0) := by
    have hid :
        Tendsto id (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := K)).mul hid
  have : (𝓝[Ioo (0 : ℝ) 1] 0).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
    exact nhdsGT_neBot _
  refine le_of_tendsto_of_tendsto hs ht ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [slope_def_field, hf0, sub_zero, sub_zero, div_le_iff₀ hz.1]
  simpa [K, pow_two, mul_assoc] using quadratic_density_bound hf (Ioo_subset_Icc_self hz)

private lemma avoidance_count (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    {N : ℕ} (hN : (∏ p ∈ P, p) ∣ N) :
    (((Finset.range (N + 1)).filter (fun n => n ≠ 0 ∧ ∀ p ∈ P, ¬p ∣ n)).card : ℝ) =
      (N : ℝ) * ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
  classical
  let S := (Finset.range (N + 1)).filter (fun n => n ≠ 0)
  have hexpand (n : ℕ) (hn : n ∈ S) :
      (if ∀ p ∈ P, ¬p ∣ n then (1 : ℝ) else 0) =
        ∑ s ∈ P.powerset, (-1 : ℝ) ^ s.card * (if (∏ p ∈ s, p) ∣ n then 1 else 0) := by
    have hterm (p : ℕ) : (if ¬p ∣ n then (1 : ℝ) else 0) =
        1 - (if p ∣ n then 1 else 0) := by by_cases hp : p ∣ n <;> simp [hp]
    have heq : (if ∀ p ∈ P, ¬p ∣ n then (1 : ℝ) else 0) =
        ∏ p ∈ P, (if ¬p ∣ n then (1 : ℝ) else 0) := by
      symm
      simpa only [Finset.prod_const_one] using
        (Finset.prod_ite_zero (s := P) (p := fun p => ¬p ∣ n) (f := fun _ => (1 : ℝ)))
    rw [heq]
    simp only [hterm, Finset.prod_sub, Finset.prod_const_one, mul_one]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.prod_ite_zero, Finset.prod_const_one]
    simp only [prime_subset_dvd s (fun p hp => hP p (Finset.mem_powerset.mp hs hp))
      (Finset.mem_filter.mp hn).2]
  have hcount (s : Finset ℕ) (hs : s ∈ P.powerset) :
      (∑ n ∈ S, (-1 : ℝ) ^ s.card * (if (∏ p ∈ s, p) ∣ n then 1 else 0)) =
        (N : ℝ) * ((-1 : ℝ) ^ s.card * ∏ p ∈ s, (p : ℝ)⁻¹) := by
    have hd : (∏ p ∈ s, p) ∣ N :=
      (Finset.prod_dvd_prod_of_subset s P id (Finset.mem_powerset.mp hs)).trans hN
    rw [← Finset.mul_sum, Finset.sum_boole, Finset.filter_filter, Nat.card_multiples',
      Nat.cast_div_charZero hd, Nat.cast_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    ring
  rw [← Finset.filter_filter, ← Finset.sum_boole]
  change (∑ n ∈ S, _) = _
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  simp only [Finset.prod_sub, Finset.prod_const_one, mul_one, Finset.mul_sum]
  exact Finset.sum_congr rfl hcount

private lemma totient_gap_le {n : ℕ} (hn : n ≠ 0) :
    1 - (n.totient : ℝ) / n ≤ ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹ := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [phi_product, mul_div_cancel_left₀ _ hn']
  suffices ∀ s : Finset ℕ, 1 - ∏ p ∈ s, (1 - (p : ℝ)⁻¹) ≤ ∑ p ∈ s, (p : ℝ)⁻¹ by
    exact this _
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hle (q : ℕ) : (q : ℝ)⁻¹ ≤ 1 := by
      by_cases hq : q = 0
      · simp [hq]
      · have hq' : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero hq
        simpa [one_div] using (one_div_le_one_div_of_le (by norm_num) hq')
    have hprod : (∏ q ∈ s, (1 - (q : ℝ)⁻¹)) ≤ 1 :=
      Finset.prod_le_one (fun q _ => sub_nonneg.mpr (hle q)) (fun q _ => sub_le_self _ (by positivity))
    rw [Finset.prod_insert hp, Finset.sum_insert hp]
    have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (p : ℝ)⁻¹ by positivity)
    nlinarith only [ih, h]

private lemma reciprocal_square_tail {m N : ℕ} (hm : m ≤ N) (hm0 : m ≠ 0) :
    (∑ p ∈ Finset.Ico (m + 1) (N + 1), (p : ℝ)⁻¹ ^ 2) ≤ (m : ℝ)⁻¹ := by
  let u (p : ℕ) := -((p - 1 : ℕ) : ℝ)⁻¹
  calc
    _ ≤ ∑ p ∈ Finset.Ico (m + 1) (N + 1), (u (p + 1) - u p) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have h1 : 0 < p - 1 := by have := (Finset.mem_Ico.mp hp).1; omega
      have h1' : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast h1
      have h2 : (0 : ℝ) < p := by have := (Finset.mem_Ico.mp hp).1; exact_mod_cast (by omega : 0 < p)
      have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      simp only [u, Nat.add_sub_cancel, hcast]
      rw [inv_pow, ← one_div]
      apply (div_le_iff₀ (sq_pos_of_pos h2)).mpr
      have hpos : 0 < (p : ℝ) - 1 := by linarith
      field_simp [hpos.ne', h2.ne']
      nlinarith
    _ = (m : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
      rw [Finset.sum_Ico_sub (f := u) (Nat.succ_le_succ hm)]
      simp [u, sub_eq_add_neg, add_comm]
    _ ≤ _ := sub_le_self _ (by positivity)

private lemma finite_large_divisor_average {m N : ℕ} (hm : m ≤ N) (hm0 : m ≠ 0) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≠ 0),
      ∑ p ∈ Finset.Ico (m + 1) (N + 1), if p ∣ n then (p : ℝ)⁻¹ else 0)
      ≤ (N : ℝ) * (m : ℝ)⁻¹ := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ p ∈ Finset.Ico (m + 1) (N + 1), ((N / p : ℕ) : ℝ) * (p : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter,
        Nat.card_multiples']
    _ ≤ ∑ p ∈ Finset.Ico (m + 1) (N + 1), (N : ℝ) * (p : ℝ)⁻¹ ^ 2 := by
      refine Finset.sum_le_sum fun p _ => ?_
      calc
        _ ≤ ((N : ℝ) / p) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (reciprocal_square_tail hm hm0) (by positivity)

private def smallPrimes (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter Nat.Prime

private lemma mem_smallPrimes {m p : ℕ} : p ∈ smallPrimes m ↔ p ≤ m ∧ p.Prime := by
  simp [smallPrimes]

private lemma one_sub_inv_nonneg (p : ℕ) : 0 ≤ 1 - (p : ℝ)⁻¹ := by
  by_cases hp : p = 0
  · simp [hp]
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast Nat.pos_of_ne_zero hp
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp'
  simpa [one_div, sub_nonneg] using h

private lemma wheel_step (k : ℕ) :
    (6 * (k : ℝ) + 1) / (6 * k + 7) ≤
      ((1 - (6 * k + 5 : ℝ)⁻¹) * (1 - (6 * k + 7 : ℝ)⁻¹)) ^ 3 := by
  let a := 6 * (k : ℝ)
  have ha : 0 ≤ a := by positivity
  have hcube (t : ℝ) (ht : 1 ≤ t) : 1 - 3 * t⁻¹ ≤ (1 - t⁻¹) ^ 3 := by
    have htinv : t⁻¹ ≤ 1 := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ht
    have hp : 0 ≤ t⁻¹ ^ 2 * (3 - t⁻¹) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith only [hp]
  have h1 : (a + 1) / (a + 4) ≤ (1 - (a + 5)⁻¹) ^ 3 := by
    calc
      _ = 1 - 3 * (a + 4)⁻¹ := by field_simp; ring
      _ ≤ 1 - 3 * (a + 5)⁻¹ := by
        have h : (a + 5)⁻¹ ≤ (a + 4)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le (by linarith : 0 < a + 4)
            (by linarith : a + 4 ≤ a + 5)
        linarith
      _ ≤ _ := hcube _ (by linarith)
  have h2 : (a + 4) / (a + 7) ≤ (1 - (a + 7)⁻¹) ^ 3 := by
    calc
      _ = 1 - 3 * (a + 7)⁻¹ := by field_simp; ring
      _ ≤ _ := hcube _ (by linarith)
  change (a + 1) / (a + 7) ≤ _
  rw [mul_pow]
  calc
    _ = ((a + 1) / (a + 4)) * ((a + 4) / (a + 7)) := by field_simp
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)

private lemma wheel_product_bound (k : ℕ) :
    1 / (27 * (6 * (k : ℝ) + 1)) ≤
      (∏ p ∈ smallPrimes (6 * k + 3), (1 - (p : ℝ)⁻¹)) ^ 3 := by
  induction k with
  | zero =>
    have h : smallPrimes 3 = {2, 3} := by decide
    norm_num [h, Finset.prod_insert, Finset.prod_singleton]
  | succ k ih =>
    let g (p : ℕ) : ℝ := 1 - (p : ℝ)⁻¹
    let P := smallPrimes (6*k+3)
    let P' := smallPrimes (6*(k+1)+3)
    have hsub : P ⊆ P' := by
      intro p hp
      have := mem_smallPrimes.mp hp
      exact mem_smallPrimes.mpr ⟨by omega, this.2⟩
    have hcand : P' \ P ⊆ ({6*k+5, 6*k+7} : Finset ℕ) := by
      intro p hp
      obtain ⟨hp', hp⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hhi, hprime⟩ := mem_smallPrimes.mp hp'
      have hlo : 6*k+3 < p := by
        by_contra! h
        exact hp (mem_smallPrimes.mpr ⟨h, hprime⟩)
      have hodd : p % 2 = 1 := by
        rcases hprime.eq_two_or_odd with rfl | hodd
        · omega
        · exact hodd
      have hnot3 : ¬3 ∣ p := by
        intro h
        rcases hprime.eq_one_or_self_of_dvd 3 h with hfalse | heq <;> omega
      have hmod : p % 3 ≠ 0 := fun h => hnot3 (Nat.dvd_iff_mod_eq_zero.mpr h)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hg (p : ℕ) : 0 ≤ g p := one_sub_inv_nonneg p
    have hprod : ∏ p ∈ ({6*k+5, 6*k+7} : Finset ℕ), g p ≤ ∏ p ∈ P' \ P, g p :=
      Finset.prod_le_prod_of_subset_of_le_one hcand (fun p _ => hg p)
        (fun p _ _ => sub_le_self _ (by positivity))
    have heq : ∏ p ∈ ({6*k+5, 6*k+7} : Finset ℕ), g p = g (6*k+5) * g (6*k+7) := by
      rw [Finset.prod_insert (by simp), Finset.prod_singleton]
    rw [heq] at hprod
    have hpow : (6 * (k : ℝ) + 1) / (6 * k + 7) ≤
        (∏ p ∈ P' \ P, g p) ^ 3 := by
      apply le_trans (wheel_step k)
      have hpow' := pow_le_pow_left₀ (mul_nonneg (hg (6*k+5)) (hg (6*k+7))) hprod 3
      simpa [g, Nat.cast_add, Nat.cast_mul] using hpow'
    change 1 / (27 * (6 * ((k + 1 : ℕ) : ℝ) + 1)) ≤ (∏ p ∈ P', g p) ^ 3
    rw [← Finset.prod_sdiff hsub, mul_pow]
    have hpos : 0 ≤ (∏ p ∈ P' \ P, g p) ^ 3 := pow_nonneg (Finset.prod_nonneg fun p _ => hg p) _
    calc
      _ = ((6 * (k : ℝ) + 1) / (6 * k + 7)) * (1 / (27 * (6 * k + 1))) := by
        push_cast
        have ht : 0 < 6 * (k : ℝ) + 1 := by positivity
        have ht' : 0 < 6 * (k : ℝ) + 7 := by positivity
        field_simp
        ring
      _ ≤ _ := mul_le_mul hpow ih (by positivity) hpos

private lemma partialDensity_count (A : Set ℕ) [DecidablePred (· ∈ A)] (b : ℕ) :
    A.partialDensity Set.univ b =
      (((Finset.range b).filter (fun n => n ∈ A)).card : ℝ) / b := by
  classical
  have hs : A ∩ Set.Iio b = ((Finset.range b).filter (fun n => n ∈ A) : Set ℕ) := by
    ext n
    simp [and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, hs,
    Set.ncard_coe_finset, Nat.ncard_Iio]

private lemma density_at_one {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f) : f 1 = 1 := by
  classical
  let A : Set ℕ := {n | (n.totient : ℝ) < 1 * n}
  have hfin : Aᶜ.Finite := by
    refine (Set.finite_Iio 2).subset ?_
    intro n hn
    by_contra! h
    apply hn
    have hlt := Nat.totient_lt n (by simpa using h : 1 < n)
    simpa [A] using (show (n.totient : ℝ) < n by exact_mod_cast hlt)
  have ha : A.HasDensity (f 1) := hf 1 ⟨zero_le_one, le_rfl⟩
  have hb : Aᶜ.HasDensity 0 := Nat.hasDensity_zero_of_finite hfin
  unfold Set.HasDensity at ha hb
  refine tendsto_nhds_unique ha (Tendsto.congr' ?_ (by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hb))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb'
  rw [partialDensity_count, partialDensity_count]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range b) (p := fun n => n ∈ A)
  rw [Finset.card_range] at h
  have hpos : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  simp only [Set.mem_compl_iff]
  apply (eq_div_iff hpos).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hpos]
  have h' : (((Finset.range b).filter (fun n => n ∈ A)).card : ℝ) +
      (((Finset.range b).filter (fun n => n ∉ A)).card : ℝ) = b := by exact_mod_cast h
  linarith

private lemma density_near_one {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∏ p ∈ smallPrimes m, (1 - (p : ℝ)⁻¹)) - (m : ℝ)⁻¹ / h ≤ 1 - f (1 - h) := by
  classical
  let P := smallPrimes m
  let Q := ∏ p ∈ P, p
  let D := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)
  let E := (m : ℝ)⁻¹ / h
  let A : Set ℕ := {n | (n.totient : ℝ) < (1 - h) * n}
  have hQ : 0 < Q := Finset.prod_pos fun p hp => (mem_smallPrimes.mp hp).2.pos
  have hseq : Tendsto (fun k : ℕ => k * Q + 1) atTop atTop := by
    refine tendsto_atTop_mono' _ (.of_forall fun k => ?_) tendsto_id
    exact (Nat.le_mul_of_pos_right k hQ).trans (Nat.le_succ _)
  have hlim : A.HasDensity (f (1 - h)) := hf _ ⟨by linarith, by linarith⟩
  have hlim' : Tendsto (fun k : ℕ => A.partialDensity Set.univ (k * Q + 1))
      atTop (𝓝 (f (1 - h))) := hlim.comp hseq
  have hlim'' : Tendsto (fun k : ℕ => 1 - (D - E) + (D - E) / (k * Q + 1 : ℕ))
      atTop (𝓝 (1 - (D - E))) := by
    simpa using (tendsto_const_nhds (x := 1 - (D - E))).add
      ((tendsto_const_div_atTop_nhds_zero_nat (D - E)).comp hseq)
  suffices f (1 - h) ≤ 1 - (D - E) by
    change D - E ≤ 1 - f (1 - h)
    linarith
  refine le_of_tendsto_of_tendsto hlim' hlim'' ?_
  filter_upwards [hseq.eventually (eventually_ge_atTop (m + 1))] with k hk
  let N := k * Q
  have hmN : m ≤ N := Nat.le_of_succ_le_succ hk
  let R := Finset.range (N + 1)
  let B := R.filter (fun n => n ∈ A)
  let U := R.filter (fun n => n ≠ 0 ∧ ∀ p ∈ P, ¬p ∣ n)
  let S := R.filter (fun n => n ≠ 0)
  let W (n : ℕ) := ∑ p ∈ Finset.Ico (m + 1) (N + 1), if p ∣ n then (p : ℝ)⁻¹ else 0
  have hterm (n : ℕ) (hn : n ∈ B ∩ U) : h ≤ W n := by
    obtain ⟨hnB, hnU⟩ := Finset.mem_inter.mp hn
    obtain ⟨hnN, hn0, hnP⟩ := Finset.mem_filter.mp hnU
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnA : (n.totient : ℝ) / n < 1 - h :=
      (div_lt_iff₀ hnpos).mpr (Finset.mem_filter.mp hnB).2
    have hsub : n.primeFactors ⊆ Finset.Ico (m + 1) (N + 1) := by
      intro p hp
      obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
      have hgt : m < p := lt_of_not_ge fun h => hnP p (mem_smallPrimes.mpr ⟨h, hpp⟩) hpd
      exact Finset.mem_Ico.mpr ⟨hgt, (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd).trans_lt
        (Finset.mem_range.mp hnN)⟩
    calc
      _ ≤ 1 - (n.totient : ℝ) / n := by linarith
      _ ≤ ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹ := totient_gap_le hn0
      _ = ∑ p ∈ n.primeFactors, if p ∣ n then (p : ℝ)⁻¹ else 0 := by
        exact Finset.sum_congr rfl fun p hp => (if_pos (Nat.mem_primeFactors.mp hp).2.1).symm
      _ ≤ W n := Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by split_ifs <;> positivity
  have hbad : ((B ∩ U).card : ℝ) ≤ (N : ℝ) * E := by
    rw [show (N : ℝ) * E = ((N : ℝ) * (m : ℝ)⁻¹) / h by simp [E, mul_div_assoc]]
    apply (le_div_iff₀ hh).mpr
    calc
      _ = ∑ _n ∈ B ∩ U, h := by simp
      _ ≤ ∑ n ∈ B ∩ U, W n := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ S, W n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hn).2).1,
            (Finset.mem_filter.mp (Finset.mem_inter.mp hn).2).2.1⟩
        · intro n _ _
          exact Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
      _ ≤ _ := finite_large_divisor_average hmN hm
  have hU : (U.card : ℝ) = (N : ℝ) * D :=
    avoidance_count P (fun p hp => (mem_smallPrimes.mp hp).2) (dvd_mul_left Q k)
  have hBU : (B ∪ U).card ≤ N + 1 := by
    simpa [R] using Finset.card_le_card
      (Finset.union_subset (Finset.filter_subset _ R) (Finset.filter_subset _ R) :
        B ∪ U ⊆ R)
  have hcount : (B.card : ℝ) + (N : ℝ) * D ≤ (N + 1 : ℕ) + (N : ℝ) * E := calc
    _ = (B.card : ℝ) + U.card := by rw [hU]
    _ = ((B ∪ U).card : ℝ) + (B ∩ U).card := by
      exact_mod_cast (Finset.card_union_add_card_inter B U).symm
    _ ≤ _ := add_le_add (by exact_mod_cast hBU) hbad
  rw [partialDensity_count]
  change (B.card : ℝ) / (N + 1 : ℕ) ≤ 1 - (D - E) + (D - E) / (N + 1 : ℕ)
  have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hpos).mpr
  rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  push_cast at hcount ⊢
  nlinarith only [hcount]

private lemma endpoint_growth_unbounded {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {C δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ h : ℝ, 0 < h → h ≤ 1 → h < δ → 1 - f (1 - h) ≤ C * h) : False := by
  let M : ℝ := max 1 (C + 1)
  obtain ⟨j, hj⟩ := exists_nat_gt (max 1 (max δ⁻¹ (189 * M ^ 3)))
  have hj1 : (1 : ℝ) < j := (le_max_left _ _).trans_lt hj
  have hjδ : δ⁻¹ < j := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hj
  have hjM : 189 * M ^ 3 < j := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hj
  let h : ℝ := ((j : ℝ) + 1)⁻¹
  have hjp : 0 < (j : ℝ) + 1 := by linarith
  have hp : 0 < h := inv_pos.mpr hjp
  have hh1 : h ≤ 1 := by
    simpa [h, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (by linarith : (1 : ℝ) ≤ (j : ℝ) + 1)
  have hhδ : h < δ := by
    have hδi : 0 < δ⁻¹ := inv_pos.mpr hδ
    have hi : ((j : ℝ) + 1)⁻¹ < (δ⁻¹)⁻¹ :=
      (inv_lt_inv₀ hjp hδi).mpr (by linarith)
    simpa [h] using hi
  have hgap := hbound h hp hh1 hhδ
  let m : ℕ := 6 * (j * j) + 3
  have hm : m ≠ 0 := by dsimp [m]; omega
  have htail := density_near_one hf hm hp hh1
  have hmsq : ((j : ℝ) + 1) ^ 2 ≤ (m : ℝ) := by
    dsimp [m]
    push_cast
    nlinarith only [sq_nonneg ((j : ℝ) - 1), sq_nonneg (j : ℝ)]
  have he : (m : ℝ)⁻¹ / h ≤ h := by
    apply (div_le_iff₀ hp).mpr
    rw [← pow_two, show h = ((j : ℝ) + 1)⁻¹ by rfl, inv_pow]
    exact inv_anti₀ (by positivity) hmsq
  let D := ∏ p ∈ smallPrimes m, (1 - (p : ℝ)⁻¹)
  have hD0 : 0 ≤ D := Finset.prod_nonneg fun p _ => one_sub_inv_nonneg p
  have hD : D ≤ M * h := by
    have hmul := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (C + 1)) hp.le
    change D - (m : ℝ)⁻¹ / h ≤ _ at htail
    linarith only [htail, hgap, he, hmul]
  have hpow : 1 / (27 * (6 * ((j * j : ℕ) : ℝ) + 1)) ≤ (M * h) ^ 3 :=
    (wheel_product_bound (j * j)).trans (pow_le_pow_left₀ hD0 hD 3)
  have hden : 27 * (6 * ((j * j : ℕ) : ℝ) + 1) ≤ 189 * ((j : ℝ) + 1) ^ 2 := by
    push_cast
    nlinarith only [hj1, sq_nonneg (j : ℝ)]
  have hlow : 1 / (189 * ((j : ℝ) + 1) ^ 2) ≤ (M * h) ^ 3 :=
    (one_div_le_one_div_of_le (by positivity) hden).trans hpow
  rw [show h = ((j : ℝ) + 1)⁻¹ by rfl, mul_pow, inv_pow, ← div_eq_mul_inv] at hlow
  have hden' : 0 < 189 * ((j : ℝ) + 1) ^ 2 := by positivity
  have hcross := (div_le_div_iff₀ hden' (pow_pos hjp 3)).mp hlow
  have hjlt : 189 * M ^ 3 < (j : ℝ) + 1 := by linarith
  have hcontra := mul_lt_mul_of_pos_right hjlt (pow_pos hjp 2)
  nlinarith only [hcross, hcontra]

private lemma no_derivative_at_one {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {y : ℝ} (hd : HasDerivWithinAt f y (Icc 0 1) 1) : False := by
  have ht := hasDerivWithinAt_iff_tendsto_slope.mp hd
  obtain ⟨δ, hδ, hlim⟩ := Metric.tendsto_nhdsWithin_nhds.mp ht 1 zero_lt_one
  apply endpoint_growth_unbounded hf (C := y + 1) hδ
  intro h hp hh1 hhδ
  have hmem : 1 - h ∈ Icc (0 : ℝ) 1 \ {1} := by
    exact ⟨⟨by linarith, by linarith⟩, by
      simp
      linarith⟩
  have hdist : dist (1 - h) 1 < δ := by
    rw [Real.dist_eq, show 1 - h - 1 = -h by ring, abs_neg, abs_of_pos hp]
    exact hhδ
  have hsl := hlim hmem hdist
  rw [Real.dist_eq, slope_def_field, show 1 - h - 1 = -h by ring, div_neg, ← neg_div,
    neg_sub] at hsl
  apply (div_le_iff₀ hp).mp
  have htop := (abs_lt.mp hsl).2
  rw [density_at_one hf] at htop
  linarith


private lemma density_difference {A B : Set ℕ} {a b : ℝ} (hs : A ⊆ B)
    (ha : A.HasDensity a) (hb : B.HasDensity b) : (B \ A).HasDensity (b - a) := by
  classical
  unfold Set.HasDensity at ha hb ⊢
  refine (hb.sub ha).congr fun N => ?_
  simp only [partialDensity_count]
  have hsub : (Finset.range N).filter (fun n => n ∈ A) ⊆
      (Finset.range N).filter (fun n => n ∈ B) := by
    intro n hn
    obtain ⟨hN, hA⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hN, hs hA⟩
  have heq : (Finset.range N).filter (fun n => n ∈ B \ A) =
      ((Finset.range N).filter (fun n => n ∈ B)) \
        ((Finset.range N).filter (fun n => n ∈ A)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, Set.mem_sdiff]
    tauto
  rw [heq, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), sub_div]

private lemma phi_ratio_mul_upper {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    ((d*n).totient : ℝ) / (d*n : ℕ) ≤ (d.totient : ℝ) / d := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdn' : ((d*n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hd hn).ne'
  simp only [phi_product, mul_div_cancel_left₀ _ hd', mul_div_cancel_left₀ _ hdn']
  refine Finset.prod_le_prod_of_subset_of_le_one ?_ (fun p _ => one_sub_inv_nonneg p)
    (fun p _ _ => sub_le_self _ (by positivity))
  intro p hp
  obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hp, hpd.trans (dvd_mul_right d n), (Nat.mul_pos hd hn).ne'⟩

private lemma scaled_tail_le_increment {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {d : ℕ} (hd : 0 < d) {r h : ℝ} (hr : r = (d.totient : ℝ) / d)
    (hh : 0 < h) (hh1 : h ≤ 1) (hupper : r + h ≤ 1) :
    (1 - f (1 - h)) / d ≤ f (r + h) - f (r * (1 - h)) := by
  classical
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by linarith
  have hl0 : 0 ≤ r * (1 - h) := mul_nonneg hr0 (by linarith)
  have hlr : r * (1 - h) ≤ r := by nlinarith only [mul_nonneg hr0 hh.le]
  let A (t : ℝ) : Set ℕ := {n | (n.totient : ℝ) < t * n}
  have hmono {a b : ℝ} (hab : a ≤ b) : A a ⊆ A b :=
    fun n hn => lt_of_lt_of_le hn (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n))
  let S := A 1 \ A (1 - h)
  let T := A (r + h) \ A (r * (1 - h))
  have hS : S.HasDensity (1 - f (1 - h)) := by
    have hs : S.HasDensity (f 1 - f (1 - h)) := density_difference
      (hmono (show 1 - h ≤ 1 by linarith)) (hf (1 - h) ⟨by linarith, by linarith⟩)
      (hf 1 ⟨zero_le_one, le_rfl⟩)
    simpa only [density_at_one hf] using hs
  have hT : T.HasDensity (f (r + h) - f (r * (1 - h))) :=
    density_difference (hmono (by linarith)) (hf _ ⟨hl0, hlr.trans hr1⟩)
      (hf _ ⟨by linarith, hupper⟩)
  have hmaps : ∀ n ∈ S, d*n ∈ T := by
    intro n hn
    have hn0 : 0 < n := by
      by_contra! hn0
      have : n = 0 := by omega
      subst n
      have hb := hn.1
      simp [A] at hb
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hdn' : (0 : ℝ) < ((d*n : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd hn0
    refine ⟨?_, ?_⟩
    · apply (div_lt_iff₀ hdn').mp
      exact (phi_ratio_mul_upper hd hn0).trans_lt (by rw [← hr]; linarith)
    · intro hbad
      have ht : 1 - h ≤ (n.totient : ℝ) / n :=
        (le_div_iff₀ hn').mpr (le_of_not_gt hn.2)
      have hl : r * (1 - h) ≤ ((d*n).totient : ℝ) / (d*n : ℕ) := calc
        _ ≤ r * ((n.totient : ℝ) / n) := mul_le_mul_of_nonneg_left ht hr0
        _ = ((d.totient * n.totient : ℕ) : ℝ) / (d*n : ℕ) := by
          rw [hr, Nat.cast_mul, Nat.cast_mul, div_mul_div_comm]
        _ ≤ _ := div_le_div_of_nonneg_right
          (by exact_mod_cast Nat.totient_super_multiplicative d n) hdn'.le
      exact (not_lt_of_ge hl) ((div_lt_iff₀ hdn').mpr hbad)
  have hseq : Tendsto (fun N : ℕ => d * N) atTop atTop := by
    refine tendsto_atTop_mono' _ (.of_forall fun N => ?_) tendsto_id
    simpa [mul_comm] using Nat.le_mul_of_pos_right N hd
  unfold Set.HasDensity at hS hT
  refine le_of_tendsto_of_tendsto' (hS.div_const (d : ℝ)) (hT.comp hseq) fun N => ?_
  change S.partialDensity univ N / (d : ℝ) ≤ T.partialDensity univ (d*N)
  rw [partialDensity_count, partialDensity_count, div_div, Nat.cast_mul, mul_comm (N : ℝ)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  refine Finset.card_le_card_of_injOn (fun n => d*n) ?_ ?_
  · intro n hn
    obtain ⟨hnN, hnS⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hnN) hd), hmaps n hnS⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd hab

private lemma derivative_increment_bound {f : ℝ → ℝ} {r y : ℝ}
    (hd : HasDerivWithinAt f y (Icc 0 1) r) :
    ∃ δ > 0, ∀ z ∈ Icc (0 : ℝ) 1, |z-r| < δ → |f z - f r| ≤ (|y| + 1) * |z-r| := by
  obtain ⟨δ, hδ, hlim⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp (hasDerivWithinAt_iff_tendsto_slope.mp hd) 1 zero_lt_one
  refine ⟨δ, hδ, fun z hz hdist => ?_⟩
  by_cases heq : z = r
  · subst z
    simp
  have hmem : z ∈ Icc (0 : ℝ) 1 \ {r} := ⟨hz, by simpa using heq⟩
  have hs := hlim hmem (by simpa [Real.dist_eq] using hdist)
  rw [Real.dist_eq] at hs
  have hab : |slope f r z| ≤ |y| + 1 := by
    calc
      _ = |(slope f r z - y) + y| := by rw [sub_add_cancel]
      _ ≤ |slope f r z - y| + |y| := abs_add_le _ _
      _ ≤ _ := by linarith
  rw [slope_def_field, abs_div] at hab
  exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr heq))).mp hab

private lemma no_derivative_at_finite_ratio {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {d : ℕ} (hd : 0 < d) {r y : ℝ} (hr : r = (d.totient : ℝ) / d) (hr1 : r < 1)
    (hder : HasDerivWithinAt f y (Icc 0 1) r) : False := by
  obtain ⟨δ, hδ, hinc⟩ := derivative_increment_bound hder
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  let C := |y| + 1
  apply endpoint_growth_unbounded hf (C := (d : ℝ) * (2 * C))
    (δ := min δ (1 - r)) (lt_min hδ (by linarith))
  intro h hh hh1 hsmall
  have hhδ : h < δ := hsmall.trans_le (min_le_left _ _)
  have hright : r + h ≤ 1 := by
    have := hsmall.trans_le (min_le_right _ _)
    linarith
  have hleft : r * (1 - h) ≤ r := by nlinarith only [mul_nonneg hr0 hh.le]
  have hleftdist : |r * (1 - h) - r| = r*h := by
    rw [abs_of_nonpos (sub_nonpos.mpr hleft)]
    ring
  have hrightdist : |r + h - r| = h := by
    rw [show r + h - r = h by ring, abs_of_pos hh]
  have hmul : r*h ≤ h := by nlinarith only [mul_nonneg (sub_nonneg.mpr hr1.le) hh.le]
  have hincr := hinc (r+h) ⟨by linarith, hright⟩ (by rwa [hrightdist])
  have hincl := hinc (r*(1-h)) ⟨mul_nonneg hr0 (by linarith), hleft.trans hr1.le⟩
    (by rw [hleftdist]; exact hmul.trans_lt hhδ)
  rw [hleftdist] at hincl
  rw [hrightdist] at hincr
  have ht : f (r+h) - f (r*(1-h)) ≤ 2*C*h := by
    have h1 := (abs_le.mp hincr).2
    have h2 := (abs_le.mp hincl).1
    dsimp [C]
    nlinarith only [h1, h2, mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ |y| + 1)]
  have hgap := (scaled_tail_le_increment hf hd hr hh hh1 hright).trans ht
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hf' := (div_le_iff₀ hdp).mp hgap
  linarith only [hf']

private lemma derivative_band_error {f : ℝ → ℝ} {x y : ℝ}
    (hd : HasDerivWithinAt f y (Icc 0 1) x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |u - x| < δ → |v - x| < δ →
      |f v - f u - y * (v - u)| ≤ ε * (|u - x| + |v - x|) := by
  obtain ⟨δ, hδ, hloc⟩ := Metric.mem_nhdsWithin_iff.mp (hd.isLittleO.def hε)
  have herror (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (hzδ : |z - x| < δ) :
      |f z - f x - (z - x) * y| ≤ ε * |z - x| := by
    have hb : z ∈ Metric.ball x δ := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hzδ
    have h := hloc ⟨hb, hz⟩
    change ‖f z - f x - (z - x) • y‖ ≤ ε * ‖z - x‖ at h
    simpa only [Real.norm_eq_abs, smul_eq_mul] using h
  refine ⟨δ, hδ, fun u hu v hv huδ hvδ => ?_⟩
  calc
    _ = |(f v - f x - (v - x) * y) - (f u - f x - (u - x) * y)| := by
      congr 1
      ring
    _ ≤ |f v - f x - (v - x) * y| + |f u - f x - (u - x) * y| :=
      abs_sub _ _
    _ ≤ _ := by
      rw [mul_add, add_comm (ε * |u - x|)]
      exact add_le_add (herror v hv hvδ) (herror u hu huδ)

private lemma nearby_ratio_bound {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {x y : ℝ} (hd : HasDerivWithinAt f y (Icc 0 1) x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ d : ℕ, 0 < d → ∀ r h : ℝ, r = (d.totient : ℝ) / d →
      0 < h → h ≤ 1 → r + h ≤ 1 → |r - x| + h < δ →
      (1 - f (1 - h)) / d ≤ y * ((1 + r) * h) + 2 * ε * (|r - x| + h) := by
  obtain ⟨δ, hδ, he⟩ := derivative_band_error hd hε
  refine ⟨δ, hδ, fun d hdpos r h hr hh hh1 hrh hnear => ?_⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by linarith
  have hrmul : 0 ≤ r * h := mul_nonneg hr0 hh.le
  have hsmall : r * h ≤ h := by nlinarith only [mul_nonneg (sub_nonneg.mpr hr1) hh.le]
  have hu : r * (1 - h) ∈ Icc (0 : ℝ) 1 := by
    exact ⟨mul_nonneg hr0 (by linarith), by nlinarith only [hr1, hrmul]⟩
  have hv : r + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hrh⟩
  have hud : |r * (1 - h) - x| ≤ |r - x| + h := by
    rw [show r * (1 - h) - x = (r - x) - r * h by ring]
    calc
      _ ≤ |r - x| + |r * h| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg hrmul]; linarith
  have hvd : |r + h - x| ≤ |r - x| + h := by
    rw [show r + h - x = (r - x) + h by ring]
    simpa [abs_of_pos hh] using abs_add_le (r - x) h
  have ha := he _ hu _ hv (hud.trans_lt hnear) (hvd.trans_lt hnear)
  have hbound := le_trans (le_abs_self _) ha
  have hwidth : r + h - r * (1 - h) = (1 + r) * h := by ring
  rw [hwidth] at hbound
  have hgap := scaled_tail_le_increment hf hdpos hr hh hh1 hrh
  nlinarith only [hgap, hbound, mul_le_mul_of_nonneg_left hud hε.le,
    mul_le_mul_of_nonneg_left hvd hε.le]

-- Balance the mod-6 product bound and the large-divisor error at m of order j³.
private lemma tail_at_inverse_square {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {j : ℕ} (hj : 2 ≤ j) :
    1 / (8 * (j : ℝ)) ≤ 1 - f (1 - 4 / (j : ℝ) ^ 2) := by
  let J : ℝ := j
  let h : ℝ := 4 / J ^ 2
  let m : ℕ := 6 * j ^ 3 + 3
  let D := ∏ p ∈ smallPrimes m, (1 - (p : ℝ)⁻¹)
  have hJ : (2 : ℝ) ≤ J := by dsimp [J]; exact_mod_cast hj
  have hJp : 0 < J := by linarith
  have hJsq : 4 ≤ J ^ 2 := by nlinarith only [hJ, sq_nonneg (J - 2)]
  have hJcube : 1 ≤ J ^ 3 := by
    calc
      1 ≤ 4 * J := by linarith
      _ ≤ J ^ 2 * J := mul_le_mul_of_nonneg_right hJsq hJp.le
      _ = J ^ 3 := by ring
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by simpa using hJsq)
  have hm : m ≠ 0 := by dsimp [m]; omega
  have htail := density_near_one hf hm hh hh1
  change D - (m : ℝ)⁻¹ / h ≤ _ at htail
  have hmreal : (m : ℝ) = 6 * J ^ 3 + 3 := by dsimp [m, J]; push_cast; rfl
  have hD : 1 / (6 * J) ≤ D := by
    have hb := wheel_product_bound (j ^ 3)
    change 1 / (27 * (6 * ((j ^ 3 : ℕ) : ℝ) + 1)) ≤ D ^ 3 at hb
    push_cast at hb
    change 1 / (27 * (6 * J ^ 3 + 1)) ≤ D ^ 3 at hb
    have hden : 27 * (6 * J ^ 3 + 1) ≤ (6 * J) ^ 3 := by
      nlinarith only [hJcube]
    have hc := (one_div_le_one_div_of_le (by positivity) hden).trans hb
    have hD0 : 0 ≤ D := Finset.prod_nonneg fun p _ => one_sub_inv_nonneg p
    have hpow : (1 / (6 * J)) ^ 3 ≤ D ^ 3 := by
      simpa only [div_pow, one_pow] using hc
    exact (pow_le_pow_iff_left₀ (by positivity) hD0 (by decide : 3 ≠ 0)).mp hpow
  have hE : (m : ℝ)⁻¹ / h ≤ 1 / (24 * J) := by
    rw [hmreal, show h = 4 / J ^ 2 by rfl, ← one_div, div_div_eq_mul_div, div_mul_eq_mul_div, div_div, one_mul]
    have hden : 0 < (6 * J ^ 3 + 3) * 4 := by positivity
    apply (div_le_div_iff₀ hden (by positivity : 0 < 24 * J)).mpr
    nlinarith only
  change 1 / (8 * J) ≤ 1 - f (1 - h)
  have hid : 1 / (6 * J) - 1 / (24 * J) = 1 / (8 * J) := by
    field_simp
    ring
  linarith only [htail, hD, hE, hid]

private lemma finite_ratio_separation {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {x y : ℝ} (hx : x < 1) (hd : HasDerivWithinAt f y (Icc 0 1) x) :
    ∃ c > 0, ∀ d : ℕ, 0 < d → c / (d : ℝ) ^ 2 < |(d.totient : ℝ) / d - x| := by
  obtain ⟨δ, hδ, hlocal⟩ := nearby_ratio_bound hf hd zero_lt_one
  let C : ℝ := 2 * |y| + 4
  have hC : 0 < C := by positivity
  let a := min δ (1 - x)
  have ha : 0 < a := lt_min hδ (sub_pos.mpr hx)
  obtain ⟨K, hK⟩ := exists_nat_gt (max 2 (max (32 * C) (8 / a)))
  have hK2 : (2 : ℝ) < K := (le_max_left _ _).trans_lt hK
  have hKC : 32 * C < K := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hK
  have hKa : 8 / a < K := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hK
  let c : ℝ := 4 / (K : ℝ) ^ 2
  refine ⟨c, by positivity, fun d hdpos => ?_⟩
  let r : ℝ := (d.totient : ℝ) / d
  let j : ℕ := K * d
  let J : ℝ := j
  let h : ℝ := 4 / J ^ 2
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
  have hdp : (0 : ℝ) < d := by positivity
  have hJ : J = (K : ℝ) * (d : ℝ) := by simp [J, j]
  have hKJ : (K : ℝ) ≤ J := by
    rw [hJ]
    exact le_mul_of_one_le_right (by positivity) hd1
  have hJ2 : (2 : ℝ) ≤ J := hK2.le.trans hKJ
  have hJp : 0 < J := by linarith
  have hj : 2 ≤ j := by dsimp [J] at hJ2; exact_mod_cast hJ2
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < J ^ 2)).mpr
    nlinarith only [hJ2, sq_nonneg (J - 2)]
  have heqh : c / (d : ℝ) ^ 2 = h := by rw [show h = 4 / J ^ 2 by rfl, hJ, mul_pow]; simp [c, div_div]
  rw [heqh]
  by_contra! hdist
  have hha : 2 * h < a := by
    have hs : J ≤ J ^ 2 := by nlinarith only [hJ2, sq_nonneg (J - 1)]
    have h8 : 8 < a * J := by
      have := (div_lt_iff₀ ha).mp (hKa.trans_le hKJ)
      simpa [mul_comm] using this
    have h8' := h8.trans_le (mul_le_mul_of_nonneg_left hs ha.le)
    dsimp [h]
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ (by positivity)).mpr (by norm_num; exact h8')
  have hrx := (abs_le.mp hdist).2
  have hrh : r + h ≤ 1 := by
    have := hha.trans_le (min_le_right _ _)
    linarith
  have hnear : |r - x| + h < δ := by
    have := hha.trans_le (min_le_left _ _)
    linarith
  have hupper := hlocal d hdpos r h rfl hh hh1 hrh hnear
  have hcoeff : y * ((1 + r) * h) ≤ (2 * |y|) * h := calc
    _ ≤ |y| * ((1 + r) * h) := by
      apply mul_le_mul_of_nonneg_right (le_abs_self _)
      have hr0 : 0 ≤ r := by dsimp [r]; positivity
      positivity
    _ ≤ _ := by
      have hr1 : r ≤ 1 := by linarith
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (show 1 + r ≤ 2 by linarith)
        hh.le) (abs_nonneg y)
      linarith only [this]
  have htail := tail_at_inverse_square hf hj
  change 1 / (8 * J) ≤ 1 - f (1 - h) at htail
  have hchain : (1 / (8 * J)) / (d : ℝ) ≤ C * h := by
    have hmain := (div_le_div_of_nonneg_right htail hdp.le).trans hupper
    dsimp [C]
    linarith only [hmain, hcoeff, hdist]
  have hcross : J ^ 2 ≤ (C * 4) * (8 * J * (d : ℝ)) := by
    rw [div_div, show h = 4 / J ^ 2 by rfl, ← mul_div_assoc] at hchain
    have := (div_le_div_iff₀ (by positivity : 0 < 8 * J * (d : ℝ))
      (by positivity : 0 < J ^ 2)).mp hchain
    simpa using this
  have hstrict : 32 * C * (d : ℝ) < J := by
    rw [hJ]
    exact mul_lt_mul_of_pos_right hKC hdp
  nlinarith only [hcross, mul_pos (sub_pos.mpr hstrict) hJp]

private lemma prime_product_ratio (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ d : ℕ, 0 < d ∧ (d.totient : ℝ) / d = ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
  let d := ∏ p ∈ P, p
  have hd : 0 < d := Finset.prod_pos fun p hp => (hP p hp).pos
  have hfac : d.primeFactors = P := by
    ext p
    rw [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpd, _⟩
      obtain ⟨q, hq, hdvd⟩ := (hp.prime.dvd_finsetProd_iff id).mp hpd
      rcases (Nat.dvd_prime (hP q hq)).mp hdvd with he | he
      · exact (hp.ne_one he).elim
      · rwa [he]
    · intro hp
      exact ⟨hP p hp, Finset.dvd_prod_of_mem id hp, hd.ne'⟩
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  exact ⟨d, hd, by rw [phi_product, mul_div_cancel_left₀ _ hd', hfac]⟩

private lemma finite_ratio_between {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) :
    ∃ d : ℕ, 0 < d ∧ (d.totient : ℝ) / d ∈ Ioo a b := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_gt (b - a)⁻¹
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hmp : 0 < (m : ℝ) := (inv_pos.mpr hgap).trans hm
  have hm' : (m : ℝ)⁻¹ < b - a := by
    have hi := (inv_lt_inv₀ hmp (inv_pos.mpr hgap)).mpr hm
    simpa using hi
  let P (n : ℕ) := (Finset.range n).filter (fun p => p.Prime ∧ m < p)
  let g (n : ℕ) := ∏ p ∈ P n, (1 - (p : ℝ)⁻¹)
  let w (p : ℕ) : ℝ := if p.Prime then (p : ℝ)⁻¹ else 0
  have hw (p : ℕ) : 0 ≤ w p := by dsimp [w]; split_ifs <;> positivity
  have hunbounded (B : ℝ) : ∃ n, B < ∑ p ∈ P n, (p : ℝ)⁻¹ := by
    by_contra! hbound
    apply not_summable_one_div_on_primes
    have heq : Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) = w := by
      funext n
      simp [w, Set.indicator, one_div]
    rw [heq]
    apply summable_of_sum_range_le hw (c := B + ∑ p ∈ Finset.range (m + 1), w p)
    intro n
    let t := (Finset.range n).filter (fun p => m < p)
    let u := (Finset.range n).filter (fun p => p ≤ m)
    have hsum : (∑ p ∈ t, w p) = ∑ p ∈ P n, (p : ℝ)⁻¹ := by
      simp only [w, ← Finset.sum_filter, t, Finset.filter_filter, P, and_comm]
    have hu : u ⊆ Finset.range (m + 1) := by
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    have hsplit : (∑ p ∈ t, w p) + ∑ p ∈ u, w p = ∑ p ∈ Finset.range n, w p := by
      simpa only [t, u, not_lt] using
        (Finset.sum_filter_add_sum_filter_not (s := Finset.range n) (p := fun p => m < p) w)
    rw [← hsplit, hsum]
    exact add_le_add (hbound n) (Finset.sum_le_sum_of_subset_of_nonneg hu fun i _ _ => hw i)
  have hexists : ∃ n, g n < b := by
    obtain ⟨n, hn⟩ := hunbounded (-Real.log b)
    refine ⟨n, lt_of_le_of_lt ?_ ((Real.exp_lt_exp.mpr (by linarith : -(∑ p ∈ P n, (p : ℝ)⁻¹) <
      Real.log b)).trans_le (le_of_eq (Real.exp_log (ha.trans hab))))⟩
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun p _ => one_sub_inv_nonneg p)
      (fun p _ => Real.one_sub_le_exp_neg _)
  let n := Nat.find hexists
  have hn : g n < b := Nat.find_spec hexists
  have hn0 : n ≠ 0 := by
    intro he
    rw [he, show g 0 = 1 by simp [g, P]] at hn
    exact (not_lt_of_ge hb) hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hprev : b ≤ g k := le_of_not_gt (Nat.find_min hexists (show k < n by omega))
  have hstep : g k - g n ≤ (m : ℝ)⁻¹ := by
    rw [hk]
    have hle : g k ≤ 1 := Finset.prod_le_one
      (fun p _ => one_sub_inv_nonneg p) (fun p _ => sub_le_self _ (by positivity))
    by_cases hp : k.Prime ∧ m < k
    · have hnext : g (k + 1) = (1 - (k : ℝ)⁻¹) * g k := by
        simp [g, P, Finset.range_add_one, Finset.filter_insert, hp,
          Finset.prod_insert]
      rw [hnext]
      calc
        _ = (k : ℝ)⁻¹ * g k := by ring
        _ ≤ (k : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ _ := by
          rw [mul_one]
          exact inv_anti₀ hmp (by exact_mod_cast hp.2.le)
    · have hnext : g (k + 1) = g k := by
        simp [g, P, Finset.range_add_one, Finset.filter_insert, hp]
      rw [hnext, sub_self]
      positivity
  obtain ⟨d, hd, hdg⟩ := prime_product_ratio (P n) fun p hp => (Finset.mem_filter.mp hp).2.1
  exact ⟨d, hd, by rw [hdg]; exact ⟨by linarith, hn⟩⟩

private lemma dense_nondifferentiability {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f) :
    ∃ S : Set (Ioo (0 : ℝ) 1), Dense S ∧ IsGδ S ∧
      ∀ x ∈ S, ∀ y : ℝ, ¬ HasDerivWithinAt f y (Icc 0 1) (x : ℝ) := by
  let I := Ioo (0 : ℝ) 1
  let : BaireSpace I := (isOpen_Ioo (a := (0 : ℝ)) (b := 1)).baireSpace
  let r (d : ℕ) : ℝ := (d.totient : ℝ) / d
  let U (k : ℕ) : Set I :=
    ⋃ (d : ℕ) (_ : 0 < d), (fun x : I => (x : ℝ)) ⁻¹'
      Metric.ball (r d) ((1 / ((k : ℝ) + 1)) / (d : ℝ) ^ 2)
  have hopen (k : ℕ) : IsOpen (U k) :=
    isOpen_iUnion fun d => isOpen_iUnion fun _ => Metric.isOpen_ball.preimage continuous_subtype_val
  have hU (k : ℕ) : Dense (U k) := by
    rw [Metric.dense_iff]
    intro x ε hε
    let a := max 0 ((x : ℝ) - ε)
    let b := min 1 ((x : ℝ) + ε)
    have hax : a < (x : ℝ) := max_lt x.property.1 (by linarith)
    have hxb : (x : ℝ) < b := lt_min x.property.2 (by linarith)
    obtain ⟨d, hd, hda, hdb⟩ := finite_ratio_between
      (show 0 < (a + x) / 2 by
        have := le_max_left (0 : ℝ) ((x : ℝ) - ε)
        have := x.property.1
        linarith)
      (show (a + x) / 2 < b by linarith)
      (min_le_left _ _)
    have hra : a < r d := by change (a + (x : ℝ)) / 2 < r d at hda; linarith
    have hrb : r d < b := hdb
    let z : I := ⟨r d, (le_max_left _ _).trans_lt hra, hrb.trans_le (min_le_left _ _)⟩
    refine ⟨z, ?_, ?_⟩
    · change dist (r d) (x : ℝ) < ε
      rw [Real.dist_eq, abs_lt]
      exact ⟨by have := (le_max_right _ _).trans_lt hra; linarith,
        by have := hrb.trans_le (min_le_right _ _); linarith⟩
    · change z ∈ ⋃ (d : ℕ) (_ : 0 < d), (fun x : I => (x : ℝ)) ⁻¹'
        Metric.ball (r d) ((1 / ((k : ℝ) + 1)) / (d : ℝ) ^ 2)
      simp only [Set.mem_iUnion]
      refine ⟨d, hd, ?_⟩
      change dist (r d) (r d) < (1 / ((k : ℝ) + 1)) / (d : ℝ) ^ 2
      rw [dist_self]
      positivity
  refine ⟨⋂ k, U k, dense_iInter_of_isOpen_nat hopen hU, IsGδ.iInter (fun k => (hopen k).isGδ), ?_⟩
  intro x hx y hd
  obtain ⟨c, hc, hsep⟩ := finite_ratio_separation hf x.property.2 hd
  obtain ⟨k, hk⟩ := exists_nat_gt c⁻¹
  have hmem := Set.mem_iInter.mp hx k
  dsimp only [U] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨d, hd', hz⟩ := hmem
  have hz' : dist (x : ℝ) (r d) < (1 / ((k : ℝ) + 1)) / (d : ℝ) ^ 2 := hz
  have hsmall : 1 / ((k : ℝ) + 1) ≤ c := by
    rw [one_div, ← inv_inv c]
    exact inv_anti₀ (inv_pos.mpr hc) (by linarith)
  rw [dist_comm, Real.dist_eq] at hz'
  exact (not_lt.mpr ((div_le_div_of_nonneg_right hsmall (by positivity)).trans
    (hsep d hd').le)) hz'

-- Count occurrences of a prime divisor among the integers up to m.
private lemma weighted_prime_reciprocals {m : ℕ} (hm : 0 < m) :
    (∑ p ∈ smallPrimes m, Real.log (p : ℝ) / p) ≤ 2 * Real.log (m : ℝ) := by
  classical
  let P := smallPrimes m
  let S := (Finset.range (m + 1)).filter (fun n => n ≠ 0)
  let w (p : ℕ) := Real.log (p : ℝ)
  have hupper : (∑ p ∈ P, ((m / p : ℕ) : ℝ) * w p) ≤ m * w m := by
    calc
      _ = ∑ p ∈ P, ∑ n ∈ S, if p ∣ n then w p else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter,
          Nat.card_multiples']
      _ = ∑ n ∈ S, ∑ p ∈ P, if p ∣ n then w p else 0 := Finset.sum_comm
      _ ≤ ∑ _n ∈ S, w m := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hnm, hn0⟩ := Finset.mem_filter.mp hn
        have hnm' : n ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hnm)
        have hP : P.filter (fun p => p ∣ n) = n.primeFactors := by
          ext p
          simp only [Finset.mem_filter, mem_smallPrimes, Nat.mem_primeFactors, P]
          exact ⟨fun ⟨⟨_, hp⟩, hpd⟩ => ⟨hp, hpd, hn0⟩,
            fun ⟨hp, hpd, _⟩ => ⟨⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd).trans hnm', hp⟩, hpd⟩⟩
        rw [← Finset.sum_filter, hP]
        have hprod : 0 < ∏ p ∈ n.primeFactors, p :=
          Finset.prod_pos fun p hp => (Nat.mem_primeFactors.mp hp).1.pos
        have hle : (∏ p ∈ n.primeFactors, p) ≤ m :=
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.prod_primeFactors_dvd n)).trans hnm'
        have hlog := Real.log_le_log (Nat.cast_pos.mpr hprod : 0 < (((∏ p ∈ n.primeFactors, p) : ℕ) : ℝ))
          (Nat.cast_le.mpr hle : (((∏ p ∈ n.primeFactors, p) : ℕ) : ℝ) ≤ m)
        push_cast at hlog
        rwa [Real.log_prod (fun p hp => by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero)] at hlog
      _ = _ := by simp [S, Finset.filter_ne']
  have hlower : ((m : ℝ) / 2) * (∑ p ∈ P, w p / p) ≤
      ∑ p ∈ P, ((m / p : ℕ) : ℝ) * w p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hpm, hprime⟩ := mem_smallPrimes.mp hp
    have hp' : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hfloor : (m : ℝ) ≤ 2 * ((m / p : ℕ) : ℝ) * p := by
      have hmod := Nat.mod_lt m hprime.pos
      have hquot : 1 ≤ m / p := (Nat.le_div_iff_mul_le hprime.pos).mpr (by simpa using hpm)
      have hmle : m ≤ 2 * (m / p) * p := by
        have hterm := Nat.mul_le_mul_right p hquot
        have hdiv := Nat.mod_add_div m p
        nlinarith only [hterm, hdiv, hmod]
      exact_mod_cast hmle
    have hbound := (div_le_iff₀ hp').mpr (show (m : ℝ) / 2 ≤ ((m / p : ℕ) : ℝ) * p by linarith)
    calc
      _ = ((m : ℝ) / 2 / p) * w p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound
        (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le : (1 : ℝ) ≤ p))
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  apply le_of_mul_le_mul_left ?_ (show 0 < (m : ℝ) / 2 by positivity)
  convert hlower.trans hupper using 1
  change (m : ℝ) / 2 * (2 * Real.log (m : ℝ)) = (m : ℝ) * Real.log (m : ℝ)
  ring

private lemma inverse_zeta_bound {t : ℝ} (ht : 0 < t) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (1 + t⁻¹)⁻¹ ≤ ∏ p ∈ P, (1 - (p : ℝ) ^ (-1 - t)) := by
  let s : ℝ := -1 - t
  have hs : s < -1 := by dsimp [s]; linarith
  let F : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ) ^ s
      map_one' := by simp
      map_mul' := by intro a b; push_cast; exact Real.mul_rpow (by positivity) (by positivity) }
  have hsum : Summable F := by
    change Summable (fun n : ℕ => (n : ℝ) ^ s)
    have h := Real.summable_one_div_nat_rpow.mpr (show 1 < -s by linarith)
    simpa only [one_div, Real.rpow_neg (Nat.cast_nonneg _), neg_neg, inv_inv] using h
  have hnorm {p : ℕ} (hp : p.Prime) : ‖F p‖ < 1 := by
    rw [Real.norm_of_nonneg (by change 0 ≤ (p : ℝ) ^ s; positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have heq := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := F) hnorm P).2.tsum_eq
  rw [Finset.filter_eq_self.mpr hP] at heq
  have htsum : (∑' n : ℕ, F n) ≤ 1 + t⁻¹ := by
    have hant : AntitoneOn (fun x : ℝ => x ^ s) (Ici ((1 : ℕ) : ℝ)) :=
      fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos
        (zero_lt_one.trans_le (by simpa only [Nat.cast_one] using mem_Ici.mp hx)) hxy (by linarith)
    have htail := hant.tsum_comp_add_le_integral 1
      (integrableOn_Ioi_rpow_of_lt hs (by norm_num))
      (fun x hx => Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) s)
    rw [integral_Ioi_rpow_of_lt hs (by norm_num)] at htail
    have hshift : Summable (fun n : ℕ => F (n + 1)) :=
      hsum.comp_injective (fun _ _ hab => Nat.add_right_cancel hab)
    rw [hsum.tsum_eq_zero_add, hshift.tsum_eq_zero_add]
    change ((0 : ℕ) : ℝ) ^ s +
      (((0 + 1 : ℕ) : ℝ) ^ s + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ s) ≤ _
    rw [Nat.zero_add, Nat.cast_zero, Nat.cast_one, Real.zero_rpow (by linarith), Real.one_rpow, zero_add]
    have hs1 : s + 1 = -t := by dsimp [s]; ring
    rw [hs1] at htail
    exact add_le_add le_rfl (by
      simpa only [Nat.cast_one, Real.one_rpow, neg_div, div_neg, neg_neg, one_div] using htail)
  have hsub : (∑' n : Nat.factoredNumbers P, F n) ≤ ∑' n : ℕ, F n :=
    hsum.tsum_subtype_le F (Nat.factoredNumbers P) (fun n => by change 0 ≤ (n : ℝ) ^ s; positivity)
  have hp : ∀ p ∈ P, 0 < 1 - F p := by
    intro p hp
    have h := hnorm (hP p hp)
    rw [Real.norm_of_nonneg (by change 0 ≤ (p : ℝ) ^ s; positivity)] at h
    exact sub_pos.mpr h
  have hprod : 0 < ∏ p ∈ P, (1 - F p) := Finset.prod_pos hp
  have hle := hsub.trans htsum
  rw [heq, Finset.prod_inv_distrib] at hle
  exact (inv_le_comm₀ (by positivity) hprod).mpr hle

-- Compare with the absolutely convergent Euler product at 1 + t.
private lemma prime_product_log_bound {m : ℕ} (hm : 0 < m) :
    Real.exp (-4) / (2 + Real.log (m : ℝ)) ≤
      ∏ p ∈ smallPrimes m, (1 - (p : ℝ)⁻¹) := by
  let P := smallPrimes m
  let t := (1 + Real.log (m : ℝ))⁻¹
  let D := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)
  let v (p : ℕ) := 2 * t * (Real.log (p : ℝ) / p)
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have ht : 0 < t := by dsimp [t]; positivity
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (mem_smallPrimes.mp hp).2
  have hlocal (p : ℕ) (hp : p ∈ P) :
      1 - (p : ℝ) ^ (-1 - t) ≤ (1 - (p : ℝ)⁻¹) * Real.exp (v p) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    have hpp : (0 : ℝ) < p := by linarith
    let a := (p : ℝ)⁻¹
    let b := t * Real.log (p : ℝ)
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have ha2 : a ≤ 1 / 2 := by
      simpa [a, one_div] using inv_anti₀ (by norm_num : 0 < (2 : ℝ)) hp2
    have hb : 0 ≤ b := by
      exact mul_nonneg ht.le (Real.log_nonneg (by linarith))
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    have hv : v p = 2 * (a * b) := by dsimp [v, a, b]; rw [div_eq_mul_inv]; ring
    have hpow : (p : ℝ) ^ (-1 - t) = a * Real.exp (-b) := by
      rw [sub_eq_add_neg, Real.rpow_add hpp, Real.rpow_neg_one, Real.rpow_def_of_pos hpp]
      congr 2
      dsimp [b]
      ring
    rw [hpow, hv]
    have hexp : 1 + 2 * (a * b) ≤ Real.exp (2 * (a * b)) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * (a * b))
    calc
      _ = 1 - a + a * (1 - Real.exp (-b)) := by ring
      _ ≤ 1 - a + a * b :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (show 1 - Real.exp (-b) ≤ b by linarith [Real.one_sub_le_exp_neg b]) ha)
      _ ≤ (1 - a) * (1 + 2 * (a * b)) := by
        nlinarith only [mul_nonneg (show 0 ≤ 1 - 2 * a by linarith) hab]
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp
        (by linarith)
  have hsum : (∑ p ∈ P, v p) ≤ 4 := by
    dsimp only [v]
    rw [← Finset.mul_sum]
    have htlog : t * Real.log (m : ℝ) ≤ 1 := by
      rw [show t = (1 + Real.log (m : ℝ))⁻¹ by rfl, ← div_eq_inv_mul]
      exact (div_le_one₀ (by positivity)).mpr (by linarith)
    have h := mul_le_mul_of_nonneg_left (weighted_prime_reciprocals hm) (by positivity : 0 ≤ 2 * t)
    nlinarith only [h, htlog]
  have hD : 0 ≤ D := Finset.prod_nonneg fun p _ => one_sub_inv_nonneg p
  have hprod : (∏ p ∈ P, (1 - (p : ℝ) ^ (-1 - t))) ≤ D * Real.exp 4 := by
    calc
      _ ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹) * Real.exp (v p) := by
        refine Finset.prod_le_prod (fun p hp => sub_nonneg.mpr ?_) hlocal
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (hprime p hp).one_lt
        exact (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)).le
      _ = D * Real.exp (∑ p ∈ P, v p) := by rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) hD
  have hz := (inverse_zeta_bound ht P hprime).trans hprod
  rw [show t⁻¹ = 1 + Real.log (m : ℝ) by simp [t],
    show (1 : ℝ) + (1 + Real.log (m : ℝ)) = 2 + Real.log (m : ℝ) by ring] at hz
  change Real.exp (-4) / (2 + Real.log (m : ℝ)) ≤ D
  rw [Real.exp_neg, div_eq_mul_inv, mul_comm, ← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.exp_pos 4)).mpr hz

private lemma small_scale_log_limit :
    Tendsto (fun h : ℝ => h * (1 + Real.log h⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
  simp only [Real.rpow_one] at hlog
  have h := (tendsto_id.mono_left nhdsWithin_le_nhds).sub hlog
  have heq (h : ℝ) : h - Real.log h * h = h * (1 + Real.log h⁻¹) := by
    rw [Real.log_inv]
    ring
  simpa only [id_eq, sub_zero, heq] using h

private lemma logarithmic_tail_lower {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ 1 → h < δ →
      (Real.exp (-4) / 6) / (1 + Real.log h⁻¹) ≤ 1 - f (1 - h) := by
  have hc : 0 < Real.exp (-4) / 6 := by positivity
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp
    (small_scale_log_limit.eventually (gt_mem_nhds hc))
  refine ⟨δ, hδ, fun h hh hh1 hhδ => ?_⟩
  have hmem : h ∈ Metric.ball (0 : ℝ) δ ∩ Ioi 0 := by
    exact ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hh] using hhδ, hh⟩
  have he : h * (1 + Real.log h⁻¹) < Real.exp (-4) / 6 := hsmall hmem
  have hi : 1 ≤ h⁻¹ := by simpa using inv_anti₀ hh hh1
  have hi0 : 0 < h⁻¹ := inv_pos.mpr hh
  have hlog0 : 0 ≤ Real.log h⁻¹ := Real.log_nonneg hi
  have hlam : 0 < 1 + Real.log h⁻¹ := by linarith
  have he' : h ≤ (Real.exp (-4) / 6) / (1 + Real.log h⁻¹) :=
    (le_div_iff₀ hlam).mpr he.le
  let m := ⌈h⁻¹ ^ 2⌉₊
  have hm : 0 < m := Nat.ceil_pos.mpr (by positivity)
  have hml : h⁻¹ ^ 2 ≤ (m : ℝ) := Nat.le_ceil _
  have hmu : (m : ℝ) ≤ 2 * h⁻¹ ^ 2 := by
    have hceil := Nat.ceil_lt_add_one (sq_nonneg h⁻¹)
    change (m : ℝ) < h⁻¹ ^ 2 + 1 at hceil
    nlinarith only [hceil, hi, sq_nonneg (h⁻¹ - 1)]
  have hE : (m : ℝ)⁻¹ / h ≤ h := by
    apply (div_le_iff₀ hh).mpr
    have h := inv_anti₀ (by positivity : 0 < h⁻¹ ^ 2) hml
    rw [inv_pow, inv_inv] at h
    simpa only [pow_two] using h
  have hlog := Real.log_le_log (by exact_mod_cast hm : 0 < (m : ℝ)) hmu
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hlog
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hden : 2 + Real.log (m : ℝ) ≤ 3 * (1 + Real.log h⁻¹) := by
    norm_num at hlog hlog2 hlog0 ⊢
    linarith only [hlog, hlog2, hlog0]
  have hD : 2 * ((Real.exp (-4) / 6) / (1 + Real.log h⁻¹)) ≤
      ∏ p ∈ smallPrimes m, (1 - (p : ℝ)⁻¹) := by
    have hp : 0 < 2 + Real.log (m : ℝ) := by
      have hlogm := Real.log_nonneg (by exact_mod_cast hm : (1 : ℝ) ≤ m)
      linarith
    have hprod := (div_le_div_of_nonneg_left (Real.exp_pos (-4)).le hp hden).trans
      (prime_product_log_bound hm)
    calc
      _ = Real.exp (-4) / (3 * (1 + Real.log h⁻¹)) := by
        field_simp [hlam.ne']
        ring
      _ ≤ _ := hprod
  have htail := density_near_one hf hm.ne' hh hh1
  linarith only [htail, hD, hE, he']

private lemma logarithmic_ratio_separation {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {x y : ℝ} (hx : x < 1) (hd : HasDerivWithinAt f y (Icc 0 1) x) :
    ∃ c > 0, ∃ δ > 0, ∀ d : ℕ, 0 < d →
      let h := |(d.totient : ℝ) / d - x|
      0 < h → h < δ → c ≤ (d : ℝ) * h * (1 + Real.log h⁻¹) := by
  obtain ⟨δ₁, hδ₁, htail⟩ := logarithmic_tail_lower hf
  obtain ⟨δ₂, hδ₂, hlocal⟩ := nearby_ratio_bound hf hd zero_lt_one
  let C := 2 * |y| + 4
  have hC : 0 < C := by positivity
  let δ := min 1 (min δ₁ (min (δ₂ / 2) ((1 - x) / 2)))
  have hδ : 0 < δ := lt_min one_pos (lt_min hδ₁ (lt_min (by positivity) (by linarith)))
  let K := Real.exp (-4) / 6
  refine ⟨K / C, by positivity, δ, hδ, fun d hdpos => ?_⟩
  dsimp only
  let r : ℝ := (d.totient : ℝ) / d
  let h := |r - x|
  change 0 < h → h < δ → K / C ≤ (d : ℝ) * h * (1 + Real.log h⁻¹)
  intro hh hhδ
  have hh1 := hhδ.le.trans (min_le_left _ _)
  have hhδ₁ := hhδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhδ₂ := hhδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhx := hhδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hrx : r - x ≤ h := le_abs_self _
  have hrh : r + h ≤ 1 := by linarith
  have hupper := hlocal d hdpos r h rfl hh hh1 hrh (show |r - x| + h < δ₂ by change h + h < δ₂; linarith)
  have hcoeff : y * ((1 + r) * h) ≤ (2 * |y|) * h := calc
    _ ≤ |y| * ((1 + r) * h) := by
      apply mul_le_mul_of_nonneg_right (le_abs_self _)
      have hr0 : 0 ≤ r := by dsimp [r]; positivity
      positivity
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (show 1 + r ≤ 2 by linarith) hh.le) (abs_nonneg y)
      linarith only [hb]
  have htop : (1 - f (1 - h)) / d ≤ C * h := by
    change (1 - f (1 - h)) / d ≤ y * ((1 + r) * h) + 2 * 1 * (h + h) at hupper
    dsimp [C]
    linarith only [hupper, hcoeff]
  have hb := htail h hh hh1 hhδ₁
  have hi : 1 ≤ h⁻¹ := by simpa using inv_anti₀ hh hh1
  have hlog : 0 < 1 + Real.log h⁻¹ := by linarith [Real.log_nonneg hi]
  have hdp : 0 < (d : ℝ) := by positivity
  change K / (1 + Real.log h⁻¹) ≤ _ at hb
  have hbound := hb.trans ((div_le_iff₀ hdp).mp htop)
  have hcross := (div_le_iff₀ hlog).mp hbound
  apply (div_le_iff₀ hC).mpr
  linarith only [hcross]

private lemma scale_log_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    a * (1 + Real.log a⁻¹) ≤ b * (1 + Real.log b⁻¹) := by
  have hb0 := ha.trans_le hab
  have hdiv := Real.log_le_sub_one_of_pos (div_pos hb0 ha)
  rw [Real.log_div hb0.ne' ha.ne'] at hdiv
  have hmul := mul_le_mul_of_nonneg_left hdiv ha.le
  rw [mul_sub, mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ _ ha.ne'] at hmul
  have hl := mul_nonneg (sub_nonneg.mpr hab) (neg_nonneg.mpr (Real.log_nonpos hb0.le hb))
  simp only [Real.log_inv]
  nlinarith only [hmul, hl]

private lemma finite_ratio_log_separation {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {x y : ℝ} (hx : x < 1) (hd : HasDerivWithinAt f y (Icc 0 1) x) :
    ∃ c > 0, ∀ d : ℕ, 0 < d →
      c / ((d : ℝ) * (1 + Real.log (d : ℝ))) < |(d.totient : ℝ) / d - x| := by
  obtain ⟨K, hK, δ, hδ, hsep⟩ := logarithmic_ratio_separation hf hx hd
  obtain ⟨u, hu, hnonzero⟩ := finite_ratio_separation hf hx hd
  have hlim : Tendsto (fun c : ℝ => c * (2 + Real.log c⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    have h := small_scale_log_limit.add (tendsto_id.mono_left nhdsWithin_le_nhds)
    simp only [add_zero] at h
    refine h.congr fun c => ?_
    simp only [id_eq]
    ring
  obtain ⟨η, hη, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp
    (hlim.eventually (gt_mem_nhds hK))
  let c := min (η / 2) (min (δ / 2) 1)
  have hc : 0 < c := lt_min (by positivity) (lt_min (by positivity) one_pos)
  have hcη : c < η := (min_le_left _ _).trans_lt (by linarith)
  have hcδ : c < δ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hm : c ∈ Metric.ball (0 : ℝ) η ∩ Ioi 0 :=
    ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hc] using hcη, hc⟩
  have hconstant : c * (2 + Real.log c⁻¹) < K := hsmall hm
  refine ⟨c, hc, fun d hdpos => ?_⟩
  let D : ℝ := d
  let L := 1 + Real.log D
  let h := |(d.totient : ℝ) / d - x|
  let H := c / (D * L)
  change H < h
  by_contra! hclose
  have hD1 : 1 ≤ D := by dsimp [D]; exact_mod_cast hdpos
  have hDp : 0 < D := zero_lt_one.trans_le hD1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hD1]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hDL : 0 < D * L := mul_pos hDp hLp
  have hHc : H ≤ c := by
    apply (div_le_iff₀ hDL).mpr
    calc
      c = c * 1 := by ring
      _ ≤ c * (D * L) := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hD1 hL1) hc.le
  have hHp : 0 < H := div_pos hc hDL
  have hH1 : H ≤ 1 := hHc.trans hc1
  have hh : 0 < h := (by positivity : 0 < u / (d : ℝ) ^ 2).trans (hnonzero d hdpos)
  have hhδ : h < δ := (hclose.trans hHc).trans_lt hcδ
  have hlow := hsep d hdpos hh hhδ
  have hmomo := mul_le_mul_of_nonneg_left (scale_log_mono hh hclose hH1) hDp.le
  have hLlog : Real.log L ≤ Real.log D := by
    have h := Real.log_le_sub_one_of_pos hLp
    dsimp [L] at h
    linarith only [h]
  have hci : 1 ≤ c⁻¹ := by simpa using inv_anti₀ hc hc1
  have hclog : 0 ≤ Real.log c⁻¹ := Real.log_nonneg hci
  have hHlog : 1 + Real.log H⁻¹ ≤ (2 + Real.log c⁻¹) * L := by
    rw [show H⁻¹ = D * L * c⁻¹ by simp [H, div_eq_mul_inv, mul_comm],
      Real.log_mul hDL.ne' (inv_ne_zero hc.ne'), Real.log_mul hDp.ne' hLp.ne']
    have h := mul_le_mul_of_nonneg_left hL1 (show 0 ≤ Real.log c⁻¹ by exact hclog)
    dsimp [L] at h ⊢
    nlinarith only [h, hLlog]
  have hupper : D * (H * (1 + Real.log H⁻¹)) ≤ c * (2 + Real.log c⁻¹) := calc
    _ ≤ D * (H * ((2 + Real.log c⁻¹) * L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHlog hHp.le) hDp.le
    _ = _ := by dsimp only [H]; field_simp
  have hcross : K ≤ D * (h * (1 + Real.log h⁻¹)) := by
    simpa only [mul_assoc] using hlow
  exact (not_lt_of_ge (hcross.trans (hmomo.trans hupper))) hconstant

private lemma logarithmic_ratio_divergence {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {x y : ℝ} (hx : x < 1) (hd : HasDerivWithinAt f y (Icc 0 1) x) :
    ∀ B > (0 : ℝ), ∃ δ > 0, ∀ d : ℕ, 0 < d →
      let a := |(d.totient : ℝ) / d - x|
      0 < a → a < δ → B ≤ (d : ℝ) * a * (1 + Real.log a⁻¹) := by
  intro B hB
  obtain ⟨δ₁, hδ₁, htail⟩ := logarithmic_tail_lower hf
  let C := 2 * |y| + 4
  let K := Real.exp (-4) / 6
  have hC : 0 < C := by positivity
  have hK : 0 < K := by positivity
  let η := min 1 (K / (2 * C * B))
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηB : η * (2 * C * B) ≤ K := by
    exact (le_div_iff₀ (by positivity : 0 < 2 * C * B)).mp (min_le_right _ _)
  obtain ⟨δ₂, hδ₂, hlocal⟩ := nearby_ratio_bound hf hd hη
  let δ := min η (min δ₁ (min (δ₂ / 2) ((1 - x) / 2)))
  have hδ : 0 < δ := lt_min hη (lt_min hδ₁ (lt_min (by positivity) (by linarith)))
  refine ⟨δ, hδ, fun d hdpos => ?_⟩
  dsimp only
  let r : ℝ := (d.totient : ℝ) / d
  let a := |r - x|
  let h := η * a
  change 0 < a → a < δ → B ≤ (d : ℝ) * a * (1 + Real.log a⁻¹)
  intro ha haδ
  have hh : 0 < h := mul_pos hη ha
  have hha : h ≤ a := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hη1 ha.le
  have haη := haδ.trans_le (min_le_left _ _)
  have hh1 := hha.trans (haη.le.trans hη1)
  have hhδ₁ := hha.trans_lt (haδ.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have haδ₂ := haδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hax := haδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hrx : r - x ≤ a := le_abs_self _
  have hrh : r + h ≤ 1 := by linarith
  have hupper := hlocal d hdpos r h rfl hh hh1 hrh (show |r - x| + h < δ₂ by change a + h < δ₂; linarith)
  have hcoeff : y * ((1 + r) * h) ≤ (2 * |y|) * h := calc
    _ ≤ |y| * ((1 + r) * h) := by
      apply mul_le_mul_of_nonneg_right (le_abs_self _)
      have hr0 : 0 ≤ r := by dsimp [r]; positivity
      positivity
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (show 1 + r ≤ 2 by linarith) hh.le) (abs_nonneg y)
      linarith only [hb]
  have htop : (1 - f (1 - h)) / d ≤ C * (η * a) := by
    change (1 - f (1 - h)) / d ≤ y * ((1 + r) * h) + 2 * η * (a + h) at hupper
    have herr := mul_le_mul_of_nonneg_left hha (show 0 ≤ 2 * η by positivity)
    dsimp only [C]
    change _ ≤ (2 * |y| + 4) * h
    nlinarith only [hupper, hcoeff, herr]
  have hdp : 0 < (d : ℝ) := by positivity
  have hloginv : 0 < 1 + Real.log h⁻¹ := by
    have hi : 1 ≤ h⁻¹ := by simpa using inv_anti₀ hh hh1
    linarith [Real.log_nonneg hi]
  have hlog : 1 + Real.log h⁻¹ ≤ 2 * (1 + Real.log a⁻¹) := by
    have hlogη := Real.log_le_log (inv_pos.mpr hη) (inv_anti₀ ha haη.le)
    rw [show h⁻¹ = η⁻¹ * a⁻¹ by simp [h, mul_comm], Real.log_mul (inv_ne_zero hη.ne') (inv_ne_zero ha.ne')]
    linarith only [hlogη]
  have htail' := htail h hh hh1 hhδ₁
  change K / (1 + Real.log h⁻¹) ≤ _ at htail'
  have hcross := (div_le_iff₀ hloginv).mp (htail'.trans ((div_le_iff₀ hdp).mp htop))
  have hscale := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C * (η * a) * (d : ℝ) by positivity)
  have hmain : K ≤ (2 * C * η) * ((d : ℝ) * a * (1 + Real.log a⁻¹)) := by
    nlinarith only [hcross, hscale]
  apply le_of_mul_le_mul_left ?_ (show 0 < 2 * C * η by positivity)
  exact (show 2 * C * η * B ≤ K by linarith only [hηB]).trans hmain

private lemma density_finset_dilates_le {S T : Set ℕ} {a b : ℝ}
    (hs : S.HasDensity a) (ht : T.HasDensity b) (D : Finset ℕ)
    (hpos : ∀ d ∈ D, 0 < d) (hmaps : ∀ d ∈ D, ∀ n ∈ S, d * n ∈ T)
    (hdisj : ∀ d ∈ D, ∀ e ∈ D, ∀ n ∈ S, ∀ m ∈ S, d * n = e * m → d = e) :
    a * (∑ d ∈ D, (d : ℝ)⁻¹) ≤ b := by
  classical
  let Q := ∏ d ∈ D, d
  let M (k d : ℕ) := k * (Q / d)
  have hQ : 0 < Q := Finset.prod_pos hpos
  have hfactor (d : ℕ) (hd : d ∈ D) : d * (Q / d) = Q :=
    Nat.mul_div_cancel' (Finset.dvd_prod_of_mem id hd)
  have hscale (k d : ℕ) (hd : d ∈ D) : M k d * d = k * Q := by
    dsimp [M]
    rw [mul_assoc, mul_comm (Q / d) d, hfactor d hd]
  have hseq (q : ℕ) (hq : 0 < q) : Tendsto (fun k : ℕ => k * q) atTop atTop :=
    tendsto_atTop_mono' _ (.of_forall fun k => Nat.le_mul_of_pos_right k hq) tendsto_id
  have hM (d : ℕ) (hd : d ∈ D) : 0 < Q / d := by
    rw [Nat.pos_iff_ne_zero]
    intro he
    have he' := hfactor d hd
    rw [he, mul_zero] at he'
    exact hQ.ne' he'.symm
  unfold Set.HasDensity at hs ht
  have hlim : Tendsto (fun k : ℕ => ∑ d ∈ D, S.partialDensity univ (M k d) / (d : ℝ)) atTop
      (𝓝 (∑ d ∈ D, a / (d : ℝ))) := by
    exact tendsto_finsetSum _ fun d hd => (hs.comp (hseq (Q / d) (hM d hd))).div_const _
  simp only [div_eq_mul_inv, ← Finset.mul_sum] at hlim
  refine le_of_tendsto_of_tendsto hlim (ht.comp (hseq Q hQ)) (.of_forall fun k => ?_)
  let R (d : ℕ) := (Finset.range (M k d)).filter (fun n => n ∈ S)
  let B := (Finset.range (k * Q)).filter (fun n => n ∈ T)
  have hcard : (D.sigma R).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn (fun p : Σ _ : ℕ, ℕ => p.1 * p.2)
    · rintro ⟨d, n⟩ hp
      obtain ⟨hd, hn⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hnM, hnS⟩ := Finset.mem_filter.mp hn
      have hlt := Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hnM) (hpos d hd)
      rw [mul_comm d (M k d), hscale k d hd] at hlt
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hmaps d hd n hnS⟩
    · rintro ⟨d, n⟩ hp ⟨e, m⟩ hq heq
      obtain ⟨hd, hn⟩ := Finset.mem_sigma.mp hp
      obtain ⟨he, hm⟩ := Finset.mem_sigma.mp hq
      have hde := hdisj d hd e he n (Finset.mem_filter.mp hn).2 m (Finset.mem_filter.mp hm).2 heq
      subst e
      have hnm := Nat.eq_of_mul_eq_mul_left (hpos d hd) heq
      change n = m at hnm
      subst m
      rfl
  change (∑ d ∈ D, S.partialDensity univ (M k d) * (d : ℝ)⁻¹) ≤ T.partialDensity univ (k * Q)
  simp only [partialDensity_count]
  have hterm (d : ℕ) (hd : d ∈ D) :
      (R d).card / (M k d : ℝ) * (d : ℝ)⁻¹ = (R d).card / (k * Q : ℕ) := by
    rw [← div_eq_mul_inv, div_div, ← Nat.cast_mul, hscale k d hd]
  change (∑ d ∈ D, (R d).card / (M k d : ℝ) * (d : ℝ)⁻¹) ≤ B.card / (k * Q : ℕ)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum, ← Finset.card_sigma]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

private lemma scaled_tail_family_le_increment {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {h u v : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≤ v) (D : Finset ℕ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hsquarefree : ∀ d ∈ D, ∏ p ∈ d.primeFactors, p = d)
    (hprimes : ∀ d ∈ D, ∀ p ∈ d.primeFactors, h * (p : ℝ) < 1)
    (hband : ∀ d ∈ D, u ≤ ((d.totient : ℝ) / d) * (1 - h) ∧ (d.totient : ℝ) / d < v) :
    (1 - f (1 - h)) * (∑ d ∈ D, (d : ℝ)⁻¹) ≤ f v - f u := by
  classical
  let A (t : ℝ) : Set ℕ := {n | (n.totient : ℝ) < t * n}
  let S := A 1 \ A (1 - h)
  let T := A v \ A u
  have hmono {a b : ℝ} (hab : a ≤ b) : A a ⊆ A b :=
    fun n hn => lt_of_lt_of_le hn (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n))
  have hs : S.HasDensity (1 - f (1 - h)) := by
    have hs' : S.HasDensity (f 1 - f (1 - h)) :=
      density_difference (hmono (by linarith)) (hf _ ⟨by linarith, by linarith⟩)
        (hf 1 ⟨zero_le_one, le_rfl⟩)
    simpa only [density_at_one hf] using hs'
  have ht : T.HasDensity (f v - f u) := density_difference (hmono huv) (hf _ hu) (hf _ hv)
  have hnp (n : ℕ) (hn : n ∈ S) : 0 < n := by
    by_contra! h
    have hn0 : n = 0 := by omega
    subst n
    simpa [A] using hn.1
  have hratio (n : ℕ) (hn : n ∈ S) : 1 - h ≤ (n.totient : ℝ) / n :=
    (le_div_iff₀ (by exact_mod_cast hnp n hn : 0 < (n : ℝ))).mpr (le_of_not_gt hn.2)
  refine density_finset_dilates_le hs ht D hpos ?_ ?_
  · intro d hd n hn
    have hdn : (0 : ℝ) < ((d * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (hpos d hd) (hnp n hn)
    have hub := (phi_ratio_mul_upper (hpos d hd) (hnp n hn)).trans_lt (hband d hd).2
    have hlb : u ≤ ((d*n).totient : ℝ) / (d*n : ℕ) := calc
      _ ≤ ((d.totient : ℝ) / d) * (1 - h) := (hband d hd).1
      _ ≤ ((d.totient : ℝ) / d) * ((n.totient : ℝ) / n) :=
        mul_le_mul_of_nonneg_left (hratio n hn) (by positivity)
      _ = ((d.totient * n.totient : ℕ) : ℝ) / (d*n : ℕ) := by
        rw [Nat.cast_mul, Nat.cast_mul, div_mul_div_comm]
      _ ≤ _ := div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.totient_super_multiplicative d n) hdn.le
    exact ⟨(div_lt_iff₀ hdn).mp hub, fun h => (not_lt_of_ge hlb) ((div_lt_iff₀ hdn).mpr h)⟩
  · intro d hd e he n hn m hm heq
    let P (k : ℕ) := k.primeFactors.filter (fun p : ℕ => h * (p : ℝ) < 1)
    have hdecode (j : ℕ) (hj : j ∈ D) (k : ℕ) (hk : k ∈ S) :
        P (j * k) = j.primeFactors := by
      rw [show P (j * k) = ((j*k).primeFactors.filter (fun p : ℕ => h * (p : ℝ) < 1)) by rfl,
        Nat.primeFactors_mul (hpos j hj).ne' (hnp k hk).ne']
      ext p
      simp only [Finset.mem_filter, Finset.mem_union]
      refine ⟨fun ⟨hp, hph⟩ => hp.elim id (fun hpk => ?_), fun hp => ⟨Or.inl hp, hprimes j hj p hp⟩⟩
      have hpp : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primeFactors.mp hpk).1.pos
      have hph' : h < (p : ℝ)⁻¹ := by
        rw [← one_div]
        exact (lt_div_iff₀ hpp).mpr hph
      have hupper : (k.totient : ℝ) / k ≤ 1 - (p : ℝ)⁻¹ := by
        have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (hnp k hk).ne'
        rw [phi_product, mul_div_cancel_left₀ _ hk']
        simpa using (Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr hpk)
          (fun q _ => one_sub_inv_nonneg q) (fun q _ _ => sub_le_self _ (by positivity)))
      linarith only [hratio k hk, hph', hupper]
    have hsame : d.primeFactors = e.primeFactors := by
      rw [← hdecode d hd n hn, ← hdecode e he m hm, heq]
    rw [← hsquarefree d hd, ← hsquarefree e he, hsame]

private lemma local_pattern_weight_bound {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hd : HasDerivWithinAt f y (Icc 0 1) x) :
    ∃ C > (0 : ℝ), ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ D : Finset ℕ,
      (∀ d ∈ D, 0 < d) →
      (∀ d ∈ D, ∏ p ∈ d.primeFactors, p = d) →
      (∀ d ∈ D, ∀ p ∈ d.primeFactors, h * (p : ℝ) < 1) →
      (∀ d ∈ D, |(d.totient : ℝ) / d - x| ≤ h) →
      (∑ d ∈ D, (d : ℝ)⁻¹) ≤ C * h * (1 + Real.log h⁻¹) := by
  obtain ⟨δ₁, hδ₁, htail⟩ := logarithmic_tail_lower hf
  obtain ⟨δ₂, hδ₂, hlocal⟩ := derivative_band_error hd zero_lt_one
  let δ := min 1 (min δ₁ (min (δ₂ / 2) (min (x / 2) ((1 - x) / 2))))
  have hδ : 0 < δ := lt_min one_pos (lt_min hδ₁
    (lt_min (by positivity) (lt_min (by linarith [hx.1]) (by linarith [hx.2]))))
  let K := Real.exp (-4) / 6
  have hK : 0 < K := by positivity
  let C := (4 * (|y| + 1)) / K
  refine ⟨C, by positivity, δ, hδ, fun h hh hsmall D hpos hsf hprimes hnear => ?_⟩
  have hh1 := hsmall.le.trans (min_le_left _ _)
  have hhδ₁ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhδ₂ : 2 * h < δ₂ := by
    have := hsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hend := hsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let u := x - 2 * h
  let v := x + 2 * h
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    have hleft := hend.trans_le (min_le_left _ _)
    exact ⟨by dsimp [u]; linarith, by dsimp [u]; linarith [hx.2]⟩
  have hv : v ∈ Icc (0 : ℝ) 1 := by
    have hright := hend.trans_le (min_le_right _ _)
    exact ⟨by dsimp [v]; linarith [hx.1], by dsimp [v]; linarith⟩
  have hwidth : v - u = 4 * h := by dsimp [u, v]; ring
  have huv : u ≤ v := by linarith
  have hud : |u - x| = 2 * h := by
    rw [show u - x = -(2 * h) by dsimp [u]; ring, abs_neg, abs_of_pos (by positivity)]
  have hvd : |v - x| = 2 * h := by
    rw [show v - x = 2 * h by dsimp [v]; ring, abs_of_pos (by positivity)]
  have hinc := le_trans (le_abs_self _) (hlocal u hu v hv (hud ▸ hhδ₂) (hvd ▸ hhδ₂))
  rw [hwidth, hud, hvd] at hinc
  have hup : f v - f u ≤ 4 * (|y| + 1) * h := by
    have h := mul_le_mul_of_nonneg_right (le_abs_self y) (by positivity : 0 ≤ 4 * h)
    linarith only [hinc, h]
  have hlow := scaled_tail_family_le_increment hf hh hh1 hu hv huv D hpos hsf hprimes
    (fun d hd => by
      let r := (d.totient : ℝ) / d
      have hr1 : r ≤ 1 := by
        apply (div_le_iff₀ (by exact_mod_cast hpos d hd : 0 < (d : ℝ))).mpr
        simpa using (show (d.totient : ℝ) ≤ d by exact_mod_cast Nat.totient_le d)
      have hr : -h ≤ r - x ∧ r - x ≤ h := abs_le.mp (hnear d hd)
      have hrh := mul_le_mul_of_nonneg_right hr1 hh.le
      exact ⟨by dsimp [u]; nlinarith only [hr.1, hrh], by dsimp [v]; linarith only [hr.2, hh]⟩)
  have hsum : 0 ≤ ∑ d ∈ D, (d : ℝ)⁻¹ := Finset.sum_nonneg fun d _ => by positivity
  have hlo := (mul_le_mul_of_nonneg_right (htail h hh hh1 hhδ₁) hsum).trans (hlow.trans hup)
  have hden : 0 < 1 + Real.log h⁻¹ := by
    have hi : 1 ≤ h⁻¹ := by simpa using inv_anti₀ hh hh1
    linarith [Real.log_nonneg hi]
  change K / (1 + Real.log h⁻¹) * (∑ d ∈ D, (d : ℝ)⁻¹) ≤ _ at hlo
  rw [div_mul_eq_mul_div] at hlo
  have hcross := (div_le_iff₀ hden).mp hlo
  apply le_of_mul_le_mul_left ?_ hK
  calc
    _ ≤ _ := hcross
    _ = _ := by dsimp only [C]; field_simp


-- Order structure of the distribution function.

private lemma density_nonneg {A : Set ℕ} {a : ℝ} (ha : A.HasDensity a) : 0 ≤ a := by
  classical
  unfold Set.HasDensity at ha
  refine ge_of_tendsto' ha fun N => ?_
  rw [partialDensity_count]
  positivity

private lemma density_le_one {A : Set ℕ} {a : ℝ} (ha : A.HasDensity a) : a ≤ 1 := by
  classical
  unfold Set.HasDensity at ha
  refine le_of_tendsto' ha fun N => ?_
  rw [partialDensity_count]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · rw [div_le_one (by exact_mod_cast hN)]
    have hcard := Finset.card_filter_le (Finset.range N) (fun n => n ∈ A)
    rw [Finset.card_range] at hcard
    exact_mod_cast hcard

private lemma distribution_mono {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≤ v) :
    f u ≤ f v := by
  have hsub : {n : ℕ | (n.totient : ℝ) < u * n} ⊆ {n : ℕ | (n.totient : ℝ) < v * n} := by
    intro n hn
    have hn' : (n.totient : ℝ) < u * n := hn
    exact show (n.totient : ℝ) < v * n from
      lt_of_lt_of_le hn' (mul_le_mul_of_nonneg_right huv (Nat.cast_nonneg n))
  have h := density_nonneg (density_difference hsub (hf u hu) (hf v hv))
  linarith

private lemma distribution_bounds {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : 0 ≤ f u ∧ f u ≤ 1 :=
  ⟨density_nonneg (hf u hu), density_le_one (hf u hu)⟩


-- Barrier at the interior point 1/4: it is not a totient ratio and every ratio stays at
-- distance at least 1/(4d), so the single-ratio obstruction holds there with no hypothesis.

private lemma four_totient_ne (d : ℕ) (hd : 0 < d) : 4 * d.totient ≠ d := by
  intro h
  have hphi : 0 < d.totient := Nat.totient_pos.mpr hd
  have key := Nat.totient_mul_prod_primeFactors d
  have h4 : ∏ p ∈ d.primeFactors, p = 4 * ∏ p ∈ d.primeFactors, (p - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hphi
    calc d.totient * ∏ p ∈ d.primeFactors, p
        = d * ∏ p ∈ d.primeFactors, (p - 1) := key
      _ = (4 * d.totient) * ∏ p ∈ d.primeFactors, (p - 1) := by rw [h]
      _ = d.totient * (4 * ∏ p ∈ d.primeFactors, (p - 1)) := by ring
  have h2dvd : 2 ∣ ∏ p ∈ d.primeFactors, p := by
    rw [h4]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨p, hp, h2p⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp h2dvd
  have hp2 : 2 = p :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_of_mem_primeFactors hp)).mp h2p
  subst hp2
  have herase := Finset.mul_prod_erase d.primeFactors (fun p => p) hp
  have hrest : ∏ p ∈ d.primeFactors.erase 2, p = 2 * ∏ p ∈ d.primeFactors, (p - 1) := by
    have h5 : 2 * ∏ p ∈ d.primeFactors.erase 2, p =
        2 * (2 * ∏ p ∈ d.primeFactors, (p - 1)) := by
      rw [herase, h4]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h5
  have h2dvd' : 2 ∣ ∏ p ∈ d.primeFactors.erase 2, p := by
    rw [hrest]
    exact Dvd.intro _ rfl
  obtain ⟨q, hq, h2q⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp h2dvd'
  obtain ⟨hq2, hqmem⟩ := Finset.mem_erase.mp hq
  exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two
    (Nat.prime_of_mem_primeFactors hqmem)).mp h2q).symm

private lemma quarter_not_ratio {d : ℕ} (hd : 0 < d) : (d.totient : ℝ) / d ≠ 1 / 4 := by
  intro h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_eq_div_iff hd'.ne' (by norm_num)] at h
  apply four_totient_ne d hd
  have hcast : ((4 * d.totient : ℕ) : ℝ) = (d : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hcast

private lemma quarter_gap {d : ℕ} (hd : 0 < d) :
    1 / (4 * (d : ℝ)) ≤ |(d.totient : ℝ) / d - 1 / 4| := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hne := four_totient_ne d hd
  have hint : (1 : ℤ) ≤ |4 * (d.totient : ℤ) - d| := by
    apply Int.one_le_abs
    intro h0
    apply hne
    have h1 : 4 * (d.totient : ℤ) = d := by linarith
    exact_mod_cast h1
  have hreal : (1 : ℝ) ≤ |4 * (d.totient : ℝ) - d| := by
    have h1 := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at h1
    exact h1
  have heq : (d.totient : ℝ) / d - 1 / 4 = (4 * (d.totient : ℝ) - d) / (4 * d) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * d)]
  exact div_le_div_of_nonneg_right hreal (by positivity)

private lemma quarter_separation_automatic :
    ∀ B > (0 : ℝ), ∃ δ > 0, ∀ d : ℕ, 0 < d →
      let a := |(d.totient : ℝ) / d - 1 / 4|
      0 < a → a < δ → B ≤ (d : ℝ) * a * (1 + Real.log a⁻¹) := by
  intro B hB
  refine ⟨Real.exp (-(4 * B)), Real.exp_pos _, ?_⟩
  intro d hd a ha haδ
  have hgap : 1 / (4 * (d : ℝ)) ≤ a := quarter_gap hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hda : 1 / 4 ≤ (d : ℝ) * a := by
    have h1 := mul_le_mul_of_nonneg_left hgap hd'.le
    have h2 : (d : ℝ) * (1 / (4 * (d : ℝ))) = 1 / 4 := by field_simp
    linarith
  have hlog : 4 * B < Real.log a⁻¹ := by
    rw [Real.log_inv]
    have h1 := Real.log_lt_log ha haδ
    rw [Real.log_exp] at h1
    linarith
  have hprod : (1 / 4 : ℝ) * (1 + 4 * B) ≤ (d : ℝ) * a * (1 + Real.log a⁻¹) :=
    mul_le_mul hda (by linarith) (by linarith) (mul_nonneg hd'.le ha.le)
  linarith


-- The same barrier at every rational point that is not a totient ratio: the gap to a ratio
-- of denominator d is at least 1/(b d), so the logarithmic separation is automatic.

private lemma rational_separation_automatic {a b : ℕ} (hb : 0 < b)
    (hne : ∀ d : ℕ, 0 < d → (d.totient : ℝ) / d ≠ (a : ℝ) / b) :
    ∀ B > (0 : ℝ), ∃ δ > 0, ∀ d : ℕ, 0 < d →
      let g := |(d.totient : ℝ) / d - (a : ℝ) / b|
      0 < g → g < δ → B ≤ (d : ℝ) * g * (1 + Real.log g⁻¹) := by
  intro B hB
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  refine ⟨Real.exp (-(b * B)), Real.exp_pos _, ?_⟩
  intro d hd g hg hgδ
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hint : (1 : ℤ) ≤ |(b : ℤ) * (d.totient : ℤ) - a * d| := by
    apply Int.one_le_abs
    intro h0
    apply hne d hd
    have h1 : (b : ℝ) * (d.totient : ℝ) - a * d = 0 := by exact_mod_cast h0
    rw [div_eq_div_iff hd'.ne' hb'.ne']
    linarith
  have hreal : (1 : ℝ) ≤ |(b : ℝ) * (d.totient : ℝ) - a * d| := by
    have h1 := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at h1
    exact h1
  have heq : (d.totient : ℝ) / d - (a : ℝ) / b =
      ((b : ℝ) * (d.totient : ℝ) - a * d) / (b * d) := by
    field_simp
  have hgap : 1 / ((b : ℝ) * d) ≤ g := by
    change 1 / ((b : ℝ) * d) ≤ |(d.totient : ℝ) / d - (a : ℝ) / b|
    rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < b * d)]
    exact div_le_div_of_nonneg_right hreal (by positivity)
  have hda : 1 / (b : ℝ) ≤ (d : ℝ) * g := by
    have h1 := mul_le_mul_of_nonneg_left hgap hd'.le
    have h2 : (d : ℝ) * (1 / ((b : ℝ) * d)) = 1 / b := by field_simp
    linarith
  have hlog : (b : ℝ) * B < Real.log g⁻¹ := by
    rw [Real.log_inv]
    have h1 := Real.log_lt_log hg hgδ
    rw [Real.log_exp] at h1
    linarith
  have hprod : (1 / (b : ℝ)) * (1 + b * B) ≤ (d : ℝ) * g * (1 + Real.log g⁻¹) :=
    mul_le_mul hda (by linarith) (by positivity) (mul_nonneg hd'.le hg.le)
  have h3 : (1 / (b : ℝ)) * (1 + b * B) = 1 / b + B := by field_simp
  have h4 : (0 : ℝ) < 1 / b := by positivity
  linarith

end Erdos50Proof

theorem OMA.solution : type_of% @Erdos50.erdos_50 := by
  intro f hf
  rintro ⟨x, hx, y, hy, hd⟩
  by_cases hx0 : x = 0
  · subst x
    exact (not_lt_of_ge (Erdos50Proof.derivative_at_zero_nonpos hf hd)) hy
  · by_cases hx1 : x = 1
    · subst x
      exact Erdos50Proof.no_derivative_at_one hf hd
    · have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),
        lt_of_le_of_ne hx.2 hx1⟩
      by_cases hratio : ∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d
      · obtain ⟨d, hdpos, hxeq⟩ := hratio
        exact Erdos50Proof.no_derivative_at_finite_ratio hf hdpos hxeq hxI.2 hd
      · have hsep := Erdos50Proof.logarithmic_ratio_divergence hf hxI.2 hd
        have hpatterns := Erdos50Proof.local_pattern_weight_bound hf hxI hd
        sorry

