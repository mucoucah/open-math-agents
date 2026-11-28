import FormalConjectures.ErdosProblems.«5»

/-!
Partial formalization of Pintz's theorem (Erdős Problem 5): there exists c > 0
such that [0, c] is contained in the limit point set of normalized prime gaps.

Everything except the single finite-scale analytic core `maynard_tao_in_ap`
(Maynard-Tao sieve plus Erdős-Rankin covering in an arithmetic progression) is
completely proved and typechecked without sorry.
-/

-- Problem: Erdős Problem 5 — pintz
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/5.lean:141 (declaration Erdos5.erdos_5.variants.pintz)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Erdos5 Filter Set
open scoped Topology

namespace OMA.PintzPartial

/-- Remaining analytic core (Maynard-Tao sieve plus Erdos-Rankin covering):
there is a fixed m such that for any lacunary shifts beta in (0, 1), any epsilon > 0,
and any threshold X, there exist a modulus W >= 1, a residue b, an integer n >= max X (W + 1)
with n === b [MOD W], and strictly increasing shifts h_r approximating beta_r * log n within
epsilon * log n such that every intermediate integer b + t (t not in range h) shares a
nontrivial factor with W while at least two of n + h_r are prime. -/
theorem maynard_tao_in_ap :
    ∃ m : ℕ, ∀ β : Fin m → ℝ, (∀ r, 0 < β r ∧ β r < 1) →
      (∀ i j, i < j → 2 * β i < β j) →
      ∀ ε > (0 : ℝ), ∀ X : ℕ, ∃ (W b n : ℕ) (h : Fin m → ℕ),
        1 ≤ W ∧ W < n ∧ X ≤ n ∧ n ≡ b [MOD W] ∧ StrictMono h ∧
        (∀ r, |(h r : ℝ) / Real.log n - β r| < ε) ∧
        (∀ i j, i < j → ∀ t, h i < t → t < h j → (∀ r, t ≠ h r) → 1 < Nat.gcd (b + t) W) ∧
        (∃ i j, i < j ∧ (n + h i).Prime ∧ (n + h j).Prime) := by
  sorry

/-- If n === b [MOD W] with 1 <= W < n and 1 < gcd (b + t) W, then n + t is composite. -/
lemma not_prime_of_modEq_of_gcd_gt_one {W b n t : ℕ} (hW1 : 1 ≤ W) (hWn : W < n)
    (hmod : n ≡ b [MOD W]) (hgcd : 1 < Nat.gcd (b + t) W) : ¬ (n + t).Prime := by
  intro hp
  set d := Nat.gcd (b + t) W
  have hdW : d ∣ W := Nat.gcd_dvd_right (b + t) W
  have hdb : d ∣ b + t := Nat.gcd_dvd_left (b + t) W
  have hmod_t : n + t ≡ b + t [MOD d] := (hmod.of_dvd hdW).add_right t
  have hdnt : d ∣ n + t := Nat.dvd_iff_mod_eq_zero.mpr (by
    rw [hmod_t, ← Nat.dvd_iff_mod_eq_zero]
    exact hdb)
  have hd_le_W : d ≤ W := Nat.le_of_dvd (by omega) hdW
  rcases hp.eq_one_or_self_of_dvd d hdnt with h1 | h2 <;> omega

/-- Clearing intermediate integers via a covering modulus W reduces to `maynard_tao_in_ap`. -/
theorem maynard_tao_cleared_shifts :
    ∃ m : ℕ, ∀ β : Fin m → ℝ, (∀ r, 0 < β r ∧ β r < 1) →
      (∀ i j, i < j → 2 * β i < β j) →
      ∀ ε > (0 : ℝ), ∀ X : ℕ, ∃ n ≥ X, ∃ h : Fin m → ℕ, StrictMono h ∧
        (∀ r, |(h r : ℝ) / Real.log n - β r| < ε) ∧
        (∀ i j, i < j → ∀ t, h i < t → t < h j → (∀ r, t ≠ h r) → ¬ (n + t).Prime) ∧
        (∃ i j, i < j ∧ (n + h i).Prime ∧ (n + h j).Prime) := by
  obtain ⟨m, hmap⟩ := maynard_tao_in_ap
  refine ⟨m, fun β hβ hβlac ε hε X => ?_⟩
  obtain ⟨W, b, n, h, hW1, hWn, hnX, hmod, hh, happrox, hgcd, h2⟩ := hmap β hβ hβlac ε hε X
  refine ⟨n, hnX, h, hh, happrox, ?_, h2⟩
  intro i j hij t hti htj hne
  exact not_prime_of_modEq_of_gcd_gt_one hW1 hWn hmod (hgcd i j hij t hti htj hne)

lemma log_le_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ Real.sqrt x := by
  have h : 0 < Real.sqrt x / 2 := by positivity
  have heq : Real.log (Real.sqrt x / 2) = Real.log x / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx.le]
  linarith only [Real.log_le_sub_one_of_pos h, heq, Real.log_two_lt_d9]

lemma primeCounting_lower {x : ℝ} (hx : 256 ≤ x) :
    x / (4 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx1 : 1 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hlogx : Real.log (x + 2) ≤ x / 8 := by
    apply (log_le_sqrt (by linarith : 0 < x + 2)).trans
    apply Real.sqrt_le_iff.2
    refine ⟨by linarith, ?_⟩
    nlinarith only [hx, mul_nonneg (show 0 ≤ x - 256 by linarith) (show 0 ≤ x by linarith)]
  have hmul := mul_le_mul_of_nonneg_left
    (show (1 : ℝ) / 2 ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    (show 0 ≤ x - 1 by linarith)
  have hnum : x / 4 ≤ (x - 1) * Real.log 2 - Real.log (x + 2) := by
    linarith only [hmul, hlogx, hx]
  calc
    x / (4 * Real.log x) = (x / 4) / Real.log x := by ring
    _ ≤ ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x :=
      div_le_div_of_nonneg_right hnum hL.le
    _ ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := Chebyshev.pi_ge' hx1

lemma nth_prime_le_mul_log {n : ℕ} (hn : 256 ≤ n) :
    (Nat.nth Nat.Prime n : ℝ) ≤ 16 * (n : ℝ) * Real.log n := by
  have hnR : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    linarith [Real.exp_one_lt_d9]
  set x : ℝ := 16 * (n : ℝ) * Real.log n with hxdef
  have hx256 : 256 ≤ x := by rw [hxdef]; nlinarith
  have hx0 : 0 < x := by linarith
  have h16log : 16 * Real.log n ≤ (n : ℝ) := by
    have hs : Real.log n ≤ Real.sqrt n := log_le_sqrt hn0
    have hsq : 16 * Real.sqrt n ≤ n := by
      have : (16 : ℝ) ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by norm_num) hn0.le]; norm_num; linarith
      nlinarith [Real.mul_self_sqrt hn0.le]
    linarith
  have hxsq : x ≤ (n : ℝ) ^ 2 := by rw [hxdef, sq]; nlinarith
  have hlogx : Real.log x ≤ 2 * Real.log n := by
    have h := Real.log_le_log hx0 hxsq
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hlogx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hcnt : (n : ℝ) + 1 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    refine le_trans ?_ (primeCounting_lower hx256)
    rw [le_div_iff₀ (by positivity)]
    have : ((n : ℝ) + 1) * (4 * Real.log x) ≤ ((n : ℝ) + 1) * (8 * Real.log n) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hxdef]
    nlinarith
  have hcntN : n + 1 ≤ Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hcnt
  have hlt : n < Nat.count Nat.Prime (⌊x⌋₊ + 1) := by
    rw [Nat.primeCounting, Nat.primeCounting'] at hcntN
    omega
  have hnth : Nat.nth Nat.Prime n < ⌊x⌋₊ + 1 := Nat.nth_lt_of_lt_count hlt
  have hle : Nat.nth Nat.Prime n ≤ ⌊x⌋₊ := by omega
  calc
    (Nat.nth Nat.Prime n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hle
    _ ≤ x := Nat.floor_le hx0.le

/-- Prime and index logarithms are asymptotically equivalent: log p_n / log n -> 1. -/
lemma log_nth_prime_div_log_tendsto_one :
    Tendsto (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun y : ℝ => (Real.log 16 + Real.log y) / y) atTop (𝓝 0) := by
    have a := (tendsto_const_nhds (x := Real.log 16)).div_atTop tendsto_id
    have b := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have ab := a.add b
    simp only [add_zero] at ab
    refine ab.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    simp [add_div]
  have hup : Tendsto (fun n : ℕ => 1 + (Real.log 16 + Real.log (Real.log n)) / Real.log n)
      atTop (𝓝 1) := by
    simpa using (hsmall.comp hL).const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    rw [le_div_iff₀ hlog, one_mul]
    apply Real.log_le_log (by linarith)
    have := Nat.add_two_le_nth_prime n
    exact_mod_cast (by omega : n ≤ Nat.nth Nat.Prime n)
  · filter_upwards [eventually_ge_atTop 256] with n hn
    have hnR : (256 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : 1 < Real.log n := by
      rw [Real.lt_log_iff_exp_lt hn0]
      linarith [Real.exp_one_lt_d9]
    have hppos : (0 : ℝ) < Nat.nth Nat.Prime n := by
      have := Nat.add_two_le_nth_prime n
      exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime n)
    have h1 : Real.log (Nat.nth Nat.Prime n : ℝ) ≤ Real.log (16 * (n : ℝ) * Real.log n) :=
      Real.log_le_log hppos (nth_prime_le_mul_log hn)
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)] at h1
    rw [div_le_iff₀ (by linarith), add_mul, one_mul, div_mul_cancel₀ _ (by linarith)]
    linarith

/-- From a strictly increasing shift tuple whose intermediate integers n + t are composite
and containing at least two primes, extract consecutive primes p_k = n + h i and p_{k+1} = n + h j. -/
lemma exists_consecutive_primes_in_shifts {m : ℕ} {h : Fin m → ℕ} (hh : StrictMono h)
    {n : ℕ}
    (hclear : ∀ i j, i < j → ∀ t, h i < t → t < h j → (∀ r, t ≠ h r) → ¬ (n + t).Prime)
    (h2 : ∃ i₁ j₁ : Fin m, i₁ < j₁ ∧ (n + h i₁).Prime ∧ (n + h j₁).Prime) :
    ∃ i j : Fin m, i < j ∧ ∃ k : ℕ, Nat.nth Nat.Prime k = n + h i ∧ primeGap k = h j - h i := by
  classical
  obtain ⟨i₁, j₁, hij₁, hp₁, hq₁⟩ := h2
  let S : Finset (Fin m) := Finset.univ.filter (fun r => i₁ < r ∧ (n + h r).Prime)
  have hS : S.Nonempty := ⟨j₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij₁, hq₁⟩⟩
  let j : Fin m := S.min' hS
  have hjmem : j ∈ S := Finset.min'_mem S hS
  have hij : i₁ < j := (Finset.mem_filter.mp hjmem).2.1
  have hpj : (n + h j).Prime := (Finset.mem_filter.mp hjmem).2.2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.nth Nat.Prime k = n + h i₁ := Nat.subset_range_nth hp₁
  obtain ⟨l, hl⟩ : ∃ l : ℕ, Nat.nth Nat.Prime l = n + h j := Nat.subset_range_nth hpj
  have hnth := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hkl : k < l := hnth.lt_iff_lt.mp (by rw [hk, hl]; have := hh hij; omega)
  have hnext_gt : n + h i₁ < Nat.nth Nat.Prime (k + 1) := by
    rw [← hk]; exact hnth (Nat.lt_succ_self k)
  have hnext_le : Nat.nth Nat.Prime (k + 1) ≤ n + h j := by
    rw [← hl]; exact hnth.monotone (by omega)
  have hnext_eq : Nat.nth Nat.Prime (k + 1) = n + h j := by
    by_contra hne
    have hlt : Nat.nth Nat.Prime (k + 1) < n + h j := lt_of_le_of_ne hnext_le hne
    set t : ℕ := Nat.nth Nat.Prime (k + 1) - n with htdef
    have hnt : n + t = Nat.nth Nat.Prime (k + 1) := by omega
    have htp : (n + t).Prime := hnt ▸ Nat.prime_nth_prime (k + 1)
    have hti : h i₁ < t := by omega
    have htj : t < h j := by omega
    by_cases hmem : ∃ r : Fin m, t = h r
    · obtain ⟨r, hr⟩ := hmem
      have hir : i₁ < r := hh.lt_iff_lt.mp (hr ▸ hti)
      have hrj : r < j := hh.lt_iff_lt.mp (hr ▸ htj)
      have hrS : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hir, hr ▸ htp⟩
      exact not_lt_of_ge (Finset.min'_le S r hrS) hrj
    · push Not at hmem
      exact hclear i₁ j hij t hti htj hmem htp
  refine ⟨i₁, j, hij, k, hk, ?_⟩
  unfold primeGap
  rw [hnext_eq, hk]
  omega

/-- Convert shift approximation relative to log n into prime-gap approximation relative to
log (n + h i). -/
lemma approx_gap_of_shifts {m : ℕ} {β : Fin m → ℝ} (hβ : ∀ r, 0 < β r ∧ β r < 1)
    {h : Fin m → ℕ} (hh : StrictMono h) {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn16 : 16 ≤ n) (hnlog : 4 / ε < Real.log n)
    (happrox : ∀ r, |(h r : ℝ) / Real.log n - β r| < ε / 4)
    {i j : Fin m} (hij : i < j) :
    |((h j - h i : ℕ) : ℝ) / Real.log ((n + h i : ℕ) : ℝ) - (β j - β i)| < ε := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hbound (r : Fin m) : (h r : ℝ) / Real.log n < 2 := by
    have := (abs_lt.mp (happrox r)).2
    linarith [(hβ r).2]
  have hhi_le : (h i : ℝ) ≤ 2 * Real.log n := by
    have := (div_lt_iff₀ hlogn).mp (hbound i)
    linarith
  have h2log_le_n : 2 * Real.log n ≤ (n : ℝ) := by
    have hs := log_le_sqrt hn0
    have hsq : 2 * Real.sqrt n ≤ n := by
      have : (2 : ℝ) ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by norm_num) hn0.le]; norm_num; linarith
      nlinarith [Real.mul_self_sqrt hn0.le]
    linarith
  have hnhi_ge : (n : ℝ) ≤ ((n + h i : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n (h i)
  have hnhi_le : ((n + h i : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    linarith
  have hlog_ge : Real.log n ≤ Real.log ((n + h i : ℕ) : ℝ) := Real.log_le_log hn0 hnhi_ge
  have hlog_le : Real.log ((n + h i : ℕ) : ℝ) ≤ Real.log n + Real.log 2 := by
    have h := Real.log_le_log (by linarith) hnhi_le
    rw [Real.log_mul (by norm_num) hn0.ne'] at h
    linarith
  have hlogp0 : 0 < Real.log ((n + h i : ℕ) : ℝ) := lt_of_lt_of_le hlogn hlog_ge
  set A : ℝ := ((h j - h i : ℕ) : ℝ)
  have hcast : A = (h j : ℝ) - (h i : ℝ) := Nat.cast_sub (hh.monotone hij.le)
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hAdiv : A / Real.log n ≤ 2 := by
    rw [hcast, sub_div]
    have h1 := hbound j
    have h2 : 0 ≤ (h i : ℝ) / Real.log n := by positivity
    linarith
  have hdiff1 : |A / Real.log n - (β j - β i)| < ε / 2 := by
    have heq : A / Real.log n - (β j - β i) =
        ((h j : ℝ) / Real.log n - β j) - ((h i : ℝ) / Real.log n - β i) := by
      rw [hcast, sub_div]; ring
    rw [heq]
    calc
      |((h j : ℝ) / Real.log n - β j) - ((h i : ℝ) / Real.log n - β i)|
          ≤ |(h j : ℝ) / Real.log n - β j| + |(h i : ℝ) / Real.log n - β i| := abs_sub _ _
      _ < ε / 4 + ε / 4 := add_lt_add (happrox j) (happrox i)
      _ = ε / 2 := by ring
  have hdiff2 : |A / Real.log ((n + h i : ℕ) : ℝ) - A / Real.log n| < ε / 2 := by
    have hnonpos : A / Real.log ((n + h i : ℕ) : ℝ) ≤ A / Real.log n :=
      div_le_div_of_nonneg_left hA0 hlogn hlog_ge
    rw [abs_of_nonpos (sub_nonpos.mpr hnonpos), neg_sub]
    have heq : A / Real.log n - A / Real.log ((n + h i : ℕ) : ℝ) =
        (A / Real.log n) * ((Real.log ((n + h i : ℕ) : ℝ) - Real.log n) /
          Real.log ((n + h i : ℕ) : ℝ)) := by
      field_simp
    rw [heq]
    have hnum : Real.log ((n + h i : ℕ) : ℝ) - Real.log n ≤ 1 := by
      linarith [Real.log_two_lt_d9]
    have hfrac : (Real.log ((n + h i : ℕ) : ℝ) - Real.log n) /
        Real.log ((n + h i : ℕ) : ℝ) ≤ 1 / Real.log n := by
      calc
        (Real.log ((n + h i : ℕ) : ℝ) - Real.log n) / Real.log ((n + h i : ℕ) : ℝ)
            ≤ 1 / Real.log ((n + h i : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hnum hlogp0.le
        _ ≤ 1 / Real.log n := one_div_le_one_div_of_le hlogn hlog_ge
    have hprod : (A / Real.log n) * ((Real.log ((n + h i : ℕ) : ℝ) - Real.log n) /
        Real.log ((n + h i : ℕ) : ℝ)) ≤ 2 / Real.log n := by
      calc
        (A / Real.log n) * ((Real.log ((n + h i : ℕ) : ℝ) - Real.log n) /
            Real.log ((n + h i : ℕ) : ℝ))
            ≤ 2 * (1 / Real.log n) :=
          mul_le_mul hAdiv hfrac (by positivity) (by norm_num)
        _ = 2 / Real.log n := by ring
    have hlt : 2 / Real.log n < ε / 2 := by
      rw [div_lt_iff₀ hlogn]
      have h4 := (div_lt_iff₀ hε0).mp hnlog
      linarith
    linarith
  calc
    |A / Real.log ((n + h i : ℕ) : ℝ) - (β j - β i)|
        = |(A / Real.log ((n + h i : ℕ) : ℝ) - A / Real.log n) +
            (A / Real.log n - (β j - β i))| := by ring_nf
    _ ≤ |A / Real.log ((n + h i : ℕ) : ℝ) - A / Real.log n| +
          |A / Real.log n - (β j - β i)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hdiff2 hdiff1
    _ = ε := by ring

/-- Remaining analytic core (a weak finite-pattern theorem in the style of
Banks, Freiberg and Maynard, only for lacunary shifts in the unit interval). -/
theorem core : ∃ m : ℕ, ∀ β : Fin m → ℝ, (∀ i, 0 < β i ∧ β i < 1) →
    (∀ i j, i < j → 2 * β i < β j) → ∃ i j, i < j ∧ β j - β i ∈ limitPointSet := by
  obtain ⟨m, hms⟩ := maynard_tao_cleared_shifts
  refine ⟨m, fun β hβ hβlac => ?_⟩
  have hex : ∀ s : ℕ, ∃ p : Fin m × Fin m, p.1 < p.2 ∧ ∃ k : ℕ, s ≤ k ∧
      |(primeGap k : ℝ) / Real.log (Nat.nth Nat.Prime k : ℝ) - (β p.2 - β p.1)| <
        1 / ((s : ℝ) + 1) := by
    intro s
    set ε : ℝ := 1 / ((s : ℝ) + 1) with hεdef
    have hε0 : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by
      rw [hεdef, div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) s]
    set X : ℕ := max 16 (max (⌈Real.exp (4 / ε)⌉₊ + 1) (Nat.nth Nat.Prime s + 1)) with hXdef
    obtain ⟨n, hnX, h, hh, happrox, hclear, h2⟩ := hms β hβ hβlac (ε / 4) (by positivity) X
    have hn16 : 16 ≤ n := le_trans (le_max_left _ _) hnX
    have hnexp : Real.exp (4 / ε) < (n : ℝ) := by
      have h1 : ⌈Real.exp (4 / ε)⌉₊ + 1 ≤ n :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnX
      have h2 : Real.exp (4 / ε) ≤ (⌈Real.exp (4 / ε)⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : (⌈Real.exp (4 / ε)⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast h1
      linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnlog : 4 / ε < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hnexp
    obtain ⟨i, j, hij, k, hk, hgap⟩ := exists_consecutive_primes_in_shifts hh hclear h2
    have hsk : s ≤ k := by
      have h1 : Nat.nth Nat.Prime s + 1 ≤ n :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnX
      have hlt : Nat.nth Nat.Prime s < Nat.nth Nat.Prime k := by rw [hk]; omega
      exact ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).lt_iff_lt.mp hlt).le
    refine ⟨(i, j), hij, k, hsk, ?_⟩
    rw [hgap, hk]
    exact approx_gap_of_shifts hβ hh hε0 hε1 hn16 hnlog happrox hij
  choose p hp_lt k hsk hdist using hex
  obtain ⟨⟨i, j⟩, hinf0⟩ := Finite.exists_infinite_fiber p
  have hinf : (p ⁻¹' {(i, j)}).Infinite := Set.infinite_coe_iff.mp hinf0
  obtain ⟨s₀, hs₀⟩ := hinf.nonempty
  have hij : i < j := by
    have h := hp_lt s₀
    have heq : p s₀ = (i, j) := hs₀
    simpa [heq] using h
  have hcl : MapClusterPt (β j - β i) atTop
      (fun r : ℕ => (primeGap r : ℝ) / Real.log (Nat.nth Nat.Prime r : ℝ)) := by
    rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
    intro δ hδ
    rw [frequently_atTop]
    intro K
    obtain ⟨s, hs_mem, hs_gt⟩ := hinf.exists_gt (max K ⌈1 / δ⌉₊)
    have hps : p s = (i, j) := hs_mem
    have hks : K ≤ k s := le_trans (le_trans (le_max_left _ _) hs_gt.le) (hsk s)
    refine ⟨k s, hks, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 := hdist s
    rw [hps] at h1
    have h2 : 1 / ((s : ℝ) + 1) ≤ δ := by
      have hceil : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
      have hgt : (⌈1 / δ⌉₊ : ℝ) < (s : ℝ) := by
        exact_mod_cast lt_of_le_of_lt (le_max_right _ _) hs_gt
      rw [div_le_iff₀ (by positivity)]
      have h3 := (div_le_iff₀ hδ).mp hceil
      nlinarith
    linarith
  obtain ⟨u, hu_mono, hu_lim⟩ := hcl.tendsto_subseq
  refine ⟨i, j, hij, (mem_limitPointSet_iff _).mpr ⟨u, hu_mono, ?_⟩⟩
  have hprod := hu_lim.mul (log_nth_prime_div_log_tendsto_one.comp hu_mono.tendsto_atTop)
  rw [mul_one] at hprod
  refine hprod.congr fun t => ?_
  have hp : 0 < Real.log (Nat.nth Nat.Prime (u t) : ℝ) :=
    Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime (u t)).one_lt)
  simp only [Function.comp_apply, normalizedGap]
  rw [div_mul_div_cancel₀ hp.ne']

/-- If no interval [0,c] lies in the closed set S, then S misses points
arbitrarily close to zero from the right. -/
lemma miss_near_zero {S : Set ℝ} (hS : IsClosed S) (h : ¬ ∃ c > (0 : ℝ), Icc 0 c ⊆ S)
    {ε : ℝ} (hε : 0 < ε) : ∃ x, 0 < x ∧ x < ε ∧ x ∉ S := by
  by_contra hne
  push Not at hne
  apply h
  refine ⟨ε, hε, ?_⟩
  have hsub : Ioo 0 ε ⊆ S := fun x hx => hne x hx.1 hx.2
  rw [← closure_Ioo hε.ne]
  exact hS.closure_subset_iff.mpr hsub

/-- Build a lacunary configuration whose points and differences all avoid S. -/
lemma build {S : Set ℝ} (hS : IsClosed S) (h : ¬ ∃ c > (0 : ℝ), Icc 0 c ⊆ S) :
    ∀ m : ℕ, ∃ β : Fin m → ℝ, (∀ i, 0 < β i ∧ β i < 1 ∧ β i ∉ S) ∧
      ∀ i j, i < j → 2 * β i < β j ∧ β j - β i ∉ S := by
  intro m
  induction m with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨β, hpos, hdiff⟩ := ih
    set U : Set ℝ := Iio 1 ∩ ⋂ i : Fin m, ({y | 2 * y < β i} ∩ {y | β i - y ∈ Sᶜ}) with hU
    have hUo : IsOpen U := by
      refine IsOpen.inter isOpen_Iio (isOpen_iInter_of_finite fun i => ?_)
      refine IsOpen.inter ?_ ?_
      · exact isOpen_lt (continuous_const.mul continuous_id) continuous_const
      · exact hS.isOpen_compl.preimage (continuous_const.sub continuous_id)
    have h0 : (0 : ℝ) ∈ U := by
      refine ⟨by norm_num, mem_iInter.mpr fun i => ⟨?_, ?_⟩⟩
      · show 2 * (0:ℝ) < β i
        linarith [(hpos i).1]
      · show β i - 0 ∈ Sᶜ
        simpa using (hpos i).2.2
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo 0 h0
    obtain ⟨y, hy0, hyε, hyS⟩ := miss_near_zero hS h hε
    have hyU : y ∈ U := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hy0]; exact hyε)
    obtain ⟨hy1, hyI⟩ := hyU
    have hyi : ∀ i, 2 * y < β i ∧ β i - y ∉ S := fun i => by
      have := mem_iInter.mp hyI i
      exact ⟨this.1, this.2⟩
    refine ⟨Fin.cons y β, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · exact ⟨hy0, hy1, hyS⟩
      · simpa using hpos k
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl _)
        | succ b => simpa using hyi b
      | succ a =>
        induction j using Fin.cases with
        | zero => exact absurd hij (Fin.not_lt_zero _)
        | succ b => simpa using hdiff a b (Fin.succ_lt_succ_iff.mp hij)

end OMA.PintzPartial

theorem OMA.solution : type_of% @Erdos5.erdos_5.variants.pintz := by
  by_contra h
  obtain ⟨m, hcore⟩ := OMA.PintzPartial.core
  obtain ⟨β, hpos, hdiff⟩ := OMA.PintzPartial.build isClosed_limitPointSet h m
  obtain ⟨i, j, hij, hmem⟩ := hcore β (fun i => ⟨(hpos i).1, (hpos i).2.1⟩)
    (fun i j hij => (hdiff i j hij).1)
  exact (hdiff i j hij).2 hmem
