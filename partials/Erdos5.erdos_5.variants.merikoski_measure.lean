import FormalConjectures.ErdosProblems.«5»

-- Problem: Erdős Problem 5 — merikoski measure
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/5.lean:187 (declaration Erdos5.erdos_5.variants.merikoski_measure)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Strategy: Merikoski four-shift theorem (sieve core, one sorry) plus a greedy
-- measure argument: if S has measure below T/3 in [0,T], pick four points a<b<c<d
-- in [0,T] with no pairwise difference in S, contradicting the four-shift theorem.

open Filter Real Erdos5
open scoped Topology

namespace OMA.Merikoski

/-- Chebyshev: theta x is at least x / 2 for large x. -/
lemma theta_half : ∀ᶠ x : ℝ in atTop, x / 2 ≤ Chebyshev.theta x := by
  have hsqrt : Real.sqrt =o[atTop] (id : ℝ → ℝ) := by
    refine Asymptotics.isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [eventually_ge_atTop ((1 / ε) ^ 2)] with x hx
    have hx0 : 0 ≤ x := (sq_nonneg _).trans hx
    have hh : 1 / ε ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
    rw [div_le_iff₀ hε] at hh
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0,
      abs_of_nonneg (Real.sqrt_nonneg x)]
    nlinarith [Real.mul_self_sqrt hx0, Real.sqrt_nonneg x]
  have herr := (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt).bound
    (show (0 : ℝ) < 1 / 16 by norm_num)
  have hlog := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 32 by norm_num)
  filter_upwards [herr, hlog, eventually_ge_atTop (32 : ℝ)] with x he hl hx
  have hx0 : 0 ≤ x := by linarith
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at he hl
  have hl' := (le_abs_self (Real.log x)).trans hl
  have hlogadd : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hpsi := Chebyshev.psi_ge' hx0
  have hdiff := (le_abs_self (Chebyshev.psi x - Chebyshev.theta x)).trans he
  have hprod := mul_le_mul_of_nonneg_left
    (show (2 / 3 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) (show 0 ≤ x - 1 by linarith)
  linarith [Real.log_two_lt_d9]

/-- pi(x) is at least x / (2 log x) for large x. -/
lemma pi_ge : ∀ᶠ x : ℝ in atTop, x / (2 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  filter_upwards [theta_half, eventually_ge_atTop (3 : ℝ)] with x hx hx3
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := Chebyshev.theta_le_psi x
  have h2 := Chebyshev.psi_le_primeCounting_mul_log' x
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- p_n is at most 5 n log n for large n. -/
lemma nth_prime_le : ∀ᶠ n : ℕ in atTop, (Nat.nth Nat.Prime n : ℝ) ≤ 5 * n * Real.log n := by
  have hx : Tendsto (fun n : ℕ => 5 * (n : ℝ) * Real.log n) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h3 := h1.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp h1)
    refine (h3.const_mul_atTop (show (0:ℝ) < 5 by norm_num)).congr fun n => ?_
    simp [Function.comp, mul_assoc]
  have hA := hx.eventually pi_ge
  have hB : ∀ᶠ n : ℕ in atTop, Real.log n ≤ 1 / 5 * n := by
    have := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 5 by norm_num)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually this] with n hn
    simp only [id_eq, Real.norm_eq_abs] at hn
    have h0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    rw [abs_of_nonneg h0] at hn
    exact (le_abs_self _).trans hn
  filter_upwards [hA, hB, eventually_ge_atTop 4] with n hA hB hn4
  have hn : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hlogn : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  set x := 5 * (n : ℝ) * Real.log n with hxdef
  have hxpos : 0 < x := by positivity
  have hx2 : x ≤ (n : ℝ) ^ 2 := by
    rw [hxdef, sq]; nlinarith
  have hlogx : Real.log x ≤ 2 * Real.log n := by
    have := Real.log_le_log hxpos hx2
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hlogxpos : 0 < Real.log x := Real.log_pos (by nlinarith)
  have hcount : (n : ℝ) + 1 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    refine le_trans ?_ hA
    rw [le_div_iff₀ (by positivity)]
    calc ((n:ℝ) + 1) * (2 * Real.log x) ≤ ((n:ℝ) + 1) * (4 * Real.log n) := by
          apply mul_le_mul_of_nonneg_left (by linarith); positivity
      _ ≤ x := by rw [hxdef]; nlinarith
  have hlt : n < Nat.count Nat.Prime (⌊x⌋₊ + 1) := by
    have : n + 1 ≤ Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hcount
    unfold Nat.primeCounting Nat.primeCounting' at this
    omega
  have := Nat.nth_lt_of_lt_count hlt
  have h3 : Nat.nth Nat.Prime n ≤ ⌊x⌋₊ := by omega
  calc (Nat.nth Nat.Prime n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h3
    _ ≤ x := Nat.floor_le hxpos.le

/-- log p_n / log n tends to 1. -/
theorem log_ratio : Tendsto (fun n : ℕ => log (Nat.nth Nat.Prime n : ℝ) / log n) atTop (𝓝 1) := by
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun y : ℝ => (Real.log 5 + Real.log y) / y) atTop (𝓝 0) := by
    have a := (tendsto_const_nhds (x := Real.log 5)).div_atTop tendsto_id
    have b := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have := a.add b
    simp only [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp [add_div]
  have hup : Tendsto (fun n : ℕ => 1 + (Real.log 5 + Real.log (Real.log n)) / Real.log n)
      atTop (𝓝 1) := by
    simpa using (hsmall.comp hL).const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    rw [le_div_iff₀ hlog, one_mul]
    apply Real.log_le_log (by linarith)
    have := Nat.add_two_le_nth_prime n
    exact_mod_cast (by omega : n ≤ Nat.nth Nat.Prime n)
  · filter_upwards [nth_prime_le, eventually_ge_atTop 3] with n hp hn
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 1 < Real.log n := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hppos : (0 : ℝ) < Nat.nth Nat.Prime n := by
      have := Nat.add_two_le_nth_prime n
      exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime n)
    have h1 : Real.log (Nat.nth Nat.Prime n) ≤ Real.log (5 * n * Real.log n) :=
      Real.log_le_log hppos hp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)] at h1
    rw [div_le_iff₀ (by linarith), add_mul, one_mul, div_mul_cancel₀ _ (by linarith)]
    linarith

/-- Transfer: a limit point in the prime normalisation is a limit point of normalizedGap. -/
theorem transfer {d : ℝ} {n : ℕ → ℕ} (hn : StrictMono n)
    (h : Tendsto (fun k => (primeGap (n k) : ℝ) / log (Nat.nth Nat.Prime (n k))) atTop (𝓝 d)) :
    d ∈ limitPointSet := by
  rw [mem_limitPointSet_iff]
  refine ⟨n, hn, ?_⟩
  have hr := (log_ratio.comp hn.tendsto_atTop)
  have hm := h.mul hr
  rw [mul_one] at hm
  refine hm.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hk2 : 2 ≤ n k := le_trans hk (hn.id_le k)
  have hn' : (2 : ℝ) ≤ (n k : ℝ) := by exact_mod_cast hk2
  have hp : (2 : ℝ) ≤ (Nat.nth Nat.Prime (n k) : ℝ) := by
    have := Nat.add_two_le_nth_prime (n k)
    exact_mod_cast (by omega : 2 ≤ Nat.nth Nat.Prime (n k))
  have hl1 : 0 < Real.log (Nat.nth Nat.Prime (n k) : ℝ) := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log (n k : ℝ) := Real.log_pos (by linarith)
  simp only [Function.comp, normalizedGap]
  field_simp

/-- Merikoski [Me20, Theorem 1], prime normalisation (the sieve core; remaining gap). -/
theorem merikoski_prime_norm (β : Fin 4 → ℝ) (hβ : Monotone β) :
    ∃ i j, i < j ∧ ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun k => (primeGap (n k) : ℝ) / log (Nat.nth Nat.Prime (n k)))
        atTop (𝓝 (β j - β i)) := by
  sorry


/-- Merikoski [Me20, Theorem 1] in the index normalisation of limitPointSet. -/
theorem four_shift (β : Fin 4 → ℝ) (hβ : Monotone β) :
    ∃ i j, i < j ∧ β j - β i ∈ limitPointSet := by
  obtain ⟨i, j, hij, n, hn, h⟩ := merikoski_prime_norm β hβ
  exact ⟨i, j, hij, transfer hn h⟩

open MeasureTheory Set

lemma vol_Icc_ne_top (a b : ℝ) : volume (Icc a b) ≠ ⊤ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

/-- One greedy step: a point x near the bottom of A, and the part B of A above x
whose differences with x avoid the limit point set; B loses at most eps plus
the measure of the limit point set inside [0,T]. -/
lemma greedy_step {T ε : ℝ} {A : Set ℝ} (he : 0 < ε) (hA : A ⊆ Icc 0 T)
    (hpos : 0 < volume.real A) :
    ∃ x ∈ A, ∃ B ⊆ A, (∀ y ∈ B, x < y ∧ y - x ∉ limitPointSet) ∧
      volume.real A - ε - volume.real (limitPointSet ∩ Icc 0 T) ≤ volume.real B := by
  have hne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [h] at hpos
  have hbdd : BddBelow A := ⟨0, fun y hy => (hA hy).1⟩
  obtain ⟨x, hxA, hxlt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf A) he)
  set P : Set ℝ := (fun y : ℝ => y + -x) ⁻¹' (limitPointSet ∩ Icc 0 T) with hP
  set E : Set ℝ := Icc (sInf A) x ∪ P with hE
  have hPvol : volume P = volume (limitPointSet ∩ Icc 0 T) := measure_preimage_add_right _ _ _
  have hPtop : volume P ≠ ⊤ := by
    rw [hPvol]; exact measure_ne_top_of_subset inter_subset_right (vol_Icc_ne_top 0 T)
  have hEtop : volume E ≠ ⊤ := measure_union_ne_top (vol_Icc_ne_top _ _) hPtop
  refine ⟨x, hxA, A \ E, sdiff_subset, ?_, ?_⟩
  · rintro y ⟨hyA, hyE⟩
    have hxy : x < y := by
      by_contra h
      exact hyE (Or.inl ⟨csInf_le hbdd hyA, not_lt.mp h⟩)
    refine ⟨hxy, fun hs => hyE (Or.inr ?_)⟩
    show y + -x ∈ limitPointSet ∩ Icc 0 T
    refine ⟨by rwa [← sub_eq_add_neg], by linarith, by linarith [(hA hxA).1, (hA hyA).2]⟩
  · have h1 := le_measureReal_sdiff (μ := volume) (s₁ := A) hEtop
    have h2 : volume.real E ≤ volume.real (Icc (sInf A) x) + volume.real P :=
      measureReal_union_le _ _
    have h3 : volume.real (Icc (sInf A) x) ≤ ε := by
      rw [Real.volume_real_Icc_of_le (csInf_le hbdd hxA)]; linarith
    have h4 : volume.real P = volume.real (limitPointSet ∩ Icc 0 T) := by
      simp only [Measure.real, hPvol]
    linarith

end OMA.Merikoski

open MeasureTheory Set OMA.Merikoski in
theorem OMA.solution : type_of% @Erdos5.erdos_5.variants.merikoski_measure := by
  intro T hT
  set S0 := limitPointSet ∩ Icc 0 T with hS0
  have hS0top : volume S0 ≠ ⊤ := measure_ne_top_of_subset inter_subset_right (vol_Icc_ne_top 0 T)
  rw [ENNReal.ofReal_le_iff_le_toReal hS0top]
  change T / 3 ≤ volume.real S0
  by_contra hlt
  push Not at hlt
  have hs0 : 0 ≤ volume.real S0 := measureReal_nonneg
  set ε := (T - 3 * volume.real S0) / 6 with hε
  have he : 0 < ε := by rw [hε]; linarith
  have hI : volume.real (Icc (0:ℝ) T) = T := by
    rw [Real.volume_real_Icc_of_le hT.le, sub_zero]
  obtain ⟨a, -, A, hA, ha, hAv⟩ := greedy_step he subset_rfl (by rw [hI]; exact hT)
  rw [hI] at hAv
  obtain ⟨b, hb, B, hB, hb', hBv⟩ := greedy_step he hA (by linarith)
  obtain ⟨c, hc, C, hC, hc', hCv⟩ := greedy_step he (hB.trans hA) (by linarith)
  have hCpos : 0 < volume.real C := by linarith
  obtain ⟨d, hd⟩ : C.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [h] at hCpos
  obtain ⟨hab, nab⟩ := ha b hb
  obtain ⟨hac, nac⟩ := ha c (hB hc)
  obtain ⟨had, nad⟩ := ha d (hB (hC hd))
  obtain ⟨hbc, nbc⟩ := hb' c hc
  obtain ⟨hbd, nbd⟩ := hb' d (hC hd)
  obtain ⟨hcd, ncd⟩ := hc' d hd
  have hmono : Monotone (![a, b, c, d] : Fin 4 → ℝ) := by
    refine Fin.monotone_iff_le_succ.mpr fun i => ?_
    fin_cases i
    · exact hab.le
    · exact hbc.le
    · exact hcd.le
  obtain ⟨i, j, hij, hmem⟩ := four_shift _ hmono
  fin_cases i <;> fin_cases j <;> simp at hij hmem <;> tauto
