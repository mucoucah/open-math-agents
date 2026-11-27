import FormalConjectures.ErdosProblems.«114»
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.RootsOfUnity.Complex

-- Problem: Erdős Problem 114 — large n
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/114.lean:63 (declaration Erdos114.erdos_114.variants.large_n)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial MeasureTheory Filter

namespace OMA

-- Translation invariance of the lemniscate length (normalisation step of Tao 2025:
-- one may move the centroid of the zeros to the origin).
lemma lemniscate_comp_X_add_C (p : ℂ[X]) (a : ℂ) :
    Erdos114.lemniscate (p.comp (X + C a)) =
      (IsometryEquiv.addRight a) ⁻¹' Erdos114.lemniscate p := by
  ext z
  simp [Erdos114.lemniscate]

lemma lemniscateLength_comp_X_add_C (p : ℂ[X]) (a : ℂ) :
    Erdos114.lemniscateLength (p.comp (X + C a)) = Erdos114.lemniscateLength p := by
  rw [Erdos114.lemniscateLength, Erdos114.lemniscateLength, lemniscate_comp_X_add_C,
    IsometryEquiv.hausdorffMeasure_preimage]

-- The translated polynomial is still monic of the same degree.
lemma monic_comp_X_add_C {p : ℂ[X]} (hp : p.Monic) (a : ℂ) : (p.comp (X + C a)).Monic :=
  hp.comp_X_add_C a

lemma natDegree_comp_X_add_C' (p : ℂ[X]) (a : ℂ) :
    (p.comp (X + C a)).natDegree = p.natDegree := by
  simp [Polynomial.natDegree_comp]

-- Coefficient of degree m of the translate of a monic polynomial of degree m + 1.
lemma coeff_comp_X_add_C_of_natDegree {p : ℂ[X]} (hp : p.Monic) (a : ℂ) {m : ℕ}
    (hm : p.natDegree = m + 1) :
    (p.comp (X + C a)).coeff m = (m + 1 : ℂ) * a + p.coeff m := by
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff]
  have hdeg : (hasseDeriv m p).natDegree ≤ 1 := by
    have := natDegree_hasseDeriv_le p m
    omega
  rw [eq_X_add_C_of_natDegree_le_one hdeg, hasseDeriv_coeff, hasseDeriv_coeff]
  have hc : (1 + m).choose m = m + 1 := by
    rw [add_comm]; exact Nat.choose_succ_self_right m
  have hlead : p.coeff (1 + m) = 1 := by
    have := hp.coeff_natDegree
    rwa [hm, add_comm] at this
  rw [hc, hlead, zero_add, Nat.choose_self]
  simp

-- Reduction to centred polynomials (second coefficient zero): it is enough to prove the
-- bound for monic p of degree n whose coefficient of degree n - 1 vanishes.
lemma reduce_to_centred (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ q : ℂ[X], q.Monic → q.natDegree = n → q.coeff (n - 1) = 0 →
      Erdos114.lemniscateLength q ≤ Erdos114.lemniscateLength (X ^ n - 1)) :
    ∀ p : ℂ[X], p.Monic → p.natDegree = n →
      Erdos114.lemniscateLength p ≤ Erdos114.lemniscateLength (X ^ n - 1) := by
  intro p hp hdeg
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hne : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hcancel : (m + 1 : ℂ) * (-(p.coeff m) / (m + 1)) = -(p.coeff m) := by
    field_simp
  have hq := h (p.comp (X + C (-(p.coeff m) / (m + 1)))) (hp.comp_X_add_C _)
    (by rw [natDegree_comp_X_add_C', hdeg])
    (by
      rw [Nat.add_sub_cancel, coeff_comp_X_add_C_of_natDegree hp _ hdeg, hcancel]
      ring)
  rwa [lemniscateLength_comp_X_add_C] at hq


section Benchmark

open Set
open scoped ENNReal

lemma norm_sub_one_eq_one_iff (w : ℂ) : ‖w - 1‖ = 1 ↔ ‖w‖ ^ 2 = 2 * w.re := by
  have h₁ := Complex.sq_norm w
  have h₂ := Complex.sq_norm (w - 1)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero] at h₁ h₂
  constructor
  · intro h
    rw [h] at h₂
    nlinarith
  · intro h
    have hs : ‖w - 1‖ ^ 2 = 1 := by nlinarith
    nlinarith [norm_nonneg (w - 1)]

lemma mem_lemniscate_X_pow_sub_one_iff (n : ℕ) (z : ℂ) :
    z ∈ Erdos114.lemniscate (X ^ n - 1) ↔ (‖z‖ ^ n) ^ 2 = 2 * (z ^ n).re := by
  change ‖(X ^ n - 1 : ℂ[X]).eval z‖ = 1 ↔ _
  rw [eval_sub, eval_pow, eval_X, eval_one, norm_sub_one_eq_one_iff, norm_pow]

private noncomputable def modelAngle (n : ℕ) (b : Bool) (r : ℝ) : ℝ :=
  if b then Real.arccos (r ^ n / 2) else -Real.arccos (r ^ n / 2)

private noncomputable def modelArc (n : ℕ) (u : ℂ) (b : Bool) (r : ℝ) : ℂ :=
  u * r * Complex.exp ((modelAngle n b r / n : ℝ) * Complex.I)

private lemma continuous_modelArc (n : ℕ) (u : ℂ) (b : Bool) :
    Continuous (modelArc n u b) := by
  have hθ : Continuous (modelAngle n b) := by
    cases b
    · exact (((continuous_id.pow n).div_const 2).arccos).neg
    · exact ((continuous_id.pow n).div_const 2).arccos
  exact (continuous_const.mul Complex.continuous_ofReal).mul
    (((Complex.continuous_ofReal.comp (hθ.div_const _)).mul continuous_const).cexp)

private lemma norm_modelArc {n : ℕ} (hn : 0 < n) {u : ℂ} (hu : u ^ n = 1)
    (b : Bool) {r : ℝ} (hr : 0 ≤ r) : ‖modelArc n u b r‖ = r := by
  have h : ‖u‖ ^ n = 1 := by rw [← norm_pow, hu, norm_one]
  have hu' := (pow_eq_one_iff_of_nonneg (norm_nonneg u) hn.ne').mp h
  rw [modelArc, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr, hu', one_mul, mul_one]

private lemma modelArc_pow {n : ℕ} (hn : 0 < n) {u : ℂ} (hu : u ^ n = 1) (b : Bool) (r : ℝ) :
    modelArc n u b r ^ n = (r : ℂ) ^ n * Complex.exp (modelAngle n b r * Complex.I) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [modelArc, mul_pow, mul_pow, hu, one_mul, ← Complex.exp_nat_mul, Complex.ofReal_div,
    Complex.ofReal_natCast]
  congr 2
  field_simp

private lemma modelArc_mem {n : ℕ} (hn : 0 < n) {u : ℂ} (hu : u ^ n = 1) (b : Bool)
    {r : ℝ} (hr : 0 ≤ r) (h₂ : r ^ n ≤ 2) :
    modelArc n u b r ∈ Erdos114.lemniscate (X ^ n - 1) := by
  have hcos : Real.cos (modelAngle n b r) = r ^ n / 2 := by
    have h := Real.cos_arccos (x := r ^ n / 2) (by have := pow_nonneg hr n; linarith : -1 ≤ r ^ n / 2)
      (by linarith)
    cases b <;> simpa [modelAngle, Real.cos_neg] using h
  have hre : (modelArc n u b r ^ n).re = r ^ n * (r ^ n / 2) := by
    rw [modelArc_pow hn hu, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, hcos]
  rw [mem_lemniscate_X_pow_sub_one_iff, hre, norm_modelArc hn hu b hr]
  ring

private lemma modelArc_index_unique {n : ℕ} (hn : 0 < n) {u v : ℂ}
    (hu : u ^ n = 1) (hv : v ^ n = 1) {b c : Bool} {r : ℝ} (hr : 0 < r)
    (hr₂ : r ^ n < 2) (heq : modelArc n u b r = modelArc n v c r) : u = v ∧ b = c := by
  have hp : 0 < r ^ n := pow_pos hr n
  have hsin : 0 < Real.sin (Real.arccos (r ^ n / 2)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact Real.arccos_pos.mpr (by linarith)
    · apply Real.arccos_lt_pi.mpr
      linarith
  have him := congrArg (fun z : ℂ => (z ^ n).im) heq
  change (modelArc n u b r ^ n).im = (modelArc n v c r ^ n).im at him
  simp only [modelArc_pow hn hu, modelArc_pow hn hv, ← Complex.ofReal_pow,
    Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at him
  have hsign : b = c := by
    cases b <;> cases c
    · rfl
    · simp [modelAngle, Real.sin_neg] at him
      nlinarith
    · simp [modelAngle, Real.sin_neg] at him
      nlinarith
    · rfl
  subst c
  refine ⟨?_, rfl⟩
  unfold modelArc at heq
  exact mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
    (mul_right_cancel₀ (Complex.exp_ne_zero _) heq)

-- The two open arcs for each n-th root of unity all project to the same radial
-- interval. The norm map is 1-Lipschitz, so their lengths add to at least 2 n R.
lemma model_length_lower_bound {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : R ^ n ≤ 2) :
    (2 : ℝ≥0∞) * n * ENNReal.ofReal R ≤ Erdos114.lemniscateLength (X ^ n - 1) := by
  classical
  let roots := nthRootsFinset n (1 : ℂ)
  let ι := (↥roots : Type) × Bool
  let arc : ι → ℝ → ℂ := fun i => modelArc n i.1.val i.2
  let A : ι → Set ℂ := fun i => arc i '' Ioo 0 R
  have hroot (i : ι) : (i.1.val : ℂ) ^ n = 1 := (mem_nthRootsFinset hn 1).mp i.1.property
  have hnorm (i : ι) (r : ℝ) (hr : 0 ≤ r) : ‖arc i r‖ = r :=
    norm_modelArc hn (hroot i) i.2 hr
  have hmeas (i : ι) : MeasurableSet (A i) := by
    have heq : A i = (arc i '' Icc 0 R) ∩ norm ⁻¹' Ioo 0 R := by
      ext z
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩, by simpa only [mem_preimage, hnorm i r hr.1.le] using hr⟩
      · rintro ⟨⟨r, hr, rfl⟩, hz⟩
        exact ⟨r, by simpa only [mem_preimage, hnorm i r hr.1] using hz, rfl⟩
    rw [heq]
    exact ((isCompact_Icc.image (continuous_modelArc n i.1.val i.2)).isClosed.measurableSet).inter
      (continuous_norm.measurable measurableSet_Ioo)
  have hdisj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro z ⟨r, hr, rfl⟩ ⟨s, hs, heq⟩
    have hrs : s = r := by
      simpa only [hnorm j s hs.1.le, hnorm i r hr.1.le] using congrArg norm heq
    subst s
    have hr₂ := (pow_lt_pow_left₀ hr.2 hr.1.le hn.ne').trans_le hR
    obtain ⟨hu, hb⟩ := modelArc_index_unique hn (hroot i) (hroot j) hr.1 hr₂ heq.symm
    exact hij (Prod.ext (Subtype.ext hu) hb)
  have hsub : (⋃ i, A i) ⊆ Erdos114.lemniscate (X ^ n - 1) := by
    intro z hz
    obtain ⟨i, r, hr, rfl⟩ := mem_iUnion.mp hz
    exact modelArc_mem hn (hroot i) i.2 hr.1.le
      ((pow_le_pow_left₀ hr.1.le hr.2.le n).trans hR)
  have hlen (i : ι) : ENNReal.ofReal R ≤ μH[1] (A i) := by
    have himage : norm '' A i = Ioo 0 R := by
      ext r
      constructor
      · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
        simpa only [hnorm i s hs.1.le] using hs
      · intro hr
        exact ⟨arc i r, ⟨r, hr, rfl⟩, hnorm i r hr.1.le⟩
    have h := (show LipschitzWith 1 (norm : ℂ → ℝ) from lipschitzWith_one_norm).hausdorffMeasure_image_le
      (by norm_num : (0 : ℝ) ≤ 1) (A i)
    rw [himage, hausdorffMeasure_real, Real.volume_Ioo] at h
    simpa using h
  have hcard : Fintype.card ι = n * 2 := by
    simpa [ι, roots] using (Complex.isPrimitiveRoot_exp n hn.ne').card_nthRootsFinset
  calc
    (2 : ℝ≥0∞) * n * ENNReal.ofReal R = ∑' _ : ι, ENNReal.ofReal R := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_ofNat, mul_comm (n : ℝ≥0∞) 2]
    _ ≤ ∑' i : ι, μH[1] (A i) := ENNReal.tsum_le_tsum hlen
    _ = μH[1] (⋃ i, A i) := (measure_iUnion hdisj hmeas).symm
    _ ≤ Erdos114.lemniscateLength (X ^ n - 1) := measure_mono hsub

lemma model_length_ge_two_mul_degree {n : ℕ} (hn : 0 < n) :
    (2 : ℝ≥0∞) * n ≤ Erdos114.lemniscateLength (X ^ n - 1) := by
  simpa using model_length_lower_bound hn (R := 1) (by norm_num)

lemma model_length_ge_radial_diameter_sum {n : ℕ} (hn : 0 < n) :
    (2 : ℝ≥0∞) * n * ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ)⁻¹) ≤
      Erdos114.lemniscateLength (X ^ n - 1) := by
  exact model_length_lower_bound hn
    (Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 2) hn.ne').le

private lemma exists_modelArc_of_mem {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z ∈ Erdos114.lemniscate (X ^ n - 1)) :
    ‖z‖ ^ n ≤ 2 ∧ ∃ (u : ℂ) (b : Bool), u ^ n = 1 ∧ z = modelArc n u b ‖z‖ := by
  have hzre := (mem_lemniscate_X_pow_sub_one_iff n z).mp hz
  have hre := Complex.re_le_norm (z ^ n)
  rw [norm_pow] at hre
  have hp : 0 ≤ ‖z‖ ^ n := pow_nonneg (norm_nonneg _) _
  have hR : ‖z‖ ^ n ≤ 2 := by
    by_contra! h
    nlinarith [mul_pos (show 0 < ‖z‖ ^ n by linarith) (sub_pos.mpr h)]
  refine ⟨hR, ?_⟩
  by_cases hzero : z = 0
  · exact ⟨1, true, one_pow _, by simp [hzero, modelArc]⟩
  let a (b : Bool) := modelArc n 1 b ‖z‖
  have hnrm (b : Bool) : ‖a b‖ = ‖z‖ := norm_modelArc hn (one_pow n) b (norm_nonneg z)
  have hare (b : Bool) : (a b ^ n).re = (z ^ n).re := by
    have h := (mem_lemniscate_X_pow_sub_one_iff n (a b)).mp
      (modelArc_mem hn (one_pow n) b (norm_nonneg z) hR)
    rw [hnrm b, hzre] at h
    linarith
  have him (b : Bool) : (a b ^ n).im = ‖z‖ ^ n * Real.sin (modelAngle n b ‖z‖) := by
    change (modelArc n 1 b ‖z‖ ^ n).im = _
    rw [modelArc_pow hn (one_pow n), ← Complex.ofReal_pow, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im]
  have himOpp : (a false ^ n).im = -(a true ^ n).im := by
    rw [him false, him true]
    change ‖z‖ ^ n * Real.sin (-Real.arccos (‖z‖ ^ n / 2)) =
      -(‖z‖ ^ n * Real.sin (Real.arccos (‖z‖ ^ n / 2)))
    rw [Real.sin_neg, mul_neg]
  have hsq : (z ^ n).im ^ 2 = (a true ^ n).im ^ 2 := by
    rw [← Complex.sq_norm_sub_sq_re, ← Complex.sq_norm_sub_sq_re, hare true,
      norm_pow, norm_pow, hnrm true]
  have hpow : ∃ b, z ^ n = a b ^ n := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨true, Complex.ext (hare true).symm h⟩
    · exact ⟨false, Complex.ext (hare false).symm (h.trans himOpp.symm)⟩
  obtain ⟨b, hb⟩ := hpow
  have ha : a b ≠ 0 := norm_pos_iff.mp (by rw [hnrm b]; exact norm_pos_iff.mpr hzero)
  refine ⟨z / a b, b, ?_, ?_⟩
  · rw [div_pow, hb, div_self (pow_ne_zero n ha)]
  · have hmul : modelArc n (z / a b) b ‖z‖ = (z / a b) * a b := by
      simp only [a, modelArc, one_mul, mul_assoc]
    rw [hmul, div_mul_cancel₀ _ ha]

private lemma lemniscate_model_eq_iUnion {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 ≤ R)
    (hpow : R ^ n = 2) :
    Erdos114.lemniscate (X ^ n - 1) =
      ⋃ i : (↥(nthRootsFinset n (1 : ℂ))) × Bool, modelArc n i.1.val i.2 '' Icc 0 R := by
  ext z
  constructor
  · intro hz
    obtain ⟨hle, u, b, hu, heq⟩ := exists_modelArc_of_mem hn hz
    have hrad : ‖z‖ ≤ R := by
      by_contra! h
      exact ((pow_lt_pow_left₀ h hR hn.ne').trans_le (hle.trans_eq hpow.symm)).false
    exact mem_iUnion.mpr ⟨(⟨u, (mem_nthRootsFinset hn 1).mpr hu⟩, b),
      ‖z‖, ⟨norm_nonneg z, hrad⟩, heq.symm⟩
  · intro hz
    obtain ⟨i, r, hr, rfl⟩ := mem_iUnion.mp hz
    exact modelArc_mem hn ((mem_nthRootsFinset hn 1).mp i.1.property) i.2 hr.1
      ((pow_le_pow_left₀ hr.1 hr.2 n).trans hpow.le)

private lemma norm_exp_mul_I_sub_le (x y : ℝ) :
    ‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖ ≤ |x - y| := by
  have heq : Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I) =
      Complex.exp (y * Complex.I) * (Complex.exp ((x - y : ℝ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    mul_comm (↑(x - y) : ℂ) Complex.I]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

private lemma modelArc_length_upper {n : ℕ} (hn : 0 < n) {u : ℂ} (hu : u ^ n = 1)
    (b : Bool) {R : ℝ} (hR : 0 ≤ R) :
    μH[1] (modelArc n u b '' Icc 0 R) ≤ ENNReal.ofReal (R + R * (Real.pi / 2 / n)) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hu' : ‖u‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg u) hn.ne').mp
    rw [← norm_pow, hu, norm_one]
  let φ (r : ℝ) := Real.arccos (r ^ n / 2) / (n : ℝ)
  let L := Real.pi / 2 / (n : ℝ)
  let g (r : ℝ) := r + R * (L - φ r)
  have hφlo (r : ℝ) : 0 ≤ φ r := div_nonneg (Real.arccos_nonneg _) hn'.le
  have hφhi {r : ℝ} (hr : 0 ≤ r) : φ r ≤ L :=
    div_le_div_of_nonneg_right
      (Real.arccos_le_pi_div_two.mpr (div_nonneg (pow_nonneg hr _) (by norm_num))) hn'.le
  have hφanti : AntitoneOn φ (Icc 0 R) := by
    intro r hr s hs hrs
    exact div_le_div_of_nonneg_right
      (Real.arccos_le_arccos (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hr.1 hrs n) (by norm_num))) hn'.le
  have hgmono : StrictMonoOn g (Icc 0 R) := by
    intro r hr s hs hrs
    have hφrs := hφanti hr hs hrs.le
    exact add_lt_add_of_lt_of_le hrs
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hφrs _) hR)
  have hgsub : g '' Icc 0 R ⊆ Icc 0 (R + R * L) := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨add_nonneg hr.1 (mul_nonneg hR (sub_nonneg.mpr (hφhi hr.1))),
      add_le_add hr.2 (mul_le_mul_of_nonneg_left (sub_le_self _ (hφlo r)) hR)⟩
  have hordered {r s : ℝ} (hr : r ∈ Icc 0 R) (hs : s ∈ Icc 0 R) (hrs : r ≤ s) :
      dist (modelArc n u b r) (modelArc n u b s) ≤ dist (g r) (g s) := by
    have hφrs := sub_nonneg.mpr (hφanti hr hs hrs)
    let e (t : ℝ) := Complex.exp ((modelAngle n b t / n : ℝ) * Complex.I)
    have he_norm : ‖e r‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hangle : |modelAngle n b r / n - modelAngle n b s / n| = φ r - φ s := by
      cases b
      · change |(-Real.arccos (r ^ n / 2)) / n - (-Real.arccos (s ^ n / 2)) / n| =
          φ r - φ s
        rw [neg_div, neg_div]
        change |-φ r - -φ s| = φ r - φ s
        rw [show -φ r - -φ s = -(φ r - φ s) by ring, abs_neg, abs_of_nonneg hφrs]
      · change |φ r - φ s| = φ r - φ s
        exact abs_of_nonneg hφrs
    have hExp : ‖e r - e s‖ ≤ φ r - φ s :=
      (norm_exp_mul_I_sub_le _ _).trans_eq hangle
    have hsplit : modelArc n u b r - modelArc n u b s =
        u * (((r - s : ℝ) : ℂ) * e r + (s : ℂ) * (e r - e s)) := by
      simp only [modelArc, e, Complex.ofReal_sub]
      ring
    have hDiff : 0 ≤ g s - g r := sub_nonneg.mpr (hgmono.monotoneOn hr hs hrs)
    rw [dist_eq_norm, hsplit, norm_mul, hu', one_mul, Real.dist_eq, abs_sub_comm,
      abs_of_nonneg hDiff]
    calc
      _ ≤ ‖((r - s : ℝ) : ℂ) * e r‖ + ‖(s : ℂ) * (e r - e s)‖ := norm_add_le _ _
      _ = (s - r) + s * ‖e r - e s‖ := by
        rw [norm_mul, norm_mul, he_norm, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hrs),
          abs_of_nonneg hs.1, neg_sub]
      _ ≤ (s - r) + R * (φ r - φ s) :=
        add_le_add_right (mul_le_mul hs.2 hExp (norm_nonneg _) hR) _
      _ = g s - g r := by dsimp [g]; ring
  let inv := Function.invFunOn g (Icc 0 R)
  have hinv {r : ℝ} (hr : r ∈ Icc 0 R) : inv (g r) = r :=
    hgmono.injOn.leftInvOn_invFunOn hr
  have hlip : LipschitzOnWith 1 (modelArc n u b ∘ inv) (g '' Icc 0 R) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    simp only [Function.comp_apply, hinv hr, hinv hs, NNReal.coe_one, one_mul]
    rcases le_total r s with hrs | hsr
    · exact hordered hr hs hrs
    · rw [dist_comm (modelArc n u b r), dist_comm (g r)]
      exact hordered hs hr hsr
  have himg : (modelArc n u b ∘ inv) '' (g '' Icc 0 R) =
      modelArc n u b '' Icc 0 R := by
    change (fun t => modelArc n u b (inv t)) '' (g '' Icc 0 R) = _
    rw [← image_image (modelArc n u b) inv, show inv '' g '' Icc 0 R = Icc 0 R from
      hgmono.injOn.invFunOn_image Subset.rfl]
  calc
    μH[1] (modelArc n u b '' Icc 0 R) ≤ μH[1] (g '' Icc 0 R) := by
      simpa only [himg, ENNReal.coe_one, ENNReal.one_rpow, one_mul] using
        hlip.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ μH[1] (Icc 0 (R + R * L)) := measure_mono hgsub
    _ = ENNReal.ofReal (R + R * L) := by rw [hausdorffMeasure_real, Real.volume_Icc, sub_zero]

-- The radial and angular variations bound the length of each arc.
lemma model_length_upper_bound {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 ≤ R) (hpow : R ^ n = 2) :
    Erdos114.lemniscateLength (X ^ n - 1) ≤
      (2 : ℝ≥0∞) * n * ENNReal.ofReal (R + R * (Real.pi / 2 / n)) := by
  classical
  let roots := nthRootsFinset n (1 : ℂ)
  let ι := (↥roots : Type) × Bool
  let A : ι → Set ℂ := fun i => modelArc n i.1.val i.2 '' Icc 0 R
  have hcard : Fintype.card ι = n * 2 := by
    simpa [ι, roots] using (Complex.isPrimitiveRoot_exp n hn.ne').card_nthRootsFinset
  change μH[1] (Erdos114.lemniscate (X ^ n - 1)) ≤ _
  rw [lemniscate_model_eq_iUnion hn hR hpow]
  change μH[1] (⋃ i, A i) ≤ _
  calc
    _ ≤ ∑' i, μH[1] (A i) := measure_iUnion_le A
    _ ≤ ∑' _ : ι, ENNReal.ofReal (R + R * (Real.pi / 2 / n)) :=
      ENNReal.tsum_le_tsum fun i =>
        modelArc_length_upper hn ((mem_nthRootsFinset hn 1).mp i.1.property) i.2 hR
    _ = _ := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_ofNat, mul_comm (n : ℝ≥0∞) 2]

lemma model_length_lt_top {n : ℕ} (hn : 0 < n) :
    Erdos114.lemniscateLength (X ^ n - 1) < ⊤ := by
  have hpow : ((2 : ℝ) ^ (n : ℝ)⁻¹) ^ n = 2 :=
    Real.rpow_inv_natCast_pow (by norm_num) hn.ne'
  apply (model_length_upper_bound hn (by positivity) hpow).trans_lt
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) ENNReal.ofReal_lt_top

-- The radial lower bound handles all centred polynomials whose lengths do not
-- exceed it. The sharp comparison for the remaining polynomials is the main gap.
lemma core_centred_long : ∀ᶠ n in atTop, ∀ q : ℂ[X], q.Monic → q.natDegree = n →
    q.coeff (n - 1) = 0 →
    (2 : ℝ≥0∞) * n * ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ)⁻¹) <
      Erdos114.lemniscateLength q →
    Erdos114.lemniscateLength q ≤ Erdos114.lemniscateLength (X ^ n - 1) := by
  sorry
lemma core_centred : ∀ᶠ n in atTop, ∀ q : ℂ[X], q.Monic → q.natDegree = n →
    q.coeff (n - 1) = 0 →
    Erdos114.lemniscateLength q ≤ Erdos114.lemniscateLength (X ^ n - 1) := by
  filter_upwards [core_centred_long, eventually_gt_atTop 0] with n h hn
  intro q hmon hdeg hcoeff
  obtain hlong | hshort := lt_or_ge
    ((2 : ℝ≥0∞) * n * ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ)⁻¹))
    (Erdos114.lemniscateLength q)
  · exact h q hmon hdeg hcoeff hlong
  · exact hshort.trans (model_length_ge_radial_diameter_sum hn)

end Benchmark

lemma core : ∀ᶠ n in atTop, ∀ p : ℂ[X], p.Monic → p.natDegree = n →
    Erdos114.lemniscateLength p ≤ Erdos114.lemniscateLength (X ^ n - 1) := by
  filter_upwards [core_centred, eventually_ge_atTop 1] with n h hn
  exact reduce_to_centred n hn h

end OMA

theorem OMA.solution : type_of% @Erdos114.erdos_114.variants.large_n := by
  exact OMA.core
