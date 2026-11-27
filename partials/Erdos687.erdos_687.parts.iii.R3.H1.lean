import OMAReductions.R_Erdos687_erdos_687_parts_iii_R3
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

import Mathlib.MeasureTheory.Integral.DominatedConvergence

import Mathlib.NumberTheory.Harmonic.Bounds

/-! Reduce the short prime-interval bound to the contribution of zeta zeros. -/

-- Step Erdos687.erdos_687.parts.iii.R3.H1: hypothesis H1 of reduction Erdos687.erdos_687.parts.iii.R3
-- Credit: @<handle>
-- H1 := ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n < p ∧ (p - n) ^ 3 ≤ n ^ 2  /-- Core: with `L = ⌈x^(1+ε)⌉`, every block `[b+1, b+L]` with `L^3 < b^2` lying in the first half of the period of `primorial x` contains an integer coprime to `primorial x`. -/

namespace OMA.Erdos687ShortInterval

open Filter Finset Real Chebyshev
open scoped Topology Asymptotics

private noncomputable def gap (x : ℝ) : ℝ := x ^ (2 / 3 : ℝ)

private lemma exists_prime_of_theta_lt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : theta x < theta y) : ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  classical
  by_contra! hn
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ := by
    intro p hp
    obtain ⟨hpy, hprime⟩ := Nat.mem_primesLE.mp hp
    have hle : (p : ℝ) ≤ y := (Nat.le_floor_iff hy).mp hpy
    have hpx : (p : ℝ) ≤ x := le_of_not_gt (fun hlt => (hn p hprime hlt).not_ge hle)
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx).mpr hpx, hprime⟩
  rw [theta_eq_sum_primesLE, theta_eq_sum_primesLE] at h
  exact h.not_ge (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => log_natCast_nonneg p))

private lemma eventually_prime_of_psi
    (hψ : ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * gap x ≤ psi (x + gap x) - psi x) :
    OMA.R_Erdos687_erdos_687_parts_iii_R3.H1 := by
  obtain ⟨c, hc, hmass⟩ := hψ
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  have hgrowth : Tendsto (fun x : ℝ => x ^ (1 / 6 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in atTop, C * sqrt (x + gap x) < c * gap x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), (tendsto_atTop.1 hgrowth)
      (2 * |C| / c + 1)] with x hx hlarge
    have hx0 : 0 ≤ x := zero_le_one.trans hx
    have hgap : gap x ≤ x := by
      unfold gap
      calc
        x ^ (2 / 3 : ℝ) ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx (by norm_num)
        _ = x := rpow_one x
    have hs : sqrt (x + gap x) ≤ 2 * sqrt x := by
      apply (sqrt_le_iff).2
      refine ⟨by positivity, ?_⟩
      nlinarith only [hgap, sq_sqrt hx0]
    have hstrict : 2 * |C| < c * x ^ (1 / 6 : ℝ) := by
      rw [mul_comm c]
      apply (div_lt_iff₀ hc).mp
      linarith only [hlarge]
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    calc
      C * sqrt (x + gap x) ≤ |C| * sqrt (x + gap x) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (sqrt_nonneg _)
      _ ≤ |C| * (2 * sqrt x) := mul_le_mul_of_nonneg_left hs (abs_nonneg C)
      _ < (c * x ^ (1 / 6 : ℝ)) * sqrt x := by
        rw [← mul_assoc, mul_comm |C| 2]
        exact mul_lt_mul_of_pos_right hstrict (sqrt_pos.2 hxpos)
      _ = c * gap x := by
        rw [mul_assoc, sqrt_eq_rpow, ← rpow_add hxpos]
        congr 2
        norm_num [gap]
  unfold OMA.R_Erdos687_erdos_687_parts_iii_R3.H1
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hmass,
    tendsto_natCast_atTop_atTop.eventually hsmall] with n hn hs
  have hpowers := hC ((n : ℝ) + gap n)
  have htheta : theta (n : ℝ) < theta ((n : ℝ) + gap n) := by
    linarith only [hpowers, theta_le_psi (n : ℝ), hn, hs]
  have hy : 0 ≤ (n : ℝ) + gap n := by unfold gap; positivity
  obtain ⟨p, hp, hnp, hpy⟩ := exists_prime_of_theta_lt (Nat.cast_nonneg n) hy htheta
  have hnp' : n < p := by exact_mod_cast hnp
  refine ⟨p, hp, hnp', ?_⟩
  have hsub : ((p - n : ℕ) : ℝ) ≤ gap n := by
    rw [Nat.cast_sub hnp'.le]
    linarith only [hpy]
  have hcube : gap n ^ (3 : ℕ) = (n : ℝ) ^ (2 : ℕ) := by
    rw [gap, ← rpow_mul_natCast (Nat.cast_nonneg n)]
    norm_num
  exact_mod_cast ((pow_le_pow_left₀ (Nat.cast_nonneg (p - n)) hsub 3).trans_eq hcube)

private lemma finite_zeros (T : ℝ) :
    {z : ℂ | riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T}.Finite := by
  apply ((isCompact_closedBall (0 : ℂ) (1 + T)).inter_riemannZetaZeros_finite).subset
  intro z hz
  change riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T at hz
  refine ⟨?_, hz.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by
    rw [abs_of_pos hz.2.1]
    linarith only [hz.2.2.1, hz.2.2.2])

private noncomputable def zerosUpTo (T : ℝ) : Finset ℂ :=
  (finite_zeros T).toFinset

private lemma mem_zerosUpTo {T : ℝ} {z : ℂ} :
    z ∈ zerosUpTo T ↔ riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T :=
  Set.Finite.mem_toFinset _

private noncomputable def multiplicity (z : ℂ) : ℕ := analyticOrderNatAt riemannZeta z

private noncomputable def height (x : ℝ) : ℝ := x ^ (7 / 20 : ℝ)

private noncomputable def zeroSum (T x : ℝ) : ℂ :=
  ∑ z ∈ zerosUpTo T, (multiplicity z : ℂ) * ((x : ℂ) ^ z / z)

private noncomputable def zeroWeight (T x : ℝ) : ℝ :=
  ∑ z ∈ zerosUpTo T, (multiplicity z : ℝ) * x ^ (z.re - 1)

private lemma norm_cpow_div_sub {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    {z : ℂ} (hz : z ≠ 0) (hre : z.re ≤ 1) :
    ‖(y : ℂ) ^ z / z - (x : ℂ) ^ z / z‖ ≤ x ^ (z.re - 1) * (y - x) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc x y) :
      HasDerivWithinAt (fun s : ℝ => (s : ℂ) ^ z / z)
        ((t : ℂ) ^ (z - 1)) (Set.Icc x y) t := by
    have ht0 : 0 < t := hx.trans_le ht.1
    have h := (hasDerivAt_ofReal_cpow_const ht0.ne' hz).div_const z
    rw [mul_comm z, mul_div_cancel_right₀ _ hz] at h
    exact h.hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Set.Icc x y) :
      ‖(t : ℂ) ^ (z - 1)‖ ≤ x ^ (z.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans_le ht.1), Complex.sub_re, Complex.one_re]
    exact rpow_le_rpow_of_nonpos hx ht.1 (sub_nonpos.mpr hre)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] using
    (convex_Icc x y).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
      ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩

private lemma norm_zeroSum_sub_le {T x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖zeroSum T y - zeroSum T x‖ ≤ (y - x) * zeroWeight T x := by
  classical
  unfold zeroSum zeroWeight
  rw [← sum_sub_distrib, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun z hz => ?_)
  obtain ⟨_, hpos, hlt, _⟩ := mem_zerosUpTo.mp hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hpos
  rw [← mul_sub, norm_mul, Complex.norm_natCast]
  calc
    (multiplicity z : ℝ) * ‖(y : ℂ) ^ z / z - (x : ℂ) ^ z / z‖
        ≤ (multiplicity z : ℝ) * (x ^ (z.re - 1) * (y - x)) :=
      mul_le_mul_of_nonneg_left (norm_cpow_div_sub hx hxy hz0 hlt.le) (Nat.cast_nonneg _)
    _ = _ := by ring

private lemma eventually_small_formula_error (A : ℝ) (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, A * (x ^ (13 / 20 : ℝ) * log x ^ (2 : ℕ)) ≤ gap x / 8 := by
  have hlog : (fun x : ℝ => log x ^ (2 : ℕ)) =o[atTop] (fun x : ℝ => x ^ (1 / 60 : ℝ)) := by
    simpa only [← rpow_natCast, Nat.cast_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1 / 60) (by norm_num))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlog.bound (show 0 < (8 * A)⁻¹ by positivity)]
    with x hx h
  rw [Real.norm_of_nonneg (sq_nonneg (log x)), Real.norm_of_nonneg (rpow_nonneg hx.le _)] at h
  have hs : x ^ (13 / 20 : ℝ) * x ^ (1 / 60 : ℝ) = gap x := by
    rw [← rpow_add hx, gap]
    norm_num
  calc
    A * (x ^ (13 / 20 : ℝ) * log x ^ (2 : ℕ)) ≤
        A * (x ^ (13 / 20 : ℝ) * ((8 * A)⁻¹ * x ^ (1 / 60 : ℝ))) := by gcongr
    _ = (x ^ (13 / 20 : ℝ) * x ^ (1 / 60 : ℝ)) / 8 := by field_simp
    _ = _ := by rw [hs]

-- Truncation at x^(7/20) permits a power saving over the length x^(2/3).
private def TruncatedFormula : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℝ in atTop,
    ∀ y ∈ Set.Icc x (x + gap x),
      ‖((psi y - y : ℝ) : ℂ) + zeroSum (height x) y‖ ≤
        A * (x ^ (13 / 20 : ℝ) * log x ^ (2 : ℕ))

private lemma eventually_mass_of_truncated_formula (hf : TruncatedFormula)
    (hz : Tendsto (fun x : ℝ => zeroWeight (height x) x) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop, c * gap x ≤ psi (x + gap x) - psi x := by
  obtain ⟨A, hA, hexp⟩ := hf
  refine ⟨1 / 2, by norm_num, ?_⟩
  have hw := hz.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hexp, eventually_small_formula_error A hA, hw]
    with x hx hf herr hweight
  let y := x + gap x
  have hgap : 0 ≤ gap x := rpow_nonneg hx.le _
  have hxy : x ≤ y := le_add_of_nonneg_right hgap
  let R (t : ℝ) : ℂ := ((psi t - t : ℝ) : ℂ) + zeroSum (height x) t
  have hxR : ‖R x‖ ≤ gap x / 8 := (hf _ ⟨le_rfl, hxy⟩).trans herr
  have hyR : ‖R y‖ ≤ gap x / 8 := (hf _ ⟨hxy, le_rfl⟩).trans herr
  have hzy := norm_zeroSum_sub_le (T := height x) hx hxy
  have hzy' : ‖zeroSum (height x) y - zeroSum (height x) x‖ ≤ gap x / 4 := by
    have hlen : y - x = gap x := by dsimp [y]; ring
    rw [hlen] at hzy
    exact hzy.trans (by simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (show zeroWeight (height x) x ≤ 1 / 4 from hweight.le) hgap)
  have htotal : ‖R x - R y + (zeroSum (height x) y - zeroSum (height x) x)‖ ≤ gap x / 2 := by
    linarith only [norm_add_le (R x - R y) (zeroSum (height x) y - zeroSum (height x) x),
      norm_sub_le (R x) (R y), hxR, hyR, hzy']
  have hre := (Complex.re_le_norm
    (R x - R y + (zeroSum (height x) y - zeroSum (height x) x))).trans htotal
  dsimp [R, y] at hre
  linarith only [hre]

open Classical in
-- An exponential counting bound controls the Laplace transform of the counting weights.
private lemma sum_exp_le_of_count_le {ι : Type*} (s : Finset ι) (w u : ι → ℝ)
    {A a b : ℝ} (ha : 0 < a) (hab : b < a)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hcount : ∀ t ≥ 0, ∑ i ∈ s.filter (fun i => u i ≤ t), w i ≤ A * exp (b * t)) :
    ∑ i ∈ s, w i * exp (-a * u i) ≤ A * exp b / (1 - exp (b - a)) := by
  classical
  let f (i : ι) := ⌊u i⌋₊
  have hmaps : ∀ i ∈ s, f i ∈ s.image f := fun i hi => mem_image_of_mem f hi
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hbin (j : ℕ) : ∑ i ∈ s.filter (fun i => f i = j), w i * exp (-a * u i) ≤
      (A * exp b) * exp (b - a) ^ j := by
    have hsub : s.filter (fun i => f i = j) ⊆ s.filter (fun i => u i ≤ (j : ℝ) + 1) := by
      intro i hi
      obtain ⟨his, hf⟩ := mem_filter.mp hi
      refine mem_filter.mpr ⟨his, ?_⟩
      have h := Nat.lt_floor_add_one (u i)
      change ⌊u i⌋₊ = j at hf
      simpa only [hf] using h.le
    calc
      _ ≤ ∑ i ∈ s.filter (fun i => f i = j), w i * exp (-a * (j : ℝ)) := by
        apply sum_le_sum
        intro i hi
        obtain ⟨his, hf⟩ := mem_filter.mp hi
        have hfloor : (j : ℝ) ≤ u i := by
          change ⌊u i⌋₊ = j at hf
          simpa only [hf] using Nat.floor_le (hu i his)
        apply mul_le_mul_of_nonneg_left _ (hw i his)
        exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left hfloor (neg_nonpos.mpr ha.le))
      _ ≤ ∑ i ∈ s.filter (fun i => u i ≤ (j : ℝ) + 1), w i * exp (-a * (j : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun i hi _ =>
          mul_nonneg (hw i (mem_filter.mp hi).1) (exp_nonneg _)
      _ ≤ (A * exp (b * ((j : ℝ) + 1))) * exp (-a * (j : ℝ)) := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right (hcount _ (by positivity)) (exp_nonneg _)
      _ = _ := by
        rw [← exp_nat_mul, mul_assoc, ← exp_add, mul_assoc, ← exp_add]
        congr 2
        ring
  have hq : exp (b - a) < 1 := exp_lt_one_iff.mpr (sub_neg.mpr hab)
  have hseries := hasSum_geometric_of_lt_one (exp_nonneg (b - a)) hq
  calc
    _ ≤ ∑ j ∈ s.image f, (A * exp b) * exp (b - a) ^ j := sum_le_sum fun j _ => hbin j
    _ = (A * exp b) * ∑ j ∈ s.image f, exp (b - a) ^ j := by rw [mul_sum]
    _ ≤ (A * exp b) * (1 - exp (b - a))⁻¹ := by
      have hA : 0 ≤ A := by
        have h := (sum_nonneg (fun i hi => hw i (mem_filter.mp hi).1)).trans
          (hcount 0 le_rfl)
        simpa using h
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA (exp_nonneg _))
      rw [← hseries.tsum_eq]
      exact hseries.summable.sum_le_tsum _ (fun j _ => by positivity)
    _ = _ := by rw [div_eq_mul_inv]

open Classical in
private def DensityEstimateWith (κ : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, σ ≤ 1 →
    (∑ z ∈ (zerosUpTo T).filter (fun z => σ ≤ z.re), (multiplicity z : ℝ)) ≤
      A * log T ^ B * T ^ (κ * (1 - σ))

-- The classical combined Ingham and Huxley estimate, counting multiplicities.
private def DensityEstimate : Prop := DensityEstimateWith (12 / 5)

-- A weaker form of the Vinogradov–Korobov zero-free region.
private def ZeroFreeEstimate : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop, ∀ z ∈ zerosUpTo T,
    c ≤ (1 - z.re) * log T ^ (3 / 4 : ℝ)

private lemma tendsto_log_pow_mul_exp (B : ℕ) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun x : ℝ => log x ^ B * exp (-d * log x ^ (1 / 4 : ℝ))) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => log x ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 * (B : ℝ)) d hd).comp hg).congr' ?_
  filter_upwards [tendsto_log_atTop.eventually_ge_atTop 0] with x hx
  change (log x ^ (1 / 4 : ℝ)) ^ (4 * (B : ℝ)) * exp (-d * log x ^ (1 / 4 : ℝ)) = _
  rw [← rpow_mul hx, show (1 / 4 : ℝ) * (4 * (B : ℝ)) = B by ring, rpow_natCast]

private lemma zeroWeight_tendsto_zero_with_density {κ : ℝ} (hκ₀ : 0 ≤ κ) (hκ : (7 / 20 : ℝ) * κ < 1)
    (hD : DensityEstimateWith κ) (hF : ZeroFreeEstimate) :
    Tendsto (fun x : ℝ => zeroWeight (height x) x) atTop (𝓝 0) := by
  classical
  obtain ⟨A, hA, B, hD⟩ := hD
  obtain ⟨c, hc, hF⟩ := hF
  let b := (7 / 20 : ℝ) * κ
  let d := (1 - b) / 2
  let a := b + d
  have hd : 0 < d := by dsimp [d, b]; linarith only [hκ]
  have hba : b < a := by dsimp [a]; linarith only [hd]
  have ha : 0 < a := by dsimp [a, b]; positivity
  let K := A * exp b / (1 - exp (-d))
  have hheight : Tendsto height atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hlim : Tendsto
      (fun x : ℝ => K * (log x ^ B * exp (-(d * c) * log x ^ (1 / 4 : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_log_pow_mul_exp B (mul_pos hd hc)).const_mul K
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    ((eventually_ge_atTop (0 : ℝ)).mono fun x hx =>
      sum_nonneg fun z _ => mul_nonneg (Nat.cast_nonneg _) (rpow_nonneg hx _)) ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hheight.eventually_ge_atTop 2, hheight.eventually hF]
    with x hx hT hfree
  have hx0 := zero_lt_one.trans hx
  have hlog : 0 < log x := log_pos hx
  have hT0 : 0 < height x := by linarith only [hT]
  have hlogT : log (height x) = (7 / 20 : ℝ) * log x := log_rpow hx0 _
  have hlogT0 : 0 ≤ log (height x) := by rw [hlogT]; positivity
  have hlogle : log (height x) ≤ log x := by linarith only [hlogT, hlog]
  let s := zerosUpTo (height x)
  let u (z : ℂ) := (1 - z.re) * log x
  let w (z : ℂ) : ℝ := multiplicity z
  have hnonneg (z : ℂ) (hz : z ∈ s) : 0 ≤ 1 - z.re :=
    sub_nonneg.mpr (mem_zerosUpTo.mp hz).2.2.1.le
  have hmin (z : ℂ) (hz : z ∈ s) : c * log x ^ (1 / 4 : ℝ) ≤ u z := by
    have hcompare := mul_le_mul_of_nonneg_left
      (rpow_le_rpow hlogT0 hlogle (by norm_num : (0 : ℝ) ≤ 3 / 4)) (hnonneg z hz)
    have ht := mul_le_mul_of_nonneg_right ((hfree z hz).trans hcompare)
      (rpow_nonneg hlog.le (1 / 4 : ℝ))
    rwa [mul_assoc (1 - z.re), ← rpow_add hlog,
      show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, rpow_one] at ht
  have hcount (t : ℝ) (ht : 0 ≤ t) :
      ∑ z ∈ s.filter (fun z => u z ≤ t), w z ≤ (A * log x ^ B) * exp (b * t) := by
    have hfilter : s.filter (fun z => u z ≤ t) = s.filter (fun z => 1 - t / log x ≤ z.re) := by
      ext z
      simp only [mem_filter, u, and_congr_right_iff]
      intro _
      have hdiv := le_div_iff₀ (a := 1 - z.re) (b := t) hlog
      constructor
      · intro hz
        linarith only [hdiv.mpr hz]
      · intro hz
        exact hdiv.mp (by linarith only [hz])
    have hpow : height x ^ (κ * (1 - (1 - t / log x))) =
        exp (b * t) := by
      rw [rpow_def_of_pos hT0, hlogT]
      congr 1
      dsimp [b]
      field_simp
      ring
    rw [hfilter]
    calc
      _ ≤ A * log (height x) ^ B *
          height x ^ (κ * (1 - (1 - t / log x))) :=
        hD _ hT _ (by linarith only [div_nonneg ht hlog.le])
      _ ≤ _ := by
        rw [hpow]
        gcongr
  have hsum := sum_exp_le_of_count_le s w u (a := a) (b := b)
    ha hba (fun z _ => Nat.cast_nonneg _) (fun z hz =>
      mul_nonneg (hnonneg z hz) hlog.le) hcount
  have hbound (z : ℂ) (hz : z ∈ s) :
      w z * x ^ (z.re - 1) ≤
        exp (-(d * c) * log x ^ (1 / 4 : ℝ)) * (w z * exp (-a * u z)) := by
    rw [rpow_def_of_pos hx0, show log x * (z.re - 1) =
      -d * u z + -a * u z by dsimp [u, a, d]; ring, exp_add]
    rw [← mul_assoc, mul_comm (w z), mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by dsimp [w]; positivity)
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left (hmin z hz) (neg_nonpos.mpr hd.le)
    linarith only [h, show -d * (c * log x ^ (1 / 4 : ℝ)) =
      -(d * c) * log x ^ (1 / 4 : ℝ) by ring]
  calc
    zeroWeight (height x) x ≤ ∑ z ∈ s,
        exp (-(d * c) * log x ^ (1 / 4 : ℝ)) * (w z * exp (-a * u z)) :=
      sum_le_sum hbound
    _ ≤ exp (-(d * c) * log x ^ (1 / 4 : ℝ)) *
        ((A * log x ^ B) * exp b / (1 - exp (b - a))) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left hsum (exp_nonneg _)
    _ = _ := by
      dsimp [K]
      rw [show b - a = -d by dsimp [a]; ring]
      ring

private lemma zeroWeight_tendsto_zero (hD : DensityEstimate) (hF : ZeroFreeEstimate) :
    Tendsto (fun x : ℝ => zeroWeight (height x) x) atTop (𝓝 0) :=
  zeroWeight_tendsto_zero_with_density (by norm_num) (by norm_num) hD hF

private lemma eventually_prime_of_zeta_estimates_with_density {κ : ℝ} (hκ₀ : 0 ≤ κ) (hκ : (7 / 20 : ℝ) * κ < 1)
    (hf : TruncatedFormula) (hD : DensityEstimateWith κ) (hF : ZeroFreeEstimate) :
    OMA.R_Erdos687_erdos_687_parts_iii_R3.H1 :=
  eventually_prime_of_psi
    (eventually_mass_of_truncated_formula hf (zeroWeight_tendsto_zero_with_density hκ₀ hκ hD hF))

private lemma eventually_prime_of_zeta_estimates
    (hf : TruncatedFormula) (hD : DensityEstimate) (hF : ZeroFreeEstimate) :
    OMA.R_Erdos687_erdos_687_parts_iii_R3.H1 :=
  eventually_prime_of_psi
    (eventually_mass_of_truncated_formula hf (zeroWeight_tendsto_zero hD hF))

open scoped Interval in
section

private noncomputable def zetaTerm (n : ℕ) (s : ℂ) : ℂ :=
  (s - 1) * ((n + 1 : ℕ) : ℂ) ^ (-s) +
    (((n + 1 : ℕ) : ℂ) + 1) ^ (1 - s) - ((n + 1 : ℕ) : ℂ) ^ (1 - s)

private lemma norm_zetaTerm_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖zetaTerm n s‖ ≤ ‖s - 1‖ * ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  let a : ℝ := (n + 1 : ℕ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hle : a ≤ a + 1 := by linarith
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  by_cases hs1 : s = 1
  · subst s
    simp [zetaTerm]
  let f (t : ℝ) : ℂ := (t : ℂ) ^ (-s)
  have fderiv {t : ℝ} (ht : 0 < t) :
      HasDerivAt f ((-s) * (t : ℂ) ^ (-s - 1)) t :=
    hasDerivAt_ofReal_cpow_const ht.ne' (neg_ne_zero.mpr hs0)
  have hfi : IntervalIntegrable f MeasureTheory.volume a (a + 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    exact fun t ht => (fderiv (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hd : ∫ t in a..(a + 1), f t =
      (((a + 1 : ℝ) : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
    have hne : -s ≠ -1 := fun h => hs1 (neg_injective h)
    have hz : (0 : ℝ) ∉ [[a, a + 1]] := by
      rw [Set.uIcc_of_le hle]
      exact fun h => ha.not_ge h.1
    simpa only [f, sub_eq_add_neg, add_comm (-s) 1] using
      (integral_cpow (a := a) (b := a + 1) (r := -s) (Or.inr ⟨hne, hz⟩))
  have hidentity : zetaTerm n s =
      (s - 1) * (∫ t in a..(a + 1), (f a - f t)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfi,
      intervalIntegral.integral_const, hd]
    have he : a + 1 - a = 1 := by ring
    rw [he, one_smul]
    simp only [zetaTerm, f, a, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
    field_simp [sub_ne_zero.mpr hs1, sub_ne_zero.mpr (Ne.symm hs1)]
    ring
  have hint : ‖∫ t in a..(a + 1), f a - f t‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    have hb : ∀ t ∈ Ι a (a + 1), ‖f a - f t‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
      intro t ht
      have ht' : t ∈ Set.Icc a (a + 1) := by
        simpa only [Set.uIcc_of_le hle] using Set.uIoc_subset_uIcc ht
      have hmean := (convex_Icc a (a + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := f) (f' := fun t => (-s) * (t : ℂ) ^ (-s - 1))
        (fun u hu => (fderiv (ha.trans_le hu.1)).hasDerivWithinAt)
        (C := ‖s‖ * a ^ (-s.re - 1)) (by
          intro u hu
          rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hu.1),
            Complex.sub_re, Complex.neg_re, Complex.one_re]
          exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos ha hu.1 (by linarith))
            (norm_nonneg s)) ⟨le_rfl, hle⟩ ht'
      rw [norm_sub_rev]
      exact hmean.trans (by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht'.1)]
        exact mul_le_of_le_one_right (by positivity) (by linarith [ht'.2]))
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rwa [show a + 1 - a = 1 by ring, abs_one, mul_one] at h
  rw [hidentity, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hint (norm_nonneg _)


private lemma summable_rpow_succ {e : ℝ} (he : e < -1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ e) :=
  (summable_nat_add_iff 1).2 (summable_nat_rpow.2 he)

private lemma differentiable_zetaTerm (n : ℕ) : Differentiable ℂ (zetaTerm n) := by
  have h₁ : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h₂ : ((n + 1 : ℕ) : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 + 1 ≠ 0)
  exact (((differentiable_id.sub_const 1).mul
    (differentiable_id.neg.const_cpow (Or.inl h₁))).add
    ((differentiable_const 1 |>.sub differentiable_id).const_cpow (Or.inl h₂))).sub
    ((differentiable_const 1 |>.sub differentiable_id).const_cpow (Or.inl h₁))

private lemma analyticOnNhd_zetaTermSum :
    AnalyticOnNhd ℂ (fun s => 1 + ∑' n, zetaTerm n s) {s : ℂ | 0 < s.re} := by
  intro z hz
  change 0 < z.re at hz
  let U : Set ℂ := {s : ℂ | z.re / 2 < s.re} ∩ Metric.ball (0 : ℂ) (‖z‖ + 1)
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hzU : z ∈ U := ⟨by change z.re / 2 < z.re; linarith,
    by simp [Metric.mem_ball]⟩
  refine ((differentiable_const (c := (1 : ℂ))).differentiableOn.add
    (Complex.differentiableOn_tsum_of_summable_norm
      ((summable_rpow_succ (e := -(z.re / 2) - 1) (by linarith)).mul_left
        ((‖z‖ + 2) * (‖z‖ + 1)))
      (fun n => (differentiable_zetaTerm n).differentiableOn) hU ?_)).analyticAt (hU.mem_nhds hzU)
  intro n s hs
  have hsre : z.re / 2 < s.re := hs.1
  have hsnorm : ‖s‖ < ‖z‖ + 1 := by simpa [Metric.mem_ball] using hs.2
  have hsnorm' : ‖s - 1‖ ≤ ‖z‖ + 2 := by
    have h := norm_sub_le s 1
    rw [norm_one] at h
    linarith only [h, hsnorm]
  exact (norm_zetaTerm_le n (by linarith)).trans (by
    gcongr
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

private lemma zetaTerm_summable {s : ℂ} (hs : 0 < s.re) : Summable (fun n => zetaTerm n s) :=
  ((summable_rpow_succ (e := -s.re - 1) (by linarith)).mul_left (‖s - 1‖ * ‖s‖)).of_norm_bounded
    (fun n => norm_zetaTerm_le n hs)

private lemma tendsto_cpow_one_sub {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ (1 - s))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  refine h.congr' (Eventually.of_forall fun n => ?_)
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [show (-(s.re - 1)) = (1 - s).re by simp [Complex.sub_re] ]
  change ((n + 1 : ℕ) : ℝ) ^ (1 - s).re = _
  rw [← Complex.norm_cpow_eq_rpow_re_of_pos hn, Complex.ofReal_natCast]

private lemma zetaTermSum_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    1 + ∑' n, zetaTerm n s = riemannZeta₁ s := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hζ := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hzsum : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) ^ s)) := by
    refine (summable_rpow_succ (e := -s.re) (by linarith)).of_norm_bounded (fun n => ?_)
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [one_div, norm_inv, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn,
      rpow_neg hn.le]
  have hζlim := ((hzsum.hasSum.tendsto_sum_nat).const_mul (s - 1))
  have hlim : Tendsto (fun N : ℕ => (s - 1) * (∑ n ∈ range N,
        (1 / (((n + 1 : ℕ) : ℂ) ^ s))) +
        (((N + 1 : ℕ) : ℂ) ^ (1 - s)) - 1) atTop
      (𝓝 ((s - 1) * riemannZeta s - 1)) := by
    rw [hζ]
    simpa only [add_zero, Nat.cast_add, Nat.cast_one] using (hζlim.add (tendsto_cpow_one_sub hs)).sub_const 1
  have heq (N : ℕ) :
      (∑ n ∈ range N, zetaTerm n s) = (s - 1) * (∑ n ∈ range N,
        (1 / (((n + 1 : ℕ) : ℂ) ^ s))) +
        (((N + 1 : ℕ) : ℂ) ^ (1 - s)) - 1 := by
    have htel := sum_range_sub' (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (1 - s)) N
    simp only [zero_add, Nat.cast_one, Complex.one_cpow] at htel
    calc
      _ = (∑ n ∈ range N, (s - 1) * (1 / (((n + 1 : ℕ) : ℂ) ^ s))) -
          (∑ n ∈ range N, (((n + 1 : ℕ) : ℂ) ^ (1 - s) -
            (((n + 1 : ℕ) : ℂ) + 1) ^ (1 - s))) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro n _
        rw [zetaTerm, Complex.cpow_neg, one_div]
        ring
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one] at htel ⊢
        rw [← mul_sum, htel]
        ring
  have hEq := tendsto_nhds_unique ((zetaTerm_summable hs0).hasSum.tendsto_sum_nat)
    (hlim.congr' (Eventually.of_forall fun n => (heq n).symm))
  rw [hEq, riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
  ring

private lemma zetaTermSum_eq {s : ℂ} (hs : 0 < s.re) :
    1 + ∑' n, zetaTerm n s = riemannZeta₁ s := by
  have htwo : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by norm_num
  have hnear : ∀ᶠ w : ℂ in 𝓝 2, 1 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)
  exact (analyticOnNhd_zetaTermSum.eqOn_of_preconnected_of_eventuallyEq
    (fun w _ => differentiable_riemannZeta₁.analyticAt w)
    (convex_halfSpace_re_gt 0).isPreconnected htwo
    (hnear.mono fun _ h => zetaTermSum_eq_of_one_lt_re h)) hs

private lemma norm_riemannZeta₁_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, δ ≤ s.re →
      ‖riemannZeta₁ s‖ ≤ 1 + C * (‖s - 1‖ * ‖s‖) := by
  let f (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ) ^ (-δ - 1)
  have hf : Summable f := summable_rpow_succ (by linarith)
  refine ⟨∑' n, f n, tsum_nonneg (fun n => by unfold f; positivity), fun s hs => ?_⟩
  have hs0 := hδ.trans_le hs
  have hbound (n : ℕ) : ‖zetaTerm n s‖ ≤ (‖s - 1‖ * ‖s‖) * f n := by
    apply (norm_zetaTerm_le n hs0).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos n) (by linarith)
  have hnorm : Summable (fun n => ‖zetaTerm n s‖) :=
    (hf.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  rw [← zetaTermSum_eq hs0]
  calc
    _ ≤ 1 + ‖∑' n, zetaTerm n s‖ := by simpa only [norm_one] using (norm_add_le (1 : ℂ) _)
    _ ≤ 1 + ∑' n, ‖zetaTerm n s‖ := add_le_add_right (norm_tsum_le_tsum_norm hnorm) _
    _ ≤ 1 + ∑' n, (‖s - 1‖ * ‖s‖) * f n :=
      add_le_add_right (hnorm.tsum_le_tsum hbound (hf.mul_left _)) _
    _ = _ := by rw [tsum_mul_left, mul_comm (‖s - 1‖ * ‖s‖)]


private lemma norm_riemannZeta_two_re_lower {s : ℂ} (hs : s.re = 2) :
    (1 / 4 : ℝ) ≤ ‖riemannZeta s‖ := by
  have hs' : 1 < s.re := by rw [hs]; norm_num
  let f (n : ℕ) : ℂ := 1 / (((n + 2 : ℕ) : ℂ) ^ s)
  let g (n : ℕ) : ℝ := ((n + 2 : ℕ) : ℝ) ^ (-(2 : ℝ))
  have hg : Summable g := (summable_nat_add_iff 2).2 (summable_nat_rpow.2 (by norm_num))
  have hfg (n : ℕ) : ‖f n‖ = g n := by
    unfold f g
    have hn : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    rw [one_div, norm_inv, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn,
      hs, rpow_neg hn.le]
  have hsf : Summable f := hg.of_norm_bounded fun n => (hfg n).le
  have hfζ : riemannZeta s = 1 + ∑' n, f n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs']
    have he : Summable (fun n : ℕ => 1 / ((n + 1 : ℂ) ^ s)) := by
      apply (summable_nat_add_iff 1).1
      simpa [f, Nat.cast_add, Nat.cast_one, ← add_assoc, show (2:ℂ) = 1+1 by norm_num] using hsf
    rw [he.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, div_one]
    congr 1
    apply tsum_congr
    intro n
    simp [f, Nat.cast_add]
    congr 1
    ring
  have hsg : (∑' n, g n) = π ^ (2 : ℕ) / 6 - 1 := by
    have hf₂ : (∑' n, (g n : ℂ)) = riemannZeta 2 - 1 := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num : 1 < (2 : ℂ).re)]
      have hm (n : ℕ) : (g n : ℂ) = 1 / ((((n + 1 : ℕ) : ℂ) + 1) ^ (2 : ℂ)) := by
        simp [g, one_div, Nat.cast_add]
        congr 1
        ring
      have he : Summable (fun n : ℕ => 1 / ((n + 1 : ℂ) ^ (2 : ℂ))) := by
        apply (summable_nat_add_iff 1).1
        have hh : Summable (fun n => (g n : ℂ)) := Complex.ofRealCLM.summable hg
        simpa only [hm] using hh
      rw [he.tsum_eq_zero_add]
      simp only [Nat.cast_zero, zero_add, Complex.one_cpow, div_one]
      rw [add_sub_cancel_left]
      exact tsum_congr hm
    rw [riemannZeta_two, ← Complex.ofReal_tsum g] at hf₂
    exact_mod_cast hf₂
  have ht : ‖∑' n, f n‖ ≤ (3 / 4 : ℝ) := by
    have hsfg : Summable (fun n => ‖f n‖) := by simpa only [hfg] using hg
    have hpi : π ^ 2 ≤ (3.15 : ℝ) ^ 2 :=
      pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2
    calc
      ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hsfg
      _ = π ^ 2 / 6 - 1 := by simp only [hfg, hsg]
      _ ≤ _ := by norm_num at hpi; linarith
  have htriangle := norm_sub_le (riemannZeta s) (∑' n, f n)
  have hone : riemannZeta s - (∑' n, f n) = 1 := by simp [hfζ]
  rw [hone, norm_one] at htriangle
  linarith only [htriangle, ht]

private lemma multiplicity_zeta₁ {z : ℂ} (hz : z ≠ 1) :
    analyticOrderNatAt riemannZeta₁ z = multiplicity z := by
  have hEq : riemannZeta₁ =ᶠ[𝓝 z] (fun s : ℂ => s - 1) * riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show z ∈ ({1}ᶜ : Set ℂ) from hz)]
      with s hs
    have hs' : s ≠ 1 := hs
    change riemannZeta₁ s = (s - 1) * riemannZeta s
    rw [riemannZeta_eq_inv_sub_mul hs', ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs'), one_mul]
  have hA : AnalyticAt ℂ (fun s : ℂ => s - 1) z := by fun_prop
  have hB : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz
  unfold multiplicity analyticOrderNatAt
  rw [analyticOrderAt_congr hEq, analyticOrderAt_mul hA hB,
    hA.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz), zero_add]

private lemma sum_mult_le_jensen {S : Finset ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M) (hc : riemannZeta₁ c ≠ 0)
    (hS : ∀ z ∈ S, z ∈ Metric.closedBall c r ∧ z ≠ 1)
    (hbound : ∀ z ∈ Metric.sphere c R, ‖riemannZeta₁ z‖ ≤ M) :
    ∑ z ∈ S, (multiplicity z : ℝ) ≤ log (M / ‖riemannZeta₁ c‖) / log (R / r) := by
  classical
  let U := Metric.closedBall c r
  let D := MeromorphicOn.divisor riemannZeta₁ U
  have hAnalytic (V : Set ℂ) : AnalyticOnNhd ℂ riemannZeta₁ V :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hd (z : ℂ) (hz : z ∈ S) : D z = (multiplicity z : ℤ) := by
    obtain ⟨hzU, hz1⟩ := hS z hz
    rw [← multiplicity_zeta₁ hz1, show D z = _ from MeromorphicOn.AnalyticOnNhd.divisor_apply (hAnalytic U) hzU]
    unfold analyticOrderNatAt
    cases analyticOrderAt riemannZeta₁ z using ENat.recTopCoe <;> simp
  have hSle : (∑ z ∈ S, D z) ≤ ∑ᶠ z, D z := by
    have hfinite := D.finiteSupport (isCompact_closedBall c r)
    let F := hfinite.toFinset ∪ S
    rw [finsum_eq_sum_of_support_subset _ (s := F)
      (fun z hz => mem_union_left _ (Set.Finite.mem_toFinset _ |>.mpr hz))]
    exact sum_le_sum_of_subset_of_nonneg subset_union_right (fun z _ _ =>
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAnalytic U) z)
  have hj := (hAnalytic (Metric.closedBall c |R|)).sum_divisor_le
    (r := r) (M := M) (by rwa [abs_of_pos hr])
    (by rwa [abs_of_pos hr, abs_of_pos (hr.trans hrR)]) hM hc
    (by rwa [abs_of_pos (hr.trans hrR)])
  rw [abs_of_pos hr] at hj
  exact (by
    exact_mod_cast (show (∑ z ∈ S, (multiplicity z : ℤ)) ≤ ∑ᶠ z, D z by
      rw [← sum_congr (rfl : S = S) hd]
      exact hSle) :
        ∑ z ∈ S, (multiplicity z : ℝ) ≤ ((∑ᶠ z, D z : ℤ) : ℝ)).trans hj

open scoped Classical in
private lemma right_zeros_unit_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t : ℝ),
      ∑ z ∈ (zerosUpTo T).filter (fun z =>
        1 / 2 ≤ z.re ∧ t ≤ z.im ∧ z.im ≤ t + 1), (multiplicity z : ℝ) ≤
          C * log (|t| + 2) := by
  classical
  obtain ⟨B, hB, hgrowth⟩ := norm_riemannZeta₁_le (show (0 : ℝ) < 1 / 8 by norm_num)
  let C := (log (4 * (1 + 16 * B)) / log 2 + 2) / log (15 / 14)
  have hlog₂ : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogRat : 0 < log (15 / 14 : ℝ) := log_pos (by norm_num)
  have hK : 1 ≤ 4 * (1 + 16 * B) := by nlinarith only [hB]
  have hKlog : 0 ≤ log (4 * (1 + 16 * B)) := log_nonneg hK
  refine ⟨C, div_pos (by positivity) hlogRat, fun T t => ?_⟩
  let c : ℂ := ⟨2, t + 1 / 2⟩
  have hcre : c.re = 2 := rfl
  have hcim : c.im = t + 1 / 2 := rfl
  have hc1 : c ≠ 1 := by
    intro h
    simp [h] at hcre
  have hcge : (1 / 4 : ℝ) ≤ ‖riemannZeta₁ c‖ := by
    have hcprod : riemannZeta₁ c = (c - 1) * riemannZeta c := by
      rw [riemannZeta_eq_inv_sub_mul hc1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hc1), one_mul]
    have hcsub : 1 ≤ ‖c - 1‖ := by
      have h := Complex.re_le_norm (c - 1)
      rw [Complex.sub_re, hcre, Complex.one_re] at h
      linarith only [h]
    rw [hcprod, norm_mul]
    simpa using mul_le_mul hcsub (norm_riemannZeta_two_re_lower hcre) (by norm_num) (by positivity)
  have hcnorm : ‖c‖ ≤ |t| + 5 / 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im c).trans ?_
    rw [hcre, hcim]
    have h := abs_add_le t (1 / 2 : ℝ)
    norm_num at h ⊢
    linarith only [h]
  let M := (1 + 16 * B) * (|t| + 2) ^ 2
  have hM : 1 ≤ M := by
    have ht : 1 ≤ (|t| + 2) ^ 2 := by nlinarith [abs_nonneg t]
    have hB' : 1 ≤ 1 + 16 * B := by linarith only [hB]
    simpa using mul_le_mul hB' ht zero_le_one (by positivity)
  have hsphere (z : ℂ) (hz : z ∈ Metric.sphere c (15 / 8)) :
      ‖riemannZeta₁ z‖ ≤ M := by
    have hd : ‖z - c‖ = 15 / 8 := by simpa [dist_eq_norm] using hz
    have hpos : 1 / 8 ≤ z.re := by
      have h := (Complex.abs_re_le_norm (z - c))
      rw [Complex.sub_re, hcre, hd] at h
      linarith only [(abs_le.mp h).1]
    have hznorm : ‖z‖ ≤ 4 * (|t| + 2) := by
      have ht := norm_add_le (z - c) c
      rw [sub_add_cancel, hd] at ht
      linarith only [ht, hcnorm, abs_nonneg t]
    have hzsub : ‖z - 1‖ ≤ 4 * (|t| + 2) := by
      have ht := norm_add_le (z - c) (c - 1)
      rw [sub_add_sub_cancel, hd] at ht
      have hcsub := norm_sub_le c 1
      rw [norm_one] at hcsub
      linarith only [ht, hcnorm, hcsub, abs_nonneg t]
    calc
      _ ≤ 1 + B * (‖z - 1‖ * ‖z‖) := hgrowth z hpos
      _ ≤ 1 + B * ((4 * (|t| + 2)) * (4 * (|t| + 2))) := by gcongr
      _ ≤ M := by dsimp [M]; nlinarith only [abs_nonneg t, sq_nonneg |t|]
  have hj := sum_mult_le_jensen (r := 7 / 4) (R := 15 / 8) (c := c)
    (S := (zerosUpTo T).filter (fun z => 1 / 2 ≤ z.re ∧ t ≤ z.im ∧ z.im ≤ t + 1))
    (by norm_num) (by norm_num) hM (norm_pos_iff.mp (by linarith only [hcge])) ?_ hsphere
  · refine hj.trans ?_
    have htlog : log 2 ≤ log (|t| + 2) := log_le_log (by norm_num) (le_add_of_nonneg_left (abs_nonneg t))
    have hr : (15 / 8 : ℝ) / (7 / 4) = 15 / 14 := by norm_num
    rw [hr, show C * log (|t| + 2) =
      ((log (4 * (1 + 16 * B)) / log 2 + 2) * log (|t| + 2)) / log (15 / 14) by dsimp [C]; ring]
    apply (div_le_div_iff_of_pos_right hlogRat).mpr
    have hrat : M / ‖riemannZeta₁ c‖ ≤ 4 * M := by
      apply (div_le_iff₀ (by linarith only [hcge] : 0 < ‖riemannZeta₁ c‖)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hcge (show 0 ≤ 4 * M by linarith only [hM])]
    have hb := log_le_log (div_pos (zero_lt_one.trans_le hM)
      (by linarith only [hcge])) hrat
    have hlogM : log (4 * M) = log (4 * (1 + 16 * B)) + 2 * log (|t| + 2) := by
      unfold M
      rw [← mul_assoc, log_mul (by linarith only [hK]) (by positivity), log_pow]
      norm_num
    have hscale := mul_le_mul_of_nonneg_left htlog
      (div_nonneg hKlog hlog₂.le)
    rw [div_mul_cancel₀ _ hlog₂.ne'] at hscale
    linarith only [hb, hlogM, hscale]
  · intro z hz
    obtain ⟨hzT, hrez, hlo, hhi⟩ := mem_filter.mp hz
    have hzRe := (mem_zerosUpTo.mp hzT).2.2.1
    have hre : (z - c).re ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
      rw [Complex.sub_re, hcre]
      exact sq_le_sq.mpr (abs_le.mpr (by constructor <;> linarith only [hrez, hzRe]))
    have him : (z - c).im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [Complex.sub_im, hcim]
      exact sq_le_sq.mpr (abs_le.mpr (by constructor <;> linarith only [hlo, hhi]))
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num : (0 : ℝ) ≤ 7 / 4)
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith only [hre, him]
    · intro h
      simp [h] at hzRe

private lemma analyticOrderAt_completed {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderAt riemannZeta z = analyticOrderAt completedRiemannZeta z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at h0
  have hz1 : z ≠ 1 := by rintro rfl; simp at h1
  have hEq : riemannZeta =ᶠ[𝓝 z] completedRiemannZeta * (fun s => (Complex.Gammaℝ s)⁻¹) := by
    have hn : ∀ᶠ s in 𝓝 z, s ≠ (0 : ℂ) :=
      isOpen_compl_singleton.mem_nhds (show z ∈ ({0}ᶜ : Set ℂ) from hz0)
    filter_upwards [hn] with s hs
    change riemannZeta s = completedRiemannZeta s * (Complex.Gammaℝ s)⁻¹
    rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
  have ha : AnalyticAt ℂ completedRiemannZeta z := by
    refine DifferentiableOn.analyticAt
      (s := ({0, 1} : Set ℂ)ᶜ) (fun s hs => ?_) ?_
    · have hne : s ≠ 0 ∧ s ≠ 1 := by simpa using hs
      exact (differentiableAt_completedZeta hne.1 hne.2).differentiableWithinAt
    · have hclosed : IsClosed ({0, 1} : Set ℂ) := by
        rw [show ({0, 1} : Set ℂ) = {0} ∪ {1} by ext; simp [or_comm] ]
        exact isClosed_singleton.union isClosed_singleton
      exact hclosed.isOpen_compl.mem_nhds (by simp [hz0, hz1])
  have hg : AnalyticAt ℂ (fun s => (Complex.Gammaℝ s)⁻¹) z :=
    Complex.differentiable_Gammaℝ_inv.analyticAt z
  rw [analyticOrderAt_congr hEq, analyticOrderAt_mul ha hg,
    hg.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h0)), add_zero]

private lemma multiplicity_one_sub {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    multiplicity (1 - z) = multiplicity z := by
  have h0' : 0 < (1 - z).re := by simp [Complex.sub_re, h1]
  have h1' : (1 - z).re < 1 := by simp [Complex.sub_re, h0]
  have ha : AnalyticAt ℂ (fun z : ℂ => 1 - z) z := by fun_prop
  have hd : deriv (fun z : ℂ => 1 - z) z ≠ 0 := by
    have hv : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id z).const_sub 1
    rw [hv.deriv]
    norm_num
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta) ha hd
  have he : completedRiemannZeta ∘ (fun z : ℂ => 1 - z) = completedRiemannZeta :=
    funext completedRiemannZeta_one_sub
  rw [he] at hcomp
  simp only [multiplicity, analyticOrderNatAt, analyticOrderAt_completed h0 h1,
    analyticOrderAt_completed h0' h1']
  exact congrArg ENat.toNat hcomp.symm

private lemma one_sub_mem_zerosUpTo {T : ℝ} {z : ℂ} (hz : z ∈ zerosUpTo T) :
    1 - z ∈ zerosUpTo T := by
  obtain ⟨hz0, hlo, hhi, hT⟩ := mem_zerosUpTo.mp hz
  refine mem_zerosUpTo.mpr ⟨?_, by simp [Complex.sub_re, hhi],
    by simp [Complex.sub_re, hlo], by simpa [Complex.sub_im] using hT⟩
  have hn (n : ℕ) : z ≠ -(n : ℂ) := by
    intro h
    rw [h, Complex.neg_re, Complex.natCast_re] at hlo
    linarith only [hlo, Nat.cast_nonneg (α := ℝ) n]
  have h1 : z ≠ 1 := by rintro rfl; simp at hhi
  rw [riemannZeta_one_sub hn h1, hz0, mul_zero]

open scoped Classical in
private lemma right_zeros_count :
    ∃ C : ℝ, 0 < C ∧ ∀ T ≥ 2,
      ∑ z ∈ (zerosUpTo T).filter (fun z => 1 / 2 ≤ z.re), (multiplicity z : ℝ) ≤
        C * T * log T := by
  classical
  obtain ⟨C, hC, hunit⟩ := right_zeros_unit_count
  refine ⟨5 * C, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith only [hT]
  let s := (zerosUpTo T).filter (fun z => 1 / 2 ≤ z.re)
  let b (z : ℂ) := ⌊T + z.im⌋₊
  let N := ⌊2 * T⌋₊ + 1
  have hzT (z : ℂ) (hz : z ∈ s) : |z.im| ≤ T :=
    (mem_zerosUpTo.mp (mem_filter.mp hz).1).2.2.2
  have hmaps (z : ℂ) (hz : z ∈ s) : b z ∈ range N := by
    apply mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.floor_mono (by linarith only [(abs_le.mp (hzT z hz)).2]))
  have hbins (j : ℕ) (hj : j ∈ range N) :
      ∑ z ∈ s.filter (fun z => b z = j), (multiplicity z : ℝ) ≤ C * log (T + 2) := by
    let t := (j : ℝ) - T
    have ht : |t| ≤ T := by
      have hj' : j ≤ ⌊2 * T⌋₊ := Nat.le_of_lt_succ (mem_range.mp hj)
      have hb : (j : ℝ) ≤ 2 * T :=
        (Nat.cast_le.mpr hj').trans (Nat.floor_le (by positivity))
      refine abs_le.mpr ⟨?_, ?_⟩
      · dsimp [t]; linarith only [Nat.cast_nonneg (α := ℝ) j]
      · dsimp [t]; linarith only [hb]
    have hsub : s.filter (fun z => b z = j) ⊆ (zerosUpTo T).filter (fun z =>
        1 / 2 ≤ z.re ∧ t ≤ z.im ∧ z.im ≤ t + 1) := by
      intro z hz
      obtain ⟨hzs, hzj⟩ := mem_filter.mp hz
      obtain ⟨hzero, hhalf⟩ := mem_filter.mp hzs
      have hpos : 0 ≤ T + z.im := by linarith only [(abs_le.mp (hzT z hzs)).1]
      have flo := Nat.floor_le hpos
      have fhi := Nat.lt_floor_add_one (T + z.im)
      change ⌊T + z.im⌋₊ = j at hzj
      rw [hzj] at flo fhi
      exact mem_filter.mpr ⟨hzero, hhalf, by dsimp [t]; linarith only [flo],
        by dsimp [t]; linarith only [fhi]⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => Nat.cast_nonneg _)).trans
      ((hunit T t).trans (mul_le_mul_of_nonneg_left
        (log_le_log (by positivity) (add_le_add_left ht 2)) hC.le))
  have hN : (N : ℝ) ≤ 2 * T + 1 := by
    dsimp [N]
    rw [Nat.cast_add, Nat.cast_one]
    gcongr
    exact Nat.floor_le (by positivity)
  have hlog : log (T + 2) ≤ 2 * log T := by
    have htSq : T + 2 ≤ T ^ (2 : ℕ) := by
      nlinarith only [mul_nonneg (show 0 ≤ T - 2 by linarith only [hT]) (show 0 ≤ T + 1 by positivity)]
    calc
      _ ≤ log (T ^ (2 : ℕ)) := log_le_log (by positivity) htSq
      _ = _ := by rw [log_pow]; norm_num
  change ∑ z ∈ s, (multiplicity z : ℝ) ≤ _
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ j ∈ range N, C * log (T + 2) := sum_le_sum hbins
    _ = (N : ℝ) * (C * log (T + 2)) := by simp [nsmul_eq_mul]
    _ ≤ ((5 / 2 : ℝ) * T) * (C * (2 * log T)) := by
      apply mul_le_mul (by linarith only [hN, hT]) (mul_le_mul_of_nonneg_left hlog hC.le)
      · exact mul_nonneg hC.le (log_nonneg (by linarith only [hT]))
      · positivity
    _ = _ := by ring

private lemma total_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ T ≥ 2,
      ∑ z ∈ zerosUpTo T, (multiplicity z : ℝ) ≤ C * T * log T := by
  classical
  obtain ⟨C, hC, hright⟩ := right_zeros_count
  refine ⟨2 * C, by positivity, fun T hT => ?_⟩
  let s := zerosUpTo T
  let U := s.filter (fun z => 1 / 2 ≤ z.re)
  let V := s.filter (fun z => ¬ 1 / 2 ≤ z.re)
  let g (z : ℂ) := 1 - z
  have hg : Function.Injective g := fun a b h => sub_right_injective h
  have hmaps : V.image g ⊆ U := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    obtain ⟨hws, hwr⟩ := mem_filter.mp hw
    refine mem_filter.mpr ⟨one_sub_mem_zerosUpTo hws, ?_⟩
    change 1 / 2 ≤ (1 - w).re
    rw [Complex.sub_re, Complex.one_re]
    linarith only [lt_of_not_ge hwr]
  have hv : ∑ z ∈ V, (multiplicity z : ℝ) ≤ ∑ z ∈ U, (multiplicity z : ℝ) := by
    calc
      _ = ∑ z ∈ V, (multiplicity (g z) : ℝ) := by
        apply sum_congr rfl
        intro z hz
        have hm := (mem_zerosUpTo.mp (mem_filter.mp hz).1).2
        rw [show g z = 1 - z from rfl, multiplicity_one_sub hm.1 hm.2.1]
      _ = ∑ z ∈ V.image g, (multiplicity z : ℝ) := by
        rw [sum_image (fun _ _ _ _ h => hg h)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hmaps (fun z _ _ => Nat.cast_nonneg _)
  have hpart : (∑ z ∈ U, (multiplicity z : ℝ)) + ∑ z ∈ V, (multiplicity z : ℝ) =
      ∑ z ∈ s, (multiplicity z : ℝ) := sum_filter_add_sum_filter_not _ _ _
  have h := hright T hT
  change (∑ z ∈ U, (multiplicity z : ℝ)) ≤ C * T * log T at h
  change (∑ z ∈ s, (multiplicity z : ℝ)) ≤ _
  rw [← hpart]
  linarith only [h, hv]

open scoped Classical in
private def RightDensityEstimateWith (κ : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Set.Icc (7 / 12 : ℝ) 1,
    (∑ z ∈ (zerosUpTo T).filter (fun z => σ ≤ z.re), (multiplicity z : ℝ)) ≤
      A * log T ^ B * T ^ (κ * (1 - σ))

private def RightDensityEstimate : Prop := RightDensityEstimateWith (12 / 5)

private lemma density_of_right_with {κ : ℝ} (hκ : (12 / 5 : ℝ) ≤ κ)
    (h : RightDensityEstimateWith κ) : DensityEstimateWith κ := by
  classical
  obtain ⟨A, hA, B, hbound⟩ := h
  obtain ⟨C, hC, htotal⟩ := total_zero_count
  let K := max (A / log 2) (C / log 2 ^ B)
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hK : 0 < K := (div_pos hA hlog2).trans_le (le_max_left _ _)
  refine ⟨K, hK, B + 1, fun T hT σ hσ => ?_⟩
  have hT0 : 0 < T := by linarith only [hT]
  have hlogT : log 2 ≤ log T := log_le_log (by norm_num) hT
  have hlogT0 := hlog2.trans_le hlogT
  have hKA : A ≤ K * log T :=
    (div_le_iff₀ hlog2).mp (le_max_left _ _) |>.trans
      (mul_le_mul_of_nonneg_left hlogT hK.le)
  have hKC : C ≤ K * log T ^ B :=
    (div_le_iff₀ (pow_pos hlog2 B)).mp (le_max_right _ _) |>.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog2.le hlogT B) hK.le)
  by_cases hs : 7 / 12 ≤ σ
  · refine (hbound T hT σ ⟨hs, hσ⟩).trans ?_
    calc
      _ ≤ ((K * log T) * log T ^ B) * T ^ (κ * (1 - σ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKA (pow_nonneg hlogT0.le B)) (rpow_nonneg hT0.le _)
      _ = _ := by rw [pow_succ]; ring
  · have hTpow : T ≤ T ^ (κ * (1 - σ)) := by
      calc
        T = T ^ (1 : ℝ) := (rpow_one T).symm
        _ ≤ _ := by
          apply rpow_le_rpow_of_exponent_le (by linarith only [hT])
          have hσ₀ : (5 / 12 : ℝ) ≤ 1 - σ := by linarith only [lt_of_not_ge hs]
          exact (by norm_num : (1 : ℝ) = (12 / 5) * (5 / 12)).le.trans
            (mul_le_mul hκ hσ₀ (by norm_num) (by linarith only [hκ]))
    calc
      _ ≤ ∑ z ∈ zerosUpTo T, (multiplicity z : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun z _ _ => Nat.cast_nonneg _)
      _ ≤ C * T * log T := htotal T hT
      _ ≤ ((K * log T ^ B) * T ^ (κ * (1 - σ))) * log T := by
        apply mul_le_mul_of_nonneg_right _ hlogT0.le
        exact mul_le_mul hKC hTpow hT0.le (by positivity)
      _ = _ := by rw [pow_succ]; ring

-- At half-integers the Perron kernel is uniformly away from its jump.
private lemma density_of_right (h : RightDensityEstimate) : DensityEstimate :=
  density_of_right_with (by norm_num) h

private def HalfIntegerFormula : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℝ in atTop,
    ∀ n : ℕ, (n : ℝ) + 1 / 2 ∈ Set.Icc (x - 1) (x + gap x + 1) →
      ‖((psi ((n : ℝ) + 1 / 2) - ((n : ℝ) + 1 / 2) : ℝ) : ℂ) +
        zeroSum (height x) ((n : ℝ) + 1 / 2)‖ ≤ A * (x ^ (13 / 20 : ℝ) * log x ^ (2 : ℕ))

private lemma zeroWeight_le_total {T y : ℝ} (hy : 1 ≤ y) :
    zeroWeight T y ≤ ∑ z ∈ zerosUpTo T, (multiplicity z : ℝ) := by
  classical
  apply sum_le_sum
  intro z hz
  have hzre := (mem_zerosUpTo.mp hz).2.2.1
  have hw : y ^ (z.re - 1) ≤ 1 := calc
    _ ≤ y ^ (0 : ℝ) := rpow_le_rpow_of_exponent_le hy (sub_nonpos.mpr hzre.le)
    _ = _ := rpow_zero y
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hw

private lemma truncatedFormula_of_halfIntegers (hf : HalfIntegerFormula) : TruncatedFormula := by
  obtain ⟨A, hA, hformula⟩ := hf
  obtain ⟨C, hC, htotal⟩ := total_zero_count
  have hgrowth : Tendsto height atTop atTop := tendsto_rpow_atTop (by norm_num)
  refine ⟨A + C + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), hgrowth.eventually_ge_atTop 2,
    tendsto_log_atTop.eventually_ge_atTop 1, hformula] with x hx hT hlog hformula
  intro y hy
  have hx0 : 0 < x := by linarith only [hx]
  have hy0 : 0 ≤ y := hx0.le.trans hy.1
  let n := ⌊y⌋₊
  let q := (n : ℝ) + 1 / 2
  have hflo : (n : ℝ) ≤ y := Nat.floor_le hy0
  have hfhi : y < (n : ℝ) + 1 := Nat.lt_floor_add_one y
  have hqfloor : ⌊q⌋₊ = n := by
    apply Nat.floor_eq_iff (by dsimp [q]; positivity) |>.mpr
    dsimp [q]
    constructor <;> linarith
  have hsame : psi y = psi q := by
    rw [psi_eq_psi_coe_floor y, psi_eq_psi_coe_floor q, hqfloor]
  have hq : q ∈ Set.Icc (x - 1) (x + gap x + 1) := by
    dsimp [q]
    exact ⟨by linarith only [hy.1, hfhi], by linarith only [hy.2, hflo]⟩
  have hdist : |y - q| ≤ 1 := abs_le.mpr ⟨by dsimp [q]; linarith only [hflo],
    by dsimp [q]; linarith only [hfhi]⟩
  have hζ : ‖zeroSum (height x) y - zeroSum (height x) q‖ ≤ C * height x * log (height x) := by
    have hq1 : 1 ≤ q := by linarith only [hq.1, hx]
    have hy1 : 1 ≤ y := by linarith only [hy.1, hx]
    have ht := htotal (height x) hT
    rcases le_total q y with hyq | hyq
    · exact (norm_zeroSum_sub_le (by linarith only [hq1]) hyq).trans
        ((mul_le_mul_of_nonneg_left (zeroWeight_le_total hq1) (sub_nonneg.mpr hyq)).trans
          ((mul_le_of_le_one_left (sum_nonneg (fun i _ => Nat.cast_nonneg (multiplicity i)))
            ((le_abs_self (y - q)).trans hdist)).trans ht))
    · rw [norm_sub_rev]
      have hdist' : q - y ≤ 1 := by
        have hd := (neg_le_abs (y - q)).trans hdist
        linarith only [hd]
      exact (norm_zeroSum_sub_le (by linarith only [hy1]) hyq).trans
        ((mul_le_mul_of_nonneg_left (zeroWeight_le_total hy1) (sub_nonneg.mpr hyq)).trans
          ((mul_le_of_le_one_left (sum_nonneg (fun i _ => Nat.cast_nonneg (multiplicity i)))
            hdist').trans ht))
  let E := x ^ (13 / 20 : ℝ) * log x ^ (2 : ℕ)
  have hlogT : log (height x) = (7 / 20 : ℝ) * log x := log_rpow hx0 _
  have hheight : height x ≤ x ^ (13 / 20 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by linarith only [hx]) (by norm_num)
  have hElog : log (height x) ≤ log x ^ (2 : ℕ) := by
    rw [hlogT]
    nlinarith only [hlog, sq_nonneg (log x - 1)]
  have hE1 : 1 ≤ E := by
    have hp : 1 ≤ x ^ (13 / 20 : ℝ) := one_le_rpow (by linarith only [hx]) (by norm_num)
    dsimp [E]
    nlinarith only [mul_le_mul hp (pow_le_pow_left₀ zero_le_one hlog 2) (by norm_num)
      (rpow_nonneg hx0.le (13 / 20 : ℝ))]
  have hζE : C * height x * log (height x) ≤ C * E := by
    dsimp [E]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul hheight hElog ?_ (rpow_nonneg hx0.le _)) hC.le
    rw [hlogT]
    positivity
  have hnorm : ‖((q - y : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hdist
  have hrewrite :
      ((psi y - y : ℝ) : ℂ) + zeroSum (height x) y =
        (((psi q - q : ℝ) : ℂ) + zeroSum (height x) q) +
          (((q - y : ℝ) : ℂ) + (zeroSum (height x) y - zeroSum (height x) q)) := by
    rw [hsame]
    push_cast
    ring
  rw [hrewrite]
  have ht := hformula n hq
  change ‖((psi q - q : ℝ) : ℂ) + zeroSum (height x) q‖ ≤ A * E at ht
  linarith only [norm_add_le (((psi q - q : ℝ) : ℂ) + zeroSum (height x) q)
    (((q - y : ℝ) : ℂ) + (zeroSum (height x) y - zeroSum (height x) q)),
    norm_add_le ((q - y : ℝ) : ℂ) (zeroSum (height x) y - zeroSum (height x) q),
    ht, hnorm, hζ.trans hζE, hE1]

private noncomputable def negZetaLogDeriv (σ t : ℝ) : ℝ :=
  (-deriv riemannZeta (⟨σ, t⟩ : ℂ) / riemannZeta (⟨σ, t⟩ : ℂ)).re

private lemma re_vonMangoldt_term (σ t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨σ, t⟩ : ℂ) n).re =
      ArithmeticFunction.vonMangoldt n * exp (-σ * log n) * cos (t * log n) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero hn', Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_re]
  rw [Complex.mul_re, Complex.mul_im]
  have hre : (Complex.log (n : ℂ)).re = log n := by
    rw [← Complex.natCast_log, Complex.ofReal_re]
  have him : (Complex.log (n : ℂ)).im = 0 := by
    rw [← Complex.natCast_log, Complex.ofReal_im]
  simp [Complex.neg_re, Complex.neg_im, hre, him, cos_neg, mul_assoc, mul_comm]

private lemma negZetaLogDeriv_positive_combination {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * negZetaLogDeriv σ 0 + 4 * negZetaLogDeriv σ t + negZetaLogDeriv σ (2 * t) := by
  let f (t : ℝ) (n : ℕ) := (LSeries.term
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨σ, t⟩ : ℂ) n).re
  have hsum0 (t : ℝ) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (⟨σ, t⟩ : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hσ
  have hsum (t : ℝ) : Summable (f t) := Complex.reCLM.summable (hsum0 t)
  have hEq (t : ℝ) : negZetaLogDeriv σ t = ∑' n, f t n := by
    unfold negZetaLogDeriv
    rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (show 1 < (⟨σ, t⟩ : ℂ).re from hσ)]
    exact Complex.re_tsum (hsum0 t)
  rw [hEq, hEq, hEq, ← tsum_mul_left, ← tsum_mul_left,
    ← ((hsum 0).mul_left 3).tsum_add ((hsum t).mul_left 4),
    ← (((hsum 0).mul_left 3).add ((hsum t).mul_left 4)).tsum_add (hsum (2 * t))]
  refine tsum_nonneg fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [f]
  · simp only [f, re_vonMangoldt_term _ _ hn, zero_mul, cos_zero, mul_one]
    rw [show 2 * t * log n = 2 * (t * log n) by ring, cos_two_mul]
    have heq : 3 * (ArithmeticFunction.vonMangoldt n * exp (-σ * log n)) +
        4 * (ArithmeticFunction.vonMangoldt n * exp (-σ * log n) * cos (t * log n)) +
        ArithmeticFunction.vonMangoldt n * exp (-σ * log n) * (2 * cos (t * log n) ^ 2 - 1) =
        2 * (ArithmeticFunction.vonMangoldt n * exp (-σ * log n)) * (1 + cos (t * log n)) ^ 2 := by ring
    rw [heq]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg
      ArithmeticFunction.vonMangoldt_nonneg (exp_nonneg _))) (sq_nonneg _)

private lemma negZetaLogDeriv_near_pole :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 < d ∧ ∀ σ ∈ Set.Ioo 1 (1 + d),
      negZetaLogDeriv σ 0 ≤ (σ - 1)⁻¹ + C := by
  obtain ⟨C, hC⟩ := log_deriv_riemannZeta_add_inv_sub_bounded.bound
  have he : ∀ᶠ s : ℂ in 𝓝[≠] 1,
      ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖ ≤ C := by simpa using hC
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨|C|, d, abs_nonneg _, hd, fun σ hσ => ?_⟩
  have hdist : dist ((σ : ℂ)) 1 = σ - 1 := by
    rw [dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hσ.1)]
  have hσ1 : ((σ : ℂ)) ≠ 1 := by
    intro h
    exact hσ.1.ne' (by exact_mod_cast h)
  have h := hball (show ((σ : ℂ)) ∈ Metric.ball 1 d ∩ ({1}ᶜ : Set ℂ) from
    ⟨Metric.mem_ball.mpr (by rw [hdist]; linarith only [hσ.2]), hσ1⟩)
  change ‖deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) + ((σ : ℂ) - 1)⁻¹‖ ≤ C at h
  let w : ℂ := deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) + ((σ : ℂ) - 1)⁻¹
  have hw : -w.re ≤ |C| :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm w).trans (h.trans (le_abs_self _)))
  have heq : w.re = -negZetaLogDeriv σ 0 + (σ - 1)⁻¹ := by
    unfold w negZetaLogDeriv
    change (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) + ((σ : ℂ) - 1)⁻¹).re =
      -(-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re + (σ - 1)⁻¹
    rw [neg_div, Complex.neg_re, neg_neg, Complex.add_re,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [heq] at hw
  linarith only [hw]

private noncomputable def logScale (t : ℝ) : ℝ := log (|t| + 3) ^ (3 / 4 : ℝ)

-- A logarithmic derivative bound that retains the contribution of an aligned zero.
private def LogDerivativeEstimate : Prop :=
  ∃ K T₀ d : ℝ, 0 < K ∧ 0 ≤ T₀ ∧ 0 < d ∧
    (∀ t : ℝ, T₀ ≤ |t| → ∀ σ ∈ Set.Ioo 1 (1 + d), negZetaLogDeriv σ t ≤ K * logScale t) ∧
    ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 → T₀ ≤ |z.im| →
      ∀ σ ∈ Set.Ioo 1 (1 + d), negZetaLogDeriv σ z.im ≤ K * logScale z.im - (σ - z.re)⁻¹

private lemma one_le_logScale (t : ℝ) : 1 ≤ logScale t := by
  have h := log_le_log (exp_pos 1)
    (exp_one_lt_three.le.trans (le_add_of_nonneg_left (abs_nonneg t)))
  rw [log_exp] at h
  exact one_le_rpow h (by norm_num)

private lemma logScale_double_le (t : ℝ) : logScale (2 * t) ≤ 2 * logScale t := by
  have ha : |2 * t| + 3 ≤ (|t| + 3) ^ (2 : ℕ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith only [abs_nonneg t, sq_nonneg |t|]
  have hb : log (|2 * t| + 3) ≤ 2 * log (|t| + 3) := by
    calc
      _ ≤ log ((|t| + 3) ^ (2 : ℕ)) := log_le_log (by positivity) ha
      _ = _ := by rw [log_pow]; norm_num
  unfold logScale
  calc
    _ ≤ (2 * log (|t| + 3)) ^ (3 / 4 : ℝ) :=
      rpow_le_rpow (log_nonneg (by linarith only [abs_nonneg (2 * t)])) hb (by norm_num)
    _ = (2 : ℝ) ^ (3 / 4 : ℝ) * log (|t| + 3) ^ (3 / 4 : ℝ) :=
      mul_rpow (by norm_num) (log_nonneg (by linarith only [abs_nonneg t]))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (rpow_nonneg (log_nonneg (by linarith only [abs_nonneg t])) _)
      exact (rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 / 4 : ℝ) ≤ 1)).trans_eq (rpow_one 2)

private lemma finite_pos_lower {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨c, hc, hlo⟩ := ih (fun j hj => hf j (mem_insert_of_mem hj))
    refine ⟨min (f i) c, lt_min (hf i (mem_insert_self i s)) hc, fun j hj => ?_⟩
    rcases mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hlo j hj)

private def ScaledLogDerivativeEstimate : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ k : ℝ, 0 < k → ∃ T₀ : ℝ, 0 ≤ T₀ ∧
    (∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, k ≤ (σ - 1) * logScale t → (σ - 1) * logScale t ≤ 2 * k →
      negZetaLogDeriv σ t ≤ K * logScale t) ∧
    ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 → T₀ ≤ |z.im| →
      ∀ σ : ℝ, k ≤ (σ - 1) * logScale z.im → (σ - 1) * logScale z.im ≤ 2 * k →
        negZetaLogDeriv σ z.im ≤ K * logScale z.im - (σ - z.re)⁻¹

private lemma logScale_mono_abs {t s : ℝ} (h : |t| ≤ |s|) : logScale t ≤ logScale s := by
  have hp : 0 < |t| + 3 := by positivity
  have hlt : log (|t| + 3) ≤ log (|s| + 3) := log_le_log hp (by linarith only [h])
  have hlt0 : 0 ≤ log (|t| + 3) := log_nonneg (by linarith only [abs_nonneg t])
  exact rpow_le_rpow hlt0 hlt (by norm_num)

private lemma tendsto_add_three_atTop : Tendsto (fun t : ℝ => t + 3) atTop atTop := by
  refine tendsto_atTop.2 fun a => ?_
  filter_upwards [eventually_ge_atTop a] with t ht
  linarith only [ht]

private lemma tendsto_logScale : Tendsto logScale atTop atTop := by
  refine ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
    (tendsto_log_atTop.comp tendsto_add_three_atTop)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [logScale, abs_of_nonneg ht]

private lemma scaledLogDerivative_of_uniform (h : LogDerivativeEstimate) : ScaledLogDerivativeEstimate := by
  obtain ⟨K, T₀, d, hK, hT₀, hd, hb, ha⟩ := h
  refine ⟨K, hK, fun k hk => ?_⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (tendsto_logScale.eventually_ge_atTop (2 * k / d + 1))
  let U := max T₀ T
  have hs (t σ : ℝ) (ht : U ≤ |t|) (hlo : k ≤ (σ - 1) * logScale t)
      (hhi : (σ - 1) * logScale t ≤ 2 * k) : σ ∈ Set.Ioo 1 (1 + d) := by
    have hL : 0 < logScale t := zero_lt_one.trans_le (one_le_logScale _)
    have h1 : 1 < σ := by
      by_contra! hn
      exact (hk.trans_le hlo).not_ge (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn) hL.le)
    have hbig := hT |t| ((le_max_right _ _).trans ht)
    rw [show logScale |t| = logScale t by simp [logScale] ] at hbig
    have hLD : 2 * k < logScale t * d :=
      (div_lt_iff₀ hd).mp (by linarith only [hbig])
    have hlt : (σ - 1) * logScale t < d * logScale t := by
      linarith only [hhi, hLD, mul_comm d (logScale t)]
    exact ⟨h1, by linarith only [(mul_lt_mul_iff_left₀ hL).mp hlt]⟩
  refine ⟨U, hT₀.trans (le_max_left _ _), ?_, ?_⟩
  · intro t ht σ hlo hhi
    exact hb t ((le_max_left _ _).trans ht) σ (hs t σ ht hlo hhi)
  · intro z hz h0 h1 ht σ hlo hhi
    exact ha z hz h0 h1 ((le_max_left _ _).trans ht) σ (hs z.im σ ht hlo hhi)

private lemma zeroFree_of_scaledLogDerivative (h : ScaledLogDerivativeEstimate) : ZeroFreeEstimate := by
  obtain ⟨K, hK, hscaled⟩ := h
  obtain ⟨C, d₀, hC, hd₀, hpole⟩ := negZetaLogDeriv_near_pole
  let D := 3 * C + 6 * K
  have hD : 0 ≤ D := by unfold D; positivity
  let k := min (d₀ / 2) (1 / (4 * (D + 1)))
  have hk : 0 < k := lt_min (by positivity) (by positivity)
  have hkd₀ : k < d₀ := (min_le_left _ _).trans_lt (by linarith only [hd₀])
  have hkD : k ≤ 1 / (4 * (D + 1)) := min_le_right _ _
  obtain ⟨T₀, hT₀, hbasic, halign⟩ := hscaled k hk
  have hKbound : k * D ≤ 1 / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (D + 1))).mp hkD
    nlinarith only [hh, hk]
  have hlarge (z : ℂ) (hz : riemannZeta z = 0) (hlo : 0 < z.re) (hhi : z.re < 1)
      (hzT : T₀ ≤ |z.im|) : k / 8 ≤ (1 - z.re) * logScale z.im := by
    let L := logScale z.im
    have hL : 1 ≤ L := one_le_logScale _
    have hL0 : 0 < L := zero_lt_one.trans_le hL
    let a := k / L
    have ha : 0 < a := div_pos hk hL0
    have hak : a ≤ k := (div_le_iff₀ hL0).2 (le_mul_of_one_le_right hk.le hL)
    have haL : a * L = k := div_mul_cancel₀ _ hL0.ne'
    let σ := 1 + a
    have hσa : σ - 1 = a := by dsimp [σ]; ring
    have hσ₀ : σ ∈ Set.Ioo 1 (1 + d₀) := ⟨by dsimp [σ]; linarith only [ha],
      by dsimp [σ]; linarith only [hak, hkd₀]⟩
    have hsc : (σ - 1) * logScale z.im = k := by rw [hσa]; exact haL
    have h2log : logScale z.im ≤ logScale (2 * z.im) := by
      apply logScale_mono_abs
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith only [abs_nonneg z.im]
    have hbsc : k ≤ (σ - 1) * logScale (2 * z.im) := by
      rw [← hsc]
      exact mul_le_mul_of_nonneg_left h2log (sub_nonneg.mpr hσ₀.1.le)
    have hbsc' : (σ - 1) * logScale (2 * z.im) ≤ 2 * k := by
      have hmul := mul_le_mul_of_nonneg_left (logScale_double_le z.im)
        (sub_nonneg.mpr hσ₀.1.le)
      rw [← mul_left_comm, hsc] at hmul
      exact hmul
    have h2 : T₀ ≤ |2 * z.im| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith only [hzT, abs_nonneg z.im]
    have h3 := negZetaLogDeriv_positive_combination hσ₀.1 z.im
    have hr := hpole σ hσ₀
    have hρ := halign z hz hlo hhi hzT σ (by rw [hsc]) (by rw [hsc]; linarith only [hk])
    have h₂ := (hbasic (2 * z.im) h2 σ hbsc hbsc').trans
      (mul_le_mul_of_nonneg_left (logScale_double_le z.im) hK.le)
    rw [hσa] at hr
    have hmain : 4 * (σ - z.re)⁻¹ ≤ 3 * a⁻¹ + D * L := by
      have hCL : 3 * C ≤ 3 * C * L := le_mul_of_one_le_right (by positivity) hL
      change negZetaLogDeriv σ z.im ≤ K * L - (σ - z.re)⁻¹ at hρ
      change negZetaLogDeriv σ (2 * z.im) ≤ K * (2 * L) at h₂
      dsimp [D]
      linarith only [h3, hr, hρ, h₂, hCL]
    have hDL : D * L ≤ (1 / 4 : ℝ) / a := by
      apply (le_div_iff₀ ha).2
      calc
        D * L * a = D * (a * L) := by ring
        _ ≤ _ := by rw [haL, mul_comm D]; exact hKbound
    have hb : 0 < σ - z.re := sub_pos.mpr (hhi.trans hσ₀.1)
    have hsmall : a / 8 ≤ 1 - z.re := by
      by_contra! hcontra
      have ht : σ - z.re ≤ (9 / 8 : ℝ) * a := by dsimp [σ]; linarith only [hcontra]
      have hlower : (32 / 9 : ℝ) / a ≤ 4 / (σ - z.re) := by
        apply (div_le_div_iff₀ ha hb).2
        linarith only [ht]
      have hupper : 4 / (σ - z.re) ≤ (13 / 4 : ℝ) / a := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        rw [div_eq_mul_inv] at hDL
        linarith only [hmain, hDL]
      have himp := (div_le_div_iff_of_pos_right ha).1 (hlower.trans hupper)
      norm_num at himp
    calc
      k / 8 = (a / 8) * L := by rw [div_mul_eq_mul_div, haL]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hL0.le
  obtain ⟨b, hb, hfinite⟩ := finite_pos_lower (zerosUpTo T₀) (fun z => 1 - z.re)
    (fun z hz => sub_pos.mpr (mem_zerosUpTo.mp hz).2.2.1)
  refine ⟨min b (k / 16), lt_min hb (by positivity), ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
  intro z hz
  obtain ⟨hζ, hlo, hhi, hheight⟩ := mem_zerosUpTo.mp hz
  have hL : 1 ≤ log T ^ (3 / 4 : ℝ) := by
    have h := log_le_log (exp_pos 1) (exp_one_lt_three.le.trans hT)
    rw [log_exp] at h
    exact one_le_rpow h (by norm_num)
  by_cases hzt : |z.im| ≤ T₀
  · have hfin := hfinite z (mem_zerosUpTo.mpr ⟨hζ, hlo, hhi, hzt⟩)
    exact (min_le_left _ _).trans (hfin.trans (le_mul_of_one_le_right (sub_nonneg.mpr hhi.le) hL))
  · have hpow : |z.im| + 3 ≤ T ^ (2 : ℕ) := by
      have hh := mul_nonneg (show 0 ≤ T - 3 by linarith only [hT])
        (show 0 ≤ T + 2 by linarith only [hT])
      nlinarith only [hh, hheight, hT]
    have ht : log (|z.im| + 3) ≤ 2 * log T := by
      calc
        _ ≤ log (T ^ (2 : ℕ)) := log_le_log (by positivity) hpow
        _ = _ := by rw [log_pow]; norm_num
    have ht' : logScale z.im ≤ 2 * log T ^ (3 / 4 : ℝ) := by
      unfold logScale
      have hlog : 0 ≤ log T := log_nonneg (by linarith only [hT])
      calc
        _ ≤ (2 * log T) ^ (3 / 4 : ℝ) :=
          rpow_le_rpow (log_nonneg (by linarith only [abs_nonneg z.im])) ht (by norm_num)
        _ = (2 : ℝ) ^ (3 / 4 : ℝ) * log T ^ (3 / 4 : ℝ) := mul_rpow (by norm_num) hlog
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (rpow_nonneg hlog _)
          exact (rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (by norm_num : (3 / 4 : ℝ) ≤ 1)).trans_eq (rpow_one 2)
    have hzlarge := (hlarge z hζ hlo hhi (le_of_not_ge hzt)).trans
      (mul_le_mul_of_nonneg_left ht' (sub_nonneg.mpr hhi.le))
    exact (min_le_right _ _).trans (by linarith only [hzlarge])

private lemma zeroFree_of_logDerivative (h : LogDerivativeEstimate) : ZeroFreeEstimate :=
  zeroFree_of_scaledLogDerivative (scaledLogDerivative_of_uniform h)

private lemma log_add_two_neg_sub_one_le (t : ℝ) : log (|-t - 1| + 2) ≤ 2 * log (|t| + 2) := by
  have h := abs_add_le (-t) (-1 : ℝ)
  rw [abs_neg, abs_neg, abs_one] at h
  have hpow : |-t - 1| + 2 ≤ (|t| + 2) ^ (2 : ℕ) := by
    rw [sub_eq_add_neg]
    nlinarith only [h, abs_nonneg t, sq_nonneg |t|]
  calc
    _ ≤ log ((|t| + 2) ^ (2 : ℕ)) := log_le_log (by positivity) hpow
    _ = _ := by rw [log_pow]; norm_num

open scoped Classical in
private lemma all_zeros_unit_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t : ℝ),
      ∑ z ∈ (zerosUpTo T).filter (fun z => t ≤ z.im ∧ z.im ≤ t + 1), (multiplicity z : ℝ) ≤
          C * log (|t| + 2) := by
  classical
  obtain ⟨C, hC, hunit⟩ := right_zeros_unit_count
  refine ⟨3 * C, by positivity, fun T t => ?_⟩
  let U := (zerosUpTo T).filter (fun z => t ≤ z.im ∧ z.im ≤ t + 1)
  let Upos := U.filter (fun z => 1 / 2 ≤ z.re)
  let Uneg := U.filter (fun z => ¬ 1 / 2 ≤ z.re)
  let V := (zerosUpTo T).filter (fun z => 1 / 2 ≤ z.re ∧ -t - 1 ≤ z.im ∧ z.im ≤ (-t - 1) + 1)
  let g (z : ℂ) := 1 - z
  have hg : Function.Injective g := fun a b h => sub_right_injective h
  have hmaps : Uneg.image g ⊆ V := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    obtain ⟨hws, hwr⟩ := mem_filter.mp hw
    obtain ⟨hwz, hlo, hhi⟩ := mem_filter.mp hws
    apply mem_filter.mpr
    refine ⟨one_sub_mem_zerosUpTo hwz, ?_⟩
    change 1 / 2 ≤ (1 - w).re ∧ -t - 1 ≤ (1 - w).im ∧ (1 - w).im ≤ (-t - 1) + 1
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
    exact ⟨by linarith only [lt_of_not_ge hwr], by linarith only [hhi], by linarith only [hlo]⟩
  have hleft : ∑ z ∈ Uneg, (multiplicity z : ℝ) ≤ C * log (|-t - 1| + 2) := by
    calc
      _ = ∑ z ∈ Uneg, (multiplicity (g z) : ℝ) := by
        apply sum_congr rfl
        intro z hz
        have hm := (mem_zerosUpTo.mp (mem_filter.mp (mem_filter.mp hz).1).1).2
        rw [show g z = 1 - z from rfl, multiplicity_one_sub hm.1 hm.2.1]
      _ = ∑ z ∈ Uneg.image g, (multiplicity z : ℝ) := by
        rw [sum_image (fun _ _ _ _ h => hg h)]
      _ ≤ ∑ z ∈ V, (multiplicity z : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hmaps (fun z _ _ => Nat.cast_nonneg _)
      _ ≤ _ := hunit T (-t - 1)
  have hright : ∑ z ∈ Upos, (multiplicity z : ℝ) ≤ C * log (|t| + 2) := by
    have heq : Upos = (zerosUpTo T).filter (fun z => 1 / 2 ≤ z.re ∧ t ≤ z.im ∧ z.im ≤ t + 1) := by
      ext z
      simp only [Upos, U, mem_filter]
      tauto
    rw [heq]
    exact hunit T t
  have hpart : (∑ z ∈ Upos, (multiplicity z : ℝ)) + ∑ z ∈ Uneg, (multiplicity z : ℝ) =
      ∑ z ∈ U, (multiplicity z : ℝ) := sum_filter_add_sum_filter_not _ _ _
  change (∑ z ∈ U, (multiplicity z : ℝ)) ≤ _
  rw [← hpart]
  have hlog := mul_le_mul_of_nonneg_left (log_add_two_neg_sub_one_le t) hC.le
  linarith only [hright, hleft, hlog]

private def SeparatedDensityEstimateWith (κ : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Set.Icc (7 / 12 : ℝ) 1,
    ∀ S : Finset ℂ, S ⊆ zerosUpTo T → (∀ z ∈ S, σ ≤ z.re) →
      (↑S : Set ℂ).Pairwise (fun z w => 1 ≤ |z.im - w.im|) →
      (S.card : ℝ) ≤ A * log T ^ B * T ^ (κ * (1 - σ))

private def SeparatedDensityEstimate : Prop := SeparatedDensityEstimateWith (12 / 5)

private lemma one_le_abs_sub_of_floor_same_parity {x y : ℝ} (hne : ⌊x⌋ ≠ ⌊y⌋)
    (hmod : ⌊x⌋ % (2 : ℤ) = ⌊y⌋ % 2) : 1 ≤ |x - y| := by
  have hx₀ := Int.floor_le x
  have hy₀ := Int.floor_le y
  have hx₁ := Int.lt_floor_add_one x
  have hy₁ := Int.lt_floor_add_one y
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h : ⌊x⌋ + 2 ≤ ⌊y⌋ := by omega
    have hr : (⌊x⌋ : ℝ) + 2 ≤ (⌊y⌋ : ℝ) := by exact_mod_cast h
    apply (show 1 ≤ -(x - y) by linarith only [hx₁, hy₀, hr]).trans
    exact neg_le_abs _
  · have h : ⌊y⌋ + 2 ≤ ⌊x⌋ := by omega
    have hr : (⌊y⌋ : ℝ) + 2 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast h
    apply (show 1 ≤ x - y by linarith only [hy₁, hx₀, hr]).trans
    exact le_abs_self _

private lemma rightDensity_of_separated_with {κ : ℝ} (h : SeparatedDensityEstimateWith κ) :
    RightDensityEstimateWith κ := by
  classical
  obtain ⟨A, hA, B, hbound⟩ := h
  obtain ⟨C, hC, hunit⟩ := all_zeros_unit_count
  refine ⟨6 * A * C, by positivity, B + 1, fun T hT σ hσ => ?_⟩
  let S := (zerosUpTo T).filter (fun z => σ ≤ z.re)
  let k (z : ℂ) : ℤ := ⌊z.im⌋
  let J := S.image k
  have hj (j : ℤ) (hj : j ∈ J) : ∃ z ∈ S, k z = j := Finset.mem_image.mp hj
  let r (j : ℤ) : ℂ := if h : j ∈ J then (hj j h).choose else 0
  have hr (j : ℤ) (hj' : j ∈ J) : r j ∈ S ∧ k (r j) = j := by
    rw [show r j = (hj j hj').choose from dif_pos hj']
    exact (hj j hj').choose_spec
  have hri : Set.InjOn r (J : Set ℤ) := by
    intro j hj l hl heq
    have he := congrArg k heq
    rwa [(hr j hj).2, (hr l hl).2] at he
  let p (j : ℤ) : Prop := j % 2 = 0
  let V := A * log T ^ B * T ^ (κ * (1 - σ))
  have hrep (P : ℤ → Prop) [DecidablePred P]
      (hpar : ∀ j l : ℤ, P j → P l → j % 2 = l % 2) :
      ((J.filter P).card : ℝ) ≤ V := by
    let E := (J.filter P).image r
    have hsub : E ⊆ S := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact (hr j (Finset.mem_filter.mp hj).1).1
    have hsep : (E : Set ℂ).Pairwise (fun z w => 1 ≤ |z.im - w.im|) := by
      intro z hz v hv hn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (show z ∈ E from hz)
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp (show v ∈ E from hv)
      obtain ⟨hjJ, hjP⟩ := Finset.mem_filter.mp hj
      obtain ⟨hlJ, hlP⟩ := Finset.mem_filter.mp hl
      have hij : j ≠ l := fun he => hn (congrArg r he)
      apply one_le_abs_sub_of_floor_same_parity
      · change k (r j) ≠ k (r l)
        rwa [(hr j hjJ).2, (hr l hlJ).2]
      · change k (r j) % 2 = k (r l) % 2
        rw [(hr j hjJ).2, (hr l hlJ).2]
        exact hpar j l hjP hlP
    have hcard : E.card = (J.filter P).card := Finset.card_image_iff.mpr
      (hri.mono (by simpa only [Finset.coe_subset] using Finset.filter_subset P J))
    rw [← hcard]
    exact hbound T hT σ hσ E (fun z hz => (Finset.mem_filter.mp (hsub hz)).1)
      (fun z hz => (Finset.mem_filter.mp (hsub hz)).2) hsep
  have hJ : (J.card : ℝ) ≤ 2 * V := by
    have h₀ := hrep p (fun j l hj hl => hj.trans hl.symm)
    have h₁ := hrep (fun j => ¬ p j) (by
      intro j l hj hl
      dsimp [p] at hj hl
      omega)
    have he := congrArg ((↑) : ℕ → ℝ) (Finset.card_filter_add_card_filter_not (s := J) p)
    push_cast at he
    linarith only [h₀, h₁, he]
  have hfib (j : ℤ) (hj' : j ∈ J) :
      ∑ z ∈ S.filter (fun z => k z = j), (multiplicity z : ℝ) ≤ 3 * C * log T := by
    have hsub : S.filter (fun z => k z = j) ⊆ (zerosUpTo T).filter
        (fun z => (j : ℝ) ≤ z.im ∧ z.im ≤ (j : ℝ) + 1) := by
      intro z hz
      obtain ⟨hzS, hzJ⟩ := Finset.mem_filter.mp hz
      have hz₀ := Int.floor_le z.im
      have hz₁ := Int.lt_floor_add_one z.im
      change ⌊z.im⌋ = j at hzJ
      rw [hzJ] at hz₀ hz₁
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzS).1, hz₀, hz₁.le⟩
    have hi := (mem_zerosUpTo.mp (Finset.mem_filter.mp (hr j hj').1).1).2.2.2
    have hh := (hr j hj').2
    change ⌊(r j).im⌋ = j at hh
    have hr₀ := Int.floor_le (r j).im
    have hr₁ := Int.lt_floor_add_one (r j).im
    rw [hh] at hr₀ hr₁
    have hjabs : |(j : ℝ)| ≤ T + 1 := abs_le.mpr (by
      obtain ⟨hlo, hhi⟩ := abs_le.mp hi
      constructor <;> linarith only [hlo, hhi, hr₀, hr₁])
    have hT₀ : 0 < T := by linarith only [hT]
    have hT2 : (4 : ℝ) ≤ T ^ (2 : ℕ) := by
      have hh := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hT 2
      norm_num at hh
      exact hh
    have hbase : |(j : ℝ)| + 2 ≤ T ^ (3 : ℕ) := by
      have hbig := mul_le_mul_of_nonneg_right hT2 hT₀.le
      nlinarith only [hjabs, hbig, hT]
    calc
      _ ≤ ∑ z ∈ (zerosUpTo T).filter (fun z => (j : ℝ) ≤ z.im ∧ z.im ≤ (j : ℝ) + 1),
          (multiplicity z : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => Nat.cast_nonneg (multiplicity z))
      _ ≤ C * log (|(j : ℝ)| + 2) := hunit T j
      _ ≤ _ := by
        have hlog := log_le_log (by positivity : (0 : ℝ) < |(j : ℝ)| + 2) hbase
        rw [log_pow, Nat.cast_ofNat] at hlog
        nlinarith only [mul_le_mul_of_nonneg_left hlog hC.le]
  have hS : (∑ z ∈ S, (multiplicity z : ℝ)) ≤ (J.card : ℝ) * (3 * C * log T) := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := J) (fun z hz => Finset.mem_image_of_mem k hz)
      (fun z => (multiplicity z : ℝ))]
    exact (Finset.sum_le_sum hfib).trans_eq (by simp [nsmul_eq_mul])
  change (∑ z ∈ S, (multiplicity z : ℝ)) ≤ _
  calc
    _ ≤ (J.card : ℝ) * (3 * C * log T) := hS
    _ ≤ (2 * V) * (3 * C * log T) := mul_le_mul_of_nonneg_right hJ
      (by have hz := log_nonneg (one_le_two.trans hT); positivity)
    _ = _ := by dsimp [V]; rw [pow_succ]; ring

private lemma rightDensity_of_separated (h : SeparatedDensityEstimate) : RightDensityEstimate :=
  rightDensity_of_separated_with h

private def SeparatedShellDensity (κ : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, ∀ᶠ H : ℝ in atTop, ∀ σ ∈ Set.Icc (7 / 12 : ℝ) 1,
    ∀ S : Finset ℂ, S ⊆ zerosUpTo (2 * H) → (∀ z ∈ S, H ≤ |z.im| ∧ σ ≤ z.re) →
      (↑S : Set ℂ).Pairwise (fun z w => 1 ≤ |z.im - w.im|) →
      (S.card : ℝ) ≤ A * log H ^ B * H ^ (κ * (1 - σ))

private lemma separatedDensity_of_shell {κ : ℝ} (hκ : 0 ≤ κ) (h : SeparatedShellDensity κ) :
    SeparatedDensityEstimateWith κ := by
  classical
  obtain ⟨A, hA, B, h⟩ := h
  obtain ⟨U, hU⟩ := eventually_atTop.mp h
  let V := max 2 U
  let C : ℝ := (zerosUpTo V).card
  have hV : 2 ≤ V := le_max_left _ _
  have hV0 : 0 < V := by linarith only [hV]
  have h₂ : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨C / log 2 ^ (B + 1) + 2 * A / log 2, by dsimp [C]; positivity, B + 1, ?_⟩
  intro T hT σ hσ S hS hRS hsep
  have hT0 : 0 < T := by linarith only [hT]
  have hlogT : log 2 ≤ log T := log_le_log (by norm_num) hT
  have hlogT0 : 0 < log T := h₂.trans_le hlogT
  have hE : 0 ≤ κ * (1 - σ) := mul_nonneg hκ (sub_nonneg.mpr hσ.2)
  let P := S.filter (fun z => |z.im| < V)
  let Q := S.filter (fun z => ¬ |z.im| < V)
  let J := ⌊log T / log 2⌋₊ + 1
  let f (z : ℂ) := Nat.log 2 ⌊|z.im| / V⌋₊
  let L (j : ℕ) : ℝ := V * (2 : ℝ) ^ j
  have hbin {z : ℂ} (hz : z ∈ Q) : L (f z) ≤ |z.im| ∧ |z.im| < 2 * L (f z) := by
    have hVle := le_of_not_gt (Finset.mem_filter.mp hz).2
    let n := ⌊|z.im| / V⌋₊
    have hN₀ : 0 < n := by
      have h₁ : (1 : ℝ) ≤ |z.im| / V := (le_div_iff₀ hV0).mpr (by simpa only [one_mul] using hVle)
      exact (Nat.le_floor_iff (by positivity : 0 ≤ |z.im| / V)).mpr (by simpa only [Nat.cast_one] using h₁)
    have hN₁ : ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hN₀.ne'
    have hN₂ : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n)
    have h₁ : (2 : ℝ) ^ f z ≤ |z.im| / V := hN₁.trans (Nat.floor_le (by positivity))
    have h₂' : |z.im| / V < (2 : ℝ) ^ (f z + 1) := (Nat.lt_floor_add_one _).trans_le hN₂
    refine ⟨?_, ?_⟩
    · dsimp [L]; rw [mul_comm V]
      exact (le_div_iff₀ hV0).mp h₁
    · have hh := (div_lt_iff₀ hV0).mp h₂'
      rw [pow_succ] at hh
      dsimp [L]
      exact hh.trans_eq (by ring)
  have hmaps (z : ℂ) (hz : z ∈ Q) : f z ∈ range J := by
    have hzT := (mem_zerosUpTo.mp (hS (Finset.mem_filter.mp hz).1)).2.2.2
    have hLT := (hbin hz).1.trans hzT
    have hpow : (2 : ℝ) ^ f z ≤ T :=
      (le_mul_of_one_le_left (by positivity) (by linarith only [hV] : 1 ≤ V)).trans hLT
    have hp := log_le_log (by positivity : 0 < (2 : ℝ) ^ f z) hpow
    rw [log_pow] at hp
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff (div_nonneg hlogT0.le h₂.le)).mpr ((le_div_iff₀ h₂).mpr hp))
  have hJ : (J : ℝ) ≤ (2 / log 2) * log T := by
    have hf := Nat.floor_le (div_nonneg hlogT0.le h₂.le)
    have hd : 1 ≤ log T / log 2 := (le_div_iff₀ h₂).mpr (by simpa only [one_mul] using hlogT)
    dsimp [J]
    push_cast
    calc
      _ ≤ 2 * (log T / log 2) := by linarith only [hf, hd]
      _ = _ := by ring
  have hQcard : (Q.card : ℝ) ≤ (J : ℝ) * (A * log T ^ B * T ^ (κ * (1 - σ))) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := range J) (fun z hz => hmaps z hz), Nat.cast_sum]
    calc
      _ ≤ ∑ _j ∈ range J, A * log T ^ B * T ^ (κ * (1 - σ)) := by
        apply Finset.sum_le_sum
        intro j _
        let W := Q.filter (fun z => f z = j)
        change (W.card : ℝ) ≤ _
        by_cases he : W.Nonempty
        · obtain ⟨w, hw⟩ := he
          have hwQ := (Finset.mem_filter.mp hw).1
          have hLjT : L j ≤ T := by
            rw [← (Finset.mem_filter.mp hw).2]
            exact (hbin hwQ).1.trans (mem_zerosUpTo.mp (hS (Finset.mem_filter.mp hwQ).1)).2.2.2
          have hL : V ≤ L j := le_mul_of_one_le_right hV0.le (one_le_pow₀ (by norm_num))
          have hWL : W ⊆ zerosUpTo (2 * L j) := by
            intro z hz
            obtain ⟨hzQ, hfj⟩ := Finset.mem_filter.mp hz
            obtain ⟨hz₁, hz₂, hz₃, _⟩ := mem_zerosUpTo.mp (hS (Finset.mem_filter.mp hzQ).1)
            have hi := (hbin hzQ).2
            rw [hfj] at hi
            exact mem_zerosUpTo.mpr ⟨hz₁, hz₂, hz₃, hi.le⟩
          have hW (z : ℂ) (hz : z ∈ W) : L j ≤ |z.im| ∧ σ ≤ z.re := by
            obtain ⟨hzQ, hfj⟩ := Finset.mem_filter.mp hz
            exact ⟨hfj ▸ (hbin hzQ).1, hRS z (Finset.mem_filter.mp hzQ).1⟩
          have hWsub : W ⊆ S := fun z hz => (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
          apply (hU (L j) ((le_max_right _ _).trans hL) σ hσ W hWL hW
            (hsep.mono (show (W : Set ℂ) ⊆ S from hWsub))).trans
          have hpos : 0 < L j := hV0.trans_le hL
          have hlogLj : 0 ≤ log (L j) := log_nonneg ((by linarith only [hV] : 1 ≤ V).trans hL)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogLj (log_le_log hpos hLjT) B) hA.le)
            (rpow_le_rpow hpos.le hLjT hE) (rpow_nonneg hpos.le _) (by positivity)
        · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty, Nat.cast_zero]
          positivity
      _ = _ := by simp [nsmul_eq_mul]
  have hPcard : (P.card : ℝ) ≤ C := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzS, hi⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁,h₂,h₃,_⟩ := mem_zerosUpTo.mp (hS hzS)
    exact mem_zerosUpTo.mpr ⟨h₁,h₂,h₃,hi.le⟩
  have hsmall : C ≤ (C / log 2 ^ (B + 1)) * log T ^ (B + 1) * T ^ (κ * (1 - σ)) := by
    have hC : 0 ≤ C := Nat.cast_nonneg _
    have hl := pow_le_pow_left₀ h₂.le hlogT (B + 1)
    have hrp := one_le_rpow (show 1 ≤ T by linarith only [hT]) hE
    calc
      _ = (C / log 2 ^ (B + 1)) * log 2 ^ (B + 1) := by field_simp
      _ ≤ (C / log 2 ^ (B + 1)) * log T ^ (B + 1) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hrp
  have hbig : (Q.card : ℝ) ≤ (2 * A / log 2) * log T ^ (B + 1) * T ^ (κ * (1 - σ)) := by
    apply hQcard.trans
    apply (mul_le_mul_of_nonneg_right hJ (by positivity)).trans_eq
    rw [pow_succ]
    ring
  have hparts := congrArg ((↑) : ℕ → ℝ)
    (Finset.card_filter_add_card_filter_not (s := S) (fun z : ℂ => |z.im| < V))
  change ((P.card + Q.card : ℕ) : ℝ) = S.card at hparts
  rw [Nat.cast_add] at hparts
  rw [← hparts]
  exact (add_le_add (hPcard.trans hsmall) hbig).trans_eq (by ring)

open scoped Classical in
private lemma zeros_height_increment :
    ∃ C : ℝ, 0 < C ∧ ∀ T ≥ (0 : ℝ), ∀ H ≤ T + 1,
      ∑ z ∈ (zerosUpTo H).filter (fun z => T < |z.im|), (multiplicity z : ℝ) ≤ C * log (T + 2) := by
  classical
  obtain ⟨C, hC, hunit⟩ := all_zeros_unit_count
  refine ⟨3 * C, by positivity, fun T hT H hH => ?_⟩
  let U := (zerosUpTo H).filter (fun z => T < |z.im|)
  let Upos := U.filter (fun z => 0 ≤ z.im)
  let Uneg := U.filter (fun z => ¬ 0 ≤ z.im)
  have hsubPos : Upos ⊆ (zerosUpTo H).filter (fun z => T ≤ z.im ∧ z.im ≤ T + 1) := by
    intro z hz
    obtain ⟨hzU, him⟩ := mem_filter.mp hz
    obtain ⟨hzH, habs⟩ := mem_filter.mp hzU
    have hu := (mem_zerosUpTo.mp hzH).2.2.2.trans hH
    rw [abs_of_nonneg him] at habs hu
    exact mem_filter.mpr ⟨hzH, habs.le, hu⟩
  have hsubNeg : Uneg ⊆ (zerosUpTo H).filter (fun z => -T - 1 ≤ z.im ∧ z.im ≤ (-T - 1) + 1) := by
    intro z hz
    obtain ⟨hzU, him⟩ := mem_filter.mp hz
    obtain ⟨hzH, habs⟩ := mem_filter.mp hzU
    have hu := (mem_zerosUpTo.mp hzH).2.2.2.trans hH
    rw [abs_of_neg (lt_of_not_ge him)] at habs hu
    exact mem_filter.mpr ⟨hzH, by linarith only [hu], by linarith only [habs]⟩
  have hPos := (sum_le_sum_of_subset_of_nonneg hsubPos
    (fun z _ _ => Nat.cast_nonneg (α := ℝ) (multiplicity z))).trans (hunit H T)
  have hNeg := (sum_le_sum_of_subset_of_nonneg hsubNeg
    (fun z _ _ => Nat.cast_nonneg (α := ℝ) (multiplicity z))).trans (hunit H (-T - 1))
  have hlog := mul_le_mul_of_nonneg_left (log_add_two_neg_sub_one_le T) hC.le
  rw [abs_of_nonneg hT] at hPos hlog
  have hpart : (∑ z ∈ Upos, (multiplicity z : ℝ)) + ∑ z ∈ Uneg, (multiplicity z : ℝ) =
      ∑ z ∈ U, (multiplicity z : ℝ) := sum_filter_add_sum_filter_not _ _ _
  change (∑ z ∈ U, (multiplicity z : ℝ)) ≤ _
  rw [← hpart]
  linarith only [hPos, hNeg, hlog]

private lemma zeroSum_height_increment :
    ∃ C : ℝ, 0 < C ∧ ∀ T H q : ℝ, 0 < T → T ≤ H → H ≤ T + 1 → 1 ≤ q →
      ‖zeroSum H q - zeroSum T q‖ ≤ C * (q / T) * log (T + 2) := by
  classical
  obtain ⟨C, hC, hcount⟩ := zeros_height_increment
  refine ⟨C, hC, fun T H q hT hTH hHT hq => ?_⟩
  let w (z : ℂ) := (multiplicity z : ℂ) * ((q : ℂ) ^ z / z)
  have hf : (zerosUpTo H).filter (fun z => |z.im| ≤ T) = zerosUpTo T := by
    ext z
    simp only [mem_filter, mem_zerosUpTo]
    constructor
    · rintro ⟨⟨hz, h0, h1, _⟩, ht⟩
      exact ⟨hz, h0, h1, ht⟩
    · rintro ⟨hz, h0, h1, ht⟩
      exact ⟨⟨hz, h0, h1, ht.trans hTH⟩, ht⟩
  have he : zeroSum H q - zeroSum T q =
      ∑ z ∈ (zerosUpTo H).filter (fun z => T < |z.im|), w z := by
    have hp := sum_filter_add_sum_filter_not (s := zerosUpTo H) (fun z => |z.im| ≤ T) w
    simp only [hf, not_le] at hp
    unfold zeroSum
    change (∑ z ∈ zerosUpTo H, w z) - ∑ z ∈ zerosUpTo T, w z = _
    rw [← hp, add_sub_cancel_left]
  rw [he]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ z ∈ (zerosUpTo H).filter (fun z => T < |z.im|), (multiplicity z : ℝ) * (q / T) := by
      refine sum_le_sum fun z hz => ?_
      obtain ⟨hzH, him⟩ := mem_filter.mp hz
      have hre := (mem_zerosUpTo.mp hzH).2.2.1
      have hzT : T ≤ ‖z‖ := him.le.trans (Complex.abs_im_le_norm z)
      unfold w
      rw [norm_mul, Complex.norm_natCast, norm_div,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hq)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hpow := (rpow_le_rpow_of_exponent_le hq hre.le).trans_eq (rpow_one q)
      exact div_le_div₀ (zero_le_one.trans hq) hpow hT hzT
    _ ≤ (C * log (T + 2)) * (q / T) := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (hcount T hT.le H hHT) (by positivity)
    _ = _ := by ring

-- The contour may be shifted to a height within one unit of the truncation.
private def SelectedHeightFormula : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℝ in atTop,
    ∃ H ∈ Set.Icc (height x) (height x + 1),
      ∀ n : ℕ, (n : ℝ) + 1 / 2 ∈ Set.Icc (x - 1) (x + gap x + 1) →
        ‖((psi ((n : ℝ) + 1 / 2) - ((n : ℝ) + 1 / 2) : ℝ) : ℂ) +
          zeroSum H ((n : ℝ) + 1 / 2)‖ ≤ A * (x ^ (13 / 20 : ℝ) * log x ^ (2 : ℕ))

private lemma halfIntegerFormula_of_selectedHeight (hf : SelectedHeightFormula) : HalfIntegerFormula := by
  obtain ⟨A, hA, hformula⟩ := hf
  obtain ⟨C, hC, hinc⟩ := zeroSum_height_increment
  refine ⟨A + 3 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ), tendsto_log_atTop.eventually_ge_atTop 1, hformula]
    with x hx hlog hxF
  obtain ⟨H, hH, hformula⟩ := hxF
  intro n hn
  let q := (n : ℝ) + 1 / 2
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hT0 : 0 < height x := rpow_pos_of_pos hx0 _
  have hq : 1 ≤ q := by linarith only [show x - 1 ≤ q from hn.1, hx]
  have hgap : gap x ≤ x :=
    (rpow_le_rpow_of_exponent_le hx1 (by norm_num : (2 / 3 : ℝ) ≤ 1)).trans_eq (rpow_one x)
  have hqle : q ≤ 3 * x := by linarith only [show q ≤ x + gap x + 1 from hn.2, hgap, hx]
  have hheight : height x ≤ sqrt x := by
    rw [sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hsqrt : sqrt x ≤ x / 2 := by
    apply (sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [mul_nonneg hx0.le (show 0 ≤ x - 4 by linarith only [hx])]
  have hlogs : log (height x + 2) ≤ log x ^ (2 : ℕ) := by
    have h := log_le_log (by positivity : 0 < height x + 2)
      (show height x + 2 ≤ x by linarith only [hheight, hsqrt, hx])
    nlinarith only [h, hlog, sq_nonneg (log x - 1)]
  have hqdiv : q / height x ≤ 3 * x ^ (13 / 20 : ℝ) := by
    have hdiv : x / height x = x ^ (13 / 20 : ℝ) := by
      calc
        _ = x ^ (1 : ℝ) / x ^ (7 / 20 : ℝ) := by rw [rpow_one, height]
        _ = _ := by rw [← rpow_sub hx0]; norm_num
    calc
      _ ≤ (3 * x) / height x := div_le_div_of_nonneg_right hqle hT0.le
      _ = _ := by rw [mul_div_assoc, hdiv]
  let E := x ^ (13 / 20 : ℝ) * log x ^ (2 : ℕ)
  have hdiff : ‖zeroSum (height x) q - zeroSum H q‖ ≤ (3 * C) * E := by
    rw [norm_sub_rev]
    apply (hinc (height x) H q hT0 hH.1 hH.2 hq).trans
    dsimp [E]
    calc
      _ ≤ C * (3 * x ^ (13 / 20 : ℝ)) * log x ^ (2 : ℕ) := by
        have hnonneg : 0 ≤ log (height x + 2) := log_nonneg (by linarith only [hT0])
        gcongr
      _ = _ := by ring
  change ‖((psi q - q : ℝ) : ℂ) + zeroSum (height x) q‖ ≤ _
  have he : ((psi q - q : ℝ) : ℂ) + zeroSum (height x) q =
      (((psi q - q : ℝ) : ℂ) + zeroSum H q) + (zeroSum (height x) q - zeroSum H q) := by ring
  rw [he]
  have hh : ‖((psi q - q : ℝ) : ℂ) + zeroSum H q‖ ≤ A * E := hformula n hn
  linarith only [norm_add_le (((psi q - q : ℝ) : ℂ) + zeroSum H q)
    (zeroSum (height x) q - zeroSum H q), hh, hdiff]

private lemma multiplicity_pos_of_mem_zerosUpTo {T : ℝ} {z : ℂ} (hz : z ∈ zerosUpTo T) :
    0 < multiplicity z := by
  obtain ⟨hζ, _, hzre, _⟩ := mem_zerosUpTo.mp hz
  have hz1 : z ≠ 1 := by rintro rfl; simp at hzre
  rw [← multiplicity_zeta₁ hz1]
  have ha : AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
    fun w _ => differentiable_riemannZeta₁.analyticAt w
  have hone : analyticOrderAt riemannZeta₁ 1 = 0 :=
    (ha 1 trivial).analyticOrderAt_eq_zero.mpr (by rw [riemannZeta₁_one]; norm_num)
  have htop : analyticOrderAt riemannZeta₁ z ≠ ⊤ :=
    ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial (by rw [hone]; simp)
  have hζ₁ : riemannZeta₁ z = 0 := by
    have heq := riemannZeta_eq_inv_sub_mul hz1
    rw [hζ, eq_comm, mul_eq_zero] at heq
    exact heq.resolve_left (inv_ne_zero (sub_ne_zero.mpr hz1))
  have hne : analyticOrderAt riemannZeta₁ z ≠ 0 := by
    intro h
    exact ((ha z trivial).analyticOrderAt_eq_zero.mp h) hζ₁
  unfold analyticOrderNatAt
  cases h : analyticOrderAt riemannZeta₁ z using ENat.recTopCoe with
  | top => exact (htop h).elim
  | coe n =>
    rw [ENat.toNat_natCast]
    exact Nat.pos_of_ne_zero (fun h' => hne (by simp [h, h']))

open scoped Classical in
private lemma zeros_near_height_count :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T ≥ 3,
      (((zerosUpTo (T + 2)).filter (fun z => T - 1 ≤ z.im ∧ z.im ≤ T + 2)).card : ℝ) ≤
        C * log (T + 3) := by
  classical
  obtain ⟨C, hC, hunit⟩ := all_zeros_unit_count
  refine ⟨max 1 (3 * C), le_max_left _ _, fun T hT => ?_⟩
  let s := zerosUpTo (T + 2)
  let S := s.filter (fun z => T - 1 ≤ z.im ∧ z.im ≤ T + 2)
  let w (z : ℂ) : ℝ := multiplicity z
  let f (t : ℝ) (z : ℂ) : ℝ := if t ≤ z.im ∧ z.im ≤ t + 1 then w z else 0
  have hc (t : ℝ) (ht : 0 ≤ t) (htt : t ≤ T + 1) : ∑ z ∈ s, f t z ≤ C * log (T + 3) := by
    simp only [f, ← sum_filter]
    refine (hunit (T + 2) t).trans (mul_le_mul_of_nonneg_left (log_le_log (by positivity) ?_) hC.le)
    rw [abs_of_nonneg ht]
    linarith only [htt]
  have hS : ∑ z ∈ S, w z ≤ ∑ z ∈ s, (f (T - 1) z + f T z + f (T + 1) z) := by
    rw [sum_filter]
    refine sum_le_sum fun z hz => ?_
    have hw : 0 ≤ w z := Nat.cast_nonneg _
    dsimp [f]
    by_cases hz' : T - 1 ≤ z.im ∧ z.im ≤ T + 2
    · rw [if_pos hz']
      by_cases h₁ : z.im ≤ T
      · rw [if_pos (show T - 1 ≤ z.im ∧ z.im ≤ T - 1 + 1 from ⟨hz'.1, by linarith only [h₁]⟩)]
        split_ifs <;> linarith only [hw]
      · by_cases h₂ : z.im ≤ T + 1
        · rw [if_pos (show T ≤ z.im ∧ z.im ≤ T + 1 from ⟨le_of_not_ge h₁, h₂⟩)]
          split_ifs <;> linarith only [hw]
        · rw [if_pos (show T + 1 ≤ z.im ∧ z.im ≤ T + 1 + 1 from
            ⟨le_of_not_ge h₂, by linarith only [hz'.2]⟩)]
          split_ifs <;> linarith only [hw]
    · rw [if_neg hz']
      split_ifs <;> linarith only [hw]
  have hc' : ((S.card : ℕ) : ℝ) ≤ ∑ z ∈ S, w z := by
    calc
      _ = ∑ z ∈ S, (1 : ℝ) := by simp [nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun z hz => by
        change (1 : ℝ) ≤ (multiplicity z : ℝ)
        exact_mod_cast (Nat.succ_le_of_lt (multiplicity_pos_of_mem_zerosUpTo (mem_filter.mp hz).1))
  change ((S.card : ℕ) : ℝ) ≤ _
  refine hc'.trans (hS.trans ?_)
  rw [sum_add_distrib, sum_add_distrib]
  have hlog := log_nonneg (show 1 ≤ T + 3 by linarith only [hT])
  calc
    _ ≤ 3 * C * log (T + 3) := by
      linarith only [hc (T - 1) (by linarith only [hT]) (by linarith),
        hc T (by linarith only [hT]) (by linarith),
        hc (T + 1) (by linarith only [hT]) le_rfl]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hlog

private def HeightSeparated (c T H : ℝ) : Prop :=
  ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 → c / log (T + 3) ≤ |H - z.im|

open MeasureTheory in
private lemma exists_separated_height :
    ∃ c : ℝ, 0 < c ∧ ∀ T ≥ 3, ∃ H ∈ Set.Icc T (T + 1), HeightSeparated c T H := by
  classical
  obtain ⟨C, hC, hcount⟩ := zeros_near_height_count
  let c := 1 / (8 * C)
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, fun T hT => ?_⟩
  let δ := c / log (T + 3)
  have hlog : 1 ≤ log (T + 3) := by
    have hh := log_le_log (exp_pos 1)
      (exp_one_lt_three.le.trans (show (3 : ℝ) ≤ T + 3 by linarith only [hT]))
    rw [log_exp] at hh
    exact hh
  have hlog0 : 0 < log (T + 3) := zero_lt_one.trans_le hlog
  have hδ : 0 < δ := div_pos hc hlog0
  have hδ1 : δ < 1 := by
    have hc8 : c ≤ 1 / 8 := div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith only [hC])
    exact (div_lt_iff₀ hlog0).mpr (by linarith only [hc8, hlog])
  let S := (zerosUpTo (T + 2)).filter (fun z => T - 1 ≤ z.im ∧ z.im ≤ T + 2)
  let J (z : ℂ) : Set ℝ := Set.Ioo (z.im - δ) (z.im + δ)
  have hmeasure : volume (⋃ z ∈ S, J z) < 1 := by
    apply (measure_biUnion_finset_le (μ := volume) S J).trans_lt
    have hJ (z : ℂ) : volume (J z) = ENNReal.ofReal (2 * δ) := by
      dsimp [J]
      rw [Real.volume_Ioo]
      congr 1
      ring
    simp only [hJ, sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast S.card,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) S.card), ← ENNReal.ofReal_one]
    apply (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr
    have ht : ((S.card : ℕ) : ℝ) * (2 * δ) ≤ 1 / 4 := by
      calc
        _ ≤ (C * log (T + 3)) * (2 * δ) := mul_le_mul_of_nonneg_right (hcount T hT) (by positivity)
        _ = _ := by dsimp [δ, c]; field_simp; ring
    linarith only [ht]
  have hout : ∃ H ∈ Set.Icc T (T + 1), H ∉ ⋃ z ∈ S, J z := by
    by_contra! h
    have hm := measure_mono (μ := volume) (show Set.Icc T (T + 1) ⊆ ⋃ z ∈ S, J z from h)
    rw [Real.volume_Icc, show T + 1 - T = 1 by ring, ENNReal.ofReal_one] at hm
    exact hmeasure.not_ge hm
  obtain ⟨H, hH, hout⟩ := hout
  refine ⟨H, hH, fun z hz hlo hhi => ?_⟩
  change δ ≤ |H - z.im|
  by_contra! hclose
  have hbound := abs_lt.mp hclose
  have hlow : T - 1 ≤ z.im := by linarith only [hbound.2, hH.1, hδ1]
  have hupp : z.im ≤ T + 2 := by linarith only [hbound.1, hH.2, hδ1]
  have him : 0 ≤ z.im := by linarith only [hlow, hT]
  have hmem : z ∈ S := mem_filter.mpr
    ⟨mem_zerosUpTo.mpr ⟨hz, hlo, hhi, by rw [abs_of_nonneg him]; exact hupp⟩, hlow, hupp⟩
  apply hout
  exact Set.mem_iUnion₂.mpr ⟨z, hmem,
    ⟨by linarith only [hbound.1], by linarith only [hbound.2]⟩⟩

-- At a height separated from all zeta zeros, the two horizontal contour integrals can be bounded.
private def SeparatedContourFormula : Prop :=
  ∀ c : ℝ, 0 < c → ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℝ in atTop,
    ∀ H ∈ Set.Icc (height x) (height x + 1), HeightSeparated c (height x) H →
      ∀ n : ℕ, (n : ℝ) + 1 / 2 ∈ Set.Icc (x - 1) (x + gap x + 1) →
        ‖((psi ((n : ℝ) + 1 / 2) - ((n : ℝ) + 1 / 2) : ℝ) : ℂ) +
          zeroSum H ((n : ℝ) + 1 / 2)‖ ≤ A * (x ^ (13 / 20 : ℝ) * log x ^ (2 : ℕ))

private lemma selectedHeightFormula_of_separatedContour (hf : SeparatedContourFormula) : SelectedHeightFormula := by
  obtain ⟨c, hc, hsep⟩ := exists_separated_height
  obtain ⟨A, hA, hformula⟩ := hf c hc
  refine ⟨A, hA, ?_⟩
  have ht : Tendsto height atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [ht.eventually_ge_atTop 3, hformula] with x hx hform
  obtain ⟨H, hH, hgood⟩ := hsep (height x) hx
  exact ⟨H, hH, hform H hH hgood⟩

open Metric

private lemma exists_logPrimitive_relative {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hnz : ∀ z ∈ ball 0 R, f z ≠ 0)
    (hbound : ∀ z ∈ ball 0 R, ‖f z‖ ≤ M) :
    ∃ F : ℂ → ℂ, F 0 = 0 ∧ (∀ z ∈ ball 0 R, HasDerivAt F (deriv f z / f z) z) ∧
      0 < log M - log ‖f 0‖ + 1 ∧
      Set.MapsTo F (ball 0 R) {z | z.re ≤ log M - log ‖f 0‖ + 1} := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball 0 R) :=
    (hf.differentiableOn.deriv isOpen_ball).div hf.differentiableOn hnz
  obtain ⟨F, hF0, hF⟩ := hd.isExactOn_ball.with_val_at 0 0
  let g (z : ℂ) := f z * Complex.exp (-F z)
  have hG (z : ℂ) (hz : z ∈ ball 0 R) : HasDerivWithinAt g 0 (ball 0 R) z := by
    have hf' := (hf z hz).differentiableAt.hasDerivAt
    have he : HasDerivAt (fun w => Complex.exp (-F w))
        (Complex.exp (-F z) * -(deriv f z / f z)) z := (hF z hz).neg.cexp
    have h : HasDerivAt g (deriv f z * Complex.exp (-F z) +
        f z * (Complex.exp (-F z) * -(deriv f z / f z))) z := hf'.mul he
    have heq : deriv f z * Complex.exp (-F z) +
        f z * (Complex.exp (-F z) * -(deriv f z / f z)) = 0 := by
      field_simp [hnz z hz]
      ring
    rw [heq] at h
    exact h.hasDerivWithinAt
  have hg (z : ℂ) (hz : z ∈ ball 0 R) : g z = g 0 := by
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun _ => 0) hG (C := 0) (by simp) (convex_ball 0 R) h0 hz
    have hzero : ‖g z - g 0‖ = 0 := le_antisymm (by simpa using he) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  let B := log M - log ‖f 0‖ + 1
  have hnorm0 : 0 < ‖f 0‖ := norm_pos_iff.mpr (hnz 0 h0)
  have hB : 0 < B := by
    have h := log_le_log hnorm0 (hbound 0 h0)
    dsimp [B]
    linarith only [h]
  have hRe : Set.MapsTo F (ball 0 R) {z | z.re ≤ B} := by
    intro z hz
    have h := congrArg norm (hg z hz)
    change ‖f z * Complex.exp (-F z)‖ = ‖f 0 * Complex.exp (-F 0)‖ at h
    rw [hF0, neg_zero, Complex.exp_zero, mul_one, norm_mul, Complex.norm_exp, Complex.neg_re] at h
    have hfnorm : 0 < ‖f z‖ := norm_pos_iff.mpr (hnz z hz)
    have he := congrArg log h
    rw [Real.log_mul hfnorm.ne' (exp_pos _).ne', log_exp] at he
    have hle := log_le_log hfnorm (hbound z hz)
    change (F z).re ≤ B
    dsimp [B]
    linarith only [he, hle]
  exact ⟨F, hF0, hF, hB, hRe⟩

private lemma norm_logDeriv_le_of_ball {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (_hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hnz : ∀ z ∈ ball 0 R, f z ≠ 0)
    (hbound : ∀ z ∈ ball 0 R, ‖f z‖ ≤ M) :
    ‖deriv f 0 / f 0‖ ≤ 4 * (log M - log ‖f 0‖ + 1) / R := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  obtain ⟨F, hF0, hF, hB, hRe⟩ := exists_logPrimitive_relative hR hf hnz hbound
  let B := log M - log ‖f 0‖ + 1
  have hdiff : DifferentiableOn ℂ F (ball 0 R) :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have hhalf : 0 < R / 2 := by positivity
  have hdc : DiffContOnCl ℂ F (ball 0 (R / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hhalf.ne']
    exact hdiff.mono (closedBall_subset_ball (by linarith only [hR]))
  have hsphere (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (R / 2)) : ‖F z‖ ≤ 2 * B := by
    have hzNorm : ‖z‖ = R / 2 := by simpa [dist_eq_norm] using hz
    have hzb : z ∈ ball 0 R := mem_ball_zero_iff.mpr (by rw [hzNorm]; linarith only [hR])
    apply (Complex.borelCaratheodory_zero hB hdiff hRe hR hzb hF0).trans
    rw [hzNorm]
    have hden : R - R / 2 = R / 2 := by ring
    rw [hden, mul_div_cancel_right₀ _ hhalf.ne']
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hhalf hdc hsphere
  rw [(hF 0 h0).deriv] at hb
  exact hb.trans_eq (by dsimp [B]; ring)

private lemma norm_logDeriv_le_on_inner_ball {f : ℂ → ℂ} {R M : ℝ}
    (hRlo : (31 / 16 : ℝ) ≤ R) (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hnz : ∀ z ∈ ball 0 R, f z ≠ 0) (hbound : ∀ z ∈ ball 0 R, ‖f z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ 15 / 8) : ‖logDeriv f z‖ ≤ 4096 * (log M - log ‖f 0‖ + 1) := by
  have hR : 0 < R := by linarith only [hRlo]
  obtain ⟨F, hF0, hF, hB, hRe⟩ := exists_logPrimitive_relative hR hf hnz hbound
  let ρ : ℝ := 1 / 32
  have hρ : 0 < ρ := by norm_num [ρ]
  have hdiff : DifferentiableOn ℂ F (ball 0 R) := fun w hw =>
    (hF w hw).differentiableAt.differentiableWithinAt
  have hins {w : ℂ} (hw : w ∈ closedBall z ρ) : ‖w‖ ≤ 61 / 32 := by
    have hnorm := mem_closedBall.mp hw
    rw [dist_eq_norm] at hnorm
    calc
      ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ 61 / 32 := by dsimp [ρ] at hnorm; linarith only [hnorm, hz]
  have hb {w : ℂ} (hw : w ∈ closedBall z ρ) : w ∈ ball 0 R :=
    mem_ball_zero_iff.mpr (by linarith only [hins hw, hRlo])
  have hdc : DiffContOnCl ℂ F (ball z ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hρ.ne']
    exact hdiff.mono (fun _ hw => hb hw)
  let B := log M - log ‖f 0‖ + 1
  have hFbound (w : ℂ) (hw : w ∈ sphere z ρ) : ‖F w‖ ≤ 128 * B := by
    have hwc := sphere_subset_closedBall hw
    apply (Complex.borelCaratheodory_zero hB hdiff hRe hR (hb hwc) hF0).trans
    have hbound₁ : 2 * B * ‖w‖ ≤ 4 * B := by
      have h := mul_le_mul_of_nonneg_left (show ‖w‖ ≤ 2 by linarith only [hins hwc])
        (show 0 ≤ 2 * B by positivity)
      linarith only [h]
    have hbound₂ : (1 / 32 : ℝ) ≤ R - ‖w‖ := by linarith only [hRlo, hins hwc]
    calc
      2 * B * ‖w‖ / (R - ‖w‖) ≤ (4 * B) / (1 / 32 : ℝ) :=
        div_le_div₀ (by positivity) hbound₁ (by norm_num) hbound₂
      _ = _ := by ring
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc hFbound
  rw [(hF z (mem_ball_zero_iff.mpr (by linarith only [hz, hRlo]))).deriv] at hd
  change ‖logDeriv f z‖ ≤ (128 * B) / ρ at hd
  exact hd.trans_eq (by dsimp [B, ρ]; ring)

private lemma canonicalFactor_logDeriv_at_zero {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ≠ 0) :
    logDeriv (Complex.canonicalFactor R w) 0 =
      w⁻¹ - (starRingEnd ℂ w) / ((R : ℂ) ^ (2 : ℕ)) := by
  let a (z : ℂ) := (R : ℂ) ^ (2 : ℕ) - starRingEnd ℂ w * z
  let b (z : ℂ) := (R : ℂ) * (z - w)
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have ha : HasDerivAt a (-(starRingEnd ℂ w)) 0 := by
    simpa [a] using (((hasDerivAt_id (0 : ℂ)).const_mul (starRingEnd ℂ w)).const_sub ((R : ℂ)^2))
  have hb : HasDerivAt b (R : ℂ) 0 := by
    simpa [b] using (((hasDerivAt_id (0 : ℂ)).sub_const w).const_mul (R : ℂ))
  rw [show Complex.canonicalFactor R w = fun z => a z / b z by rfl,
    logDeriv_div _ (by simp [a, hR']) (by simp [b, hR', hw])
      ha.differentiableAt hb.differentiableAt, logDeriv_apply, logDeriv_apply, ha.deriv, hb.deriv]
  simp [a, b]
  field_simp [hR', hw]
  ring

private lemma canonicalFactor_logDeriv_re {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ≠ 0) :
    (logDeriv (Complex.canonicalFactor R w) 0).re =
      w.re / ‖w‖ ^ (2 : ℕ) - w.re / R ^ (2 : ℕ) := by
  rw [canonicalFactor_logDeriv_at_zero hR hw, Complex.sub_re, Complex.inv_re, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_pow, Complex.div_ofReal_re, Complex.conj_re]

private lemma canonicalFactor_logDeriv_re_nonpos {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw : w ≠ 0) (hball : w ∈ Metric.ball 0 R) (hreal : w.re ≤ 0) :
    (logDeriv (Complex.canonicalFactor R w) 0).re ≤ 0 := by
  rw [canonicalFactor_logDeriv_re hR hw]
  apply sub_nonpos.mpr
  have hn := (mem_ball_zero_iff.mp hball).le
  have hw₂ : 0 < ‖w‖ ^ (2 : ℕ) := pow_pos (norm_pos_iff.mpr hw) _
  have hR₂ : 0 < R ^ (2 : ℕ) := pow_pos hR _
  refine (div_le_div_iff₀ hw₂ hR₂).mpr ?_
  exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hreal

private lemma canonicalFactor_logDeriv_re_aligned {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hball : w ∈ Metric.ball 0 R) (him : w.im = 0) (hreal : w.re < 0) :
    (logDeriv (Complex.canonicalFactor R w) 0).re ≤ R⁻¹ - (-w.re)⁻¹ := by
  have hw : w ≠ 0 := by
    intro h
    simp [h] at hreal
  have hcast : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [him])
  have hnorm : ‖w‖ = -w.re := by
    nth_rw 1 [← hcast]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hreal]
  rw [canonicalFactor_logDeriv_re hR hw, hnorm]
  have hd : -w.re ≤ R := by rw [← hnorm]; exact (mem_ball_zero_iff.mp hball).le
  have hq : (-w.re) / R ^ (2 : ℕ) ≤ R⁻¹ := by
    calc
      _ ≤ R / R ^ (2 : ℕ) := div_le_div_of_nonneg_right hd (by positivity)
      _ = _ := by field_simp
  have he : w.re / (-w.re) ^ (2 : ℕ) = -(-w.re)⁻¹ := by
    field_simp [hreal.ne]
  rw [he]
  linarith only [hq, show (-w.re) / R ^ (2 : ℕ) = -(w.re / R ^ (2 : ℕ)) by ring]

open Metric in
private lemma disk_logDeriv_data {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 R, f z ≠ 0 ∧ ‖f z‖ ≤ M) :
    ∃ (g : ℂ → ℂ) (Z : Finset ℂ),
      (∀ w, w ∈ Z ↔ MeromorphicOn.divisor f (ball 0 R) w ≠ 0) ∧
      (∀ w ∈ Z, w ∈ ball 0 R ∧ f w = 0) ∧
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ w ∈ closedBall 0 R, g w ≠ 0) ∧
      (∀ w ∈ ball 0 R, ‖g w‖ ≤ M) ∧ log ‖f 0‖ ≤ log ‖g 0‖ ∧
      (∀ x ∈ ball 0 R, f x ≠ 0 → logDeriv g x =
        (∑ w ∈ Z, (MeromorphicOn.divisor f (ball 0 R) w : ℂ) *
          logDeriv (Complex.canonicalFactor R w) x) + logDeriv f x) := by
  classical
  let U := closedBall (0 : ℂ) R
  let V := ball (0 : ℂ) R
  have hU0 : (0 : ℂ) ∈ U := mem_closedBall_self hR.le
  have hfin (z : ℂ) (hz : z ∈ U) : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall 0 R).isPreconnected hU0 hz
      (by rw [(hf 0 hU0).analyticOrderAt_eq_zero.mpr hf0]; simp)
  have hfm (z : ℂ) (hz : z ∈ U) : meromorphicOrderAt f z ≠ ⊤ := by
    rw [(hf z hz).meromorphicOrderAt_eq]
    rcases ENat.ne_top_iff_exists.mp (hfin z hz) with ⟨n, hn⟩
    rw [← hn]
    simp
  have hmzero (z : ℂ) (hz : z ∈ U) (hne : f z ≠ 0) : meromorphicOrderAt f z = 0 := by
    rw [(hf z hz).meromorphicOrderAt_eq, (hf z hz).analyticOrderAt_eq_zero.mpr hne]
    simp
  obtain ⟨g, gD⟩ := hf.meromorphicOn.exists_ecanonicalDecomp (fun z => hfm z z.prop)
  let D := MeromorphicOn.divisor f V
  let Z := (hf.meromorphicOn.divisor_ball_support_finite (R := R)).toFinset
  have hZ (w : ℂ) : w ∈ Z ↔ D w ≠ 0 := Set.Finite.mem_toFinset _
  have hD0 (z : ℂ) : 0 ≤ D z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (hf.mono ball_subset_closedBall) z
  have hDb : MeromorphicOn.divisor f (sphere 0 R) = 0 := by
    ext z
    by_cases hz : z ∈ sphere 0 R
    · have ha := hf z (sphere_subset_closedBall hz)
      rw [hf.meromorphicOn.mono_set sphere_subset_closedBall |>.divisor_apply hz,
        hmzero z (sphere_subset_closedBall hz) (hboundary z hz).1]
      simp
    · simpa using Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
        (MeromorphicOn.divisor f (sphere 0 R)) hz
  have hDmem (w : ℂ) (hw : w ∈ Z) : w ∈ V ∧ f w = 0 := by
    have hh := (hZ w).mp hw
    have hwV : w ∈ V := D.supportWithinDomain hh
    refine ⟨hwV, ?_⟩
    by_contra hne
    have h0 := hmzero w (ball_subset_closedBall hwV) hne
    apply hh
    change MeromorphicOn.divisor f (ball 0 R) w = 0
    rw [hf.meromorphicOn.mono_set ball_subset_closedBall |>.divisor_apply hwV, h0]
    simp
  have hnonzero (w : ℂ) (hw : w ∈ Z) : w ≠ 0 := fun he => hf0 (he ▸ (hDmem w hw).2)
  let P (z : ℂ) := ∏ w ∈ Z, (Complex.canonicalFactor R w z) ^ (D w)
  have hgEq (w : ℂ) (hw : w ∈ U) (hwz : f w ≠ 0) : g w = P w * f w := by
    have ha := hf w hw
    rw [gD.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt hw
      (hmzero w hw hwz) hR,
      ha.meromorphicTrailingCoeffAt_of_ne_zero hwz, hDb]
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, neg_zero, zpow_zero, finprod_one, mul_one, smul_eq_mul]
    congr 1
    exact finprod_eq_prod_of_mulSupport_subset _ (fun z hz => (hZ z).2 (by
      intro hz'
      exact hz (by change Complex.canonicalFactor R z w ^ (D z) = 1; rw [hz', zpow_zero])))
  have hgSphere (w : ℂ) (hw : w ∈ sphere 0 R) : ‖g w‖ ≤ M := by
    rw [hgEq w (sphere_subset_closedBall hw) (hboundary w hw).1, norm_mul]
    have hh : ‖P w‖ = 1 := by
      unfold P
      rw [norm_prod]
      exact prod_eq_one fun z hz => by
        rw [norm_zpow, Complex.norm_canonicalFactor_eval_circle_eq_one (hDmem z hz).1 hw, one_zpow]
    rw [hh, one_mul]
    exact (hboundary w hw).2
  have hgBound (w : ℂ) (hw : w ∈ V) : ‖g w‖ ≤ M := by
    have hgc : DiffContOnCl ℂ g V := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball (0 : ℂ) hR.ne']
      exact gD.analyticOnNhd.differentiableOn
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hgc _ (subset_closure hw)
    rw [frontier_ball (0 : ℂ) hR.ne']
    exact hgSphere
  have hG0 : log ‖f 0‖ ≤ log ‖g 0‖ := by
    rw [hgEq 0 hU0 hf0, norm_mul]
    apply log_le_log (norm_pos_iff.mpr hf0)
    have hp : 1 ≤ ‖P 0‖ := by
      unfold P
      rw [norm_prod]
      refine Finset.one_le_prod fun w hw => ?_
      rw [norm_zpow]
      apply one_le_zpow₀ _ (hD0 w)
      have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (hnonzero w hw)
      rw [Complex.canonicalFactor_apply, mul_zero, sub_zero, zero_sub, norm_div, norm_pow,
        norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      apply (one_le_div₀ (mul_pos hR hwn)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp (hDmem w hw).1).le hR.le]
    exact le_mul_of_one_le_left (norm_nonneg _) hp
  have hlog (x : ℂ) (hx : x ∈ V) (hfx : f x ≠ 0) : logDeriv g x =
      (∑ w ∈ Z, (D w : ℂ) * logDeriv (Complex.canonicalFactor R w) x) + logDeriv f x := by
    have hxU : x ∈ U := ball_subset_closedBall hx
    have hne (w : ℂ) (hw : w ∈ Z) : x ≠ w := fun h => hfx (h ▸ (hDmem w hw).2)
    have hPa (w : ℂ) (hw : w ∈ Z) : DifferentiableAt ℂ (Complex.canonicalFactor R w) x :=
      (Complex.analyticOnNhd_canonicalFactor R w x (hne w hw)).differentiableAt
    have hPn (w : ℂ) (hw : w ∈ Z) : Complex.canonicalFactor R w x ≠ 0 :=
      Complex.canonicalFactor_ne_zero (hDmem w hw).1 hxU (hne w hw)
    have hPd : DifferentiableAt ℂ P x := by
      apply DifferentiableAt.fun_finsetProd
      exact fun w hw => (hPa w hw).zpow (Or.inl (hPn w hw))
    have hPnz : P x ≠ 0 := prod_ne_zero_iff.2 (fun w hw => zpow_ne_zero _ (hPn w hw))
    have he : g =ᶠ[𝓝 x] fun w => P w * f w := by
      filter_upwards [isOpen_ball.mem_nhds hx, (hf x hxU).continuousAt.eventually_ne hfx] with u hu hfu
      exact hgEq u (ball_subset_closedBall hu) hfu
    rw [(logDeriv_congr_nhds he).eq_of_nhds, logDeriv_mul _ hPnz hfx hPd (hf x hxU).differentiableAt]
    congr 1
    unfold P
    rw [logDeriv_prod (f := fun w z => (Complex.canonicalFactor R w z) ^ (D w))
      (x := x) (fun w hw => zpow_ne_zero _ (hPn w hw))
      (fun w hw => (hPa w hw).zpow (Or.inl (hPn w hw)))]
    exact sum_congr rfl (fun w hw => logDeriv_fun_zpow (hPa w hw) (D w))
  exact ⟨g, Z, hZ, hDmem, gD.analyticOnNhd, gD.ne_zero, hgBound, hG0, hlog⟩

open Metric in
private lemma disk_logDerivative_upper {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 R, f z ≠ 0 ∧ ‖f z‖ ≤ M)
    (hleft : ∀ z ∈ ball 0 R, f z = 0 → z.re ≤ 0) :
    -(logDeriv f 0).re ≤ 4 * (log M - log ‖f 0‖ + 1) / R ∧
    ∀ z ∈ ball 0 R, f z = 0 → z.im = 0 → z.re < 0 →
      -(logDeriv f 0).re ≤ 4 * (log M - log ‖f 0‖ + 1) / R + R⁻¹ - (-z.re)⁻¹ := by
  classical
  let U := closedBall (0 : ℂ) R
  let V := ball (0 : ℂ) R
  let E := 4 * (log M - log ‖f 0‖ + 1) / R
  have hU0 : (0 : ℂ) ∈ U := mem_closedBall_self hR.le
  have hV0 : (0 : ℂ) ∈ V := mem_ball_self hR
  have hfin (z : ℂ) (hz : z ∈ U) : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall 0 R).isPreconnected hU0 hz
      (by rw [(hf 0 hU0).analyticOrderAt_eq_zero.mpr hf0]; simp)
  let D := MeromorphicOn.divisor f V
  obtain ⟨g, Z, hZ, hDmem, hgA, hgN, hgBound, hG0, hlog_all⟩ := disk_logDeriv_data hR hf hf0 hboundary
  have hlog := hlog_all 0 hV0 hf0
  have hD0 (z : ℂ) : 0 ≤ D z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (hf.mono ball_subset_closedBall) z
  have hnonzero (w : ℂ) (hw : w ∈ Z) : w ≠ 0 := fun he => hf0 (he ▸ (hDmem w hw).2)
  have hGbound : ‖logDeriv g 0‖ ≤ E := by
    apply (norm_logDeriv_le_of_ball hR hM (hgA.mono ball_subset_closedBall)
      (fun z hz => hgN z (ball_subset_closedBall hz)) hgBound).trans
    exact div_le_div_of_nonneg_right (by linarith only [hG0]) hR.le
  let r (w : ℂ) : ℝ := (D w : ℝ) * (logDeriv (Complex.canonicalFactor R w) 0).re
  have hr (w : ℂ) (hw : w ∈ Z) : r w ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hD0 w)
      (canonicalFactor_logDeriv_re_nonpos hR (hnonzero w hw) (hDmem w hw).1
        (hleft w (hDmem w hw).1 (hDmem w hw).2))
  have hgre : (logDeriv g 0).re = (∑ w ∈ Z, r w) + (logDeriv f 0).re := by
    rw [hlog, Complex.add_re]
    change Complex.reCLM (∑ w ∈ Z, (D w : ℂ) * logDeriv (Complex.canonicalFactor R w) 0) +
      (logDeriv f 0).re = _
    rw [map_sum]
    congr 1
    apply sum_congr rfl
    intro w hw
    simp [r, Complex.mul_re]
  have hboundRe : -(logDeriv g 0).re ≤ E :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hGbound)
  refine ⟨by linarith only [hgre, hboundRe, sum_nonpos hr], ?_⟩
  intro w hwV hfw him hreal
  have hwU := ball_subset_closedBall hwV
  have hwZ : w ∈ Z := by
    apply (hZ w).2
    have hO := ((hf w hwU).analyticOrderAt_ne_zero).mpr hfw
    change MeromorphicOn.divisor f V w ≠ 0
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono ball_subset_closedBall) hwV]
    rcases ENat.ne_top_iff_exists.mp (hfin w hwU) with ⟨n, hn⟩
    rw [← hn] at hO ⊢
    simpa using hO
  have hDw : 1 ≤ (D w : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ D w from by
      have hh := (hZ w).1 hwZ
      have hn := hD0 w
      change D w ≠ 0 at hh
      omega)
  have hRterm : r w ≤ R⁻¹ - (-w.re)⁻¹ := by
    have ht := canonicalFactor_logDeriv_re_aligned hR hwV him hreal
    have hneg := canonicalFactor_logDeriv_re_nonpos hR (hnonzero w hwZ) hwV hreal.le
    have hh := mul_le_mul_of_nonpos_right hDw hneg
    rw [one_mul] at hh
    exact hh.trans ht
  have hsum : (∑ z ∈ Z, r z) ≤ R⁻¹ - (-w.re)⁻¹ := by
    rw [← sum_erase_add _ _ hwZ]
    have hs : (∑ z ∈ Z.erase w, r z) ≤ 0 := sum_nonpos fun z hz => hr z (mem_of_mem_erase hz)
    linarith only [hs, hRterm]
  linarith only [hgre, hboundRe, hsum]

private lemma norm_inv_riemannZeta_le_real {s : ℂ} (hs : 1 < s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  let a (n : ℕ) : ℂ := ArithmeticFunction.moebius n
  let b (n : ℕ) : ℝ := (n : ℝ) ^ (-s.re)
  have hsreal : 1 < (s.re : ℂ).re := hs
  have hb : Summable b := summable_nat_rpow.2 (by linarith only [hs])
  have hζ : (riemannZeta s)⁻¹ = LSeries a s := by
    have h := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs] at h
    change riemannZeta s * LSeries a s = 1 at h
    calc
      _ = (riemannZeta s)⁻¹ * 1 := by rw [mul_one]
      _ = (riemannZeta s)⁻¹ * (riemannZeta s * LSeries a s) := by rw [h]
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (riemannZeta_ne_zero_of_one_le_re hs.le), one_mul]
  have ht (n : ℕ) : ‖LSeries.term a s n‖ ≤ b n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero, norm_zero]
      exact rpow_nonneg (Nat.cast_nonneg _) _
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.term_of_ne_zero hn, norm_div, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    change ‖a n‖ / (n : ℝ) ^ s.re ≤ (n : ℝ) ^ (-s.re)
    rw [rpow_neg hn0.le, ← one_div]
    apply div_le_div_of_nonneg_right _ (rpow_nonneg hn0.le _)
    have h := ArithmeticFunction.abs_moebius_le_one (n := n)
    dsimp [a]
    exact_mod_cast h
  have hnorm : Summable (fun n => ‖LSeries.term a s n‖) :=
    hb.of_nonneg_of_le (fun _ => norm_nonneg _) ht
  have hreal : riemannZeta (s.re : ℂ) = ((∑' n, b n : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hsreal, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have hnz : (s.re : ℂ) ≠ 0 := by
        intro hn
        have hre := congrArg Complex.re hn
        simp only [Complex.ofReal_re, Complex.zero_re] at hre
        linarith only [hre, hs]
      simp [b, Real.zero_rpow (by linarith only [hs] : -s.re ≠ 0), Complex.zero_cpow hnz]
    · have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [one_div, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hn0.le,
        ← Complex.ofReal_inv, ← rpow_neg hn0.le]
  rw [hζ, LSeries, hreal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun n => rpow_nonneg (Nat.cast_nonneg n) _)]
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum ht hb)

private lemma riemannZeta_near_one_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      (s.re - 1) / C ≤ ‖riemannZeta s‖ := by
  obtain ⟨B, hB, hb⟩ := norm_riemannZeta₁_le (show (0 : ℝ) < 1 by norm_num)
  let C := 1 + 2 * B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun s hlo hhi => ?_⟩
  have hp : 0 < s.re - 1 := sub_pos.mpr hlo
  have hs1 : (s.re : ℂ) ≠ 1 := by
    intro h
    have h0 := congrArg Complex.re h
    exact hlo.ne' h0
  have hreg := hb (s.re : ℂ) hlo.le
  have hreg' : ‖riemannZeta₁ (s.re : ℂ)‖ ≤ C := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp, abs_of_pos (zero_lt_one.trans hlo)] at hreg
    refine hreg.trans (add_le_add_right ?_ 1)
    rw [mul_comm 2 B]
    apply mul_le_mul_of_nonneg_left _ hB
    have hδ : s.re - 1 ≤ 1 := by linarith only [hhi]
    simpa only [one_mul] using mul_le_mul hδ hhi (zero_lt_one.trans hlo).le zero_le_one
  have hs0 : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hlo.le)
  have hinv := norm_inv_riemannZeta_le_real hlo
  rw [norm_inv] at hinv
  have hup : ‖riemannZeta (s.re : ℂ)‖ ≤ C / (s.re - 1) := by
    rw [riemannZeta_eq_inv_sub_mul hs1, norm_mul, norm_inv, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
      div_eq_mul_inv, mul_comm C]
    exact mul_le_mul_of_nonneg_left hreg' (inv_nonneg.mpr hp.le)
  have h : 1 / ‖riemannZeta s‖ ≤ C / (s.re - 1) := by simpa only [one_div] using hinv.trans hup
  have hh := (div_le_div_iff₀ hs0 hp).mp h
  exact (div_le_iff₀ hC).mpr (by simpa [mul_comm] using hh)

private noncomputable def localWidth (t : ℝ) : ℝ := log (|t| + 3) ^ (-(2 / 3) : ℝ)

-- A narrow-strip growth bound supplied by the Vinogradov–Korobov estimate for zeta.
private def ZetaGrowthNearOne : Prop :=
  ∃ A T₀ : ℝ, 0 ≤ A ∧ 3 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
    ∀ s ∈ Metric.closedBall (⟨1, t⟩ : ℂ) (4 * localWidth t),
      ‖riemannZeta s‖ ≤ log (|t| + 3) ^ A

private lemma norm_zeta_truncation_error {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) {N : ℕ} (hN : 0 < N) :
    ‖riemannZeta s - ∑ n ∈ range N, ((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤
      ((N + 1 : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖ + (‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
  let f (n : ℕ) : ℂ := zetaTerm n s
  let S := ∑ n ∈ range N, ((n + 1 : ℕ) : ℂ) ^ (-s)
  let P := ((N + 1 : ℕ) : ℂ) ^ (1 - s)
  have ht : (∑ n ∈ range N, f n) = (s - 1) * S + P - 1 := by
    let g (n : ℕ) : ℂ := ((n + 1 : ℕ) : ℂ) ^ (1 - s)
    have hg := Finset.sum_range_sub' g N
    have h₀ : g 0 = 1 := by simp [g]
    rw [h₀] at hg
    calc
      _ = (∑ n ∈ range N, (s - 1) * ((n + 1 : ℕ) : ℂ) ^ (-s)) -
          ∑ n ∈ range N, (g n - g (n + 1)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro n _
        dsimp [f, g, zetaTerm]
        push_cast
        ring
      _ = _ := by
        rw [← Finset.mul_sum, hg]
        change (s - 1) * S - (1 - P) = (s - 1) * S + P - 1
        ring
  have hsum : Summable f := zetaTerm_summable hs
  have hz : (s - 1) * riemannZeta s = riemannZeta₁ s := by
    rw [riemannZeta_eq_inv_sub_mul hs₁, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs₁), one_mul]
  rw [← zetaTermSum_eq hs] at hz
  change (s - 1) * riemannZeta s = 1 + ∑' n, f n at hz
  rw [← hsum.sum_add_tsum_nat_add N, ht] at hz
  have hEq : riemannZeta s - S = (P + ∑' n : ℕ, f (n + N)) / (s - 1) := by
    apply (eq_div_iff (sub_ne_zero.mpr hs₁)).mpr
    linear_combination hz
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let r (x : ℝ) := x ^ (-s.re - 1)
  have hr : -s.re - 1 < -1 := by linarith only [hs]
  have hA : AntitoneOn r (Set.Ici (N : ℝ)) := by
    intro a ha b hb hab
    exact rpow_le_rpow_of_nonpos (hN0.trans_le ha) hab (by linarith only [hs])
  have hTail : (∑' n : ℕ, r (n + N + 1 : ℕ)) ≤ (N : ℝ) ^ (-s.re) / s.re := by
    have h := hA.tsum_comp_add_le_integral N (integrableOn_Ioi_rpow_of_lt hr hN0)
      (fun t ht => rpow_nonneg (hN0.le.trans ht.le) _)
    dsimp only [r] at h
    rw [integral_Ioi_rpow_of_lt hr hN0, show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq] at h
    exact h
  let C := ‖s - 1‖ * ‖s‖
  have hterm (n : ℕ) : ‖f (n + N)‖ ≤ C * r (n + N + 1 : ℕ) := norm_zetaTerm_le _ hs
  have hrs : Summable (fun n : ℕ => r (n + N + 1 : ℕ)) :=
    (summable_nat_add_iff N).mpr (summable_rpow_succ hr)
  have hdom := hrs.mul_left C
  have hnorm : Summable (fun n : ℕ => ‖f (n + N)‖) :=
    hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hterr : ‖∑' n : ℕ, f (n + N)‖ ≤ C * ((N : ℝ) ^ (-s.re) / s.re) := by
    calc
      _ ≤ ∑' n : ℕ, ‖f (n + N)‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : ℕ, C * r (n + N + 1 : ℕ) := hnorm.tsum_le_tsum hterm hdom
      _ ≤ _ := by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hTail (by dsimp [C]; positivity)
  have hP : ‖P‖ = ((N + 1 : ℕ) : ℝ) ^ (1 - s.re) := by
    dsimp [P]
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [Complex.sub_re]
  change ‖riemannZeta s - S‖ ≤ _
  rw [hEq, norm_div]
  calc
    _ ≤ (‖P‖ + C * ((N : ℝ) ^ (-s.re) / s.re)) / ‖s - 1‖ :=
      div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add_right hterr _)) (norm_nonneg _)
    _ = _ := by
      rw [hP]
      dsimp [C]
      have hsn : ‖s - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs₁)
      field_simp

private noncomputable def zetaCutoff (t : ℝ) : ℕ := ⌈(|t| + 3) ^ (2 : ℕ)⌉₊

private lemma zetaCutoff_bounds (t : ℝ) :
    (|t| + 3) ^ (2 : ℕ) ≤ (zetaCutoff t : ℝ) ∧ ((zetaCutoff t : ℝ) + 1) ≤ (|t| + 4) ^ (2 : ℕ) := by
  refine ⟨Nat.le_ceil _, ?_⟩
  have h := Nat.ceil_lt_add_one (show 0 ≤ (|t| + 3) ^ (2 : ℕ) by positivity)
  change (zetaCutoff t : ℝ) < (|t| + 3) ^ (2 : ℕ) + 1 at h
  nlinarith only [h, abs_nonneg t]

private lemma norm_zeta_sub_cutoff {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 2) (ht : 3 ≤ |s.im|) :
    ‖riemannZeta s - ∑ n ∈ range (zetaCutoff s.im), ((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ 5 := by
  let N := zetaCutoff s.im
  have hN := zetaCutoff_bounds s.im
  change (|s.im| + 3) ^ (2 : ℕ) ≤ (N : ℝ) ∧ (N : ℝ) + 1 ≤ (|s.im| + 4) ^ (2 : ℕ) at hN
  have hS : 0 < s.re := by linarith only [hs]
  have ht0 : 0 < |s.im| := by linarith only [ht]
  have hs₁ : s ≠ 1 := by intro heq; norm_num [heq] at ht
  have hN1 : (1 : ℝ) ≤ N := by
    nlinarith only [hN.1, abs_nonneg s.im, sq_nonneg |s.im|]
  have hN0 : 0 < N := by exact_mod_cast (zero_lt_one.trans_le hN1)
  have hsn : ‖s‖ ≤ |s.im| + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hS] at h
    linarith only [h, hs']
  have hsi : |s.im| ≤ ‖s - 1‖ := by simpa [Complex.sub_im] using Complex.abs_im_le_norm (s - 1)
  have hB : ((N + 1 : ℕ) : ℝ) ^ (1 - s.re) ≤ |s.im| + 4 := by
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
        rpow_le_rpow_of_exponent_le (by push_cast; linarith only [hN1]) (by linarith only [hs])
      _ = sqrt ((N : ℝ) + 1) := by rw [sqrt_eq_rpow, Nat.cast_add_one]
      _ ≤ _ := by
        rw [sqrt_le_iff]
        exact ⟨by positivity, hN.2⟩
  have hA : (N : ℝ) ^ (-s.re) ≤ (|s.im| + 3)⁻¹ := by
    calc
      _ ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) := rpow_le_rpow_of_exponent_le hN1 (by linarith only [hs])
      _ = (sqrt (N : ℝ))⁻¹ := by rw [Real.rpow_neg (Nat.cast_nonneg _), sqrt_eq_rpow]
      _ ≤ _ := by
        have hle : |s.im| + 3 ≤ sqrt (N : ℝ) := Real.le_sqrt_of_sq_le hN.1
        exact (inv_le_inv₀ ((by positivity : 0 < |s.im| + 3).trans_le hle) (by positivity)).mpr hle
  apply (norm_zeta_truncation_error hS hs₁ hN0).trans
  have hfront : ((N + 1 : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖ ≤ 3 := by
    apply (div_le_iff₀ (ht0.trans_le hsi)).mpr
    linarith only [hB, hsi, ht]
  have htail : (‖s‖ / s.re) * (N : ℝ) ^ (-s.re) ≤ 2 := by
    have hnorm : ‖s‖ / s.re ≤ 2 * (|s.im| + 2) := by
      apply (div_le_iff₀ hS).mpr
      nlinarith only [hsn, mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ |s.im| + 2 by positivity)]
    calc
      _ ≤ (2 * (|s.im| + 2)) * (|s.im| + 3)⁻¹ :=
        mul_le_mul hnorm hA (by positivity) (by positivity)
      _ ≤ _ := by
        rw [← div_eq_mul_inv]
        exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  linarith only [hfront, htail]

private noncomputable def logFrequency (n : ℕ) : ℝ := log (n + 1 : ℝ)

private lemma abs_logFrequency_sub_lower {m n N : ℕ} (hm : m < N) (hn : n < N) :
    |(m : ℝ) - (n : ℝ)| / N ≤ |logFrequency m - logFrequency n| := by
  wlog hmn : m ≤ n generalizing m n
  · have h := this hn hm (by omega)
    simpa only [abs_sub_comm] using h
  have hM : 0 < (m : ℝ) + 1 := by positivity
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hnum := Real.log_le_sub_one_of_pos (div_pos hM hN)
  rw [Real.log_div hM.ne' hN.ne'] at hnum
  have he : 1 - ((m : ℝ) + 1) / ((n : ℝ) + 1) = ((n : ℝ) - m) / ((n : ℝ) + 1) := by field_simp; ring
  have hdiff : ((n : ℝ) - m) / ((n : ℝ) + 1) ≤ logFrequency n - logFrequency m := by
    rw [← he, logFrequency, logFrequency]
    linarith only [hnum]
  rw [abs_of_nonpos (sub_nonpos.mpr hmn'), neg_sub]
  have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hn
  calc
    _ ≤ ((n : ℝ) - m) / ((n : ℝ) + 1) := div_le_div_of_nonneg_left (sub_nonneg.mpr hmn') hN hn'
    _ ≤ logFrequency n - logFrequency m := hdiff
    _ ≤ _ := neg_le_abs (logFrequency m - logFrequency n) |>.trans' (by ring_nf; rfl)

private noncomputable def harmonicWeight (N : ℕ) : ℝ := ∑ j ∈ range N, ((j + 1 : ℝ))⁻¹

private lemma sum_inv_nat_dist_le {n N : ℕ} (hn : n < N) :
    ∑ m ∈ (range N).erase n, |(n : ℝ) - (m : ℝ)|⁻¹ ≤ 2 * harmonicWeight N := by
  classical
  let S := (range N).erase n
  let L := S.filter (fun m => m < n)
  let U := S.filter (fun m => ¬m < n)
  let a (m : ℕ) := |(n : ℝ) - (m : ℝ)|⁻¹
  let h (j : ℕ) := ((j + 1 : ℝ))⁻¹
  have hpart : (∑ m ∈ L, a m) + ∑ m ∈ U, a m = ∑ m ∈ S, a m :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change ∑ m ∈ S, a m ≤ _
  rw [← hpart]
  have hL : ∑ m ∈ L, a m ≤ harmonicWeight N := by
    let g (m : ℕ) := n - (m + 1)
    have hi : Set.InjOn g (L : Set ℕ) := by
      intro i hi j hj heq
      have hil := (Finset.mem_filter.mp (show i ∈ L from hi)).2
      have hjl := (Finset.mem_filter.mp (show j ∈ L from hj)).2
      dsimp [g] at heq
      omega
    have hmaps : L.image g ⊆ range N := by
      intro j hj
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr ((Nat.sub_le _ _).trans_lt hn)
    calc
      _ = ∑ m ∈ L, h (g m) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hl : m < n := (Finset.mem_filter.mp hm).2
        have hle : (m : ℝ) ≤ n := by exact_mod_cast hl.le
        dsimp [a, h, g]
        rw [abs_of_nonneg (sub_nonneg.mpr hle), Nat.cast_sub (by omega), Nat.cast_add_one]
        congr 1
        ring
      _ = ∑ j ∈ L.image g, h j := (Finset.sum_image (fun i hiL j hjL hij => hi hiL hjL hij)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hmaps (fun _ _ _ => by unfold h; positivity)
  have hU : ∑ m ∈ U, a m ≤ harmonicWeight N := by
    let g (m : ℕ) := m - (n + 1)
    have hlo (m : ℕ) (hm : m ∈ U) : n < m := by
      obtain ⟨hmS, hmge⟩ := Finset.mem_filter.mp hm
      exact lt_of_le_of_ne (le_of_not_gt hmge) (Finset.mem_erase.mp hmS).1.symm
    have hi : Set.InjOn g (U : Set ℕ) := by
      intro i hi j hj heq
      have hil := hlo i hi
      have hjl := hlo j hj
      dsimp [g] at heq
      omega
    have hmaps : U.image g ⊆ range N := by
      intro j hj
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hj
      have hN := Finset.mem_range.mp (Finset.mem_erase.mp (Finset.mem_filter.mp hm).1).2
      exact Finset.mem_range.mpr ((Nat.sub_le _ _).trans_lt hN)
    calc
      _ = ∑ m ∈ U, h (g m) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hl := hlo m hm
        have hle : (n : ℝ) ≤ m := by exact_mod_cast hl.le
        dsimp [a, h, g]
        rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, Nat.cast_sub (by omega), Nat.cast_add_one]
        congr 1
        ring
      _ = ∑ j ∈ U.image g, h j := (Finset.sum_image (fun i hiU j hjU hij => hi hiU hjU hij)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hmaps (fun _ _ _ => by unfold h; positivity)
  linarith only [hL, hU]

private lemma sum_inv_logFrequency_dist_le {n N : ℕ} (hn : n < N) :
    ∑ m ∈ (range N).erase n, |logFrequency n - logFrequency m|⁻¹ ≤ 2 * (N : ℝ) * harmonicWeight N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast ((Nat.zero_le n).trans_lt hn)
  calc
    _ ≤ ∑ m ∈ (range N).erase n, (N : ℝ) * |(n : ℝ) - (m : ℝ)|⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨hmn, hm⟩ := Finset.mem_erase.mp hm
      have hnm' : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hmn.symm
      have hpos : 0 < |(n : ℝ) - (m : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hnm')
      have hlog := abs_logFrequency_sub_lower hn (Finset.mem_range.mp hm)
      have h := (inv_le_inv₀ ((div_pos hpos hN0).trans_le hlog) (div_pos hpos hN0)).mpr hlog
      rwa [div_eq_mul_inv, mul_inv_rev, inv_inv] at h
    _ = (N : ℝ) * ∑ m ∈ (range N).erase n, |(n : ℝ) - (m : ℝ)|⁻¹ := by rw [Finset.mul_sum]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sum_inv_nat_dist_le hn) hN0.le).trans_eq (by ring)

private lemma symmetric_row_sum_bound {ι : Type*} (S : Finset ι) {a : ι → ℝ} {k : ι → ι → ℝ} {R : ℝ}
    (hn : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ k i j) (hs : ∀ i ∈ S, ∀ j ∈ S, k i j = k j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, k i j ≤ R) :
    ∑ i ∈ S, ∑ j ∈ S, (a i * a j) * k i j ≤ R * ∑ i ∈ S, a i ^ (2 : ℕ) := by
  let x (i j : ι) := (a i ^ (2 : ℕ)) * k i j
  let y (i j : ι) := (a j ^ (2 : ℕ)) * k i j
  have hflip : (∑ i ∈ S, ∑ j ∈ S, y i j) = ∑ i ∈ S, ∑ j ∈ S, x i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [x, y]
    rw [hs j hj i hi]
  have hfirst : (∑ i ∈ S, ∑ j ∈ S, x i j) ≤ R * ∑ i ∈ S, a i ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    dsimp [x]
    rw [← Finset.mul_sum, mul_comm R]
    exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, (x i j + y i j) * (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hle : a i * a j ≤ (a i ^ (2 : ℕ) + a j ^ (2 : ℕ)) * (1 / 2 : ℝ) :=
        by nlinarith only [sq_nonneg (a i - a j)]
      exact (mul_le_mul_of_nonneg_right hle (hn i hi j hj)).trans_eq (by dsimp [x,y]; ring)
    _ = ((∑ i ∈ S, ∑ j ∈ S, x i j) + ∑ i ∈ S, ∑ j ∈ S, y i j) * (1 / 2 : ℝ) := by
      simp_rw [← Finset.sum_mul, Finset.sum_add_distrib]
    _ = (∑ i ∈ S, ∑ j ∈ S, x i j) := by rw [hflip]; ring
    _ ≤ _ := hfirst

private noncomputable def imaginaryPhase (freq t : ℝ) : ℂ :=
  Complex.exp ((freq : ℂ) * (t : ℂ) * Complex.I)

private lemma norm_imaginaryPhase (freq t : ℝ) : ‖imaginaryPhase freq t‖ = 1 := by
  simp [imaginaryPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private lemma imaginaryPhase_add (freq μ t : ℝ) :
    imaginaryPhase (freq + μ) t = imaginaryPhase freq t * imaginaryPhase μ t := by
  unfold imaginaryPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma imaginaryPhase_conj (freq t : ℝ) :
    (starRingEnd ℂ) (imaginaryPhase freq t) = imaginaryPhase (-freq) t := by
  unfold imaginaryPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

private lemma continuous_imaginaryPhase (freq : ℝ) : Continuous (imaginaryPhase freq) := by
  unfold imaginaryPhase
  fun_prop

private lemma hasDerivAt_imaginaryPhase (freq t : ℝ) :
    HasDerivAt (imaginaryPhase freq) (((freq : ℂ) * Complex.I) * imaginaryPhase freq t) t := by
  have hd : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have he := ((hd.const_mul (freq : ℂ)).mul_const Complex.I).cexp
  simpa only [imaginaryPhase, mul_one, mul_comm (Complex.exp _)] using! he

private lemma norm_integral_imaginaryPhase_le {freq : ℝ} (hfreq : freq ≠ 0) (l u : ℝ) :
    ‖∫ t in l..u, imaginaryPhase freq t‖ ≤ 2 / |freq| := by
  let c : ℂ := (freq : ℂ) * Complex.I
  have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hfreq) Complex.I_ne_zero
  have he (t : ℝ) : imaginaryPhase freq t = Complex.exp (c * (t : ℂ)) := by
    unfold imaginaryPhase c
    congr 1
    ring
  have hnorm : ‖c‖ = |freq| := by simp [c, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [he]
  rw [integral_exp_mul_complex hc, ← he, ← he, norm_div, hnorm]
  exact div_le_div_of_nonneg_right ((norm_sub_le _ _).trans_eq (by norm_num [norm_imaginaryPhase])) (abs_nonneg _)

private noncomputable def logDirichletPolynomial (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ range N, a n * imaginaryPhase (logFrequency n) t

private lemma continuous_logDirichletPolynomial (N : ℕ) (a : ℕ → ℂ) :
    Continuous (logDirichletPolynomial N a) :=
  continuous_finsetSum _ (fun _ _ => continuous_const.mul (continuous_imaginaryPhase _))

private lemma logDirichletPolynomial_mean_square {l u : ℝ} (hlu : l ≤ u) (N : ℕ) (a : ℕ → ℂ) :
    (∫ t in l..u, ‖logDirichletPolynomial N a t‖ ^ (2 : ℕ)) ≤
      (u - l + 4 * (N : ℝ) * harmonicWeight N) * ∑ n ∈ range N, ‖a n‖ ^ (2 : ℕ) := by
  classical
  let P := logDirichletPolynomial N a
  let F (n m : ℕ) (t : ℝ) := (a n * (starRingEnd ℂ) (a m)) *
    imaginaryPhase (logFrequency n - logFrequency m) t
  let E := ∫ t in l..u, ‖P t‖ ^ (2 : ℕ)
  have hE : 0 ≤ E := intervalIntegral.integral_nonneg hlu (fun _ _ => sq_nonneg _)
  have hId (t : ℝ) : ((‖P t‖ ^ (2 : ℕ) : ℝ) : ℂ) = ∑ n ∈ range N, ∑ m ∈ range N, F n m t := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    unfold P logDirichletPolynomial
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [F]
    rw [map_mul, imaginaryPhase_conj, sub_eq_add_neg, imaginaryPhase_add]
    ring
  have hi (n m : ℕ) : IntervalIntegrable (F n m) MeasureTheory.volume l u :=
    (continuous_const.mul (continuous_imaginaryPhase _)).intervalIntegrable _ _
  have hsum (n : ℕ) : IntervalIntegrable (fun t => ∑ m ∈ range N, F n m t) MeasureTheory.volume l u := by
    exact (continuous_finsetSum _ (fun m _ => continuous_const.mul (continuous_imaginaryPhase _))).intervalIntegrable _ _
  have hEeq : (E : ℂ) = ∑ n ∈ range N, ∑ m ∈ range N, ∫ t in l..u, F n m t := by
    calc
      _ = ∫ t in l..u, ((‖P t‖ ^ (2 : ℕ) : ℝ) : ℂ) := by rw [intervalIntegral.integral_ofReal]
      _ = ∫ t in l..u, ∑ n ∈ range N, ∑ m ∈ range N, F n m t := by simp_rw [hId]
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum (fun n _ => hsum n)]
        apply Finset.sum_congr rfl
        intro n hn
        exact intervalIntegral.integral_finsetSum (fun m _ => hi n m)
  let G (n m : ℕ) := if n = m then u - l else 2 * |logFrequency n - logFrequency m|⁻¹
  have hnonneg (n m : ℕ) : 0 ≤ G n m := by
    unfold G
    split_ifs
    · exact sub_nonneg.mpr hlu
    · positivity
  have hs (n m : ℕ) : G n m = G m n := by
    rcases eq_or_ne n m with rfl | hn
    · rfl
    · simp only [G, if_neg hn, if_neg hn.symm, abs_sub_comm]
  have hrow (n : ℕ) (hn : n ∈ range N) : ∑ m ∈ range N, G n m ≤ u - l + 4 * (N : ℝ) * harmonicWeight N := by
    rw [← Finset.sum_erase_add _ _ hn]
    have hdiff : (∑ m ∈ (range N).erase n, G n m) = 2 * ∑ m ∈ (range N).erase n,
        |logFrequency n - logFrequency m|⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m hm => if_neg (Finset.mem_erase.mp hm).1.symm)
    rw [hdiff, show G n n = u - l from if_pos rfl]
    have hh := mul_le_mul_of_nonneg_left (sum_inv_logFrequency_dist_le (Finset.mem_range.mp hn))
      (show (0 : ℝ) ≤ 2 by norm_num)
    linarith only [hh]
  have hF (n m : ℕ) (hn : n ∈ range N) (hm : m ∈ range N) :
      ‖∫ t in l..u, F n m t‖ ≤ (‖a n‖ * ‖a m‖) * G n m := by
    dsimp [F]
    rw [intervalIntegral.integral_const_mul, norm_mul, norm_mul, Complex.norm_conj]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rcases eq_or_ne n m with rfl | hne
    · rw [show G n n = u - l from if_pos rfl, sub_self]
      simp only [imaginaryPhase, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
        intervalIntegral.integral_const, Complex.real_smul, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hlu), le_refl]
    · rw [show G n m = _ from if_neg hne, ← div_eq_mul_inv]
      apply norm_integral_imaginaryPhase_le
      intro hzero
      have h := abs_logFrequency_sub_lower (Finset.mem_range.mp hn) (Finset.mem_range.mp hm)
      rw [hzero, abs_zero] at h
      have hp : 0 < |(n : ℝ) - (m : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
      exact (div_pos hp (by exact_mod_cast ((Nat.zero_le n).trans_lt (Finset.mem_range.mp hn)))).not_ge h
  change E ≤ _
  calc
    _ = ‖(E : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
    _ ≤ ∑ n ∈ range N, ∑ m ∈ range N, ‖∫ t in l..u, F n m t‖ := by
      rw [hEeq]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ n ∈ range N, ∑ m ∈ range N, (‖a n‖ * ‖a m‖) * G n m :=
      Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hF n m hn hm
    _ ≤ _ := symmetric_row_sum_bound _ (fun n _ m _ => hnonneg n m) (fun n _ m _ => hs n m) hrow

private lemma hasDerivAt_norm_sq_complex {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun x => ‖f x‖ ^ (2 : ℕ)) (2 * (f' * (starRingEnd ℂ) (f t)).re) t := by
  have hr : HasDerivAt (fun x => (f x).re) f'.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have hi : HasDerivAt (fun x => (f x).im) f'.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  have hfun : (fun x => ‖f x‖ ^ (2 : ℕ)) = fun x => (f x).re ^ (2 : ℕ) + (f x).im ^ (2 : ℕ) := by
    funext x
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hval : 2 * (f' * (starRingEnd ℂ) (f t)).re =
      (2 : ℕ) * (f t).re ^ (2 - 1 : ℕ) * f'.re + (2 : ℕ) * (f t).im ^ (2 - 1 : ℕ) * f'.im := by
    simp [Complex.mul_re]
    ring
  rw [hfun, hval]
  exact (hr.pow 2).add (hi.pow 2)

private lemma abs_norm_sq_deriv_le (z w : ℂ) :
    |2 * (w * (starRingEnd ℂ) z).re| ≤ ‖z‖ ^ (2 : ℕ) + ‖w‖ ^ (2 : ℕ) := by
  rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  calc
    _ ≤ 2 * ‖w * (starRingEnd ℂ) z‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ ≤ _ := by rw [norm_mul, Complex.norm_conj]; nlinarith only [sq_nonneg (‖w‖ - ‖z‖)]

private lemma norm_sq_le_unit_integral {f g : ℝ → ℂ} {l u t : ℝ} (hlen : u - l = 1)
    (ht : t ∈ Set.Icc l u) (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) :
    ‖f t‖ ^ (2 : ℕ) ≤ 2 * (∫ x in l..u, ‖f x‖ ^ (2 : ℕ)) + (∫ x in l..u, ‖g x‖ ^ (2 : ℕ)) := by
  let p (x : ℝ) : ℝ := ‖f x‖ ^ (2 : ℕ)
  let q (x : ℝ) : ℝ := ‖g x‖ ^ (2 : ℕ)
  let d (x : ℝ) : ℝ := 2 * (g x * (starRingEnd ℂ) (f x)).re
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hp : Continuous p := hcont.norm.pow _
  have hq : Continuous q := hg.norm.pow _
  have hd : Continuous d := by
    dsimp [d]
    fun_prop
  have hd' (x : ℝ) : HasDerivAt p (d x) x := hasDerivAt_norm_sq_complex (hf x)
  have hdu (x : ℝ) : |d x| ≤ p x + q x := abs_norm_sq_deriv_le (f x) (g x)
  have hl : l ≤ u := ht.1.trans ht.2
  let M := ∫ x in l..u, (p x + q x)
  have hdiff (x y : ℝ) (hx : x ∈ Set.Icc l u) (hy : y ∈ Set.Icc l u) :
      |p y - p x| ≤ M := by
    wlog hxy : x ≤ y generalizing x y
    · simpa only [abs_sub_comm] using this y x hy hx (le_of_not_ge hxy)
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd' z) (hd.intervalIntegrable x y)]
    calc
      _ ≤ ∫ z in x..y, |d z| := by
        simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := d) hxy
      _ ≤ ∫ z in x..y, (p z + q z) := intervalIntegral.integral_mono_on hxy
        (hd.abs.intervalIntegrable _ _) ((hp.add hq).intervalIntegrable _ _) (fun z _ => hdu z)
      _ ≤ _ := intervalIntegral.integral_mono_interval hx.1 hxy hy.2
        (Eventually.of_forall fun z => add_nonneg (sq_nonneg _) (sq_nonneg _)) ((hp.add hq).intervalIntegrable _ _)
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc l u) : p t ≤ p x + M := by
    have h := (le_abs_self (p t - p x)).trans (hdiff x t hx ht)
    linarith only [h]
  have hc (a : ℝ) : (∫ _x in l..u, a) = a := by rw [intervalIntegral.integral_const, hlen, one_smul]
  change p t ≤ _
  calc
    _ = ∫ _x in l..u, p t := (hc (p t)).symm
    _ ≤ ∫ x in l..u, (p x + M) := intervalIntegral.integral_mono_on hl intervalIntegrable_const
      ((hp.add continuous_const).intervalIntegrable _ _) hpoint
    _ = _ := by
      rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _) intervalIntegrable_const, hc]
      dsimp [M]
      rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _) (hq.intervalIntegrable _ _)]
      ring

open MeasureTheory in
private lemma sum_local_integrals_le {S : Finset ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T) (hsep : (S : Set ℝ).Pairwise (fun t u => 1 ≤ |t - u|))
    {f : ℝ → ℝ} (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) :
    ∑ t ∈ S, (∫ x in (t - 1 / 2)..(t + 1 / 2), f x) ≤ ∫ x in (-T - 1 / 2)..(T + 1 / 2), f x := by
  let A (t : ℝ) := Set.Ioc (t - 1 / 2) (t + 1 / 2)
  let B := Set.Ioc (-T - 1 / 2) (T + 1 / 2)
  have hglob : -T - 1 / 2 ≤ T + 1 / 2 := by linarith only [hT]
  have hpair : (S : Set ℝ).Pairwise (fun t u => Disjoint (A t) (A u)) := by
    intro t ht u hu htu
    have h := hsep ht hu htu
    rw [Set.disjoint_left]
    intro x hx hx'
    have h₁ : |t - u| < 1 := abs_lt.mpr (by
      change t - 1 / 2 < x ∧ x ≤ t + 1 / 2 at hx
      change u - 1 / 2 < x ∧ x ≤ u + 1 / 2 at hx'
      constructor <;> linarith only [hx.1, hx.2, hx'.1, hx'.2])
    exact h.not_gt h₁
  have hi (t : ℝ) : IntegrableOn f (A t) := (hf.intervalIntegrable _ _).1
  have hm (t : ℝ) (ht : t ∈ S) : A t ⊆ B := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hS t ht)
    exact Set.Ioc_subset_Ioc (by linarith only [hlo]) (by linarith only [hhi])
  have he (t : ℝ) : (∫ x in (t - 1 / 2)..(t + 1 / 2), f x) = ∫ x in A t, f x :=
    intervalIntegral.integral_of_le (by linarith)
  simp_rw [he]
  rw [← integral_biUnion_finset S (fun _ _ => measurableSet_Ioc) hpair (fun t _ => hi t),
    intervalIntegral.integral_of_le hglob]
  apply setIntegral_mono_set (hf.intervalIntegrable _ _).1 (Eventually.of_forall (fun x => hn x))
  exact (Set.iUnion₂_subset hm).eventuallyLE

private lemma logDirichletPolynomial_sample_square {S : Finset ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T) (hsep : (S : Set ℝ).Pairwise (fun t u => 1 ≤ |t - u|))
    (N : ℕ) (a : ℕ → ℂ) :
    ∑ t ∈ S, ‖logDirichletPolynomial N a t‖ ^ (2 : ℕ) ≤
      ((2 * T + 1) + 4 * (N : ℝ) * harmonicWeight N) * (2 + (log (N : ℝ)) ^ (2 : ℕ)) *
        ∑ n ∈ range N, ‖a n‖ ^ (2 : ℕ) := by
  let P := logDirichletPolynomial N a
  let b (n : ℕ) := a n * ((logFrequency n : ℂ) * Complex.I)
  let Q := logDirichletPolynomial N b
  let L := -T - 1 / 2
  let U := T + 1 / 2
  let R := 2 * T + 1 + 4 * (N : ℝ) * harmonicWeight N
  have hR : 0 ≤ R := by
    dsimp [R, harmonicWeight]
    positivity
  have hLU : L ≤ U := by dsimp [L, U]; linarith only [hT]
  have hd (t : ℝ) : HasDerivAt P (Q t) t := by
    dsimp [P, Q, logDirichletPolynomial]
    apply HasDerivAt.fun_sum
    intro n hn
    simpa only [b, mul_assoc] using (hasDerivAt_imaginaryPhase (logFrequency n) t).const_mul (a n)
  have hP := continuous_logDirichletPolynomial N a
  have hQ := continuous_logDirichletPolynomial N b
  have hbound (t : ℝ) : ‖P t‖ ^ (2 : ℕ) ≤
      2 * (∫ x in (t - 1 / 2)..(t + 1 / 2), ‖P x‖ ^ (2 : ℕ)) +
        (∫ x in (t - 1 / 2)..(t + 1 / 2), ‖Q x‖ ^ (2 : ℕ)) :=
    norm_sq_le_unit_integral (by ring) ⟨by linarith, by linarith⟩ hd hQ
  have hA := sum_local_integrals_le (f := fun x => ‖P x‖ ^ (2 : ℕ)) hT hS hsep (hP.norm.pow 2) (fun x => sq_nonneg ‖P x‖)
  have hB := sum_local_integrals_le (f := fun x => ‖Q x‖ ^ (2 : ℕ)) hT hS hsep (hQ.norm.pow 2) (fun x => sq_nonneg ‖Q x‖)
  have hAP := logDirichletPolynomial_mean_square hLU N a
  have hBQ := logDirichletPolynomial_mean_square hLU N b
  have hR' : U - L + 4 * (N : ℝ) * harmonicWeight N = R := by dsimp [R, L, U]; ring
  rw [hR'] at hAP hBQ
  have hcoef : (∑ n ∈ range N, ‖b n‖ ^ (2 : ℕ)) ≤
      (log (N : ℝ)) ^ (2 : ℕ) * (∑ n ∈ range N, ‖a n‖ ^ (2 : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hn₁ : (n : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hn)
    have hfreq : logFrequency n ≤ log (N : ℝ) := log_le_log (by positivity) hn₁
    have hpos : 0 ≤ logFrequency n := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [b]
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos,
      mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpos hfreq _) (sq_nonneg _)
  change ∑ t ∈ S, ‖P t‖ ^ (2 : ℕ) ≤ _
  apply (Finset.sum_le_sum (fun t _ => hbound t)).trans
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    _ ≤ 2 * (∫ x in L..U, ‖P x‖ ^ (2 : ℕ)) + (∫ x in L..U, ‖Q x‖ ^ (2 : ℕ)) := by linarith only [hA, hB]
    _ ≤ 2 * (R * ∑ n ∈ range N, ‖a n‖ ^ (2 : ℕ)) + (R * ∑ n ∈ range N, ‖b n‖ ^ (2 : ℕ)) := by
      dsimp [P, Q]; linarith only [hAP, hBQ]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hcoef hR
      change _ ≤ R * (2 + (log (N : ℝ)) ^ (2 : ℕ)) * ∑ n ∈ range N, ‖a n‖ ^ (2 : ℕ)
      linarith only [h]

private noncomputable def truncatedMoebius (X n : ℕ) : ℂ :=
  if n ≤ X then (ArithmeticFunction.moebius n : ℂ) else 0

private noncomputable def moebiusPolynomial (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range X, (ArithmeticFunction.moebius (n + 1) : ℂ) * (((n + 1 : ℕ) : ℂ) ^ (-s))

private noncomputable def mollifiedZetaCoeff (X : ℕ) : ℕ → ℂ :=
  LSeries.convolution (1 : ℕ → ℂ) (truncatedMoebius X)

private lemma truncatedMoebius_term_support (X : ℕ) (s : ℂ) :
    ∀ n ∉ Finset.Ico 1 (X + 1), LSeries.term (truncatedMoebius X) s n = 0 := by
  intro n hn
  rcases eq_or_ne n 0 with rfl | h0
  · exact LSeries.term_zero _ _
  · have hn' : ¬n ≤ X := by
      intro hX
      exact hn (Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr h0, Nat.lt_succ_of_le hX⟩)
    rw [LSeries.term_of_ne_zero h0, truncatedMoebius, if_neg hn', zero_div]

private lemma LSeries_truncatedMoebius (X : ℕ) (s : ℂ) :
    LSeries (truncatedMoebius X) s = moebiusPolynomial X s := by
  unfold LSeries moebiusPolynomial
  rw [tsum_eq_sum (truncatedMoebius_term_support X s), Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro n hn
  have h0 : 1 + n ≠ 0 := by omega
  have hx : n + 1 ≤ X := Nat.succ_le_of_lt (Finset.mem_range.mp hn)
  rw [Nat.add_comm 1 n] at h0 ⊢
  rw [LSeries.term_of_ne_zero h0, truncatedMoebius, if_pos hx, Complex.cpow_neg, div_eq_mul_inv]

private lemma analytic_moebiusPolynomial (X : ℕ) : AnalyticOnNhd ℂ (moebiusPolynomial X) Set.univ := by
  intro s _
  unfold moebiusPolynomial
  apply Finset.analyticAt_fun_sum
  intro n _
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd : Differentiable ℂ (fun w : ℂ => ((n + 1 : ℕ) : ℂ) ^ (-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hn)
  exact analyticAt_const.mul (hd.analyticAt s)

private lemma hasSum_mollifiedZeta {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    LSeriesHasSum (mollifiedZetaCoeff X) s (riemannZeta s * moebiusPolynomial X s) := by
  have h : LSeriesSummable (truncatedMoebius X) s :=
    summable_of_ne_finset_zero (truncatedMoebius_term_support X s)
  rw [← LSeries_truncatedMoebius]
  exact (LSeriesHasSum_one hs).convolution h.LSeriesHasSum

private lemma mollifiedZetaCoeff_small {X n : ℕ} (hn : n ≤ X) :
    mollifiedZetaCoeff X n = if n = 1 then 1 else 0 := by
  have hfull : LSeries.convolution (1 : ℕ → ℂ) (fun n => (ArithmeticFunction.moebius n : ℂ)) =
      LSeries.delta := by
    rw [LSeries.one_convolution_eq_zeta_convolution]
    simp [← ArithmeticFunction.natCoe_apply, ← ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.coe_mul, ArithmeticFunction.one_eq_delta, -ArithmeticFunction.zeta_apply]
  change mollifiedZetaCoeff X n = LSeries.delta n
  rw [← hfull, mollifiedZetaCoeff, LSeries.convolution_def, LSeries.convolution_def]
  apply Finset.sum_congr rfl
  intro p hp
  have hp₂ : p.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp hp).2)
    (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp))
  rw [truncatedMoebius, if_pos (hp₂.trans hn)]

private lemma norm_mollifiedZetaCoeff_le (X n : ℕ) :
    ‖mollifiedZetaCoeff X n‖ ≤ (n.divisors.card : ℝ) := by
  rw [mollifiedZetaCoeff, LSeries.convolution_def]
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, ‖(1 : ℕ → ℂ) p.1 * truncatedMoebius X p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      rw [Pi.one_apply, one_mul, truncatedMoebius]
      split_ifs
      · rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.2)
      · simp
    _ = _ := by rw [← Nat.map_div_right_divisors]; simp

private lemma divisor_pair_encoding {n a b : ℕ} (ha : a ∈ n.divisors) (hb : b ∈ n.divisors) :
    let g := a.gcd b
    let x := a / g
    let y := b / g
    let z := n / (a.lcm b)
    (g * x) = a ∧ (g * y) = b ∧ g * x * y * z = n ∧ 0 < g ∧ 0 < x ∧ 0 < y ∧ 0 < z := by
  dsimp only
  obtain ⟨had, hn⟩ := Nat.mem_divisors.mp ha
  obtain ⟨hbd, _⟩ := Nat.mem_divisors.mp hb
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun he => hn (Nat.zero_dvd.mp (he ▸ had)))
  have hb0 : 0 < b := Nat.pos_of_ne_zero (fun he => hn (Nat.zero_dvd.mp (he ▸ hbd)))
  let g := a.gcd b
  let l := a.lcm b
  let x := a / g
  let y := b / g
  let z := n / l
  have hd₁ : g ∣ a := Nat.gcd_dvd_left a b
  have hd₂ : g ∣ b := Nat.gcd_dvd_right a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha0
  have hld : l ∣ n := Nat.lcm_dvd had hbd
  have hl : 0 < l := Nat.pos_of_ne_zero (Nat.lcm_ne_zero ha0.ne' hb0.ne')
  have hx : g * x = a := by dsimp [x]; rw [mul_comm]; exact Nat.div_mul_cancel hd₁
  have hy : g * y = b := by dsimp [y]; rw [mul_comm]; exact Nat.div_mul_cancel hd₂
  have hxy : g * x * y = l := by
    apply Nat.mul_left_cancel hg
    calc
      _ = (g * x) * (g * y) := by ring
      _ = a * b := by rw [hx, hy]
      _ = _ := (Nat.gcd_mul_lcm a b).symm
  have hz : l * z = n := by dsimp [z]; rw [mul_comm]; exact Nat.div_mul_cancel hld
  change g * x = a ∧ g * y = b ∧ g * x * y * z = n ∧ 0 < g ∧ 0 < x ∧ 0 < y ∧ 0 < z
  refine ⟨hx, hy, by rwa [hxy], hg, ?_, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd ha0 hd₁) hg
  · exact Nat.div_pos (Nat.le_of_dvd hb0 hd₂) hg
  · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hld) hl

private lemma harmonicWeight_eq_sum_Icc (N : ℕ) :
    harmonicWeight N = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  unfold harmonicWeight
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm 1 i, Nat.cast_add_one]

private lemma divisor_square_sum_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) * (harmonicWeight N) ^ (3 : ℕ) := by
  classical
  let I := Finset.Icc 1 N
  let D := I.sigma (fun n => n.divisors ×ˢ n.divisors)
  let P := (I ×ˢ (I ×ˢ (I ×ˢ I))).filter
    (fun p : ℕ × ℕ × ℕ × ℕ => p.1 * p.2.1 * p.2.2.1 * p.2.2.2 ≤ N)
  let enc (p : Σ _ : ℕ, ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
    let g := p.2.1.gcd p.2.2
    (g, p.2.1 / g, p.2.2 / g, p.1 / (p.2.1.lcm p.2.2))
  let dec (p : ℕ × ℕ × ℕ × ℕ) : Σ _ : ℕ, ℕ × ℕ :=
    ⟨p.1 * p.2.1 * p.2.2.1 * p.2.2.2, (p.1 * p.2.1, p.1 * p.2.2.1)⟩
  have henc {p : Σ _ : ℕ, ℕ × ℕ} (hp : p ∈ D) : dec (enc p) = p ∧ enc p ∈ P := by
    rcases p with ⟨n,a,b⟩
    obtain ⟨hn, hab⟩ := Finset.mem_sigma.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := divisor_pair_encoding ha hb
    have hN := (Finset.mem_Icc.mp hn).2
    have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
    have haN := (Nat.le_of_dvd hn₀ (Nat.dvd_of_mem_divisors ha)).trans hN
    have hbN := (Nat.le_of_dvd hn₀ (Nat.dvd_of_mem_divisors hb)).trans hN
    refine ⟨?_, ?_⟩
    · dsimp [dec, enc]
      rw [h₃, h₁, h₂]
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨h₄, (Nat.gcd_le_left b (Nat.pos_of_ne_zero ?_)).trans haN⟩, ?_⟩
        · intro he
          have h := Nat.dvd_of_mem_divisors ha
          rw [he] at h
          exact hn₀.ne' (Nat.zero_dvd.mp h)
        · apply Finset.mem_product.mpr
          refine ⟨Finset.mem_Icc.mpr ⟨h₅, (Nat.div_le_self a _).trans haN⟩, ?_⟩
          apply Finset.mem_product.mpr
          exact ⟨Finset.mem_Icc.mpr ⟨h₆, (Nat.div_le_self b _).trans hbN⟩,
            Finset.mem_Icc.mpr ⟨h₇, (Nat.div_le_self n _).trans hN⟩⟩
      · simpa only [enc, h₃] using hN
  have hcard : D.card ≤ P.card := by
    have hinj : Set.InjOn enc (D : Set (Σ _ : ℕ, ℕ × ℕ)) := by
      intro p hp q hq he
      rw [← (henc hp).1, ← (henc hq).1, he]
    rw [← Finset.card_image_iff.mpr hinj]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (henc hq).2
  have hD : (D.card : ℝ) = ∑ n ∈ I, (n.divisors.card : ℝ) ^ (2 : ℕ) := by
    rw [Finset.card_sigma, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.card_product, Nat.cast_mul, pow_two]
  have hP : (P.card : ℝ) = ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I,
      ((I.filter (fun d => a * b * c * d ≤ N)).card : ℝ) := by
    simp only [P, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hrow {a b c : ℕ} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) :
      ((I.filter (fun d => a * b * c * d ≤ N)).card : ℝ) ≤ (N : ℝ) / ((a : ℝ) * b * c) := by
    have hprod : 0 < a * b * c := Nat.mul_pos (Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1)
      (Finset.mem_Icc.mp hc).1
    have hsub : I.filter (fun d => a * b * c * d ≤ N) ⊆ Finset.Icc 1 (N / (a * b * c)) := by
      intro d hd
      obtain ⟨hdI, hdp⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hdI).1,
        (Nat.le_div_iff_mul_le hprod).mpr (by simpa only [Nat.mul_comm d] using hdp)⟩
    have hN := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hN
    calc
      _ ≤ ((N / (a * b * c) : ℕ) : ℝ) := by exact_mod_cast hN
      _ ≤ _ := by
        simpa only [Nat.cast_mul] using
          (Nat.cast_div_le : ((N / (a * b * c) : ℕ) : ℝ) ≤ (N : ℝ) / ((a * b * c : ℕ) : ℝ))
  calc
    _ = (D.card : ℝ) := hD.symm
    _ ≤ (P.card : ℝ) := by exact_mod_cast hcard
    _ = _ := hP
    _ ≤ ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, (N : ℝ) / ((a : ℝ) * b * c) := by
      exact Finset.sum_le_sum fun _ ha => Finset.sum_le_sum fun _ hb => Finset.sum_le_sum fun _ hc => hrow ha hb hc
    _ = _ := by
      rw [harmonicWeight_eq_sum_Icc]
      have he (a b c : ℕ) : (N : ℝ) / ((a : ℝ) * b * c) = (N : ℝ) * ((a : ℝ)⁻¹ * (b : ℝ)⁻¹ * (c : ℝ)⁻¹) := by
        rw [div_eq_mul_inv, mul_inv_rev, mul_inv_rev]
        ring
      change _ = (N : ℝ) * (∑ i ∈ I, (i : ℝ)⁻¹) ^ (3 : ℕ)
      let H := ∑ i ∈ I, (i : ℝ)⁻¹
      have hrow' (a : ℕ) :
          (∑ b ∈ I, ∑ c ∈ I, (N : ℝ) * ((a : ℝ)⁻¹ * (b : ℝ)⁻¹ * (c : ℝ)⁻¹)) =
            ((N : ℝ) * (a : ℝ)⁻¹) * (H * H) := by
        have he' (b c : ℕ) : (N : ℝ) * ((a : ℝ)⁻¹ * (b : ℝ)⁻¹ * (c : ℝ)⁻¹) =
            (((N : ℝ) * (a : ℝ)⁻¹) * (b : ℝ)⁻¹) * (c : ℝ)⁻¹ := by ring
        simp_rw [he', ← Finset.mul_sum]
        change (∑ b ∈ I, ((N : ℝ) * (a : ℝ)⁻¹ * (b : ℝ)⁻¹) * H) = _
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        change (N : ℝ) * (a : ℝ)⁻¹ * H * H = _
        ring
      simp_rw [he, hrow']
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      change (N : ℝ) * H * (H * H) = (N : ℝ) * H ^ (3 : ℕ)
      ring

private lemma norm_weighted_sum_range_le {w : ℕ → ℝ} (hw : Antitone w) (hwn : ∀ n, 0 ≤ w n)
    {a : ℕ → ℂ} {B : ℝ} {N : ℕ}
    (ha : ∀ k ≤ N, ‖∑ n ∈ range k, a n‖ ≤ B) :
    ‖∑ n ∈ range N, (w n : ℂ) * a n‖ ≤ w 0 * B := by
  let P (k : ℕ) := ∑ n ∈ range k, a n
  have he := Finset.sum_range_by_parts w a N
  simp only [Complex.real_smul] at he
  rw [he]
  change ‖(w (N - 1) : ℂ) * P N - (∑ n ∈ range (N - 1), ((w (n + 1) - w n : ℝ) : ℂ) * P (n + 1))‖ ≤ _
  apply (norm_sub_le _ _).trans
  have htop : ‖(w (N - 1) : ℂ) * P N‖ ≤ w (N - 1) * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hwn _)]
    exact mul_le_mul_of_nonneg_left (ha N le_rfl) (hwn _)
  have hsum : ‖∑ n ∈ range (N - 1), ((w (n + 1) - w n : ℝ) : ℂ) * P (n + 1)‖ ≤
      (w 0 - w (N - 1)) * B := by
    calc
      _ ≤ ∑ n ∈ range (N - 1), ‖((w (n + 1) - w n : ℝ) : ℂ) * P (n + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range (N - 1), (w n - w (n + 1)) * B := by
        apply Finset.sum_le_sum
        intro n hn
        have hle : n + 1 ≤ N := by have := Finset.mem_range.mp hn; omega
        have hd := hw (Nat.le_succ n)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hd), neg_sub]
        exact mul_le_mul_of_nonneg_left (ha (n + 1) hle) (sub_nonneg.mpr hd)
      _ = _ := by rw [← Finset.sum_mul, Finset.sum_range_sub']
  exact (add_le_add htop hsum).trans_eq (by ring)

private noncomputable def blockEnergy (f : ℕ → ℂ) (j m : ℕ) : ℝ :=
  ‖∑ n ∈ range (2 ^ j), f (m + n)‖ ^ (2 : ℕ)

private noncomputable def dyadicEnergy (f : ℕ → ℂ) : ℕ → ℕ → ℝ
  | 0, m => blockEnergy f 0 m
  | j + 1, m => blockEnergy f (j + 1) m + dyadicEnergy f j m + dyadicEnergy f j (m + 2 ^ j)

private lemma dyadicEnergy_nonneg (f : ℕ → ℂ) (j m : ℕ) : 0 ≤ dyadicEnergy f j m := by
  induction j generalizing m with
  | zero => exact sq_nonneg _
  | succ j ih => exact add_nonneg (add_nonneg (sq_nonneg _) (ih m)) (ih _)

private lemma blockEnergy_le_dyadicEnergy (f : ℕ → ℂ) (j m : ℕ) : blockEnergy f j m ≤ dyadicEnergy f j m := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    change blockEnergy f (j + 1) m ≤ blockEnergy f (j + 1) m + dyadicEnergy f j m + dyadicEnergy f j (m + 2 ^ j)
    exact (le_add_of_nonneg_right (dyadicEnergy_nonneg f j m)).trans
      (le_add_of_nonneg_right (dyadicEnergy_nonneg f j _))

private lemma weighted_square_add_le {a b r : ℝ} (hr : 0 < r) :
    (a + b) ^ (2 : ℕ) ≤ (r + 1) * (a ^ (2 : ℕ) + b ^ (2 : ℕ) / r) := by
  have h : ((r + 1) * (a ^ (2 : ℕ) + b ^ (2 : ℕ) / r) - (a + b) ^ (2 : ℕ)) * r =
      (r * a - b) ^ (2 : ℕ) := by field_simp; ring
  have hh : 0 ≤ ((r + 1) * (a ^ (2 : ℕ) + b ^ (2 : ℕ) / r) - (a + b) ^ (2 : ℕ)) * r := by
    rw [h]
    exact sq_nonneg _
  have hh := (mul_nonneg_iff_of_pos_right hr).mp hh
  linarith only [hh]

private lemma norm_prefix_sq_le_dyadicEnergy (f : ℕ → ℂ) (j m k : ℕ) (hk : k ≤ 2 ^ j) :
    ‖∑ n ∈ range k, f (m + n)‖ ^ (2 : ℕ) ≤ ((j : ℝ) + 1) * dyadicEnergy f j m := by
  induction j generalizing m k with
  | zero =>
    have hk' : k ≤ 1 := by simpa only [pow_zero] using hk
    rcases k with _ | k
    · simp only [Finset.range_zero, Finset.sum_empty, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        Nat.cast_zero, zero_add, one_mul]
      exact dyadicEnergy_nonneg f 0 m
    · obtain rfl : k = 0 := by omega
      change blockEnergy f 0 m ≤ _
      simp only [Nat.cast_zero, zero_add, one_mul, dyadicEnergy]
      exact le_rfl
  | succ j ih =>
    let r : ℝ := (j : ℝ) + 1
    have hr : 0 < r := by dsimp [r]; positivity
    let N := (2 : ℕ) ^ j
    have hN : k ≤ N + N := by rw [pow_succ] at hk; dsimp [N]; omega
    let E := dyadicEnergy f j m
    let F := dyadicEnergy f j (m + N)
    let B := blockEnergy f (j + 1) m
    have hE : 0 ≤ E := dyadicEnergy_nonneg f j m
    have hF : 0 ≤ F := dyadicEnergy_nonneg f j (m + N)
    have hB : 0 ≤ B := sq_nonneg _
    have he : ((j.succ : ℝ) + 1) * dyadicEnergy f (j.succ) m = (r + 1) * (B + E + F) := by
      simp only [r, B, E, F, N, Nat.cast_succ, dyadicEnergy]
    rw [he]
    by_cases hkn : k ≤ N
    · apply (ih m k hkn).trans
      change r * E ≤ (r + 1) * (B + E + F)
      have hBR := mul_nonneg hr.le hB
      have hFR := mul_nonneg hr.le hF
      nlinarith only [hE, hF, hB, hBR, hFR]
    · have hNk : N ≤ k := (lt_of_not_ge hkn).le
      have hK : k - N ≤ N := by omega
      let A := ∑ n ∈ range N, f (m + n)
      let C := ∑ n ∈ range (k - N), f (m + N + n)
      have hA : ‖A‖ ^ (2 : ℕ) ≤ E := blockEnergy_le_dyadicEnergy f j m
      have hC := ih (m + N) (k - N) hK
      change ‖C‖ ^ (2 : ℕ) ≤ r * F at hC
      have hsum : (∑ n ∈ range k, f (m + n)) = A + C := by
        rw [show k = N + (k - N) from (Nat.add_sub_of_le hNk).symm, Finset.sum_range_add]
        simp only [A, C, add_assoc]
      rw [hsum]
      calc
        _ ≤ (‖A‖ + ‖C‖) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _
        _ ≤ (r + 1) * (‖A‖ ^ (2 : ℕ) + ‖C‖ ^ (2 : ℕ) / r) := weighted_square_add_le hr
        _ ≤ (r + 1) * (B + E + F) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hDiv := (div_le_iff₀ hr).mpr (hC.trans_eq (mul_comm _ _))
          linarith only [hA, hB, hDiv]

private lemma sum_dyadicEnergy_le {ι : Type*} (S : Finset ι) (f : ι → ℕ → ℂ) (q : ℕ → ℝ)
    (J m : ℕ) {K : ℝ}
    (hblock : ∀ j m', m ≤ m' → m' + 2 ^ j ≤ m + 2 ^ J →
      ∑ t ∈ S, blockEnergy (f t) j m' ≤ K * ∑ n ∈ range ((2 : ℕ) ^ j), q (m' + n)) :
    ∑ t ∈ S, dyadicEnergy (f t) J m ≤ ((J : ℝ) + 1) * (K * ∑ n ∈ range ((2 : ℕ) ^ J), q (m + n)) := by
  induction J generalizing m with
  | zero => simpa only [dyadicEnergy, Nat.cast_zero, zero_add, one_mul] using hblock 0 m le_rfl le_rfl
  | succ J ih =>
    let N := (2 : ℕ) ^ J
    have he : (2 : ℕ) ^ J.succ = N + N := by rw [pow_succ]; dsimp [N]; omega
    have hbig := hblock J.succ m le_rfl le_rfl
    have h₁ := ih m (fun j m' hlo hhi =>
      hblock j m' hlo (hhi.trans (by rw [he]; exact Nat.add_le_add_left (Nat.le_add_right N N) m)))
    have h₂ := ih (m + N) (fun j m' hlo hhi =>
      hblock j m' ((Nat.le_add_right m N).trans hlo) (hhi.trans_eq (by rw [he, Nat.add_assoc])))
    have hsplit : (∑ n ∈ range ((2 : ℕ) ^ J.succ), q (m + n)) =
        (∑ n ∈ range N, q (m + n)) + ∑ n ∈ range N, q (m + N + n) := by
      rw [he, Finset.sum_range_add]
      simp only [add_assoc]
    simp only [dyadicEnergy, Finset.sum_add_distrib, Nat.cast_succ]
    rw [hsplit] at hbig ⊢
    dsimp [N] at h₂ hbig ⊢
    nlinarith only [hbig, h₁, h₂]

private noncomputable def blockPolynomial (a : ℕ → ℂ) (m k : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ range k, a (m + n) * imaginaryPhase (log ((m + n : ℕ) : ℝ)) t

private lemma sample_blockPolynomial {ι : Type*} (S : Finset ι) (u : ι → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hu : ∀ z ∈ S, |u z| ≤ T) (hsep : (S : Set ι).Pairwise (fun z w => 1 ≤ |u z - u w|))
    (a : ℕ → ℂ) {m k N : ℕ} (hm : 0 < m) (hk : m + k ≤ N + 1) :
    ∑ z ∈ S, ‖blockPolynomial a m k (u z)‖ ^ (2 : ℕ) ≤
      ((2 * T + 1) + 4 * (N : ℝ) * harmonicWeight N) * (2 + (log (N : ℝ)) ^ (2 : ℕ)) *
        ∑ n ∈ range k, ‖a (m + n)‖ ^ (2 : ℕ) := by
  classical
  let φ (i : ℕ) := m + i - 1
  let W := (range k).image φ
  let b (j : ℕ) : ℂ := if j ∈ W then a (j + 1) else 0
  have hφ (i : ℕ) : φ i + 1 = m + i := by dsimp [φ]; omega
  have hφi : Function.Injective φ := fun i j h => by dsimp [φ] at h; omega
  have hW : W ⊆ range N := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hil := Finset.mem_range.mp hi
    apply Finset.mem_range.mpr
    dsimp [φ]
    omega
  have hpoly (t : ℝ) : logDirichletPolynomial N b t = blockPolynomial a m k t := by
    unfold logDirichletPolynomial blockPolynomial
    rw [← Finset.sum_subset hW (fun j _ hj => by simp [b, hj]), Finset.sum_image (fun _ _ _ _ h => hφi h)]
    apply Finset.sum_congr rfl
    intro i hi
    have hiW : φ i ∈ W := Finset.mem_image_of_mem _ hi
    simp only [b, if_pos hiW, hφ, logFrequency]
    rw [← Nat.cast_add_one, hφ]
  have hcoef : (∑ n ∈ range N, ‖b n‖ ^ (2 : ℕ)) = ∑ n ∈ range k, ‖a (m + n)‖ ^ (2 : ℕ) := by
    rw [← Finset.sum_subset hW (fun j _ hj => by simp [b, hj]), Finset.sum_image (fun _ _ _ _ h => hφi h)]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) (by simp only [b, if_pos (show φ i ∈ W from Finset.mem_image_of_mem _ hi), hφ])
  let E := S.image u
  have hEi : Set.InjOn u (S : Set ι) := by
    intro z hz w hw heq
    by_contra hn
    have h := hsep hz hw hn
    change 1 ≤ |u z - u w| at h
    rw [heq, sub_self, abs_zero] at h
    norm_num at h
  have hEh (t : ℝ) (ht : t ∈ E) : |t| ≤ T := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
    exact hu z hz
  have hEsep : (E : Set ℝ).Pairwise (fun t v => 1 ≤ |t - v|) := by
    intro t ht v hv hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (show t ∈ E from ht)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (show v ∈ E from hv)
    exact hsep hz hw (fun he => hn (congrArg u he))
  have h := logDirichletPolynomial_sample_square hT hEh hEsep N b
  rw [hcoef] at h
  simp_rw [hpoly] at h
  rwa [Finset.sum_image (fun z hz w hw he => hEi hz hw he)] at h

private lemma sample_weighted_dyadicPolynomial {ι : Type*} (S : Finset ι) (u : ι → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hu : ∀ z ∈ S, |u z| ≤ T) (hsep : (S : Set ι).Pairwise (fun z w => 1 ≤ |u z - u w|))
    (a : ℕ → ℂ) (w : ι → ℕ → ℝ) {m j N : ℕ} (hm : 0 < m) (hj : m + 2 ^ j ≤ N + 1)
    (hw : ∀ z ∈ S, Antitone (w z)) (hwn : ∀ z ∈ S, ∀ n, 0 ≤ w z n) (hw1 : ∀ z ∈ S, w z 0 ≤ 1) :
    ∑ z ∈ S, ‖∑ n ∈ range (2 ^ j), (w z n : ℂ) * a (m + n) *
         imaginaryPhase (log ((m + n : ℕ) : ℝ)) (u z)‖ ^ (2 : ℕ) ≤
      ((j : ℝ) + 1) ^ (2 : ℕ) * (((2 * T + 1) + 4 * (N : ℝ) * harmonicWeight N) * (2 + (log (N : ℝ)) ^ (2 : ℕ))) *
        ∑ n ∈ range ((2 : ℕ) ^ j), ‖a (m + n)‖ ^ (2 : ℕ) := by
  let f (z : ι) (n : ℕ) : ℂ := a n * imaginaryPhase (log (n : ℝ)) (u z)
  let K := ((2 * T + 1) + 4 * (N : ℝ) * harmonicWeight N) * (2 + (log (N : ℝ)) ^ (2 : ℕ))
  have hpt (z : ι) (hz : z ∈ S) :
      ‖∑ n ∈ range (2 ^ j), (w z n : ℂ) * f z (m + n)‖ ^ (2 : ℕ) ≤ ((j : ℝ) + 1) * dyadicEnergy (f z) j m := by
    let E := ((j : ℝ) + 1) * dyadicEnergy (f z) j m
    have hE : 0 ≤ E := mul_nonneg (by positivity) (dyadicEnergy_nonneg _ _ _)
    have hpre (k : ℕ) (hk : k ≤ 2 ^ j) : ‖∑ n ∈ range k, f z (m + n)‖ ≤ sqrt E := by
      rw [Real.le_sqrt (norm_nonneg _) hE]
      exact norm_prefix_sq_le_dyadicEnergy (f z) j m k hk
    have h := norm_weighted_sum_range_le (hw z hz) (hwn z hz) hpre
    have hh := h.trans (mul_le_of_le_one_left (sqrt_nonneg _) (hw1 z hz))
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (sq_sqrt hE)
  have hsum : ∑ z ∈ S, dyadicEnergy (f z) j m ≤ ((j : ℝ) + 1) * (K * ∑ n ∈ range ((2 : ℕ) ^ j), ‖a (m + n)‖ ^ (2 : ℕ)) := by
    apply sum_dyadicEnergy_le S f (fun n => ‖a n‖ ^ (2 : ℕ)) j m
    intro l m' hlo hhi
    exact sample_blockPolynomial S u hT hu hsep a (hm.trans_le hlo) (hhi.trans hj)
  have hAssoc (z : ι) (n : ℕ) : (w z n : ℂ) * a (m + n) *
      imaginaryPhase (log ((m + n : ℕ) : ℝ)) (u z) = (w z n : ℂ) * f z (m + n) := by
    dsimp [f]
    ring
  simp_rw [hAssoc]
  change (∑ z ∈ S, ‖∑ n ∈ range (2 ^ j), (w z n : ℂ) * f z (m + n)‖ ^ (2 : ℕ)) ≤
    ((j : ℝ) + 1) ^ (2 : ℕ) * K * ∑ n ∈ range ((2 : ℕ) ^ j), ‖a (m + n)‖ ^ (2 : ℕ)
  apply (Finset.sum_le_sum hpt).trans
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

private lemma norm_sum_le_of_dyadic_block_bound {f : ℕ → ℂ} {N : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ j k : ℕ, (2 : ℕ) ^ j ≤ N → k ≤ 2 ^ j →
      ‖∑ n ∈ range k, f (2 ^ j + n)‖ ≤ B) :
    ‖∑ n ∈ range N, f (n + 1)‖ ≤ ((Nat.log 2 N : ℝ) + 1) * B := by
  have hmain (j : ℕ) : ‖∑ n ∈ Ico 1 (min (N + 1) ((2 : ℕ) ^ j)), f n‖ ≤ (j : ℝ) * B := by
    induction j with
    | zero => simp
    | succ j ih =>
      let m := min (N + 1) ((2 : ℕ) ^ (j + 1))
      have hm : m ≤ N + 1 := min_le_left _ _
      have hj : 0 < (2 : ℕ) ^ j := by positivity
      have hmono : (2 : ℕ) ^ j ≤ 2 ^ (j + 1) := by rw [pow_succ]; omega
      by_cases hz : (2 : ℕ) ^ j ≤ N
      · have hz' : (2 : ℕ) ^ j ≤ N + 1 := by omega
        have hmlo : (2 : ℕ) ^ j ≤ m := le_min hz' hmono
        rw [min_eq_right hz'] at ih
        have hc : m - 2 ^ j ≤ (2 : ℕ) ^ j := by
          have hh := min_le_right (N + 1) ((2 : ℕ) ^ (j + 1))
          rw [pow_succ] at hh
          dsimp [m]
          omega
        have h := hblock j (m - 2 ^ j) hz hc
        have hdiff : ‖∑ n ∈ Ico ((2 : ℕ) ^ j) m, f n‖ ≤ B := by
          rw [Finset.sum_Ico_eq_sum_range]
          simpa only [Nat.add_comm] using h
        change ‖∑ n ∈ Ico 1 m, f n‖ ≤ _
        rw [← Finset.sum_Ico_consecutive _ hj hmlo, Nat.cast_succ, add_mul, one_mul]
        exact (norm_add_le _ _).trans (add_le_add ih hdiff)
      · have hz' : N + 1 ≤ (2 : ℕ) ^ j := by omega
        rw [min_eq_left hz'] at ih
        rw [min_eq_left (hz'.trans hmono), Nat.cast_succ, add_mul, one_mul]
        exact ih.trans (le_add_of_nonneg_right hB)
  have h := hmain ((Nat.log 2 N).succ)
  rw [min_eq_left (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N), Nat.cast_succ] at h
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel] at h
  simpa only [Nat.add_comm] using h

private lemma cubic_exponent_le {u v D b δ : ℝ} (hu : 0 ≤ u) (hv : 0 < v)
    (hD : 0 < D) (hb : 0 < b) (hδ : δ ≤ D * v ^ (-(2 / 3) : ℝ)) :
    δ * u - b * u ^ (3 : ℕ) / v ^ (2 : ℕ) ≤ D * max 1 (D / b) := by
  let a := v ^ (2 / 3 : ℝ)
  let y := u / a
  let K := max 1 (D / b)
  have ha : 0 < a := Real.rpow_pos_of_pos hv _
  have hy : 0 ≤ y := div_nonneg hu ha.le
  have hc : a ^ (3 : ℕ) = v ^ (2 : ℕ) := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast hv.le]
    norm_num
  have hy3 : u ^ (3 : ℕ) / v ^ (2 : ℕ) = y ^ (3 : ℕ) := by dsimp [y]; rw [div_pow, hc]
  have hδu : δ * u ≤ D * y := by
    apply (mul_le_mul_of_nonneg_right hδ hu).trans_eq
    rw [Real.rpow_neg hv.le]
    dsimp [y, a]
    ring
  rw [mul_div_assoc, hy3]
  apply (sub_le_sub_right hδu _).trans
  by_cases hyK : y ≤ K
  · have hep := mul_le_mul_of_nonneg_left hyK hD.le
    exact (sub_le_self _ (by positivity)).trans hep
  · have h1 : 1 ≤ y := (le_max_left _ _).trans (lt_of_not_ge hyK).le
    have h2 : D ≤ y * b := (div_le_iff₀ hb).mp ((le_max_right _ _).trans (lt_of_not_ge hyK).le)
    have h3 : D * y ≤ b * y ^ (3 : ℕ) := by
      have h4 := mul_le_mul_of_nonneg_right h2 hy
      have h5 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ b * y ^ (2 : ℕ) by positivity)
      nlinarith only [h4, h5]
    apply (sub_nonpos.mpr h3).trans
    exact mul_nonneg hD.le ((zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_left _ _))

-- The dyadic exponential sum estimate used in the Vinogradov–Korobov argument.
private def ZetaOscillationEstimate : Prop :=
  ∃ b C T₀ : ℝ, 0 < b ∧ 1 ≤ C ∧ 3 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ j k : ℕ,
    (2 : ℕ) ^ j ≤ zetaCutoff t → k ≤ 2 ^ j →
    let N := (2 : ℕ) ^ j
    ‖∑ n ∈ range k, ((N + n : ℕ) : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ≤
      C * N * Real.exp (-b * Real.log (N : ℝ) ^ (3 : ℕ) / Real.log (|t| + 3) ^ (2 : ℕ))

private lemma cpow_split_re_im (s : ℂ) {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ (-s) = (((n : ℝ) ^ (-s.re) : ℝ) : ℂ) * (n : ℂ) ^ (-((s.im : ℂ) * Complex.I)) := by
  have h := Complex.re_add_im s
  have hsum : -s = (-s.re : ℝ) + -((s.im : ℂ) * Complex.I) := by
    push_cast
    rw [← neg_add, h]
  rw [hsum, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne'),
    ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

private lemma norm_zeta_of_oscillation (h : ZetaOscillationEstimate) :
    ∃ C T₀ : ℝ, 0 < C ∧ 3 ≤ T₀ ∧ ∀ s : ℂ, T₀ ≤ |s.im| → 1 / 2 ≤ s.re → s.re ≤ 2 →
      1 - s.re ≤ 8 * Real.log (|s.im| + 3) ^ (-(2 / 3) : ℝ) →
      ‖riemannZeta s‖ ≤ C * Real.log (|s.im| + 3) := by
  obtain ⟨b, C, T₀, hb, hC, hT, hmain⟩ := h
  let B := C * Real.exp (8 * max 1 (8 / b))
  let D := 4 / Real.log 2 + 1
  have hB : 0 < B := mul_pos (zero_lt_one.trans_le hC) (Real.exp_pos _)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨B * D + 5, T₀, by positivity, hT, fun s hs hσ hσ' hclose => ?_⟩
  let t := s.im
  let L := Real.log (|t| + 3)
  let N := zetaCutoff t
  let f (n : ℕ) : ℂ := (n : ℂ) ^ (-s)
  have hL : 1 ≤ L := by
    have hlog := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans
      (le_add_of_nonneg_left (abs_nonneg t)))
    rwa [Real.log_exp] at hlog
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hblock (j k : ℕ) (hj : (2 : ℕ) ^ j ≤ N) (hk : k ≤ 2 ^ j) :
      ‖∑ n ∈ range k, f (2 ^ j + n)‖ ≤ B := by
    let M := (2 : ℕ) ^ j
    let m : ℝ := M
    let w (n : ℕ) : ℝ := ((M + n : ℕ) : ℝ) ^ (-s.re)
    let a (n : ℕ) : ℂ := ((M + n : ℕ) : ℂ) ^ (-((t : ℂ) * Complex.I))
    let F := C * m * Real.exp (-b * Real.log m ^ (3 : ℕ) / L ^ (2 : ℕ))
    have hM : 0 < M := by dsimp [M]; positivity
    have hm : 0 < m := by
      change (0 : ℝ) < (M : ℝ)
      exact_mod_cast hM
    have hm1 : 1 ≤ m := by
      change (1 : ℝ) ≤ (M : ℝ)
      exact_mod_cast Nat.succ_le_of_lt hM
    have hwn (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
    have hw : Antitone w := by
      intro n l hnl
      apply rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.add_le_add_left hnl M)
      linarith only [hσ]
    have ha (l : ℕ) (hl : l ≤ k) : ‖∑ n ∈ range l, a n‖ ≤ F := hmain t hs j l hj (hl.trans hk)
    change ‖∑ n ∈ range k, f (M + n)‖ ≤ B
    simp_rw [f, fun n : ℕ => cpow_split_re_im s (Nat.add_pos_left hM n)]
    change ‖∑ n ∈ range k, (w n : ℂ) * a n‖ ≤ B
    apply (norm_weighted_sum_range_le hw hwn ha).trans
    have he : w 0 * F = C * Real.exp ((1 - s.re) * Real.log m - b * Real.log m ^ (3 : ℕ) / L ^ (2 : ℕ)) := by
      dsimp [w, F]
      change m ^ (-s.re) * (C * m * Real.exp (-b * Real.log m ^ (3 : ℕ) / L ^ (2 : ℕ))) = _
      rw [show m ^ (-s.re) * (C * m * Real.exp (-b * Real.log m ^ (3 : ℕ) / L ^ (2 : ℕ))) =
        C * ((m ^ (-s.re) * m ^ (1 : ℝ)) * Real.exp (-b * Real.log m ^ (3 : ℕ) / L ^ (2 : ℕ))) by
          rw [Real.rpow_one]; ring]
      rw [← Real.rpow_add hm, Real.rpow_def_of_pos hm, ← Real.exp_add]
      congr 2
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (cubic_exponent_le (Real.log_nonneg hm1) hL0 (by norm_num) hb hclose)) (zero_le_one.trans hC)
  have hsu := norm_sum_le_of_dyadic_block_bound hB.le hblock
  have hN := zetaCutoff_bounds t
  have hN0 : (0 : ℝ) < N := by
    nlinarith only [hN.1, abs_nonneg t, sq_nonneg |t|]
  have hNnat : N ≠ 0 := Nat.pos_iff_ne_zero.mp (by exact_mod_cast hN0)
  have hlogN : Real.log (N : ℝ) ≤ 4 * L := by
    have hbase : |t| + 4 ≤ (|t| + 3) ^ (2 : ℕ) := by
      nlinarith only [abs_nonneg t, sq_nonneg |t|]
    have hp := Real.log_le_log (by positivity : (0 : ℝ) < |t| + 4) hbase
    rw [Real.log_pow, Nat.cast_ofNat] at hp
    calc
      _ ≤ Real.log ((|t| + 4) ^ (2 : ℕ)) := Real.log_le_log hN0 (by linarith only [hN.2])
      _ = 2 * Real.log (|t| + 4) := by rw [Real.log_pow]; norm_num
      _ ≤ _ := by dsimp [L]; linarith only [hp]
  have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hNnat
  have hcount : (Nat.log 2 N : ℝ) + 1 ≤ D * L := by
    have hp := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (Nat.log 2 N)) hpow
    rw [Real.log_pow] at hp
    have hscale : (Nat.log 2 N : ℝ) ≤ (4 / Real.log 2) * L := by
      have : (Nat.log 2 N : ℝ) * Real.log 2 ≤ (4 * L) := hp.trans hlogN
      calc
        (Nat.log 2 N : ℝ) ≤ (4 * L) / Real.log 2 := (le_div_iff₀ hlog2).mpr this
        _ = _ := by ring
    dsimp [D]
    nlinarith only [hscale, hL]
  have herr := norm_zeta_sub_cutoff hσ hσ' (hT.trans hs)
  let S := ∑ n ∈ range N, f (n + 1)
  have htriangle : ‖riemannZeta s‖ ≤ ‖riemannZeta s - S‖ + ‖S‖ := by
    simpa only [sub_add_cancel] using norm_add_le (riemannZeta s - S) S
  calc
    _ ≤ 5 + ((Nat.log 2 N : ℝ) + 1) * B := htriangle.trans (add_le_add herr hsu)
    _ ≤ 5 + (D * L) * B := add_le_add_right (mul_le_mul_of_nonneg_right hcount hB.le) _
    _ ≤ _ := by nlinarith only [hL]

private lemma zetaGrowthNearOne_of_oscillation (h : ZetaOscillationEstimate) : ZetaGrowthNearOne := by
  obtain ⟨C, T, hC, hT, hnorm⟩ := norm_zeta_of_oscillation h
  have hlog : Tendsto (fun u : ℝ => Real.log (u + 3)) atTop atTop := tendsto_log_atTop.comp (by
    apply Filter.tendsto_atTop.mpr
    intro r
    filter_upwards [eventually_ge_atTop r] with u hu
    linarith only [hu])
  have hwidth : Tendsto (fun u : ℝ => Real.log (u + 3) ^ (-(2 / 3) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hlog
  have hsmall : ∀ᶠ u : ℝ in atTop, Real.log (u + 3) ^ (-(2 / 3) : ℝ) < 1 / 8 :=
    (tendsto_order.mp hwidth).2 _ (by norm_num)
  obtain ⟨U, hU⟩ := eventually_atTop.mp (hsmall.and (hlog.eventually_ge_atTop (2 * C)))
  refine ⟨2, max (T + 1) U, by norm_num, (by linarith only [hT] : 3 ≤ T + 1).trans (le_max_left _ _), ?_⟩
  intro t ht s hs
  let L := Real.log (|t| + 3)
  let l := Real.log (|s.im| + 3)
  have htl : T + 1 ≤ |t| := (le_max_left _ _).trans ht
  obtain ⟨hwidth', hL⟩ := hU _ ((le_max_right _ _).trans ht)
  have hL0 : 0 < L := Real.log_pos (by linarith only [abs_nonneg t])
  have hl0 : 0 < l := Real.log_pos (by linarith only [abs_nonneg s.im])
  have hd := Metric.mem_closedBall.mp hs
  rw [dist_eq_norm] at hd
  have hR := (Complex.abs_re_le_norm (s - (⟨1, t⟩ : ℂ))).trans hd
  have hi := (Complex.abs_im_le_norm (s - (⟨1, t⟩ : ℂ))).trans hd
  change |s.re - 1| ≤ 4 * L ^ (-(2 / 3) : ℝ) at hR
  change |s.im - t| ≤ 4 * L ^ (-(2 / 3) : ℝ) at hi
  have hmax : 4 * L ^ (-(2 / 3) : ℝ) ≤ 1 / 2 := by
    change L ^ (-(2 / 3) : ℝ) < 1 / 8 at hwidth'
    linarith only [hwidth']
  have hre := abs_le.mp (hR.trans hmax)
  have hlow : T ≤ |s.im| := by
    have habs := abs_add_le (t - s.im) s.im
    rw [sub_add_cancel, abs_sub_comm t s.im] at habs
    linarith only [habs, hi.trans hmax, htl]
  have hlogs : l ≤ 2 * L := by
    have habs := abs_add_le (s.im - t) t
    rw [sub_add_cancel] at habs
    have hb : |s.im| + 3 ≤ (|t| + 3) ^ (2 : ℕ) := by
      nlinarith only [habs, hi.trans hmax, abs_nonneg t, sq_nonneg |t|]
    simpa only [L, l, Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity : 0 < |s.im| + 3) hb
  have hwidth_comp : L ^ (-(2 / 3) : ℝ) ≤ 2 * l ^ (-(2 / 3) : ℝ) := by
    have hl2 : l / 2 ≤ L := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa [mul_comm] using hlogs)
    calc
      _ ≤ (l / 2) ^ (-(2 / 3) : ℝ) := rpow_le_rpow_of_nonpos (by positivity) hl2 (by norm_num)
      _ = (2 : ℝ) ^ (2 / 3 : ℝ) * l ^ (-(2 / 3) : ℝ) := by
        rw [Real.div_rpow hl0.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          div_inv_eq_mul, mul_comm]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (2 / 3 : ℝ) ≤ 1)).trans_eq (rpow_one 2)
  have hclose : 1 - s.re ≤ 8 * l ^ (-(2 / 3) : ℝ) := by
    have hp := (neg_le_abs (s.re - 1)).trans hR
    linarith only [hp, hwidth_comp]
  have hz := hnorm s hlow (by linarith only [hre.1]) (by linarith only [hre.2]) hclose
  calc
    _ ≤ C * l := hz
    _ ≤ C * (2 * L) := mul_le_mul_of_nonneg_left hlogs hC.le
    _ ≤ L ^ (2 : ℕ) := by
      change 2 * C ≤ L at hL
      nlinarith only [mul_le_mul_of_nonneg_right hL hL0.le]
    _ = _ := by norm_cast

private lemma exists_radius_avoiding_zeros (s : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ R ∈ Set.Ioo r (2 * r), ∀ z ∈ Metric.sphere (0 : ℂ) R, riemannZeta (s + z) ≠ 0 := by
  let E := Metric.closedBall s (2 * r) ∩ riemannZetaZeros
  have hE : E.Finite := (isCompact_closedBall s _).inter_riemannZetaZeros_finite
  let F := (fun z => dist z s) '' E
  have hF : F.Finite := hE.image _
  obtain ⟨R, hR, hRF⟩ := ((Set.Ioo_infinite (show r < 2 * r by linarith only [hr])).sdiff hF).nonempty
  refine ⟨R, hR, fun z hz hzero => ?_⟩
  have hzR : ‖z‖ = R := by simpa [dist_eq_norm] using hz
  have hD : dist (s + z) s = R := by rw [dist_eq_norm, add_sub_cancel_left, hzR]
  exact hRF ⟨s + z, ⟨Metric.mem_closedBall.mpr (hD.le.trans hR.2.le), hzero⟩, hD⟩

private lemma eventually_log_affine_le_power (P Q : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ u : ℝ in atTop, P * log u + Q ≤ u ^ (1 / 12 : ℝ) := by
  have he : 0 < (2 * (P + 1))⁻¹ := by positivity
  have hlog := (isLittleO_log_rpow_atTop (r := 1 / 12) (by norm_num)).bound he
  have hpow : Tendsto (fun u : ℝ => u ^ (1 / 12 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog, hpow.eventually_ge_atTop (2 * Q)] with u hu hl hq
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  rw [Real.norm_of_nonneg (log_nonneg hu), Real.norm_of_nonneg (rpow_nonneg hu0 _)] at hl
  have hc : P * (2 * (P + 1))⁻¹ ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < 2 * (P + 1) by positivity)).mpr
    linarith
  have hp : P * log u ≤ (1 / 2 : ℝ) * u ^ (1 / 12 : ℝ) := calc
    _ ≤ P * ((2 * (P + 1))⁻¹ * u ^ (1 / 12 : ℝ)) := mul_le_mul_of_nonneg_left hl hP
    _ = (P * (2 * (P + 1))⁻¹) * u ^ (1 / 12 : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (rpow_nonneg hu0 _)
  linarith only [hp, hq]

private lemma scaledLogDerivative_of_zetaGrowth (hg : ZetaGrowthNearOne) : ScaledLogDerivativeEstimate := by
  obtain ⟨A, T₀, hA, hT₀, hgrowth⟩ := hg
  obtain ⟨C, hC, hζlow⟩ := riemannZeta_near_one_lower
  refine ⟨1, one_pos, fun k hk => ?_⟩
  have huInf : Tendsto (fun t : ℝ => log (t + 3)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_add_three_atTop
  let P := 4 * (A + 3 / 4)
  let Q := 4 * (log C - log k + 1) + 1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpT : Tendsto (fun u : ℝ => u ^ (1 / 12 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (huInf.eventually
    ((hpT.eventually_ge_atTop (2 * k)).and (eventually_log_affine_le_power P Q hP)))
  let T' := max T₀ T
  have hT' : 0 ≤ T' := (by linarith only [hT₀] : 0 ≤ T₀).trans (le_max_left _ _)
  have hcore (t : ℝ) (ht : T' ≤ |t|) (σ : ℝ)
      (hlo : k ≤ (σ - 1) * logScale t) (hhi : (σ - 1) * logScale t ≤ 2 * k) :
      negZetaLogDeriv σ t ≤ logScale t ∧
        ∀ z : ℂ, riemannZeta z = 0 → z.re < 1 → z.im = t →
          negZetaLogDeriv σ t ≤ logScale t - (σ - z.re)⁻¹ := by
    have ht0 : T₀ ≤ |t| := (le_max_left _ _).trans ht
    have ht3 : 3 ≤ |t| := hT₀.trans ht0
    let u := log (|t| + 3)
    let r := localWidth t
    let L := logScale t
    have hu : 1 ≤ u := by
      have h := log_le_log (exp_pos 1) (exp_one_lt_three.le.trans (by linarith only [ht3] : 3 ≤ |t| + 3))
      rwa [log_exp] at h
    have hu0 : 0 < u := zero_lt_one.trans_le hu
    have hr : 0 < r := rpow_pos_of_pos hu0 _
    have hr1 : r ≤ 1 :=
      (rpow_le_rpow_of_exponent_le hu (show (-(2 / 3) : ℝ) ≤ 0 by norm_num)).trans_eq (rpow_zero u)
    have hL : 0 < L := rpow_pos_of_pos hu0 _
    have hσ : 1 < σ := by
      by_contra! hn
      exact (hk.trans_le hlo).not_ge (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn) hL.le)
    have hbox := hT |t| ((le_max_right _ _).trans ht)
    change 2 * k ≤ u ^ (1 / 12 : ℝ) ∧ P * log u + Q ≤ u ^ (1 / 12 : ℝ) at hbox
    have hrL : r * L = u ^ (1 / 12 : ℝ) := by
      change u ^ (-(2 / 3) : ℝ) * u ^ (3 / 4 : ℝ) = _
      rw [← rpow_add hu0]
      norm_num
    have hδ : σ - 1 ≤ r :=
      (mul_le_mul_iff_left₀ hL).mp (hhi.trans (hbox.1.trans_eq hrL.symm))
    have hσ2 : σ ≤ 2 := by linarith only [hδ, hr1]
    let s : ℂ := ⟨σ, t⟩
    let a : ℂ := ⟨1, t⟩
    let f (w : ℂ) : ℂ := riemannZeta (s + w)
    let M := u ^ A
    have hM : 0 < M := rpow_pos_of_pos hu0 _
    obtain ⟨R, hR, hboundary⟩ := exists_radius_avoiding_zeros s hr
    have hR0 := hr.trans hR.1
    have hR2 : R < 2 := hR.2.trans_le (by linarith only [hr1])
    have hsh : s - a = ((σ - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, a, Complex.sub_re, Complex.sub_im]
    have hfBound (w : ℂ) (hw : w ∈ Metric.closedBall 0 R) : ‖f w‖ ≤ M := by
      have hwn : ‖w‖ ≤ R := by simpa [dist_eq_norm] using hw
      apply hgrowth t ht0
      rw [Metric.mem_closedBall, dist_eq_norm, show s + w - a = (s - a) + w by ring]
      refine (norm_add_le _ _).trans ?_
      rw [hsh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ)]
      linarith only [hδ, hwn, hR.2, hr]
    have hnoPole (w : ℂ) (hw : w ∈ Metric.closedBall 0 R) : s + w ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.one_im, s] at him
      have hti : |t| = |w.im| := by rw [show t = -w.im by linarith only [him], abs_neg]
      have hnorm : ‖w‖ ≤ R := by simpa [dist_eq_norm] using hw
      have htNorm := (Complex.abs_im_le_norm w).trans hnorm
      linarith only [ht3, hti, hR2, htNorm]
    have hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) := fun w hw =>
      (analyticOn_riemannZeta (s + w) (hnoPole w hw)).comp (by fun_prop)
    have hf0 : f 0 ≠ 0 := by
      simpa [f] using (riemannZeta_ne_zero_of_one_le_re (s := s) hσ.le)
    have hleft (w : ℂ) (_ : w ∈ Metric.ball 0 R) (hw : f w = 0) : w.re ≤ 0 := by
      by_contra! hn
      apply riemannZeta_ne_zero_of_one_le_re _ hw
      rw [Complex.add_re]
      change 1 ≤ σ + w.re
      linarith only [hσ, hn]
    obtain ⟨hp, halign⟩ := disk_logDerivative_upper hR0 hM hf hf0
      (fun w hw => ⟨hboundary w hw, hfBound w (Metric.sphere_subset_closedBall hw)⟩) hleft
    have hval : -(logDeriv f 0).re = negZetaLogDeriv σ t := by
      rw [logDeriv_apply]
      change -(deriv (fun w => riemannZeta (s + w)) 0 / riemannZeta (s + 0)).re =
        (-deriv riemannZeta s / riemannZeta s).re
      rw [deriv_comp_const_add, add_zero, neg_div, Complex.neg_re]
    rw [hval] at hp halign
    have hlow : k / (C * L) ≤ ‖f 0‖ := by
      have hkL : k / L ≤ σ - 1 := (div_le_iff₀ hL).mpr hlo
      have h := hζlow s hσ hσ2
      simpa [f, div_div, mul_comm L C] using (div_le_div_of_nonneg_right hkL hC.le).trans h
    have hloglo := log_le_log (div_pos hk (mul_pos hC hL)) hlow
    have hlogL : log L = (3 / 4 : ℝ) * log u := log_rpow hu0 _
    rw [log_div hk.ne' (mul_pos hC hL).ne', log_mul hC.ne' hL.ne', hlogL] at hloglo
    have hlogM : log M = A * log u := log_rpow hu0 _
    have hmaxLog : 0 ≤ log M - log ‖f 0‖ + 1 := by
      have h := log_le_log (norm_pos_iff.mpr hf0) (hfBound 0 (Metric.mem_closedBall_self hR0.le))
      linarith only [h]
    have hbudget : 4 * (log M - log ‖f 0‖ + 1) / R + R⁻¹ ≤ L := by
      have hB : 4 * (log M - log ‖f 0‖ + 1) + 1 ≤ u ^ (1 / 12 : ℝ) := by
        have hh := hbox.2
        dsimp [P, Q] at hh
        rw [hlogM]
        linarith only [hloglo, hh]
      have hBR : 4 * (log M - log ‖f 0‖ + 1) + 1 ≤ L * R := by
        rw [← hrL] at hB
        exact hB.trans (by rw [mul_comm r]; exact mul_le_mul_of_nonneg_left hR.1.le hL.le)
      rw [← one_div, ← add_div]
      exact (div_le_iff₀ hR0).2 hBR
    refine ⟨by linarith only [hp, hbudget, inv_nonneg.mpr hR0.le], fun z hz hzre hzim => ?_⟩
    let w := z - s
    have hfw : f w = 0 := by dsimp [f, w]; rwa [add_sub_cancel]
    have hwim : w.im = 0 := by dsimp [w, s]; simp [hzim]
    have hwre : w.re = z.re - σ := rfl
    have hwneg : w.re < 0 := by rw [hwre]; linarith only [hzre, hσ]
    have hwNorm : ‖w‖ = σ - z.re := by
      have hwCast : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [hwim])
      nth_rw 1 [← hwCast]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hwneg, hwre]
      ring
    by_cases hwR : w ∈ Metric.ball 0 R
    · have h := halign w hwR hfw hwim hwneg
      rw [hwre, neg_sub] at h
      exact h.trans (sub_le_sub_right hbudget _)
    · have hd : R ≤ σ - z.re := by
        have hn : ¬ ‖w‖ < R := fun h => hwR (mem_ball_zero_iff.mpr h)
        exact (le_of_not_gt hn).trans_eq hwNorm
      have hi : (σ - z.re)⁻¹ ≤ R⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hR0 hd
      linarith only [hp, hbudget, hi]
  refine ⟨T', hT', ?_, ?_⟩
  · intro t ht σ hlo hhi
    simpa only [one_mul] using (hcore t ht σ hlo hhi).1
  · intro z hz h0 h1 ht σ hlo hhi
    simpa only [one_mul] using (hcore z.im ht σ hlo hhi).2 z hz h1 rfl

section

open Complex

private noncomputable def zpoint (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

@[simp] private lemma zpoint_re (x y : ℝ) : (zpoint x y).re = x := by simp [zpoint, Complex.mul_re]
@[simp] private lemma zpoint_im (x y : ℝ) : (zpoint x y).im = y := by simp [zpoint, Complex.mul_im]

private lemma zpoint_ne_zero_of_re {x y : ℝ} (hx : x ≠ 0) : zpoint x y ≠ 0 := by
  intro h
  exact hx (by simpa using congrArg Complex.re h)

private lemma zpoint_ne_zero_of_im {x y : ℝ} (hy : y ≠ 0) : zpoint x y ≠ 0 := by
  intro h
  exact hy (by simpa using congrArg Complex.im h)

private lemma integral_arctan_deriv {d : ℝ} (hd : d ≠ 0) (a b : ℝ) :
    (∫ t in a..b, d / (d ^ 2 + t ^ 2)) = Real.arctan (b / d) - Real.arctan (a / d) := by
  have hder (t : ℝ) : HasDerivAt (fun x : ℝ => Real.arctan (x / d)) (d / (d ^ 2 + t ^ 2)) t := by
    have h := (Real.hasDerivAt_arctan (t / d)).comp t ((hasDerivAt_id t).div_const d)
    have he : (1 / (1 + (t / d) ^ 2)) * (1 / d) = d / (d ^ 2 + t ^ 2) := by
      field_simp [hd]
    rw [← he]
    exact h
  have hcont : Continuous fun t : ℝ => d / (d ^ 2 + t ^ 2) :=
    continuous_const.div (by fun_prop) (fun t => (by positivity : 0 < d ^ 2 + t ^ 2).ne')
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) (hcont.intervalIntegrable a b)

private lemma integral_inv_vertical {d T : ℝ} (hd : d ≠ 0) :
    (∫ t in -T..T, (zpoint d t)⁻¹) = ((2 * Real.arctan (T / d) : ℝ) : ℂ) := by
  have h₁ : Continuous (fun t : ℝ => d / (d ^ 2 + t ^ 2)) :=
    continuous_const.div (by fun_prop) (fun t => (by positivity : 0 < d ^ 2 + t ^ 2).ne')
  have h₂ : Continuous (fun t : ℝ => -t / (d ^ 2 + t ^ 2)) :=
    continuous_neg.div (by fun_prop) (fun t => (by positivity : 0 < d ^ 2 + t ^ 2).ne')
  have he (t : ℝ) : (zpoint d t)⁻¹ =
      ((d / (d ^ 2 + t ^ 2) : ℝ) : ℂ) + I * ((-t / (d ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.inv_re, Complex.normSq_apply, zpoint_re, zpoint_im, Complex.add_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, sub_zero, add_zero, pow_two]
    · simp only [Complex.inv_im, Complex.normSq_apply, zpoint_re, zpoint_im, Complex.add_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, one_mul, zero_add, pow_two]
  have hodd : (∫ t in -T..T, -t / (d ^ 2 + t ^ 2)) = 0 := by
    let f (t : ℝ) := -t / (d ^ 2 + t ^ 2)
    have ih := intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
    rw [neg_neg] at ih
    change (∫ t in -T..T, f t) = 0
    have hneg (t : ℝ) : f (-t) = -f t := by simp [f, neg_div]
    simp_rw [hneg, intervalIntegral.integral_neg] at ih
    linarith only [ih]
  simp_rw [he]
  have ha : Continuous (fun t : ℝ => ((d / (d ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
    continuous_ofReal.comp h₁
  have hb : Continuous (fun t : ℝ => I * ((-t / (d ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
    continuous_const.mul (continuous_ofReal.comp h₂)
  rw [intervalIntegral.integral_add (ha.intervalIntegrable (-T) T) (hb.intervalIntegrable (-T) T),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hodd]
  rw [integral_arctan_deriv hd, neg_div, Real.arctan_neg]
  push_cast
  ring

private lemma integral_inv_horizontal_sub {a b T : ℝ} (hT : 0 < T) :
    (∫ t in a..b, (zpoint t (-T))⁻¹) - (∫ t in a..b, (zpoint t T)⁻¹) =
      (2 * I) * ((Real.arctan (b / T) - Real.arctan (a / T) : ℝ) : ℂ) := by
  have hc (w : ℝ) (hw : w ≠ 0) : Continuous (fun t => (zpoint t w)⁻¹) :=
    (by unfold zpoint; fun_prop : Continuous (fun t => zpoint t w)).inv₀
      (fun t => zpoint_ne_zero_of_im hw)
  have he (t : ℝ) : (zpoint t (-T))⁻¹ - (zpoint t T)⁻¹ =
      (2 * I) * ((T / (T ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.inv_re, Complex.normSq_apply, zpoint_re, zpoint_im, Complex.sub_re,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
        Complex.im_ofNat, Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one,
        add_zero, neg_mul_neg, sub_self]
    · simp only [Complex.inv_im, Complex.normSq_apply, zpoint_re, zpoint_im, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
        Complex.im_ofNat, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        neg_neg, add_zero, sub_zero, zero_add, neg_mul_neg, pow_two]
      ring
  rw [← intervalIntegral.integral_sub ((hc (-T) (neg_ne_zero.mpr hT.ne')).intervalIntegrable a b)
    ((hc T hT.ne').intervalIntegrable a b)]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, integral_arctan_deriv hT.ne']

private noncomputable def rectIntegral (a b T : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ t in a..b, f (zpoint t (-T))) - (∫ t in a..b, f (zpoint t T)) +
    I * (∫ t in -T..T, f (zpoint b t)) - I * (∫ t in -T..T, f (zpoint a t))

private lemma rectIntegral_inv {a b T : ℝ} (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    rectIntegral a b T (fun s => s⁻¹) = 2 * (Real.pi : ℂ) * I := by
  have hap : 0 < -a := neg_pos.mpr ha
  have hpos (d : ℝ) (hd : 0 < d) : Real.arctan (d / T) + Real.arctan (T / d) = Real.pi / 2 := by
    rw [show T / d = (d / T)⁻¹ by field_simp, Real.arctan_inv_of_pos (div_pos hd hT)]
    ring
  have hneg : Real.arctan (a / T) + Real.arctan (T / a) = -(Real.pi / 2) := by
    have h := hpos (-a) hap
    rw [neg_div, div_neg, Real.arctan_neg, Real.arctan_neg] at h
    linarith only [h]
  rw [rectIntegral, integral_inv_horizontal_sub hT, integral_inv_vertical ha.ne, integral_inv_vertical hb.ne']
  have hSum : (Real.arctan (b / T) + Real.arctan (T / b)) -
      (Real.arctan (a / T) + Real.arctan (T / a)) = Real.pi := by rw [hpos b hb, hneg]; ring
  have hcast := congrArg ((↑) : ℝ → ℂ) hSum
  push_cast at hcast ⊢
  linear_combination (2 * I) * hcast

private noncomputable def perronIntegrand (v : ℝ) (s : ℂ) : ℂ := Complex.exp ((v : ℂ) * s) / s

private lemma continuous_perron_horizontal (v : ℝ) {T : ℝ} (hT : T ≠ 0) :
    Continuous (fun t => perronIntegrand v (zpoint t T)) := by
  unfold perronIntegrand
  exact (by unfold zpoint; fun_prop : Continuous (fun t => Complex.exp ((v : ℂ) * zpoint t T))).div
    (by unfold zpoint; fun_prop) (fun _ => zpoint_ne_zero_of_im hT)

private lemma continuous_perron_vertical (v : ℝ) {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun t => perronIntegrand v (zpoint c t)) := by
  unfold perronIntegrand
  exact (by unfold zpoint; fun_prop : Continuous (fun t => Complex.exp ((v : ℂ) * zpoint c t))).div
    (by unfold zpoint; fun_prop) (fun _ => zpoint_ne_zero_of_re hc)

private lemma rectIntegral_eq_zero {a b T : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f ([[a, b]] ×ℂ [[-T, T]])) :
    rectIntegral a b T f = 0 := by
  have hd : DifferentiableOn ℂ f ([[ (zpoint a (-T)).re, (zpoint b T).re ]] ×ℂ
      [[ (zpoint a (-T)).im, (zpoint b T).im ]]) := by simpa only [zpoint_re, zpoint_im] using hf
  simpa [rectIntegral, zpoint_re, zpoint_im, zpoint, smul_eq_mul] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (zpoint a (-T)) (zpoint b T) hd)

private noncomputable def rectIntegralBetween (a b c d : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ t in a..b, f (zpoint t c)) - (∫ t in a..b, f (zpoint t d)) +
    I * (∫ t in c..d, f (zpoint b t)) - I * (∫ t in c..d, f (zpoint a t))

private lemma rectIntegralBetween_eq_zero {a b c d : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f ([[a, b]] ×ℂ [[c, d]])) :
    rectIntegralBetween a b c d f = 0 := by
  have hd : DifferentiableOn ℂ f ([[ (zpoint a c).re, (zpoint b d).re ]] ×ℂ
      [[ (zpoint a c).im, (zpoint b d).im ]]) := by simpa only [zpoint_re, zpoint_im] using hf
  simpa [rectIntegralBetween, zpoint_re, zpoint_im, zpoint, smul_eq_mul] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (zpoint a c) (zpoint b d) hd)

private lemma rectIntegralBetween_add_adjacent {a b c d e : ℝ} {f : ℂ → ℂ}
    (ha₁ : IntervalIntegrable (fun t => f (zpoint a t)) MeasureTheory.volume c d)
    (ha₂ : IntervalIntegrable (fun t => f (zpoint a t)) MeasureTheory.volume d e)
    (hb₁ : IntervalIntegrable (fun t => f (zpoint b t)) MeasureTheory.volume c d)
    (hb₂ : IntervalIntegrable (fun t => f (zpoint b t)) MeasureTheory.volume d e) :
    rectIntegralBetween a b c d f + rectIntegralBetween a b d e f =
      rectIntegralBetween a b c e f := by
  unfold rectIntegralBetween
  rw [← intervalIntegral.integral_add_adjacent_intervals ha₁ ha₂,
    ← intervalIntegral.integral_add_adjacent_intervals hb₁ hb₂]
  ring

private lemma rectIntegralBetween_inv_eq_zero {a b c d : ℝ} (h : (0 : ℝ) ∉ [[c, d]]) :
    rectIntegralBetween a b c d (fun s => s⁻¹) = 0 := by
  apply rectIntegralBetween_eq_zero
  intro z hz
  have hn : z ≠ 0 := by
    rintro rfl
    exact h (by simpa using hz.2)
  exact (differentiableAt_id.inv hn).differentiableWithinAt

private lemma rectIntegralBetween_inv {a b c d : ℝ} (ha : a < 0) (hb : 0 < b)
    (hc : c < 0) (hd : 0 < d) :
    rectIntegralBetween a b c d (fun s => s⁻¹) = 2 * (Real.pi : ℂ) * I := by
  let T := min (-c) d
  have hT : 0 < T := lt_min (neg_pos.mpr hc) hd
  have hcT : c ≤ -T := le_neg.mpr (min_le_left _ _)
  have hTd : T ≤ d := min_le_right _ _
  have hcont (x : ℝ) (hx : x ≠ 0) : Continuous (fun t => (zpoint x t)⁻¹) :=
    (by unfold zpoint; fun_prop : Continuous (fun t => zpoint x t)).inv₀
      (fun _ => zpoint_ne_zero_of_re hx)
  have hadd (u v w : ℝ) := rectIntegralBetween_add_adjacent
      ((hcont a ha.ne).intervalIntegrable u v) ((hcont a ha.ne).intervalIntegrable v w)
      ((hcont b hb.ne').intervalIntegrable u v) ((hcont b hb.ne').intervalIntegrable v w)
  have hleft : rectIntegralBetween a b c (-T) (fun s => s⁻¹) = 0 := by
    apply rectIntegralBetween_inv_eq_zero
    rw [Set.uIcc_of_le hcT]
    exact fun h => (neg_lt_zero.mpr hT).not_ge h.2
  have hright : rectIntegralBetween a b T d (fun s => s⁻¹) = 0 := by
    apply rectIntegralBetween_inv_eq_zero
    rw [Set.uIcc_of_le hTd]
    exact fun h => hT.not_ge h.1
  have hmid : rectIntegralBetween a b (-T) T (fun s => s⁻¹) = 2 * (Real.pi : ℂ) * I :=
    rectIntegral_inv ha hb hT
  have h₁ := hadd c (-T) T
  have h₂ := hadd c T d
  rw [hleft, hmid, zero_add] at h₁
  rw [← h₁, hright, add_zero] at h₂
  exact h₂.symm

private lemma rectIntegral_sub_inv {a b T : ℝ} {w : ℂ} (ha : a < w.re) (hb : w.re < b)
    (hlo : -T < w.im) (hhi : w.im < T) :
    rectIntegral a b T (fun s => (s - w)⁻¹) = 2 * (Real.pi : ℂ) * I := by
  have hz (x y : ℝ) : zpoint x y - w = zpoint (x - w.re) (y - w.im) :=
    Complex.ext (by simp) (by simp)
  unfold rectIntegral
  simp_rw [hz]
  rw [intervalIntegral.integral_comp_sub_right (f := fun t => (zpoint t (-T - w.im))⁻¹),
    intervalIntegral.integral_comp_sub_right (f := fun t => (zpoint t (T - w.im))⁻¹),
    intervalIntegral.integral_comp_sub_right (f := fun t => (zpoint (b - w.re) t)⁻¹),
    intervalIntegral.integral_comp_sub_right (f := fun t => (zpoint (a - w.re) t)⁻¹)]
  exact rectIntegralBetween_inv (sub_neg.mpr ha) (sub_pos.mpr hb) (sub_neg.mpr hlo) (sub_pos.mpr hhi)

private lemma analytic_remainder_of_principal_parts {U : Set ℂ} (S : Finset ℂ)
    (f : ℂ → ℂ) (c : ℂ → ℂ) (hf : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z)
    (hpart : ∀ w ∈ S, ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧
      f =ᶠ[𝓝[≠] w] fun z => c w * (z - w)⁻¹ + g z) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      ∀ z ∈ U, z ∉ S → f z = G z + ∑ w ∈ S, c w * (z - w)⁻¹ := by
  classical
  let P (w z : ℂ) := c w * (z - w)⁻¹
  let F (z : ℂ) := f z - ∑ w ∈ S, P w z
  let G (z : ℂ) := if z ∈ S then limUnder (𝓝[≠] z) F else F z
  have hp (w z : ℂ) (hw : z ≠ w) : AnalyticAt ℂ (P w) z :=
    analyticAt_const.mul ((by fun_prop : AnalyticAt ℂ (fun v : ℂ => v - w) z).inv (sub_ne_zero.mpr hw))
  have hoff {K : Finset ℂ} {z : ℂ} (hz : z ∉ K) : ∀ᶠ v in 𝓝 z, v ∉ K :=
    K.finite_toSet.isClosed.isOpen_compl.mem_nhds hz
  refine ⟨G, ?_, fun z _ hz => ?_⟩
  · intro w hwU
    by_cases hw : w ∈ S
    · obtain ⟨g, hg, heq⟩ := hpart w hw
      let R (z : ℂ) := g z - ∑ k ∈ S.erase w, P k z
      have hR : AnalyticAt ℂ R w := hg.sub ((S.erase w).analyticAt_fun_sum fun k hk =>
        hp k w (Ne.symm (Finset.mem_erase.mp hk).1))
      have hF : F =ᶠ[𝓝[≠] w] R := by
        filter_upwards [heq] with z hz
        change f z = P w z + g z at hz
        change f z - ∑ k ∈ S, P k z = g z - ∑ k ∈ S.erase w, P k z
        rw [hz, ← Finset.sum_erase_add _ _ hw]
        ring
      have hG : R =ᶠ[𝓝[≠] w] G := by
        filter_upwards [hF, (nhdsWithin_le_nhds : 𝓝[≠] w ≤ 𝓝 w) (hoff (Finset.notMem_erase w S)),
          self_mem_nhdsWithin] with z he hz hwz
        have hzS : z ∉ S := fun h => hz (Finset.mem_erase.mpr ⟨hwz, h⟩)
        simpa only [G, if_neg hzS] using he.symm
      have hlim : limUnder (𝓝[≠] w) F = R w :=
        ((hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hF.symm).limUnder_eq
      apply hR.congr
      rw [← nhdsNE_sup_pure w, Filter.EventuallyEq, Filter.eventually_sup]
      exact ⟨hG, by simp [G, hw, hlim]⟩
    · have hF : AnalyticAt ℂ F w := (hf w hwU hw).sub (S.analyticAt_fun_sum fun k hk =>
        hp k w (fun h => hw (h ▸ hk)))
      exact hF.congr (by filter_upwards [hoff hw] with z hz; simp [G, hz])
  · simp [G, hz, F, P]

private lemma integral_eq_with_principal_parts {u v : ℝ} {S : Finset ℂ} {f G : ℂ → ℂ}
    {r : ℂ → ℂ} {p : ℝ → ℂ} (hp : Continuous p)
    (hG : ∀ t ∈ [[u, v]], AnalyticAt ℂ G (p t))
    (hS : ∀ t ∈ [[u, v]], p t ∉ S)
    (heq : ∀ t ∈ [[u, v]], f (p t) = G (p t) + ∑ w ∈ S, r w * (p t - w)⁻¹) :
    (∫ t in u..v, f (p t)) = (∫ t in u..v, G (p t)) +
      ∑ w ∈ S, r w * ∫ t in u..v, (p t - w)⁻¹ := by
  have hGc : ContinuousOn (fun t => G (p t)) [[u, v]] := fun t ht =>
    ((hG t ht).continuousAt.comp hp.continuousAt).continuousWithinAt
  have hI (w : ℂ) (hw : w ∈ S) : ContinuousOn (fun t => (p t - w)⁻¹) [[u, v]] :=
    (hp.sub continuous_const).continuousOn.inv₀ fun t ht =>
      sub_ne_zero.mpr (fun h => hS t ht (h.symm ▸ hw))
  have hterm (w : ℂ) (hw : w ∈ S) :
      IntervalIntegrable (fun t => r w * (p t - w)⁻¹) MeasureTheory.volume u v :=
    (continuousOn_const.mul (hI w hw)).intervalIntegrable
  calc
    _ = ∫ t in u..v, G (p t) + ∑ w ∈ S, r w * (p t - w)⁻¹ := intervalIntegral.integral_congr heq
    _ = _ := by
      have hsum : IntervalIntegrable (fun t => ∑ w ∈ S, r w * (p t - w)⁻¹)
          MeasureTheory.volume u v := by
        have hfun : (fun t => ∑ w ∈ S, r w * (p t - w)⁻¹) =
            ∑ w ∈ S, (fun t => r w * (p t - w)⁻¹) := by
          funext t
          simp only [Finset.sum_apply]
        rw [hfun]
        exact IntervalIntegrable.sum S hterm
      rw [intervalIntegral.integral_add hGc.intervalIntegrable hsum,
        intervalIntegral.integral_finsetSum hterm]
      simp_rw [intervalIntegral.integral_const_mul]

private lemma rectIntegral_eq_sum_residues {a b T : ℝ}
    (S : Finset ℂ) (f r : ℂ → ℂ)
    (hS : ∀ w ∈ S, a < w.re ∧ w.re < b ∧ -T < w.im ∧ w.im < T)
    (hf : ∀ z ∈ ([[a, b]] ×ℂ [[-T, T]]), z ∉ S → AnalyticAt ℂ f z)
    (hpart : ∀ w ∈ S, ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧
      f =ᶠ[𝓝[≠] w] fun z => r w * (z - w)⁻¹ + g z) :
    rectIntegral a b T f = (2 * (Real.pi : ℂ) * I) * ∑ w ∈ S, r w := by
  obtain ⟨G, hG, heq⟩ := analytic_remainder_of_principal_parts S f r hf hpart
  have horiz (y : ℝ) (hy : y = -T ∨ y = T) :
      (∫ t in a..b, f (zpoint t y)) = (∫ t in a..b, G (zpoint t y)) +
        ∑ w ∈ S, r w * ∫ t in a..b, (zpoint t y - w)⁻¹ := by
    have hmem (t : ℝ) (ht : t ∈ [[a, b]]) : zpoint t y ∈ ([[a, b]] ×ℂ [[-T, T]]) := by
      refine ⟨by simpa only [Set.mem_preimage, zpoint_re] using ht, ?_⟩
      change (zpoint t y).im ∈ [[-T, T]]
      rw [zpoint_im]
      rcases hy with rfl | rfl
      · exact Set.left_mem_uIcc
      · exact Set.right_mem_uIcc
    have hnot (t : ℝ) : zpoint t y ∉ S := by
      intro h
      obtain ⟨_, _, hlo, hhi⟩ := hS _ h
      rw [zpoint_im] at hlo hhi
      rcases hy with rfl | rfl
      · exact (lt_irrefl _) hlo
      · exact (lt_irrefl _) hhi
    exact integral_eq_with_principal_parts (by unfold zpoint; fun_prop)
      (fun t ht => hG _ (hmem t ht)) (fun t _ => hnot t)
      (fun t ht => heq _ (hmem t ht) (hnot t))
  have vert (x : ℝ) (hx : x = a ∨ x = b) :
      (∫ t in -T..T, f (zpoint x t)) = (∫ t in -T..T, G (zpoint x t)) +
        ∑ w ∈ S, r w * ∫ t in -T..T, (zpoint x t - w)⁻¹ := by
    have hmem (t : ℝ) (ht : t ∈ [[-T, T]]) : zpoint x t ∈ ([[a, b]] ×ℂ [[-T, T]]) := by
      refine ⟨?_, by simpa only [Set.mem_preimage, zpoint_im] using ht⟩
      change (zpoint x t).re ∈ [[a, b]]
      rw [zpoint_re]
      rcases hx with rfl | rfl
      · exact Set.left_mem_uIcc
      · exact Set.right_mem_uIcc
    have hnot (t : ℝ) : zpoint x t ∉ S := by
      intro h
      obtain ⟨hlo, hhi, _, _⟩ := hS _ h
      rw [zpoint_re] at hlo hhi
      rcases hx with rfl | rfl
      · exact (lt_irrefl _) hlo
      · exact (lt_irrefl _) hhi
    exact integral_eq_with_principal_parts (by unfold zpoint; fun_prop)
      (fun t ht => hG _ (hmem t ht)) (fun t _ => hnot t)
      (fun t ht => heq _ (hmem t ht) (hnot t))
  have hsum : rectIntegral a b T f = rectIntegral a b T G +
      ∑ w ∈ S, r w * rectIntegral a b T (fun z => (z - w)⁻¹) := by
    unfold rectIntegral
    rw [horiz (-T) (Or.inl rfl), horiz T (Or.inr rfl), vert b (Or.inr rfl), vert a (Or.inl rfl)]
    have hcomm (w v : ℂ) : r w * (I * v) = I * (r w * v) := by ring
    simp only [mul_sub, mul_add, hcomm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hsum, rectIntegral_eq_zero hG.differentiableOn, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hS w hw
  rw [rectIntegral_sub_inv h₁ h₂ h₃ h₄, mul_comm]

private lemma rectIntegral_perron_of_pos {a b T : ℝ} (ha : 0 < a) (hab : a ≤ b) (v : ℝ) :
    rectIntegral a b T (perronIntegrand v) = 0 := by
  apply rectIntegral_eq_zero
  intro z hz
  have hre : a ≤ z.re := by
    have h : z.re ∈ [[a, b]] := hz.1
    rw [Set.uIcc_of_le hab] at h
    exact h.1
  have hn : z ≠ 0 := by rintro rfl; simp at hre; linarith only [ha, hre]
  exact ((by fun_prop : DifferentiableAt ℂ (fun w => Complex.exp ((v : ℂ) * w)) z).div
    differentiableAt_id hn).differentiableWithinAt

private lemma rectIntegral_perron_cross {a b T : ℝ} (ha : a < 0) (hb : 0 < b) (hT : 0 < T)
    (v : ℝ) : rectIntegral a b T (perronIntegrand v) = 2 * (Real.pi : ℂ) * I := by
  let F (s : ℂ) := Complex.exp ((v : ℂ) * s)
  let G := dslope F 0
  have hd : DifferentiableOn ℂ G Set.univ :=
    (Complex.differentiableOn_dslope (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝 0)).mpr
      (by unfold F; fun_prop)
  have he (s : ℂ) (hs : s ≠ 0) : G s = perronIntegrand v s - s⁻¹ := by
    rw [show G = dslope F 0 from rfl, dslope_of_ne F hs, slope_def_field]
    simp only [F, mul_zero, Complex.exp_zero, sub_zero, perronIntegrand]
    rw [sub_div, one_div]
  have hh1 := funext fun t : ℝ => he (zpoint t (-T)) (zpoint_ne_zero_of_im (neg_ne_zero.mpr hT.ne'))
  have hh2 := funext fun t : ℝ => he (zpoint t T) (zpoint_ne_zero_of_im hT.ne')
  have hv1 := funext fun t : ℝ => he (zpoint b t) (zpoint_ne_zero_of_re hb.ne')
  have hv2 := funext fun t : ℝ => he (zpoint a t) (zpoint_ne_zero_of_re ha.ne)
  have hInvH (y : ℝ) (hy : y ≠ 0) : Continuous (fun t => (zpoint t y)⁻¹) :=
    (by unfold zpoint; fun_prop : Continuous (fun t => zpoint t y)).inv₀ (fun _ => zpoint_ne_zero_of_im hy)
  have hInvV (x : ℝ) (hx : x ≠ 0) : Continuous (fun t => (zpoint x t)⁻¹) :=
    (by unfold zpoint; fun_prop : Continuous (fun t => zpoint x t)).inv₀ (fun _ => zpoint_ne_zero_of_re hx)
  have hg : rectIntegral a b T G = 0 := rectIntegral_eq_zero (hd.mono (Set.subset_univ _))
  unfold rectIntegral at hg
  rw [hh1, hh2, hv1, hv2] at hg
  rw [intervalIntegral.integral_sub
    ((continuous_perron_horizontal v (neg_ne_zero.mpr hT.ne')).intervalIntegrable a b)
    ((hInvH _ (neg_ne_zero.mpr hT.ne')).intervalIntegrable a b),
    intervalIntegral.integral_sub ((continuous_perron_horizontal v hT.ne').intervalIntegrable a b)
      ((hInvH _ hT.ne').intervalIntegrable a b),
    intervalIntegral.integral_sub ((continuous_perron_vertical v hb.ne').intervalIntegrable (-T) T)
      ((hInvV _ hb.ne').intervalIntegrable (-T) T),
    intervalIntegral.integral_sub ((continuous_perron_vertical v ha.ne).intervalIntegrable (-T) T)
      ((hInvV _ ha.ne).intervalIntegrable (-T) T)] at hg
  have hsub : rectIntegral a b T (perronIntegrand v) - rectIntegral a b T (fun s => s⁻¹) = 0 := by
    unfold rectIntegral
    linear_combination hg
  exact (sub_eq_zero.mp hsub).trans (rectIntegral_inv ha hb hT)

private lemma norm_perron_integrand {s : ℂ} (v : ℝ) :
    ‖perronIntegrand v s‖ = Real.exp (v * s.re) / ‖s‖ := by
  unfold perronIntegrand
  rw [norm_div, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

private lemma integral_exp_affine {v : ℝ} (hv : v ≠ 0) (a b : ℝ) :
    (∫ t in a..b, Real.exp (v * t)) = (Real.exp (v * b) - Real.exp (v * a)) / v := by
  have hd (t : ℝ) : HasDerivAt (fun s => Real.exp (v * s) / v) (Real.exp (v * t)) t := by
    have h := (((hasDerivAt_id t).const_mul v).exp).div_const v
    simpa only [id_eq, mul_one, mul_div_cancel_right₀ _ hv] using h
  have hc : Continuous (fun t => Real.exp (v * t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable a b), sub_div]

private lemma norm_perron_horizontal {v a b y T : ℝ} (hab : a ≤ b) (hT : 0 < T)
    (hy : |y| = T) (hv : v ≠ 0) :
    ‖∫ t in a..b, perronIntegrand v (zpoint t y)‖ ≤
      ((Real.exp (v * b) - Real.exp (v * a)) / v) / T := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith only [hy, hT]
  have hc : Continuous (fun t => Real.exp (v * t) / T) := by fun_prop
  have hb (t : ℝ) : ‖perronIntegrand v (zpoint t y)‖ ≤ Real.exp (v * t) / T := by
    rw [norm_perron_integrand, zpoint_re]
    have hyn := Complex.abs_im_le_norm (zpoint t y)
    rw [zpoint_im, hy] at hyn
    exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hT hyn
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hab
    (f := fun t => perronIntegrand v (zpoint t y))
    (g := fun t => Real.exp (v*t) / T)
    (Filter.Eventually.of_forall fun t _ => hb t) (hc.intervalIntegrable a b)
  rw [intervalIntegral.integral_div, integral_exp_affine hv] at h
  exact h

private lemma norm_perron_vertical {v c T : ℝ} (hc : c ≠ 0) (hT : 0 < T) :
    ‖I * ∫ t in -T..T, perronIntegrand v (zpoint c t)‖ ≤
      (2 * T) * Real.exp (v * c) / |c| := by
  rw [norm_mul, Complex.norm_I, one_mul]
  have hnorm (t : ℝ) : ‖perronIntegrand v (zpoint c t)‖ ≤ Real.exp (v * c) / |c| := by
    rw [norm_perron_integrand, zpoint_re]
    apply div_le_div_of_nonneg_left (Real.exp_nonneg _) (abs_pos.mpr hc)
    simpa only [zpoint_re] using Complex.abs_re_le_norm (zpoint c t)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hnorm t)
    (a := -T) (b := T)
  rw [show T - (-T) = 2 * T by ring, abs_of_pos (by positivity : 0 < 2 * T)] at h
  exact h.trans_eq (by ring)

private noncomputable def perronVertical (v c T : ℝ) : ℂ :=
  I * ∫ t in -T..T, perronIntegrand v (zpoint c t)

private lemma norm_vertical_diff_sub_rectangle (a b T v : ℝ) :
    ‖perronVertical v b T - perronVertical v a T - rectIntegral a b T (perronIntegrand v)‖ ≤
      ‖∫ t in a..b, perronIntegrand v (zpoint t (-T))‖ +
      ‖∫ t in a..b, perronIntegrand v (zpoint t T)‖ := by
  unfold perronVertical rectIntegral
  rw [show _ - _ - (_ - _ + _ - _) =
    (∫ t in a..b, perronIntegrand v (zpoint t T)) -
      (∫ t in a..b, perronIntegrand v (zpoint t (-T))) by ring]
  exact (norm_sub_le _ _).trans_eq (add_comm _ _)

private lemma le_of_all_pos_error {x y : ℝ} (h : ∀ ε > 0, x ≤ y + ε) : x ≤ y := by
  by_contra! hn
  linarith only [h ((x - y) / 2) (by linarith only [hn]), hn]

private lemma perronVertical_error {v c T : ℝ} (hv : v ≠ 0) (hc : 0 < c) (hT : 0 < T) :
    ‖perronVertical v c T - (if 0 < v then 2 * (Real.pi : ℂ) * I else 0)‖ ≤
      2 * (Real.exp (v * c) / (T * |v|)) := by
  apply le_of_all_pos_error
  intro ε hε
  let B := Real.exp (v * c) / (T * |v|)
  let L := 2 * T / ε + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hεL : 2 * T ≤ ε * L := by
    dsimp [L]
    have hh : ε * (2 * T / ε) = 2 * T := by field_simp
    linarith only [show ε * (2 * T / ε + 1) = ε * (2 * T / ε) + ε by ring, hh, hε]
  have hlim {s : ℝ} (hs : L ≤ |s|) (hvs : v * s ≤ 0) : ‖perronVertical v s T‖ ≤ ε := by
    have hsn : s ≠ 0 := by rintro rfl; simp at hs; linarith only [hs, hL]
    apply (norm_perron_vertical hsn hT).trans
    apply (div_le_iff₀ (abs_pos.mpr hsn)).mpr
    have he := Real.exp_le_one_iff.mpr hvs
    have h₁ := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * T)
    have h₂ := mul_le_mul_of_nonneg_left hs hε.le
    linarith only [h₁, h₂, hεL]
  rcases lt_or_gt_of_ne hv with hvn | hvp
  · rw [if_neg hvn.not_gt, sub_zero]
    let d := c + L
    have hcd : c ≤ d := le_add_of_nonneg_right hL.le
    have hd : 0 < d := hc.trans_le hcd
    have hfar : ‖perronVertical v d T‖ ≤ ε :=
      hlim (by rw [abs_of_pos hd]; dsimp [d]; linarith only [hc])
        (mul_nonpos_of_nonpos_of_nonneg hvn.le hd.le)
    have he := rectIntegral_perron_of_pos (T := T) hc hcd v
    have hhor (y : ℝ) (hy : |y| = T) :
        ‖∫ t in c..d, perronIntegrand v (zpoint t y)‖ ≤ B := by
      apply (norm_perron_horizontal hcd hT hy hv).trans
      apply (div_le_iff₀ hT).mpr
      have hh : (Real.exp (v * d) - Real.exp (v * c)) / v ≤ Real.exp (v * c) / (-v) := by
        have heq : (Real.exp (v * d) - Real.exp (v * c)) / v =
            (Real.exp (v * c) - Real.exp (v * d)) / (-v) := by rw [← neg_sub, neg_div, div_neg]
        rw [heq]
        exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_nonneg _)) (neg_nonneg.mpr hvn.le)
      have hh₂ : B * T = Real.exp (v * c) / (-v) := by
        dsimp [B]
        rw [abs_of_neg hvn]
        field_simp
      exact hh.trans_eq hh₂.symm
    have hdiff := norm_vertical_diff_sub_rectangle c d T v
    rw [he, sub_zero, norm_sub_rev] at hdiff
    have hbound : ‖perronVertical v c T - perronVertical v d T‖ ≤ 2 * B := by
      have hp := hhor T (abs_of_pos hT)
      have hn := hhor (-T) (by rw [abs_neg, abs_of_pos hT])
      linarith only [hdiff, hp, hn]
    change ‖perronVertical v c T‖ ≤ 2 * B + ε
    calc
      _ = ‖(perronVertical v c T - perronVertical v d T) + perronVertical v d T‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hbound hfar)
  · rw [if_pos hvp]
    let d := -L
    have hd : d < 0 := neg_neg_of_pos hL
    have hdc : d ≤ c := hd.le.trans hc.le
    have hfar : ‖perronVertical v d T‖ ≤ ε :=
      hlim (by rw [abs_of_neg hd]; exact neg_neg L |>.ge)
        (mul_nonpos_of_nonneg_of_nonpos hvp.le hd.le)
    have he := rectIntegral_perron_cross hd hc hT v
    have hhor (y : ℝ) (hy : |y| = T) :
        ‖∫ t in d..c, perronIntegrand v (zpoint t y)‖ ≤ B := by
      apply (norm_perron_horizontal hdc hT hy hv).trans
      apply (div_le_iff₀ hT).mpr
      have hh := div_le_div_of_nonneg_right
        (sub_le_self (Real.exp (v * c)) (Real.exp_nonneg (v * d))) hvp.le
      have hh₂ : B * T = Real.exp (v * c) / v := by
        dsimp [B]
        rw [abs_of_pos hvp]
        field_simp
      exact hh.trans_eq hh₂.symm
    have hdiff := norm_vertical_diff_sub_rectangle d c T v
    rw [he] at hdiff
    have hbound : ‖perronVertical v c T - perronVertical v d T - 2 * (Real.pi : ℂ) * I‖ ≤ 2 * B := by
      have hp := hhor T (abs_of_pos hT)
      have hn := hhor (-T) (by rw [abs_neg, abs_of_pos hT])
      linarith only [hdiff, hp, hn]
    change ‖perronVertical v c T - 2 * (Real.pi : ℂ) * I‖ ≤ 2 * B + ε
    calc
      _ = ‖(perronVertical v c T - perronVertical v d T - 2 * (Real.pi : ℂ) * I) +
          perronVertical v d T‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hbound hfar)

private noncomputable def quadraticPerronKernel (v : ℝ) (s : ℂ) : ℂ :=
  (2 * Complex.exp ((v : ℂ) * s)) / (s * (s + 1) * (s + 2))

private lemma zpoint_add_real (c t d : ℝ) : zpoint c t + (d : ℂ) = zpoint (c + d) t := by
  unfold zpoint
  push_cast
  ring

private lemma quadraticPerronKernel_eq {v : ℝ} {s : ℂ} (h₀ : s ≠ 0) (h₁ : s + 1 ≠ 0) (h₂ : s + 2 ≠ 0) :
    quadraticPerronKernel v s = perronIntegrand v s -
      2 * (Real.exp (-v) : ℂ) * perronIntegrand v (s + 1) +
      (Real.exp (-(2 * v)) : ℂ) * perronIntegrand v (s + 2) := by
  let E := Complex.exp ((v : ℂ) * s)
  have hshift (d : ℝ) : (Real.exp (-(d * v)) : ℂ) * perronIntegrand v (s + (d : ℂ)) = E / (s + (d : ℂ)) := by
    rw [perronIntegrand, ← mul_div_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h₁' : (Real.exp (-v) : ℂ) * perronIntegrand v (s + 1) = E / (s + 1) := by
    simpa only [one_mul, Complex.ofReal_one] using hshift 1
  have h₂' : (Real.exp (-(2 * v)) : ℂ) * perronIntegrand v (s + 2) = E / (s + 2) := by
    simpa only [Complex.ofReal_ofNat] using hshift 2
  rw [mul_assoc (2 : ℂ), h₁', h₂']
  change 2 * E / (s * (s + 1) * (s + 2)) = E / s - 2 * (E / (s + 1)) + E / (s + 2)
  field_simp
  ring

private noncomputable def quadraticPerronVertical (v c T : ℝ) : ℂ :=
  I * ∫ t in -T..T, quadraticPerronKernel v (zpoint c t)

private lemma quadraticPerronVertical_eq {v c T : ℝ} (hc : 0 < c) :
    quadraticPerronVertical v c T = perronVertical v c T -
      (2 * (Real.exp (-v) : ℂ)) * perronVertical v (c + 1) T +
      (Real.exp (-(2 * v)) : ℂ) * perronVertical v (c + 2) T := by
  have hc1 : 0 < c + 1 := by positivity
  have hc2 : 0 < c + 2 := by positivity
  have he (t : ℝ) : quadraticPerronKernel v (zpoint c t) = perronIntegrand v (zpoint c t) -
      (2 * (Real.exp (-v) : ℂ)) * perronIntegrand v (zpoint (c + 1) t) +
      (Real.exp (-(2 * v)) : ℂ) * perronIntegrand v (zpoint (c + 2) t) := by
    have h₁ : zpoint c t + 1 = zpoint (c + 1) t := by simpa using zpoint_add_real c t 1
    have h₂ : zpoint c t + 2 = zpoint (c + 2) t := by simpa using zpoint_add_real c t 2
    rw [quadraticPerronKernel_eq (zpoint_ne_zero_of_re hc.ne')
      (h₁ ▸ zpoint_ne_zero_of_re hc1.ne') (h₂ ▸ zpoint_ne_zero_of_re hc2.ne'), h₁, h₂]
  have h₀ : IntervalIntegrable (fun t => perronIntegrand v (zpoint c t)) MeasureTheory.volume (-T) T :=
    (continuous_perron_vertical v hc.ne').intervalIntegrable _ _
  have h₁ : IntervalIntegrable (fun t => (2 * (Real.exp (-v) : ℂ)) * perronIntegrand v (zpoint (c + 1) t))
      MeasureTheory.volume (-T) T :=
    ((continuous_perron_vertical v hc1.ne').const_mul _).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun t => (Real.exp (-(2 * v)) : ℂ) * perronIntegrand v (zpoint (c + 2) t))
      MeasureTheory.volume (-T) T :=
    ((continuous_perron_vertical v hc2.ne').const_mul _).intervalIntegrable _ _
  unfold quadraticPerronVertical perronVertical
  simp_rw [he]
  rw [intervalIntegral.integral_add (h₀.sub h₁) h₂, intervalIntegral.integral_sub h₀ h₁,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

private noncomputable def quadraticPerronWeight (v : ℝ) : ℝ :=
  if 0 < v then (1 - Real.exp (-v)) ^ (2 : ℕ) else 0

private lemma quadraticPerronVertical_error {v c T : ℝ} (hv : v ≠ 0) (hc : 0 < c) (hT : 0 < T) :
    ‖quadraticPerronVertical v c T - (2 * (Real.pi : ℂ) * I) * (quadraticPerronWeight v : ℂ)‖ ≤
      8 * (Real.exp (v * c) / (T * |v|)) := by
  let S := 2 * (Real.pi : ℂ) * I
  let L := if 0 < v then S else 0
  let k := Real.exp (v * c) / (T * |v|)
  let Δ (d : ℝ) := (Real.exp (-(d * v)) : ℂ) * (perronVertical v (c + d) T - L)
  have hb (d : ℝ) (hd : 0 < c + d) : ‖Δ d‖ ≤ 2 * k := by
    dsimp [Δ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_left (perronVertical_error hv hd hT) (Real.exp_nonneg _)).trans_eq
    change Real.exp (-(d * v)) * (2 * (Real.exp (v * (c + d)) / (T * |v|))) =
      2 * (Real.exp (v * c) / (T * |v|))
    calc
      _ = 2 * ((Real.exp (-(d * v)) * Real.exp (v * (c + d))) / (T * |v|)) := by ring
      _ = _ := by rw [← Real.exp_add, show -(d * v) + v * (c + d) = v * c by ring]
  have hId : quadraticPerronVertical v c T - S * (quadraticPerronWeight v : ℂ) =
      Δ 0 - 2 * Δ 1 + Δ 2 := by
    rw [quadraticPerronVertical_eq hc]
    simp only [Δ, zero_mul, neg_zero, Real.exp_zero, Complex.ofReal_one, add_zero, one_mul,
      quadraticPerronWeight, L]
    by_cases h : 0 < v
    · rw [if_pos h, if_pos h, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
        show -(2 * v) = -v + -v by ring, Real.exp_add, Complex.ofReal_mul]
      ring
    · rw [if_neg h, if_neg h, Complex.ofReal_zero]
      ring
  rw [hId]
  have h₀ := hb 0 (by simpa using hc)
  have h₁ := hb 1 (by positivity)
  have h₂ := hb 2 (by positivity)
  have htwo : ‖(2 : ℂ) * Δ 1‖ ≤ 4 * k := by
    rw [norm_mul, Complex.norm_ofNat]
    linarith only [h₁]
  have hl := norm_sub_le (Δ 0) (2 * Δ 1)
  have hr := norm_add_le (Δ 0 - 2 * Δ 1) (Δ 2)
  linarith only [h₀, h₂, htwo, hl, hr]

private lemma logDeriv_analyticAt_of_ne_zero {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (hn : f w ≠ 0) : AnalyticAt ℂ (logDeriv f) w :=
  hf.deriv.div hf hn

private lemma logDeriv_sub_const (w z : ℂ) : logDeriv (fun v : ℂ => v - w) z = (z - w)⁻¹ := by
  have hd : HasDerivAt (fun v : ℂ => v - w) 1 z := (hasDerivAt_id z).sub_const w
  rw [logDeriv_apply, hd.deriv, one_div]

private lemma logDeriv_eventually_eq_principal_part {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (htop : analyticOrderAt f w ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧
      logDeriv f =ᶠ[𝓝[≠] w] fun z => (analyticOrderNatAt f w : ℂ) * (z - w)⁻¹ + g z := by
  obtain ⟨g, hg, hgn, heq⟩ := hf.analyticOrderAt_ne_top.mp htop
  refine ⟨logDeriv g, logDeriv_analyticAt_of_ne_zero hg hgn, ?_⟩
  have hne : ∀ᶠ z in 𝓝 w, g z ≠ 0 := hg.continuousAt.eventually_ne hgn
  have heq' := heq.eventually_nhds.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] w ≤ 𝓝 w)
  filter_upwards [heq', hne.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] w ≤ 𝓝 w),
    hg.eventually_analyticAt.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] w ≤ 𝓝 w),
    self_mem_nhdsWithin] with z hz hgz hga hzw
  let n := analyticOrderNatAt f w
  let A (x : ℂ) := x - w
  have hz' : f =ᶠ[𝓝 z] (A · ^ n) * g := by
    filter_upwards [hz] with x hx
    simpa only [Pi.mul_apply, smul_eq_mul] using hx
  have hza : A z ≠ 0 := sub_ne_zero.mpr hzw
  have hAd : DifferentiableAt ℂ A z := by unfold A; fun_prop
  have hP : DifferentiableAt ℂ (A · ^ n) z := hAd.pow n
  rw [(logDeriv_congr_nhds hz').eq_of_nhds]
  change logDeriv (fun x => A x ^ n * g x) z = _
  rw [logDeriv_mul z (f := fun x => A x ^ n) (g := g) (pow_ne_zero _ hza) hgz hP hga.differentiableAt,
    logDeriv_fun_pow hAd]
  exact congrArg (fun v => (n : ℂ) * v + logDeriv g z) (logDeriv_sub_const w z)

private lemma analyticOrderAt_zeta₁_ne_top (z : ℂ) : analyticOrderAt riemannZeta₁ z ≠ ⊤ := by
  have hA : AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
    fun w _ => differentiable_riemannZeta₁.analyticAt w
  have h1 : analyticOrderAt riemannZeta₁ 1 = 0 :=
    (hA 1 trivial).analyticOrderAt_eq_zero.mpr (by rw [riemannZeta₁_one]; norm_num)
  exact hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial (by rw [h1]; simp)

private lemma neg_logDeriv_zeta_eq {z : ℂ} (hz : z ≠ 1) (hn : riemannZeta₁ z ≠ 0) :
    -logDeriv riemannZeta z = (z - 1)⁻¹ - logDeriv riemannZeta₁ z := by
  have heq : riemannZeta =ᶠ[𝓝 z] (fun w => (w - 1)⁻¹) * riemannZeta₁ := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact riemannZeta_eq_inv_sub_mul hw
  have htrans : logDeriv (fun w : ℂ => (w - 1)⁻¹) z = -(z - 1)⁻¹ := by
    have hd : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := by fun_prop
    simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul, logDeriv_sub_const]
      using logDeriv_fun_zpow hd (-1)
  rw [(logDeriv_congr_nhds heq).eq_of_nhds]
  change -logDeriv (fun w => (w - 1)⁻¹ * riemannZeta₁ w) z = _
  rw [logDeriv_mul z (f := fun w : ℂ => (w - 1)⁻¹) (g := riemannZeta₁)
      (inv_ne_zero (sub_ne_zero.mpr hz)) hn
      ((show DifferentiableAt ℂ (fun w : ℂ => w - 1) z by fun_prop).inv (sub_ne_zero.mpr hz))
      differentiable_riemannZeta₁.differentiableAt,
    htrans]
  ring

private lemma neg_logDeriv_zeta_at_pole :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧
      (fun z => -logDeriv riemannZeta z) =ᶠ[𝓝[≠] (1 : ℂ)] fun z => 1 * (z - 1)⁻¹ + g z := by
  have hA := differentiable_riemannZeta₁.analyticAt (1 : ℂ)
  have h1 : riemannZeta₁ 1 ≠ 0 := by rw [riemannZeta₁_one]; norm_num
  refine ⟨fun z => -logDeriv riemannZeta₁ z, (logDeriv_analyticAt_of_ne_zero hA h1).neg, ?_⟩
  filter_upwards [(hA.continuousAt.eventually_ne h1).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] (1 : ℂ) ≤ 𝓝 1), self_mem_nhdsWithin] with z hn hz
  rw [neg_logDeriv_zeta_eq hz hn, one_mul, sub_eq_add_neg]

private lemma neg_logDeriv_zeta_at_zero {T : ℝ} {w : ℂ} (hw : w ∈ zerosUpTo T) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧
      (fun z => -logDeriv riemannZeta z) =ᶠ[𝓝[≠] w]
        fun z => -(multiplicity w : ℂ) * (z - w)⁻¹ + g z := by
  have hw1 : w ≠ 1 := by
    intro heq
    have hre := (mem_zerosUpTo.mp hw).2.2.1
    simp [heq] at hre
  have ha := analyticOn_riemannZeta w hw1
  have htop : analyticOrderAt riemannZeta w ≠ ⊤ := by
    have hEq : riemannZeta₁ =ᶠ[𝓝 w] (fun z : ℂ => z - 1) * riemannZeta := by
      filter_upwards [eventually_ne_nhds hw1] with z hz
      change riemannZeta₁ z = (z - 1) * riemannZeta z
      rw [riemannZeta_eq_inv_sub_mul hz, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz), one_mul]
    have h := analyticOrderAt_zeta₁_ne_top w
    rw [analyticOrderAt_congr hEq, analyticOrderAt_mul (by fun_prop) ha,
      (show analyticOrderAt (fun z : ℂ => z - 1) w = 0 from
        (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - 1) w).analyticOrderAt_eq_zero.mpr
          (sub_ne_zero.mpr hw1)), zero_add] at h
    exact h
  obtain ⟨g, hg, heq⟩ := logDeriv_eventually_eq_principal_part ha htop
  refine ⟨fun z => -g z, hg.neg, ?_⟩
  filter_upwards [heq] with z hz
  rw [hz, multiplicity, neg_add, neg_mul]

private lemma perronIntegrand_analyticAt (v : ℝ) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (perronIntegrand v) z := by
  unfold perronIntegrand
  exact (by fun_prop : AnalyticAt ℂ (fun s => Complex.exp ((v : ℂ) * s)) z).div analyticAt_id hz

private lemma principal_part_mul {f K : ℂ → ℂ} {w r : ℂ}
    (hK : AnalyticAt ℂ K w) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g w)
    (heq : f =ᶠ[𝓝[≠] w] fun z => r * (z - w)⁻¹ + g z) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G w ∧
      (fun z => f z * K z) =ᶠ[𝓝[≠] w] fun z => (r * K w) * (z - w)⁻¹ + G z := by
  obtain ⟨U, hU, hUo, hwU⟩ := _root_.eventually_nhds_iff.mp hK.eventually_analyticAt
  have hn : U ∈ 𝓝 w := hUo.mem_nhds hwU
  have hd : DifferentiableOn ℂ K U := fun z hz => (hU z hz).differentiableAt.differentiableWithinAt
  have hD : AnalyticAt ℂ (dslope K w) w :=
    ((Complex.differentiableOn_dslope hn).mpr hd).analyticOnNhd hUo w hwU
  refine ⟨fun z => r * dslope K w z + g z * K z, (analyticAt_const.mul hD).add (hg.mul hK), ?_⟩
  filter_upwards [heq, self_mem_nhdsWithin] with z hz hzw
  change z ≠ w at hzw
  rw [hz, dslope_of_ne K hzw, slope_def_field, div_eq_mul_inv]
  ring

private noncomputable def zetaPerron (q : ℝ) (z : ℂ) : ℂ :=
  -logDeriv riemannZeta z * perronIntegrand (Real.log q) z

private lemma zetaPerron_analyticAt (q : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hz : riemannZeta z ≠ 0) : AnalyticAt ℂ (zetaPerron q) z :=
  (logDeriv_analyticAt_of_ne_zero (analyticOn_riemannZeta z hz1) hz).neg.mul
    (perronIntegrand_analyticAt _ hz0)

private lemma perronIntegrand_eq_cpow {q : ℝ} (hq : 0 < q) (z : ℂ) :
    perronIntegrand (Real.log q) z = (q : ℂ) ^ z / z := by
  rw [perronIntegrand, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
    Complex.ofReal_log hq.le, mul_comm]

private noncomputable def zetaDetectorIntegrand (X : ℕ) (v : ℝ) (ρ w : ℂ) : ℂ :=
  riemannZeta (ρ + w) * moebiusPolynomial X (ρ + w) * quadraticPerronKernel v w

private lemma analytic_quadraticPerronKernel (v : ℝ) {w : ℂ} (h₀ : w ≠ 0) (h₁ : w + 1 ≠ 0)
    (h₂ : w + 2 ≠ 0) : AnalyticAt ℂ (quadraticPerronKernel v) w := by
  unfold quadraticPerronKernel
  exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 2 * Complex.exp ((v : ℂ) * w)) w).div
    (by fun_prop) (mul_ne_zero (mul_ne_zero h₀ h₁) h₂)

private lemma rectIntegral_zetaDetector_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hreal : 1 / 2 < ρ.re) (hreal' : ρ.re < 1) {H : ℝ} (hH : |ρ.im| < H) (X : ℕ) (v : ℝ) :
    rectIntegral (1 / 2 - ρ.re) 2 H (zetaDetectorIntegrand X v ρ) =
      (2 * (Real.pi : ℂ) * I) * (moebiusPolynomial X 1 * quadraticPerronKernel v (1 - ρ)) := by
  classical
  let a := 1 / 2 - ρ.re
  let w₀ : ℂ := 1 - ρ
  let P := moebiusPolynomial X 1 * quadraticPerronKernel v w₀
  let c (w : ℂ) := if w = 0 then 0 else P
  have ha : a < 0 := by dsimp [a]; linarith only [hreal]
  have ha₁ : -1 < a := by dsimp [a]; linarith only [hreal']
  have hH0 := (abs_nonneg ρ.im).trans_lt hH
  have hwre : 0 < w₀.re := by change 0 < 1 - ρ.re; linarith only [hreal']
  have hwre' : w₀.re < 2 := by change 1 - ρ.re < 2; linarith only [hreal]
  have hwim : |w₀.im| < H := by simpa only [w₀, Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hH
  have hw₀ : w₀ ≠ 0 := fun he => hwre.ne' (by simp [he])
  have hw₁ : w₀ + 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith only [he, hwre]
  have hw₂ : w₀ + 2 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.re_ofNat, Complex.zero_re] at he
    linarith only [he, hwre]
  let S : Finset ℂ := {0, w₀}
  have hS (w : ℂ) (hw : w ∈ S) : a < w.re ∧ w.re < 2 ∧ -H < w.im ∧ w.im < H := by
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simpa only [Complex.zero_re, Complex.zero_im] using
        And.intro ha (And.intro (by norm_num : (0 : ℝ) < 2) (And.intro (neg_lt_zero.mpr hH0) hH0))
    · rw [Finset.mem_singleton.mp hw]
      exact ⟨ha.trans hwre, hwre', (abs_lt.mp hwim).1, (abs_lt.mp hwim).2⟩
  have hm (w : ℂ) : AnalyticAt ℂ (fun w => moebiusPolynomial X (ρ + w)) w :=
    (analytic_moebiusPolynomial X (ρ + w) trivial).comp (by fun_prop)
  have hp (w : ℂ) (hw : w ≠ w₀) : AnalyticAt ℂ (fun w => riemannZeta (ρ + w)) w := by
    have hh : ρ + w ≠ 1 := by
      intro he
      apply hw
      dsimp [w₀]
      linear_combination he
    exact (analyticOn_riemannZeta (ρ + w) hh).comp (by fun_prop)
  have hreg : ∀ w ∈ ([[a, 2]] ×ℂ [[-H, H]]), w ∉ S → AnalyticAt ℂ (zetaDetectorIntegrand X v ρ) w := by
    intro w hw hwS
    have hwr : a ≤ w.re := by
      have hr : w.re ∈ [[a, 2]] := hw.1
      rw [Set.uIcc_of_le (by linarith only [ha])] at hr
      exact hr.1
    have h₀ : w ≠ 0 := fun he => hwS (Finset.mem_insert.mpr (Or.inl he))
    have hh : w ≠ w₀ := fun he => hwS (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he)))
    have h₁ : w + 1 ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
      linarith only [hre, hwr, ha₁]
    have h₂ : w + 2 ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      simp only [Complex.add_re, Complex.re_ofNat, Complex.zero_re] at hre
      linarith only [hre, hwr, ha₁]
    exact ((hp w hh).mul (hm w)).mul (analytic_quadraticPerronKernel v h₀ h₁ h₂)
  have hpart : ∀ w ∈ S, ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧
      zetaDetectorIntegrand X v ρ =ᶠ[𝓝[≠] w] fun t => c w * (t - w)⁻¹ + g t := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · let F (t : ℂ) := riemannZeta (ρ + t) * moebiusPolynomial X (ρ + t) *
        ((2 * Complex.exp ((v : ℂ) * t)) / ((t + 1) * (t + 2)))
      have hFa : AnalyticAt ℂ F 0 := by
        unfold F
        exact ((hp 0 hw₀.symm).mul (hm 0)).mul
          ((by fun_prop : AnalyticAt ℂ (fun t : ℂ => 2 * Complex.exp ((v : ℂ) * t)) 0).div
            (by fun_prop) (by norm_num))
      have hF0 : F 0 = 0 := by simp [F, hρ]
      have he : (fun t : ℂ => t⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)] fun t => (1 : ℂ) * (t - 0)⁻¹ + (fun _ : ℂ => 0) t :=
        Eventually.of_forall (fun _ => by simp)
      obtain ⟨G, hG, hGe⟩ := principal_part_mul hFa analyticAt_const he
      refine ⟨G, hG, ?_⟩
      have heq : zetaDetectorIntegrand X v ρ = fun t => t⁻¹ * F t := by
        funext t
        simp only [zetaDetectorIntegrand, quadraticPerronKernel, F, div_eq_mul_inv, mul_inv_rev]
        ring
      rw [heq, show c 0 = 0 from if_pos rfl]
      rwa [hF0, mul_zero] at hGe
    · rw [Finset.mem_singleton.mp hw]
      let F (t : ℂ) := riemannZeta₁ (ρ + t) * moebiusPolynomial X (ρ + t) * quadraticPerronKernel v t
      have hFa : AnalyticAt ℂ F w₀ := by
        unfold F
        exact (((differentiable_riemannZeta₁.analyticAt (ρ + w₀)).comp (by fun_prop)).mul (hm w₀)).mul
          (analytic_quadraticPerronKernel v hw₀ hw₁ hw₂)
      have hsum (t : ℂ) : ρ + t - 1 = t - w₀ := by dsimp [w₀]; ring
      have hF0 : F w₀ = P := by
        have he : ρ + w₀ = 1 := by dsimp [w₀]; ring
        simp only [F, he, riemannZeta₁_one, one_mul, P]
      have he : (fun t : ℂ => (t - w₀)⁻¹) =ᶠ[𝓝[≠] w₀] fun t =>
          (1 : ℂ) * (t - w₀)⁻¹ + (fun _ : ℂ => 0) t := Eventually.of_forall (fun _ => by simp)
      obtain ⟨G, hG, hGe⟩ := principal_part_mul hFa analyticAt_const he
      refine ⟨G, hG, ?_⟩
      have heq : zetaDetectorIntegrand X v ρ =ᶠ[𝓝[≠] w₀] fun t => (t - w₀)⁻¹ * F t := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have hs : ρ + t ≠ 1 := fun he => (sub_ne_zero.mpr ht) (by rw [← hsum, he, sub_self])
        rw [zetaDetectorIntegrand, riemannZeta_eq_inv_sub_mul hs, hsum]
        dsimp [F]
        ring
      rw [show c w₀ = P from if_neg hw₀]
      rw [hF0, one_mul] at hGe
      exact heq.trans hGe
  have hs := rectIntegral_eq_sum_residues S (zetaDetectorIntegrand X v ρ) c hS hreg hpart
  have hn : (0 : ℂ) ∉ ({w₀} : Finset ℂ) := fun h => hw₀ (Finset.mem_singleton.mp h).symm
  rw [show S = insert 0 {w₀} from rfl, Finset.sum_insert hn, Finset.sum_singleton,
    show c 0 = 0 from if_pos rfl, show c w₀ = P from if_neg hw₀, zero_add] at hs
  exact hs

private lemma norm_riemannZeta_le_inv_add :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s ≠ 1 →
      ‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + C * ‖s‖ := by
  obtain ⟨C, hC, hbound⟩ := norm_riemannZeta₁_le (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨C, hC, fun s hs hne => ?_⟩
  rw [riemannZeta_eq_inv_sub_mul hne, norm_mul, norm_inv]
  apply (mul_le_mul_of_nonneg_left (hbound s hs) (by positivity)).trans_eq
  have hp : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [mul_add, mul_one, show ‖s - 1‖⁻¹ * (C * (‖s - 1‖ * ‖s‖)) = C * ‖s‖ by
    field_simp]

private lemma norm_moebiusPolynomial_le (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) : ‖moebiusPolynomial X s‖ ≤ X := by
  unfold moebiusPolynomial
  calc
    _ ≤ ∑ n ∈ range X, ‖(ArithmeticFunction.moebius (n + 1) : ℂ) * (((n + 1 : ℕ) : ℂ) ^ (-s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ range X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_intCast, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hmu : |(ArithmeticFunction.moebius (n + 1) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
      have hrp : ((n + 1 : ℕ) : ℝ) ^ (-s.re) ≤ 1 := by
        rw [← Real.rpow_zero ((n + 1 : ℕ) : ℝ)]
        exact rpow_le_rpow_of_exponent_le hn (neg_nonpos.mpr hs)
      simpa only [one_mul] using mul_le_mul hmu hrp (by positivity) (show (0 : ℝ) ≤ 1 by norm_num)
    _ = _ := by simp

private lemma norm_quadraticPerronKernel (v : ℝ) (z : ℂ) :
    ‖quadraticPerronKernel v z‖ = (2 * Real.exp (v * z.re)) / (‖z‖ * ‖z + 1‖ * ‖z + 2‖) := by
  unfold quadraticPerronKernel
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private lemma norm_quadraticPerronKernel_vertical {v c d : ℝ} (hd : 0 < d) (hd₁ : d ≤ 1)
    (h₀ : d ≤ |c|) (h₁ : d ≤ |c + 1|) (h₂ : d ≤ |c + 2|) (t : ℝ) :
    ‖quadraticPerronKernel v (zpoint c t)‖ ≤
      (16 * Real.exp (v * c) / d ^ (3 : ℕ)) / (1 + |t|) ^ (3 : ℕ) := by
  have hlow (j : ℝ) (hj : d ≤ |c + j|) : d * (1 + |t|) / 2 ≤ ‖zpoint c t + (j : ℂ)‖ := by
    rw [zpoint_add_real]
    have hR := hj.trans (by simpa only [zpoint_re] using Complex.abs_re_le_norm (zpoint (c + j) t))
    have hI : |t| ≤ ‖zpoint (c + j) t‖ := by
      simpa only [zpoint_im] using Complex.abs_im_le_norm (zpoint (c + j) t)
    have hh := mul_le_of_le_one_left (abs_nonneg t) hd₁
    nlinarith only [hR, hI, hh]
  let L := d * (1 + |t|) / 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hl₀ : L ≤ ‖zpoint c t‖ := by simpa only [Complex.ofReal_zero, add_zero] using hlow 0 (by simpa using h₀)
  have hl₁ : L ≤ ‖zpoint c t + 1‖ := by simpa only [Complex.ofReal_one] using hlow 1 h₁
  have hl₂ : L ≤ ‖zpoint c t + 2‖ := by simpa only [Complex.ofReal_ofNat] using hlow 2 h₂
  have hp : L ^ (3 : ℕ) ≤ ‖zpoint c t‖ * ‖zpoint c t + 1‖ * ‖zpoint c t + 2‖ := by
    simpa only [pow_succ, pow_zero, one_mul] using
      mul_le_mul (mul_le_mul hl₀ hl₁ hL.le (norm_nonneg _)) hl₂ hL.le (by positivity)
  rw [norm_quadraticPerronKernel, zpoint_re]
  calc
    _ ≤ (2 * Real.exp (v * c)) / L ^ (3 : ℕ) := div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = _ := by dsimp [L]; field_simp; ring

open MeasureTheory in
private lemma integrable_detector_vertical (X : ℕ) (v : ℝ) (ρ : ℂ) (c : ℝ)
    (hreal : 1 / 2 ≤ ρ.re + c) (hne : ρ.re + c ≠ 1) (h₀ : c ≠ 0) (h₁ : c + 1 ≠ 0) (h₂ : c + 2 ≠ 0) :
    Integrable (fun t => zetaDetectorIntegrand X v ρ (zpoint c t)) := by
  obtain ⟨C, hC, hζ⟩ := norm_riemannZeta_le_inv_add
  let F (t : ℝ) := zetaDetectorIntegrand X v ρ (zpoint c t)
  let d := min 1 (min |c| (min |c + 1| |c + 2|))
  have hd : 0 < d := lt_min zero_lt_one (lt_min (abs_pos.mpr h₀) (lt_min (abs_pos.mpr h₁) (abs_pos.mpr h₂)))
  have hd₁ : d ≤ 1 := min_le_left _ _
  have hd₀' : d ≤ |c| := (min_le_right _ _).trans (min_le_left _ _)
  have hd₁' : d ≤ |c + 1| := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd₂' : d ≤ |c + 2| := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let D := 16 * Real.exp (v * c) / d ^ (3 : ℕ)
  have hD : 0 < D := by dsimp [D]; positivity
  let L := |ρ.re + c| + |ρ.im| + 1
  let Z := |ρ.re + c - 1|⁻¹ + C * L
  let B := (Z * (X : ℝ)) * D
  have hZ : 0 ≤ Z := by dsimp [Z, L]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpole (t : ℝ) : ρ + zpoint c t ≠ 1 := by
    intro he
    apply hne
    simpa only [Complex.add_re, zpoint_re, Complex.one_re] using congrArg Complex.re he
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun t => by
    have hz : AnalyticAt ℂ (zetaDetectorIntegrand X v ρ) (zpoint c t) := by
      unfold zetaDetectorIntegrand
      have ha := (analyticOn_riemannZeta (ρ + zpoint c t) (hpole t)).comp
        (by fun_prop : AnalyticAt ℂ (fun w => ρ + w) (zpoint c t))
      have hb := (analytic_moebiusPolynomial X (ρ + zpoint c t) trivial).comp
        (by fun_prop : AnalyticAt ℂ (fun w => ρ + w) (zpoint c t))
      have hne₁ : zpoint c t + 1 ≠ 0 := by
        rw [← Complex.ofReal_one, zpoint_add_real]
        exact zpoint_ne_zero_of_re h₁
      have hne₂ : zpoint c t + 2 ≠ 0 := by
        rw [← Complex.ofReal_ofNat, zpoint_add_real]
        exact zpoint_ne_zero_of_re h₂
      exact (ha.mul hb).mul (analytic_quadraticPerronKernel v (zpoint_ne_zero_of_re h₀) hne₁ hne₂)
    exact hz.continuousAt.comp (by unfold zpoint; fun_prop)
  have hdF (t : ℝ) : ‖F t‖ ≤ B * (1 + t ^ (2 : ℕ))⁻¹ := by
    let s := ρ + zpoint c t
    have hs : 1 / 2 ≤ s.re := by simpa only [s, Complex.add_re, zpoint_re] using hreal
    have hsNorm : ‖s‖ ≤ L * (1 + |t|) := by
      have hl := Complex.norm_le_abs_re_add_abs_im s
      rw [show s.re = ρ.re + c from by simp [s], show s.im = ρ.im + t from by simp [s] ] at hl
      have hli := abs_add_le ρ.im t
      dsimp [L]
      nlinarith only [hl, hli, mul_nonneg (abs_nonneg (ρ.re + c)) (abs_nonneg t),
        mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
    have hζn : ‖riemannZeta s‖ ≤ Z * (1 + |t|) := by
      apply (hζ s hs (hpole t)).trans
      have hsub : |ρ.re + c - 1| ≤ ‖s - 1‖ := by
        simpa [s, Complex.sub_re] using Complex.abs_re_le_norm (s - 1)
      have hi := (inv_le_inv₀ ((abs_pos.mpr (sub_ne_zero.mpr hne)).trans_le hsub)
        (abs_pos.mpr (sub_ne_zero.mpr hne))).mpr hsub
      have hN := mul_le_mul_of_nonneg_left hsNorm hC
      dsimp [Z]
      nlinarith only [hi, hN, mul_nonneg (inv_nonneg.mpr (abs_nonneg (ρ.re + c - 1))) (abs_nonneg t)]
    have hMq := norm_moebiusPolynomial_le X (by linarith only [hs])
    have hK := norm_quadraticPerronKernel_vertical hd hd₁ hd₀' hd₁' hd₂' t (v := v)
    change ‖riemannZeta s * moebiusPolynomial X s * quadraticPerronKernel v (zpoint c t)‖ ≤ _
    rw [norm_mul, norm_mul]
    calc
      _ ≤ ((Z * (1 + |t|)) * (X : ℝ)) * (D / (1 + |t|) ^ (3 : ℕ)) :=
        mul_le_mul (mul_le_mul hζn hMq (norm_nonneg _) (by positivity)) hK (norm_nonneg _) (by positivity)
      _ = B * ((1 + |t|) ^ (2 : ℕ))⁻¹ := by dsimp [B]; field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
        have h := sq_abs t
        nlinarith only [h, abs_nonneg t]
  exact (integrable_inv_one_add_sq.const_mul B).mono' hF.aestronglyMeasurable (Eventually.of_forall hdF)

private lemma detector_horizontal_integral_bound (X : ℕ) (v : ℝ) {ρ : ℂ}
    (hreal : 1 / 2 < ρ.re) (hreal' : ρ.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H ≥ |ρ.im| + 3, ∀ y : ℝ, |y| = H →
      ‖∫ s in (1 / 2 - ρ.re)..2, zetaDetectorIntegrand X v ρ (zpoint s y)‖ ≤ C / H ^ (2 : ℕ) := by
  obtain ⟨C, hC, hζ⟩ := norm_riemannZeta_le_inv_add
  let a := 1 / 2 - ρ.re
  let M := max (Real.exp (v * a)) (Real.exp (v * 2))
  let K := (1 + 3 * C) * (X : ℝ) * (2 * M)
  have ha : a < 0 := by dsimp [a]; linarith only [hreal]
  have ha' : -1 < a := by dsimp [a]; linarith only [hreal']
  have hM : 0 < M := (Real.exp_pos _).trans_le (le_max_left _ _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨3 * K, by positivity, fun H hH y hy => ?_⟩
  have hH₁ : 1 ≤ H := by linarith only [hH, abs_nonneg ρ.im]
  have hH₀ : 0 < H := zero_lt_one.trans_le hH₁
  have hab : a ≤ 2 := by linarith only [ha]
  have hfun (s : ℝ) (hs : s ∈ Set.Icc a 2) : ‖zetaDetectorIntegrand X v ρ (zpoint s y)‖ ≤ K / H ^ (2 : ℕ) := by
    let w := ρ + zpoint s y
    have hwre : w.re = ρ.re + s := by simp [w]
    have hwim : w.im = ρ.im + y := by simp [w]
    have hlow : 1 / 2 ≤ w.re := by rw [hwre]; dsimp [a] at hs; linarith only [hs.1]
    have hupp : w.re ≤ 3 := by rw [hwre]; linarith only [hreal', hs.2]
    have hwNorm : ‖w‖ ≤ 3 * H := by
      have h := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hlow), hwim] at h
      have hh := abs_add_le ρ.im y
      rw [hy] at hh
      linarith only [h, hh, hupp, hH, hH₁]
    have hdist : 1 ≤ ‖w - 1‖ := by
      have he := Complex.abs_im_le_norm (w - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero, hwim] at he
      have h := abs_add_le (ρ.im + y) (-ρ.im)
      rw [show ρ.im + y + -ρ.im = y by ring, abs_neg, hy] at h
      linarith only [h, he, hH]
    have hw₁ : w ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hdist; norm_num at hdist
    have hζw : ‖riemannZeta w‖ ≤ (1 + 3 * C) * H := by
      have hi : ‖w - 1‖⁻¹ ≤ 1 := by simpa only [inv_one] using
        (inv_le_inv₀ (zero_lt_one.trans_le hdist) zero_lt_one).mpr hdist
      apply (hζ w hlow hw₁).trans
      nlinarith only [hi, mul_le_mul_of_nonneg_left hwNorm hC, hH₁]
    have hMPoly : ‖moebiusPolynomial X w‖ ≤ X := norm_moebiusPolynomial_le X ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hlow)
    have hExp : Real.exp (v * s) ≤ M := by
      rcases le_total 0 v with hp | hn
      · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hp)).trans (le_max_right _ _)
      · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hs.1 hn)).trans (le_max_left _ _)
    have hiz (j : ℝ) : H ≤ ‖zpoint s y + (j : ℂ)‖ := by
      rw [zpoint_add_real]
      simpa only [zpoint_im, hy] using Complex.abs_im_le_norm (zpoint (s + j) y)
    have h₀ : H ≤ ‖zpoint s y‖ := by simpa only [Complex.ofReal_zero, add_zero] using hiz 0
    have h₁ : H ≤ ‖zpoint s y + 1‖ := by simpa only [Complex.ofReal_one] using hiz 1
    have h₂ : H ≤ ‖zpoint s y + 2‖ := by simpa only [Complex.ofReal_ofNat] using hiz 2
    have hPow : H ^ (3 : ℕ) ≤ ‖zpoint s y‖ * ‖zpoint s y + 1‖ * ‖zpoint s y + 2‖ := by
      simpa only [pow_succ, pow_zero, one_mul] using
        mul_le_mul (mul_le_mul h₀ h₁ hH₀.le (norm_nonneg _)) h₂ hH₀.le (by positivity)
    have hKernel : ‖quadraticPerronKernel v (zpoint s y)‖ ≤ (2 * M) / H ^ (3 : ℕ) := by
      rw [norm_quadraticPerronKernel, zpoint_re]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hExp (by norm_num)) (by positivity) hPow
    change ‖riemannZeta w * moebiusPolynomial X w * quadraticPerronKernel v (zpoint s y)‖ ≤ _
    rw [norm_mul, norm_mul]
    apply (mul_le_mul (mul_le_mul hζw hMPoly (norm_nonneg _) (by positivity)) hKernel (norm_nonneg _) (by positivity)).trans_eq
    dsimp [K]
    field_simp
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := 2) (C := K / H ^ (2 : ℕ)) (f := fun s => zetaDetectorIntegrand X v ρ (zpoint s y))
    (fun s hs => hfun s (by simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hs))
  apply hi.trans
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  calc
    _ ≤ (K / H ^ (2 : ℕ)) * 3 := mul_le_mul_of_nonneg_left (by linarith only [ha']) (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1200000 in
open MeasureTheory in
private lemma zetaDetector_vertical_difference {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hreal : 1 / 2 < ρ.re) (hreal' : ρ.re < 1) (X : ℕ) (v : ℝ) :
    I * (∫ t : ℝ, zetaDetectorIntegrand X v ρ (zpoint 2 t)) -
      I * (∫ t : ℝ, zetaDetectorIntegrand X v ρ (zpoint (1 / 2 - ρ.re) t)) =
      (2 * (Real.pi : ℂ) * I) * (moebiusPolynomial X 1 * quadraticPerronKernel v (1 - ρ)) := by
  let a := 1 / 2 - ρ.re
  let F := zetaDetectorIntegrand X v ρ
  let V (c H : ℝ) := I * ∫ t in -H..H, F (zpoint c t)
  let P := (2 * (Real.pi : ℂ) * I) * (moebiusPolynomial X 1 * quadraticPerronKernel v (1 - ρ))
  have hA : Integrable (fun t => F (zpoint a t)) := integrable_detector_vertical X v ρ a
    (by dsimp [a]; linarith) (by dsimp [a]; exact fun h => by linarith only [h])
    (by dsimp [a]; exact fun h => by linarith only [h, hreal])
    (by dsimp [a]; exact fun h => by linarith only [h, hreal'])
    (by dsimp [a]; exact fun h => by linarith only [h, hreal'])
  have hB : Integrable (fun t => F (zpoint 2 t)) := integrable_detector_vertical X v ρ 2
    (by linarith only [hreal]) (by exact fun h => by linarith only [h, hreal])
    (by norm_num) (by norm_num) (by norm_num)
  have hlim (c : ℝ) (h : Integrable (fun t => F (zpoint c t))) :
      Tendsto (V c) atTop (𝓝 (I * ∫ t : ℝ, F (zpoint c t))) := by
    have hT : Tendsto (fun H : ℝ => ∫ t in -H..H, F (zpoint c t)) atTop (𝓝 (∫ t : ℝ, F (zpoint c t))) :=
      intervalIntegral_tendsto_integral (μ := volume) (a := fun H : ℝ => -H) (b := fun H : ℝ => H)
        h tendsto_neg_atTop_atBot tendsto_id
    exact hT.const_mul I
  obtain ⟨C, hC, hhor⟩ := detector_horizontal_integral_bound X v hreal hreal'
  have hTarget : Tendsto (fun H : ℝ => V 2 H - V a H) atTop (𝓝 P) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hdecay : Tendsto (fun H : ℝ => (2 * C) / H ^ (2 : ℕ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, inv_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
        using ((tendsto_inv_atTop_zero : Tendsto (fun H : ℝ => H⁻¹) atTop (𝓝 0)).pow 2).const_mul (2 * C)
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hdecay
    filter_upwards [eventually_ge_atTop (|ρ.im| + 3)] with H hH
    have hH0 : 0 < H := by linarith only [hH, abs_nonneg ρ.im]
    have h := rectIntegral_zetaDetector_of_zero hρ hreal hreal' (show |ρ.im| < H by linarith only [hH]) X v
    change rectIntegral a 2 H F = P at h
    have he : V 2 H - V a H - P = (∫ s in a..2, F (zpoint s H)) - (∫ s in a..2, F (zpoint s (-H))) := by
      rw [← h, rectIntegral]
      dsimp [V]
      ring
    rw [he]
    have h₁ := hhor H hH H (abs_of_pos hH0)
    have h₂ := hhor H hH (-H) (by rw [abs_neg, abs_of_pos hH0])
    exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))
  exact tendsto_nhds_unique ((hlim 2 hB).sub (hlim a hA)) hTarget

private lemma rectIntegral_zetaPerron {a b H q : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 1 < b)
    (hH : 0 < H) (hq : 0 < q)
    (hvert : ∀ z ∈ zerosUpTo H, z.re ≠ a)
    (hhor : ∀ z ∈ zerosUpTo H, |z.im| < H) :
    rectIntegral a b H (zetaPerron q) = (2 * (Real.pi : ℂ) * I) *
      ((q : ℂ) - ∑ z ∈ (zerosUpTo H).filter (fun z => a < z.re),
        (multiplicity z : ℂ) * ((q : ℂ) ^ z / z)) := by
  classical
  let Z := (zerosUpTo H).filter (fun z => a < z.re)
  let S := insert (1 : ℂ) Z
  let r (z : ℂ) : ℂ := if z = 1 then (q : ℂ) else -(multiplicity z : ℂ) * ((q : ℂ) ^ z / z)
  have hone : (1 : ℂ) ∉ Z := by simp [Z, mem_zerosUpTo]
  have hS (z : ℂ) (hz : z ∈ S) : a < z.re ∧ z.re < b ∧ -H < z.im ∧ z.im < H := by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · change a < (1 : ℝ) ∧ (1 : ℝ) < b ∧ -H < 0 ∧ 0 < H
      exact ⟨ha1, hb, neg_lt_zero.mpr hH, hH⟩
    · obtain ⟨hzH, hza⟩ := Finset.mem_filter.mp hz
      have hzi := abs_lt.mp (hhor z hzH)
      exact ⟨hza, (mem_zerosUpTo.mp hzH).2.2.1.trans hb, hzi.1, hzi.2⟩
  have hA : ∀ z ∈ ([[a, b]] ×ℂ [[-H, H]]), z ∉ S → AnalyticAt ℂ (zetaPerron q) z := by
    intro z hz hzS
    have hza : a ≤ z.re := by
      have h : z.re ∈ [[a, b]] := hz.1
      rw [Set.uIcc_of_le (ha1.le.trans hb.le)] at h
      exact h.1
    have hzH : |z.im| ≤ H := by
      have h : z.im ∈ [[-H, H]] := hz.2
      rw [Set.uIcc_of_le (by linarith only [hH])] at h
      exact abs_le.mpr h
    have hz0 : z ≠ 0 := fun heq => ha.not_ge (by simpa [heq] using hza)
    have hz1 : z ≠ 1 := fun heq => hzS (Finset.mem_insert.mpr (Or.inl heq))
    refine zetaPerron_analyticAt q hz0 hz1 fun hzero => ?_
    have hzre : z.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hzero
    have hmem := mem_zerosUpTo.mpr ⟨hzero, ha.trans_le hza, hzre, hzH⟩
    exact hzS (Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨hmem, lt_of_le_of_ne hza (Ne.symm (hvert z hmem))⟩)))
  have hpart : ∀ z ∈ S, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      zetaPerron q =ᶠ[𝓝[≠] z] fun w => r z * (w - z)⁻¹ + g w := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzZ
    · obtain ⟨g, hg, heq⟩ := neg_logDeriv_zeta_at_pole
      have hK : perronIntegrand (Real.log q) 1 = (q : ℂ) := by
        rw [perronIntegrand_eq_cpow hq, cpow_one, div_one]
      obtain ⟨G, hG, hE⟩ := principal_part_mul
        (perronIntegrand_analyticAt (Real.log q) (by norm_num : (1 : ℂ) ≠ 0)) hg heq
      refine ⟨G, hG, ?_⟩
      rw [show r 1 = (q : ℂ) from if_pos rfl]
      rwa [hK, one_mul] at hE
    · have hzH : z ∈ zerosUpTo H := (Finset.mem_filter.mp hzZ).1
      have hz0 : z ≠ 0 := fun heq => (mem_zerosUpTo.mp hzH).2.1.ne' (by simp [heq])
      have hz1 : z ≠ 1 := fun heq => hone (heq ▸ hzZ)
      obtain ⟨g, hg, heq⟩ := neg_logDeriv_zeta_at_zero hzH
      obtain ⟨G, hG, hE⟩ := principal_part_mul (perronIntegrand_analyticAt (Real.log q) hz0) hg heq
      refine ⟨G, hG, ?_⟩
      rw [show r z = _ from if_neg hz1]
      rwa [perronIntegrand_eq_cpow hq] at hE
  rw [rectIntegral_eq_sum_residues S (zetaPerron q) r hS hA hpart, Finset.sum_insert hone]
  congr 1
  have hterm (z : ℂ) (hz : z ∈ Z) : r z = -((multiplicity z : ℂ) * ((q : ℂ) ^ z / z)) := by
    have hn : z ≠ 1 := fun heq => hone (heq ▸ hz)
    simp [r, hn]
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, sub_eq_add_neg]
  simp [r, Z]

private noncomputable def mangoldtWeight (q c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ArithmeticFunction.vonMangoldt n * Real.exp (c * Real.log (q / n))

private noncomputable def kernelErrorWeight (q c : ℝ) (n : ℕ) : ℝ :=
  mangoldtWeight q c n / |Real.log (q / n)|

private noncomputable def zetaVertical (q c T : ℝ) : ℂ :=
  I * ∫ t in -T..T,
    (-deriv riemannZeta (zpoint c t) / riemannZeta (zpoint c t)) *
      perronIntegrand (Real.log q) (zpoint c t)

private noncomputable def perronTerm (q c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  if n = 0 then 0 else
    (ArithmeticFunction.vonMangoldt n : ℂ) * perronIntegrand (Real.log (q / n)) (zpoint c t)

private lemma log_ratio_cpow {q : ℝ} (hq : 0 < q) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    Complex.exp ((Real.log (q / (n : ℝ)) : ℂ) * s) =
      Complex.exp ((Real.log q : ℂ) * s) / (n : ℂ) ^ s := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [Real.log_div hq.ne' hn0.ne', Complex.ofReal_sub, sub_mul, Complex.exp_sub,
    Complex.natCast_log, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]

private lemma norm_quadraticPerronKernel_right (v t : ℝ) :
    ‖quadraticPerronKernel v (zpoint 2 t)‖ ≤ (16 * Real.exp (v * 2)) * (1 + t ^ (2 : ℕ))⁻¹ := by
  apply (norm_quadraticPerronKernel_vertical (c := 2) (d := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) t).trans
  rw [one_pow, div_one, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  have hT : 1 + t ^ (2 : ℕ) ≤ (1 + |t|) ^ (2 : ℕ) := by
    nlinarith only [sq_abs t, abs_nonneg t]
  exact hT.trans (pow_le_pow_right₀ (by linarith only [abs_nonneg t]) (by norm_num))

private lemma continuous_quadraticPerronKernel_right (v : ℝ) :
    Continuous (fun t : ℝ => quadraticPerronKernel v (zpoint 2 t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h₁ : zpoint 2 t + 1 ≠ 0 := by
    rw [← Complex.ofReal_one, zpoint_add_real]
    exact zpoint_ne_zero_of_re (by norm_num)
  have h₂ : zpoint 2 t + 2 ≠ 0 := by
    rw [← Complex.ofReal_ofNat, zpoint_add_real]
    exact zpoint_ne_zero_of_re (by norm_num)
  exact (analytic_quadraticPerronKernel v (zpoint_ne_zero_of_re (by norm_num)) h₁ h₂).continuousAt.comp
    (by unfold zpoint; fun_prop)

open MeasureTheory in
private lemma quadraticPerronKernel_right_integral {v : ℝ} (hv : v ≠ 0) :
    I * (∫ t : ℝ, quadraticPerronKernel v (zpoint 2 t)) =
      (2 * (Real.pi : ℂ) * I) * (quadraticPerronWeight v : ℂ) := by
  have hi : Integrable (fun t => quadraticPerronKernel v (zpoint 2 t)) :=
    (integrable_inv_one_add_sq.const_mul (16 * Real.exp (v * 2))).mono'
      (continuous_quadraticPerronKernel_right v).aestronglyMeasurable
      (Eventually.of_forall (norm_quadraticPerronKernel_right v))
  have hlim := (intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id).const_mul I
  change Tendsto (quadraticPerronVertical v 2) atTop (𝓝 (I * ∫ t : ℝ, quadraticPerronKernel v (zpoint 2 t))) at hlim
  apply tendsto_nhds_unique hlim
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hdecay : Tendsto (fun T : ℝ => 8 * (Real.exp (v * 2) / (T * |v|))) atTop (𝓝 0) := by
    have ht := tendsto_inv_atTop_zero.const_mul (8 * Real.exp (v * 2) / |v|)
    rw [mul_zero] at ht
    exact ht.congr (fun T => by simp only [div_eq_mul_inv, mul_inv_rev]; ring)
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    ((eventually_gt_atTop (0 : ℝ)).mono (fun _ hT => quadraticPerronVertical_error hv (by norm_num) hT)) hdecay

private noncomputable def smoothedMollifiedSum (X : ℕ) (Y : ℝ) (ρ : ℂ) : ℂ :=
  ∑ n ∈ range ⌈Y⌉₊, LSeries.term (mollifiedZetaCoeff X) ρ n *
    (quadraticPerronWeight (Real.log (Y / n)) : ℂ)

set_option maxHeartbeats 800000 in
open MeasureTheory in
private lemma zetaDetector_right_integral {ρ : ℂ} (hre : 0 < ρ.re) (X : ℕ) {Y : ℝ}
    (hY : 0 < Y) (hYn : ∀ n : ℕ, (n : ℝ) ≠ Y) :
    I * (∫ t : ℝ, zetaDetectorIntegrand X (Real.log Y) ρ (zpoint 2 t)) =
      (2 * (Real.pi : ℂ) * I) * smoothedMollifiedSum X Y ρ := by
  let a := mollifiedZetaCoeff X
  let S := 2 * (Real.pi : ℂ) * I
  let v (n : ℕ) := Real.log (Y / n)
  let F (n : ℕ) (t : ℝ) := LSeries.term a ρ n * quadraticPerronKernel (v n) (zpoint 2 t)
  let G (t : ℝ) := (1 + t ^ (2 : ℕ))⁻¹
  let C := 16 * Real.exp (Real.log Y * 2)
  let g (n : ℕ) := ‖LSeries.term a (ρ + 2) n‖ * C
  have hC : 0 < C := by dsimp [C]; positivity
  have hg (n : ℕ) : 0 ≤ g n := mul_nonneg (norm_nonneg _) hC.le
  have hGi : Integrable G := integrable_inv_one_add_sq
  have hs0 : Summable (LSeries.term a (ρ + 2)) := (hasSum_mollifiedZeta (s := ρ + 2)
    (by simp only [Complex.add_re, Complex.re_ofNat]; linarith only [hre]) X).summable
  have hGs : Summable g := (summable_norm_iff.mpr hs0).mul_right C
  have he (n : ℕ) (z : ℂ) :
      LSeries.term a ρ n * quadraticPerronKernel (v n) z =
        LSeries.term a (ρ + z) n * quadraticPerronKernel (Real.log Y) z := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, quadraticPerronKernel, quadraticPerronKernel]
      dsimp [v]
      rw [log_ratio_cpow hY hn, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  have hnorm (n : ℕ) (t : ℝ) : ‖F n t‖ ≤ g n * G t := by
    change ‖LSeries.term a ρ n * quadraticPerronKernel (v n) (zpoint 2 t)‖ ≤ _
    rw [he, norm_mul]
    have hterm : ‖LSeries.term a (ρ + zpoint 2 t) n‖ = ‖LSeries.term a (ρ + 2) n‖ := by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      simp only [Complex.add_re, zpoint_re, Complex.re_ofNat]
    rw [hterm]
    exact (mul_le_mul_of_nonneg_left (norm_quadraticPerronKernel_right (Real.log Y) t) (norm_nonneg _)).trans_eq (by
      dsimp [g, C, G]; ring)
  have hcont (n : ℕ) : Continuous (F n) :=
    (continuous_quadraticPerronKernel_right (v n)).const_mul _
  have hFi (n : ℕ) : Integrable (F n) :=
    (hGi.const_mul (g n)).mono' (hcont n).aestronglyMeasurable (Eventually.of_forall (hnorm n))
  have hsum : Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    apply (hGs.mul_right (∫ t : ℝ, G t)).of_nonneg_of_le
    · intro n
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro n
      rw [← integral_const_mul]
      exact integral_mono (hFi n).norm (hGi.const_mul (g n)) (hnorm n)
  have hE (t : ℝ) : zetaDetectorIntegrand X (Real.log Y) ρ (zpoint 2 t) = ∑' n, F n t := by
    have hr : 1 < (ρ + zpoint 2 t).re := by rw [Complex.add_re, zpoint_re]; linarith only [hre]
    have hs0 : HasSum (LSeries.term a (ρ + zpoint 2 t))
        (riemannZeta (ρ + zpoint 2 t) * moebiusPolynomial X (ρ + zpoint 2 t)) := hasSum_mollifiedZeta hr X
    have hs := hs0.mul_right (quadraticPerronKernel (Real.log Y) (zpoint 2 t))
    simp_rw [F, he]
    exact hs.tsum_eq.symm
  have hT (n : ℕ) : I * (∫ t : ℝ, F n t) = S * (LSeries.term a ρ n * (quadraticPerronWeight (v n) : ℂ)) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, LSeries.term_zero]
    · have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hv : v n ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (div_pos hY hp) (fun h =>
        hYn n (by have h' := (div_eq_iff hp.ne').mp h; linarith only [h']))
      dsimp [F]
      rw [integral_const_mul, mul_left_comm I, quadraticPerronKernel_right_integral hv]
      ring
  have hsupp : ∀ n ∉ range ⌈Y⌉₊, LSeries.term a ρ n * (quadraticPerronWeight (v n) : ℂ) = 0 := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · have hnC : ⌈Y⌉₊ ≤ n := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
      have hYn' : Y ≤ n := (Nat.le_ceil Y).trans (by exact_mod_cast hnC)
      have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      have h := Real.log_nonpos (div_nonneg hY.le hp.le) ((div_le_one₀ hp).mpr hYn')
      rw [quadraticPerronWeight, if_neg (show ¬0 < v n from not_lt.mpr h), Complex.ofReal_zero, mul_zero]
  calc
    _ = I * ∑' n, (∫ t : ℝ, F n t) := by
      rw [MeasureTheory.integral_tsum_of_summable_integral_norm hFi hsum]
      exact congrArg (fun z : ℂ => I * z) (integral_congr_ae (Eventually.of_forall hE))
    _ = ∑' n, I * (∫ t : ℝ, F n t) := by rw [tsum_mul_left]
    _ = S * smoothedMollifiedSum X Y ρ := by
      simp_rw [hT]
      rw [tsum_mul_left, tsum_eq_sum hsupp]
      rfl

private lemma zeta_perron_integrand_eq_tsum {q c : ℝ} (hq : 0 < q) (hc : 1 < c) (t : ℝ) :
    (-deriv riemannZeta (zpoint c t) / riemannZeta (zpoint c t)) *
      perronIntegrand (Real.log q) (zpoint c t) =
        ∑' n, perronTerm q c n t := by
  have hs : 1 < (zpoint c t).re := by simpa only [zpoint_re] using hc
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries,
    ← tsum_mul_right]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [perronTerm]
  · simp only [perronTerm, if_neg hn, LSeries.term_of_ne_zero hn, perronIntegrand]
    rw [log_ratio_cpow hq hn]
    ring

private lemma mangoldtWeight_eq_reTerm {q c : ℝ} (hq : 0 < q) (n : ℕ) :
    mangoldtWeight q c n = q ^ c *
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mangoldtWeight]
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [mangoldtWeight, if_neg hn, show (c : ℂ) = (⟨c, 0⟩ : ℂ) from rfl,
    re_vonMangoldt_term c 0 hn, zero_mul, Real.cos_zero, mul_one,
    Real.log_div hq.ne' hn0.ne', mul_sub, Real.exp_sub, rpow_def_of_pos hq]
  rw [mul_comm c (Real.log q), neg_mul, Real.exp_neg]
  ring

private lemma summable_mangoldtWeight {q c : ℝ} (hq : 0 < q) (hc : 1 < c) :
    Summable (mangoldtWeight q c) := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : ℂ)) (by simpa using hc)
  have hr : Summable (fun n =>
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n).re) :=
    Complex.reCLM.summable h
  change Summable (fun n => mangoldtWeight q c n)
  simp_rw [mangoldtWeight_eq_reTerm hq]
  exact hr.mul_left _

private lemma norm_perronTerm_le {q c : ℝ} (hc : 0 < c) (n : ℕ) (t : ℝ) :
    ‖perronTerm q c n t‖ ≤ mangoldtWeight q c n / c := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [perronTerm, mangoldtWeight]
  simp only [perronTerm, mangoldtWeight, if_neg hn, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, norm_perron_integrand, zpoint_re, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
  rw [mul_comm (Real.log (q / (n : ℝ))) c]
  apply div_le_div_of_nonneg_left (Real.exp_nonneg _) hc
  simpa only [zpoint_re, abs_of_pos hc] using Complex.abs_re_le_norm (zpoint c t)

private lemma hasSum_perronTerm_vertical {q c T : ℝ} (hq : 0 < q) (hc : 1 < c) (hT : 0 < T) :
    HasSum (fun n => if n = 0 then 0 else
      (ArithmeticFunction.vonMangoldt n : ℂ) * perronVertical (Real.log (q / n)) c T)
      (zetaVertical q c T) := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hle : -T ≤ T := by linarith only [hT]
  have hcont (n : ℕ) : Continuous (perronTerm q c n) := by
    rcases eq_or_ne n 0 with rfl | hn
    · exact (show Continuous (fun _ : ℝ => (0 : ℂ)) from continuous_const).congr
        (fun t => by simp [perronTerm])
    have hEq : perronTerm q c n =
        fun t => (ArithmeticFunction.vonMangoldt n : ℂ) * perronIntegrand (Real.log (q / n)) (zpoint c t) :=
      funext fun t => if_neg hn
    rw [hEq]
    exact continuous_const.mul (continuous_perron_vertical _ hc0.ne')
  let μ := MeasureTheory.volume.restrict (Set.Ioc (-T) T)
  have hint (n : ℕ) : MeasureTheory.Integrable (perronTerm q c n) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      ((hcont n).intervalIntegrable (-T) T)
  have hSum : Summable (fun n => ∫ t, ‖perronTerm q c n t‖ ∂μ) := by
    apply (((summable_mangoldtWeight hq hc).div_const c).mul_left (2 * T)).of_nonneg_of_le
    · exact fun n => MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
    · intro n
      change (∫ t in Set.Ioc (-T) T, ‖perronTerm q c n t‖) ≤ 2 * T * (mangoldtWeight q c n / c)
      rw [← intervalIntegral.integral_of_le hle]
      have hM := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle
        ((hcont n).norm.intervalIntegrable (-T) T) intervalIntegrable_const
        (fun t _ => norm_perronTerm_le hc0 n t)
      rw [intervalIntegral.integral_const, smul_eq_mul,
        show T - (-T) = 2 * T by ring] at hM
      exact hM
  have h := (MeasureTheory.hasSum_integral_of_summable_integral_norm hint hSum).mul_left I
  simp only [μ, ← intervalIntegral.integral_of_le hle] at h
  have hp (n : ℕ) : I * (∫ t in -T..T, perronTerm q c n t) =
      if n = 0 then 0 else (ArithmeticFunction.vonMangoldt n : ℂ) *
        perronVertical (Real.log (q / n)) c T := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [perronTerm]
    simp only [perronTerm, if_neg hn, perronVertical]
    rw [intervalIntegral.integral_const_mul, mul_left_comm]
  rw [show (fun n => I * (∫ t in -T..T, perronTerm q c n t)) = _ from funext hp] at h
  simp_rw [← zeta_perron_integrand_eq_tsum hq hc] at h
  exact h

private lemma norm_zetaVertical_sub_psi_le_error {q c T : ℝ} (hq : 0 < q) (hc : 1 < c) (hT : 0 < T)
    (hnot : ∀ n : ℕ, (n : ℝ) ≠ q) (herror : Summable (kernelErrorWeight q c)) :
    ‖zetaVertical q c T - (2 * (Real.pi : ℂ) * I) * (Chebyshev.psi q : ℂ)‖ ≤
      (2 / T) * ∑' n, kernelErrorWeight q c n := by
  classical
  let Z := 2 * (Real.pi : ℂ) * I
  let S := Ioc 0 ⌊q⌋₊
  let M (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)
  let a (n : ℕ) := if n = 0 then 0 else M n * perronVertical (Real.log (q / n)) c T
  let b (n : ℕ) := if n ∈ S then Z * M n else 0
  have ha : HasSum a (zetaVertical q c T) := hasSum_perronTerm_vertical hq hc hT
  have hb : HasSum b (Z * (Chebyshev.psi q : ℂ)) := by
    have hs : HasSum b (∑ n ∈ S, b n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => if_neg hn)
    have he : (∑ n ∈ S, b n) = Z * (Chebyshev.psi q : ℂ) := by
      simp only [Chebyshev.psi]
      push_cast
      rw [mul_sum]
      exact sum_congr rfl (fun n hn => if_pos hn)
    exact he ▸ hs
  have hbound (n : ℕ) : ‖a n - b n‖ ≤ (2 / T) * kernelErrorWeight q c n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [a, b, S, kernelErrorWeight, mangoldtWeight]
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hlog : Real.log (q / n) ≠ 0 := by
      intro h
      have he := Real.log_injOn_pos (Set.mem_Ioi.2 (div_pos hq hn0)) (Set.mem_Ioi.2 zero_lt_one) (h.trans Real.log_one.symm)
      exact (hnot n) ((div_eq_one_iff_eq hn0.ne').mp he).symm
    have hS : n ∈ S ↔ 0 < Real.log (q / n) := by
      rw [Real.log_pos_iff (div_nonneg hq.le hn0.le), lt_div_iff₀ hn0, one_mul]
      simp only [S, mem_Ioc, Nat.pos_of_ne_zero hn, true_and]
      exact (Nat.le_floor_iff hq.le).trans ⟨fun h => lt_of_le_of_ne h (hnot n), le_of_lt⟩
    have he : a n - b n = M n * (perronVertical (Real.log (q / n)) c T -
        (if 0 < Real.log (q / n) then Z else 0)) := by
      simp only [a, b, if_neg hn, hS, mul_sub]
      split_ifs <;> ring
    rw [he, norm_mul]
    apply (mul_le_mul_of_nonneg_left (perronVertical_error hlog (zero_lt_one.trans hc) hT)
      (norm_nonneg (M n))).trans_eq
    rw [kernelErrorWeight, mangoldtWeight, if_neg hn, show ‖M n‖ = ArithmeticFunction.vonMangoldt n by
      unfold M; rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] ]
    rw [mul_comm (Real.log (q / (n : ℝ))) c]
    ring
  have hs : Summable (fun n => ‖a n - b n‖) :=
    (herror.mul_left (2 / T)).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  rw [← (ha.sub hb).tsum_eq]
  exact (norm_tsum_le_tsum_norm hs).trans
    ((hs.tsum_le_tsum hbound (herror.mul_left (2 / T))).trans_eq tsum_mul_left)

private lemma halfInteger_ne_nat (m n : ℕ) : (n : ℝ) ≠ (m : ℝ) + 1 / 2 := by
  intro h
  rcases le_or_gt n m with hn | hn
  · have hle : (n : ℝ) ≤ m := by exact_mod_cast hn
    linarith only [hle, h]
  · have hle : ((m : ℝ) + 1) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
    linarith only [hle, h]

private noncomputable def smoothedMollifiedTail (X : ℕ) (Y : ℝ) (ρ : ℂ) : ℂ :=
  ∑ n ∈ (range ⌈Y⌉₊).filter (fun n => X < n), LSeries.term (mollifiedZetaCoeff X) ρ n *
    (quadraticPerronWeight (Real.log (Y / n)) : ℂ)

private noncomputable def detectorLeftIntegral (X : ℕ) (Y : ℝ) (ρ : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ, zetaDetectorIntegrand X (Real.log Y) ρ (zpoint (1 / 2 - ρ.re) t))

private lemma smoothedMollifiedSum_eq {X : ℕ} (hX : 1 ≤ X) {Y : ℝ} (hY : 1 < Y) (ρ : ℂ) :
    smoothedMollifiedSum X Y ρ = (((1 - Y⁻¹) ^ (2 : ℕ) : ℝ) : ℂ) + smoothedMollifiedTail X Y ρ := by
  classical
  let f (n : ℕ) := LSeries.term (mollifiedZetaCoeff X) ρ n * (quadraticPerronWeight (Real.log (Y / n)) : ℂ)
  let U := range ⌈Y⌉₊
  let A := U.filter (fun n => X < n)
  let B := U.filter (fun n => ¬ X < n)
  have hpart : (∑ n ∈ A, f n) + (∑ n ∈ B, f n) = ∑ n ∈ U, f n := sum_filter_add_sum_filter_not _ _ _
  change (∑ n ∈ U, f n) = _ + (∑ n ∈ A, f n)
  rw [← hpart, add_comm]
  congr 1
  have hB1 : 1 ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, not_lt.mpr hX⟩
    have hh := hY.trans_le (Nat.le_ceil Y)
    exact_mod_cast hh
  have hBrest (n : ℕ) (hn : n ∈ B) (h₁ : n ≠ 1) : f n = 0 := by
    have hnX := le_of_not_gt (Finset.mem_filter.mp hn).2
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [f, LSeries.term_zero]
    · dsimp [f]
      rw [LSeries.term_of_ne_zero hn0, mollifiedZetaCoeff_small hnX, if_neg h₁, zero_div, zero_mul]
  rw [Finset.sum_eq_single_of_mem 1 hB1 hBrest]
  dsimp [f]
  have he : LSeries.term (mollifiedZetaCoeff X) ρ 1 = 1 := by
    rw [LSeries.term_of_ne_zero (by norm_num : (1 : ℕ) ≠ 0), mollifiedZetaCoeff_small hX]
    norm_num
  rw [he, one_mul, Nat.cast_one, div_one, quadraticPerronWeight, if_pos (Real.log_pos hY), Real.exp_neg,
    Real.exp_log (zero_lt_one.trans hY)]

private lemma smoothedMollifiedSum_at_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hreal : 1 / 2 < ρ.re)
    (hreal' : ρ.re < 1) (X : ℕ) {Y : ℝ} (hY : 0 < Y) (hYn : ∀ n : ℕ, (n : ℝ) ≠ Y) :
    smoothedMollifiedSum X Y ρ =
      moebiusPolynomial X 1 * quadraticPerronKernel (Real.log Y) (1 - ρ) + detectorLeftIntegral X Y ρ := by
  let S := 2 * (Real.pi : ℂ) * I
  have hS : S ≠ 0 := by dsimp [S]; exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have h := zetaDetector_vertical_difference hρ hreal hreal' X (Real.log Y)
  rw [zetaDetector_right_integral (by linarith only [hreal]) X hY hYn] at h
  have he : S * detectorLeftIntegral X Y ρ =
      I * ∫ t : ℝ, zetaDetectorIntegrand X (Real.log Y) ρ (zpoint (1 / 2 - ρ.re) t) := by
    dsimp [S, detectorLeftIntegral]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  apply mul_left_cancel₀ hS
  rw [mul_add, he]
  linear_combination h

private lemma norm_detector_pole_le {ρ : ℂ} (hr : 0 ≤ ρ.re) {Y : ℝ} (hY : 1 ≤ Y)
    (hi : 0 < |ρ.im|) (X : ℕ) :
    ‖moebiusPolynomial X 1 * quadraticPerronKernel (Real.log Y) (1 - ρ)‖ ≤
      (2 * (X : ℝ) * Y) / |ρ.im| ^ (3 : ℕ) := by
  have h₀ : |ρ.im| ≤ ‖(1 : ℂ) - ρ‖ := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using Complex.abs_im_le_norm ((1 : ℂ) - ρ)
  have h₁ : |ρ.im| ≤ ‖(1 : ℂ) - ρ + 1‖ := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, Complex.add_im, add_zero, abs_neg]
      using Complex.abs_im_le_norm ((1 : ℂ) - ρ + 1)
  have h₂ : |ρ.im| ≤ ‖(1 : ℂ) - ρ + 2‖ := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, Complex.add_im, Complex.im_ofNat, add_zero, abs_neg]
      using Complex.abs_im_le_norm ((1 : ℂ) - ρ + 2)
  have hp : |ρ.im| ^ (3 : ℕ) ≤ ‖(1 : ℂ) - ρ‖ * ‖1 - ρ + 1‖ * ‖1 - ρ + 2‖ := by
    simpa only [pow_succ, pow_zero, one_mul] using
      mul_le_mul (mul_le_mul h₀ h₁ hi.le (norm_nonneg _)) h₂ hi.le (by positivity)
  have hExp : Real.exp (Real.log Y * (1 - ρ.re)) ≤ Y := by
    rw [← Real.rpow_def_of_pos (zero_lt_one.trans_le hY)]
    exact (rpow_le_rpow_of_exponent_le hY (by linarith only [hr])).trans_eq (rpow_one _)
  have hK : ‖quadraticPerronKernel (Real.log Y) (1 - ρ)‖ ≤ (2 * Y) / |ρ.im| ^ (3 : ℕ) := by
    rw [norm_quadraticPerronKernel, Complex.sub_re, Complex.one_re]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hExp (by norm_num)) (by positivity) hp
  rw [norm_mul]
  apply (mul_le_mul (norm_moebiusPolynomial_le X (by norm_num : 0 ≤ (1 : ℂ).re)) hK (norm_nonneg _) (by positivity)).trans_eq
  ring

private noncomputable def detectorX (T : ℝ) : ℕ := ⌈T⌉₊

private noncomputable def detectorY (T : ℝ) : ℝ := (⌈T ^ (4 / 3 : ℝ)⌉₊ : ℝ) + 1 / 2

private lemma detector_parameter_bounds {T : ℝ} (hT : 1 ≤ T) :
    (1 ≤ detectorX T ∧ (detectorX T : ℝ) ≤ 2 * T) ∧
    (T ^ (4 / 3 : ℝ) ≤ detectorY T ∧ detectorY T ≤ 3 * T ^ (4 / 3 : ℝ)) := by
  have hx₁ := Nat.le_ceil T
  have hx₂ := (Nat.ceil_lt_add_one (zero_le_one.trans hT)).le
  have hp : 1 ≤ T ^ (4 / 3 : ℝ) := one_le_rpow hT (by norm_num)
  have hy₁ := Nat.le_ceil (T ^ (4 / 3 : ℝ))
  have hy₂ := (Nat.ceil_lt_add_one (zero_le_one.trans hp)).le
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact_mod_cast hT.trans hx₁
  · change (⌈T⌉₊ : ℝ) ≤ 2 * T
    linarith only [hx₂, hT]
  · dsimp [detectorY]
    linarith only [hy₁]
  · dsimp [detectorY]
    linarith only [hy₂, hp]

private lemma zetaDetector_dichotomy :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ, riemannZeta ρ = 0 → 7 / 12 ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| →
      (1 / 8 : ℝ) ≤ ‖smoothedMollifiedTail (detectorX T) (detectorY T) ρ‖ ∨
      (1 / 8 : ℝ) ≤ ‖detectorLeftIntegral (detectorX T) (detectorY T) ρ‖ := by
  have hTend : Tendsto (fun T : ℝ => T ^ (4 / 3 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hDecay : Tendsto (fun T : ℝ => T ^ (-(2 / 3) : ℝ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hTend.eventually_ge_atTop (4 : ℝ),
    (tendsto_order.mp hDecay).2 (1 / 192) (by norm_num)] with T hT hTY hD
  intro ρ hz hre hre' him
  let X := detectorX T
  let Y := detectorY T
  have hT0 := zero_lt_one.trans_le hT
  obtain ⟨⟨hX₁,hX₂⟩,hY₁,hY₂⟩ := detector_parameter_bounds hT
  have hY4 : 4 ≤ Y := hTY.trans hY₁
  have hY0 : 0 < Y := by linarith only [hY4]
  have hYgt : 1 < Y := by linarith only [hY4]
  have hYne (n : ℕ) : (n : ℝ) ≠ Y := halfInteger_ne_nat _ _
  let U := moebiusPolynomial X 1 * quadraticPerronKernel (Real.log Y) (1 - ρ)
  have hU : ‖U‖ ≤ 1 / 16 := by
    apply (norm_detector_pole_le (by linarith only [hre]) hYgt.le (hT0.trans_le him) X).trans
    calc
      _ ≤ (2 * (2 * T) * (3 * T ^ (4 / 3 : ℝ))) / T ^ (3 : ℕ) := by
        apply div_le_div₀ (by positivity) _ (by positivity) (pow_le_pow_left₀ hT0.le him _)
        apply mul_le_mul (mul_le_mul_of_nonneg_left hX₂ (by norm_num)) hY₂ hY0.le (by positivity)
      _ = 12 * T ^ (-(2 / 3) : ℝ) := by
        rw [show 2 * (2 * T) * (3 * T ^ (4 / 3 : ℝ)) = 12 * (T * T ^ (4 / 3 : ℝ)) by ring, mul_div_assoc]
        congr 1
        calc
          _ = (T ^ (1 : ℝ) * T ^ (4 / 3 : ℝ)) / T ^ (3 : ℝ) := by rw [Real.rpow_one, Real.rpow_ofNat]
          _ = _ := by rw [← Real.rpow_add hT0, ← Real.rpow_sub hT0]; norm_num
      _ ≤ _ := by linarith only [hD]
  have hYinv : Y⁻¹ ≤ 1 / 4 := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hY4
  let f := (((1 - Y⁻¹) ^ (2 : ℕ) : ℝ) : ℂ)
  have hf : 9 / 16 ≤ ‖f‖ := by
    dsimp [f]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) (show 3 / 4 ≤ 1 - Y⁻¹ by linarith only [hYinv]) 2
    norm_num at h
    exact h
  have hS := smoothedMollifiedSum_at_zero hz (by linarith only [hre]) hre' X hY0 hYne
  rw [smoothedMollifiedSum_eq hX₁ hYgt] at hS
  have he : f = U + detectorLeftIntegral X Y ρ - smoothedMollifiedTail X Y ρ := by
    change f + smoothedMollifiedTail X Y ρ = U + detectorLeftIntegral X Y ρ at hS
    linear_combination hS
  by_contra! hh
  have hb := norm_sub_le (U + detectorLeftIntegral X Y ρ) (smoothedMollifiedTail X Y ρ)
  rw [← he] at hb
  linarith only [hf, hU, hh.1, hh.2, hb, norm_add_le U (detectorLeftIntegral X Y ρ)]

private def DetectorMomentEstimate (f : ℝ → ℂ → ℂ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, ∀ᶠ H : ℝ in atTop, ∀ σ ∈ Set.Icc (7 / 12 : ℝ) 1,
    ∀ S : Finset ℂ, S ⊆ zerosUpTo (2 * H) → (∀ z ∈ S, H ≤ |z.im| ∧ σ ≤ z.re) →
      (↑S : Set ℂ).Pairwise (fun z w => 1 ≤ |z.im - w.im|) →
      ∑ z ∈ S, ‖f H z‖ ^ (2 : ℕ) ≤ A * Real.log H ^ B * H ^ ((8 / 3 : ℝ) * (1 - σ))

private lemma separatedShellDensity_of_detector
    (hTail : DetectorMomentEstimate (fun T => smoothedMollifiedTail (detectorX T) (detectorY T)))
    (hLeft : DetectorMomentEstimate (fun T => detectorLeftIntegral (detectorX T) (detectorY T))) :
    SeparatedShellDensity (8 / 3) := by
  obtain ⟨A, hA, B, hTail⟩ := hTail
  obtain ⟨C, hC, D, hLeft⟩ := hLeft
  let K := max B D
  refine ⟨64 * (A + C), by positivity, K, ?_⟩
  filter_upwards [zetaDetector_dichotomy, hTail, hLeft, eventually_ge_atTop (Real.exp (1 : ℝ))]
    with H hDetect hTail hLeft hH
  intro σ hσ S hS hSh hsep
  let f (z : ℂ) := smoothedMollifiedTail (detectorX H) (detectorY H) z
  let g (z : ℂ) := detectorLeftIntegral (detectorX H) (detectorY H) z
  let L := Real.log H
  let P := H ^ ((8 / 3 : ℝ) * (1 - σ))
  have hH0 := (Real.exp_pos _).trans_le hH
  have hL : 1 ≤ L := by
    have ht := Real.log_le_log (Real.exp_pos 1) hH
    rwa [Real.log_exp] at ht
  have hpoint (z : ℂ) (hz : z ∈ S) : (1 / 64 : ℝ) ≤ ‖f z‖ ^ (2 : ℕ) + ‖g z‖ ^ (2 : ℕ) := by
    have hm := mem_zerosUpTo.mp (hS hz)
    have hre : 7 / 12 ≤ z.re := hσ.1.trans (hSh z hz).2
    rcases hDetect z hm.1 hre hm.2.2.1 (hSh z hz).1 with h | h
    · have h' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8) h 2
      norm_num at h'
      exact h'.trans (le_add_of_nonneg_right (sq_nonneg _))
    · have h' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8) h 2
      norm_num at h'
      exact h'.trans (le_add_of_nonneg_left (sq_nonneg _))
  have hsum : (S.card : ℝ) / 64 ≤ (∑ z ∈ S, ‖f z‖ ^ (2 : ℕ)) + ∑ z ∈ S, ‖g z‖ ^ (2 : ℕ) := by
    have hh := Finset.sum_le_sum (s := S) hpoint
    simpa only [Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv, one_div, Finset.sum_add_distrib] using hh
  have hF : (∑ z ∈ S, ‖f z‖ ^ (2 : ℕ)) ≤ A * L ^ K * P :=
    (hTail σ hσ S hS hSh hsep).trans (by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (le_max_left _ _)) hA.le) (rpow_nonneg hH0.le _))
  have hG : (∑ z ∈ S, ‖g z‖ ^ (2 : ℕ)) ≤ C * L ^ K * P :=
    (hLeft σ hσ S hS hSh hsep).trans (by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (le_max_right _ _)) hC.le) (rpow_nonneg hH0.le _))
  change (S.card : ℝ) ≤ 64 * (A + C) * L ^ K * P
  nlinarith only [hsum, hF, hG]

private lemma harmonicWeight_le_log (N : ℕ) : harmonicWeight N ≤ 1 + Real.log (N : ℝ) := by
  rw [harmonicWeight_eq_sum_Icc]
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log N

private lemma sum_eq_sum_dyadic_blocks (f : ℕ → ℂ) (J : ℕ) :
    ∑ n ∈ Ico 1 ((2 : ℕ) ^ J), f n = ∑ j ∈ range J, ∑ k ∈ range ((2 : ℕ) ^ j), f ((2 : ℕ) ^ j + k) := by
  induction J with
  | zero => simp
  | succ j ih =>
    have hJ : 1 ≤ (2 : ℕ) ^ j := Nat.succ_le_of_lt (by positivity)
    have hmono : (2 : ℕ) ^ j ≤ 2 ^ j.succ := by rw [pow_succ]; omega
    have hd : (2 : ℕ) ^ j.succ - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
    rw [← Finset.sum_Ico_consecutive f hJ hmono, ih, Finset.sum_range_succ,
      Finset.sum_Ico_eq_sum_range, hd]

private lemma norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ z ∈ S, f z‖ ^ (2 : ℕ) ≤ (S.card : ℝ) * ∑ z ∈ S, ‖f z‖ ^ (2 : ℕ) :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _).trans (sq_sum_le_card_mul_sum_sq (s := S) (f := fun z => ‖f z‖))

private noncomputable def detectorWeight (Y : ℝ) (n : ℕ) : ℝ := max 0 (1 - (n : ℝ) / Y) ^ (2 : ℕ)

private lemma detectorWeight_eq {Y : ℝ} (hY : 0 < Y) {n : ℕ} (hn : 0 < n) :
    quadraticPerronWeight (Real.log (Y / n)) = detectorWeight Y n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : 0 < Y / (n : ℝ) := div_pos hY hn0
  rcases lt_or_ge (n : ℝ) Y with h | h
  · rw [quadraticPerronWeight, if_pos (log_pos ((one_lt_div₀ hn0).mpr h)), Real.exp_neg, Real.exp_log hp]
    have hE : (Y / (n : ℝ))⁻¹ = (n : ℝ) / Y := inv_div _ _
    rw [hE, detectorWeight, max_eq_right ((sub_nonneg.mpr ((div_le_one₀ hY).mpr h.le)))]
  · rw [quadraticPerronWeight, if_neg (not_lt.mpr (log_nonpos hp.le ((div_le_one₀ hn0).mpr h))),
      detectorWeight, max_eq_left (sub_nonpos.mpr ((one_le_div₀ hY).mpr h))]
    norm_num

private lemma detectorWeight_nonneg (Y : ℝ) (n : ℕ) : 0 ≤ detectorWeight Y n := sq_nonneg _

private lemma detectorWeight_anti {Y : ℝ} (hY : 0 < Y) : Antitone (detectorWeight Y) := by
  intro m n hmn
  apply pow_le_pow_left₀ (le_max_left _ _) _ 2
  exact max_le_max_left 0 (sub_le_sub_left (div_le_div_of_nonneg_right (by exact_mod_cast hmn) hY.le) _)

private lemma detectorWeight_le_one {Y : ℝ} (hY : 0 < Y) (n : ℕ) : detectorWeight Y n ≤ 1 := by
  have h : max (0 : ℝ) (1 - (n : ℝ) / Y) ≤ 1 := max_le zero_le_one (sub_le_self _ (by positivity))
  unfold detectorWeight
  simpa only [one_pow] using pow_le_pow_left₀ (le_max_left (0 : ℝ) (1 - (n : ℝ) / Y)) h 2

private noncomputable def tailCoefficient (X : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  if X < n then mollifiedZetaCoeff X n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) else 0

private noncomputable def tailWeight (Y σ : ℝ) (ρ : ℂ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (σ - ρ.re) * detectorWeight Y n

private noncomputable def smoothedTailBlock (X : ℕ) (Y σ : ℝ) (ρ : ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ range ((2 : ℕ) ^ j), (tailWeight Y σ ρ (2 ^ j + k) : ℂ) * tailCoefficient X σ (2 ^ j + k) *
    imaginaryPhase (Real.log ((2 ^ j + k : ℕ) : ℝ)) (-ρ.im)

private lemma smoothedMollifiedTail_eq_blocks {X : ℕ} {Y σ : ℝ} (hY : 0 < Y) (ρ : ℂ) {J : ℕ}
    (hJ : ⌈Y⌉₊ ≤ (2 : ℕ) ^ J) :
    smoothedMollifiedTail X Y ρ = ∑ j ∈ range J, smoothedTailBlock X Y σ ρ j := by
  let f (n : ℕ) := (tailWeight Y σ ρ n : ℂ) * tailCoefficient X σ n * imaginaryPhase (Real.log (n : ℝ)) (-ρ.im)
  have hf (n : ℕ) (hn : X < n) :
      LSeries.term (mollifiedZetaCoeff X) ρ n * (quadraticPerronWeight (Real.log (Y / n)) : ℂ) = f n := by
    have hn0 : 0 < n := (Nat.zero_le X).trans_lt hn
    have hp : 0 < (n : ℝ) := by exact_mod_cast hn0
    have hPhase : (n : ℂ) ^ (-((ρ.im : ℂ) * Complex.I)) = imaginaryPhase (Real.log (n : ℝ)) (-ρ.im) := by
      rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn0.ne'), ← Complex.natCast_log, imaginaryPhase]
      congr 1
      push_cast
      ring
    rw [LSeries.term_of_ne_zero hn0.ne', div_eq_mul_inv, ← Complex.cpow_neg, cpow_split_re_im ρ hn0, hPhase,
      detectorWeight_eq hY hn0]
    dsimp [f, tailCoefficient, tailWeight]
    rw [if_pos hn, Complex.ofReal_mul]
    have hr : ((((n : ℝ) ^ (σ - ρ.re)) : ℝ) : ℂ) * ((((n : ℝ) ^ (-σ)) : ℝ) : ℂ) =
        ((((n : ℝ) ^ (-ρ.re)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hp, show σ - ρ.re + -σ = -ρ.re by ring]
    linear_combination -hr * (mollifiedZetaCoeff X n * ((detectorWeight Y n : ℝ) : ℂ) *
      imaginaryPhase (Real.log (n : ℝ)) (-ρ.im))
  have h0 : f 0 = 0 := by simp [f, tailCoefficient]
  have hfin : ∀ n ≥ ⌈Y⌉₊, f n = 0 := by
    intro n hn
    have hh : Y ≤ n := (Nat.le_ceil Y).trans (by exact_mod_cast hn)
    have hW : detectorWeight Y n = 0 := by
      rw [detectorWeight, max_eq_left (sub_nonpos.mpr ((one_le_div₀ hY).mpr hh))]
      norm_num
    simp [f, tailWeight, hW]
  unfold smoothedMollifiedTail
  calc
    _ = ∑ n ∈ (range ⌈Y⌉₊).filter (fun n => X < n), f n :=
      Finset.sum_congr rfl fun n hn => hf n (Finset.mem_filter.mp hn).2
    _ = ∑ n ∈ range ⌈Y⌉₊, f n := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hnr hn
      have hnot : ¬ X < n := fun h => hn (Finset.mem_filter.mpr ⟨hnr, h⟩)
      simp [f, tailCoefficient, hnot]
    _ = ∑ n ∈ range ((2 : ℕ) ^ J), f n := by
      apply Finset.sum_subset (Finset.range_subset_range.mpr hJ)
      intro n _ hn
      exact hfin n (Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h)))
    _ = ∑ n ∈ Ico 1 ((2 : ℕ) ^ J), f n := by
      symm
      apply Finset.sum_subset (by
        intro n hn
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2)
      intro n hnr hni
      have hn0 : n = 0 := by
        have hlt := Finset.mem_range.mp hnr
        by_contra hne
        exact hni (Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, hlt⟩)
      simpa only [hn0] using h0
    _ = _ := sum_eq_sum_dyadic_blocks f J

private lemma sum_tailCoefficient_sq_le (X : ℕ) {M : ℕ} (hM : 0 < M) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ n ∈ range M, ‖tailCoefficient X σ (M + n)‖ ^ (2 : ℕ) ≤
      (M : ℝ) ^ (-(2 * σ)) * ((2 * M : ℕ) : ℝ) * harmonicWeight (2 * M) ^ (3 : ℕ) := by
  have hMp : 0 < (M : ℝ) := by exact_mod_cast hM
  have hcoeff (n : ℕ) (hn : M ≤ n) : ‖tailCoefficient X σ n‖ ^ (2 : ℕ) ≤
      (M : ℝ) ^ (-(2 * σ)) * (n.divisors.card : ℝ) ^ (2 : ℕ) := by
    unfold tailCoefficient
    split_ifs with hx
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg n) _),
        mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n), Nat.cast_ofNat,
        show -σ * 2 = -(2 * σ) by ring, mul_comm]
      exact mul_le_mul (rpow_le_rpow_of_nonpos hMp (by exact_mod_cast hn) (by linarith only [hσ]))
        (pow_le_pow_left₀ (norm_nonneg _) (norm_mollifiedZetaCoeff_le X n) _) (sq_nonneg _) (by positivity)
    · simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity
  have hs : ∑ n ∈ range M, ((M + n).divisors.card : ℝ) ^ (2 : ℕ) ≤
      ((2 * M : ℕ) : ℝ) * harmonicWeight (2 * M) ^ (3 : ℕ) := by
    have he : (∑ n ∈ Ico M (2 * M), (n.divisors.card : ℝ) ^ (2 : ℕ)) =
        ∑ n ∈ range M, ((M + n).divisors.card : ℝ) ^ (2 : ℕ) := by
      rw [Finset.sum_Ico_eq_sum_range, show 2 * M - M = M by omega]
    rw [← he]
    apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => sq_nonneg _)).trans (divisor_square_sum_le _)
    intro n hn
    obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Icc.mpr ⟨hM.trans_le hl, hu.le⟩
  calc
    _ ≤ ∑ n ∈ range M, (M : ℝ) ^ (-(2 * σ)) * ((M + n).divisors.card : ℝ) ^ (2 : ℕ) :=
      Finset.sum_le_sum fun n _ => hcoeff _ (Nat.le_add_right _ _)
    _ ≤ _ := by
      rw [← Finset.mul_sum, mul_assoc]
      exact mul_le_mul_of_nonneg_left hs (by positivity)

set_option maxHeartbeats 900000 in
private lemma detector_tail_moment :
    DetectorMomentEstimate (fun T => smoothedMollifiedTail (detectorX T) (detectorY T)) := by
  let C := 10 / Real.log 2 + 1
  have hlog₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨120000000 * C ^ (4 : ℕ), by positivity, 10, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with H hH
  intro σ hσ S hS _hSh hsep
  let X := detectorX H
  let Y := detectorY H
  let L := ⌈Y⌉₊
  let J := Nat.log 2 L + 1
  let V := Real.log H
  let P := H ^ ((8 / 3 : ℝ) * (1 - σ))
  have hH1 : 1 ≤ H := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hH
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  have hV : 1 ≤ V := by
    have hh := Real.log_le_log (Real.exp_pos 1) hH
    rwa [Real.log_exp] at hh
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  obtain ⟨⟨_hX1, _hX2⟩, hY1, hY2⟩ := detector_parameter_bounds hH1
  have hPow : 1 ≤ H ^ (4 / 3 : ℝ) := one_le_rpow hH1 (by norm_num)
  have hY0 : 0 < Y := zero_lt_one.trans_le (hPow.trans hY1)
  have hL0 : 0 < L := by
    have hL' : 0 < (L : ℝ) := hY0.trans_le (Nat.le_ceil Y)
    exact_mod_cast hL'
  have hL' : (L : ℝ) ≤ 4 * H ^ (4 / 3 : ℝ) := by
    have h := Nat.ceil_lt_add_one hY0.le
    change (L : ℝ) < Y + 1 at h
    linarith only [h, hY2, hPow]
  have hLog {t : ℝ} (ht : 0 < t) (htt : t ≤ 8 * H ^ (4 / 3 : ℝ)) : Real.log t ≤ 10 * V := by
    have h := Real.log_le_log ht htt
    rw [Real.log_mul (by norm_num) (rpow_pos_of_pos hH0 _).ne', Real.log_rpow hH0] at h
    have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    dsimp [V] at hV ⊢
    linarith only [h, hb, hV]
  have hJ : (J : ℝ) ≤ C * V := by
    have h := Nat.pow_log_le_self 2 hL0.ne'
    have h' : (2 : ℝ) ^ (Nat.log 2 L) ≤ (L : ℝ) := by exact_mod_cast h
    have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (Nat.log 2 L)) h'
    rw [Real.log_pow] at hlog
    have hp := hLog (Nat.cast_pos.mpr hL0) (by
      have hh : 0 ≤ H ^ (4 / 3 : ℝ) := by positivity
      linarith only [hL', hh])
    have hq := (le_div_iff₀ hlog₂).mpr (hlog.trans hp)
    dsimp [J, C]
    push_cast
    linarith only [hq, hV, show (10 * V) / Real.log 2 = (10 / Real.log 2) * V by ring]
  have hcut : ⌈Y⌉₊ ≤ (2 : ℕ) ^ J := (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) L).le
  let b (j : ℕ) (z : ℂ) := smoothedTailBlock X Y σ z j
  have hblock (j : ℕ) (hj : j ∈ range J) :
      ∑ z ∈ S, ‖b j z‖ ^ (2 : ℕ) ≤ 120000000 * (J : ℝ) ^ (2 : ℕ) * (V ^ (6 : ℕ) * P) := by
    let M := (2 : ℕ) ^ j
    let N := 2 * M
    have hM : 0 < M := by dsimp [M]; positivity
    have hMp : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
    have hN0 : 0 < (N : ℝ) := by dsimp [N]; positivity
    have hj' : j ≤ Nat.log 2 L := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hML : M ≤ L := (Nat.pow_le_pow_right (by norm_num) hj').trans (Nat.pow_log_le_self 2 hL0.ne')
    have hMbound : (M : ℝ) ≤ 4 * H ^ (4 / 3 : ℝ) := (Nat.cast_le.mpr hML).trans hL'
    have hNbound : (N : ℝ) ≤ 8 * H ^ (4 / 3 : ℝ) := by dsimp [N]; push_cast; linarith only [hMbound]
    have hlogN := hLog hN0 hNbound
    have hN1 : (1 : ℝ) ≤ N := by
      change (1 : ℝ) ≤ ((2 * M : ℕ) : ℝ)
      exact_mod_cast (show 1 ≤ 2 * M by omega)
    have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    have hHarm : harmonicWeight N ≤ 11 * V := by linarith only [harmonicWeight_le_log N, hlogN, hV]
    by_cases hActive : X < N
    · have hHt : H ≤ (N : ℝ) := (Nat.le_ceil H).trans (Nat.cast_le.mpr hActive.le)
      let a := tailCoefficient X σ
      let w (z : ℂ) (n : ℕ) := tailWeight Y σ z (M + n)
      have hu (z : ℂ) (hz : z ∈ S) : |(-z.im)| ≤ 2 * H := by
        rw [abs_neg]
        exact (mem_zerosUpTo.mp (hS hz)).2.2.2
      have hsep' : (S : Set ℂ).Pairwise (fun z w => 1 ≤ |-z.im - -w.im|) := by
        intro z hz v hv he
        have hh := hsep hz hv he
        change 1 ≤ |z.im - v.im| at hh
        change 1 ≤ |-z.im - -v.im|
        rw [show -z.im - -v.im = -(z.im - v.im) by ring, abs_neg]
        exact hh
      have hw0 (z : ℂ) (n : ℕ) : 0 ≤ w z n := by dsimp [w,tailWeight]; exact mul_nonneg (by positivity) (detectorWeight_nonneg _ _)
      have hw (z : ℂ) (hz : z ∈ S) : Antitone (w z) := by
        have hβ : σ - z.re ≤ 0 := sub_nonpos.mpr (_hSh z hz).2
        intro n l hn
        dsimp [w,tailWeight]
        exact mul_le_mul (rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.add_le_add_left hn M) hβ)
          (detectorWeight_anti hY0 (Nat.add_le_add_left hn M)) (detectorWeight_nonneg _ _) (by positivity)
      have hw1 (z : ℂ) (hz : z ∈ S) : w z 0 ≤ 1 := by
        have hm1 : (1 : ℝ) ≤ ((M + 0 : ℕ) : ℝ) := by exact_mod_cast hM
        have hr : ((M + 0 : ℕ) : ℝ) ^ (σ - z.re) ≤ 1 := by
          rw [← rpow_zero ((M + 0 : ℕ) : ℝ)]
          exact rpow_le_rpow_of_exponent_le hm1 (sub_nonpos.mpr (_hSh z hz).2)
        exact (mul_le_mul hr (detectorWeight_le_one hY0 _) (detectorWeight_nonneg _ _) zero_le_one).trans_eq (by ring)
      have hsample := sample_weighted_dyadicPolynomial S (fun z : ℂ => -z.im) (show 0 ≤ 2 * H by positivity)
        hu hsep' a w hM (show M + 2 ^ j ≤ N + 1 by dsimp [M, N]; omega) hw (fun z _ => hw0 z) hw1
      let K := ((2 * (2 * H) + 1) + 4 * (N : ℝ) * harmonicWeight N) * (2 + (Real.log (N : ℝ)) ^ (2 : ℕ))
      have hK : K ≤ 5000 * (N : ℝ) * V ^ (3 : ℕ) := by
        have hA : 2 * (2 * H) + 1 + 4 * (N : ℝ) * harmonicWeight N ≤ 49 * (N : ℝ) * V := by
          have h₁ := mul_le_mul_of_nonneg_left hHarm (show 0 ≤ 4 * (N : ℝ) by positivity)
          have h₂ := le_mul_of_one_le_right hN0.le hV
          nlinarith only [h₁, h₂, hHt, hN1]
        have hB : 2 + (Real.log (N : ℝ)) ^ (2 : ℕ) ≤ 102 * V ^ (2 : ℕ) := by
          have h₁ := pow_le_pow_left₀ hlogN0 hlogN 2
          have h₂ := pow_le_pow_left₀ zero_le_one hV 2
          nlinarith only [h₁, h₂]
        calc
          K ≤ (49 * (N : ℝ) * V) * (102 * V ^ (2 : ℕ)) := mul_le_mul hA hB (by positivity) (by positivity)
          _ ≤ _ := by nlinarith only [show 0 ≤ (N : ℝ) * V ^ (3 : ℕ) by positivity]
      have hcoef : ∑ n ∈ range M, ‖a (M + n)‖ ^ (2 : ℕ) ≤
          ((M : ℝ) ^ (-(2 * σ)) * (N : ℝ)) * (11 * V) ^ (3 : ℕ) := by
        apply (sum_tailCoefficient_sq_le X hM (by linarith only [hσ.1])).trans
        have hHn : 0 ≤ harmonicWeight N := Finset.sum_nonneg fun n _ => by positivity
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHn hHarm _) (by positivity)
      have hjJ : ((j : ℝ) + 1) ^ (2 : ℕ) ≤ (J : ℝ) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)) 2
      have hMpower : (M : ℝ) ^ (2 - 2 * σ) ≤ 4 * P := by
        have hE : 0 ≤ 2 - 2 * σ := by linarith only [hσ.2]
        calc
          _ ≤ (4 * H ^ (4 / 3 : ℝ)) ^ (2 - 2 * σ) := rpow_le_rpow hMp.le hMbound hE
          _ = (4 : ℝ) ^ (2 - 2 * σ) * P := by
            rw [Real.mul_rpow (by norm_num) (rpow_nonneg hH0.le _), ← Real.rpow_mul hH0.le]
            dsimp [P]
            congr 2
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            ((rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) (by linarith only [hσ.1])).trans_eq
              (rpow_one 4)) (by positivity)
      have hEq : (N : ℝ) ^ (2 : ℕ) * (M : ℝ) ^ (-(2 * σ)) = 4 * (M : ℝ) ^ (2 - 2 * σ) := by
        dsimp [N]
        push_cast
        rw [mul_pow, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, mul_assoc, ← Real.rpow_ofNat (M : ℝ) 2,
          ← Real.rpow_add hMp, show (2 : ℝ) + -(2 * σ) = 2 - 2 * σ by ring]
      apply hsample.trans
      change (((j : ℝ) + 1) ^ (2 : ℕ) * K) * ∑ n ∈ range M, ‖a (M + n)‖ ^ (2 : ℕ) ≤ _
      calc
        _ ≤ ((J : ℝ) ^ (2 : ℕ) * (5000 * (N : ℝ) * V ^ (3 : ℕ))) *
            (((M : ℝ) ^ (-(2 * σ)) * (N : ℝ)) * (11 * V) ^ (3 : ℕ)) := by
          apply mul_le_mul _ hcoef (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
          exact mul_le_mul hjJ hK (by dsimp [K, harmonicWeight]; positivity) (by positivity)
        _ = (6655000 * (J : ℝ) ^ (2 : ℕ) * V ^ (6 : ℕ)) *
            ((N : ℝ) ^ (2 : ℕ) * (M : ℝ) ^ (-(2 * σ))) := by ring
        _ ≤ _ := by
          rw [hEq]
          have h1 := mul_le_mul_of_nonneg_left hMpower
            (show 0 ≤ (26620000 : ℝ) * (J : ℝ) ^ (2 : ℕ) * V ^ (6 : ℕ) by positivity)
          have h2 : 0 ≤ (J : ℝ) ^ (2 : ℕ) * (V ^ (6 : ℕ) * P) := by positivity
          nlinarith only [h1, h2]
    · have hZero (z : ℂ) : b j z = 0 := by
        unfold b smoothedTailBlock
        apply Finset.sum_eq_zero
        intro n hn
        have hnM : n < M := Finset.mem_range.mp hn
        have hX : M + n ≤ X := by
          have hn := le_of_not_gt hActive
          dsimp [N] at hn
          omega
        change (tailWeight Y σ z (M + n) : ℂ) * tailCoefficient X σ (M + n) *
          imaginaryPhase (Real.log ((M + n : ℕ) : ℝ)) (-z.im) = 0
        rw [tailCoefficient, if_neg (not_lt.mpr hX), mul_zero, zero_mul]
      simp only [hZero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
      positivity
  change (∑ z ∈ S, ‖smoothedMollifiedTail X Y z‖ ^ (2 : ℕ)) ≤ _
  simp_rw [smoothedMollifiedTail_eq_blocks (σ := σ) hY0 _ hcut]
  change (∑ z ∈ S, ‖∑ j ∈ range J, b j z‖ ^ (2 : ℕ)) ≤ _
  have hsum : (∑ z ∈ S, ‖∑ j ∈ range J, b j z‖ ^ (2 : ℕ)) ≤
      120000000 * (J : ℝ) ^ (4 : ℕ) * (V ^ (6 : ℕ) * P) := by
    calc
      _ ≤ ∑ z ∈ S, (J : ℝ) * ∑ j ∈ range J, ‖b j z‖ ^ (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro z _
        simpa only [Finset.card_range] using norm_sum_sq_le_card_mul_sum_norm_sq (range J) (fun j => b j z)
      _ = (J : ℝ) * ∑ j ∈ range J, ∑ z ∈ S, ‖b j z‖ ^ (2 : ℕ) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (J : ℝ) * ∑ j ∈ range J, (120000000 * (J : ℝ) ^ (2 : ℕ) * (V ^ (6 : ℕ) * P)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hblock) (Nat.cast_nonneg _)
      _ = _ := by simp [nsmul_eq_mul]; ring
  apply hsum.trans
  change _ ≤ (120000000 * C ^ (4 : ℕ)) * V ^ (10 : ℕ) * P
  calc
    _ ≤ 120000000 * (C * V) ^ (4 : ℕ) * (V ^ (6 : ℕ) * P) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg J) hJ 4) (by norm_num)) (by positivity)
    _ = _ := by ring

private def WeylZetaEstimate : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, ∀ t : ℝ,
    ‖riemannZeta (zpoint (1 / 2) t)‖ ≤ A * (|t| + 3) ^ (1 / 6 : ℝ) * Real.log (|t| + 3) ^ B

private lemma one_add_log_pow_le_rpow (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ≥ 1, (1 + Real.log x) ^ B ≤ C * x ^ (1 / 3 : ℝ) := by
  let r := (3 * ((B : ℝ) + 1))⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨(1 + r⁻¹) ^ B, by positivity, fun x hx => ?_⟩
  have hx0 := zero_lt_one.trans_le hx
  have hp := one_le_rpow hx hr.le
  have hlog := Real.log_le_sub_one_of_pos (rpow_pos_of_pos hx0 r)
  rw [Real.log_rpow hx0] at hlog
  have h : Real.log x ≤ (x ^ r - 1) / r := (le_div_iff₀ hr).mpr (by linarith only [hlog])
  have he : 1 + Real.log x ≤ (1 + r⁻¹) * x ^ r := by
    have ht := mul_nonneg (inv_nonneg.mpr hr.le) (show 0 ≤ x ^ r by positivity)
    rw [div_eq_mul_inv, sub_mul, one_mul] at h
    nlinarith only [h, hp, inv_nonneg.mpr hr.le]
  have hE : r * (B : ℝ) ≤ 1 / 3 := by
    dsimp [r]
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  calc
    _ ≤ ((1 + r⁻¹) * x ^ r) ^ B := pow_le_pow_left₀ (by have := Real.log_nonneg hx; linarith) he _
    _ = (1 + r⁻¹) ^ B * x ^ (r * (B : ℝ)) := by rw [mul_pow, Real.rpow_mul_natCast hx0.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hx hE) (by positivity)

private lemma norm_zeta_weyl_shifted (h : WeylZetaEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, ∀ H ≥ Real.exp 1, ∀ γ : ℝ, |γ| ≤ 2 * H → ∀ t : ℝ,
      ‖riemannZeta (zpoint (1 / 2) (γ + t))‖ ≤
        C * H ^ (1 / 6 : ℝ) * Real.log H ^ B * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨A, hA, B, hζ⟩ := h
  obtain ⟨D, hD, hlog⟩ := one_add_log_pow_le_rpow B
  refine ⟨5 * A * 5 ^ B * D, by positivity, B, fun H hH γ hγ t => ?_⟩
  let x := 1 + |t|
  let V := Real.log H
  have hx : 1 ≤ x := le_add_of_nonneg_right (abs_nonneg t)
  have hx0 := zero_lt_one.trans_le hx
  have hH0 := (Real.exp_pos _).trans_le hH
  have hH1 : 1 ≤ H := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hH
  have hV : 1 ≤ V := by
    have h := Real.log_le_log (Real.exp_pos 1) hH
    rwa [Real.log_exp] at h
  have ht : |γ + t| + 3 ≤ (5 * H) * x := by
    have ht := abs_add_le γ t
    dsimp [x]
    nlinarith only [ht, hγ, hH1, abs_nonneg t, mul_nonneg (sub_nonneg.mpr hH1) (abs_nonneg t)]
  have hp : (|γ + t| + 3) ^ (1 / 6 : ℝ) ≤ 5 * H ^ (1 / 6 : ℝ) * x ^ (1 / 6 : ℝ) := by
    apply (rpow_le_rpow (by positivity) ht (by norm_num)).trans
    rw [Real.mul_rpow (by positivity) hx0.le, Real.mul_rpow (by norm_num) hH0.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) (by norm_num : (1 / 6 : ℝ) ≤ 1)).trans_eq (rpow_one 5)
  have hL : Real.log (|γ + t| + 3) ≤ 5 * V * (1 + Real.log x) := by
    have h := Real.log_le_log (by positivity : 0 < |γ + t| + 3) ht
    rw [Real.log_mul (by positivity) hx0.ne', Real.log_mul (by norm_num) hH0.ne'] at h
    have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    exact h.trans (by
      change _ ≤ 5 * V * (1 + Real.log x)
      nlinarith only [h5, hV, mul_nonneg (sub_nonneg.mpr hV) (Real.log_nonneg hx), Real.log_nonneg hx])
  have hnon : 0 ≤ Real.log (|γ + t| + 3) := Real.log_nonneg (by linarith only [abs_nonneg (γ + t)])
  have hLogB : Real.log (|γ + t| + 3) ^ B ≤ ((5 * V) ^ B * D) * x ^ (1 / 3 : ℝ) := by
    apply (pow_le_pow_left₀ hnon hL _).trans
    rw [mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlog x hx) (by positivity)
  apply (hζ (γ + t)).trans
  calc
    _ ≤ (A * (5 * H ^ (1 / 6 : ℝ) * x ^ (1 / 6 : ℝ))) * (((5 * V) ^ B * D) * x ^ (1 / 3 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hA.le) hLogB (pow_nonneg hnon _) (by positivity)
    _ = (5 * A * 5 ^ B * D) * H ^ (1 / 6 : ℝ) * V ^ B * (x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ)) := by
      rw [mul_pow (5 : ℝ) V]
      ring
    _ = _ := by rw [← Real.rpow_add hx0, show (1 / 6 : ℝ) + 1 / 3 = 1 / 2 by norm_num]

private lemma moebiusPolynomial_as_block (X : ℕ) (t : ℝ) :
    moebiusPolynomial X (zpoint (1 / 2) t) =
      blockPolynomial (fun n => (ArithmeticFunction.moebius n : ℂ) * Complex.ofReal ((n : ℝ) ^ (-(1 / 2) : ℝ))) 1 X (-t) := by
  unfold moebiusPolynomial blockPolynomial
  apply Finset.sum_congr rfl
  intro n _
  have hn : 0 < n + 1 := Nat.succ_pos n
  rw [Nat.add_comm 1 n, cpow_split_re_im _ hn, zpoint_re, zpoint_im, mul_assoc]
  congr 2
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne'), ← Complex.natCast_log, imaginaryPhase]
  congr 1
  push_cast
  ring

private lemma moebiusPolynomial_shifted_sample_bound {H : ℝ} (hH : Real.exp 1 ≤ H) {S : Finset ℂ}
    (hS : ∀ z ∈ S, |z.im| ≤ 2 * H) (hsep : (S : Set ℂ).Pairwise (fun z w => 1 ≤ |z.im - w.im|)) (t : ℝ) :
    ∑ z ∈ S, ‖moebiusPolynomial (detectorX H) (zpoint (1 / 2) (z.im + t))‖ ^ (2 : ℕ) ≤
      600 * H * Real.log H ^ (4 : ℕ) * (1 + |t|) := by
  let N := detectorX H
  let L := Real.log H
  let x := 1 + |t|
  let a (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ) * Complex.ofReal ((n : ℝ) ^ (-(1 / 2) : ℝ))
  let u (z : ℂ) := -(z.im + t)
  let T := 2 * H + |t|
  have hH0 := (Real.exp_pos _).trans_le hH
  have hH1 : 1 ≤ H := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hH
  have hL : 1 ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hH
    rwa [Real.log_exp] at hh
  obtain ⟨⟨hN1,hN2⟩, _, _⟩ := detector_parameter_bounds hH1
  have hN0 : 0 < (N : ℝ) := (by norm_num : (0 : ℝ) < 1).trans_le (by exact_mod_cast hN1)
  have hLogN : Real.log (N : ℝ) ≤ 2 * L := by
    have h := Real.log_le_log hN0 hN2
    rw [Real.log_mul (by norm_num) hH0.ne'] at h
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h, hL, h2]
  have hLogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hHarm : harmonicWeight N ≤ 3 * L := by linarith only [harmonicWeight_le_log N, hLogN, hL]
  have hu (z : ℂ) (hz : z ∈ S) : |u z| ≤ T := by
    dsimp [u, T]
    rw [abs_neg]
    exact (abs_add_le _ _).trans (add_le_add_left (hS z hz) _)
  have hsep' : (S : Set ℂ).Pairwise (fun z w => 1 ≤ |u z - u w|) := by
    intro z hz w hw hzw
    have ht := hsep hz hw hzw
    change 1 ≤ |z.im - w.im| at ht
    change 1 ≤ |u z - u w|
    rw [show u z - u w = -(z.im - w.im) by dsimp [u]; ring, abs_neg]
    exact ht
  have hsample := sample_blockPolynomial S u (show 0 ≤ T by dsimp [T]; positivity) hu hsep' a
    (m := 1) (k := N) (N := N) (by norm_num) (by omega)
  have hcoef : ∑ n ∈ range N, ‖a (1 + n)‖ ^ (2 : ℕ) ≤ harmonicWeight N := by
    apply Finset.sum_le_sum
    intro n _
    have hn : 0 < ((1 + n : ℕ) : ℝ) := by positivity
    dsimp [a]
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((1 + n : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)), mul_pow, ← Real.rpow_mul_natCast hn.le, Nat.cast_ofNat,
      show (-(1 / 2) : ℝ) * 2 = -1 by norm_num, Real.rpow_neg_one, Nat.add_comm 1 n, Nat.cast_add_one]
    have hmu : |(ArithmeticFunction.moebius (n + 1) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
    exact mul_le_of_le_one_left (by positivity) (by simpa using pow_le_pow_left₀ (abs_nonneg _) hmu 2)
  simp_rw [moebiusPolynomial_as_block]
  change (∑ z ∈ S, ‖blockPolynomial a 1 N (u z)‖ ^ (2 : ℕ)) ≤ _
  apply hsample.trans
  have hA : 2 * T + 1 + 4 * (N : ℝ) * harmonicWeight N ≤ 31 * H * L * x := by
    have h₁ := mul_le_mul hN2 hHarm (Finset.sum_nonneg fun _ _ => by positivity : 0 ≤ harmonicWeight N) (by positivity : 0 ≤ 2 * H)
    have h₂ : 2 * T + 1 ≤ 7 * H * x := by
      dsimp [T, x]
      nlinarith only [hH1, abs_nonneg t, mul_nonneg (sub_nonneg.mpr hH1) (abs_nonneg t)]
    have h₃ := mul_le_mul_of_nonneg_right hL (show 0 ≤ H * x by dsimp [x]; positivity)
    have h₄ := mul_le_mul_of_nonneg_left (show 1 ≤ x from le_add_of_nonneg_right (abs_nonneg t)) (show 0 ≤ H * L by positivity)
    nlinarith only [h₁, h₂, h₃, h₄]
  have hB : 2 + Real.log (N : ℝ) ^ (2 : ℕ) ≤ 6 * L ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ hLogN0 hLogN 2
    have h' := pow_le_pow_left₀ zero_le_one hL 2
    nlinarith only [h, h']
  calc
    _ ≤ ((31 * H * L * x) * (6 * L ^ (2 : ℕ))) * (3 * L) := by
      apply mul_le_mul (mul_le_mul hA hB (by positivity) (by dsimp [x]; positivity)) (hcoef.trans hHarm)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by dsimp [x]; positivity)
    _ ≤ _ := by
      change _ ≤ 600 * H * L ^ (4 : ℕ) * x
      have h : 0 ≤ H * L ^ (4 : ℕ) * x := by dsimp [x]; positivity
      nlinarith only [h]

private noncomputable def detectorProfile (t : ℝ) : ℝ := (1 + t ^ (2 : ℕ))⁻¹

open MeasureTheory in
private lemma integral_mul_sq_le_of_nonneg {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf₀ : ∀ t, 0 ≤ f t) (hg₀ : ∀ t, 0 ≤ g t)
    (hf₂ : Integrable (fun t => f t ^ (2 : ℕ))) (hg₂ : Integrable (fun t => g t ^ (2 : ℕ))) :
    (∫ t, f t * g t) ^ (2 : ℕ) ≤ (∫ t, f t ^ (2 : ℕ)) * (∫ t, g t ^ (2 : ℕ)) := by
  have hfL : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hf₂
  have hgL : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hg₂
  have he : ENNReal.ofReal 2 = 2 := by norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (Eventually.of_forall hf₀) (Eventually.of_forall hg₀) (he ▸ hfL) (he ▸ hgL)
  have h' : (∫ t, f t * g t) ≤
      Real.sqrt (∫ t, f t ^ (2 : ℕ)) * Real.sqrt (∫ t, g t ^ (2 : ℕ)) := by
    simpa only [Real.rpow_ofNat, ← Real.sqrt_eq_rpow] using h
  apply (pow_le_pow_left₀ (integral_nonneg (fun t => mul_nonneg (hf₀ t) (hg₀ t))) h' 2).trans_eq
  have hfn : 0 ≤ ∫ t, f t ^ (2 : ℕ) := integral_nonneg (fun _ => sq_nonneg _)
  have hgn : 0 ≤ ∫ t, g t ^ (2 : ℕ) := integral_nonneg (fun _ => sq_nonneg _)
  rw [mul_pow, sq_sqrt hfn, sq_sqrt hgn]

open MeasureTheory in
private lemma detectorProfile_cauchy {f : ℝ → ℝ} (hf : Continuous f) (hf₀ : ∀ t, 0 ≤ f t)
    {B : ℝ} (_hB : 0 ≤ B) (hfb : ∀ t, f t ≤ B) :
    Integrable (fun t => detectorProfile t * f t / Real.sqrt (1 + |t|)) ∧
      Integrable (fun t => detectorProfile t * f t ^ (2 : ℕ) / (1 + |t|)) ∧
      (∫ t, detectorProfile t * f t / Real.sqrt (1 + |t|)) ^ (2 : ℕ) ≤
        Real.pi * ∫ t, detectorProfile t * f t ^ (2 : ℕ) / (1 + |t|) := by
  let G := detectorProfile
  let x (t : ℝ) := 1 + |t|
  let a (t : ℝ) := Real.sqrt (G t)
  let b (t : ℝ) := Real.sqrt (G t) * f t / Real.sqrt (x t)
  have hG : Continuous G := by
    unfold G detectorProfile
    exact (by fun_prop : Continuous (fun t : ℝ => 1 + t ^ (2 : ℕ))).inv₀ (fun t => (by positivity : 0 < 1 + t ^ (2 : ℕ)).ne')
  have hG₀ (t : ℝ) : 0 ≤ G t := by dsimp [G, detectorProfile]; positivity
  have hGi : Integrable G := integrable_inv_one_add_sq
  have hGa : Continuous a := hG.sqrt
  have hx (t : ℝ) : 1 ≤ x t := le_add_of_nonneg_right (abs_nonneg t)
  have hx0 (t : ℝ) : 0 < x t := zero_lt_one.trans_le (hx t)
  have hGb : Continuous b := (hGa.mul hf).div (show Continuous (fun t => Real.sqrt (x t)) by unfold x; fun_prop)
    (fun t => (sqrt_pos.mpr (hx0 t)).ne')
  have ha (t : ℝ) : a t ^ (2 : ℕ) = G t := sq_sqrt (hG₀ t)
  have hb (t : ℝ) : b t ^ (2 : ℕ) = G t * f t ^ (2 : ℕ) / x t := by
    dsimp [b]
    rw [div_pow, mul_pow, sq_sqrt (hG₀ t), sq_sqrt (hx0 t).le]
  have hab (t : ℝ) : a t * b t = G t * f t / Real.sqrt (x t) := by
    dsimp [a,b]
    rw [← mul_div_assoc, ← mul_assoc, ← pow_two, sq_sqrt (hG₀ t)]
  have hi (t : ℝ) : 1 ≤ Real.sqrt (x t) := (by norm_num : (1 : ℝ) ≤ Real.sqrt 1).trans (sqrt_le_sqrt (hx t))
  have h₁ : Integrable (fun t => G t * f t / Real.sqrt (x t)) := by
    refine (hGi.const_mul B).mono' ((hGa.mul hGb).aestronglyMeasurable.congr
      (Eventually.of_forall hab)) (Eventually.of_forall fun t => ?_)
    have hg : 0 ≤ G t * f t := mul_nonneg (hG₀ t) (hf₀ t)
    rw [Real.norm_of_nonneg (div_nonneg hg (sqrt_nonneg _))]
    calc
      _ ≤ G t * f t := div_le_self hg (hi t)
      _ ≤ _ := by rw [mul_comm B]; exact mul_le_mul_of_nonneg_left (hfb t) (hG₀ t)
  have h₂ : Integrable (fun t => G t * f t ^ (2 : ℕ) / x t) := by
    refine (hGi.const_mul (B ^ (2 : ℕ))).mono' ((hGb.pow 2).aestronglyMeasurable.congr
      (Eventually.of_forall hb)) (Eventually.of_forall fun t => ?_)
    have hg : 0 ≤ G t * f t ^ (2 : ℕ) := mul_nonneg (hG₀ t) (sq_nonneg _)
    rw [Real.norm_of_nonneg (div_nonneg hg (hx0 t).le)]
    calc
      _ ≤ G t * f t ^ (2 : ℕ) := div_le_self hg (hx t)
      _ ≤ _ := by
        rw [mul_comm (B ^ (2 : ℕ))]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hf₀ t) (hfb t) _) (hG₀ t)
  refine ⟨h₁, h₂, ?_⟩
  have ha₂ : Integrable (fun t => a t ^ (2 : ℕ)) := by simpa only [ha] using hGi
  have hb₂ : Integrable (fun t => b t ^ (2 : ℕ)) := by simpa only [hb] using h₂
  have h := integral_mul_sq_le_of_nonneg hGa hGb (fun _ => sqrt_nonneg _)
    (fun t => div_nonneg (mul_nonneg (sqrt_nonneg _) (hf₀ t)) (sqrt_nonneg _)) ha₂ hb₂
  simp_rw [hab, ha, hb] at h
  simpa only [G, detectorProfile, integral_univ_inv_one_add_sq, x] using h

open MeasureTheory in
set_option maxHeartbeats 900000 in
private lemma norm_detectorLeft_le_of_weyl {A : ℝ} (hA : 0 ≤ A) (B : ℕ) {H : ℝ} (hH : Real.exp 1 ≤ H)
    {σ : ℝ} (hσ : 7 / 12 ≤ σ) {ρ : ℂ} (hρ : σ ≤ ρ.re) (hρ' : ρ.re < 1)
    (hZ : ∀ t : ℝ, ‖riemannZeta (zpoint (1 / 2) (ρ.im + t))‖ ≤
      A * H ^ (1 / 6 : ℝ) * Real.log H ^ B * (1 + |t|) ^ (1 / 2 : ℝ)) :
    ‖detectorLeftIntegral (detectorX H) (detectorY H) ρ‖ ≤
      ((16 / ((1 / 12 : ℝ) ^ (3 : ℕ)) * A) / (2 * Real.pi) * H ^ (1 / 6 : ℝ) * Real.log H ^ B *
        H ^ ((4 / 3 : ℝ) * (1 / 2 - σ))) *
      ∫ t : ℝ, detectorProfile t * ‖moebiusPolynomial (detectorX H) (zpoint (1 / 2) (ρ.im + t))‖ / Real.sqrt (1 + |t|) := by
  let X := detectorX H
  let Y := detectorY H
  let a := 1 / 2 - ρ.re
  let L := Real.log H
  let F (t : ℝ) := zetaDetectorIntegrand X (Real.log Y) ρ (zpoint a t)
  let U (t : ℝ) := ‖moebiusPolynomial X (zpoint (1 / 2) (ρ.im + t))‖
  let q := H ^ ((4 / 3 : ℝ) * (1 / 2 - σ))
  let D := 16 / ((1 / 12 : ℝ) ^ (3 : ℕ))
  let K := D * A * H ^ (1 / 6 : ℝ) * L ^ B * q
  have hH0 := (Real.exp_pos _).trans_le hH
  have hH1 : 1 ≤ H := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hH
  have hL : 0 ≤ L := Real.log_nonneg hH1
  have hK : 0 ≤ K := by dsimp [K, D]; positivity
  have ha : a ≤ -(1 / 12 : ℝ) := by dsimp [a]; linarith only [hσ, hρ]
  have ha' : -(1 / 2 : ℝ) < a := by dsimp [a]; linarith only [hρ']
  obtain ⟨_, hY, _⟩ := detector_parameter_bounds hH1
  have hY1 : 1 ≤ Y := (one_le_rpow hH1 (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans hY
  have hY0 := zero_lt_one.trans_le hY1
  have hQ : Real.exp (Real.log Y * a) ≤ q := by
    rw [← rpow_def_of_pos hY0]
    calc
      _ ≤ Y ^ (1 / 2 - σ) := rpow_le_rpow_of_exponent_le hY1 (by dsimp [a]; linarith only [hρ])
      _ ≤ (H ^ (4 / 3 : ℝ)) ^ (1 / 2 - σ) := rpow_le_rpow_of_nonpos (by positivity) hY (by linarith only [hσ])
      _ = q := (Real.rpow_mul hH0.le _ _).symm
  have hF : Integrable F := integrable_detector_vertical X _ ρ a
    (by dsimp [a]; linarith) (by dsimp [a]; exact fun h => by linarith only [h])
    (fun h => by linarith only [ha, h]) (fun h => by linarith only [ha', h]) (fun h => by linarith only [ha', h])
  have hU : Continuous U := by
    unfold U
    exact ((continuousOn_univ.mp (analytic_moebiusPolynomial X).continuousOn).comp
      (by unfold zpoint; fun_prop)).norm
  have hUbound (t : ℝ) : U t ≤ X := norm_moebiusPolynomial_le X (by rw [zpoint_re]; norm_num)
  obtain ⟨hIg, _, _⟩ := detectorProfile_cauchy hU (fun _ => norm_nonneg _) (Nat.cast_nonneg _) hUbound
  have hNorm (t : ℝ) : ‖F t‖ ≤ K * (detectorProfile t * U t / Real.sqrt (1 + |t|)) := by
    let x := 1 + |t|
    have hx : 0 < x := by dsimp [x]; positivity
    have hxS : 0 < Real.sqrt x := sqrt_pos.mpr hx
    have hKern := norm_quadraticPerronKernel_vertical (v := Real.log Y) (c := a) (d := 1 / 12)
      (by norm_num) (by norm_num) (by rw [abs_of_nonpos (by linarith only [ha])]; linarith only [ha])
      (by rw [abs_of_pos (by linarith only [ha'])]; linarith only [ha'])
      (by rw [abs_of_pos (by linarith only [ha'])]; linarith only [ha']) t
    have hKern' : ‖quadraticPerronKernel (Real.log Y) (zpoint a t)‖ ≤ (D * q) / x ^ (3 : ℕ) := by
      apply hKern.trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ = D * Real.exp (Real.log Y * a) := by dsimp [D]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hQ (by dsimp [D]; positivity)
    have hEq : ρ + zpoint a t = zpoint (1 / 2) (ρ.im + t) := by
      apply Complex.ext
      · simp [a]
      · simp
    change ‖zetaDetectorIntegrand X (Real.log Y) ρ (zpoint a t)‖ ≤ _
    rw [zetaDetectorIntegrand, hEq, norm_mul, norm_mul]
    have hz := hZ t
    rw [← sqrt_eq_rpow] at hz
    calc
      _ ≤ ((A * H ^ (1 / 6 : ℝ) * L ^ B * Real.sqrt x) * U t) * ((D * q) / x ^ (3 : ℕ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hz (norm_nonneg _)) hKern' (norm_nonneg _) (by positivity)
      _ = K * ( (x ^ (2 : ℕ))⁻¹ * U t / Real.sqrt x) := by
        dsimp [K]
        field_simp
        rw [sq_sqrt hx.le]
        ring
      _ ≤ _ := by
        have hG : (x ^ (2 : ℕ))⁻¹ ≤ detectorProfile t := by
          apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
          dsimp [x]
          nlinarith only [sq_abs t, abs_nonneg t]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hG (norm_nonneg _)) hxS.le) hK
  have hInt : ‖∫ t : ℝ, F t‖ ≤ K * (∫ t : ℝ, detectorProfile t * U t / Real.sqrt (1 + |t|)) := by
    apply (norm_integral_le_integral_norm F).trans
    rw [← integral_const_mul]
    exact integral_mono hF.norm (hIg.const_mul K) hNorm
  rw [detectorLeftIntegral, norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  apply (mul_le_mul_of_nonneg_left hInt (by positivity)).trans_eq
  dsimp [K, D]
  ring

open MeasureTheory in
set_option maxHeartbeats 900000 in
private lemma detector_left_moment_of_weyl (h : WeylZetaEstimate) :
    DetectorMomentEstimate (fun T => detectorLeftIntegral (detectorX T) (detectorY T)) := by
  obtain ⟨A, hA, B, hZeta⟩ := norm_zeta_weyl_shifted h
  let D := (16 / ((1 / 12 : ℝ) ^ (3 : ℕ)) * A) / (2 * Real.pi)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨600 * Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ), by positivity, 2 * B + 4, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with H hH
  intro σ hσ S hS hR hsep
  let X := detectorX H
  let Y := detectorY H
  let L := Real.log H
  let W (t : ℝ) := 1 + |t|
  let U (z : ℂ) (t : ℝ) : ℝ := ‖moebiusPolynomial X (zpoint (1 / 2) (z.im + t))‖
  let G (z : ℂ) (t : ℝ) : ℝ := detectorProfile t * (U z t) ^ (2 : ℕ) / W t
  let K := D * H ^ (1 / 6 : ℝ) * L ^ B * H ^ ((4 / 3 : ℝ) * (1 / 2 - σ))
  have hH0 := (Real.exp_pos _).trans_le hH
  have hH1 : 1 ≤ H := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hH
  have hL : 0 ≤ L := Real.log_nonneg hH1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have habs (z : ℂ) (hz : z ∈ S) : |z.im| ≤ 2 * H := (mem_zerosUpTo.mp (hS hz)).2.2.2
  have hU (z : ℂ) : Continuous (U z) := by
    unfold U
    exact ((continuousOn_univ.mp (analytic_moebiusPolynomial X).continuousOn).comp
      (by unfold zpoint; fun_prop)).norm
  have hUbound (z : ℂ) (t : ℝ) : U z t ≤ (X : ℝ) :=
    norm_moebiusPolynomial_le X (by rw [zpoint_re]; norm_num)
  have hC (z : ℂ) := detectorProfile_cauchy (hU z) (fun _ => norm_nonneg _) (Nat.cast_nonneg X) (hUbound z)
  have hpt (z : ℂ) (hz : z ∈ S) : ‖detectorLeftIntegral X Y z‖ ^ (2 : ℕ) ≤
      (K ^ (2 : ℕ) * Real.pi) * ∫ t, G z t := by
    have h := norm_detectorLeft_le_of_weyl hA.le B hH hσ.1 (hR z hz).2
      (mem_zerosUpTo.mp (hS hz)).2.2.1 (hZeta H hH z.im (habs z hz))
    change ‖detectorLeftIntegral X Y z‖ ≤ K * ∫ t, detectorProfile t * U z t / Real.sqrt (1 + |t|) at h
    apply (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    rw [mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC z).2.2 (sq_nonneg _)
  have hsum : ∑ z ∈ S, (∫ t, G z t) ≤ (600 * H * L ^ (4 : ℕ)) * Real.pi := by
    have hGi (z : ℂ) (_ : z ∈ S) : Integrable (G z) := (hC z).2.1
    rw [← integral_finsetSum S hGi, ← integral_univ_inv_one_add_sq, ← integral_const_mul]
    have hI : Integrable (fun t : ℝ => (600 * H * L ^ (4 : ℕ)) * (1 + t ^ (2 : ℕ))⁻¹) :=
      integrable_inv_one_add_sq.const_mul _
    apply integral_mono (integrable_finsetSum S hGi) hI
    intro t
    change (∑ z ∈ S, detectorProfile t * U z t ^ (2 : ℕ) / W t) ≤
      (600 * H * L ^ (4 : ℕ)) * detectorProfile t
    have h := moebiusPolynomial_shifted_sample_bound hH habs hsep t
    change (∑ z ∈ S, U z t ^ (2 : ℕ)) ≤ 600 * H * L ^ (4 : ℕ) * W t at h
    have hP : 0 ≤ detectorProfile t := by unfold detectorProfile; positivity
    have hW : 0 < W t := by unfold W; positivity
    have heq : (∑ z ∈ S, detectorProfile t * U z t ^ (2 : ℕ) / W t) =
        detectorProfile t * ((∑ z ∈ S, U z t ^ (2 : ℕ)) / W t) := by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    rw [heq, mul_comm (600 * H * L ^ (4 : ℕ))]
    apply mul_le_mul_of_nonneg_left _ hP
    exact (div_le_iff₀ hW).mpr h
  have hE : (H ^ (1 / 6 : ℝ)) ^ (2 : ℕ) * (H ^ ((4 / 3 : ℝ) * (1 / 2 - σ))) ^ (2 : ℕ) * H =
      H ^ ((8 / 3 : ℝ) * (1 - σ)) := by
    rw [← Real.rpow_mul_natCast hH0.le, ← Real.rpow_mul_natCast hH0.le, ← Real.rpow_add hH0]
    let e := (1 / 6 : ℝ) * ((2 : ℕ) : ℝ) + (4 / 3 * (1 / 2 - σ)) * ((2 : ℕ) : ℝ)
    change H ^ e * H = _
    calc
      _ = H ^ e * H ^ (1 : ℝ) := by rw [rpow_one]
      _ = _ := by rw [← Real.rpow_add hH0]; congr 1; dsimp [e]; ring
  have hLp : (L ^ B) ^ (2 : ℕ) * L ^ (4 : ℕ) = L ^ (2 * B + 4) := by
    rw [← pow_mul, ← pow_add, Nat.mul_comm B 2]
  change (∑ z ∈ S, ‖detectorLeftIntegral X Y z‖ ^ (2 : ℕ)) ≤ _
  calc
    _ ≤ ∑ z ∈ S, (K ^ (2 : ℕ) * Real.pi) * ∫ t, G z t := Finset.sum_le_sum hpt
    _ ≤ (K ^ (2 : ℕ) * Real.pi) * ((600 * H * L ^ (4 : ℕ)) * Real.pi) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      dsimp [K]
      have hFactor :
          (D * H ^ (1 / 6 : ℝ) * L ^ B * H ^ ((4 / 3 : ℝ) * (1 / 2 - σ))) ^ (2 : ℕ) * Real.pi *
              (600 * H * L ^ (4 : ℕ) * Real.pi) =
            (600 * Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ)) * ((L ^ B) ^ (2 : ℕ) * L ^ (4 : ℕ)) *
              ((H ^ (1 / 6 : ℝ)) ^ (2 : ℕ) * (H ^ ((4 / 3 : ℝ) * (1 / 2 - σ))) ^ (2 : ℕ) * H) := by ring
      rw [hFactor, hLp, hE]

private lemma sum_inv_distance_halfInteger (m : ℕ) :
    ∑ n ∈ Finset.range (2 * m + 2), |(m : ℝ) + 1 / 2 - (n : ℝ)|⁻¹ ≤ 4 * (harmonic (m + 1) : ℝ) := by
  let f (n : ℕ) := |(m : ℝ) + 1 / 2 - (n : ℝ)|⁻¹
  let g (n : ℕ) := ((n : ℝ) + 1 / 2)⁻¹
  have hsmall (n : ℕ) (hn : n ∈ range (m + 1)) : f (m - n) = g n := by
    have hnm : n ≤ m := Nat.le_of_lt_succ (mem_range.mp hn)
    unfold f g
    rw [Nat.cast_sub hnm]
    rw [show (m : ℝ) + 1 / 2 - ((m : ℝ) - n) = (n : ℝ) + 1 / 2 by ring,
      abs_of_pos (by positivity)]
  have hbig (n : ℕ) : f (n + (m + 1)) = g n := by
    unfold f g
    push_cast
    rw [show (m : ℝ) + 1 / 2 - ((n : ℝ) + ((m : ℝ) + 1)) =
      -((n : ℝ) + 1 / 2) by ring, abs_neg, abs_of_pos (by positivity)]
  have hg : (∑ n ∈ range (m + 1), g n) ≤ 2 * (harmonic (m + 1) : ℝ) := by
    unfold harmonic
    push_cast
    rw [mul_sum]
    refine sum_le_sum fun n _ => ?_
    unfold g
    have hcomp := one_div_le_one_div_of_le (show 0 < ((n : ℝ) + 1) / 2 by positivity)
      (show ((n : ℝ) + 1) / 2 ≤ (n : ℝ) + 1 / 2 by linarith only [Nat.cast_nonneg (α := ℝ) n])
    have heq : (((n : ℝ) + 1) / 2)⁻¹ = 2 * ((n : ℝ) + 1)⁻¹ := by field_simp
    simpa only [one_div, heq] using hcomp
  change ∑ n ∈ range (2 * m + 2), f n ≤ _
  rw [show 2 * m + 2 = (m + 1) + (m + 1) by omega, sum_range_add]
  have hsum1 : (∑ n ∈ range (m + 1), f n) = ∑ n ∈ range (m + 1), g n := by
    rw [← sum_range_reflect f]
    simpa only [Nat.add_sub_cancel] using sum_congr rfl hsmall
  have hsum2 : (∑ n ∈ range (m + 1), f (m + 1 + n)) = ∑ n ∈ range (m + 1), g n := by
    exact sum_congr rfl (fun n _ => by rw [Nat.add_comm]; exact hbig n)
  rw [hsum1, hsum2]
  linarith only [hg]

private lemma abs_log_ratio_lower {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hrq : r ≤ 2 * q) :
    |q - r| / (2 * q) ≤ |Real.log (q / r)| := by
  have hlog := Real.log_div hq.ne' hr.ne'
  rw [hlog]
  rcases le_total r q with h | h
  · have he := Real.log_le_sub_one_of_pos (div_pos hr hq)
    rw [Real.log_div hr.ne' hq.ne'] at he
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hle : (q - r) / (2 * q) ≤ (q - r) / q :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr h) hq (by linarith only [hq])
    have heq : (q - r) / q = 1 - r / q := by rw [sub_div, div_self hq.ne']
    rw [heq] at hle
    exact hle.trans ((by linarith only [he] : 1 - r / q ≤ Real.log q - Real.log r).trans (le_abs_self _))
  · have he := Real.log_le_sub_one_of_pos (div_pos hq hr)
    rw [Real.log_div hq.ne' hr.ne'] at he
    rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    have hle : (r - q) / (2 * q) ≤ (r - q) / r :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr h) hr hrq
    have heq : (r - q) / r = 1 - q / r := by rw [sub_div, div_self hr.ne']
    rw [heq] at hle
    exact hle.trans ((by linarith only [he] : 1 - q / r ≤ -(Real.log q - Real.log r)).trans (neg_le_abs _))

private lemma abs_log_ratio_far {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hfar : r ≤ q / 2 ∨ 2 * q ≤ r) : Real.log 2 ≤ |Real.log (q / r)| := by
  rcases hfar with h | h
  · calc
      _ ≤ Real.log (q / r) := Real.log_le_log (by norm_num) ((le_div_iff₀ hr).mpr (by linarith only [h]))
      _ ≤ _ := le_abs_self _
  · have he : Real.log (r / q) = -Real.log (q / r) := by
      rw [Real.log_div hq.ne' hr.ne', Real.log_div hr.ne' hq.ne']; ring
    calc
      _ ≤ Real.log (r / q) := Real.log_le_log (by norm_num) ((le_div_iff₀ hq).mpr (by linarith only [h]))
      _ ≤ _ := by rw [he]; exact neg_le_abs _

private lemma mangoldtWeight_nonneg (q c : ℝ) (n : ℕ) : 0 ≤ mangoldtWeight q c n := by
  unfold mangoldtWeight
  split_ifs
  · positivity
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_nonneg _)

private noncomputable def perronLine (q : ℝ) := 1 + (Real.log q)⁻¹

private lemma mangoldtWeight_tsum {q c : ℝ} (hq : 0 < q) (hc : 1 < c) :
    ∑' n, mangoldtWeight q c n = q ^ c * negZetaLogDeriv c 0 := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : ℂ)) (by simpa using hc)
  simp_rw [mangoldtWeight_eq_reTerm hq]
  rw [tsum_mul_left, ← Complex.re_tsum h]
  have he : ∑' n, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n =
      -deriv riemannZeta (c : ℂ) / riemannZeta (c : ℂ) :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hc)
  rw [he]
  rfl

private lemma kernelErrorWeight_halfInteger :
    ∃ K Q : ℝ, 0 < K ∧ ∀ m : ℕ, Q ≤ (m : ℝ) + 1 / 2 →
      let q := (m : ℝ) + 1 / 2
      Summable (kernelErrorWeight q (perronLine q)) ∧
        ∑' n, kernelErrorWeight q (perronLine q) n ≤ K * q * Real.log q ^ (2 : ℕ) := by
  classical
  obtain ⟨C, d, hC, hd, hpole⟩ := negZetaLogDeriv_near_pole
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp
    (tendsto_log_atTop.eventually_ge_atTop (1 / d + 1))
  let K := Real.exp 1 * (1 + C) / Real.log 2 + 192
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K, max 2 Q, by dsimp [K]; positivity, fun m hq => ?_⟩
  dsimp only
  let q := (m : ℝ) + 1 / 2
  let c := perronLine q
  have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
  have hq0 : 0 < q := by linarith only [hq2]
  have hLg : 1 / d + 1 ≤ Real.log q := hQ q ((le_max_right _ _).trans hq)
  have hL : 1 ≤ Real.log q := by have h := div_pos (show (0 : ℝ) < 1 by norm_num) hd; linarith only [hLg, h]
  have hL0 : 0 < Real.log q := zero_lt_one.trans_le hL
  have hc1 : 1 < c := by unfold c perronLine; linarith only [inv_pos.mpr hL0]
  have hc2 : c ≤ 2 := by
    have hh : (Real.log q)⁻¹ ≤ 1 := by rw [← one_div]; exact (div_le_iff₀ hL0).mpr (by simpa using hL)
    dsimp [c, perronLine]
    linarith only [hh]
  have hld : (Real.log q)⁻¹ < d := by
    rw [← one_div]
    apply (div_lt_iff₀ hL0).mpr
    have hh := (div_lt_iff₀ hd).mp (show 1 / d < Real.log q by linarith only [hLg])
    simpa only [mul_comm] using hh
  have hnear : c ∈ Set.Ioo 1 (1 + d) := ⟨hc1, by dsimp [c, perronLine]; linarith only [hld]⟩
  have hmass : ∑' n, mangoldtWeight q c n ≤ (Real.exp 1 * (1 + C)) * q * Real.log q ^ (2 : ℕ) := by
    rw [mangoldtWeight_tsum hq0 hc1]
    have h := hpole c hnear
    have hcinv : (c - 1)⁻¹ = Real.log q := by
      dsimp [c, perronLine]
      rw [add_sub_cancel_left, inv_inv]
    rw [hcinv] at h
    have hqc : q ^ c = Real.exp 1 * q := by
      dsimp [c, perronLine]
      rw [rpow_add hq0, rpow_one, rpow_def_of_pos hq0, mul_inv_cancel₀ hL0.ne', mul_comm]
    have hlog : Real.log q + C ≤ (1 + C) * Real.log q ^ (2 : ℕ) := by
      have hL2 : Real.log q ≤ Real.log q ^ (2 : ℕ) := by
        nlinarith only [mul_nonneg hL0.le (show 0 ≤ Real.log q - 1 by linarith only [hL])]
      have hCC := mul_le_mul_of_nonneg_left (le_trans hL hL2) hC
      nlinarith only [hL2, hCC]
    rw [hqc]
    calc
      _ ≤ Real.exp 1 * q * ((1 + C) * Real.log q ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (h.trans hlog) (by positivity)
      _ = _ := by ring
  let S := range (2 * m + 2)
  let f (n : ℕ) := if n ∈ S then |q - (n : ℝ)|⁻¹ else 0
  have hf : Summable f :=
    summable_of_ne_finset_zero (s := S) (fun n hn => if_neg hn)
  have hsum_f : ∑' n, f n ≤ 12 * Real.log q := by
    have hF : HasSum f (∑ n ∈ S, f n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => if_neg hn)
    rw [hF.tsum_eq, sum_congr rfl (fun n hn => show f n = |q - (n : ℝ)|⁻¹ from if_pos hn)]
    have hsum := sum_inv_distance_halfInteger m
    have hharm := harmonic_le_one_add_log (m + 1)
    have hlm : Real.log ((m + 1 : ℕ) : ℝ) ≤ 2 * Real.log q := by
      have hc : ((m + 1 : ℕ) : ℝ) ≤ 2 * q := by
        push_cast
        dsimp [q]
        linarith only [Nat.cast_nonneg (α := ℝ) m]
      have hln := Real.log_le_log (by positivity : 0 < ((m + 1 : ℕ) : ℝ)) hc
      rw [Real.log_mul (by norm_num) hq0.ne'] at hln
      have hh := Real.log_le_log (by norm_num) hq2
      linarith only [hln, hh]
    change (∑ n ∈ range (2 * m + 2), |(m : ℝ) + 1 / 2 - (n : ℝ)|⁻¹) ≤ _
    linarith only [hsum, hharm, hlm, hL]
  have hbound (n : ℕ) : kernelErrorWeight q c n ≤
      mangoldtWeight q c n / Real.log 2 + (16 * q * Real.log q) * f n := by
    have hf0 : 0 ≤ f n := by by_cases hn : n ∈ S <;> simp [f, hn, inv_nonneg]
    have hfarTerm : 0 ≤ mangoldtWeight q c n / Real.log 2 := div_nonneg (mangoldtWeight_nonneg q c n) hlog₂.le
    have hnearTerm : 0 ≤ (16 * q * Real.log q) * f n := by positivity
    rcases eq_or_ne n 0 with rfl | hn
    · exact (by simp [kernelErrorWeight, mangoldtWeight] :
        kernelErrorWeight q c 0 = 0).trans_le (add_nonneg hfarTerm hnearTerm)
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    by_cases hfar : (n : ℝ) ≤ q / 2 ∨ 2 * q ≤ (n : ℝ)
    · exact (div_le_div_of_nonneg_left (mangoldtWeight_nonneg _ _ _) hlog₂
        (abs_log_ratio_far hq0 hn0 hfar)).trans (le_add_of_nonneg_right hnearTerm)
    · have hnlow : q / 2 < (n : ℝ) := lt_of_not_ge (fun h => hfar (Or.inl h))
      have hnhi : (n : ℝ) < 2 * q := lt_of_not_ge (fun h => hfar (Or.inr h))
      have hnS : n ∈ S := by
        apply mem_range.mpr
        have hh : (n : ℝ) < ((2 * m + 2 : ℕ) : ℝ) := by
          push_cast
          dsimp [q] at hnhi
          linarith only [hnhi]
        exact_mod_cast hh
      have hδ : 0 < |q - (n : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (halfInteger_ne_nat m n).symm)
      have hlogLower := abs_log_ratio_lower hq0 hn0 hnhi.le
      have hweight : mangoldtWeight q c n ≤ 8 * Real.log q := by
        have hLn : Real.log (n : ℝ) ≤ 2 * Real.log q := by
          have hh := Real.log_le_log hn0 hnhi.le
          rw [Real.log_mul (by norm_num) hq0.ne'] at hh
          linarith only [hh, Real.log_le_log (by norm_num : 0 < (2 : ℝ)) hq2]
        have hExp : Real.exp (c * Real.log (q / n)) ≤ 4 := by
          have hlo : Real.log (q / n) ≤ Real.log 2 :=
            Real.log_le_log (div_pos hq0 hn0) ((div_le_iff₀ hn0).2 (by linarith only [hnlow]))
          have hp := mul_le_mul_of_nonneg_left hlo (zero_lt_one.trans hc1).le
          have hh := mul_le_mul_of_nonneg_right hc2 hlog₂.le
          have hu := Real.exp_le_exp.mpr (hp.trans hh)
          have heq : Real.exp (2 * Real.log 2) = 4 := by
            rw [two_mul, Real.exp_add, Real.exp_log (by norm_num)]
            norm_num
          exact hu.trans_eq heq
        rw [mangoldtWeight, if_neg hn]
        calc
          _ ≤ (2 * Real.log q) * 4 :=
            mul_le_mul (ArithmeticFunction.vonMangoldt_le_log.trans hLn) hExp (Real.exp_nonneg _) (by positivity)
          _ = _ := by ring
      have herr : kernelErrorWeight q c n ≤ (16 * q * Real.log q) * f n := by
        calc
          _ ≤ mangoldtWeight q c n / (|q - (n : ℝ)| / (2 * q)) :=
            div_le_div_of_nonneg_left (mangoldtWeight_nonneg _ _ _) (by positivity) hlogLower
          _ ≤ (8 * Real.log q) / (|q - (n : ℝ)| / (2 * q)) :=
            div_le_div_of_nonneg_right hweight (by positivity)
          _ = _ := by rw [show f n = _ from if_pos hnS]; field_simp; ring
      exact herr.trans (le_add_of_nonneg_left hfarTerm)
  have hdom : Summable (fun n => mangoldtWeight q c n / Real.log 2 + (16 * q * Real.log q) * f n) :=
    ((summable_mangoldtWeight hq0 hc1).div_const _).add (hf.mul_left _)
  have herr : Summable (kernelErrorWeight q c) :=
    hdom.of_nonneg_of_le (fun n => div_nonneg (mangoldtWeight_nonneg _ _ _) (abs_nonneg _)) hbound
  refine ⟨herr, ?_⟩
  calc
    _ ≤ ∑' n, (mangoldtWeight q c n / Real.log 2 + (16 * q * Real.log q) * f n) :=
      herr.tsum_le_tsum hbound hdom
    _ = (∑' n, mangoldtWeight q c n) / Real.log 2 + (16 * q * Real.log q) * (∑' n, f n) := by
      rw [((summable_mangoldtWeight hq0 hc1).div_const _).tsum_add (hf.mul_left _),
        tsum_div_const, tsum_mul_left]
    _ ≤ (Real.exp 1 * (1 + C) * q * Real.log q ^ (2 : ℕ)) / Real.log 2 +
        (16 * q * Real.log q) * (12 * Real.log q) :=
      add_le_add (div_le_div_of_nonneg_right hmass hlog₂.le)
        (mul_le_mul_of_nonneg_left hsum_f (by positivity))
    _ = _ := by dsimp [K]; ring

private lemma separated_height_abs {c T H : ℝ} (hc : 0 < c) (hT : 3 ≤ T)
    (hs : HeightSeparated c T H) {z : ℂ} (hz : z ∈ zerosUpTo H) :
    |z.im| < H := by
  obtain ⟨hzero, hre, hre', hbound⟩ := mem_zerosUpTo.mp hz
  have hp : 0 < c / Real.log (T + 3) := div_pos hc (Real.log_pos (by linarith only [hT]))
  refine lt_of_le_of_ne hbound fun heq => ?_
  rcases le_total 0 z.im with hpos | hneg
  · rw [abs_of_nonneg hpos] at heq
    have h := hs z hzero hre hre'
    rw [heq, sub_self, abs_zero] at h
    exact hp.not_ge h
  · have h := hs (1 - z) (mem_zerosUpTo.mp (one_sub_mem_zerosUpTo hz)).1
      (mem_zerosUpTo.mp (one_sub_mem_zerosUpTo hz)).2.1
      (mem_zerosUpTo.mp (one_sub_mem_zerosUpTo hz)).2.2.1
    have him : (1 - z).im = H := by
      simpa only [Complex.sub_im, Complex.one_im, zero_sub] using (abs_of_nonpos hneg).symm.trans heq
    rw [him, sub_self, abs_zero] at h
    exact hp.not_ge h

open MeasureTheory in
private lemma exists_separated_abscissa :
    ∃ C : ℝ, 0 < C ∧ ∀ H ≥ 3, ∃ a ∈ Set.Icc (1 / 8 : ℝ) (1 / 4),
      ∀ z ∈ zerosUpTo H, (C * H * Real.log H)⁻¹ ≤ |a - z.re| := by
  classical
  obtain ⟨B, hB, hb⟩ := total_zero_count
  let C := 32 * B
  refine ⟨C, by dsimp [C]; positivity, fun H hH => ?_⟩
  let S := zerosUpTo H
  let δ := (C * H * Real.log H)⁻¹
  have hHpos : 0 < H := by linarith only [hH]
  have hlog : 0 < Real.log H := Real.log_pos (by linarith only [hH])
  have hδ : 0 < δ := by dsimp [δ, C]; positivity
  have hcard : (S.card : ℝ) ≤ B * H * Real.log H := by
    calc
      _ = ∑ _z ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ z ∈ S, (multiplicity z : ℝ) := by
        apply sum_le_sum
        intro z hz
        exact_mod_cast multiplicity_pos_of_mem_zerosUpTo hz
      _ ≤ _ := hb H (by linarith only [hH])
  let J (z : ℂ) : Set ℝ := Set.Ioo (z.re - δ) (z.re + δ)
  have hJ (z : ℂ) : volume (J z) = ENNReal.ofReal (2 * δ) := by
    dsimp [J]
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hm : volume (⋃ z ∈ S, J z) < ENNReal.ofReal (1 / 8 : ℝ) := by
    apply (measure_biUnion_finset_le (μ := volume) S J).trans_lt
    simp only [hJ, sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast S.card,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) S.card)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 8)).mpr
    calc
      _ ≤ B * H * Real.log H * (2 * δ) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 1 / 16 := by dsimp [δ, C]; field_simp; ring
      _ < _ := by norm_num
  have hout : ∃ a ∈ Set.Icc (1 / 8 : ℝ) (1 / 4), a ∉ ⋃ z ∈ S, J z := by
    by_contra! h
    have hle := measure_mono (μ := volume) (show Set.Icc (1 / 8 : ℝ) (1 / 4) ⊆ ⋃ z ∈ S, J z from h)
    rw [Real.volume_Icc, show (1 / 4 : ℝ) - 1 / 8 = 1 / 8 by norm_num] at hle
    exact hm.not_ge hle
  obtain ⟨a, ha, havoids⟩ := hout
  refine ⟨a, ha, fun z hz => le_of_not_gt fun h => havoids ?_⟩
  apply Set.mem_iUnion₂.mpr
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  exact ⟨z, hz, ⟨by linarith only [hlo], by linarith only [hhi]⟩⟩

private lemma zeros_norm_uniform_lower :
    ∃ b : ℝ, 0 < b ∧ ∀ T z, z ∈ zerosUpTo T → b ≤ ‖z‖ := by
  obtain ⟨a, ha, hlow⟩ := finite_pos_lower (zerosUpTo 1) (fun z => ‖z‖) (fun z hz =>
    norm_pos_iff.mpr (fun e => (mem_zerosUpTo.mp hz).2.1.ne' (by simp [e])))
  refine ⟨min 1 a, lt_min zero_lt_one ha, fun T z hz => ?_⟩
  by_cases hi : |z.im| ≤ 1
  · obtain ⟨hzero, hpos, hre, _⟩ := mem_zerosUpTo.mp hz
    exact (min_le_right _ _).trans (hlow z (mem_zerosUpTo.mpr ⟨hzero, hpos, hre, hi⟩))
  · exact (min_le_left _ _).trans ((le_of_not_ge hi).trans (Complex.abs_im_le_norm _))

open scoped Classical in
private lemma zeroSum_sub_filtered_le :
    ∃ B : ℝ, 0 < B ∧ ∀ {H q a : ℝ}, 2 ≤ H → 1 ≤ q → a ≤ 1 / 4 →
      ‖zeroSum H q - ∑ z ∈ (zerosUpTo H).filter (fun z => a < z.re),
        (multiplicity z : ℂ) * ((q : ℂ) ^ z / z)‖ ≤ B * q ^ (1 / 4 : ℝ) * H * Real.log H := by
  classical
  obtain ⟨b, hb, hnorm⟩ := zeros_norm_uniform_lower
  obtain ⟨C, hC, hcount⟩ := total_zero_count
  refine ⟨C / b, div_pos hC hb, fun {H q a} hH hq ha => ?_⟩
  let S := zerosUpTo H
  let f (z : ℂ) := (multiplicity z : ℂ) * ((q : ℂ) ^ z / z)
  let U := S.filter (fun z => a < z.re)
  let V := S.filter (fun z => ¬ a < z.re)
  have hpart : (∑ z ∈ U, f z) + ∑ z ∈ V, f z = zeroSum H q :=
    Finset.sum_filter_add_sum_filter_not S (fun z : ℂ => a < z.re) f
  change ‖zeroSum H q - ∑ z ∈ U, f z‖ ≤ _
  rw [← hpart, add_sub_cancel_left]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  calc
    _ ≤ ∑ z ∈ V, ‖f z‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ V, (multiplicity z : ℝ) * (q ^ (1 / 4 : ℝ) / b) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hzS, hzβ⟩ := Finset.mem_filter.mp hz
      dsimp [f]
      rw [norm_mul, Complex.norm_natCast, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact div_le_div₀ (rpow_nonneg hq0.le _) (rpow_le_rpow_of_exponent_le hq ((le_of_not_gt hzβ).trans ha))
        hb (hnorm H z hzS)
    _ = (∑ z ∈ V, (multiplicity z : ℝ)) * (q ^ (1 / 4 : ℝ) / b) := by rw [Finset.sum_mul]
    _ ≤ (C * H * Real.log H) * (q ^ (1 / 4 : ℝ) / b) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun z _ _ =>
        Nat.cast_nonneg (multiplicity z))).trans (hcount H hH)
    _ = _ := by ring

private lemma canonicalFactor_logDeriv_norm_le {R : ℝ} {w z : ℂ}
    (hR : (31 / 16 : ℝ) ≤ R) (hw : ‖w‖ < R) (hz : ‖z‖ ≤ 15 / 8) (hzw : z ≠ w) :
    ‖logDeriv (Complex.canonicalFactor R w) z‖ ≤ 16 + ‖z - w‖⁻¹ := by
  let A (v : ℂ) := (R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ w) * v
  let B (v : ℂ) := (R : ℂ) * (v - w)
  have hR0 : 0 < R := by linarith only [hR]
  have hRz : 0 < R - ‖z‖ := by linarith only [hR, hz]
  have hA : R * (R - ‖z‖) ≤ ‖A z‖ := by
    have h := norm_sub_norm_le ((R : ℂ) ^ (2 : ℕ)) ((starRingEnd ℂ w) * z)
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, norm_mul, Complex.norm_conj] at h
    have hmul := mul_le_mul_of_nonneg_right hw.le (norm_nonneg z)
    dsimp [A]
    nlinarith only [h, hmul]
  have hAz : A z ≠ 0 := norm_pos_iff.mp ((mul_pos hR0 hRz).trans_le hA)
  have hBz : B z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hR0.ne') (sub_ne_zero.mpr hzw)
  have hAd : HasDerivAt A (-(starRingEnd ℂ w)) z := by
    dsimp [A]
    simpa only [id_eq, mul_one, neg_mul] using
      ((((hasDerivAt_id z).const_mul (starRingEnd ℂ w)).const_sub ((R : ℂ) ^ (2 : ℕ))))
  have hB' : logDeriv B z = (z - w)⁻¹ := by
    unfold B
    rw [logDeriv_const_mul (f := fun v : ℂ => v - w) z (R : ℂ) (Complex.ofReal_ne_zero.mpr hR0.ne'),
      logDeriv_sub_const]
  have he := logDeriv_div z (f := A) (g := B) hAz hBz hAd.differentiableAt (by unfold B; fun_prop)
  change logDeriv (Complex.canonicalFactor R w) z = _ at he
  rw [he, hB']
  apply (norm_sub_le _ _).trans
  rw [norm_inv]
  apply add_le_add_left
  rw [logDeriv_apply, hAd.deriv, norm_div, norm_neg, Complex.norm_conj]
  calc
    _ ≤ R / (R * (R - ‖z‖)) := div_le_div₀ hR0.le hw.le (mul_pos hR0 hRz) hA
    _ = 1 / (R - ‖z‖) := by field_simp
    _ ≤ 16 := (div_le_iff₀ hRz).mpr (by linarith only [hR, hz])

private lemma exists_zeta_radius (c : ℂ) {r R : ℝ} (hlt : r < R) :
    ∃ ρ ∈ Set.Ioo r R, ∀ w ∈ Metric.sphere (0 : ℂ) ρ, riemannZeta₁ (c + w) ≠ 0 := by
  let E := Metric.closedBall c R ∩ riemannZetaZeros
  have hE : E.Finite := (isCompact_closedBall c _).inter_riemannZetaZeros_finite
  let F := (fun z => dist z c) '' E
  obtain ⟨ρ, hρ, hρF⟩ := ((Set.Ioo_infinite hlt).sdiff (hE.image _)).nonempty
  refine ⟨ρ, hρ, fun w hw hzero => ?_⟩
  have hne : c + w ≠ 1 := by
    intro h
    simp [h, riemannZeta₁_one] at hzero
  have hwn : ‖w‖ = ρ := by simpa [dist_eq_norm] using hw
  have hdist : dist (c + w) c = ρ := by rw [dist_eq_norm, add_sub_cancel_left, hwn]
  apply hρF
  change ρ ∈ F
  refine ⟨c + w, ⟨Metric.mem_closedBall.mpr (hdist.le.trans hρ.2.le), ?_⟩, hdist⟩
  rw [show c + w ∈ riemannZetaZeros ↔ riemannZeta (c + w) = 0 from Iff.rfl,
    riemannZeta_eq_inv_sub_mul hne, hzero, mul_zero]

private lemma log_abs_add_three_ge_one (t : ℝ) : 1 ≤ Real.log (|t| + 3) := by
  have h := Real.log_le_log (Real.exp_pos 1)
    (Real.exp_one_lt_three.le.trans (by linarith only [abs_nonneg t] : (3 : ℝ) ≤ |t| + 3))
  simpa only [Real.log_exp] using h

private lemma norm_zeta₁_disk_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, ∀ z : ℂ, ‖z‖ ≤ 63 / 32 →
      ‖riemannZeta₁ (zpoint 2 t + z)‖ ≤ C * (|t| + 3) ^ (2 : ℕ) := by
  obtain ⟨B, hB, hb⟩ := norm_riemannZeta₁_le (by norm_num : (0 : ℝ) < 1 / 32)
  refine ⟨1 + 4 * B, by linarith only [hB], fun t z hz => ?_⟩
  have hzre : 1 / 32 ≤ (zpoint 2 t + z).re := by
    have h := (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
    rw [Complex.add_re, zpoint_re]
    linarith only [h, hz]
  have hcenter : ‖zpoint 2 t‖ ≤ 2 + |t| := by
    simpa using Complex.norm_le_abs_re_add_abs_im (zpoint 2 t)
  have h₁ : ‖zpoint 2 t + z‖ ≤ 2 * (|t| + 3) := by
    have h := norm_add_le (zpoint 2 t) z
    linarith only [h, hcenter, hz, abs_nonneg t]
  have h₂ : ‖zpoint 2 t + z - 1‖ ≤ 2 * (|t| + 3) := by
    have h := norm_sub_le (zpoint 2 t + z) (1 : ℂ)
    have h' := norm_add_le (zpoint 2 t) z
    rw [norm_one] at h
    linarith only [h, h', hcenter, hz, abs_nonneg t]
  apply (hb _ hzre).trans
  have hmul := mul_le_mul h₂ h₁ (norm_nonneg _) (by positivity : 0 ≤ 2 * (|t| + 3))
  have hsq : 1 ≤ (|t| + 3) ^ (2 : ℕ) := by nlinarith only [abs_nonneg t, sq_nonneg |t|]
  calc
    _ ≤ 1 + B * ((2 * (|t| + 3)) * (2 * (|t| + 3))) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hmul hB) _
    _ ≤ _ := by nlinarith only [hsq]

private lemma norm_zeta₁_center_lower (t : ℝ) : (1 / 4 : ℝ) ≤ ‖riemannZeta₁ (zpoint 2 t)‖ := by
  let s := zpoint 2 t
  have hs : s.re = 2 := zpoint_re _ _
  have hn : s ≠ 1 := fun h => (by norm_num : (2 : ℝ) ≠ 1) (by simpa [h] using hs.symm)
  have he : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hn, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hn), one_mul]
  have hnorm : 1 ≤ ‖s - 1‖ := by
    have h := Complex.abs_re_le_norm (s - 1)
    norm_num [Complex.sub_re, hs] at h ⊢
    exact h
  rw [show zpoint 2 t = s from rfl, he, norm_mul]
  exact (norm_riemannZeta_two_re_lower hs).trans (le_mul_of_one_le_left (norm_nonneg _) hnorm)

private lemma analyticOrderAt_add_left (f : ℂ → ℂ) (c w : ℂ) (hf : AnalyticAt ℂ f (c + w)) :
    analyticOrderAt (fun y => f (c + y)) w = analyticOrderAt f (c + w) := by
  let g (y : ℂ) := c + y
  have hg : AnalyticAt ℂ g w := by unfold g; fun_prop
  have he : (fun y => g y - g w) = fun y => y - w := by
    funext y
    dsimp [g]
    ring
  change analyticOrderAt (f ∘ g) w = analyticOrderAt f (g w)
  rw [hf.analyticOrderAt_comp hg, he]
  have hder : HasDerivAt (fun y : ℂ => y - w) 1 w := (hasDerivAt_id w).sub_const w
  have horder : analyticOrderAt (fun y => y - w) w = 1 :=
    (by fun_prop : AnalyticAt ℂ (fun y : ℂ => y - w) w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (sub_self w) (by rw [hder.deriv]; exact one_ne_zero)
  rw [horder, mul_one]

private lemma translated_zeta₁_divisor {c w : ℂ} {R : ℝ} (hw : w ∈ Metric.ball (0 : ℂ) R)
    (hne : c + w ≠ 1) :
    MeromorphicOn.divisor (fun y => riemannZeta₁ (c + y)) (Metric.ball 0 R) w =
      (multiplicity (c + w) : ℤ) := by
  have hd : AnalyticOnNhd ℂ (fun y => riemannZeta₁ (c + y)) (Metric.ball 0 R) :=
    fun y _ => (differentiable_riemannZeta₁.analyticAt (c + y)).comp (by fun_prop)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hd hw,
    analyticOrderAt_add_left _ _ _ (differentiable_riemannZeta₁.analyticAt _), ← multiplicity_zeta₁ hne,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_zeta₁_ne_top (c + w))]
  simp

open scoped Classical in
private lemma local_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ∑ w ∈ (zerosUpTo (|t| + 2)).filter (fun w => |w.im - t| ≤ 2), (multiplicity w : ℝ) ≤
        C * Real.log (|t| + 3) := by
  classical
  obtain ⟨A, hA, hcount⟩ := all_zeros_unit_count
  refine ⟨8 * A, by positivity, fun t => ?_⟩
  let S := zerosUpTo (|t| + 2)
  let U (s : ℝ) := S.filter (fun z => s ≤ z.im ∧ z.im ≤ s + 1)
  let f (w : ℂ) : ℝ := multiplicity w
  let L := Real.log (|t| + 3)
  have hunion (P Q : Finset ℂ) : ∑ w ∈ P ∪ Q, f w ≤ (∑ w ∈ P, f w) + ∑ w ∈ Q, f w := by
    rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => Nat.cast_nonneg (multiplicity w))
  have hu {j : ℝ} (hj : |j| ≤ 2) : ∑ w ∈ U (t + j), f w ≤ 2 * A * L := by
    have htj := abs_add_le t j
    have hbase : |t + j| + 2 ≤ (|t| + 3) ^ (2 : ℕ) := by
      nlinarith only [htj, hj, sq_nonneg |t|, abs_nonneg t]
    have hlog := Real.log_le_log (by positivity : 0 < |t + j| + 2) hbase
    rw [Real.log_pow, Nat.cast_ofNat] at hlog
    exact (hcount (|t| + 2) (t + j)).trans
      ((mul_le_mul_of_nonneg_left hlog hA.le).trans_eq (by dsimp [L]; ring))
  have hsub : S.filter (fun w => |w.im - t| ≤ 2) ⊆
      ((U (t - 2) ∪ U (t - 1)) ∪ U t) ∪ U (t + 1) := by
    intro w hw
    obtain ⟨hmem, hdist⟩ := Finset.mem_filter.mp hw
    obtain ⟨hl, hh⟩ := abs_le.mp hdist
    simp only [Finset.mem_union, U, Finset.mem_filter, hmem, true_and]
    by_cases h₁ : w.im ≤ t - 1
    · exact Or.inl (Or.inl (Or.inl ⟨by linarith only [hl], by linarith only [h₁]⟩))
    by_cases h₂ : w.im ≤ t
    · exact Or.inl (Or.inl (Or.inr ⟨by linarith only [h₁], by linarith only [h₂]⟩))
    by_cases h₃ : w.im ≤ t + 1
    · exact Or.inl (Or.inr ⟨by linarith only [h₂], h₃⟩)
    · exact Or.inr ⟨by linarith only [h₃], by linarith only [hh]⟩
  have h₁ : ∑ w ∈ U (t - 2), f w ≤ 2 * A * L := by simpa [sub_eq_add_neg] using hu (j := -2) (by norm_num)
  have h₂ : ∑ w ∈ U (t - 1), f w ≤ 2 * A * L := by simpa [sub_eq_add_neg] using hu (j := -1) (by norm_num)
  have h₃ : ∑ w ∈ U t, f w ≤ 2 * A * L := by simpa using hu (j := 0) (by norm_num)
  have h₄ : ∑ w ∈ U (t + 1), f w ≤ 2 * A * L := hu (j := 1) (by norm_num)
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => Nat.cast_nonneg (multiplicity w))).trans
  have ha := hunion (U (t - 2)) (U (t - 1))
  have hb := hunion (U (t - 2) ∪ U (t - 1)) (U t)
  have hc := hunion ((U (t - 2) ∪ U (t - 1)) ∪ U t) (U (t + 1))
  linarith only [h₁, h₂, h₃, h₄, ha, hb, hc]

private lemma translated_zeta₁_zero_mem {t : ℝ} {w : ℂ} (hw : ‖w‖ ≤ 63 / 32)
    (hzero : riemannZeta₁ (zpoint 2 t + w) = 0) :
    zpoint 2 t + w ∈ zerosUpTo (|t| + 2) ∧ |(zpoint 2 t + w).im - t| ≤ 2 := by
  let s := zpoint 2 t + w
  have hs1 : s ≠ 1 := by
    intro h
    change riemannZeta₁ s = 0 at hzero
    simp [h, riemannZeta₁_one] at hzero
  have hζ : riemannZeta s = 0 := by rw [riemannZeta_eq_inv_sub_mul hs1, hzero, mul_zero]
  have hsre : 0 < s.re := by
    have h := (neg_le_abs w.re).trans (Complex.abs_re_le_norm w)
    change 0 < (zpoint 2 t + w).re
    rw [Complex.add_re, zpoint_re]
    linarith only [h, hw]
  have hsre' : s.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  have him : |w.im| ≤ 2 := (Complex.abs_im_le_norm w).trans (hw.trans (by norm_num))
  refine ⟨mem_zerosUpTo.mpr ⟨hζ, hsre, hsre', ?_⟩, ?_⟩
  · rw [Complex.add_im, zpoint_im]
    exact (abs_add_le _ _).trans (add_le_add_right him _)
  · rw [Complex.add_im, zpoint_im, add_sub_cancel_left]
    exact him

private lemma norm_logDeriv_zeta₁_segment :
    ∃ K : ℝ, 0 < K ∧ ∀ t σ : ℝ, 1 / 8 ≤ σ → σ ≤ 2 → ∀ δ : ℝ, 0 < δ →
      (∀ w ∈ zerosUpTo (|t| + 2), |w.im - t| ≤ 2 → δ ≤ ‖zpoint σ t - w‖) →
      riemannZeta₁ (zpoint σ t) ≠ 0 ∧
        ‖logDeriv riemannZeta₁ (zpoint σ t)‖ ≤ K * Real.log (|t| + 3) * (1 + δ⁻¹) := by
  classical
  obtain ⟨C, hC, hbound⟩ := norm_zeta₁_disk_bound
  obtain ⟨N, hN, hn⟩ := local_zero_count
  let A : ℝ := |Real.log C| + |Real.log (1 / 4 : ℝ)| + 3
  let K := 4096 * A + 16 * N
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨K, by dsimp [K]; positivity, fun t σ hσ hσ' δ hδ hSep => ?_⟩
  let c := zpoint 2 t
  let s := zpoint σ t
  let x := s - c
  let f (w : ℂ) := riemannZeta₁ (c + w)
  let L := Real.log (|t| + 3)
  let M := C * (|t| + 3) ^ (2 : ℕ)
  have hcx : c + x = s := by dsimp [x]; ring
  have hx : ‖x‖ ≤ 15 / 8 := by
    have hx' : x = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [x, c, s, Complex.sub_re]
      · simp [x, c, s, Complex.sub_im]
    rw [hx', Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hσ')]
    linarith only [hσ]
  have hfn : f x ≠ 0 := by
    intro hzero
    have hm := translated_zeta₁_zero_mem (hx.trans (by norm_num)) (show riemannZeta₁ (zpoint 2 t + x) = 0 from hzero)
    change zpoint 2 t + x = s at hcx
    rw [hcx] at hm
    have h := hSep s hm.1 hm.2
    rw [sub_self, norm_zero] at h
    exact hδ.not_ge h
  refine ⟨by simpa only [f, hcx] using hfn, ?_⟩
  obtain ⟨R, hR, hRnz⟩ := exists_zeta_radius c (by norm_num : (31 / 16 : ℝ) < 63 / 32)
  have hR0 : 0 < R := by linarith only [hR.1]
  have hfA (z : ℂ) : AnalyticAt ℂ f z :=
    (differentiable_riemannZeta₁.analyticAt (c + z)).comp (by fun_prop)
  have hFlower : (1 / 4 : ℝ) ≤ ‖f 0‖ := by simpa only [f, add_zero, c] using norm_zeta₁_center_lower t
  have hf0 : f 0 ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hFlower)
  obtain ⟨g, Z, _, hZ, hgA, hgN, hgBound, hg0, hlog⟩ := disk_logDeriv_data hR0
    (fun z _ => hfA z) hf0 (M := M) (fun z hz => ⟨hRnz z hz, hbound t z (by
      have h := Metric.mem_sphere.mp hz
      rw [dist_zero_right] at h
      exact h.le.trans hR.2.le)⟩)
  have hL : 1 ≤ L := log_abs_add_three_ge_one t
  have hM : Real.log M = Real.log C + 2 * L := by
    dsimp [M, L]
    rw [Real.log_mul (by linarith only [hC]) (by positivity), Real.log_pow, Nat.cast_ofNat]
  have hB : Real.log M - Real.log ‖g 0‖ + 1 ≤ A * L := by
    rw [hM]
    have hf0log := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hFlower
    have ha : 0 ≤ |Real.log C| + |Real.log (1 / 4 : ℝ)| + 1 := by positivity
    have hLL := mul_le_mul_of_nonneg_left hL ha
    dsimp [A]
    nlinarith only [hg0, hf0log, hLL, le_abs_self (Real.log C), neg_le_abs (Real.log (1 / 4 : ℝ))]
  have hgb : ‖logDeriv g x‖ ≤ 4096 * (A * L) :=
    (norm_logDeriv_le_on_inner_ball hR.1.le (hgA.mono Metric.ball_subset_closedBall)
      (fun z hz => hgN z (Metric.ball_subset_closedBall hz)) hgBound hx).trans
        (mul_le_mul_of_nonneg_left hB (by norm_num))
  let D := MeromorphicOn.divisor f (Metric.ball 0 R)
  have hxR : x ∈ Metric.ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr (by linarith only [hx, hR.1])
  have hZw {w : ℂ} (hw : w ∈ Z) : c + w ∈ zerosUpTo (|t| + 2) ∧ |(c + w).im - t| ≤ 2 :=
    translated_zeta₁_zero_mem ((mem_ball_zero_iff.mp (hZ w hw).1).le.trans hR.2.le)
      (hZ w hw).2
  have hD {w : ℂ} (hw : w ∈ Z) : D w = (multiplicity (c + w) : ℤ) := by
    apply translated_zeta₁_divisor (hZ w hw).1
    intro h
    have hh := (mem_zerosUpTo.mp (hZw hw).1).2.2.1
    simp [h] at hh
  have hNsum : ∑ w ∈ Z, (multiplicity (c + w) : ℝ) ≤ N * L := by
    let P := (zerosUpTo (|t| + 2)).filter (fun w => |w.im - t| ≤ 2)
    have hsub : Z.image (fun w => c + w) ⊆ P := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_filter.mpr (hZw hv)
    calc
      _ = ∑ w ∈ Z.image (fun w => c + w), (multiplicity w : ℝ) := by
        rw [Finset.sum_image (fun _ _ _ _ heq => add_left_cancel heq)]
      _ ≤ ∑ w ∈ P, (multiplicity w : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => Nat.cast_nonneg (multiplicity w))
      _ ≤ N * L := hn t
  let G (w : ℂ) := logDeriv (Complex.canonicalFactor R w) x
  have hSb : ‖∑ w ∈ Z, (D w : ℂ) * G w‖ ≤ (N * L) * (16 + δ⁻¹) := by
    calc
      _ ≤ ∑ w ∈ Z, ‖(D w : ℂ) * G w‖ := norm_sum_le _ _
      _ ≤ ∑ w ∈ Z, (multiplicity (c + w) : ℝ) * (16 + δ⁻¹) := by
        apply Finset.sum_le_sum
        intro w hw
        rw [hD hw, Int.cast_natCast, norm_mul, Complex.norm_natCast]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hδw := hSep (c + w) (hZw hw).1 (hZw hw).2
        have he : x - w = s - (c + w) := by dsimp [x]; ring
        have hd : δ ≤ ‖x - w‖ := he ▸ hδw
        have hxw : x ≠ w := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hd))
        apply (canonicalFactor_logDeriv_norm_le hR.1.le
          (mem_ball_zero_iff.mp (hZ w hw).1) hx hxw).trans
        exact add_le_add_right (inv_le_inv₀ (hδ.trans_le hd) hδ |>.2 (by linarith only [hd])) _
      _ = (∑ w ∈ Z, (multiplicity (c + w) : ℝ)) * (16 + δ⁻¹) := Finset.sum_mul .. |>.symm
      _ ≤ (N * L) * (16 + δ⁻¹) := mul_le_mul_of_nonneg_right hNsum (by positivity)
  have hf_eq : logDeriv f x = logDeriv riemannZeta₁ s := by
    have hd : HasDerivAt (fun z : ℂ => c + z) 1 x := (hasDerivAt_id x).const_add c
    change logDeriv (riemannZeta₁ ∘ fun z => c + z) x = _
    rw [logDeriv_comp differentiable_riemannZeta₁.differentiableAt hd.differentiableAt, hd.deriv, mul_one, hcx]
  rw [← hf_eq, show logDeriv f x = logDeriv g x - ∑ w ∈ Z, (D w : ℂ) * G w from
    eq_sub_of_add_eq' (hlog x hxR hfn).symm]
  apply (norm_sub_le _ _).trans
  apply (add_le_add hgb hSb).trans
  dsimp [K]
  have hp : 0 ≤ A * L * δ⁻¹ := by positivity
  have hp' : 0 ≤ N * L * δ⁻¹ := by positivity
  nlinarith only [hp, hp']

private lemma norm_negLogDeriv_zeta_of_separation :
    ∃ K : ℝ, 0 < K ∧ ∀ t σ : ℝ, 1 / 8 ≤ σ → σ ≤ 2 → ∀ δ : ℝ, 0 < δ →
      (∀ w ∈ zerosUpTo (|t| + 2), |w.im - t| ≤ 2 → δ ≤ ‖zpoint σ t - w‖) →
      1 / 2 ≤ ‖zpoint σ t - 1‖ → riemannZeta (zpoint σ t) ≠ 0 ∧
      ‖-logDeriv riemannZeta (zpoint σ t)‖ ≤ K * Real.log (|t| + 3) * (1 + δ⁻¹) := by
  obtain ⟨K, hK, hbound⟩ := norm_logDeriv_zeta₁_segment
  refine ⟨K + 2, by positivity, fun t σ hs hs' δ hd hsep hdist => ?_⟩
  let s := zpoint σ t
  have hn : s ≠ 1 := by
    intro he
    change 1 / 2 ≤ ‖s - 1‖ at hdist
    norm_num [he] at hdist
  obtain ⟨hnz, h⟩ := hbound t σ hs hs' δ hd hsep
  have hζ : riemannZeta s ≠ 0 := by
    rw [riemannZeta_eq_inv_sub_mul hn]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hn)) hnz
  refine ⟨hζ, ?_⟩
  change ‖-logDeriv riemannZeta s‖ ≤ _
  rw [neg_logDeriv_zeta_eq hn hnz]
  apply (norm_sub_le _ _).trans
  rw [norm_inv]
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    have hp : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hn)
    rw [← one_div]
    exact (div_le_iff₀ hp).mpr (by linarith only [hdist])
  apply (add_le_add hinv h).trans
  have hlog := log_abs_add_three_ge_one t
  have hi := inv_nonneg.mpr hd.le
  nlinarith only [hlog, hi, mul_nonneg (sub_nonneg.mpr hlog) hi]

private lemma separated_height_both {c T H : ℝ} (hs : HeightSeparated c T H) {t : ℝ}
    (ht : |t| = H) {w : ℂ} (hzero : riemannZeta w = 0) (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    c / Real.log (T + 3) ≤ |t - w.im| := by
  rcases le_total 0 t with hpos | hneg
  · rw [abs_of_nonneg hpos] at ht
    rw [ht]
    exact hs w hzero hw₀ hw₁
  · have hv : riemannZeta (starRingEnd ℂ w) = 0 := by rw [riemannZeta_conj, hzero, map_zero]
    have hh := hs (starRingEnd ℂ w) hv (by simpa using hw₀) (by simpa using hw₁)
    have he : H - (starRingEnd ℂ w).im = -(t - w.im) := by
      rw [Complex.conj_im, ← ht, abs_of_nonpos hneg]
      ring
    rwa [he, abs_neg] at hh

private lemma zetaLogDeriv_on_selected_edges (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ T ≥ 3, ∀ H ≥ T, HeightSeparated c T H →
      ∃ a ∈ Set.Icc (1 / 8 : ℝ) (1 / 4),
      (∀ w ∈ zerosUpTo H, w.re ≠ a) ∧
      (∀ σ ∈ Set.Icc (1 / 8 : ℝ) 2, ∀ t : ℝ, |t| = H →
        ‖-logDeriv riemannZeta (zpoint σ t)‖ ≤ K * Real.log (H + 3) ^ (2 : ℕ)) ∧
      (∀ t ∈ Set.Icc (-H) H, riemannZeta (zpoint a t) ≠ 0 ∧
        ‖-logDeriv riemannZeta (zpoint a t)‖ ≤ K * H * Real.log (H + 3) ^ (2 : ℕ)) := by
  obtain ⟨B, hB, hlogDeriv⟩ := norm_negLogDeriv_zeta_of_separation
  obtain ⟨D, hD, hchoose⟩ := exists_separated_abscissa
  let K := B * ((1 + c⁻¹) + (1 + 2 * D))
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  refine ⟨K, by dsimp [K]; positivity, fun T hT H hHT hSep => ?_⟩
  have hH : 3 ≤ H := hT.trans hHT
  have hH0 : 0 < H := by linarith only [hH]
  have hHD : 3 ≤ H + 2 := by linarith only [hH]
  let δ := (D * (H + 2) * Real.log (H + 2))⁻¹
  have hlogH : 0 < Real.log (H + 2) := Real.log_pos (by linarith only [hH])
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨a, ha, havoids⟩ := hchoose (H + 2) hHD
  have hδw {w : ℂ} (hw : w ∈ zerosUpTo (H + 2)) : δ ≤ |a - w.re| := havoids w hw
  have hsubset {u : ℝ} (hu : u ≤ H + 2) {w : ℂ} (hw : w ∈ zerosUpTo u) : w ∈ zerosUpTo (H + 2) := by
    obtain ⟨hz, h₀, h₁, hi⟩ := mem_zerosUpTo.mp hw
    exact mem_zerosUpTo.mpr ⟨hz, h₀, h₁, hi.trans hu⟩
  refine ⟨a, ha, fun w hw he => ?_, ?_, ?_⟩
  · have hh := hδw (hsubset (by linarith) hw)
    rw [he, sub_self, abs_zero] at hh
    exact hδ.not_ge hh
  · intro σ hσ t ht
    let ε := c / Real.log (T + 3)
    let L := Real.log (H + 3)
    have hlogT : 0 < Real.log (T + 3) := Real.log_pos (by linarith only [hT])
    have hε : 0 < ε := div_pos hc hlogT
    have hL : 1 ≤ L := by simpa only [L, abs_of_nonneg hH0.le] using log_abs_add_three_ge_one H
    have hl : Real.log (T + 3) ≤ L := Real.log_le_log (by linarith only [hT]) (by linarith only [hHT])
    have hd (w : ℂ) (hw : w ∈ zerosUpTo (|t| + 2)) (_hw' : |w.im - t| ≤ 2) :
        ε ≤ ‖zpoint σ t - w‖ := by
      obtain ⟨hz, h₀, h₁, _⟩ := mem_zerosUpTo.mp hw
      have h := separated_height_both hSep ht hz h₀ h₁
      have hh := Complex.abs_im_le_norm (zpoint σ t - w)
      rw [Complex.sub_im, zpoint_im] at hh
      exact h.trans hh
    have hp : 1 / 2 ≤ ‖zpoint σ t - 1‖ := by
      have hi := Complex.abs_im_le_norm (zpoint σ t - 1)
      rw [Complex.sub_im, zpoint_im, Complex.one_im, sub_zero, ht] at hi
      linarith only [hi, hH]
    have he := (hlogDeriv t σ hσ.1 hσ.2 ε hε hd hp).2
    rw [ht] at he
    apply he.trans
    have hεi : ε⁻¹ ≤ L * c⁻¹ := by
      have heq : ε⁻¹ = Real.log (T + 3) * c⁻¹ := by
        dsimp [ε]
        rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
      rw [heq]
      exact mul_le_mul_of_nonneg_right hl hci.le
    have hh : 1 + ε⁻¹ ≤ (1 + c⁻¹) * L := by nlinarith only [hL, hεi]
    calc
      _ ≤ B * L * ((1 + c⁻¹) * L) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (B * (1 + c⁻¹)) * L ^ (2 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [K]; nlinarith only [hB, hD, mul_pos hB hD]) (sq_nonneg _)
  · intro t ht
    let L := Real.log (H + 3)
    let l := Real.log (|t| + 3)
    have htH : |t| ≤ H := abs_le.mpr ht
    have hl : l ≤ L := Real.log_le_log (by positivity) (by linarith only [htH])
    have hL : 1 ≤ L := by simpa only [L, abs_of_nonneg hH0.le] using log_abs_add_three_ge_one H
    have hll : 1 ≤ l := log_abs_add_three_ge_one t
    have hs' : a ≤ 2 := by linarith only [ha.2]
    have hdist (w : ℂ) (hw : w ∈ zerosUpTo (|t| + 2)) (_hw' : |w.im - t| ≤ 2) :
        δ ≤ ‖zpoint a t - w‖ := by
      have hr := Complex.abs_re_le_norm (zpoint a t - w)
      rw [Complex.sub_re, zpoint_re] at hr
      exact (hδw (hsubset (by linarith only [htH]) hw)).trans hr
    have hp : 1 / 2 ≤ ‖zpoint a t - 1‖ := by
      have hr := Complex.abs_re_le_norm (zpoint a t - 1)
      rw [Complex.sub_re, zpoint_re, Complex.one_re, abs_of_nonpos (by linarith only [ha.2])] at hr
      linarith only [hr, ha.2]
    obtain ⟨hn, he⟩ := hlogDeriv t a ha.1 hs' δ hδ hdist hp
    refine ⟨hn, he.trans ?_⟩
    have hli : Real.log (H + 2) ≤ L := Real.log_le_log (by linarith only [hH]) (by linarith)
    have hinv : δ⁻¹ ≤ (2 * D) * (H * L) := by
      dsimp [δ]
      rw [inv_inv]
      have hh := mul_le_mul (show H + 2 ≤ 2 * H by linarith only [hH]) hli
        (Real.log_nonneg (by linarith only [hH])) (by positivity : 0 ≤ 2 * H)
      calc
        _ = D * ((H + 2) * Real.log (H + 2)) := by ring
        _ ≤ D * ((2 * H) * L) := mul_le_mul_of_nonneg_left hh hD.le
        _ = _ := by ring
    have hHL : 1 ≤ H * L := by
      exact (show (1 : ℝ) ≤ H by linarith only [hH]).trans (le_mul_of_one_le_right hH0.le hL)
    have hsum : 1 + δ⁻¹ ≤ (1 + 2 * D) * (H * L) := by nlinarith only [hinv, hHL]
    calc
      _ ≤ (B * L) * ((1 + 2 * D) * (H * L)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hl hB.le) hsum (by positivity) (by positivity)
      _ = (B * (1 + 2 * D)) * (H * L ^ (2 : ℕ)) := by ring
      _ ≤ K * (H * L ^ (2 : ℕ)) := mul_le_mul_of_nonneg_right (by
        dsimp [K]; nlinarith only [hB, hci, mul_pos hB hci]) (by positivity)
      _ = _ := by dsimp [L]; ring

private lemma zetaVertical_eq (q a H : ℝ) :
    zetaVertical q a H = I * ∫ t in -H..H, zetaPerron q (zpoint a t) := by
  simp only [zetaVertical, zetaPerron, logDeriv_apply, neg_div]

private lemma norm_zetaPerron (q : ℝ) (hq : 0 < q) (z : ℂ) :
    ‖zetaPerron q z‖ = ‖-logDeriv riemannZeta z‖ * (q ^ z.re / ‖z‖) := by
  rw [zetaPerron, norm_mul, norm_perron_integrand, Real.rpow_def_of_pos hq]

private lemma norm_zetaPerron_horizontal_integral {q a b H t B : ℝ} (hq : 1 ≤ q)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) (hH : 0 < H) (ht : |t| = H) (hB : 0 ≤ B)
    (hbound : ∀ σ ∈ Set.Icc a b, ‖-logDeriv riemannZeta (zpoint σ t)‖ ≤ B) :
    ‖∫ σ in a..b, zetaPerron q (zpoint σ t)‖ ≤ (2 * B) * (q ^ b / H) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := B * (q ^ b / H)) (a := a) (b := b) (f := fun σ => zetaPerron q (zpoint σ t)) (by
      intro σ hσ
      have hs : σ ∈ Set.Icc a b := Set.uIoc_subset_uIcc hσ
        |> (fun h => by simpa only [Set.uIcc_of_le hab] using h)
      rw [norm_zetaPerron q (zero_lt_one.trans_le hq), zpoint_re]
      apply mul_le_mul (hbound σ hs) _ (by positivity) hB
      apply div_le_div₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hq hs.2) hH
      simpa only [zpoint_im, ht] using Complex.abs_im_le_norm (zpoint σ t))
  refine h.trans ?_
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  calc
    _ ≤ (B * (q ^ b / H)) * 2 := mul_le_mul_of_nonneg_left (by linarith only [ha, hb]) (by positivity)
    _ = _ := by ring

private lemma integral_profile {H : ℝ} (hH : 0 ≤ H) :
    (∫ t in -H..H, (1 + |t|)⁻¹) = 2 * Real.log (1 + H) := by
  let f (t : ℝ) := (1 + |t|)⁻¹
  change (∫ t in -H..H, f t) = _
  have hf : Continuous f := (continuous_const.add continuous_abs).inv₀ (fun t => (show 0 < (1 : ℝ) + |t| by positivity).ne')
  have heven : (∫ t in -H..0, f t) = ∫ t in 0..H, f t := by
    simpa only [f, abs_neg, neg_zero] using
      (intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := H)).symm
  have hright : (∫ t in 0..H, f t) = Real.log (1 + H) := by
    have he : (∫ t in 0..H, f t) = ∫ t in 0..H, (t + 1)⁻¹ := by
      apply intervalIntegral.integral_congr
      rw [Set.uIcc_of_le hH]
      intro t ht
      simp [f, abs_of_nonneg ht.1, add_comm]
    rw [he, intervalIntegral.integral_comp_add_right (f := fun t : ℝ => t⁻¹), zero_add,
      integral_inv_of_pos zero_lt_one (by positivity), div_one, add_comm H 1]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-H) 0) (hf.intervalIntegrable 0 H), heven, hright]
  ring

private lemma norm_zetaVertical_le_of_uniform_logDeriv {q a H B : ℝ} (hq : 0 < q) (ha : 1 / 8 ≤ a)
    (ha' : a < 1) (hH : 0 < H) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Icc (-H) H, riemannZeta (zpoint a t) ≠ 0 ∧
      ‖-logDeriv riemannZeta (zpoint a t)‖ ≤ B) :
    ‖zetaVertical q a H‖ ≤ (18 * B) * q ^ a * Real.log (1 + H) := by
  have ha0 : 0 < a := by linarith only [ha]
  have he : -H ≤ H := by linarith only [hH]
  let f (t : ℝ) := zetaPerron q (zpoint a t)
  have hcont : ContinuousOn f [[-H, H]] := by
    rw [Set.uIcc_of_le he]
    intro t ht
    have hz1 : zpoint a t ≠ 1 := by
      intro h
      have hr := congrArg Complex.re h
      exact ha'.ne (by simpa only [zpoint_re, Complex.one_re] using hr)
    exact ((zetaPerron_analyticAt q (zpoint_ne_zero_of_re ha0.ne') hz1 (hbound t ht).1).continuousAt.comp
      (by unfold zpoint; fun_prop : ContinuousAt (fun t => zpoint a t) t)).continuousWithinAt
  let g (t : ℝ) := (9 * B) * q ^ a * (1 + |t|)⁻¹
  have hg : Continuous g := continuous_const.mul ((continuous_const.add continuous_abs).inv₀
    (fun t => (show 0 < (1 : ℝ) + |t| by positivity).ne'))
  rw [zetaVertical_eq, norm_mul, Complex.norm_I, one_mul]
  change ‖∫ t in -H..H, f t‖ ≤ _
  refine (intervalIntegral.norm_integral_le_integral_norm he).trans ?_
  have hl : ∀ t ∈ Set.Icc (-H) H, ‖f t‖ ≤ g t := by
    intro t ht
    have hN : 0 < ‖zpoint a t‖ := norm_pos_iff.mpr (zpoint_ne_zero_of_re ha0.ne')
    have hr : a ≤ ‖zpoint a t‖ := by
      simpa only [zpoint_re, abs_of_pos ha0] using Complex.abs_re_le_norm (zpoint a t)
    have hi : |t| ≤ ‖zpoint a t‖ := by
      simpa only [zpoint_im] using Complex.abs_im_le_norm (zpoint a t)
    have hd : 1 + |t| ≤ 9 * ‖zpoint a t‖ := by linarith only [ha, hr, hi]
    have hden : ‖zpoint a t‖⁻¹ ≤ 9 * (1 + |t|)⁻¹ := by
      rw [← one_div, ← div_eq_mul_inv]
      exact (div_le_div_iff₀ hN (by positivity)).2 (by simpa only [one_mul] using hd)
    dsimp [f]
    rw [norm_zetaPerron q hq, zpoint_re, div_eq_mul_inv]
    calc
      _ ≤ B * (q ^ a * (9 * (1 + |t|)⁻¹)) :=
        mul_le_mul (hbound t ht).2 (mul_le_mul_of_nonneg_left hden (by positivity)) (by positivity) hB
      _ = g t := by dsimp [g]; ring
  calc
    _ ≤ ∫ t in -H..H, g t := intervalIntegral.integral_mono_on he hcont.norm.intervalIntegrable
      (hg.intervalIntegrable _ _) hl
    _ = _ := by
      dsimp [g]
      rw [intervalIntegral.integral_const_mul, integral_profile hH.le]
      ring

private lemma perronLine_bounds {q : ℝ} (hq : 1 ≤ Real.log q) :
    1 < perronLine q ∧ perronLine q ≤ 2 := by
  have hp : 0 < Real.log q := zero_lt_one.trans_le hq
  have hlu : (Real.log q)⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_iff₀ hp).mpr (by simpa using hq)
  unfold perronLine
  exact ⟨lt_add_of_pos_right _ (inv_pos.mpr hp), by linarith only [hlu]⟩

private lemma rpow_perronLine {q : ℝ} (hq : 1 < q) : q ^ perronLine q = Real.exp 1 * q := by
  have hq0 := zero_lt_one.trans hq
  have hlog := Real.log_pos hq
  rw [perronLine, Real.rpow_add hq0, Real.rpow_one, Real.rpow_def_of_pos hq0,
    mul_inv_cancel₀ hlog.ne', mul_comm]

private lemma zeta_contour_bound_at (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ T ≥ 3, ∀ H ≥ T, HeightSeparated c T H → ∀ q ≥ Real.exp 1,
      ‖zetaVertical q (perronLine q) H - (2 * (Real.pi : ℂ) * I) * ((q : ℂ) - zeroSum H q)‖ ≤
        K * ((q / H) * Real.log (H + 3) ^ (2 : ℕ) +
          q ^ (1 / 4 : ℝ) * H * Real.log (H + 3) ^ (3 : ℕ)) := by
  classical
  obtain ⟨B, hB, hedges⟩ := zetaLogDeriv_on_selected_edges c hc
  obtain ⟨C, hC, homit⟩ := zeroSum_sub_filtered_le
  let A := 4 * B * Real.exp 1
  let D := 18 * B + (2 * Real.pi) * C
  let K := A + D
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K, by dsimp [K]; positivity, fun T hT H hHT hSep q hq => ?_⟩
  have hH : 3 ≤ H := hT.trans hHT
  have hH0 : 0 < H := by linarith only [hH]
  have hq1 : 1 < q := Real.one_lt_exp_iff.mpr zero_lt_one |>.trans_le hq
  have hlogq : 1 ≤ Real.log q := by
    have h := Real.log_le_log (Real.exp_pos 1) hq
    rwa [Real.log_exp] at h
  let b := perronLine q
  obtain ⟨hb, hb'⟩ := perronLine_bounds hlogq
  obtain ⟨a, ha, hvert, hhor, hl⟩ := hedges T hT H hHT hSep
  have ha0 : 0 < a := by linarith only [ha.1]
  have ha1 : a < 1 := by linarith only [ha.2]
  have hab : a ≤ b := (ha1.trans hb).le
  let Z := (zerosUpTo H).filter (fun z => a < z.re)
  let Q := ∑ z ∈ Z, (multiplicity z : ℂ) * ((q : ℂ) ^ z / z)
  let S := 2 * (Real.pi : ℂ) * I
  let L := Real.log (H + 3)
  let U := (q / H) * L ^ (2 : ℕ)
  let V := q ^ (1 / 4 : ℝ) * H * L ^ (3 : ℕ)
  have hL : 1 ≤ L := by simpa only [L, abs_of_nonneg hH0.le] using log_abs_add_three_ge_one H
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let J (y : ℝ) := ∫ t in a..b, zetaPerron q (zpoint t y)
  have hJ (t : ℝ) (ht : |t| = H) : ‖J t‖ ≤ (2 * B * Real.exp 1) * U := by
    have hh (σ : ℝ) (hσ : σ ∈ Set.Icc a b) := hhor σ ⟨ha.1.trans hσ.1, hσ.2.trans hb'⟩ t ht
    apply (norm_zetaPerron_horizontal_integral hq1.le ha0.le hab hb' hH0 ht
      (show 0 ≤ B * L ^ (2 : ℕ) by positivity) hh).trans
    rw [show b = perronLine q from rfl, rpow_perronLine hq1]
    dsimp [U, L]
    ring_nf
    exact le_rfl
  have hVt : ‖zetaVertical q a H‖ ≤ (18 * B) * V := by
    apply (norm_zetaVertical_le_of_uniform_logDeriv (zero_lt_one.trans hq1) ha.1 ha1 hH0
      (show 0 ≤ B * H * L ^ (2 : ℕ) by positivity) hl).trans
    have hp := Real.rpow_le_rpow_of_exponent_le hq1.le ha.2
    have hlog := Real.log_le_log (by positivity : 0 < 1 + H) (by linarith : 1 + H ≤ H + 3)
    calc
      _ ≤ (18 * (B * H * L ^ (2 : ℕ))) * q ^ (1 / 4 : ℝ) * L := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hlog
        · exact Real.log_nonneg (by linarith only [hH])
        · positivity
      _ = _ := by dsimp [V, L]; ring
  have hS : ‖S‖ = 2 * Real.pi := by
    dsimp [S]
    simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hQ : ‖S * (zeroSum H q - Q)‖ ≤ ((2 * Real.pi) * C) * V := by
    rw [norm_mul, hS]
    have hh := homit (show 2 ≤ H by linarith only [hH]) hq1.le ha.2
    apply (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * Real.pi)).trans
    have hlog : Real.log H ≤ L ^ (3 : ℕ) := by
      apply (Real.log_le_log hH0 (show H ≤ H + 3 by linarith)).trans
      exact le_self_pow₀ hL (by norm_num)
    calc
      _ ≤ (2 * Real.pi) * (C * q ^ (1 / 4 : ℝ) * H * L ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
      _ = _ := by dsimp [V]; ring
  have hR := rectIntegral_zetaPerron ha0 ha1 hb hH0 (zero_lt_one.trans hq1) hvert
    (fun z hz => separated_height_abs hc hT hSep hz)
  change rectIntegral a b H (zetaPerron q) = S * ((q : ℂ) - Q) at hR
  rw [rectIntegral, ← zetaVertical_eq q b H, ← zetaVertical_eq q a H] at hR
  change J (-H) - J H + zetaVertical q b H - zetaVertical q a H = S * ((q : ℂ) - Q) at hR
  have heq : zetaVertical q b H - S * ((q : ℂ) - zeroSum H q) =
      ((J H - J (-H)) + zetaVertical q a H) + S * (zeroSum H q - Q) := by
    linear_combination hR
  change ‖zetaVertical q b H - S * ((q : ℂ) - zeroSum H q)‖ ≤ K * (U + V)
  rw [heq]
  have hpos := hJ H (abs_of_pos hH0)
  have hneg := hJ (-H) (by rw [abs_neg, abs_of_pos hH0])
  have hsum : ‖((J H - J (-H)) + zetaVertical q a H) + S * (zeroSum H q - Q)‖ ≤ A * U + D * V := by
    have h₁ := norm_sub_le (J H) (J (-H))
    have h₂ := norm_add_le (J H - J (-H)) (zetaVertical q a H)
    have h₃ := norm_add_le ((J H - J (-H)) + zetaVertical q a H) (S * (zeroSum H q - Q))
    dsimp [A, D]
    nlinarith only [h₁, h₂, h₃, hpos, hneg, hVt, hQ]
  apply hsum.trans
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  dsimp [K]
  nlinarith only [mul_nonneg hA.le hV, mul_nonneg hD.le hU]

-- The contour shift from the Perron line to the left of the zeta zeros.
private def ZetaContourEstimate : Prop :=
  ∀ c : ℝ, 0 < c → ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℝ in atTop,
    ∀ H ∈ Set.Icc (height x) (height x + 1), HeightSeparated c (height x) H →
      ∀ n : ℕ, (n : ℝ) + 1 / 2 ∈ Set.Icc (x - 1) (x + gap x + 1) →
        let q := (n : ℝ) + 1 / 2
        ‖zetaVertical q (perronLine q) H - (2 * (Real.pi : ℂ) * I) * ((q : ℂ) - zeroSum H q)‖ ≤
          A * (x ^ (13 / 20 : ℝ) * Real.log x ^ (2 : ℕ))

private lemma zetaContourEstimate_proved : ZetaContourEstimate := by
  intro c hc
  obtain ⟨K, hK, hbound⟩ := zeta_contour_bound_at c hc
  refine ⟨60 * K, by positivity, ?_⟩
  have ht : Tendsto height atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hsmall := (isLittleO_log_rpow_atTop (r := 1 / 20) (by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop (5 : ℝ), ht.eventually_ge_atTop (3 : ℝ), hsmall] with x hx hT hlogsmall
  intro H hH hSep n hn
  let q := (n : ℝ) + 1 / 2
  let L := Real.log (H + 3)
  let E := x ^ (13 / 20 : ℝ) * Real.log x ^ (2 : ℕ)
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hH0 : 0 < H := by linarith only [hH.1, hT]
  have hq : Real.exp 1 ≤ q := Real.exp_one_lt_three.le.trans (by
    have h := hn.1
    change x - 1 ≤ q at h
    linarith only [h, hx])
  have hq0 : 0 < q := (Real.exp_pos 1).trans_le hq
  have hgap : gap x ≤ x := (Real.rpow_le_rpow_of_exponent_le hx1
    (by norm_num : (2 / 3 : ℝ) ≤ 1)).trans_eq (Real.rpow_one x)
  have hqle : q ≤ 3 * x := by linarith only [show q ≤ x + gap x + 1 from hn.2, hgap, hx]
  have hTle : height x ≤ x := (Real.rpow_le_rpow_of_exponent_le hx1
    (by norm_num : (7 / 20 : ℝ) ≤ 1)).trans_eq (Real.rpow_one x)
  have hHle : H ≤ 2 * height x := by linarith only [hH.2, hT]
  have hL : L ≤ 2 * Real.log x := by
    have hle : H + 3 ≤ x ^ (2 : ℕ) := by
      nlinarith only [hH.2, hTle, mul_nonneg hx0.le (show 0 ≤ x - 2 by linarith only [hx]), hx]
    simpa only [L, Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity : 0 < H + 3) hle
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith only [hH0])
  have hqdiv : q / H ≤ 3 * x ^ (13 / 20 : ℝ) := by
    calc
      _ ≤ q / height x := div_le_div_of_nonneg_left hq0.le (by linarith only [hT]) hH.1
      _ ≤ (3 * x) / height x := div_le_div_of_nonneg_right hqle (by linarith only [hT])
      _ = _ := by
        rw [mul_div_assoc]
        congr 1
        calc
          _ = x ^ (1 : ℝ) / x ^ (7 / 20 : ℝ) := by rw [Real.rpow_one, height]
          _ = _ := by rw [← Real.rpow_sub hx0]; norm_num
  have hhorizontal : (q / H) * L ^ (2 : ℕ) ≤ 12 * E := by
    calc
      _ ≤ (3 * x ^ (13 / 20 : ℝ)) * (2 * Real.log x) ^ (2 : ℕ) :=
        mul_le_mul hqdiv (pow_le_pow_left₀ hL0 hL _) (sq_nonneg _) (by positivity)
      _ = _ := by dsimp [E]; ring
  have hquarter : q ^ (1 / 4 : ℝ) ≤ 3 * x ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (3 * x) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hq0.le hqle (by norm_num)
      _ = 3 ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans_eq (Real.rpow_one 3)
  have hsmallx : Real.log x ≤ x ^ (1 / 20 : ℝ) := by
    simpa only [Real.norm_of_nonneg hxlog, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] using hlogsmall
  have hvertical : q ^ (1 / 4 : ℝ) * H * L ^ (3 : ℕ) ≤ 48 * E := by
    calc
      _ ≤ ((3 * x ^ (1 / 4 : ℝ)) * (2 * height x)) * (2 * Real.log x) ^ (3 : ℕ) :=
        mul_le_mul (mul_le_mul hquarter hHle hH0.le (by positivity)) (pow_le_pow_left₀ hL0 hL _)
          (by positivity) (by positivity)
      _ = 48 * ((x ^ (1 / 4 : ℝ) * height x) * (Real.log x ^ (2 : ℕ) * Real.log x)) := by ring
      _ ≤ 48 * ((x ^ (1 / 4 : ℝ) * height x) * (Real.log x ^ (2 : ℕ) * x ^ (1 / 20 : ℝ))) := by
        gcongr
      _ = _ := by
        dsimp [E, height]
        rw [show (13 / 20 : ℝ) = (1 / 4 : ℝ) + 7 / 20 + 1 / 20 by norm_num,
          Real.rpow_add hx0, Real.rpow_add hx0]
        ring
  have h := hbound (height x) hT H hH.1 hSep q hq
  apply h.trans
  change K * ((q / H) * L ^ (2 : ℕ) + q ^ (1 / 4 : ℝ) * H * L ^ (3 : ℕ)) ≤ (60 * K) * E
  calc
    _ ≤ K * (12 * E + 48 * E) := mul_le_mul_of_nonneg_left (add_le_add hhorizontal hvertical) hK.le
    _ = _ := by ring

private lemma separatedContourFormula_of_zetaContour (hF : ZetaContourEstimate) :
    SeparatedContourFormula := by
  intro c hc
  obtain ⟨A, hA, hmain⟩ := hF c hc
  obtain ⟨K, Q, hK, hkernel⟩ := kernelErrorWeight_halfInteger
  let B := (A + 24 * K) / (2 * Real.pi)
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 4 (Q + 1)), hmain] with x hx hf
  intro H hH hs n hn
  let q := (n : ℝ) + 1 / 2
  let E := x ^ (13 / 20 : ℝ) * Real.log x ^ (2 : ℕ)
  let S := 2 * (Real.pi : ℂ) * I
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith only [hx4]
  have hx1 : 1 ≤ x := by linarith only [hx4]
  have hq3 : 3 ≤ q := by linarith only [hx4, show x - 1 ≤ q from hn.1]
  have hq0 : 0 < q := by linarith only [hq3]
  have hqQ : Q ≤ q := by linarith only [(le_max_right _ _).trans hx, show x - 1 ≤ q from hn.1]
  have hc1 : 1 < perronLine q := by
    dsimp [perronLine]
    exact lt_add_of_pos_right _ (inv_pos.mpr (Real.log_pos (by linarith only [hq3])))
  have hT0 : 0 < height x := rpow_pos_of_pos hx0 _
  have hH0 := hT0.trans_le hH.1
  have hgap : gap x ≤ x :=
    (rpow_le_rpow_of_exponent_le hx1 (by norm_num : (2 / 3 : ℝ) ≤ 1)).trans_eq (rpow_one x)
  have hqle : q ≤ 3 * x := by linarith only [show q ≤ x + gap x + 1 from hn.2, hgap, hx4]
  have hlog : Real.log q ≤ 2 * Real.log x := by
    have hq2 : q ≤ x ^ (2 : ℕ) := by
      nlinarith only [hqle, mul_nonneg hx0.le (show 0 ≤ x - 3 by linarith only [hx4])]
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hq0 hq2
  have hqdiv : q / H ≤ 3 * x ^ (13 / 20 : ℝ) := by
    calc
      _ ≤ q / height x := div_le_div_of_nonneg_left hq0.le hT0 hH.1
      _ ≤ (3 * x) / height x := div_le_div_of_nonneg_right hqle hT0.le
      _ = _ := by
        rw [mul_div_assoc]
        congr 1
        calc
          _ = x ^ (1 : ℝ) / x ^ (7 / 20 : ℝ) := by rw [rpow_one, height]
          _ = _ := by rw [← rpow_sub hx0]; norm_num
  obtain ⟨hSummable, hKq⟩ := hkernel n hqQ
  have hperron := norm_zetaVertical_sub_psi_le_error (q := q) hq0 hc1 hH0
    (halfInteger_ne_nat n) hSummable
  have hpow : Real.log q ^ (2 : ℕ) ≤ 4 * Real.log x ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ (Real.log_nonneg (by linarith only [hq3])) hlog 2
    exact h.trans_eq (by ring)
  have hPer : ‖zetaVertical q (perronLine q) H - S * (psi q : ℂ)‖ ≤ (24 * K) * E := by
    apply hperron.trans
    calc
      _ ≤ (2 / H) * (K * q * Real.log q ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hKq (by positivity)
      _ = (2 * K) * ((q / H) * Real.log q ^ (2 : ℕ)) := by ring
      _ ≤ (2 * K) * ((3 * x ^ (13 / 20 : ℝ)) * (4 * Real.log x ^ (2 : ℕ))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hqdiv hpow (sq_nonneg _) (by positivity)) (by positivity)
      _ = _ := by dsimp [E]; ring
  let a := zetaVertical q (perronLine q) H
  have hContour : ‖a - S * ((q : ℂ) - zeroSum H q)‖ ≤ A * E := hf H hH hs n hn
  have he : S * (((psi q - q : ℝ) : ℂ) + zeroSum H q) =
      (a - S * ((q : ℂ) - zeroSum H q)) - (a - S * (psi q : ℂ)) := by
    push_cast
    ring
  have h := (norm_sub_le (a - S * ((q : ℂ) - zeroSum H q)) (a - S * (psi q : ℂ))).trans
    (add_le_add hContour hPer)
  rw [← he, norm_mul] at h
  have hS : ‖S‖ = 2 * Real.pi := by
    dsimp [S]
    simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hS] at h
  change ‖((psi q - q : ℝ) : ℂ) + zeroSum H q‖ ≤ B * E
  rw [show B * E = (A * E + 24 * K * E) / (2 * Real.pi) by dsimp [B]; ring]
  apply (le_div_iff₀ (show 0 < 2 * Real.pi by positivity)).mpr
  linarith only [h, mul_comm (2 * Real.pi)]

end

end

end OMA.Erdos687ShortInterval

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R3.H1 := by
  have estimates :
      OMA.Erdos687ShortInterval.WeylZetaEstimate ∧
      OMA.Erdos687ShortInterval.ZetaOscillationEstimate := by
    sorry
  exact OMA.Erdos687ShortInterval.eventually_prime_of_zeta_estimates_with_density (by norm_num) (by norm_num)
    (OMA.Erdos687ShortInterval.truncatedFormula_of_halfIntegers
      (OMA.Erdos687ShortInterval.halfIntegerFormula_of_selectedHeight
        (OMA.Erdos687ShortInterval.selectedHeightFormula_of_separatedContour
          (OMA.Erdos687ShortInterval.separatedContourFormula_of_zetaContour OMA.Erdos687ShortInterval.zetaContourEstimate_proved))))
    (OMA.Erdos687ShortInterval.density_of_right_with (by norm_num)
      (OMA.Erdos687ShortInterval.rightDensity_of_separated_with
        (OMA.Erdos687ShortInterval.separatedDensity_of_shell (by norm_num)
          (OMA.Erdos687ShortInterval.separatedShellDensity_of_detector
            OMA.Erdos687ShortInterval.detector_tail_moment
            (OMA.Erdos687ShortInterval.detector_left_moment_of_weyl estimates.1)))))
    (OMA.Erdos687ShortInterval.zeroFree_of_scaledLogDerivative
      (OMA.Erdos687ShortInterval.scaledLogDerivative_of_zetaGrowth
        (OMA.Erdos687ShortInterval.zetaGrowthNearOne_of_oscillation estimates.2)))

