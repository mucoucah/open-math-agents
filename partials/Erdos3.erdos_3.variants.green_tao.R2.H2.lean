import OMAReductions.R_Erdos3_erdos_3_variants_green_tao_R2
import Mathlib

/-! Finite cube sums and correlations of the balanced function. -/

open scoped BigOperators ComplexConjugate Pointwise

namespace Erdos3Structured

private def interval (N : ℕ) : Finset ℤ := Finset.Icc 1 N

private def shifts (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

private noncomputable def density (N : ℕ) (S : Finset ℕ) : ℝ := (S.card : ℝ) / N

private noncomputable def balanced (N : ℕ) (S : Finset ℕ) (x : ℤ) : ℝ :=
  (if 0 < x ∧ x.toNat ∈ S then 1 else 0) -
    (if 0 < x ∧ x ≤ (N : ℤ) then density N S else 0)

private def face (f : ℤ → ℝ) (a b x : ℤ) : ℝ :=
  f x * f (x + a) * f (x + b) * f (x + a + b)

private noncomputable def cubeSum (N : ℕ) (f : ℤ → ℝ) : ℝ :=
  ∑ x ∈ interval N, ∑ a ∈ shifts N, ∑ b ∈ shifts N, ∑ e ∈ shifts N,
    f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
      f (x + b + e) * f (x + a + b + e)

private lemma density_mem_unitInterval {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) : 0 ≤ density N S ∧ density N S ≤ 1 := by
  refine ⟨by unfold density; positivity, ?_⟩
  have hc : S.card ≤ N := (Finset.card_le_card hS).trans_eq (by simp)
  by_cases hN : N = 0
  · simp [density, hN]
  · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)).mpr (by exact_mod_cast hc)

private lemma balanced_eq_zero {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    {x : ℤ} (hx : x ∉ interval N) : balanced N S x = 0 := by
  have hord : ¬ (0 < x ∧ x ≤ (N : ℤ)) := by
    unfold interval at hx
    simp only [Finset.mem_Icc] at hx
    omega
  have hmem : ¬ (0 < x ∧ x.toNat ∈ S) := by
    rintro ⟨hxpos, hxS⟩
    have hxN := (Finset.mem_Icc.mp (hS hxS)).2
    exact hord ⟨hxpos, by omega⟩
  simp [balanced, hord, hmem]

private lemma abs_balanced_le_one {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (x : ℤ) : |balanced N S x| ≤ 1 := by
  obtain ⟨hd₀, hd₁⟩ := density_mem_unitInterval hS
  rw [abs_le]
  unfold balanced
  split_ifs <;> constructor <;> linarith

private lemma sum_translate_eq {N : ℕ} {g : ℤ → ℝ}
    (hg : ∀ y ∉ interval N, g y = 0) {x : ℤ} (hx : x ∈ interval N) :
    ∑ e ∈ shifts N, g (x + e) = ∑ y ∈ interval N, g y := by
  simp only [interval, Finset.mem_Icc] at hx
  refine Finset.sum_bij_ne_zero (fun e _ _ => x + e) ?_ ?_ ?_ ?_
  · intro e he h
    exact by_contra fun hy => h (hg _ hy)
  · intro e₁ _ _ e₂ _ _ h
    omega
  · intro y hy h
    have hy' : 1 ≤ y ∧ y ≤ (N : ℤ) := Finset.mem_Icc.mp hy
    refine ⟨y - x, ?_, ?_, by omega⟩
    · unfold shifts
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · simpa only [add_sub_cancel] using h
  · intros
    rfl

private lemma cubeSum_eq_sq {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) :
    cubeSum N f = ∑ a ∈ shifts N, ∑ b ∈ shifts N, (∑ x ∈ interval N, face f a b x) ^ 2 := by
  unfold cubeSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hg : ∀ y ∉ interval N, face f a b y = 0 := by
    intro y hy
    simp [face, hf y hy]
  rw [← sum_translate_eq hg hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [face, add_right_comm (x + _) e, add_right_comm x e]
  ring

private lemma cubeSum_nonneg {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) : 0 ≤ cubeSum N f := by
  rw [cubeSum_eq_sq hf]
  positivity

private noncomputable def derivativeEnergy (N : ℕ) (f : ℤ → ℝ) (a : ℤ) : ℝ :=
  ∑ b ∈ shifts N, (∑ x ∈ interval N, face f a b x) ^ 2

private lemma card_interval (N : ℕ) : (interval N).card = N := by
  simp [interval, Int.card_Icc]

private lemma card_shifts (N : ℕ) : (shifts N).card = 2 * N + 1 := by
  simp only [shifts, Int.card_Icc]
  omega

private lemma abs_sum_face_le {N : ℕ} {f : ℤ → ℝ} (habs : ∀ x, |f x| ≤ 1)
    (a b : ℤ) : |∑ x ∈ interval N, face f a b x| ≤ N := by
  calc
    _ ≤ ∑ x ∈ interval N, |face f a b x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ interval N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      simp only [face, abs_mul]
      calc
        _ ≤ (1 : ℝ) * 1 * 1 * 1 := by gcongr <;> apply habs
        _ = 1 := by norm_num
    _ = _ := by simp [card_interval]

private lemma derivativeEnergy_le {N : ℕ} {f : ℤ → ℝ} (habs : ∀ x, |f x| ≤ 1)
    (a : ℤ) : derivativeEnergy N f a ≤ (2 * (N : ℝ) + 1) * (N : ℝ) ^ 2 := by
  unfold derivativeEnergy
  calc
    _ ≤ ∑ _ ∈ shifts N, (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_sum_face_le habs a b) _
    _ = _ := by simp [card_shifts, Nat.cast_add, Nat.cast_mul]

private lemma card_filter_large_terms {ι : Type*} (D : Finset ι) (v : ι → ℝ)
    {u t : ℝ} (ht : 0 ≤ t) (hv : ∀ a ∈ D, v a ≤ u) :
    (∑ a ∈ D, v a) ≤
      ((D.filter (fun a => t ≤ v a)).card : ℝ) * u + (D.card : ℝ) * t := by
  classical
  calc
    _ ≤ ∑ a ∈ D, ((if t ≤ v a then u else 0) + t) := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs with h
      · linarith [hv a ha]
      · linarith
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_filter, Finset.sum_const]
      simp only [nsmul_eq_mul]

private lemma many_large_derivativeEnergies {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) (habs : ∀ x, |f x| ≤ 1)
    (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 ≤ δ) (hlarge : δ * (N : ℝ) ^ 4 ≤ cubeSum N f) :
    let D := (shifts N).filter (fun a => δ * (N : ℝ) ^ 3 / 6 ≤ derivativeEnergy N f a)
    δ * (N : ℝ) / 6 ≤ (D.card : ℝ) := by
  dsimp only
  let D := (shifts N).filter (fun a => δ * (N : ℝ) ^ 3 / 6 ≤ derivativeEnergy N f a)
  change _ ≤ (D.card : ℝ)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hcount : ((shifts N).card : ℝ) ≤ 3 * (N : ℝ) := by
    push_cast [card_shifts]
    linarith
  have hbound : ∀ a ∈ shifts N, derivativeEnergy N f a ≤ 3 * (N : ℝ) ^ 3 := by
    intro a _
    have hc : 2 * (N : ℝ) + 1 ≤ 3 * (N : ℝ) := by linarith
    calc
      _ ≤ _ := derivativeEnergy_le habs a
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = _ := by ring
  have htotal : δ * (N : ℝ) ^ 4 ≤ ∑ a ∈ shifts N, derivativeEnergy N f a := by
    simpa only [cubeSum_eq_sq hf, derivativeEnergy] using hlarge
  have hsplit := card_filter_large_terms (shifts N) (derivativeEnergy N f)
    (u := 3 * (N : ℝ) ^ 3) (t := δ * (N : ℝ) ^ 3 / 6)
    (by positivity) hbound
  have hsmall := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ δ * (N : ℝ) ^ 3 / 6 by positivity)
  have hmul : (δ * (N : ℝ) / 6) * (3 * (N : ℝ) ^ 3) ≤
      (D.card : ℝ) * (3 * (N : ℝ) ^ 3) := by
    change _ ≤ (D.card : ℝ) * _ + _ at hsplit
    linarith only [htotal, hsplit, hsmall]
  exact le_of_mul_le_mul_right hmul (by positivity)


section Fourier

variable {M : ℕ} [NeZero M]

private noncomputable def fourier (g : ZMod M → ℝ) (k : ZMod M) : ℂ :=
  ZMod.dft (fun x => (g x : ℂ)) k

private noncomputable def cyclicCorrelation (g : ZMod M → ℝ) (b : ZMod M) : ℝ :=
  ∑ x, g x * g (x + b)

private lemma sum_dft_mul (g h : ZMod M → ℂ) :
    ∑ k, ZMod.dft g k * ZMod.dft h (-k) = (M : ℂ) * ∑ x, g x * h x := by
  classical
  calc
    _ = ∑ k : ZMod M, ∑ x : ZMod M,
        g x * (ZMod.stdAddChar (-(x * k)) * ZMod.dft h (-k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [ZMod.dft_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      simp only [smul_eq_mul]
      ring
    _ = ∑ x : ZMod M, g x * ZMod.dft (fun k => ZMod.dft h (-k)) x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [ZMod.dft_apply, Finset.mul_sum]
      simp only [smul_eq_mul, mul_comm _ x]
    _ = _ := by
      rw [ZMod.dft_comp_neg, ZMod.dft_dft, Finset.mul_sum]
      simp only [neg_neg, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring

private lemma fourier_neg (g : ZMod M → ℝ) (k : ZMod M) :
    fourier g (-k) = star (fourier g k) := by
  unfold fourier
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [smul_eq_mul, map_sum, map_mul, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [mul_neg, neg_neg]
  calc
    _ = ZMod.stdAddChar (-(-(x * k))) := by rw [neg_neg]
    _ = _ := by
      rw [AddChar.map_neg_eq_inv]
      exact Complex.inv_eq_conj (Circle.norm_coe _)

private lemma fourier_pair (g : ZMod M → ℝ) (k : ZMod M) :
    fourier g k * fourier g (-k) = ((‖fourier g k‖ ^ 2 : ℝ) : ℂ) := by
  rw [fourier_neg]
  simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' (fourier g k)

private lemma fourier_cyclicCorrelation (g : ZMod M → ℝ) (k : ZMod M) :
    fourier (cyclicCorrelation g) k = fourier g k * fourier g (-k) := by
  classical
  change ZMod.dft (fun b => ((cyclicCorrelation g b : ℝ) : ℂ)) k = _
  simp only [ZMod.dft_apply, cyclicCorrelation, fourier, Complex.ofReal_sum,
    Complex.ofReal_mul, smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun b => ?_
  change ZMod.stdAddChar (-(b * k)) * ((g x : ℂ) * (g (x + b) : ℂ)) =
    (ZMod.stdAddChar (-((x + b) * k)) * (g (x + b) : ℂ)) *
      (ZMod.stdAddChar (-(x * -k)) * (g x : ℂ))
  calc
    _ = (ZMod.stdAddChar (-((x + b) * k)) * ZMod.stdAddChar (-(x * -k))) *
        ((g x : ℂ) * (g (x + b) : ℂ)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = _ := by ring

private lemma sum_sq_fourier (g : ZMod M → ℝ) :
    ∑ k, ‖fourier g k‖ ^ 2 = (M : ℝ) * ∑ x, g x ^ 2 := by
  have h := sum_dft_mul (fun x => (g x : ℂ)) (fun x => (g x : ℂ))
  change ∑ k, fourier g k * fourier g (-k) = _ at h
  simp_rw [fourier_pair, ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_natCast,
    ← sq] at h
  exact_mod_cast h

private lemma sum_fourth_fourier (g : ZMod M → ℝ) :
    ∑ k, ‖fourier g k‖ ^ 4 = (M : ℝ) * ∑ b, cyclicCorrelation g b ^ 2 := by
  rw [← sum_sq_fourier]
  apply Finset.sum_congr rfl
  intro k _
  rw [fourier_cyclicCorrelation, fourier_pair, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  ring

private lemma exists_large_fourier (g : ZMod M → ℝ) {u t : ℝ} (hu : 0 < u)
    (h₂ : ∑ x, g x ^ 2 ≤ u) (h₄ : t * u ≤ ∑ b, cyclicCorrelation g b ^ 2) :
    ∃ k, t ≤ ‖fourier g k‖ ^ 2 := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod M))
    (fun k => ‖fourier g k‖ ^ 2) Finset.univ_nonempty
  refine ⟨k, ?_⟩
  by_cases ht : t ≤ 0
  · exact ht.trans (sq_nonneg _)
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hcompare : ∑ j, ‖fourier g j‖ ^ 4 ≤ ‖fourier g k‖ ^ 2 * ∑ j, ‖fourier g j‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq]
    exact mul_le_mul_of_nonneg_right (hk j hj) (sq_nonneg _)
  rw [sum_fourth_fourier, sum_sq_fourier] at hcompare
  have hc := (mul_le_mul_of_nonneg_left h₄ hM.le).trans
    (hcompare.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₂ hM.le) (sq_nonneg _)))
  have heq : t * ((M : ℝ) * u) ≤ ‖fourier g k‖ ^ 2 * ((M : ℝ) * u) := by
    linarith only [hc]
  exact le_of_mul_le_mul_right heq (mul_pos hM hu)

end Fourier

section Periodic

private noncomputable def periodize (N : ℕ) (g : ℤ → ℝ) (z : ZMod (2 * N + 1)) : ℝ :=
  g (z.val : ℤ)

private lemma val_intCast_small {N : ℕ} {x : ℤ} (h₀ : 0 ≤ x) (h₁ : x < 2 * (N : ℤ) + 1) :
    (((x : ZMod (2 * N + 1)).val : ℕ) : ℤ) = x := by
  rw [ZMod.val_intCast, Int.emod_eq_of_lt h₀ (by push_cast; exact h₁)]

private lemma periodize_intCast {N : ℕ} {g : ℤ → ℝ} (hg : ∀ x ∉ interval N, g x = 0)
    {x : ℤ} (hl : 1 - (N : ℤ) ≤ x) (hr : x ≤ 2 * (N : ℤ)) :
    periodize N g (x : ZMod (2 * N + 1)) = g x := by
  by_cases h₀ : 0 ≤ x
  · simp only [periodize, val_intCast_small h₀ (by omega : x < 2 * (N : ℤ) + 1)]
  let y := x + (2 * (N : ℤ) + 1)
  have hxy : (x : ZMod (2 * N + 1)) = (y : ZMod (2 * N + 1)) := by
    have hcast : (((2 * N + 1 : ℕ) : ℤ) : ZMod (2 * N + 1)) = 0 := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_self (2 * N + 1)
    have hy : y = x + ((2 * N + 1 : ℕ) : ℤ) := by rfl
    rw [hy, Int.cast_add, hcast, add_zero]
  have hy₀ : (N : ℤ) < y := by dsimp [y]; omega
  have hy₁ : y < 2 * (N : ℤ) + 1 := by dsimp [y]; omega
  rw [hxy, periodize, val_intCast_small (by omega : 0 ≤ y) hy₁]
  have hy : y ∉ interval N := by simp only [interval, Finset.mem_Icc]; omega
  have hx : x ∉ interval N := by simp only [interval, Finset.mem_Icc]; omega
  rw [hg y hy, hg x hx]

private lemma sum_zmod_of_val_support {A : Type*} [AddCommMonoid A] {N : ℕ}
    (G : ZMod (2 * N + 1) → A) (hG : ∀ z, (z.val : ℤ) ∉ interval N → G z = 0) :
    ∑ z, G z = ∑ x ∈ interval N, G (x : ZMod (2 * N + 1)) := by
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => (x : ZMod (2 * N + 1))) ?_ ?_ ?_ ?_
  · simp
  · intro x hx _ y hy _ h
    have hx' : 1 ≤ x ∧ x ≤ (N : ℤ) := Finset.mem_Icc.mp hx
    have hy' : 1 ≤ y ∧ y ≤ (N : ℤ) := Finset.mem_Icc.mp hy
    have hval := congrArg (fun z : ZMod (2 * N + 1) => (z.val : ℤ)) h
    simpa only [val_intCast_small (by omega : 0 ≤ x) (by omega : x < 2 * (N : ℤ) + 1),
      val_intCast_small (by omega : 0 ≤ y) (by omega : y < 2 * (N : ℤ) + 1)] using hval
  · intro z _ hz
    have hcast : ((z.val : ℤ) : ZMod (2 * N + 1)) = z := by simp
    refine ⟨(z.val : ℤ), by_contra fun hz' => hz (hG z hz'), ?_, hcast⟩
    simpa only [hcast] using hz
  · intros
    rfl

private lemma shiftCast_inj {N : ℕ} {b c : ℤ} (hb : b ∈ shifts N) (hc : c ∈ shifts N)
    (h : (b : ZMod (2 * N + 1)) = (c : ZMod (2 * N + 1))) : b = c := by
  have hb' : -(N : ℤ) ≤ b ∧ b ≤ (N : ℤ) := Finset.mem_Icc.mp hb
  have hc' : -(N : ℤ) ≤ c ∧ c ≤ (N : ℤ) := Finset.mem_Icc.mp hc
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub b c (2 * N + 1)).mp h
  have hz : c - b = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by omega)
  omega

private lemma sum_zmod_eq_sum_shifts {A : Type*} [AddCommMonoid A] {N : ℕ}
    (G : ZMod (2 * N + 1) → A) :
    ∑ z, G z = ∑ b ∈ shifts N, G (b : ZMod (2 * N + 1)) := by
  symm
  refine Finset.sum_bij (fun b _ => (b : ZMod (2 * N + 1))) ?_ ?_ ?_ ?_
  · simp
  · exact fun _ hb _ hc h => shiftCast_inj hb hc h
  · intro z _
    have hz := z.val_lt
    by_cases h : z.val ≤ N
    · exact ⟨(z.val : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
    · refine ⟨(z.val : ℤ) - ((2 * N + 1 : ℕ) : ℤ), ?_, ?_⟩
      · apply Finset.mem_Icc.mpr
        push_cast
        omega
      · rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self, sub_zero,
          ZMod.natCast_zmod_val]
  · intros
    rfl

private lemma cyclicCorrelation_periodize {N : ℕ} {g : ℤ → ℝ} (hg : ∀ x ∉ interval N, g x = 0)
    {b : ℤ} (hb : b ∈ shifts N) :
    cyclicCorrelation (periodize N g) (b : ZMod (2 * N + 1)) =
      ∑ x ∈ interval N, g x * g (x + b) := by
  unfold cyclicCorrelation
  rw [sum_zmod_of_val_support _ (fun z hz => by rw [show periodize N g z = 0 from hg _ hz, zero_mul])]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : 1 ≤ x ∧ x ≤ (N : ℤ) := Finset.mem_Icc.mp hx
  have hb' : -(N : ℤ) ≤ b ∧ b ≤ (N : ℤ) := Finset.mem_Icc.mp hb
  rw [← Int.cast_add, periodize_intCast hg (by omega : 1 - (N : ℤ) ≤ x)
    (by omega : x ≤ 2 * (N : ℤ)), periodize_intCast hg (by omega) (by omega)]

private lemma derivativeEnergy_periodize {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) (a : ℤ) :
    derivativeEnergy N f a =
      ∑ b, cyclicCorrelation (periodize N (fun x => f x * f (x + a))) b ^ 2 := by
  rw [sum_zmod_eq_sum_shifts]
  unfold derivativeEnergy
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [cyclicCorrelation_periodize (fun x hx => by simp [hf x hx]) hb]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold face
  rw [show x + b + a = x + a + b by omega]
  ring

private lemma sq_sum_periodize_le {N : ℕ} {g : ℤ → ℝ} (hg : ∀ x ∉ interval N, g x = 0)
    (habs : ∀ x, |g x| ≤ 1) :
    ∑ z, periodize N g z ^ 2 ≤ (N : ℝ) := by
  rw [sum_zmod_of_val_support _ (fun z hz => by rw [show periodize N g z = 0 from hg _ hz, zero_pow (by decide)])]
  calc
    _ ≤ ∑ _ ∈ interval N, (1 : ℝ) := by
      refine Finset.sum_le_sum fun x hx => ?_
      have hx' : 1 ≤ x ∧ x ≤ (N : ℤ) := Finset.mem_Icc.mp hx
      rw [periodize_intCast hg (by omega) (by omega), ← sq_abs, ← one_pow 2]
      exact pow_le_pow_left₀ (abs_nonneg _) (habs x) _
    _ = _ := by simp [card_interval]

private lemma fourier_periodize {N : ℕ} {g : ℤ → ℝ} (hg : ∀ x ∉ interval N, g x = 0)
    (k : ZMod (2 * N + 1)) :
    fourier (periodize N g) k =
      ∑ x ∈ interval N, ZMod.stdAddChar (-((x : ZMod (2 * N + 1)) * k)) * (g x : ℂ) := by
  unfold fourier
  rw [ZMod.dft_apply, sum_zmod_of_val_support _ (fun z hz => by rw [show periodize N g z = 0 from hg _ hz, Complex.ofReal_zero, smul_zero])]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : 1 ≤ x ∧ x ≤ (N : ℤ) := Finset.mem_Icc.mp hx
  rw [periodize_intCast hg (by omega) (by omega), smul_eq_mul]

private lemma exists_large_derivative_fourier {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) (habs : ∀ x, |f x| ≤ 1)
    (hN : 1 ≤ N) {a : ℤ} {δ : ℝ} (ha : δ * (N : ℝ) ^ 3 / 6 ≤ derivativeEnergy N f a) :
    ∃ k : ZMod (2 * N + 1),
      δ * (N : ℝ) ^ 2 / 6 ≤
        ‖∑ x ∈ interval N, ZMod.stdAddChar (-((x : ZMod (2 * N + 1)) * k)) *
          ((f x : ℂ) * (f (x + a) : ℂ))‖ ^ 2 := by
  let g : ℤ → ℝ := fun x => f x * f (x + a)
  have hg : ∀ x ∉ interval N, g x = 0 := by
    intro x hx
    simp [g, hf x hx]
  have hgabs (x : ℤ) : |g x| ≤ 1 := by
    dsimp only [g]
    rw [abs_mul]
    calc
      _ ≤ (1 : ℝ) * 1 := by gcongr <;> apply habs
      _ = 1 := by norm_num
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have henergy : (δ * (N : ℝ) ^ 2 / 6) * (N : ℝ) ≤
      ∑ b, cyclicCorrelation (periodize N g) b ^ 2 := by
    rw [← derivativeEnergy_periodize hf a]
    linarith only [ha]
  obtain ⟨k, hk⟩ := exists_large_fourier (periodize N g) hpos (sq_sum_periodize_le hg hgabs) henergy
  refine ⟨k, ?_⟩
  simpa only [fourier_periodize hg, g, Complex.ofReal_mul] using hk

private noncomputable def cyclicDerivative {M : ℕ} (g : ZMod M → ℝ) (a : ZMod M)
    (z : ZMod M) : ℝ := g z * g (z + a)

private lemma periodize_derivative {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) {a : ℤ} (ha : a ∈ shifts N) :
    periodize N (fun x => f x * f (x + a)) =
      cyclicDerivative (periodize N f) (a : ZMod (2 * N + 1)) := by
  funext z
  change f (z.val : ℤ) * f ((z.val : ℤ) + a) =
    f (z.val : ℤ) * periodize N f (z + (a : ZMod (2 * N + 1)))
  by_cases hz : (z.val : ℤ) ∈ interval N
  · congr 1
    have hz' : 1 ≤ (z.val : ℤ) ∧ (z.val : ℤ) ≤ (N : ℤ) := Finset.mem_Icc.mp hz
    have ha' : -(N : ℤ) ≤ a ∧ a ≤ (N : ℤ) := Finset.mem_Icc.mp ha
    have heq : z + (a : ZMod (2 * N + 1)) =
        (((z.val : ℤ) + a : ℤ) : ZMod (2 * N + 1)) := by
      rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [heq, periodize_intCast hf (by omega) (by omega)]
  · rw [hf _ hz, zero_mul, zero_mul]

private lemma large_cube_has_fourier_graph {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) (habs : ∀ x, |f x| ≤ 1)
    (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 ≤ δ) (hlarge : δ * (N : ℝ) ^ 4 ≤ cubeSum N f) :
    ∃ H : Finset (ZMod (2 * N + 1)), ∃ ξ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
      δ * (N : ℝ) / 6 ≤ (H.card : ℝ) ∧
        ∀ a ∈ H, Real.sqrt (δ / 6) * (N : ℝ) ≤
          ‖fourier (cyclicDerivative (periodize N f) a) (ξ a)‖ := by
  classical
  let D := (shifts N).filter (fun a => δ * (N : ℝ) ^ 3 / 6 ≤ derivativeEnergy N f a)
  let H := D.image (fun a : ℤ => (a : ZMod (2 * N + 1)))
  have hcard : H.card = D.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb h
    exact shiftCast_inj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h
  have hcoeff (a : ZMod (2 * N + 1)) (ha : a ∈ H) :
      ∃ k, Real.sqrt (δ / 6) * (N : ℝ) ≤ ‖fourier (cyclicDerivative (periodize N f) a) k‖ := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hbmem, hbenergy⟩ := Finset.mem_filter.mp hb
    obtain ⟨k, hk⟩ := exists_large_derivative_fourier hf habs hN hbenergy
    refine ⟨k, ?_⟩
    let g := fun x : ℤ => f x * f (x + b)
    have hg : ∀ x ∉ interval N, g x = 0 := fun x hx => by simp [g, hf x hx]
    have hchar := fourier_periodize hg k
    rw [periodize_derivative hf hbmem] at hchar
    simp only [g, Complex.ofReal_mul] at hchar
    rw [← hchar] at hk
    have hsq : (Real.sqrt (δ / 6) * (N : ℝ)) ^ 2 = δ * (N : ℝ) ^ 2 / 6 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp (hsq.trans_le hk)
  let ξ := fun a => if ha : a ∈ H then (hcoeff a ha).choose else 0
  refine ⟨H, ξ, ?_, ?_⟩
  · rw [hcard]
    exact many_large_derivativeEnergies hf habs hN hδ hlarge
  · intro a ha
    simpa only [ξ, dif_pos ha] using (hcoeff a ha).choose_spec

end Periodic


section Box

variable {ι : Type*} [Fintype ι]

private lemma norm_sum_mul_sq_le {κ : Type*} [Fintype κ] (a b : κ → ℂ) :
    ‖∑ i, a i * b i‖ ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖b i‖ ^ 2 := by
  have h := norm_sum_le Finset.univ (fun i => a i * b i)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

private lemma sum_sq_of_norm_le_one (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ∑ i, ‖a i‖ ^ 2 ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _ : ι, (1 : ℝ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (ha i) 2
    _ = _ := by simp

private lemma complex_ofReal_sq_norm (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.ofReal_pow, Complex.mul_conj']

private noncomputable def boxSum (W : ι → ι → ℂ) : ℂ :=
  ∑ x, ∑ x', ∑ y, ∑ y', (W x y * conj (W x' y)) * (conj (W x y') * W x' y')

private lemma boxSum_eq (W : ι → ι → ℂ) :
    boxSum W = ((∑ x, ∑ x', ‖∑ y, W x y * conj (W x' y)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [boxSum, Complex.ofReal_sum, complex_ofReal_sq_norm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]

private lemma box_cauchySchwarz (u v : ι → ℂ) (W : ι → ι → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ y, ‖v y‖ ≤ 1) :
    ‖∑ y, v y * ∑ x, u x * W x y‖ ^ 4 ≤ (Fintype.card ι : ℝ) ^ 4 * ‖boxSum W‖ := by
  let X : ι → ℂ := fun y => ∑ x, u x * W x y
  let A : ℝ := ∑ y, ‖X y‖ ^ 2
  let U : ι × ι → ℂ := fun p => u p.1 * conj (u p.2)
  let Y : ι × ι → ℂ := fun p => ∑ y, W p.1 y * conj (W p.2 y)
  have hfirst : ‖∑ y, v y * X y‖ ^ 2 ≤ (Fintype.card ι : ℝ) * A :=
    (norm_sum_mul_sq_le v X).trans
      (mul_le_mul_of_nonneg_right (sum_sq_of_norm_le_one v hv) (by positivity))
  have hA : (A : ℂ) = ∑ p, U p * Y p := by
    simp only [A, X, U, Y, Complex.ofReal_sum, complex_ofReal_sq_norm, Fintype.sum_prod_type,
      map_sum, map_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hU : ∀ p : ι × ι, ‖U p‖ ≤ 1 := by
    intro p
    simp only [U, norm_mul, Complex.norm_conj]
    calc
      _ ≤ (1 : ℝ) * 1 := by gcongr <;> apply hu
      _ = 1 := by norm_num
  have hY : (∑ p, ‖Y p‖ ^ 2) = ‖boxSum W‖ := by
    rw [boxSum_eq, Fintype.sum_prod_type, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsecond : A ^ 2 ≤ (Fintype.card ι : ℝ) ^ 2 * ‖boxSum W‖ := by
    have h := norm_sum_mul_sq_le U Y
    rw [← hA, Complex.norm_real, Real.norm_of_nonneg (by positivity), hY] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    simpa only [Fintype.card_prod, Nat.cast_mul, sq] using sum_sq_of_norm_le_one U hU
  change ‖∑ y, v y * X y‖ ^ 4 ≤ _
  calc
    _ = (‖∑ y, v y * X y‖ ^ 2) ^ 2 := by ring
    _ ≤ ((Fintype.card ι : ℝ) * A) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ = (Fintype.card ι : ℝ) ^ 2 * A ^ 2 := mul_pow _ _ _
    _ ≤ (Fintype.card ι : ℝ) ^ 2 * ((Fintype.card ι : ℝ) ^ 2 * ‖boxSum W‖) := by gcongr
    _ = _ := by ring

end Box

section Phase

variable {M : ℕ} [NeZero M]

private lemma conj_stdAddChar (z : ZMod M) :
    conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (Circle.norm_coe _)).symm

private lemma sum_stdAddChar_mul_of_ne_zero {v : ZMod M} (hv : v ≠ 0) :
    ∑ y, ZMod.stdAddChar (y * v) = 0 := by
  simp_rw [mul_comm _ v]
  exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M hv)

private noncomputable def phaseKernel (H : Finset (ZMod M)) (ξ : ZMod M → ZMod M)
    (w : ZMod M → ℂ) (x y : ZMod M) : ℂ :=
  if x - y ∈ H then w (x - y) * ZMod.stdAddChar (-(y * ξ (x - y))) else 0

private def phaseQuad (H : Finset (ZMod M)) (ξ : ZMod M → ZMod M) (h s t : ZMod M) : Prop :=
  h ∈ H ∧ h + s ∈ H ∧ h - t ∈ H ∧ h + s - t ∈ H ∧
    ξ h + ξ (h + s - t) = ξ (h + s) + ξ (h - t)

private instance decidablePhaseQuad (H : Finset (ZMod M)) (ξ : ZMod M → ZMod M)
    (h s t : ZMod M) : Decidable (phaseQuad H ξ h s t) := by
  unfold phaseQuad
  infer_instance

private noncomputable def phaseParallelograms (H : Finset (ZMod M)) (ξ : ZMod M → ZMod M) :
    Finset (ZMod M × ZMod M × ZMod M) := by
  classical
  exact Finset.univ.filter (fun p => phaseQuad H ξ p.1 p.2.1 p.2.2)

private lemma phaseKernel_norm_le (H : Finset (ZMod M)) (ξ : ZMod M → ZMod M)
    (w : ZMod M → ℂ) (hw : ∀ h, ‖w h‖ ≤ 1) (x y : ZMod M) :
    ‖phaseKernel H ξ w x y‖ ≤ 1 := by
  unfold phaseKernel
  split_ifs
  · rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
    exact hw _
  · simp

private lemma norm_phase_line (H : Finset (ZMod M)) (ξ : ZMod M → ZMod M)
    (w : ZMod M → ℂ) (hw : ∀ h, ‖w h‖ ≤ 1) (h s t : ZMod M) :
    ‖∑ y, (phaseKernel H ξ w (h + y) y * conj (phaseKernel H ξ w (h + s + y) y)) *
        (conj (phaseKernel H ξ w (h + y) (t + y)) *
          phaseKernel H ξ w (h + s + y) (t + y))‖ ≤
      if phaseQuad H ξ h s t then (M : ℝ) else 0 := by
  classical
  let W := phaseKernel H ξ w
  let term := fun y => (W (h + y) y * conj (W (h + s + y) y)) *
    (conj (W (h + y) (t + y)) * W (h + s + y) (t + y))
  change ‖∑ y, term y‖ ≤ _
  have he₁ (y : ZMod M) : h + y - y = h := by abel
  have he₂ (y : ZMod M) : h + s + y - y = h + s := by abel
  have he₃ (y : ZMod M) : h + y - (t + y) = h - t := by abel
  have he₄ (y : ZMod M) : h + s + y - (t + y) = h + s - t := by abel
  by_cases he : phaseQuad H ξ h s t
  · rw [if_pos he]
    calc
      _ ≤ ∑ y, ‖term y‖ := norm_sum_le _ _
      _ ≤ ∑ _ : ZMod M, (1 : ℝ) := by
        refine Finset.sum_le_sum fun y _ => ?_
        simp only [term, norm_mul, Complex.norm_conj]
        calc
          _ ≤ (1 : ℝ) * 1 * (1 * 1) := by
            gcongr <;> exact phaseKernel_norm_le H ξ w hw _ _
          _ = 1 := by norm_num
      _ = _ := by simp [ZMod.card]
  rw [if_neg he]
  suffices hz : ∑ y, term y = 0 by rw [hz, norm_zero]
  by_cases hm : h ∈ H ∧ h + s ∈ H ∧ h - t ∈ H ∧ h + s - t ∈ H
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hm
    let v := ξ (h + s) + ξ (h - t) - ξ h - ξ (h + s - t)
    let c := w h * conj (w (h + s)) * (conj (w (h - t)) * w (h + s - t)) *
      ZMod.stdAddChar (t * (ξ (h - t) - ξ (h + s - t)))
    have hv : v ≠ 0 := by
      intro hv
      apply he
      refine ⟨h₁, h₂, h₃, h₄, ?_⟩
      change ξ (h + s) + ξ (h - t) - ξ h - ξ (h + s - t) = 0 at hv
      linear_combination -hv
    have hterm (y : ZMod M) : term y = c * ZMod.stdAddChar (y * v) := by
      simp only [term, W, phaseKernel, he₁, he₂, he₃, he₄, if_pos h₁, if_pos h₂, if_pos h₃,
        if_pos h₄, map_mul, conj_stdAddChar, neg_neg]
      calc
        _ = w h * conj (w (h + s)) * (conj (w (h - t)) * w (h + s - t)) *
            (ZMod.stdAddChar (-(y * ξ h)) * ZMod.stdAddChar (y * ξ (h + s)) *
              ZMod.stdAddChar ((t + y) * ξ (h - t)) *
              ZMod.stdAddChar (-((t + y) * ξ (h + s - t)))) := by ring
        _ = _ := by
          dsimp only [c, v]
          conv_rhs => rw [mul_assoc]
          simp only [← AddChar.map_add_eq_mul]
          congr 2
          ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_stdAddChar_mul_of_ne_zero hv, mul_zero]
  · have hzero (y : ZMod M) : term y = 0 := by
      simp only [not_and_or] at hm
      rcases hm with h₁ | h₂ | h₃ | h₄ <;>
        simp [term, W, phaseKernel, *]
    simp only [hzero, Finset.sum_const_zero]

private lemma boxSum_reindex (W : ZMod M → ZMod M → ℂ) :
    boxSum W = ∑ h, ∑ s, ∑ t, ∑ y,
      (W (h + y) y * conj (W (h + s + y) y)) *
        (conj (W (h + y) (t + y)) * W (h + s + y) (t + y)) := by
  let T (x x' y y' : ZMod M) := (W x y * conj (W x' y)) * (conj (W x y') * W x' y')
  change (∑ x, ∑ x', ∑ y, ∑ y', T x x' y y') =
    ∑ h, ∑ s, ∑ t, ∑ y, T (h + y) (h + s + y) y (t + y)
  calc
    _ = ∑ y, ∑ x, ∑ x', ∑ y', T x x' y y' := by
      calc
        _ = ∑ x, ∑ y, ∑ x', ∑ y', T x x' y y' :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ = ∑ y, ∑ h, ∑ s, ∑ t, T (h + y) (h + s + y) y (t + y) := by
      apply Finset.sum_congr rfl
      intro y _
      symm
      refine Fintype.sum_equiv (Equiv.addRight y) _ _ fun h => ?_
      change (∑ s, ∑ t, T (h + y) (h + s + y) y (t + y)) =
        ∑ x', ∑ y', T (h + y) x' y y'
      refine Fintype.sum_equiv (Equiv.addLeft (h + y)) _ _ fun s => ?_
      change (∑ t, T (h + y) (h + s + y) y (t + y)) =
        ∑ y', T (h + y) (h + y + s) y y'
      rw [add_right_comm h s y]
      exact Fintype.sum_equiv (Equiv.addRight y) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_comm]

private lemma norm_box_phaseKernel_le (H : Finset (ZMod M)) (ξ : ZMod M → ZMod M)
    (w : ZMod M → ℂ) (hw : ∀ h, ‖w h‖ ≤ 1) :
    ‖boxSum (phaseKernel H ξ w)‖ ≤ (M : ℝ) * ((phaseParallelograms H ξ).card : ℝ) := by
  classical
  let W := phaseKernel H ξ w
  let T (h s t y : ZMod M) :=
    (W (h + y) y * conj (W (h + s + y) y)) *
      (conj (W (h + y) (t + y)) * W (h + s + y) (t + y))
  change ‖boxSum W‖ ≤ _
  rw [boxSum_reindex]
  change ‖∑ h, ∑ s, ∑ t, ∑ y, T h s t y‖ ≤ _
  calc
    _ ≤ ∑ h, ∑ s, ∑ t, ‖∑ y, T h s t y‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
      exact norm_sum_le _ _
    _ ≤ ∑ h, ∑ s, ∑ t, if phaseQuad H ξ h s t then (M : ℝ) else 0 := by
      exact Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun s _ =>
        Finset.sum_le_sum fun t _ => norm_phase_line H ξ w hw h s t
    _ = ∑ p : ZMod M × ZMod M × ZMod M,
        if phaseQuad H ξ p.1 p.2.1 p.2.2 then (M : ℝ) else 0 := by
      simp only [Fintype.sum_prod_type]
    _ = _ := by
      rw [← Finset.sum_filter]
      change (∑ p ∈ phaseParallelograms H ξ, (M : ℝ)) = _
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

private noncomputable def phaseGraph (H : Finset (ZMod M)) (ξ : ZMod M → ZMod M) :
    Finset (ZMod M × ZMod M) := H.image (fun h => (h, ξ h))

private lemma card_phaseParallelograms_le_addEnergy
    (H : Finset (ZMod M)) (ξ : ZMod M → ZMod M) :
    (phaseParallelograms H ξ).card ≤ (phaseGraph H ξ).addEnergy (phaseGraph H ξ) := by
  classical
  let pts := phaseGraph H ξ
  let point (h : ZMod M) := (h, ξ h)
  unfold Finset.addEnergy
  change _ ≤ ((pts ×ˢ pts) ×ˢ pts ×ˢ pts |>.filter
    (fun p => p.1.1 + p.2.1 = p.1.2 + p.2.2)).card
  refine Finset.card_le_card_of_injOn
    (fun (p : ZMod M × ZMod M × ZMod M) =>
      let h := p.1
      let s := p.2.1
      let t := p.2.2
      ((point h, point (h + s)), point (h + s - t), point (h - t))) ?_ ?_
  · rintro ⟨h, s, t⟩ hp
    change (h, s, t) ∈ phaseParallelograms H ξ at hp
    have hh : phaseQuad H ξ h s t := (Finset.mem_filter.mp hp).2
    obtain ⟨h₁, h₂, h₃, h₄, hfreq⟩ := hh
    have hpt (x : ZMod M) (hx : x ∈ H) : point x ∈ pts := Finset.mem_image_of_mem _ hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hpt h h₁, hpt _ h₂⟩,
      Finset.mem_product.mpr ⟨hpt _ h₄, hpt _ h₃⟩⟩, ?_⟩
    apply Prod.ext
    · change h + (h + s - t) = (h + s) + (h - t)
      abel
    · exact hfreq
  · rintro ⟨h, s, t⟩ _ ⟨h', s', t'⟩ _ he
    have hh : h = h' := congrArg (fun x => x.1.1.1) he
    have hs : h + s = h' + s' := congrArg (fun x => x.1.2.1) he
    have ht : h - t = h' - t' := congrArg (fun x => x.2.2.1) he
    subst h'
    have htt : t = t' := by linear_combination -ht
    exact Prod.ext rfl (Prod.ext (add_left_cancel hs) htt)

private noncomputable def align (z : ℂ) : ℂ := conj z / (‖z‖ : ℂ)

private lemma norm_align_le (z : ℂ) : ‖align z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [align, hz]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [align, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self hn]

private lemma align_mul (z : ℂ) : align z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [align, hz]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [align, div_mul_eq_mul_div, mul_comm (conj z) z, ← complex_ofReal_sq_norm,
    ← Complex.ofReal_div, sq, mul_div_cancel_right₀ _ hn]

private lemma sum_phaseKernel_eq (g : ZMod M → ℝ) (H : Finset (ZMod M))
    (ξ : ZMod M → ZMod M) (w : ZMod M → ℂ) :
    ∑ y, (g y : ℂ) * ∑ x, (g x : ℂ) * phaseKernel H ξ w x y =
      ∑ h ∈ H, w h * fourier (cyclicDerivative g h) (ξ h) := by
  classical
  have inner (y : ZMod M) :
      ∑ x, (g x : ℂ) * phaseKernel H ξ w x y =
        ∑ h ∈ H, (g (h + y) : ℂ) * (w h * ZMod.stdAddChar (-(y * ξ h))) := by
    calc
      _ = ∑ h : ZMod M, (g (h + y) : ℂ) * phaseKernel H ξ w (h + y) y :=
        (Fintype.sum_equiv (Equiv.addRight y) _ _ (fun _ => rfl)).symm
      _ = _ := by
        simp only [phaseKernel, add_sub_cancel_right, mul_ite, mul_zero]
        rw [← Finset.sum_filter]
        simp
  simp_rw [inner, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [fourier, ZMod.dft_apply, cyclicDerivative, Complex.ofReal_mul, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [add_comm h y]
  ring

private lemma phaseGraph_addEnergy_lower (g : ZMod M → ℝ) (H : Finset (ZMod M))
    (ξ : ZMod M → ZMod M) (hg : ∀ x, |g x| ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (hcoeff : ∀ h ∈ H, θ ≤ ‖fourier (cyclicDerivative g h) (ξ h)‖) :
    ((H.card : ℝ) * θ) ^ 4 ≤ (M : ℝ) ^ 5 * ((phaseGraph H ξ).addEnergy (phaseGraph H ξ) : ℝ) := by
  let V := fun h => fourier (cyclicDerivative g h) (ξ h)
  let w := fun h => align (V h)
  let W := phaseKernel H ξ w
  have hgn (x : ZMod M) : ‖(g x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hg x
  have hbox := box_cauchySchwarz (fun x => (g x : ℂ)) (fun x => (g x : ℂ)) W hgn hgn
  change ‖∑ y, (g y : ℂ) * ∑ x, (g x : ℂ) * phaseKernel H ξ w x y‖ ^ 4 ≤ _ at hbox
  rw [sum_phaseKernel_eq] at hbox
  change ‖∑ h ∈ H, align (V h) * V h‖ ^ 4 ≤ _ at hbox
  simp only [align_mul, ← Complex.ofReal_sum, Complex.norm_real, ZMod.card] at hbox
  rw [Real.norm_of_nonneg (by positivity)] at hbox
  have hsum : (H.card : ℝ) * θ ≤ ∑ h ∈ H, ‖V h‖ := by
    calc
      _ = ∑ _ ∈ H, θ := by simp
      _ ≤ _ := Finset.sum_le_sum hcoeff
  have hW : ‖boxSum W‖ ≤ (M : ℝ) * ((phaseGraph H ξ).addEnergy (phaseGraph H ξ) : ℝ) :=
    (norm_box_phaseKernel_le H ξ w (fun h => norm_align_le (V h))).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast card_phaseParallelograms_le_addEnergy H ξ)
        (by positivity))
  calc
    _ ≤ (∑ h ∈ H, ‖V h‖) ^ 4 := pow_le_pow_left₀ (by positivity) hsum 4
    _ ≤ (M : ℝ) ^ 4 * ‖boxSum W‖ := hbox
    _ ≤ (M : ℝ) ^ 4 * ((M : ℝ) * ((phaseGraph H ξ).addEnergy (phaseGraph H ξ) : ℝ)) := by
      gcongr
    _ = _ := by ring

end Phase


private lemma large_cube_has_high_energy_graph {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) (habs : ∀ x, |f x| ≤ 1)
    (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 ≤ δ) (hlarge : δ * (N : ℝ) ^ 4 ≤ cubeSum N f) :
    ∃ H : Finset (ZMod (2 * N + 1)), ∃ ξ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
      δ * (N : ℝ) / 6 ≤ (H.card : ℝ) ∧
        (∀ a ∈ H, Real.sqrt (δ / 6) * (N : ℝ) ≤
          ‖fourier (cyclicDerivative (periodize N f) a) (ξ a)‖) ∧
        (δ / 6) ^ 6 * (N : ℝ) ^ 3 / 3 ^ 5 ≤
          ((phaseGraph H ξ).addEnergy (phaseGraph H ξ) : ℝ) := by
  classical
  obtain ⟨H, ξ, hcard, hξ⟩ := large_cube_has_fourier_graph hf habs hN hδ hlarge
  refine ⟨H, ξ, hcard, hξ, ?_⟩
  let A := phaseGraph H ξ
  let E : ℝ := A.addEnergy A
  change _ ≤ E
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hbound := phaseGraph_addEnergy_lower (periodize N f) H ξ (fun x => habs _)
    (by positivity) hξ
  change ((H.card : ℝ) * (Real.sqrt (δ / 6) * (N : ℝ))) ^ 4 ≤ ((2 * N + 1 : ℕ) : ℝ) ^ 5 * E
    at hbound
  have hmod : ((2 * N + 1 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by push_cast; linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hsqrt : (Real.sqrt (δ / 6)) ^ 4 = (δ / 6) ^ 2 := by
    calc
      _ = ((Real.sqrt (δ / 6)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  have hmul : (δ / 6) ^ 6 * (N : ℝ) ^ 8 ≤ (3 * (N : ℝ)) ^ 5 * E := by
    calc
      _ = ((δ * (N : ℝ) / 6) * (Real.sqrt (δ / 6) * (N : ℝ))) ^ 4 := by
        simp only [mul_pow, hsqrt]
        ring
      _ ≤ ((H.card : ℝ) * (Real.sqrt (δ / 6) * (N : ℝ))) ^ 4 := by gcongr
      _ ≤ ((2 * N + 1 : ℕ) : ℝ) ^ 5 * E := hbound
      _ ≤ _ := by gcongr
  have hscaled : ((δ / 6) ^ 6 * (N : ℝ) ^ 3 / 3 ^ 5) * (3 * (N : ℝ)) ^ 5 ≤
      E * (3 * (N : ℝ)) ^ 5 := by
    calc
      _ = (δ / 6) ^ 6 * (N : ℝ) ^ 8 := by ring
      _ ≤ (3 * (N : ℝ)) ^ 5 * E := hmul
      _ = _ := mul_comm _ _
  exact le_of_mul_le_mul_right hscaled (by positivity)


section Popular

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

private def sumFibreCard (A : Finset G) (z : G) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 + p.2 = z)).card

private lemma sumFibreCard_le (A : Finset G) (z : G) : sumFibreCard A z ≤ A.card := by
  unfold sumFibreCard
  refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq he
    change x = x' at he
    change (x, y) ∈ (A ×ˢ A).filter _ at hp
    change (x', y') ∈ (A ×ˢ A).filter _ at hq
    have hx : x + y = z := (Finset.mem_filter.mp hp).2
    have hy : x' + y' = z := (Finset.mem_filter.mp hq).2
    subst x'
    exact Prod.ext rfl (add_left_cancel (hx.trans hy.symm))

private lemma sum_sumFibreCard (A P : Finset G) :
    ∑ z ∈ P, sumFibreCard A z = ((A ×ˢ A).filter (fun p => p.1 + p.2 ∈ P)).card :=
  Finset.sum_card_fiberwise_eq_card_filter _ _ _

private lemma sum_sumFibreCard_full (A : Finset G) :
    ∑ z ∈ A + A, sumFibreCard A z = A.card ^ 2 := by
  rw [sum_sumFibreCard]
  rw [Finset.filter_eq_self.mpr (fun p hp => Finset.add_mem_add
    (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2), Finset.card_product, sq]

private lemma exists_popular_sums (A : Finset G) (hA : A.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hE : ε * (A.card : ℝ) ^ 3 ≤ (A.addEnergy A : ℝ)) :
    ∃ P : Finset G, (ε / 2) * (P.card : ℝ) ≤ A.card ∧
      (ε / 2) * (A.card : ℝ) ^ 2 ≤
        (((A ×ˢ A).filter (fun p => p.1 + p.2 ∈ P)).card : ℝ) := by
  classical
  let n : ℝ := A.card
  let r (z : G) : ℝ := sumFibreCard A z
  let q := ε * n / 2
  let P := (A + A).filter (fun z => q ≤ r z)
  let edges : ℝ := ((A ×ˢ A).filter (fun p => p.1 + p.2 ∈ P)).card
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast hA.card_pos
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr (z : G) : 0 ≤ r z ∧ r z ≤ n := ⟨by dsimp [r]; positivity,
    by dsimp only [n, r]; exact_mod_cast sumFibreCard_le A z⟩
  have h₁ : ∑ z ∈ A + A, r z = n ^ 2 := by dsimp only [n, r]; exact_mod_cast sum_sumFibreCard_full A
  have h₂ : ∑ z ∈ P, r z = edges := by dsimp only [r, edges]; exact_mod_cast sum_sumFibreCard A P
  have h₃ : ∑ z ∈ A + A, r z ^ 2 = (A.addEnergy A : ℝ) := by
    dsimp only [r, sumFibreCard]
    exact_mod_cast (Finset.addEnergy_eq_sum_sq' A A).symm
  have hPsub : P ⊆ A + A := Finset.filter_subset _ _
  have hilim : (A + A).filter (fun z => z ∈ P) = P := by
    ext z
    exact ⟨fun hz => (Finset.mem_filter.mp hz).2, fun hz => Finset.mem_filter.mpr ⟨hPsub hz, hz⟩⟩
  have h₄ : (A.addEnergy A : ℝ) ≤ n * edges + q * n ^ 2 := by
    rw [← h₃]
    calc
      _ ≤ ∑ z ∈ A + A, ((if z ∈ P then n * r z else 0) + q * r z) := by
        refine Finset.sum_le_sum fun z hz => ?_
        by_cases hp : z ∈ P
        · rw [if_pos hp]
          have h := mul_le_mul_of_nonneg_right (hr z).2 (hr z).1
          have h' : 0 ≤ q * r z := mul_nonneg hq (hr z).1
          simpa only [sq] using h.trans (le_add_of_nonneg_right h')
        · rw [if_neg hp, zero_add, sq]
          have hlt : r z ≤ q := by
            apply le_of_not_ge
            intro h
            exact hp (Finset.mem_filter.mpr ⟨hz, h⟩)
          exact mul_le_mul_of_nonneg_right hlt (hr z).1
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, hilim, ← Finset.mul_sum,
          ← Finset.mul_sum, h₂, h₁]
  have hedge : (ε / 2) * n ^ 2 ≤ edges := by
    apply le_of_mul_le_mul_left _ hn
    change ε * n ^ 3 ≤ _ at hE
    dsimp [q] at h₄
    linarith only [hE, h₄]
  have hedgemax : edges ≤ n ^ 2 := by
    dsimp only [edges, n]
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (by simp [sq])
  have hpopular : (P.card : ℝ) * q ≤ edges := by
    rw [← h₂]
    calc
      _ = ∑ _ ∈ P, q := by simp
      _ ≤ _ := Finset.sum_le_sum fun z hz => (Finset.mem_filter.mp hz).2
  refine ⟨P, ?_, hedge⟩
  apply le_of_mul_le_mul_left _ hn
  dsimp [q] at hpopular
  linarith only [hpopular, hedgemax]

end Popular

section DenseGraph

variable {α β : Type*}

private noncomputable def relPairs (A : Finset α) (B : Finset β) (R : α → β → Prop) :
    Finset (α × β) := by
  classical
  exact (A ×ˢ B).filter (fun p => R p.1 p.2)

private noncomputable def leftNeighbors (A : Finset α) (R : α → β → Prop) (b : β) : Finset α := by
  classical
  exact A.filter (fun a => R a b)

private noncomputable def commonNeighbors (B : Finset β) (R : α → β → Prop) (a a' : α) :
    Finset β := by
  classical
  exact B.filter (fun b => R a b ∧ R a' b)

private lemma mem_leftNeighbors {A : Finset α} {R : α → β → Prop} {a : α} {b : β} :
    a ∈ leftNeighbors A R b ↔ a ∈ A ∧ R a b := by
  classical
  unfold leftNeighbors
  apply Finset.mem_filter

private lemma mem_commonNeighbors {B : Finset β} {R : α → β → Prop} {a a' : α}
    {b : β} : b ∈ commonNeighbors B R a a' ↔ b ∈ B ∧ R a b ∧ R a' b := by
  classical
  unfold commonNeighbors
  apply Finset.mem_filter

private lemma card_relPairs_eq_sum_left (A : Finset α) (B : Finset β) (R : α → β → Prop) :
    (relPairs A B R).card = ∑ a ∈ A, (leftNeighbors B (fun b a => R a b) a).card := by
  classical
  unfold relPairs leftNeighbors
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private lemma card_relPairs_eq_sum_right (A : Finset α) (B : Finset β) (R : α → β → Prop) :
    (relPairs A B R).card = ∑ b ∈ B, (leftNeighbors A R b).card := by
  classical
  unfold relPairs leftNeighbors
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private noncomputable def poorPairs (X : Finset α) (B : Finset β) (R : α → β → Prop)
    (τ : ℝ) : Finset (α × α) :=
  relPairs X X (fun a a' => ((commonNeighbors B R a a').card : ℝ) < τ * (B.card : ℝ))

private lemma sum_card_poorPairs (A : Finset α) (B : Finset β) (R : α → β → Prop) (τ : ℝ) :
    ∑ b ∈ B, (poorPairs (leftNeighbors A R b) B R τ).card =
      ∑ p ∈ poorPairs A B R τ, (commonNeighbors B R p.1 p.2).card := by
  classical
  let P := poorPairs A B R τ
  let S (p : α × α) (b : β) := R p.1 b ∧ R p.2 b
  have hp (b : β) : poorPairs (leftNeighbors A R b) B R τ = leftNeighbors P S b := by
    ext p
    simp only [P, S, poorPairs, relPairs, leftNeighbors, Finset.mem_filter, Finset.mem_product]
    tauto
  simp_rw [hp]
  rw [← card_relPairs_eq_sum_right, card_relPairs_eq_sum_left]
  refine Finset.sum_congr rfl fun p _ => congrArg Finset.card ?_
  ext b
  simp [leftNeighbors, commonNeighbors, S]

private lemma exists_many_well_connected (A : Finset α) (B : Finset β) (R : α → β → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (hdense : ρ * (A.card : ℝ) * (B.card : ℝ) ≤ ((relPairs A B R).card : ℝ)) :
    ∃ X : Finset α, X ⊆ A ∧ ρ * (A.card : ℝ) / 2 ≤ (X.card : ℝ) ∧
      ((poorPairs X B R (ρ ^ 2 / 128)).card : ℝ) ≤ (X.card : ℝ) ^ 2 / 64 := by
  classical
  let n : ℝ := A.card
  let m : ℝ := B.card
  let τ := ρ ^ 2 / 128
  let X (b : β) := leftNeighbors A R b
  let d (b : β) : ℝ := (X b).card
  let bad (b : β) : ℝ := (poorPairs (X b) B R τ).card
  let Q := poorPairs A B R τ
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast hA.card_pos
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast hB.card_pos
  have hsum : ρ * n * m ≤ ∑ b ∈ B, d b := by
    rw [card_relPairs_eq_sum_right, Nat.cast_sum] at hdense
    exact hdense
  have hdenseSq := pow_le_pow_left₀ (by positivity : 0 ≤ ρ * n * m) hsum 2
  have hcs : (∑ b ∈ B, d b) ^ 2 ≤ m * ∑ b ∈ B, d b ^ 2 := by
    simpa [m] using Finset.sum_mul_sq_le_sq_mul_sq B (fun _ : β => (1 : ℝ)) d
  have hgood : ρ ^ 2 * n ^ 2 * m ≤ ∑ b ∈ B, d b ^ 2 := by
    apply le_of_mul_le_mul_left _ hm
    calc
      _ = (ρ * n * m) ^ 2 := by ring
      _ ≤ _ := hdenseSq.trans hcs
  have hcount : (Q.card : ℝ) ≤ n ^ 2 := by
    dsimp only [Q, n, poorPairs, relPairs]
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_product _ _ |>.trans (sq _).symm)
  have hbad : ∑ b ∈ B, bad b ≤ τ * m * n ^ 2 := by
    calc
      _ = ∑ p ∈ Q, ((commonNeighbors B R p.1 p.2).card : ℝ) := by
        dsimp only [bad, X, Q]
        exact_mod_cast sum_card_poorPairs A B R τ
      _ ≤ ∑ _ ∈ Q, τ * m := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact ((Finset.mem_filter.mp hp).2 : ((commonNeighbors B R p.1 p.2).card : ℝ) < τ * m).le
      _ = (Q.card : ℝ) * (τ * m) := by simp
      _ ≤ n ^ 2 * (τ * m) := mul_le_mul_of_nonneg_right hcount (by dsimp [τ]; positivity)
      _ = _ := by ring
  have haverage : (∑ _ ∈ B, ρ ^ 2 * n ^ 2 / 2) ≤ ∑ b ∈ B, (d b ^ 2 - 64 * bad b) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    change m * _ ≤ _
    dsimp [τ] at hbad
    linarith only [hgood, hbad]
  obtain ⟨b, _, hb⟩ := Finset.exists_le_of_sum_le hB haverage
  have hbad₀ : 0 ≤ bad b := by dsimp [bad]; positivity
  have hdsq : (ρ * n / 2) ^ 2 ≤ d b ^ 2 := by
    nlinarith only [hb, hbad₀, sq_nonneg (ρ * n)]
  have hd : ρ * n / 2 ≤ d b := (sq_le_sq₀ (by positivity) (by dsimp [d]; positivity)).mp hdsq
  refine ⟨X b, Finset.filter_subset _ _, hd, ?_⟩
  change bad b ≤ d b ^ 2 / 64
  nlinarith only [hb, sq_nonneg (ρ * n)]

private lemma erase_poor_vertices (X : Finset α) (B : Finset β) (R : α → β → Prop) {τ : ℝ}
    (hX : X.Nonempty)
    (hbad : ((poorPairs X B R τ).card : ℝ) ≤ (X.card : ℝ) ^ 2 / 64) :
    ∃ Y : Finset α, Y ⊆ X ∧ (X.card : ℝ) / 2 ≤ (Y.card : ℝ) ∧
      ∀ a ∈ Y, ∀ a' ∈ Y,
        ∃ T : Finset α, T ⊆ X ∧ (X.card : ℝ) / 2 ≤ (T.card : ℝ) ∧
          ∀ c ∈ T, τ * (B.card : ℝ) ≤ ((commonNeighbors B R a c).card : ℝ) ∧
            τ * (B.card : ℝ) ≤ ((commonNeighbors B R a' c).card : ℝ) := by
  classical
  let x : ℝ := X.card
  let D (a : α) := leftNeighbors X
    (fun c a => ((commonNeighbors B R a c).card : ℝ) < τ * (B.card : ℝ)) a
  let Z := X.filter (fun a => x / 8 < ((D a).card : ℝ))
  have hx : 0 < x := by dsimp only [x]; exact_mod_cast hX.card_pos
  have hZsub : Z ⊆ X := Finset.filter_subset _ _
  have hdeg : ∑ a ∈ X, ((D a).card : ℝ) = ((poorPairs X B R τ).card : ℝ) := by
    unfold poorPairs
    rw [card_relPairs_eq_sum_left, Nat.cast_sum]
  have hZ : (Z.card : ℝ) ≤ x / 8 := by
    have hsum : (x / 8) * (Z.card : ℝ) ≤ ∑ a ∈ X, ((D a).card : ℝ) := by
      calc
        _ = ∑ _ ∈ Z, x / 8 := by simp [mul_comm]
        _ ≤ ∑ a ∈ Z, ((D a).card : ℝ) :=
          Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2.le
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hZsub (by intros; positivity)
    rw [hdeg] at hsum
    exact le_of_mul_le_mul_left (by change _ ≤ x / 8 * (x / 8); nlinarith only [hsum, hbad])
      (by positivity : 0 < x / 8)
  let Y := X \ Z
  have hY : (Y.card : ℝ) + (Z.card : ℝ) = x := by
    dsimp only [Y, x]
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hZsub
  refine ⟨Y, Finset.sdiff_subset, by linarith only [hY, hZ, hx], ?_⟩
  have hD (a : α) (ha : a ∈ Y) : ((D a).card : ℝ) ≤ x / 8 := by
    apply le_of_not_gt
    intro he
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, he⟩)
  have hDsub (a : α) : D a ⊆ X := Finset.filter_subset _ _
  intro a ha a' ha'
  let U := D a ∪ D a'
  let T := X \ U
  have hU : (U.card : ℝ) ≤ ((D a).card : ℝ) + ((D a').card : ℝ) := by
    dsimp only [U]
    exact_mod_cast Finset.card_union_le (D a) (D a')
  have hT : (T.card : ℝ) + (U.card : ℝ) = x := by
    dsimp only [T, U, x]
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.union_subset (hDsub a) (hDsub a'))
  refine ⟨T, Finset.sdiff_subset, by linarith only [hT, hU, hD a ha, hD a' ha', hx], ?_⟩
  intro c hc
  obtain ⟨hcX, hcU⟩ := Finset.mem_sdiff.mp hc
  have h₁ : c ∉ D a := fun h => hcU (Finset.mem_union_left _ h)
  have h₂ : c ∉ D a' := fun h => hcU (Finset.mem_union_right _ h)
  exact ⟨le_of_not_gt fun h => h₁ (Finset.mem_filter.mpr ⟨hcX, h⟩),
    le_of_not_gt fun h => h₂ (Finset.mem_filter.mpr ⟨hcX, h⟩)⟩

private lemma dense_middle_vertices (A : Finset α) (B : Finset β) (R : α → β → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (hdense : ρ * (A.card : ℝ) * (B.card : ℝ) ≤ ((relPairs A B R).card : ℝ)) :
    ∃ Y : Finset α, Y ⊆ A ∧ ρ * (A.card : ℝ) / 4 ≤ (Y.card : ℝ) ∧
      ∀ a ∈ Y, ∀ a' ∈ Y,
        ∃ T : Finset α, T ⊆ A ∧ ρ * (A.card : ℝ) / 4 ≤ (T.card : ℝ) ∧
          ∀ c ∈ T,
            (ρ ^ 2 / 128) * (B.card : ℝ) ≤ ((commonNeighbors B R a c).card : ℝ) ∧
            (ρ ^ 2 / 128) * (B.card : ℝ) ≤ ((commonNeighbors B R a' c).card : ℝ) := by
  obtain ⟨X, hXA, hXcard, hXbad⟩ := exists_many_well_connected A B R hA hB hρ hdense
  have hX : X.Nonempty := by
    apply Finset.card_pos.mp
    have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < ρ * (A.card : ℝ) / 2) hXcard)
  obtain ⟨Y, hYX, hY, hm⟩ := erase_poor_vertices X B R hX hXbad
  refine ⟨Y, hYX.trans hXA, by linarith only [hY, hXcard], ?_⟩
  intro a ha a' ha'
  obtain ⟨T, hTX, hT, hc⟩ := hm a ha a' ha'
  exact ⟨T, hTX.trans hXA, by linarith only [hT, hXcard], hc⟩

end DenseGraph

section SmallDifference

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

private def alternatingSum (p : G × G × G × G) : G :=
  p.1 - p.2.1 + p.2.2.1 - p.2.2.2

private def alternatingFibre (P : Finset G) (d : G) : Finset (G × G × G × G) :=
  (P ×ˢ P ×ˢ P ×ˢ P).filter (fun p => alternatingSum p = d)

private lemma card_alternatingFibre_ge (A P T : Finset G) (a a' : G) {u : ℝ}
    (hu : 0 ≤ u)
    (hcommon : ∀ c ∈ T,
      u ≤ ((commonNeighbors A (fun x y => x + y ∈ P) a c).card : ℝ) ∧
        u ≤ ((commonNeighbors A (fun x y => x + y ∈ P) a' c).card : ℝ)) :
    (T.card : ℝ) * u ^ 2 ≤ ((alternatingFibre P (a - a')).card : ℝ) := by
  classical
  let L (c : G) := commonNeighbors A (fun x y => x + y ∈ P) a c
  let R (c : G) := commonNeighbors A (fun x y => x + y ∈ P) a' c
  let D := T.sigma (fun c => L c ×ˢ R c)
  have hD : (T.card : ℝ) * u ^ 2 ≤ (D.card : ℝ) := by
    simp only [D, Finset.card_sigma, Nat.cast_sum, Finset.card_product, Nat.cast_mul]
    calc
      _ = ∑ _ ∈ T, u ^ 2 := by simp
      _ ≤ _ := by
        refine Finset.sum_le_sum fun c hc => ?_
        obtain ⟨hc₁, hc₂⟩ := hcommon c hc
        rw [sq]
        exact mul_le_mul hc₁ hc₂ hu (by positivity)
  apply hD.trans
  have hcard : D.card ≤ (alternatingFibre P (a - a')).card := by
    refine Finset.card_le_card_of_injOn
      (fun (p : Σ _ : G, G × G) =>
        (a + p.2.1, p.1 + p.2.1, p.1 + p.2.2, a' + p.2.2)) ?_ ?_
    · rintro ⟨c, b, b'⟩ hp
      change ⟨c, (b, b')⟩ ∈ D at hp
      have hbs := Finset.mem_product.mp (Finset.mem_sigma.mp hp).2
      have hb : a + b ∈ P ∧ c + b ∈ P := (mem_commonNeighbors.mp hbs.1).2
      have hb' : a' + b' ∈ P ∧ c + b' ∈ P := (mem_commonNeighbors.mp hbs.2).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hb.1, Finset.mem_product.mpr ⟨hb.2,
        Finset.mem_product.mpr ⟨hb'.2, hb'.1⟩⟩⟩, ?_⟩
      unfold alternatingSum
      dsimp only
      abel
    · rintro ⟨c, b, b'⟩ _ ⟨e, d, d'⟩ _ he
      have h₁ : a + b = a + d := congrArg Prod.fst he
      have h₂ : c + b = e + d := congrArg (fun p => p.2.1) he
      have h₃ : a' + b' = a' + d' := congrArg (fun p => p.2.2.2) he
      have hbd : b = d := add_left_cancel h₁
      have hb'd' : b' = d' := add_left_cancel h₃
      subst d
      subst d'
      have hce : c = e := add_right_cancel h₂
      subst e
      rfl
  exact_mod_cast hcard

private lemma sum_alternatingFibre_le (D P : Finset G) :
    ∑ d ∈ D, ((alternatingFibre P d).card : ℝ) ≤ (P.card : ℝ) ^ 4 := by
  have h : ∑ d ∈ D, (alternatingFibre P d).card ≤ P.card ^ 4 := by
    unfold alternatingFibre
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    refine (Finset.card_filter_le _ _).trans_eq ?_
    simp only [Finset.card_product]
    ring
  exact_mod_cast h

private lemma exists_small_difference_subset (A : Finset G) (hA : A.Nonempty) {ε : ℝ}
    (hε : 0 < ε) (hE : ε * (A.card : ℝ) ^ 3 ≤ (A.addEnergy A : ℝ)) :
    ∃ Y : Finset G, Y ⊆ A ∧ (ε / 8) * (A.card : ℝ) ≤ (Y.card : ℝ) ∧
      ((ε / 2) ^ 9 / 65536) * ((Y - Y).card : ℝ) ≤ (A.card : ℝ) := by
  classical
  obtain ⟨P, hP, hdense⟩ := exists_popular_sums A hA hε hE
  let ρ := ε / 2
  let R (a b : G) := a + b ∈ P
  let n : ℝ := A.card
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast hA.card_pos
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hgraph : ρ * n * n ≤ ((relPairs A A R).card : ℝ) := by
    rw [mul_assoc, ← sq]
    have heq : relPairs A A R = (A ×ˢ A).filter (fun p => p.1 + p.2 ∈ P) := by
      ext p
      simp [relPairs, R]
    rw [heq]
    exact hdense
  obtain ⟨Y, hYA, hY, hmiddle⟩ := dense_middle_vertices A A R hA hA hρ hgraph
  refine ⟨Y, hYA, by dsimp only [ρ, n] at hY; linarith only [hY], ?_⟩
  let w := (ρ ^ 2 / 128 * n) ^ 2 * (ρ * n / 4)
  have hf (d : G) (hd : d ∈ Y - Y) : w ≤ ((alternatingFibre P d).card : ℝ) := by
    obtain ⟨a, ha, a', ha', rfl⟩ := Finset.mem_sub.mp hd
    obtain ⟨T, _, hT, hcommon⟩ := hmiddle a ha a' ha'
    have hcard := card_alternatingFibre_ge A P T a a'
      (show 0 ≤ (ρ ^ 2 / 128) * n by positivity) hcommon
    calc
      _ ≤ (T.card : ℝ) * ((ρ ^ 2 / 128) * n) ^ 2 := by
        unfold w
        rw [mul_comm]
        gcongr
      _ ≤ _ := hcard
  have htotal : ((Y - Y).card : ℝ) * w ≤ (P.card : ℝ) ^ 4 := by
    calc
      _ = ∑ _ ∈ Y - Y, w := by simp
      _ ≤ ∑ d ∈ Y - Y, ((alternatingFibre P d).card : ℝ) := Finset.sum_le_sum hf
      _ ≤ _ := sum_alternatingFibre_le _ _
  have hp : (ρ * (P.card : ℝ)) ^ 4 ≤ n ^ 4 :=
    pow_le_pow_left₀ (by positivity) hP 4
  have hc : ((Y - Y).card : ℝ) * w * ρ ^ 4 ≤ n ^ 4 := by
    refine (mul_le_mul_of_nonneg_right htotal (by positivity)).trans ?_
    rw [mul_comm, ← mul_pow]
    exact hp
  change (ρ ^ 9 / 65536) * ((Y - Y).card : ℝ) ≤ n
  refine le_of_mul_le_mul_right ?_ (pow_pos hn 3)
  calc
    _ = ((Y - Y).card : ℝ) * w * ρ ^ 4 := by dsimp [w]; ring
    _ ≤ n ^ 4 := hc
    _ = n * n ^ 3 := by ring

end SmallDifference

private lemma card_phaseGraph {M : ℕ} [NeZero M] (H : Finset (ZMod M))
    (ξ : ZMod M → ZMod M) : (phaseGraph H ξ).card = H.card := by
  apply Finset.card_image_of_injective
  intro a b h
  exact congrArg Prod.fst h

private lemma restrict_phaseGraph {M : ℕ} [NeZero M] {H : Finset (ZMod M)}
    {ξ : ZMod M → ZMod M} {Y : Finset (ZMod M × ZMod M)} (hY : Y ⊆ phaseGraph H ξ) :
    Y.image Prod.fst ⊆ H ∧ phaseGraph (Y.image Prod.fst) ξ = Y := by
  classical
  have hpoint (p : ZMod M × ZMod M) (hp : p ∈ Y) : p.1 ∈ H ∧ p = (p.1, ξ p.1) := by
    obtain ⟨a, ha, h⟩ := Finset.mem_image.mp (hY hp)
    subst p
    exact ⟨ha, rfl⟩
  constructor
  · intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact (hpoint p hp).1
  · ext p
    constructor
    · intro hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      simpa only [← (hpoint q hq).2] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨p.1, Finset.mem_image_of_mem _ hp, (hpoint p hp).2.symm⟩

private noncomputable def graphRate (δ : ℝ) : ℝ := (δ / 6) ^ 6 / 3 ^ 8

private lemma large_cube_has_small_difference_graph {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) (habs : ∀ x, |f x| ≤ 1)
    (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) (hlarge : δ * (N : ℝ) ^ 4 ≤ cubeSum N f) :
    ∃ J : Finset (ZMod (2 * N + 1)), ∃ ξ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
      graphRate δ * δ * (N : ℝ) / 48 ≤ (J.card : ℝ) ∧
        (∀ a ∈ J, Real.sqrt (δ / 6) * (N : ℝ) ≤
          ‖fourier (cyclicDerivative (periodize N f) a) (ξ a)‖) ∧
        ((graphRate δ / 8) * ((graphRate δ / 2) ^ 9 / 65536)) *
          (((phaseGraph J ξ - phaseGraph J ξ).card) : ℝ) ≤ (J.card : ℝ) := by
  classical
  obtain ⟨H, ξ, hcard, hξ, hE⟩ := large_cube_has_high_energy_graph hf habs hN hδ.le hlarge
  let A := phaseGraph H ξ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hAcard : A.card = H.card := card_phaseGraph H ξ
  have hA : A.Nonempty := by
    rw [← Finset.card_pos, hAcard]
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < δ * (N : ℝ) / 6) hcard)
  have hAupper : (A.card : ℝ) ≤ 3 * (N : ℝ) := by
    have h := Finset.card_le_univ H
    rw [ZMod.card] at h
    have h' : (H.card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast h
    rw [hAcard]
    push_cast at h'
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hε : 0 < graphRate δ := by unfold graphRate; positivity
  have hAenergy : graphRate δ * (A.card : ℝ) ^ 3 ≤ (A.addEnergy A : ℝ) := by
    calc
      _ ≤ graphRate δ * (3 * (N : ℝ)) ^ 3 := by gcongr
      _ = (δ / 6) ^ 6 * (N : ℝ) ^ 3 / 3 ^ 5 := by unfold graphRate; ring
      _ ≤ _ := hE
  obtain ⟨Y, hYA, hY, hdiff⟩ := exists_small_difference_subset A hA hε hAenergy
  obtain ⟨hsub, hYeq⟩ := restrict_phaseGraph hYA
  let J := Y.image Prod.fst
  have hJcard : J.card = Y.card := by rw [← card_phaseGraph J ξ]; exact congrArg Finset.card hYeq
  refine ⟨J, ξ, ?_, fun a ha => hξ a (hsub ha), ?_⟩
  · rw [hJcard]
    calc
      _ = (graphRate δ / 8) * (δ * (N : ℝ) / 6) := by ring
      _ ≤ (graphRate δ / 8) * (A.card : ℝ) := by rw [hAcard]; gcongr
      _ ≤ _ := hY
  · change phaseGraph J ξ = Y at hYeq
    rw [hYeq, hJcard, mul_assoc]
    exact (mul_le_mul_of_nonneg_left hdiff (by positivity)).trans hY


section Vertical

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A] [DecidableEq G] [DecidableEq A]

private lemma card_fibre_mul_le_card_add (Γ D : Finset (G × A))
    (hΓ : Set.InjOn Prod.fst (Γ : Set (G × A))) (x : G) :
    Γ.card * (D.filter (fun z => z.1 = x)).card ≤ (Γ + D).card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun p : (G × A) × (G × A) => p.1 + p.2) ?_ ?_
  · intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
    exact Finset.add_mem_add h₁ (Finset.mem_filter.mp h₂).1
  · intro p hp q hq he
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
    obtain ⟨h₃, h₄⟩ := Finset.mem_product.mp hq
    have hx := (Finset.mem_filter.mp h₂).2
    have hx' := (Finset.mem_filter.mp h₄).2
    have hfirst := congrArg Prod.fst he
    change p.1.1 + p.2.1 = q.1.1 + q.2.1 at hfirst
    rw [hx, hx'] at hfirst
    have he₁ : p.1 = q.1 := hΓ h₁ h₃ (add_right_cancel hfirst)
    change p.1 + p.2 = q.1 + q.2 at he
    rw [he₁] at he
    have he₂ : p.2 = q.2 := add_left_cancel he
    exact Prod.ext he₁ he₂

private lemma card_vertical_fibre_le (Γ : Finset (G × A)) (hΓ : Γ.Nonempty)
    (hfst : Set.InjOn Prod.fst (Γ : Set (G × A))) (m n : ℕ) (x : G) :
    (((((m • Γ) - (n • Γ)).filter (fun z => z.1 = x)).card : ℕ) : ℚ≥0) ≤
      (((Γ - Γ).card : ℚ≥0) / Γ.card) ^ (m + n + 1) := by
  let D := (m • Γ) - (n • Γ)
  have hcard : (0 : ℚ≥0) < Γ.card := by exact_mod_cast hΓ.card_pos
  have h := card_fibre_mul_le_card_add Γ D hfst x
  have hadd : Γ + D = ((m + 1) • Γ) - (n • Γ) := by
    dsimp only [D]
    rw [add_nsmul, one_nsmul]
    ext z
    simp only [Finset.mem_add, Finset.mem_sub]
    constructor
    · rintro ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, rfl⟩
      exact ⟨b + a, ⟨b, hb, a, ha, rfl⟩, c, hc, by abel⟩
    · rintro ⟨_, ⟨b, hb, a, ha, rfl⟩, c, hc, rfl⟩
      exact ⟨a, ha, b - c, ⟨b, hb, c, hc, rfl⟩, by abel⟩
  rw [hadd] at h
  have h' : (Γ.card : ℚ≥0) * ((D.filter (fun z => z.1 = x)).card : ℚ≥0) ≤
      ((((m + 1) • Γ) - (n • Γ)).card : ℚ≥0) := by exact_mod_cast h
  have hp := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hΓ Γ (m + 1) n
  rw [show m + 1 + n = m + n + 1 by omega, mul_comm] at hp
  exact le_of_mul_le_mul_left (h'.trans hp) hcard

private lemma fst_inj_of_no_vertical {D : Finset (G × A)}
    (h : ∀ w ∈ D - D, w.1 = 0 → w.2 = 0) :
    Set.InjOn Prod.fst (D : Set (G × A)) := by
  intro x hx y hy hxy
  have hsub : x - y ∈ D - D := Finset.sub_mem_sub hx hy
  have hfirst : (x - y).1 = 0 := sub_eq_zero.mpr hxy
  have hsecond := h (x - y) hsub hfirst
  exact Prod.ext hxy (sub_eq_zero.mp hsecond)

private lemma exists_local_additive_graph (D Q : Finset (G × A))
    (hadd : D + D - D ⊆ Q) (hsub : D - D ⊆ Q)
    (hQ : ∀ w ∈ Q, w.1 = 0 → w.2 = 0) :
    ∃ φ : G → A,
      (∀ w ∈ D, φ w.1 = w.2) ∧
      ∀ x ∈ D.image Prod.fst, ∀ y ∈ D.image Prod.fst, x + y ∈ D.image Prod.fst →
        φ (x + y) = φ x + φ y := by
  classical
  have hf : Set.InjOn Prod.fst (D : Set (G × A)) :=
    fst_inj_of_no_vertical (fun w hw => hQ w (hsub hw))
  have hpoint (x : G) (hx : x ∈ D.image Prod.fst) :
      ∃ w ∈ D, w.1 = x := Finset.mem_image.mp hx
  let φ (x : G) := if hx : x ∈ D.image Prod.fst then (hpoint x hx).choose.2 else 0
  have hφ (w : G × A) (hw : w ∈ D) : φ w.1 = w.2 := by
    have hx : w.1 ∈ D.image Prod.fst := Finset.mem_image_of_mem _ hw
    dsimp only [φ]
    rw [dif_pos hx]
    have hp := (hpoint w.1 hx).choose_spec
    have h := hf hp.1 hw hp.2
    exact congrArg Prod.snd h
  refine ⟨φ, hφ, ?_⟩
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := hpoint x hx
  obtain ⟨b, hb, rfl⟩ := hpoint y hy
  obtain ⟨c, hc, he⟩ := hpoint (a.1 + b.1) hxy
  have hin : a + b - c ∈ Q := hadd (Finset.sub_mem_sub (Finset.add_mem_add ha hb) hc)
  have hfirst : (a + b - c).1 = 0 := sub_eq_zero.mpr he.symm
  have hsecond : a.2 + b.2 - c.2 = 0 := hQ _ hin hfirst
  rw [← he, hφ c hc, hφ a ha, hφ b hb, sub_eq_zero.mp hsecond]

end Vertical

section Separation

variable {M : ℕ} [NeZero M]

private noncomputable def surviving (V : Finset (ZMod M)) (k : ZMod M) : Finset (ZMod M) :=
  V.filter (fun v => (1 : ℝ) / 2 < (ZMod.stdAddChar (k * v)).re)

private lemma bad_multipliers_card_le {v : ZMod M} (hv : v ≠ 0) :
    (((surviving (Finset.univ : Finset (ZMod M)) v).card : ℕ) : ℝ) ≤
      2 * (M : ℝ) / 3 := by
  let B := surviving (Finset.univ : Finset (ZMod M)) v
  let z (k : ZMod M) := ZMod.stdAddChar (v * k)
  have hzsum : ∑ k, z k = 0 := by
    dsimp only [z]
    simp_rw [mul_comm v]
    exact sum_stdAddChar_mul_of_ne_zero hv
  have hsum : ∑ k, (z k).re = 0 := by
    simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re hzsum
  have hB : (3 / 2 : ℝ) * (B.card : ℝ) ≤ (M : ℝ) := by
    calc
      _ = ∑ _ ∈ B, (3 / 2 : ℝ) := by simp [mul_comm]
      _ = ∑ k : ZMod M, if 1 / 2 < (z k).re then (3 / 2 : ℝ) else 0 := by
        rw [← Finset.sum_filter]
        rfl
      _ ≤ ∑ k : ZMod M, ((z k).re + 1) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hn : ‖z k‖ = 1 := by
          simp only [z, ZMod.stdAddChar_apply, Circle.norm_coe]
        have hre := Complex.abs_re_le_norm (z k)
        rw [hn, abs_le] at hre
        split_ifs <;> linarith [hre.1]
      _ = _ := by simp [Finset.sum_add_distrib, hsum, ZMod.card]
  linarith only [hB]

private lemma exists_surviving_le (V : Finset (ZMod M)) (hV : 0 ∉ V) :
    ∃ k, ((surviving V k).card : ℝ) ≤ 2 * (V.card : ℝ) / 3 := by
  classical
  let U : Finset (ZMod M) := Finset.univ
  let R (v k : ZMod M) : Prop := (1 : ℝ) / 2 < (ZMod.stdAddChar (k * v)).re
  have hleft (v : ZMod M) : leftNeighbors U (fun k v => R v k) v = surviving U v := by
    ext k
    simp only [leftNeighbors, surviving, Finset.mem_filter, R, mul_comm k v]
  have hright (k : ZMod M) : leftNeighbors V R k = surviving V k := by
    ext v
    simp only [leftNeighbors, surviving, Finset.mem_filter, R]
  have hcount : ∑ k ∈ U, ((surviving V k).card : ℝ) =
      ∑ v ∈ V, ((surviving U v).card : ℝ) := by
    have hL := card_relPairs_eq_sum_left V U R
    have hR := card_relPairs_eq_sum_right V U R
    simp only [hleft] at hL
    simp only [hright] at hR
    exact_mod_cast hR.symm.trans hL
  have hcompare : (∑ k ∈ U, ((surviving V k).card : ℝ)) ≤
      ∑ _ ∈ U, (2 * (V.card : ℝ) / 3) := by
    rw [hcount]
    have hs := Finset.sum_le_sum (s := V) (f := fun v => ((surviving U v).card : ℝ))
      (g := fun _ => 2 * (M : ℝ) / 3) (fun v hv => bad_multipliers_card_le (by
        intro h
        exact hV (h ▸ hv)))
    calc
      _ ≤ ∑ _ ∈ V, 2 * (M : ℝ) / 3 := hs
      _ = _ := by simp [U, ZMod.card]; ring
  obtain ⟨k, _, hk⟩ := Finset.exists_le_of_sum_le (show U.Nonempty from Finset.univ_nonempty)
    hcompare
  exact ⟨k, hk⟩

private lemma exists_separating_multipliers (V : Finset (ZMod M)) (hV : 0 ∉ V)
    (m : ℕ) (hm : V.card < 2 ^ m) :
    ∃ ks : List (ZMod M), ks.length ≤ 2 * m ∧
      ∀ v ∈ V, ∃ k ∈ ks, (ZMod.stdAddChar (k * v)).re ≤ 1 / 2 := by
  classical
  induction m generalizing V with
  | zero =>
    have hcard : V.card = 0 := by simpa using (Nat.lt_succ_iff.mp hm)
    refine ⟨[], by simp, ?_⟩
    simp [Finset.card_eq_zero.mp hcard]
  | succ m ih =>
    obtain ⟨k₁, hk₁⟩ := exists_surviving_le V hV
    let V₁ := surviving V k₁
    have h₁ : V₁ ⊆ V := Finset.filter_subset _ _
    obtain ⟨k₂, hk₂⟩ := exists_surviving_le V₁ (fun h => hV (h₁ h))
    let V₂ := surviving V₁ k₂
    have h₂ : V₂ ⊆ V₁ := Finset.filter_subset _ _
    have hm₂ : V₂.card < 2 ^ m := by
      have hpow : (V.card : ℝ) < (2 : ℝ) ^ (m + 1) := by exact_mod_cast hm
      rw [pow_succ] at hpow
      change (V₁.card : ℝ) ≤ _ at hk₁
      change (V₂.card : ℝ) ≤ _ at hk₂
      have hreal : (V₂.card : ℝ) < (2 : ℝ) ^ m := by
        linarith only [hk₁, hk₂, hpow, pow_pos (by norm_num : (0 : ℝ) < 2) m]
      exact_mod_cast hreal
    obtain ⟨ks, hklen, hksep⟩ := ih V₂ (fun h => hV (h₁ (h₂ h))) hm₂
    refine ⟨k₁ :: k₂ :: ks, by simp only [List.length_cons]; omega, ?_⟩
    intro v hv
    by_cases hv₁ : v ∈ V₁
    · by_cases hv₂ : v ∈ V₂
      · obtain ⟨k, hk, hsep⟩ := hksep v hv₂
        exact ⟨k, by simp [hk], hsep⟩
      · refine ⟨k₂, by simp, le_of_not_gt ?_⟩
        exact fun h => hv₂ (Finset.mem_filter.mpr ⟨hv₁, h⟩)
    · refine ⟨k₁, by simp, le_of_not_gt ?_⟩
      exact fun h => hv₁ (Finset.mem_filter.mpr ⟨hv, h⟩)

end Separation

section PhaseGrid

private noncomputable def phaseGrid (z : ℂ) : ℤ × ℤ := (⌊64 * z.re⌋, ⌊64 * z.im⌋)

private lemma grid_coord_bounds (r : ℝ) (hr : |r| ≤ 1) : ⌊64 * r⌋ ∈ Finset.Icc (-64 : ℤ) 64 := by
  rw [abs_le] at hr
  apply Finset.mem_Icc.mpr
  constructor
  · apply Int.le_floor.mpr
    push_cast
    linarith [hr.1]
  · apply Int.floor_le_iff.mpr
    norm_num
    linarith [hr.2]

private def phaseGridRange : Finset (ℤ × ℤ) := Finset.Icc (-64 : ℤ) 64 ×ˢ Finset.Icc (-64 : ℤ) 64

set_option maxRecDepth 8192 in
private lemma phaseGrid_mem (z : ℂ) (hz : ‖z‖ ≤ 1) : phaseGrid z ∈ phaseGridRange := by
  unfold phaseGridRange
  rw [Finset.mem_product]
  exact ⟨grid_coord_bounds z.re ((Complex.abs_re_le_norm z).trans hz),
    grid_coord_bounds z.im ((Complex.abs_im_le_norm z).trans hz)⟩

private lemma grid_coord_close {r s : ℝ} (h : ⌊64 * r⌋ = ⌊64 * s⌋) : |r - s| ≤ 1 / 64 := by
  have ha := Int.floor_le (64 * r)
  have hb := Int.lt_floor_add_one (64 * r)
  rw [h] at ha hb
  have hc := Int.floor_le (64 * s)
  have hd := Int.lt_floor_add_one (64 * s)
  rw [abs_le]
  exact ⟨by linarith [ha, hd], by linarith [hb, hc]⟩

private lemma phaseGrid_close {z z' : ℂ} (h : phaseGrid z = phaseGrid z') :
    ‖z - z'‖ ≤ 1 / 32 := by
  have hre := grid_coord_close (congrArg Prod.fst h)
  have him := grid_coord_close (congrArg Prod.snd h)
  have hn := Complex.norm_le_abs_re_add_abs_im (z - z')
  rw [Complex.sub_re, Complex.sub_im] at hn
  linarith

set_option maxRecDepth 8192 in
private lemma exists_large_phase_bin {ι : Type*} (J : Finset ι) (g : ι → ℂ)
    (hg : ∀ a ∈ J, ‖g a‖ ≤ 1) :
    ∃ J' : Finset ι, J' ⊆ J ∧ J.card ≤ 32768 * J'.card ∧
      ∀ a ∈ J', ∀ b ∈ J', ‖g a - g b‖ ≤ 1 / 32 := by
  classical
  let P := phaseGridRange
  let p (a : ι) := phaseGrid (g a)
  let F (y : ℤ × ℤ) := J.filter (fun a => p a = y)
  have hsum : ∑ y ∈ P, (F y).card = J.card := by
    unfold F
    rw [Finset.sum_card_fiberwise_eq_card_filter, Finset.filter_eq_self.mpr]
    exact fun a ha => phaseGrid_mem _ (hg a ha)
  have hPcard : P.card ≤ 32768 := by
    unfold P phaseGridRange
    rw [Finset.card_product, Int.card_Icc]
    change 129 * 129 ≤ 32768
    norm_num
  have hP : P.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    unfold P phaseGridRange
    simp only [Finset.mem_product, Finset.mem_Icc]
    norm_num
  obtain ⟨y, _, hy⟩ := Finset.exists_max_image P (fun y => (F y).card) hP
  refine ⟨F y, Finset.filter_subset _ _, ?_, ?_⟩
  · calc
      _ = ∑ y ∈ P, (F y).card := hsum.symm
      _ ≤ ∑ _ ∈ P, (F y).card := Finset.sum_le_sum hy
      _ = P.card * (F y).card := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hPcard
  · intro a ha b hb
    apply phaseGrid_close
    exact ((Finset.mem_filter.mp ha).2).trans (Finset.mem_filter.mp hb).2.symm

private lemma exists_simultaneous_phase_bins {M : ℕ} [NeZero M] {ι : Type*}
    (J : Finset ι) (ξ : ι → ZMod M) (ks : List (ZMod M)) :
    ∃ J' : Finset ι, J' ⊆ J ∧ J.card ≤ 32768 ^ ks.length * J'.card ∧
      ∀ k ∈ ks, ∀ a ∈ J', ∀ b ∈ J',
        ‖ZMod.stdAddChar (k * ξ a) - ZMod.stdAddChar (k * ξ b)‖ ≤ 1 / 32 := by
  induction ks generalizing J with
  | nil =>
    refine ⟨J, Finset.Subset.refl _, by simp, by simp⟩
  | cons k ks ih =>
    obtain ⟨J₁, hsub₁, hcard₁, hclose₁⟩ := exists_large_phase_bin J
      (fun a => ZMod.stdAddChar (k * ξ a))
      (fun _ _ => by rw [ZMod.stdAddChar_apply, Circle.norm_coe])
    obtain ⟨J₂, hsub₂, hcard₂, hclose₂⟩ := ih J₁
    refine ⟨J₂, hsub₂.trans hsub₁, ?_, ?_⟩
    · calc
        _ ≤ 32768 * J₁.card := hcard₁
        _ ≤ 32768 * (32768 ^ ks.length * J₂.card) := Nat.mul_le_mul_left _ hcard₂
        _ = _ := by simp only [List.length_cons, pow_succ]; ring
    · intro j hj a ha b hb
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hclose₁ a (hsub₂ ha) b (hsub₂ hb)
      · exact hclose₂ j hj a ha b hb

end PhaseGrid

section CharacterBounds

variable {M : ℕ} [NeZero M]

private lemma norm_stdAddChar (a : ZMod M) : ‖ZMod.stdAddChar a‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

private lemma norm_stdAddChar_sub_one (a b : ZMod M) :
    ‖ZMod.stdAddChar (a - b) - 1‖ = ‖ZMod.stdAddChar a - ZMod.stdAddChar b‖ := by
  have hprod : ZMod.stdAddChar b * ZMod.stdAddChar (-b) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  calc
    _ = ‖(ZMod.stdAddChar a - ZMod.stdAddChar b) * ZMod.stdAddChar (-b)‖ := by
      rw [sub_mul, hprod, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg]
    _ = _ := by rw [norm_mul, norm_stdAddChar, mul_one]

private lemma norm_stdAddChar_add_sub_le (a b c d : ZMod M) :
    ‖ZMod.stdAddChar (a + b) - ZMod.stdAddChar (c + d)‖ ≤
      ‖ZMod.stdAddChar a - ZMod.stdAddChar c‖ + ‖ZMod.stdAddChar b - ZMod.stdAddChar d‖ := by
  calc
    _ = ‖(ZMod.stdAddChar a - ZMod.stdAddChar c) * ZMod.stdAddChar b +
        ZMod.stdAddChar c * (ZMod.stdAddChar b - ZMod.stdAddChar d)‖ := by
      simp only [AddChar.map_add_eq_mul]
      congr 1
      ring
    _ ≤ _ := by
      simpa only [norm_mul, norm_stdAddChar b, norm_stdAddChar c, one_mul, mul_one] using norm_add_le
        ((ZMod.stdAddChar a - ZMod.stdAddChar c) * ZMod.stdAddChar b)
        (ZMod.stdAddChar c * (ZMod.stdAddChar b - ZMod.stdAddChar d))

private lemma norm_char_nsmul_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Γ : Finset (G × ZMod M)) (k x₀ : ZMod M) {r : ℝ}
    (hΓ : ∀ a ∈ Γ, ‖ZMod.stdAddChar (k * a.2) - ZMod.stdAddChar (k * x₀)‖ ≤ r)
    (m : ℕ) {z : G × ZMod M} (hz : z ∈ m • Γ) :
    ‖ZMod.stdAddChar (k * z.2) - ZMod.stdAddChar (k * (m • x₀))‖ ≤ (m : ℝ) * r := by
  induction m generalizing z with
  | zero =>
    have hz0 : z = 0 := by simpa only [zero_nsmul, Finset.mem_zero] using hz
    subst z
    simp
  | succ m ih =>
    rw [succ_nsmul] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    simp only [Prod.snd_add, succ_nsmul, mul_add]
    calc
      _ ≤ ‖ZMod.stdAddChar (k * a.2) - ZMod.stdAddChar (k * (m • x₀))‖ +
          ‖ZMod.stdAddChar (k * b.2) - ZMod.stdAddChar (k * x₀)‖ :=
        norm_stdAddChar_add_sub_le _ _ _ _
      _ ≤ (m : ℝ) * r + r := add_le_add (ih ha) (hΓ b hb)
      _ = _ := by push_cast; ring

private lemma norm_char_nsmul_sub_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Γ : Finset (G × ZMod M)) (k x₀ : ZMod M) {r : ℝ}
    (hΓ : ∀ a ∈ Γ, ‖ZMod.stdAddChar (k * a.2) - ZMod.stdAddChar (k * x₀)‖ ≤ r)
    (m : ℕ) {z : G × ZMod M} (hz : z ∈ (m • Γ) - (m • Γ)) :
    ‖ZMod.stdAddChar (k * z.2) - 1‖ ≤ 2 * (m : ℝ) * r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
  rw [Prod.snd_sub, mul_sub, norm_stdAddChar_sub_one]
  calc
    _ ≤ ‖ZMod.stdAddChar (k * a.2) - ZMod.stdAddChar (k * (m • x₀))‖ +
        ‖ZMod.stdAddChar (k * b.2) - ZMod.stdAddChar (k * (m • x₀))‖ := by
      simpa only [Complex.dist_eq] using dist_triangle_right (ZMod.stdAddChar (k * a.2))
        (ZMod.stdAddChar (k * b.2)) (ZMod.stdAddChar (k * (m • x₀)))
    _ ≤ (m : ℝ) * r + (m : ℝ) * r := add_le_add (norm_char_nsmul_le Γ k x₀ hΓ m ha)
      (norm_char_nsmul_le Γ k x₀ hΓ m hb)
    _ = _ := by ring

end CharacterBounds

section VerticalThinning

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
private lemma fst_injOn_phaseGraph (J : Finset (ZMod M)) (ξ : ZMod M → ZMod M) :
    Set.InjOn Prod.fst (phaseGraph J ξ : Set (ZMod M × ZMod M)) := by
  intro a ha b hb he
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
  exact congrArg (fun z => (z, ξ z)) he

private lemma nsmul_finset_mono {G : Type*} [AddMonoid G] [DecidableEq G]
    {A B : Finset G} (h : A ⊆ B) (n : ℕ) : n • A ⊆ n • B := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, succ_nsmul]
    exact Finset.add_subset_add ih h

private noncomputable def nonzeroVertical (Γ : Finset (ZMod M × ZMod M)) :
    Finset (ZMod M) :=
  ((((6 : ℕ) • Γ - (6 : ℕ) • Γ).filter (fun p => p.1 = 0)).image Prod.snd).erase 0

private lemma card_nonzeroVertical_le {J : Finset (ZMod M)} (hJ : J.Nonempty)
    (ξ : ZMod M → ZMod M) :
    let Γ := phaseGraph J ξ
    ((nonzeroVertical Γ).card : ℚ≥0) ≤ (((Γ - Γ).card : ℚ≥0) / Γ.card) ^ (13 : ℕ) := by
  let Γ := phaseGraph J ξ
  let F := (((6 : ℕ) • Γ - (6 : ℕ) • Γ).filter (fun p => p.1 = 0))
  have h : (nonzeroVertical Γ).card ≤ F.card :=
    (Finset.card_erase_le.trans Finset.card_image_le)
  have hcast : ((nonzeroVertical Γ).card : ℚ≥0) ≤ F.card := by exact_mod_cast h
  have hΓ : Γ.Nonempty := by
    rw [← Finset.card_pos, card_phaseGraph]
    exact hJ.card_pos
  exact hcast.trans (card_vertical_fibre_le Γ hΓ (fst_injOn_phaseGraph J ξ) 6 6 0)

private lemma two_pow_log2_succ_bounds (q : ℕ) :
    q < 2 ^ ((q + 1).log2 + 1) ∧ 2 ^ ((q + 1).log2 + 1) ≤ 2 * (q + 1) := by
  refine ⟨(Nat.lt_succ_self q).trans (Nat.lt_log2_self (n := q + 1)), ?_⟩
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.log2_self_le (Nat.succ_ne_zero q))

private lemma thin_graph_without_vertical {J : Finset (ZMod M)} (hJ : J.Nonempty)
    (ξ : ZMod M → ZMod M) :
    ∃ J' : Finset (ZMod M), J'.Nonempty ∧ J' ⊆ J ∧
      J.card ≤ (2 * ((nonzeroVertical (phaseGraph J ξ)).card + 1)) ^ 30 * J'.card ∧
      ∀ w ∈ (6 : ℕ) • phaseGraph J' ξ - (6 : ℕ) • phaseGraph J' ξ,
        w.1 = 0 → w.2 = 0 := by
  classical
  let Γ := phaseGraph J ξ
  let V := nonzeroVertical Γ
  let m := (V.card + 1).log2 + 1
  have hV : 0 ∉ V := Finset.notMem_erase _ _
  have hm := two_pow_log2_succ_bounds V.card
  obtain ⟨ks, hks, hsep⟩ := exists_separating_multipliers V hV m hm.1
  obtain ⟨J', hsub, hcard, hbins⟩ := exists_simultaneous_phase_bins J ξ ks
  have hJ' : J'.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, mul_zero] at hcard
    exact (Nat.not_le_of_lt hJ.card_pos) hcard
  have hpow : 32768 ^ ks.length ≤ (2 * (V.card + 1)) ^ 30 := by
    calc
      _ ≤ 32768 ^ (2 * m) := Nat.pow_le_pow_right (by decide) hks
      _ = (2 ^ m) ^ 30 := by
        calc
          _ = ((2 : ℕ) ^ 15) ^ (2 * m) := by norm_num
          _ = _ := by simp only [← pow_mul]; congr 1; omega
      _ ≤ _ := Nat.pow_le_pow_left hm.2 _
  refine ⟨J', hJ', hsub, hcard.trans (Nat.mul_le_mul_right _ hpow), ?_⟩
  intro w hw hwfirst
  by_contra hnonzero
  let Γ' := phaseGraph J' ξ
  have hΓ' : Γ' ⊆ Γ := Finset.image_subset_image hsub
  have hwQ : w ∈ (6 : ℕ) • Γ - (6 : ℕ) • Γ :=
    Finset.sub_subset_sub (nsmul_finset_mono hΓ' 6) (nsmul_finset_mono hΓ' 6) hw
  have hwV : w.2 ∈ V := by
    apply Finset.mem_erase.mpr
    exact ⟨hnonzero, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hwQ, hwfirst⟩)⟩
  obtain ⟨k, hk, hksep⟩ := hsep w.2 hwV
  obtain ⟨a₀, ha₀⟩ := hJ'
  have hΓclose : ∀ p ∈ Γ', ‖ZMod.stdAddChar (k * p.2) -
      ZMod.stdAddChar (k * ξ a₀)‖ ≤ 1 / 32 := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact hbins k hk a ha a₀ ha₀
  have hnorm := norm_char_nsmul_sub_le Γ' k (ξ a₀) hΓclose 6 hw
  have hre := Complex.abs_re_le_norm (ZMod.stdAddChar (k * w.2) - 1)
  rw [Complex.sub_re, Complex.one_re, abs_le] at hre
  norm_num at hnorm
  linarith only [hre.1, hnorm, hksep]

end VerticalThinning

section LocalFrequencies

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
private lemma projection_phaseGraph (J : Finset (ZMod M)) (ξ : ZMod M → ZMod M) :
    (phaseGraph J ξ).image (AddMonoidHom.fst (ZMod M) (ZMod M)) = J := by
  unfold phaseGraph
  rw [Finset.image_image]
  simp [Function.comp_def]

private lemma triple_difference_subset {G : Type*} [DecidableEq G] [AddCommGroup G]
    (A : Finset G) :
    ((2 : ℕ) • A - (2 : ℕ) • A) + ((2 : ℕ) • A - (2 : ℕ) • A) -
      ((2 : ℕ) • A - (2 : ℕ) • A) ⊆ ((6 : ℕ) • A - (6 : ℕ) • A) := by
  let P := (2 : ℕ) • A
  have hsum {x y z : G} (hx : x ∈ P) (hy : y ∈ P) (hz : z ∈ P) : x + y + z ∈ (6 : ℕ) • A := by
    have he : P + P + P = (6 : ℕ) • A := by
      unfold P
      rw [← add_nsmul, ← add_nsmul]
    rw [← he]
    exact Finset.add_mem_add (Finset.add_mem_add hx hy) hz
  intro x hx
  change x ∈ (P - P) + (P - P) - (P - P) at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_sub.mp hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Finset.mem_add.mp hy
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := Finset.mem_sub.mp hx₁
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := Finset.mem_sub.mp hx₂
  obtain ⟨a₃, ha₃, b₃, hb₃, rfl⟩ := Finset.mem_sub.mp hz
  exact Finset.mem_sub.mpr ⟨_, hsum ha₁ ha₂ hb₃, _, hsum hb₁ hb₂ ha₃, by abel⟩

omit [NeZero M] in
private lemma exists_additive_frequency_extension {J : Finset (ZMod M)} (hJ : J.Nonempty)
    (ξ : ZMod M → ZMod M)
    (hzero : ∀ w ∈ (6 : ℕ) • phaseGraph J ξ - (6 : ℕ) • phaseGraph J ξ,
      w.1 = 0 → w.2 = 0) :
    ∃ φ : ZMod M → ZMod M,
      (∀ a ∈ J, ∀ b ∈ J, φ (a - b) = ξ a - ξ b) ∧
      ∀ x ∈ (2 : ℕ) • J - (2 : ℕ) • J, ∀ y ∈ (2 : ℕ) • J - (2 : ℕ) • J,
        x + y ∈ (2 : ℕ) • J - (2 : ℕ) • J → φ (x + y) = φ x + φ y := by
  let Γ := phaseGraph J ξ
  let P := (2 : ℕ) • Γ
  let D := P - P
  let Q := (6 : ℕ) • Γ - (6 : ℕ) • Γ
  obtain ⟨a₀, ha₀⟩ := hJ
  let γ₀ : ZMod M × ZMod M := (a₀, ξ a₀)
  have hγ₀ : γ₀ ∈ Γ := Finset.mem_image_of_mem _ ha₀
  have hmemP (g : ZMod M × ZMod M) (hg : g ∈ Γ) : g + γ₀ ∈ P := by
    unfold P
    rw [two_nsmul]
    exact Finset.add_mem_add hg hγ₀
  have hD₀ : 0 ∈ D := by
    simpa only [sub_self] using Finset.sub_mem_sub (hmemP γ₀ hγ₀) (hmemP γ₀ hγ₀)
  have hadd : D + D - D ⊆ Q := triple_difference_subset Γ
  have hsub : D - D ⊆ Q := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
    apply hadd
    simpa only [add_zero] using Finset.sub_mem_sub (Finset.add_mem_add ha hD₀) hb
  obtain ⟨φ, hφ, hlocal⟩ := exists_local_additive_graph D Q hadd hsub hzero
  have hprojection : D.image Prod.fst = (2 : ℕ) • J - (2 : ℕ) • J := by
    change ((2 : ℕ) • Γ - (2 : ℕ) • Γ).image
        (AddMonoidHom.fst (ZMod M) (ZMod M)) = _
    let π := AddMonoidHom.fst (ZMod M) (ZMod M)
    have hsub' (A B : Finset (ZMod M × ZMod M)) :
        (A - B).image π = A.image π - B.image π :=
      Finset.image_image₂_distrib (map_sub π)
    rw [hsub', Finset.image_nsmul, projection_phaseGraph]
  rw [hprojection] at hlocal
  refine ⟨φ, ?_, hlocal⟩
  intro a ha b hb
  have ha' : (a, ξ a) ∈ Γ := Finset.mem_image_of_mem _ ha
  have hb' : (b, ξ b) ∈ Γ := Finset.mem_image_of_mem _ hb
  have hw : (a, ξ a) - (b, ξ b) ∈ D := by
    simpa only [add_sub_add_right_eq_sub] using Finset.sub_mem_sub
      (hmemP (a, ξ a) ha') (hmemP (b, ξ b) hb')
  exact hφ _ hw

end LocalFrequencies

section Bogolyubov

variable {M : ℕ} [NeZero M]

private noncomputable def indicatorCyclic (J : Finset (ZMod M)) (x : ZMod M) : ℝ :=
  if x ∈ J then 1 else 0

private lemma sum_indicatorCyclic_pow (J : Finset (ZMod M)) {m : ℕ} (hm : m ≠ 0) :
    ∑ x, indicatorCyclic J x ^ m = (J.card : ℝ) := by
  classical
  calc
    _ = ∑ x : ZMod M, if x ∈ J then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ J <;> simp [indicatorCyclic, hx, hm]
    _ = _ := by rw [← Finset.sum_filter]; simp

private lemma fourier_indicatorCyclic_zero (J : Finset (ZMod M)) :
    fourier (indicatorCyclic J) 0 = ((J.card : ℝ) : ℂ) := by
  unfold fourier
  rw [ZMod.dft_apply_zero, ← Complex.ofReal_sum]
  congr 1
  simpa only [pow_one] using sum_indicatorCyclic_pow J (by decide : (1 : ℕ) ≠ 0)

private lemma sum_fourier_indicatorCyclic_sq (J : Finset (ZMod M)) :
    ∑ k, ‖fourier (indicatorCyclic J) k‖ ^ 2 = (M : ℝ) * (J.card : ℝ) := by
  rw [sum_sq_fourier, sum_indicatorCyclic_pow J (by decide : (2 : ℕ) ≠ 0)]

private lemma iteratedCorrelation_eq_fourierSum (g : ZMod M → ℝ) (t : ZMod M) :
    (M : ℂ) * (cyclicCorrelation (cyclicCorrelation g) t : ℂ) =
      ∑ k, ZMod.stdAddChar (k * t) * ((‖fourier g k‖ ^ 4 : ℝ) : ℂ) := by
  let T := cyclicCorrelation (cyclicCorrelation g)
  have hT (k : ZMod M) : fourier T k = ((‖fourier g k‖ ^ 4 : ℝ) : ℂ) := by
    unfold T
    rw [fourier_cyclicCorrelation, fourier_pair, fourier_cyclicCorrelation, fourier_pair,
      Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    congr 1
    ring
  have h := congrFun (ZMod.dft_dft (fun x => (T x : ℂ))) (-t)
  change ZMod.dft (fun k => fourier T k) (-t) = (M : ℂ) • (T (-(-t)) : ℂ) at h
  calc
    _ = ZMod.dft (fun k => fourier T k) (-t) := by
      simpa only [smul_eq_mul, neg_neg] using h.symm
    _ = _ := by simp only [ZMod.dft_apply, hT, mul_neg, neg_neg, smul_eq_mul]

private lemma exists_add_mem_of_corr_ne_zero {J : Finset (ZMod M)} {t : ZMod M}
    (h : cyclicCorrelation (indicatorCyclic J) t ≠ 0) :
    ∃ x ∈ J, x + t ∈ J := by
  unfold cyclicCorrelation at h
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨x, ?_, ?_⟩ <;> by_contra hbad <;> simp [indicatorCyclic, hbad] at hx

private lemma mem_double_difference_of_iteratedCorrelation_ne_zero {J : Finset (ZMod M)}
    {t : ZMod M} (h : cyclicCorrelation (cyclicCorrelation (indicatorCyclic J)) t ≠ 0) :
    t ∈ (2 : ℕ) • J - (2 : ℕ) • J := by
  unfold cyclicCorrelation at h
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h₁ : cyclicCorrelation (indicatorCyclic J) y ≠ 0 := left_ne_zero_of_mul hy
  have h₂ : cyclicCorrelation (indicatorCyclic J) (y + t) ≠ 0 := right_ne_zero_of_mul hy
  obtain ⟨a, ha, ha'⟩ := exists_add_mem_of_corr_ne_zero h₁
  obtain ⟨b, hb, hb'⟩ := exists_add_mem_of_corr_ne_zero h₂
  rw [two_nsmul]
  exact Finset.mem_sub.mpr ⟨_, Finset.add_mem_add hb' ha, _, Finset.add_mem_add hb ha', by abel⟩

private noncomputable def spectrumThreshold (J : Finset (ZMod M)) : ℝ :=
  (J.card : ℝ) ^ 3 / (2 * (M : ℝ))

private noncomputable def largeSpectrum (J : Finset (ZMod M)) : Finset (ZMod M) :=
  Finset.univ.filter (fun k => spectrumThreshold J ≤ ‖fourier (indicatorCyclic J) k‖ ^ 2)

private noncomputable def bohrSet (Ω : Finset (ZMod M)) (r : ℝ) : Finset (ZMod M) := by
  classical
  exact Finset.univ.filter (fun t => ∀ k ∈ Ω, ‖ZMod.stdAddChar (k * t) - 1‖ ≤ r)

private lemma mem_bohrSet {Ω : Finset (ZMod M)} {r : ℝ} {t : ZMod M} :
    t ∈ bohrSet Ω r ↔ ∀ k ∈ Ω, ‖ZMod.stdAddChar (k * t) - 1‖ ≤ r := by
  classical
  simp [bohrSet]

private lemma zero_mem_largeSpectrum (J : Finset (ZMod M)) : 0 ∈ largeSpectrum J := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hJ : (J.card : ℝ) ≤ M := by
    exact_mod_cast (Finset.card_le_univ J).trans_eq (ZMod.card M)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [fourier_indicatorCyclic_zero, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    spectrumThreshold, div_le_iff₀ (by positivity)]
  have hm := mul_le_mul_of_nonneg_right (show (J.card : ℝ) ≤ 2 * M by linarith) (sq_nonneg (J.card : ℝ))
  linarith only [hm]

private lemma card_largeSpectrum_bound {J : Finset (ZMod M)} (hJ : J.Nonempty) :
    ((largeSpectrum J).card : ℝ) * (J.card : ℝ) ^ 2 ≤ 2 * (M : ℝ) ^ 2 := by
  let Ω := largeSpectrum J
  let n : ℝ := J.card
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast hJ.card_pos
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have h : (Ω.card : ℝ) * spectrumThreshold J ≤ (M : ℝ) * n := by
    calc
      _ = ∑ _ ∈ Ω, spectrumThreshold J := by simp
      _ ≤ ∑ k ∈ Ω, ‖fourier (indicatorCyclic J) k‖ ^ 2 :=
        Finset.sum_le_sum fun k hk => (Finset.mem_filter.mp hk).2
      _ ≤ ∑ k, ‖fourier (indicatorCyclic J) k‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
      _ = _ := sum_fourier_indicatorCyclic_sq J
  have hτ : spectrumThreshold J * (2 * (M : ℝ)) = n ^ 3 := by
    unfold spectrumThreshold
    exact div_mul_cancel₀ _ (by positivity)
  change (Ω.card : ℝ) * n ^ 2 ≤ _
  refine le_of_mul_le_mul_right ?_ hn
  calc
    _ = ((Ω.card : ℝ) * spectrumThreshold J) * (2 * (M : ℝ)) := by
      rw [mul_assoc _ (spectrumThreshold J), hτ]
      ring
    _ ≤ ((M : ℝ) * n) * (2 * (M : ℝ)) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by ring

private lemma bohr_largeSpectrum_subset_double_difference {J : Finset (ZMod M)} (hJ : J.Nonempty) :
    bohrSet (largeSpectrum J) (1 / 2) ⊆ (2 : ℕ) • J - (2 : ℕ) • J := by
  classical
  let Ω := largeSpectrum J
  let g := indicatorCyclic J
  let n : ℝ := J.card
  let W (k : ZMod M) := ‖fourier g k‖ ^ 4
  let τ := spectrumThreshold J
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast hJ.card_pos
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hW (k : ZMod M) : 0 ≤ W k := by dsimp [W]; positivity
  intro t ht
  have hnear : ∀ k ∈ Ω, ‖ZMod.stdAddChar (k * t) - 1‖ ≤ 1 / 2 := mem_bohrSet.mp ht
  have htail : (∑ k, if k ∈ Ω then 0 else W k) ≤ n ^ 4 / 2 := by
    calc
      _ ≤ ∑ k, τ * ‖fourier g k‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        by_cases hk : k ∈ Ω
        · rw [if_pos hk]
          unfold τ spectrumThreshold
          positivity
        · rw [if_neg hk]
          have hs : ‖fourier g k‖ ^ 2 ≤ τ := by
            apply le_of_not_ge
            intro hi
            exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
          change ‖fourier g k‖ ^ 4 ≤ _
          calc
            _ = ‖fourier g k‖ ^ 2 * ‖fourier g k‖ ^ 2 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = τ * ((M : ℝ) * n) := by rw [← Finset.mul_sum, sum_fourier_indicatorCyclic_sq]
      _ = _ := by
        unfold τ spectrumThreshold n
        field_simp
  have hweighted (k : ZMod M) :
      (if k = 0 then n ^ 4 else 0) - (if k ∈ Ω then 0 else W k) ≤
        (ZMod.stdAddChar (k * t)).re * W k := by
    have habs := Complex.abs_re_le_norm (ZMod.stdAddChar (k * t))
    rw [norm_stdAddChar, abs_le] at habs
    by_cases hzero : k = 0
    · subst k
      have hΩ₀ : (0 : ZMod M) ∈ Ω := zero_mem_largeSpectrum J
      simp only [ite_true, if_pos hΩ₀, sub_zero, zero_mul,
        AddChar.map_zero_eq_one, Complex.one_re, one_mul, W, g, fourier_indicatorCyclic_zero,
        Complex.norm_real, Real.norm_of_nonneg hn.le, n]
      exact le_rfl
    rw [if_neg hzero]
    by_cases hk : k ∈ Ω
    · rw [if_pos hk, sub_zero]
      have hb := Complex.abs_re_le_norm (ZMod.stdAddChar (k * t) - 1)
      rw [Complex.sub_re, Complex.one_re, abs_le] at hb
      exact mul_nonneg (by linarith only [hb.1, hnear k hk]) (hW k)
    · rw [if_neg hk, zero_sub, ← neg_one_mul]
      exact mul_le_mul_of_nonneg_right habs.1 (hW k)
  have hsum : n ^ 4 - (∑ k, if k ∈ Ω then 0 else W k) ≤
      ∑ k, (ZMod.stdAddChar (k * t)).re * W k := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hweighted k)
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h
    exact h
  have hreal : (M : ℝ) * cyclicCorrelation (cyclicCorrelation g) t =
      ∑ k, (ZMod.stdAddChar (k * t)).re * W k := by
    have h := congrArg Complex.re (iteratedCorrelation_eq_fourierSum g t)
    simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, W] using h
  rw [← hreal] at hsum
  apply mem_double_difference_of_iteratedCorrelation_ne_zero
  intro he
  change cyclicCorrelation (cyclicCorrelation g) t = 0 at he
  rw [he, mul_zero] at hsum
  linarith only [htail, hsum, pow_pos hn 4]

private lemma bohrSet_nonempty (Ω : Finset (ZMod M)) {r : ℝ} (hr : 0 ≤ r) :
    (bohrSet Ω r).Nonempty := by
  refine ⟨0, mem_bohrSet.mpr fun k _ => ?_⟩
  simpa only [mul_zero, AddChar.map_zero_eq_one, sub_self, norm_zero] using hr

private lemma bohrSet_card_lower (Ω : Finset (ZMod M)) {r : ℝ} (hr : 1 / 32 ≤ r) :
    M ≤ 32768 ^ Ω.card * (bohrSet Ω r).card := by
  classical
  obtain ⟨A, _, hA, hclose⟩ := exists_simultaneous_phase_bins
    (Finset.univ : Finset (ZMod M)) id Ω.toList
  rw [Finset.card_univ, ZMod.card, Finset.length_toList] at hA
  have hA' : A.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty, mul_zero] at hA
    exact (NeZero.ne M) (Nat.eq_zero_of_le_zero hA)
  obtain ⟨a₀, ha₀⟩ := hA'
  have hcard : A.card ≤ (bohrSet Ω r).card := by
    refine Finset.card_le_card_of_injOn (fun a => a - a₀) ?_ ?_
    · intro a ha
      apply mem_bohrSet.mpr
      intro k hk
      rw [mul_sub, norm_stdAddChar_sub_one]
      exact (hclose k (Finset.mem_toList.mpr hk) a ha a₀ ha₀).trans hr
    · intro x _ y _ h
      exact sub_left_injective h
  exact hA.trans (Nat.mul_le_mul_left _ hcard)

private lemma diff_mem_bohrSet {Ω : Finset (ZMod M)} {r s : ℝ} {a b : ZMod M}
    (ha : a ∈ bohrSet Ω r) (hb : b ∈ bohrSet Ω s) :
    a - b ∈ bohrSet Ω (r + s) := by
  apply mem_bohrSet.mpr
  intro k hk
  rw [mul_sub, norm_stdAddChar_sub_one]
  calc
    _ ≤ ‖ZMod.stdAddChar (k * a) - 1‖ + ‖ZMod.stdAddChar (k * b) - 1‖ := by
      simpa only [Complex.dist_eq] using dist_triangle_right (ZMod.stdAddChar (k * a))
        (ZMod.stdAddChar (k * b)) (1 : ℂ)
    _ ≤ _ := add_le_add (mem_bohrSet.mp ha _ hk) (mem_bohrSet.mp hb _ hk)

private noncomputable def translatedSlice (J B : Finset (ZMod M)) (s : ZMod M) :
    Finset (ZMod M) :=
  J.filter (fun a => a - s ∈ B)

private lemma sum_card_translatedSlice (J B : Finset (ZMod M)) :
    ∑ s, (translatedSlice J B s).card = J.card * B.card := by
  classical
  let U : Finset (ZMod M) := Finset.univ
  let R (a s : ZMod M) := a - s ∈ B
  have hL (a : ZMod M) : (leftNeighbors U (fun s a => R a s) a).card = B.card := by
    refine Finset.card_bij (fun s _ => a - s) ?_ ?_ ?_
    · intro s hs
      exact (mem_leftNeighbors.mp hs).2
    · intro s _ s' _ he
      exact sub_right_injective he
    · intro b hb
      have he : a - (a - b) = b := by abel
      refine ⟨a - b, ?_, he⟩
      refine mem_leftNeighbors.mpr ⟨Finset.mem_univ _, ?_⟩
      change a - (a - b) ∈ B
      rwa [he]
  have hR (s : ZMod M) : leftNeighbors J R s = translatedSlice J B s := by
    ext a
    simp only [leftNeighbors, translatedSlice, R, Finset.mem_filter]
  have hLeft := card_relPairs_eq_sum_left J U R
  have hRight := card_relPairs_eq_sum_right J U R
  simp only [hL, Finset.sum_const, smul_eq_mul] at hLeft
  simp only [hR] at hRight
  exact hRight.symm.trans hLeft

private lemma exists_large_translatedSlice (J B : Finset (ZMod M)) :
    ∃ s, J.card * B.card ≤ M * (translatedSlice J B s).card := by
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod M))
    (fun s => (translatedSlice J B s).card) Finset.univ_nonempty
  refine ⟨s, ?_⟩
  calc
    _ = ∑ t, (translatedSlice J B t).card := (sum_card_translatedSlice J B).symm
    _ ≤ ∑ _ : ZMod M, (translatedSlice J B s).card := Finset.sum_le_sum hs
    _ = _ := by simp [ZMod.card]


end Bogolyubov

private noncomputable def differenceRatioBound (δ : ℝ) : ℝ :=
  ((graphRate δ / 8) * ((graphRate δ / 2) ^ 9 / 65536))⁻¹

private noncomputable def graphDensityRate (δ : ℝ) : ℝ :=
  graphRate δ * δ / (48 * (2 * (differenceRatioBound δ ^ 13 + 1)) ^ 30)

private lemma graphDensityRate_pos {δ : ℝ} (hδ : 0 < δ) : 0 < graphDensityRate δ := by
  unfold graphDensityRate differenceRatioBound graphRate
  positivity

private lemma large_cube_has_local_frequency_extension {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) (habs : ∀ x, |f x| ≤ 1)
    (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) (hlarge : δ * (N : ℝ) ^ 4 ≤ cubeSum N f) :
    ∃ J : Finset (ZMod (2 * N + 1)), ∃ ξ φ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
      J.Nonempty ∧ graphDensityRate δ * (N : ℝ) ≤ (J.card : ℝ) ∧
        (∀ a ∈ J, Real.sqrt (δ / 6) * (N : ℝ) ≤
          ‖fourier (cyclicDerivative (periodize N f) a) (ξ a)‖) ∧
        (∀ a ∈ J, ∀ b ∈ J, φ (a - b) = ξ a - ξ b) ∧
        (∀ x ∈ (2 : ℕ) • J - (2 : ℕ) • J, ∀ y ∈ (2 : ℕ) • J - (2 : ℕ) • J,
          x + y ∈ (2 : ℕ) • J - (2 : ℕ) • J → φ (x + y) = φ x + φ y) := by
  classical
  obtain ⟨J, ξ, hcard, hξ, hdiff⟩ := large_cube_has_small_difference_graph hf habs hN hδ hlarge
  let Γ := phaseGraph J ξ
  let V := nonzeroVertical Γ
  let τ := (graphRate δ / 8) * ((graphRate δ / 2) ^ 9 / 65536)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hrate : 0 < graphRate δ := by unfold graphRate; positivity
  have hτ : 0 < τ := by unfold τ; positivity
  have hcardpos : 0 < (J.card : ℝ) := (by positivity : 0 < graphRate δ * δ * (N : ℝ) / 48).trans_le hcard
  have hJ : J.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcardpos)
  have hΓcard : Γ.card = J.card := card_phaseGraph J ξ
  have hΓden : (0 : ℝ) < Γ.card := by rwa [hΓcard]
  have hratio : ((Γ - Γ).card : ℝ) / Γ.card ≤ differenceRatioBound δ := by
    change _ ≤ τ⁻¹
    rw [← one_div, div_le_div_iff₀ hΓden hτ, one_mul, hΓcard, mul_comm _ τ]
    exact hdiff
  have hVq := card_nonzeroVertical_le hJ ξ
  change (V.card : ℚ≥0) ≤ (((Γ - Γ).card : ℚ≥0) / Γ.card) ^ (13 : ℕ) at hVq
  have hVr : (V.card : ℝ) ≤ (((Γ - Γ).card : ℝ) / Γ.card) ^ 13 := by
    simpa only [NNRat.cast_pow, NNRat.cast_div, NNRat.cast_natCast] using
      (NNRat.cast_mono (K := ℝ) hVq)
  have hV : (V.card : ℝ) ≤ differenceRatioBound δ ^ 13 :=
    hVr.trans (pow_le_pow_left₀ (by positivity) hratio _)
  obtain ⟨J', hJ', hsub, hthin, hzero⟩ := thin_graph_without_vertical hJ ξ
  obtain ⟨φ, hφ, hadd⟩ := exists_additive_frequency_extension hJ' ξ hzero
  refine ⟨J', ξ, φ, hJ', ?_, fun a ha => hξ a (hsub ha), hφ, hadd⟩
  let loss := (2 * (differenceRatioBound δ ^ 13 + 1)) ^ 30
  have hloss : 0 < loss := by
    unfold loss differenceRatioBound
    positivity
  have hh : (J.card : ℝ) ≤ ((2 * ((V.card : ℝ) + 1)) ^ 30) * (J'.card : ℝ) := by
    exact_mod_cast hthin
  have hh' : (J.card : ℝ) ≤ loss * (J'.card : ℝ) := by
    refine hh.trans ?_
    unfold loss
    gcongr
  apply le_of_mul_le_mul_left _ hloss
  calc
    _ = graphRate δ * δ * (N : ℝ) / 48 := by
      unfold graphDensityRate
      change loss * (graphRate δ * δ / (48 * loss) * (N : ℝ)) = _
      field_simp
    _ ≤ _ := hcard.trans hh'

private def LocalFrequencyStructure (N : ℕ) (δ : ℝ) (f : ℤ → ℝ) : Prop :=
  ∃ Ω J : Finset (ZMod (2 * N + 1)), ∃ ξ φ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
    J.Nonempty ∧
    (Ω.card : ℝ) * graphDensityRate δ ^ 2 ≤ 18 ∧
    2 * N + 1 ≤ 32768 ^ Ω.card * (bohrSet Ω (1 / 4)).card ∧
    (graphDensityRate δ / 3) * ((bohrSet Ω (1 / 4)).card : ℝ) ≤ (J.card : ℝ) ∧
    (∀ a ∈ J, Real.sqrt (δ / 6) * (N : ℝ) ≤
      ‖fourier (cyclicDerivative (periodize N f) a) (ξ a)‖) ∧
    (∀ a ∈ J, ∀ b ∈ J, a - b ∈ bohrSet Ω (1 / 2) ∧ φ (a - b) = ξ a - ξ b) ∧
    (∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b)

private lemma large_cube_has_local_frequency_structure {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) (habs : ∀ x, |f x| ≤ 1)
    (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) (hlarge : δ * (N : ℝ) ^ 4 ≤ cubeSum N f) :
    LocalFrequencyStructure N δ f := by
  classical
  obtain ⟨J, ξ, φ, hJ, hsize, hξ, hφ, hadd⟩ :=
    large_cube_has_local_frequency_extension hf habs hN hδ hlarge
  let M := 2 * N + 1
  let rate := graphDensityRate δ
  let Ω := largeSpectrum J
  let B := bohrSet Ω (1 / 4)
  let B' := bohrSet Ω (1 / 2)
  have hB : B.Nonempty := bohrSet_nonempty Ω (by norm_num)
  have hB' := bohr_largeSpectrum_subset_double_difference hJ
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hMpos : (0 : ℝ) < M := by dsimp [M]; positivity
  have hMle : (M : ℝ) ≤ 3 * (N : ℝ) := by dsimp only [M]; push_cast; linarith
  have hrate : 0 < rate := graphDensityRate_pos hδ
  have hΩ : (Ω.card : ℝ) * rate ^ 2 ≤ 18 := by
    refine le_of_mul_le_mul_right ?_ (sq_pos_of_pos hNpos)
    calc
      _ = (Ω.card : ℝ) * (rate * (N : ℝ)) ^ 2 := by ring
      _ ≤ (Ω.card : ℝ) * (J.card : ℝ) ^ 2 := by gcongr
      _ ≤ 2 * (M : ℝ) ^ 2 := card_largeSpectrum_bound hJ
      _ ≤ 2 * (3 * (N : ℝ)) ^ 2 := by gcongr
      _ = _ := by ring
  obtain ⟨s, hs⟩ := exists_large_translatedSlice J B
  let T := translatedSlice J B s
  have hs' : (J.card : ℝ) * (B.card : ℝ) ≤ (M : ℝ) * (T.card : ℝ) := by
    dsimp only [M, T]
    exact_mod_cast hs
  have hT : (rate / 3) * (B.card : ℝ) ≤ (T.card : ℝ) := by
    refine le_of_mul_le_mul_right ?_ hMpos
    calc
      _ ≤ (rate / 3) * (B.card : ℝ) * (3 * (N : ℝ)) := by gcongr
      _ = (rate * (N : ℝ)) * (B.card : ℝ) := by ring
      _ ≤ (J.card : ℝ) * (B.card : ℝ) := by gcongr
      _ ≤ (M : ℝ) * (T.card : ℝ) := hs'
      _ = _ := mul_comm _ _
  have hTne : T.Nonempty := by
    have hcard : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
    apply Finset.card_pos.mp
    exact_mod_cast ((by positivity : 0 < (rate / 3) * (B.card : ℝ)).trans_le hT)
  have hTsub : T ⊆ J := Finset.filter_subset _ _
  refine ⟨Ω, T, ξ, φ, hTne, hΩ, bohrSet_card_lower Ω (by norm_num), hT,
    fun a ha => hξ a (hTsub ha), ?_, ?_⟩
  · intro a ha b hb
    refine ⟨?_, hφ a (hTsub ha) b (hTsub hb)⟩
    have hd := diff_mem_bohrSet (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    have he : (a - s) - (b - s) = a - b := by abel
    rw [he, show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num] at hd
    exact hd
  · intro a ha b hb hab
    exact hadd a (hB' ha) b (hB' hb) (hB' hab)

section CyclicLift

private def cyclicLift (N : ℕ) (S : Finset ℕ) : Finset (ZMod (2 * N + 1)) :=
  S.image (fun x : ℕ => (x : ZMod (2 * N + 1)))

private lemma val_of_interval_cast {N a : ℕ} (ha : a ∈ Finset.Icc 1 N) :
    (a : ZMod (2 * N + 1)).val = a := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  have h := (Finset.mem_Icc.mp ha).2
  omega

private lemma nat_mem_cyclicLift_iff {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) {z : ZMod (2 * N + 1)} :
    z ∈ cyclicLift N S ↔ z.val ∈ S := by
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rwa [val_of_interval_cast (hS hx)]
  · intro hz
    exact Finset.mem_image.mpr ⟨z.val, hz, z.natCast_zmod_val⟩

private lemma card_cyclicLift {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N) :
    (cyclicLift N S).card = S.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb h
  have he := congrArg ZMod.val h
  simpa only [val_of_interval_cast (hS ha), val_of_interval_cast (hS hb)] using he

private lemma periodic_balanced_eq_indicators {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N) :
    periodize N (balanced N S) = fun z => indicatorCyclic (cyclicLift N S) z -
      density N S * indicatorCyclic (cyclicLift N (Finset.Icc 1 N)) z := by
  funext z
  change (if 0 < (z.val : ℤ) ∧ (z.val : ℤ).toNat ∈ S then (1 : ℝ) else 0) -
    (if 0 < (z.val : ℤ) ∧ (z.val : ℤ) ≤ (N : ℤ) then density N S else 0) = _
  have hmem : (0 < (z.val : ℤ) ∧ (z.val : ℤ).toNat ∈ S) ↔ z ∈ cyclicLift N S := by
    rw [nat_mem_cyclicLift_iff hS, Int.toNat_natCast]
    exact ⟨And.right, fun h => ⟨by have h' := (Finset.mem_Icc.mp (hS h)).1; omega, h⟩⟩
  have hI : (0 < (z.val : ℤ) ∧ (z.val : ℤ) ≤ (N : ℤ)) ↔ z ∈ cyclicLift N (Finset.Icc 1 N) := by
    rw [nat_mem_cyclicLift_iff (fun _ h => h), Finset.mem_Icc]
    omega
  simp only [hmem, hI, indicatorCyclic, mul_ite, mul_one, mul_zero]

private lemma sum_periodic_balanced_eq_zero {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hN : 1 ≤ N) :
    ∑ z, periodize N (balanced N S) z = 0 := by
  have hsum (J : Finset (ZMod (2 * N + 1))) : ∑ z, indicatorCyclic J z = (J.card : ℝ) := by
    simpa only [pow_one] using sum_indicatorCyclic_pow J (by decide : (1 : ℕ) ≠ 0)
  have hNr : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  rw [periodic_balanced_eq_indicators hS, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, hsum,
    card_cyclicLift hS, card_cyclicLift (Finset.Subset.refl _)]
  simp only [Nat.card_Icc, Nat.add_sub_cancel, density]
  rw [div_mul_cancel₀ _ hNr, sub_self]

private lemma cyclicLift_no_four_ap {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : ∀ a d : ℕ, 0 < d → a ∈ S → a + d ∈ S → a + 2 * d ∈ S →
      a + 3 * d ∈ S → False)
    {a d : ZMod (2 * N + 1)} (hd : d ≠ 0)
    (h₀ : a ∈ cyclicLift N S) (h₁ : a + d ∈ cyclicLift N S)
    (h₂ : a + 2 * d ∈ cyclicLift N S) (h₃ : a + 3 * d ∈ cyclicLift N S) : False := by
  obtain ⟨x₀, hx₀, hx₀a⟩ := Finset.mem_image.mp h₀
  obtain ⟨x₁, hx₁, hx₁a⟩ := Finset.mem_image.mp h₁
  obtain ⟨x₂, hx₂, hx₂a⟩ := Finset.mem_image.mp h₂
  obtain ⟨x₃, hx₃, hx₃a⟩ := Finset.mem_image.mp h₃
  let r := (x₁ : ℤ) - x₀
  have hdiff {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) : (y : ℤ) - x ∈ shifts N := by
    have hxb := Finset.mem_Icc.mp (hS hx)
    have hyb := Finset.mem_Icc.mp (hS hy)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hr : (r : ZMod (2 * N + 1)) = d := by
    simp only [r, Int.cast_sub, Int.cast_natCast, hx₀a, hx₁a]
    ring
  have hr₂ : (((x₂ : ℤ) - x₁ : ℤ) : ZMod (2 * N + 1)) = d := by
    simp only [Int.cast_sub, Int.cast_natCast, hx₂a, hx₁a]
    ring
  have hr₃ : (((x₃ : ℤ) - x₂ : ℤ) : ZMod (2 * N + 1)) = d := by
    simp only [Int.cast_sub, Int.cast_natCast, hx₃a, hx₂a]
    ring
  have hstep₂ : (x₂ : ℤ) - x₁ = r :=
    shiftCast_inj (hdiff hx₁ hx₂) (hdiff hx₀ hx₁) (hr₂.trans hr.symm)
  have hstep₃ : (x₃ : ℤ) - x₂ = r :=
    shiftCast_inj (hdiff hx₂ hx₃) (hdiff hx₀ hx₁) (hr₃.trans hr.symm)
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hr
    exact hd hr.symm
  by_cases hrpos : 0 < r
  · have h0 : (x₁ : ℤ) - x₀ = r := rfl
    refine hfree x₀ r.toNat (by omega) hx₀ ?_ ?_ ?_
    · rwa [show x₀ + r.toNat = x₁ by omega]
    · rwa [show x₀ + 2 * r.toNat = x₂ by omega]
    · rwa [show x₀ + 3 * r.toNat = x₃ by omega]
  · have h0 : (x₁ : ℤ) - x₀ = r := rfl
    refine hfree x₃ (-r).toNat (by omega) hx₃ ?_ ?_ ?_
    · rwa [show x₃ + (-r).toNat = x₂ by omega]
    · rwa [show x₃ + 2 * (-r).toNat = x₁ by omega]
    · rwa [show x₃ + 3 * (-r).toNat = x₀ by omega]

private lemma cyclic_four_ap_sum_of_free {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N)
    (hfree : ∀ a d : ℕ, 0 < d → a ∈ S → a + d ∈ S → a + 2 * d ∈ S →
      a + 3 * d ∈ S → False) :
    let g := indicatorCyclic (cyclicLift N S)
    ∑ a, ∑ d, g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) = (S.card : ℝ) := by
  dsimp only
  let L := cyclicLift N S
  let g := indicatorCyclic L
  have hterm (a d : ZMod (2 * N + 1)) :
      g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) =
        if d = 0 then g a ^ 4 else 0 := by
    by_cases hd : d = 0
    · subst d
      simp only [ite_true, mul_zero, add_zero]
      ring
    rw [if_neg hd]
    by_cases h₀ : a ∈ L <;> by_cases h₁ : a + d ∈ L <;>
    by_cases h₂ : a + 2 * d ∈ L <;> by_cases h₃ : a + 3 * d ∈ L <;>
    simp [g, indicatorCyclic, h₀, h₁, h₂, h₃]
    exact (cyclicLift_no_four_ap hS hfree hd h₀ h₁ h₂ h₃).elim
  change (∑ a, ∑ d, g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d)) = _
  calc
    _ = ∑ a : ZMod (2 * N + 1), g a ^ 4 := by
      simp_rw [hterm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = (L.card : ℝ) := sum_indicatorCyclic_pow L (by decide)
    _ = _ := by rw [card_cyclicLift hS]

end CyclicLift


section PartitionEnergy

variable {X I J : Type*} [DecidableEq I] [DecidableEq J]

private noncomputable def fibreMean (S : Finset X) (P : X → I) (f : X → ℝ) (i : I) : ℝ :=
  (∑ x ∈ S with P x = i, f x) / ((S.filter (fun x => P x = i)).card : ℝ)

private noncomputable def partMean (S : Finset X) (P : X → I) (f : X → ℝ) (x : X) : ℝ :=
  fibreMean S P f (P x)

private lemma fibreMean_mul_card (S : Finset X) (P : X → I) (f : X → ℝ) (i : I) :
    fibreMean S P f i * ((S.filter (fun x => P x = i)).card : ℝ) =
      ∑ x ∈ S with P x = i, f x := by
  unfold fibreMean
  by_cases he : S.filter (fun x => P x = i) = ∅
  · simp [he]
  · have hc : (↑(S.filter (fun x => P x = i)).card : ℝ) ≠ 0 := by
      exact_mod_cast (show (S.filter (fun x => P x = i)).card ≠ 0 from
        fun hc => he (Finset.card_eq_zero.mp hc))
    exact div_mul_cancel₀ _ hc

private lemma sum_partMean_mul_label (S : Finset X) (P : X → I) (f : X → ℝ) (w : I → ℝ) :
    ∑ x ∈ S, partMean S P f x * w (P x) = ∑ x ∈ S, f x * w (P x) := by
  classical
  have maps : (S : Set X).MapsTo P (S.image P) := fun x hx => Finset.mem_image_of_mem _ hx
  calc
    _ = ∑ i ∈ S.image P, ∑ x ∈ S with P x = i, partMean S P f x * w (P x) :=
      (Finset.sum_fiberwise_of_maps_to maps _).symm
    _ = ∑ i ∈ S.image P, (∑ x ∈ S with P x = i, f x) * w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      calc
        _ = ∑ _x ∈ S with P _x = i, fibreMean S P f i * w i := by
          refine Finset.sum_congr rfl fun x hx => ?_
          simp only [partMean, (Finset.mem_filter.mp hx).2]
        _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_comm _ (fibreMean S P f i),
            fibreMean_mul_card]
    _ = ∑ i ∈ S.image P, ∑ x ∈ S with P x = i, f x * w (P x) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to maps _

private lemma abs_partMean_le_one (S : Finset X) (P : X → I) (f : X → ℝ)
    (hf : ∀ x ∈ S, |f x| ≤ 1) (x : X) : |partMean S P f x| ≤ 1 := by
  let F := S.filter (fun y => P y = P x)
  change |(∑ y ∈ F, f y) / (F.card : ℝ)| ≤ 1
  by_cases hF : F.Nonempty
  · have hp : 0 < (F.card : ℝ) := by exact_mod_cast hF.card_pos
    rw [abs_div, abs_of_nonneg hp.le, div_le_one hp]
    calc
      _ ≤ ∑ y ∈ F, |f y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ F, (1 : ℝ) :=
        Finset.sum_le_sum fun y hy => hf y (Finset.mem_filter.mp hy).1
      _ = _ := by simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    simp

private lemma partMean_sq_sum_le_card (S : Finset X) (P : X → I) (f : X → ℝ)
    (hf : ∀ x ∈ S, |f x| ≤ 1) :
    ∑ x ∈ S, partMean S P f x ^ 2 ≤ (S.card : ℝ) := by
  calc
    _ ≤ ∑ _ ∈ S, (1 : ℝ) := by
      refine Finset.sum_le_sum fun x _ => ?_
      rw [← sq_abs]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (abs_partMean_le_one S P f hf x) 2
    _ = _ := by simp

private lemma partMean_energy_decomposition (S : Finset X) (Q : X → J) (p : J → I)
    (f : X → ℝ) :
    ∑ x ∈ S, partMean S Q f x ^ 2 =
      (∑ x ∈ S, partMean S (p ∘ Q) f x ^ 2) +
        ∑ x ∈ S, (partMean S Q f x - partMean S (p ∘ Q) f x) ^ 2 := by
  let A := partMean S (p ∘ Q) f
  let B := partMean S Q f
  have hA : (∑ x ∈ S, A x ^ 2) = ∑ x ∈ S, f x * A x := by
    simpa only [A, partMean, sq] using
      sum_partMean_mul_label S (p ∘ Q) f (fibreMean S (p ∘ Q) f)
  have hB : (∑ x ∈ S, B x * A x) = ∑ x ∈ S, f x * A x := by
    simpa only [A, B, partMean, Function.comp_apply] using
      sum_partMean_mul_label S Q f (fun j => fibreMean S (p ∘ Q) f (p j))
  change ∑ x ∈ S, B x ^ 2 = (∑ x ∈ S, A x ^ 2) + ∑ x ∈ S, (B x - A x) ^ 2
  have hpoint (x : X) : (B x - A x) ^ 2 = B x ^ 2 + A x ^ 2 - 2 * (B x * A x) := by ring
  simp only [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith only [hA, hB]

private lemma partMean_energy_increment (S : Finset X) (Q : X → J) (p : J → I)
    (f : X → ℝ) (w : J → ℝ) (hw : ∀ j, |w j| ≤ 1) {η : ℝ} (hη : 0 ≤ η)
    (hc : η * (S.card : ℝ) ≤ |∑ x ∈ S, (f x - partMean S (p ∘ Q) f x) * w (Q x)|) :
    (∑ x ∈ S, partMean S (p ∘ Q) f x ^ 2) + η ^ 2 * (S.card : ℝ) ≤
      ∑ x ∈ S, partMean S Q f x ^ 2 := by
  rw [partMean_energy_decomposition S Q p f]
  apply add_le_add_right
  by_cases hS : S.Nonempty
  · let A := partMean S (p ∘ Q) f
    let B := partMean S Q f
    let n : ℝ := S.card
    have hn : 0 < n := by dsimp only [n]; exact_mod_cast hS.card_pos
    have hc' : η * n ≤ |∑ x ∈ S, (B x - A x) * w (Q x)| := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      unfold B
      rw [sum_partMean_mul_label]
      simpa only [sub_mul, Finset.sum_sub_distrib] using hc
    have hw₂ : ∑ x ∈ S, w (Q x) ^ 2 ≤ n := by
      calc
        _ ≤ ∑ _ ∈ S, (1 : ℝ) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [← sq_abs]
          simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hw (Q x)) 2
        _ = _ := by simp [n]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun x => B x - A x) (fun x => w (Q x))
    change η ^ 2 * n ≤ ∑ x ∈ S, (B x - A x) ^ 2
    refine le_of_mul_le_mul_right ?_ hn
    calc
      _ = (η * n) ^ 2 := by ring
      _ ≤ |∑ x ∈ S, (B x - A x) * w (Q x)| ^ 2 := pow_le_pow_left₀ (by positivity) hc' 2
      _ ≤ (∑ x ∈ S, (B x - A x) ^ 2) * ∑ x ∈ S, w (Q x) ^ 2 := by simpa only [sq_abs] using hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left hw₂ (by positivity)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

end PartitionEnergy

private lemma graphDensityRate_ge_monomial {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    graphDensityRate 1 * δ ^ 23407 ≤ graphDensityRate δ := by
  let G := graphRate 1
  let τ := (G / 8) * ((G / 2) ^ 9 / 65536)
  have hG : 0 < G := by unfold G graphRate; positivity
  have hτ : 0 < τ := by unfold τ; positivity
  have hrate : graphRate δ = G * δ ^ 6 := by unfold G graphRate; ring
  have hratio : differenceRatioBound δ * δ ^ 60 = differenceRatioBound 1 := by
    have hD : (graphRate δ / 8) * ((graphRate δ / 2) ^ 9 / 65536) = τ * δ ^ 60 := by
      rw [hrate]
      unfold τ
      ring
    change ((graphRate δ / 8) * ((graphRate δ / 2) ^ 9 / 65536))⁻¹ * δ ^ 60 = τ⁻¹
    rw [hD]
    field_simp
  let R₀ := differenceRatioBound 1
  let R := differenceRatioBound δ
  have hDpow : R ^ 13 * δ ^ 780 = R₀ ^ 13 := by
    calc
      _ = (R * δ ^ 60) ^ 13 := by ring
      _ = _ := congrArg (fun r : ℝ => r ^ 13) hratio
  have hR₀ : 0 < R₀ := by unfold R₀ differenceRatioBound; positivity
  have hR : 0 < R := by unfold R differenceRatioBound graphRate; positivity
  have hδpow := pow_le_one₀ hδ.le hδ₁ (n := 780)
  let L₀ := (2 * (R₀ ^ 13 + 1)) ^ 30
  let L := (2 * (R ^ 13 + 1)) ^ 30
  have hL₀ : 0 < L₀ := by unfold L₀; positivity
  have hL : 0 < L := by unfold L; positivity
  have hbase : (2 * (R ^ 13 + 1)) * δ ^ 780 ≤ 2 * (R₀ ^ 13 + 1) := by
    calc
      _ = 2 * (R ^ 13 * δ ^ 780 + δ ^ 780) := by ring
      _ ≤ _ := by rw [hDpow]; gcongr
  have hloss : L * δ ^ 23400 ≤ L₀ := by
    calc
      _ = ((2 * (R ^ 13 + 1)) * δ ^ 780) ^ 30 := by
        unfold L
        rw [show δ ^ 23400 = (δ ^ 780) ^ 30 by ring, ← mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase 30
  change (G * 1 / (48 * L₀)) * δ ^ 23407 ≤ graphRate δ * δ / (48 * L)
  rw [mul_one, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity), hrate]
  calc
    _ = (48 * G * δ ^ 7) * (L * δ ^ 23400) := by ring
    _ ≤ (48 * G * δ ^ 7) * L₀ := mul_le_mul_of_nonneg_left hloss (by positivity)
    _ = _ := by ring

private lemma sqrt_le_bohrSet_card {M : ℕ} [NeZero M] (Ω : Finset (ZMod M)) {r : ℝ}
    (hr : 1 / 32 ≤ r) (hscale : (Ω.card : ℝ) * (2 * Real.log 32768) ≤ Real.log (M : ℝ)) :
    Real.sqrt (M : ℝ) ≤ ((bohrSet Ω r).card : ℝ) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hS : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM
  have hcard := bohrSet_card_lower Ω hr
  have hcardR : (M : ℝ) ≤ (32768 : ℝ) ^ Ω.card * ((bohrSet Ω r).card : ℝ) := by
    exact_mod_cast hcard
  have hQ : (32768 : ℝ) ^ Ω.card ≤ Real.sqrt (M : ℝ) := by
    apply (sq_le_sq₀ (by positivity) hS.le).mp
    rw [Real.sq_sqrt hM.le, ← pow_mul]
    have hbase : (0 : ℝ) < (32768 : ℝ) ^ (Ω.card * 2) := by positivity
    rw [← Real.log_le_log_iff hbase hM, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hscale]
  apply le_of_mul_le_mul_left _ hS
  calc
    _ = (M : ℝ) := Real.mul_self_sqrt hM.le
    _ ≤ (32768 : ℝ) ^ Ω.card * ((bohrSet Ω r).card : ℝ) := hcardR
    _ ≤ _ := by gcongr

private lemma log_density_bound_from_scale {N p : ℕ} {S : Finset ℕ} {B : ℝ}
    (hN : 3 ≤ N) (hp : 0 < p) (hB : 0 < B)
    (hscale : (density N S) ^ p * Real.log (N : ℝ) ≤ B) :
    (S.card : ℝ) ≤ B ^ ((p : ℝ)⁻¹) * ((N : ℝ) * Real.log N ^ (-((p : ℝ)⁻¹))) := by
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN₁ : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN₁
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hd : 0 ≤ density N S := by unfold density; positivity
  have hpow : density N S ^ p ≤ B / Real.log (N : ℝ) := (le_div_iff₀ hlog).mpr hscale
  have h := Real.rpow_le_rpow (pow_nonneg hd p) hpow (by positivity : 0 ≤ (p : ℝ)⁻¹)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd, mul_inv_cancel₀ hp'.ne', Real.rpow_one,
    Real.div_rpow hB.le hlog.le, div_eq_mul_inv, ← Real.rpow_neg hlog.le] at h
  have hc := mul_le_mul_of_nonneg_right h hN₀.le
  rw [density, div_mul_cancel₀ _ hN₀.ne'] at hc
  simpa only [mul_assoc, mul_comm (Real.log (N : ℝ) ^ (-((p : ℝ)⁻¹))) (N : ℝ)] using hc

private lemma pow_log_bound_gives_bohr_size {N K : ℕ} {S : Finset ℕ} {κ : ℝ}
    (hN : 3 ≤ N) (hS : S ⊆ Finset.Icc 1 N) (hSne : S.Nonempty)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (Ω : Finset (ZMod (2 * N + 1)))
    (hΩ : (Ω.card : ℝ) * graphDensityRate (κ * density N S ^ K) ^ 2 ≤ 18)
    (hscale : 36 * Real.log 32768 ≤ graphDensityRate 1 ^ 2 * κ ^ 46814 *
      density N S ^ (K * 46814) * Real.log N) :
    Real.sqrt ((2 * N + 1 : ℕ) : ℝ) ≤ ((bohrSet Ω (1 / 4)).card : ℝ) := by
  let δ := κ * density N S ^ K
  let R := graphDensityRate δ
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show N > 0 by omega)
  have hN₁ : (1 : ℝ) < N := by exact_mod_cast (show N > 1 by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN₁
  have hlogQ : 0 < Real.log 32768 := Real.log_pos (by norm_num)
  have hd : 0 < density N S := by
    unfold density
    exact div_pos (by exact_mod_cast hSne.card_pos) hN₀
  have hd₁ := (density_mem_unitInterval hS).2
  have hδ : 0 < δ := by unfold δ; positivity
  have hδ₁ : δ ≤ 1 := by
    unfold δ
    calc
      _ ≤ 1 * 1 := mul_le_mul hκ₁ (pow_le_one₀ hd.le hd₁) (by positivity) zero_le_one
      _ = 1 := one_mul _
  have hR : 0 < R := graphDensityRate_pos hδ
  have hR₁ : 0 < graphDensityRate 1 := graphDensityRate_pos zero_lt_one
  have hmono := graphDensityRate_ge_monomial hδ hδ₁
  have hRpow : graphDensityRate 1 ^ 2 * κ ^ 46814 * density N S ^ (K * 46814) ≤ R ^ 2 := by
    calc
      _ = (graphDensityRate 1 * δ ^ 23407) ^ 2 := by
        rw [mul_pow, ← pow_mul]
        change graphDensityRate 1 ^ 2 * κ ^ 46814 * density N S ^ (K * 46814) =
          graphDensityRate 1 ^ 2 * δ ^ 46814
        unfold δ
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hmono 2
  have hM : (N : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 2 * N + 1 by omega)
  have hlogM : Real.log (N : ℝ) ≤ Real.log ((2 * N + 1 : ℕ) : ℝ) := Real.log_le_log hN₀ hM
  apply sqrt_le_bohrSet_card Ω (by norm_num)
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hR)
  calc
    _ = ((Ω.card : ℝ) * R ^ 2) * (2 * Real.log 32768) := by ring
    _ ≤ 18 * (2 * Real.log 32768) := mul_le_mul_of_nonneg_right hΩ (by positivity)
    _ ≤ R ^ 2 * Real.log (N : ℝ) := by
      have hh := hscale.trans (mul_le_mul_of_nonneg_right hRpow hlog.le)
      linarith only [hh]
    _ ≤ R ^ 2 * Real.log ((2 * N + 1 : ℕ) : ℝ) := by gcongr
    _ = _ := mul_comm _ _

section BohrRegularity

variable {M : ℕ} [NeZero M]

private lemma exists_simultaneous_bins {ι κ : Type*} (J : Finset ι) (g : κ → ι → ℂ) (ks : List κ)
    (hg : ∀ k ∈ ks, ∀ a ∈ J, ‖g k a‖ ≤ 1) :
    ∃ J' : Finset ι, J' ⊆ J ∧ J.card ≤ 32768 ^ ks.length * J'.card ∧
      ∀ k ∈ ks, ∀ a ∈ J', ∀ b ∈ J', ‖g k a - g k b‖ ≤ 1 / 32 := by
  induction ks generalizing J with
  | nil =>
    refine ⟨J, Finset.Subset.refl _, by simp, by simp⟩
  | cons k ks ih =>
    obtain ⟨J₁, hsub₁, hcard₁, hclose₁⟩ := exists_large_phase_bin J (g k) (hg k (by simp))
    obtain ⟨J₂, hsub₂, hcard₂, hclose₂⟩ := ih J₁ (fun j hj a ha => hg j (by simp [hj]) a (hsub₁ ha))
    refine ⟨J₂, hsub₂.trans hsub₁, ?_, ?_⟩
    · calc
        _ ≤ 32768 * J₁.card := hcard₁
        _ ≤ 32768 * (32768 ^ ks.length * J₂.card) := Nat.mul_le_mul_left _ hcard₂
        _ = _ := by simp only [List.length_cons, pow_succ]; ring
    · intro j hj a ha b hb
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hclose₁ a (hsub₂ ha) b (hsub₂ hb)
      · exact hclose₂ j hj a ha b hb

private lemma bohrSet_mono {Ω : Finset (ZMod M)} {r s : ℝ} (hrs : r ≤ s) :
    bohrSet Ω r ⊆ bohrSet Ω s := by
  intro a ha
  exact mem_bohrSet.mpr fun k hk => (mem_bohrSet.mp ha k hk).trans hrs

private lemma add_mem_bohrSet {Ω : Finset (ZMod M)} {r s : ℝ} {a b : ZMod M}
    (ha : a ∈ bohrSet Ω r) (hb : b ∈ bohrSet Ω s) : a + b ∈ bohrSet Ω (r + s) := by
  apply mem_bohrSet.mpr
  intro k hk
  have ht := norm_stdAddChar_add_sub_le (k * a) (k * b) 0 0
  rw [zero_add, AddChar.map_zero_eq_one, ← mul_add] at ht
  exact ht.trans (add_le_add (mem_bohrSet.mp ha k hk) (mem_bohrSet.mp hb k hk))

private lemma card_bohrSet_double_le (Ω : Finset (ZMod M)) {r : ℝ} (hr : 0 < r) :
    (bohrSet Ω (2 * r)).card ≤ 32768 ^ Ω.card * (bohrSet Ω r).card := by
  classical
  let B := bohrSet Ω (2 * r)
  let g (k a : ZMod M) := (ZMod.stdAddChar (k * a) - 1) / ((2 * r : ℝ) : ℂ)
  have hrad : 0 < 2 * r := by positivity
  have hg (k : ZMod M) (hk : k ∈ Ω.toList) (a : ZMod M) (ha : a ∈ B) : ‖g k a‖ ≤ 1 := by
    unfold g
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hrad.le, div_le_one hrad]
    exact mem_bohrSet.mp ha k (Finset.mem_toList.mp hk)
  obtain ⟨A, _, hA, hclose⟩ := exists_simultaneous_bins B g Ω.toList hg
  rw [Finset.length_toList] at hA
  have hA' : A.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty, mul_zero] at hA
    exact (Nat.not_le_of_lt (bohrSet_nonempty Ω hrad.le).card_pos) hA
  obtain ⟨a₀, ha₀⟩ := hA'
  have hcard : A.card ≤ (bohrSet Ω r).card := by
    refine Finset.card_le_card_of_injOn (fun a => a - a₀) ?_ ?_
    · intro a ha
      apply mem_bohrSet.mpr
      intro k hk
      rw [mul_sub, norm_stdAddChar_sub_one]
      have hb := hclose k (Finset.mem_toList.mpr hk) a ha a₀ ha₀
      unfold g at hb
      rw [← sub_div, sub_sub_sub_cancel_right, norm_div, Complex.norm_real,
        Real.norm_of_nonneg hrad.le, div_le_iff₀ hrad] at hb
      linarith only [hb, hr]
    · intro a _ b _ hab
      exact sub_left_injective hab
  exact hA.trans (Nat.mul_le_mul_left _ hcard)

private lemma exists_bohr_band_from_growth (Ω : Finset (ZMod M)) {r η : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) {n : ℕ} (hn : 0 < n)
    (hgrowth : (32768 : ℝ) ^ Ω.card < (1 + η) ^ n) :
    ∃ R : ℝ, r ≤ R ∧ R ≤ 2 * r ∧
      ((bohrSet Ω (R + r / (2 * n))).card : ℝ) ≤
        (1 + η) * ((bohrSet Ω (R - r / (2 * n))).card : ℝ) := by
  let t (i : ℕ) := r + (i : ℝ) * (r / n)
  let F (i : ℕ) : ℝ := (bohrSet Ω (t i)).card
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hRstep : 0 ≤ r / n := by positivity
  have ht₀ : t 0 = r := by simp [t]
  have htn : t n = 2 * r := by
    dsimp [t]
    field_simp
    ring
  have hF₀ : 0 < F 0 := by
    unfold F
    rw [ht₀]
    exact_mod_cast (bohrSet_nonempty Ω hr.le).card_pos
  have hFbound : F n ≤ (32768 : ℝ) ^ Ω.card * F 0 := by
    unfold F
    rw [ht₀, htn]
    exact_mod_cast card_bohrSet_double_le Ω hr
  have hex : ∃ i : ℕ, i < n ∧ F (i + 1) ≤ (1 + η) * F i := by
    by_contra! h
    have hiBound : ∀ i ≤ n, (1 + η) ^ i * F 0 ≤ F i := by
      intro i hi
      induction i with
      | zero => simp
      | succ i ih =>
        have hi' : i ≤ n := by omega
        calc
          _ = (1 + η) * ((1 + η) ^ i * F 0) := by rw [pow_succ]; ring
          _ ≤ (1 + η) * F i := mul_le_mul_of_nonneg_left (ih hi') (by positivity)
          _ ≤ _ := (h i (by omega)).le
    have hc := (hiBound n le_rfl).trans hFbound
    exact (not_le_of_gt hgrowth) (le_of_mul_le_mul_right hc hF₀)
  obtain ⟨i, hi, h⟩ := hex
  let R := t i + r / (2 * n)
  have h₁ : R - r / (2 * n) = t i := by unfold R; ring
  have h₂ : R + r / (2 * n) = t (i + 1) := by
    unfold R t
    push_cast
    field_simp
    ring
  have hlow : r ≤ R := by
    unfold R t
    linarith only [show 0 ≤ (i : ℝ) * (r / n) by positivity,
      show 0 ≤ r / (2 * (n : ℝ)) by positivity]
  have hu : R ≤ 2 * r := by
    rw [← htn]
    have hitle : ((i + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hi
    have hmon : t (i + 1) ≤ t n := by unfold t; gcongr
    rw [← h₂] at hmon
    linarith only [hmon, show 0 ≤ r / (2 * (n : ℝ)) by positivity]
  refine ⟨R, hlow, hu, ?_⟩
  rw [h₁, h₂]
  exact h

private lemma exists_bohr_band (Ω : Finset (ZMod M)) {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (m : ℕ) (hm : 1 ≤ (m : ℝ) * η) :
    let n := m * (15 * Ω.card + 1)
    ∃ R : ℝ, r ≤ R ∧ R ≤ 2 * r ∧
      ((bohrSet Ω (R + r / (2 * n))).card : ℝ) ≤
        (1 + η) * ((bohrSet Ω (R - r / (2 * n))).card : ℝ) := by
  dsimp only
  have hm₀ : 0 < m := by
    by_contra! h
    have h' : m = 0 := by omega
    norm_num [h'] at hm
  apply exists_bohr_band_from_growth Ω hr hη.le (by positivity)
  have hpow : (2 : ℝ) ≤ (1 + η) ^ m := by
    have hh := one_add_mul_le_pow (show (-2 : ℝ) ≤ η by linarith) m
    linarith only [hh, hm]
  calc
    _ = (2 : ℝ) ^ (15 * Ω.card) := by rw [pow_mul]; norm_num
    _ < (2 : ℝ) ^ (15 * Ω.card + 1) := by
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    _ ≤ ((1 + η) ^ m) ^ (15 * Ω.card + 1) := pow_le_pow_left₀ (by norm_num) hpow _
    _ = _ := by rw [← pow_mul]

private lemma card_bohrSet_dyadic_le (Ω : Finset (ZMod M)) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    (bohrSet Ω ((2 : ℝ) ^ j * r)).card ≤ 32768 ^ (j * Ω.card) * (bohrSet Ω r).card := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hscale : (2 : ℝ) ^ (j + 1) * r = 2 * ((2 : ℝ) ^ j * r) := by rw [pow_succ]; ring
    calc
      _ ≤ 32768 ^ Ω.card * (bohrSet Ω ((2 : ℝ) ^ j * r)).card := by
        rw [hscale]
        exact card_bohrSet_double_le Ω (by positivity)
      _ ≤ 32768 ^ Ω.card * (32768 ^ (j * Ω.card) * (bohrSet Ω r).card) :=
        Nat.mul_le_mul_left _ ih
      _ = _ := by
        rw [Nat.succ_mul, pow_add]
        ring

private lemma bohrSet_card_lower_small_radius (Ω : Finset (ZMod M)) {r : ℝ} (hr : 0 < r)
    (j : ℕ) (hj : 1 / 32 ≤ (2 : ℝ) ^ j * r) :
    M ≤ 32768 ^ ((j + 1) * Ω.card) * (bohrSet Ω r).card := by
  calc
    _ ≤ 32768 ^ Ω.card * (bohrSet Ω ((2 : ℝ) ^ j * r)).card := bohrSet_card_lower Ω hj
    _ ≤ 32768 ^ Ω.card * (32768 ^ (j * Ω.card) * (bohrSet Ω r).card) :=
      Nat.mul_le_mul_left _ (card_bohrSet_dyadic_le Ω hr j)
    _ = _ := by
      rw [Nat.add_mul, one_mul, pow_add]
      ring

private lemma bohr_band_translation_card (Ω : Finset (ZMod M)) {R γ η : ℝ}
    (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    {u : ZMod M} (hu : u ∈ bohrSet Ω γ) :
    let B := bohrSet Ω R
    let C := B.image (fun x => x + u)
    ((B \ C).card : ℝ) + ((C \ B).card : ℝ) ≤ 2 * η * (B.card : ℝ) := by
  classical
  dsimp only
  let B := bohrSet Ω R
  let C := B.image (fun x => x + u)
  let I := bohrSet Ω (R - γ)
  let O := bohrSet Ω (R + γ)
  have hIB : I ⊆ B := bohrSet_mono (by linarith)
  have hBO : B ⊆ O := bohrSet_mono (by linarith)
  have hIO := hIB.trans hBO
  have hIC : I ⊆ C := by
    intro x hx
    apply Finset.mem_image.mpr
    refine ⟨x - u, ?_, by abel⟩
    have h := diff_mem_bohrSet hx hu
    simpa only [sub_add_cancel] using h
  have hCO : C ⊆ O := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact add_mem_bohrSet hy hu
  have hBC : B \ C ⊆ O \ I := by
    intro x hx
    obtain ⟨hxB, hxC⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hBO hxB, fun h => hxC (hIC h)⟩
  have hCB : C \ B ⊆ O \ I := by
    intro x hx
    obtain ⟨hxC, hxB⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hCO hxC, fun h => hxB (hIB h)⟩
  have hdiff : ((O \ I).card : ℝ) + (I.card : ℝ) = (O.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hIO
  have hbi : (I.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast Finset.card_le_card hIB
  have hbd : ((O \ I).card : ℝ) ≤ η * (B.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hbi hη
    change (O.card : ℝ) ≤ (1 + η) * (I.card : ℝ) at hband
    linarith only [hdiff, hband, h]
  have ha : ((B \ C).card : ℝ) ≤ ((O \ I).card : ℝ) := by exact_mod_cast Finset.card_le_card hBC
  have hb : ((C \ B).card : ℝ) ≤ ((O \ I).card : ℝ) := by exact_mod_cast Finset.card_le_card hCB
  change ((B \ C).card : ℝ) + ((C \ B).card : ℝ) ≤ 2 * η * (B.card : ℝ)
  linarith only [ha, hb, hbd]

private lemma abs_sum_sub_sum_le_sdiff {ι : Type*} [DecidableEq ι] (A B : Finset ι)
    (f : ι → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x ∈ A, f x) - ∑ x ∈ B, f x| ≤ ((A \ B).card : ℝ) + ((B \ A).card : ℝ) := by
  let I := A ∩ B
  have ha : A \ I = A \ B := by ext x; simp [I]
  have hb : B \ I = B \ A := by ext x; simp [I, and_comm]
  have hA := Finset.sum_sdiff (f := f) (show I ⊆ A from Finset.inter_subset_left)
  have hB := Finset.sum_sdiff (f := f) (show I ⊆ B from Finset.inter_subset_right)
  rw [ha] at hA
  rw [hb] at hB
  have h : (∑ x ∈ A, f x) - ∑ x ∈ B, f x = (∑ x ∈ A \ B, f x) - ∑ x ∈ B \ A, f x := by
    linarith only [hA, hB]
  have habs (s : Finset ι) : |∑ x ∈ s, f x| ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ s, |f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ s, (1 : ℝ) := Finset.sum_le_sum fun x _ => hf x
      _ = _ := by simp
  rw [h]
  calc
    _ ≤ |∑ x ∈ A \ B, f x| + |∑ x ∈ B \ A, f x| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (∑ x ∈ A \ B, f x) 0 (∑ x ∈ B \ A, f x)
    _ ≤ _ := add_le_add (habs _) (habs _)

private lemma bohr_band_translation_sum (Ω : Finset (ZMod M)) {R γ η : ℝ}
    (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    {u : ZMod M} (hu : u ∈ bohrSet Ω γ) (f : ZMod M → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x ∈ bohrSet Ω R, f (x + u)) - ∑ x ∈ bohrSet Ω R, f x| ≤
      2 * η * ((bohrSet Ω R).card : ℝ) := by
  classical
  let B := bohrSet Ω R
  let C := B.image (fun x => x + u)
  have hsum : ∑ x ∈ C, f x = ∑ x ∈ B, f (x + u) := by
    apply Finset.sum_image
    exact fun x _ y _ h => add_right_cancel h
  change |(∑ x ∈ B, f (x + u)) - ∑ x ∈ B, f x| ≤ 2 * η * (B.card : ℝ)
  rw [← hsum]
  have hcard := bohr_band_translation_card Ω hγ hη hband hu
  change ((B \ C).card : ℝ) + ((C \ B).card : ℝ) ≤ 2 * η * (B.card : ℝ) at hcard
  rw [add_comm ((B \ C).card : ℝ)] at hcard
  exact (abs_sum_sub_sum_le_sdiff C B f hf).trans hcard

end BohrRegularity

private def RegularLocalFrequencyStructure (N : ℕ) (δ η : ℝ) (m : ℕ) (f : ℤ → ℝ) : Prop :=
  ∃ Ω J : Finset (ZMod (2 * N + 1)), ∃ ξ φ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
    ∃ s : ZMod (2 * N + 1), ∃ R : ℝ,
    let n := m * (15 * Ω.card + 1)
    let γ : ℝ := (1 / 16) / (2 * (n : ℝ))
    1 / 16 ≤ R ∧ R ≤ 1 / 8 ∧ J.Nonempty ∧
    (Ω.card : ℝ) * graphDensityRate δ ^ 2 ≤ 18 ∧
    ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ) ∧
    2 * N + 1 ≤ 32768 ^ ((n.log2 + 2) * Ω.card) * (bohrSet Ω γ).card ∧
    2 * N + 1 ≤ 32768 ^ Ω.card * (bohrSet Ω R).card ∧
    (graphDensityRate δ / 3) * ((bohrSet Ω R).card : ℝ) ≤ (J.card : ℝ) ∧
    (∀ a ∈ J, a - s ∈ bohrSet Ω R) ∧
    (∀ a ∈ J, Real.sqrt (δ / 6) * (N : ℝ) ≤
      ‖fourier (cyclicDerivative (periodize N f) a) (ξ a)‖) ∧
    (∀ a ∈ J, ∀ b ∈ J, a - b ∈ bohrSet Ω (1 / 2) ∧ φ (a - b) = ξ a - ξ b) ∧
    (∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b)

private lemma large_cube_has_regular_local_frequency_structure {N : ℕ} {f : ℤ → ℝ}
    (hf : ∀ x ∉ interval N, f x = 0) (habs : ∀ x, |f x| ≤ 1)
    (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) (hlarge : δ * (N : ℝ) ^ 4 ≤ cubeSum N f)
    {η : ℝ} (hη : 0 < η) (m : ℕ) (hm : 1 ≤ (m : ℝ) * η) :
    RegularLocalFrequencyStructure N δ η m f := by
  classical
  obtain ⟨J, ξ, φ, hJ, hsize, hξ, hφ, hadd⟩ :=
    large_cube_has_local_frequency_extension hf habs hN hδ hlarge
  let M := 2 * N + 1
  let rate := graphDensityRate δ
  let Ω := largeSpectrum J
  let n := m * (15 * Ω.card + 1)
  let γ : ℝ := (1 / 16) / (2 * (n : ℝ))
  obtain ⟨R, hRlo, hRhi, hband⟩ := exists_bohr_band Ω (by norm_num : (0 : ℝ) < 1 / 16) hη m hm
  have hRlo' : (1 / 16 : ℝ) ≤ R := hRlo
  have hRhi' : R ≤ (1 / 8 : ℝ) := by linarith only [hRhi]
  let B := bohrSet Ω R
  have hB : B.Nonempty := bohrSet_nonempty Ω (by linarith only [hRlo'])
  have hB' := bohr_largeSpectrum_subset_double_difference hJ
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hMpos : (0 : ℝ) < M := by dsimp [M]; positivity
  have hMle : (M : ℝ) ≤ 3 * (N : ℝ) := by dsimp only [M]; push_cast; linarith
  have hrate : 0 < rate := graphDensityRate_pos hδ
  have hΩ : (Ω.card : ℝ) * rate ^ 2 ≤ 18 := by
    refine le_of_mul_le_mul_right ?_ (sq_pos_of_pos hNpos)
    calc
      _ = (Ω.card : ℝ) * (rate * (N : ℝ)) ^ 2 := by ring
      _ ≤ (Ω.card : ℝ) * (J.card : ℝ) ^ 2 := by gcongr
      _ ≤ 2 * (M : ℝ) ^ 2 := card_largeSpectrum_bound hJ
      _ ≤ 2 * (3 * (N : ℝ)) ^ 2 := by gcongr
      _ = _ := by ring
  obtain ⟨s, hs⟩ := exists_large_translatedSlice J B
  let T := translatedSlice J B s
  have hs' : (J.card : ℝ) * (B.card : ℝ) ≤ (M : ℝ) * (T.card : ℝ) := by
    dsimp only [M, T]
    exact_mod_cast hs
  have hT : (rate / 3) * (B.card : ℝ) ≤ (T.card : ℝ) := by
    refine le_of_mul_le_mul_right ?_ hMpos
    calc
      _ ≤ (rate / 3) * (B.card : ℝ) * (3 * (N : ℝ)) := by gcongr
      _ = (rate * (N : ℝ)) * (B.card : ℝ) := by ring
      _ ≤ (J.card : ℝ) * (B.card : ℝ) := by gcongr
      _ ≤ (M : ℝ) * (T.card : ℝ) := hs'
      _ = _ := mul_comm _ _
  have hTne : T.Nonempty := by
    have hcard : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
    apply Finset.card_pos.mp
    exact_mod_cast ((by positivity : 0 < (rate / 3) * (B.card : ℝ)).trans_le hT)
  have hTsub : T ⊆ J := Finset.filter_subset _ _
  have hTpos {a : ZMod M} (ha : a ∈ T) : a - s ∈ B := (Finset.mem_filter.mp ha).2
  have hn : 0 < (n : ℝ) := by
    have hm₀ : 0 < m := by
      by_contra! h
      have he : m = 0 := by omega
      norm_num [he] at hm
    unfold n
    positivity
  have hsmall : M ≤ 32768 ^ ((n.log2 + 2) * Ω.card) * (bohrSet Ω γ).card := by
    apply bohrSet_card_lower_small_radius Ω (by unfold γ; positivity) (n.log2 + 1)
    have hp : (n : ℝ) ≤ (2 : ℝ) ^ (n.log2 + 1) := by
      exact_mod_cast Nat.lt_log2_self.le
    unfold γ
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    linarith only [hp]
  refine ⟨Ω, T, ξ, φ, s, R, hRlo', hRhi', hTne, hΩ, hband, hsmall,
    bohrSet_card_lower Ω (by linarith only [hRlo']), hT, fun _ ha => hTpos ha,
    fun a ha => hξ a (hTsub ha), ?_, ?_⟩
  · intro a ha b hb
    refine ⟨?_, hφ a (hTsub ha) b (hTsub hb)⟩
    have hd := diff_mem_bohrSet (hTpos ha) (hTpos hb)
    have he : (a - s) - (b - s) = a - b := by abel
    rw [he] at hd
    exact bohrSet_mono (by linarith only [hRhi']) hd
  · intro a ha b hb hab
    exact hadd a (hB' ha) b (hB' hb) (hB' hab)

section LocalQuadraticPhase

private def halfMod (N : ℕ) : ZMod (2 * N + 1) := ((N + 1 : ℕ) : ZMod (2 * N + 1))

private lemma add_halfMod_self (N : ℕ) : halfMod N + halfMod N = 1 := by
  unfold halfMod
  rw [← Nat.cast_add, show N + 1 + (N + 1) = (2 * N + 1) + 1 by omega,
    Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add]

private def localQuadratic {N : ℕ} (φ : ZMod (2 * N + 1) → ZMod (2 * N + 1))
    (x : ZMod (2 * N + 1)) : ZMod (2 * N + 1) :=
  halfMod N * (x * φ x)

private def polarizationDefect {N : ℕ} (φ : ZMod (2 * N + 1) → ZMod (2 * N + 1))
    (x y : ZMod (2 * N + 1)) : ZMod (2 * N + 1) :=
  halfMod N * (y * φ x - x * φ y)

private lemma localQuadratic_polarization {N : ℕ} {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)}
    {x y : ZMod (2 * N + 1)} (hxy : φ (x + y) = φ x + φ y) :
    localQuadratic φ (x + y) - localQuadratic φ x - localQuadratic φ y =
      x * φ y + polarizationDefect φ x y := by
  unfold localQuadratic polarizationDefect
  rw [hxy]
  calc
    _ = (halfMod N + halfMod N) * (x * φ y) + halfMod N * (y * φ x - x * φ y) := by ring
    _ = _ := by rw [add_halfMod_self, one_mul]

private lemma norm_localQuadratic_polarization_error {N : ℕ}
    {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)} {x y : ZMod (2 * N + 1)}
    (hxy : φ (x + y) = φ x + φ y) :
    ‖ZMod.stdAddChar (localQuadratic φ (x + y) - localQuadratic φ x - localQuadratic φ y) -
        ZMod.stdAddChar (x * φ y)‖ = ‖ZMod.stdAddChar (polarizationDefect φ x y) - 1‖ := by
  rw [← norm_stdAddChar_sub_one, localQuadratic_polarization hxy, add_sub_cancel_left]

private def thirdDifference {G : Type*} [AddCommGroup G]
    (q : G → G) (a b c x : G) : G :=
  (q (x + a + b + c) - q (x + a + b)) -
    (q (x + a + c) - q (x + a)) -
      ((q (x + b + c) - q (x + b)) - (q (x + c) - q x))

private lemma norm_stdAddChar_sub_sub_one_le {M : ℕ} [NeZero M] (a b : ZMod M) :
    ‖ZMod.stdAddChar (a - b) - 1‖ ≤ ‖ZMod.stdAddChar a - 1‖ + ‖ZMod.stdAddChar b - 1‖ := by
  rw [norm_stdAddChar_sub_one]
  simpa only [Complex.dist_eq] using
    dist_triangle_right (ZMod.stdAddChar a) (ZMod.stdAddChar b) (1 : ℂ)

private lemma localQuadratic_thirdDifference_bound {N : ℕ}
    {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)} {a b c x : ZMod (2 * N + 1)}
    (hadd : ∀ w ∈ ({x, x + a, x + b, x + a + b} : Finset (ZMod (2 * N + 1))),
      φ (w + c) = φ w + φ c)
    {ε : ℝ} (happrox : ∀ w ∈ ({x, x + a, x + b, x + a + b} : Finset (ZMod (2 * N + 1))),
      ‖ZMod.stdAddChar (polarizationDefect φ w c) - 1‖ ≤ ε) :
    ‖ZMod.stdAddChar (thirdDifference (localQuadratic φ) a b c x) - 1‖ ≤ 4 * ε := by
  let e (w : ZMod (2 * N + 1)) := polarizationDefect φ w c
  have hp (w : ZMod (2 * N + 1))
      (hw : w ∈ ({x, x + a, x + b, x + a + b} : Finset (ZMod (2 * N + 1)))) :
      localQuadratic φ (w + c) - localQuadratic φ w =
        localQuadratic φ c + w * φ c + e w := by
    have h := localQuadratic_polarization (hadd w hw)
    dsimp [e]
    linear_combination h
  have hdiff : thirdDifference (localQuadratic φ) a b c x =
      (e (x + a + b) - e (x + a)) - (e (x + b) - e x) := by
    unfold thirdDifference
    rw [hp (x + a + b) (by simp), hp (x + a) (by simp), hp (x + b) (by simp), hp x (by simp)]
    ring
  rw [hdiff]
  calc
    _ ≤ ‖ZMod.stdAddChar (e (x + a + b) - e (x + a)) - 1‖ +
          ‖ZMod.stdAddChar (e (x + b) - e x) - 1‖ := norm_stdAddChar_sub_sub_one_le _ _
    _ ≤ (ε + ε) + (ε + ε) := by
      apply add_le_add
      · exact (norm_stdAddChar_sub_sub_one_le _ _).trans
          (add_le_add (happrox _ (by simp)) (happrox _ (by simp)))
      · exact (norm_stdAddChar_sub_sub_one_le _ _).trans
          (add_le_add (happrox _ (by simp)) (happrox _ (by simp)))
    _ = _ := by ring

private lemma localQuadratic_thirdDifference_eq_zero {N : ℕ}
    {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)} {a b c x : ZMod (2 * N + 1)}
    (ha : φ (x + a) = φ x + φ a)
    (hb : φ (x + b) = φ x + φ b)
    (hab : φ (x + a + b) = φ x + φ a + φ b)
    (hc : φ (x + c) = φ x + φ c)
    (hac : φ (x + a + c) = φ x + φ a + φ c)
    (hbc : φ (x + b + c) = φ x + φ b + φ c)
    (habc : φ (x + a + b + c) = φ x + φ a + φ b + φ c) :
    thirdDifference (localQuadratic φ) a b c x = 0 := by
  unfold thirdDifference localQuadratic
  rw [ha, hb, hab, hc, hac, hbc, habc]
  ring

private lemma localQuadratic_bohr_thirdDifference {N : ℕ}
    (Ω : Finset (ZMod (2 * N + 1))) {R : ℝ} {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)}
    (hadd : ∀ a ∈ bohrSet Ω R, ∀ b ∈ bohrSet Ω R,
      a + b ∈ bohrSet Ω R → φ (a + b) = φ a + φ b)
    {a b c x : ZMod (2 * N + 1)}
    (hx : x ∈ bohrSet Ω (R / 4)) (ha : a ∈ bohrSet Ω (R / 4))
    (hb : b ∈ bohrSet Ω (R / 4)) (hc : c ∈ bohrSet Ω (R / 4)) (hR : 0 ≤ R) :
    thirdDifference (localQuadratic φ) a b c x = 0 := by
  have h₁ : bohrSet Ω (R / 4) ⊆ bohrSet Ω R := bohrSet_mono (by linarith)
  have h₂ : bohrSet Ω (R / 4 + R / 4) ⊆ bohrSet Ω R := bohrSet_mono (by linarith)
  have h₃ : bohrSet Ω (R / 4 + R / 4 + R / 4) ⊆ bohrSet Ω R := bohrSet_mono (by linarith)
  have h₄ : bohrSet Ω (R / 4 + R / 4 + R / 4 + R / 4) ⊆ bohrSet Ω R :=
    bohrSet_mono (by linarith)
  have hxa := add_mem_bohrSet hx ha
  have hxb := add_mem_bohrSet hx hb
  have hxab := add_mem_bohrSet hxa hb
  have Hxa := hadd _ (h₁ hx) _ (h₁ ha) (h₂ hxa)
  have Hxb := hadd _ (h₁ hx) _ (h₁ hb) (h₂ hxb)
  have Hxab := hadd _ (h₂ hxa) _ (h₁ hb) (h₃ hxab)
  have Hxc := hadd _ (h₁ hx) _ (h₁ hc) (h₂ (add_mem_bohrSet hx hc))
  have Hxac := hadd _ (h₂ hxa) _ (h₁ hc) (h₃ (add_mem_bohrSet hxa hc))
  have Hxbc := hadd _ (h₂ hxb) _ (h₁ hc) (h₃ (add_mem_bohrSet hxb hc))
  have Hxabc := hadd _ (h₃ hxab) _ (h₁ hc) (h₄ (add_mem_bohrSet hxab hc))
  rw [Hxa] at Hxab Hxac
  rw [Hxb] at Hxbc
  rw [Hxab] at Hxabc
  exact localQuadratic_thirdDifference_eq_zero Hxa Hxb Hxab Hxc Hxac Hxbc Hxabc

private lemma localQuadratic_bohr_progression {N : ℕ}
    (Ω : Finset (ZMod (2 * N + 1))) {R : ℝ} {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)}
    (hadd : ∀ a ∈ bohrSet Ω R, ∀ b ∈ bohrSet Ω R,
      a + b ∈ bohrSet Ω R → φ (a + b) = φ a + φ b)
    {x d : ZMod (2 * N + 1)} (hx : x ∈ bohrSet Ω (R / 4))
    (hd : d ∈ bohrSet Ω (R / 4)) (hR : 0 ≤ R) :
    localQuadratic φ (x + 3 * d) - 3 * localQuadratic φ (x + 2 * d) +
      3 * localQuadratic φ (x + d) - localQuadratic φ x = 0 := by
  have h := localQuadratic_bohr_thirdDifference Ω hadd hx hd hd hd hR
  unfold thirdDifference at h
  rw [show x + d + d + d = x + 3 * d by ring, show x + d + d = x + 2 * d by ring] at h
  linear_combination h

end LocalQuadraticPhase

section QuadraticModelCount

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

private noncomputable def pairWeight (f : G → ℝ) (p : G × G) : ℝ := f p.1 * f p.2

private def pairLinearForm (c : ℕ) (p : G × G) : G := p.1 + c • p.2

private noncomputable def weightedFibre (f : G → ℝ) (c : ℕ) (z : G) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (G × G)) with pairLinearForm c p = z, pairWeight f p

private lemma sum_weightedFibre (f : G → ℝ) (c : ℕ) :
    ∑ z, weightedFibre f c z = (∑ x, f x) ^ 2 := by
  calc
    _ = ∑ p : G × G, pairWeight f p :=
      Finset.sum_fiberwise_of_maps_to (fun p (_ : p ∈ Finset.univ) => Finset.mem_univ (pairLinearForm c p)) _
    _ = _ := by rw [Fintype.sum_prod_type, sq, Finset.sum_mul]; simp [pairWeight, Finset.mul_sum]

private lemma sum_sq_weightedFibre (f : G → ℝ) (c : ℕ) :
    ∑ z, weightedFibre f c z ^ 2 =
      ∑ p : G × G, ∑ q : G × G with pairLinearForm c q = pairLinearForm c p,
        pairWeight f p * pairWeight f q := by
  let L := pairLinearForm (G := G) c
  let u := weightedFibre f c
  let w := pairWeight f
  have hmaps : ((Finset.univ : Finset (G × G)) : Set (G × G)).MapsTo L (Finset.univ : Finset G) :=
    fun _ _ => Finset.mem_univ _
  change (∑ z, u z ^ 2) = ∑ p : G × G, ∑ q : G × G with L q = L p, w p * w q
  calc
    _ = ∑ z : G, ∑ p : G × G with L p = z, w p * u (L p) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [sq]
      change ((∑ p : G × G with L p = z, w p) * u z) = _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ p, w p * u (L p) := Finset.sum_fiberwise_of_maps_to hmaps _
    _ = _ := by
      refine Finset.sum_congr rfl fun p _ => ?_
      change w p * (∑ q : G × G with L q = L p, w q) = _
      rw [Finset.mul_sum]

private lemma quadratic_model_count_lower (f : G → ℝ) :
    (∑ x, f x) ^ 4 ≤
      (Fintype.card G : ℝ) * ∑ p : G × G, ∑ q : G × G with q.1 + 3 • q.2 = p.1 + 3 • p.2,
        f p.1 * f p.2 * (f q.1 * f q.2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset G) (fun _ => (1 : ℝ))
    (weightedFibre f 3)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [mul_one, sum_weightedFibre, sum_sq_weightedFibre] at h
  change (∑ x, f x) ^ 4 ≤
    (Fintype.card G : ℝ) * ∑ p : G × G, ∑ q : G × G with pairLinearForm 3 q = pairLinearForm 3 p,
      pairWeight f p * pairWeight f q
  exact (show (∑ x, f x) ^ 4 = ((∑ x, f x) ^ 2) ^ 2 by ring).le.trans h

end QuadraticModelCount

section TwistedCorrelation

variable {M : ℕ} [NeZero M]

private lemma sum_translate_cyclic (F : ZMod M → ℂ) (t : ZMod M) :
    (∑ x, F (x + t)) = ∑ x, F x :=
  Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)

private noncomputable def derivativeSummand (g : ZMod M → ℝ) (ξ : ZMod M → ZMod M)
    (h x : ZMod M) : ℂ :=
  ZMod.stdAddChar (-(x * ξ h)) * ((g x : ℂ) * (g (x + h) : ℂ))

private lemma sum_derivativeSummand (g : ZMod M → ℝ) (ξ : ZMod M → ZMod M) (h : ZMod M) :
    ∑ x, derivativeSummand g ξ h x = fourier (cyclicDerivative g h) (ξ h) := by
  simp only [fourier, ZMod.dft_apply, derivativeSummand, cyclicDerivative, Complex.ofReal_mul, smul_eq_mul]

private lemma exists_translated_derivative_correlation (g : ZMod M → ℝ)
    (J B : Finset (ZMod M)) (ξ : ZMod M → ZMod M) {θ : ℝ}
    (hcoeff : ∀ h ∈ J, θ ≤ ‖fourier (cyclicDerivative g h) (ξ h)‖) :
    let w := fun h => align (fourier (cyclicDerivative g h) (ξ h))
    ∃ x₀ : ZMod M, (B.card : ℝ) * (J.card : ℝ) * θ ≤ (M : ℝ) *
      ‖∑ h ∈ J, w h * ∑ t ∈ B, derivativeSummand g ξ h (x₀ + t)‖ := by
  let V := fun h => fourier (cyclicDerivative g h) (ξ h)
  let w := fun h => align (V h)
  let L (x₀ : ZMod M) := ∑ h ∈ J, w h * ∑ t ∈ B, derivativeSummand g ξ h (x₀ + t)
  have hsum : ∑ x₀, L x₀ = (B.card : ℂ) * ∑ h ∈ J, (‖V h‖ : ℂ) := by
    unfold L
    rw [Finset.sum_comm]
    calc
      _ = ∑ h ∈ J, w h * ∑ x₀, ∑ t ∈ B, derivativeSummand g ξ h (x₀ + t) := by
        simp only [Finset.mul_sum]
      _ = ∑ h ∈ J, w h * ((B.card : ℂ) * V h) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.sum_comm]
        simp only [sum_translate_cyclic, sum_derivativeSummand, Finset.sum_const, nsmul_eq_mul, V]
      _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [mul_left_comm, show w h * V h = (‖V h‖ : ℂ) from align_mul _]
  have hre : ∑ x₀, (L x₀).re = (B.card : ℝ) * ∑ h ∈ J, ‖V h‖ := by
    simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using congrArg Complex.re hsum
  obtain ⟨x₀, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod M))
    (fun x => (L x).re) Finset.univ_nonempty
  refine ⟨x₀, ?_⟩
  have hV : (J.card : ℝ) * θ ≤ ∑ h ∈ J, ‖V h‖ := by
    calc
      _ = ∑ _ ∈ J, θ := by simp
      _ ≤ _ := Finset.sum_le_sum hcoeff
  calc
    _ ≤ (B.card : ℝ) * ∑ h ∈ J, ‖V h‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hV (by positivity)
    _ = ∑ x, (L x).re := hre.symm
    _ ≤ ∑ _ : ZMod M, (L x₀).re := Finset.sum_le_sum hmax
    _ = (M : ℝ) * (L x₀).re := by simp [ZMod.card]
    _ ≤ _ := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (Complex.abs_re_le_norm _)) (by positivity)

private lemma affine_frequency_on_slice {J : Finset (ZMod M)} (hJ : J.Nonempty)
    {Ω : Finset (ZMod M)} {R : ℝ} (hR : R ≤ 1 / 4) (s : ZMod M)
    (ξ φ : ZMod M → ZMod M) (hpos : ∀ a ∈ J, a - s ∈ bohrSet Ω R)
    (hdiff : ∀ a ∈ J, ∀ b ∈ J, φ (a - b) = ξ a - ξ b)
    (hadd : ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b) :
    ∃ freqOffset : ZMod M, ∀ a ∈ J, ξ a = freqOffset + φ (a - s) := by
  obtain ⟨a₀, ha₀⟩ := hJ
  refine ⟨ξ a₀ - φ (a₀ - s), ?_⟩
  intro a ha
  have hIn : bohrSet Ω R ⊆ bohrSet Ω (1 / 2) := bohrSet_mono (by linarith only [hR])
  have hA := diff_mem_bohrSet (hpos a ha) (hpos a₀ ha₀)
  have he : (a - s) - (a₀ - s) = a - a₀ := by abel
  rw [he] at hA
  have hD := bohrSet_mono (show R + R ≤ 1 / 2 by linarith only [hR]) hA
  have hsum : a - a₀ + (a₀ - s) = a - s := by abel
  have hlocal := hadd (a - a₀) hD (a₀ - s) (hIn (hpos a₀ ha₀))
    (by rw [hsum]; exact hIn (hpos a ha))
  rw [hsum, hdiff a ha a₀ ha₀] at hlocal
  rw [hlocal]
  abel

private lemma exists_local_twisted_correlation_rect (g : ZMod M → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (J A B : Finset (ZMod M)) (s freqOffset : ZMod M) (ξ φ : ZMod M → ZMod M)
    (hpos : ∀ h ∈ J, h - s ∈ B) (haff : ∀ h ∈ J, ξ h = freqOffset + φ (h - s)) {θ : ℝ}
    (hc : ∀ h ∈ J, θ ≤ ‖fourier (cyclicDerivative g h) (ξ h)‖) :
    ∃ x₀ : ZMod M, ∃ U V W : ZMod M → ℂ,
      (∀ x, U x = (g (x₀ + x) : ℂ) * ZMod.stdAddChar (-(x * freqOffset))) ∧
      (∀ z, W z = (g (x₀ + s + z) : ℂ)) ∧
      (∀ x, ‖U x‖ ≤ 1) ∧ (∀ x, ‖V x‖ ≤ 1) ∧ (∀ x, ‖W x‖ ≤ 1) ∧
      (A.card : ℝ) * (J.card : ℝ) * θ ≤ (M : ℝ) *
        ‖∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y))‖ := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_translated_derivative_correlation g J A ξ hc
  let w (h : ZMod M) := align (fourier (cyclicDerivative g h) (ξ h))
  let U (x : ZMod M) := (g (x₀ + x) : ℂ) * ZMod.stdAddChar (-(x * freqOffset))
  let V (y : ZMod M) := if s + y ∈ J then w (s + y) * ZMod.stdAddChar (-(x₀ * ξ (s + y))) else 0
  let W (z : ZMod M) := (g (x₀ + s + z) : ℂ)
  have hgn (x : ZMod M) : ‖(g x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hg x
  have hU (x : ZMod M) : ‖U x‖ ≤ 1 := by
    simpa only [U, norm_mul, norm_stdAddChar, mul_one] using hgn (x₀ + x)
  have hV (y : ZMod M) : ‖V y‖ ≤ 1 := by
    unfold V
    split_ifs
    · rw [norm_mul, norm_stdAddChar, mul_one]
      exact norm_align_le _
    · simp
  have hW (z : ZMod M) : ‖W z‖ ≤ 1 := hgn (x₀ + s + z)
  refine ⟨x₀, U, V, W, fun _ => rfl, fun _ => rfl, hU, hV, hW, ?_⟩
  let F (h : ZMod M) := w h * ∑ x ∈ A, derivativeSummand g ξ h (x₀ + x)
  let Y := B.filter (fun y => s + y ∈ J)
  have hreindex : ∑ h ∈ J, F h = ∑ y ∈ Y, F (s + y) := by
    refine Finset.sum_bij (fun h _ => h - s) ?_ ?_ ?_ ?_
    · intro h hh
      exact Finset.mem_filter.mpr ⟨hpos h hh, by rwa [add_comm s, sub_add_cancel]⟩
    · intro h _ h' _ he
      exact sub_left_injective he
    · intro y hy
      have hm : s + y ∈ J := (Finset.mem_filter.mp hy).2
      exact ⟨s + y, hm, by abel⟩
    · intro h _
      rw [add_comm s, sub_add_cancel]
  have hterm (y : ZMod M) (hy : s + y ∈ J) :
      F (s + y) = ∑ x ∈ A, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y)) := by
    unfold F
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hf : ξ (s + y) = freqOffset + φ y := by simpa only [add_comm s, add_sub_cancel_right] using haff _ hy
    simp only [derivativeSummand, U, V, if_pos hy, W]
    have harg : x₀ + x + (s + y) = x₀ + s + (x + y) := by abel
    rw [harg]
    have hphase : -( (x₀ + x) * ξ (s + y)) =
        -(x * freqOffset) + -(x₀ * ξ (s + y)) + -(x * φ y) := by rw [hf]; ring
    rw [hphase, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring
  have hsum : ∑ h ∈ J, F h =
      ∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y)) := by
    rw [hreindex]
    calc
      _ = ∑ y ∈ B, if s + y ∈ J then F (s + y) else 0 := by rw [← Finset.sum_filter]
      _ = _ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hy : s + y ∈ J
        · rw [if_pos hy, hterm y hy]
        · simp [hy, V]
  rw [← hsum]
  exact hx₀

private lemma exists_local_twisted_correlation (g : ZMod M → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (J B : Finset (ZMod M)) (s freqOffset : ZMod M) (ξ φ : ZMod M → ZMod M)
    (hpos : ∀ h ∈ J, h - s ∈ B) (haff : ∀ h ∈ J, ξ h = freqOffset + φ (h - s)) {θ : ℝ}
    (hc : ∀ h ∈ J, θ ≤ ‖fourier (cyclicDerivative g h) (ξ h)‖) :
    ∃ x₀ : ZMod M, ∃ U V W : ZMod M → ℂ,
      (∀ x, U x = (g (x₀ + x) : ℂ) * ZMod.stdAddChar (-(x * freqOffset))) ∧
      (∀ z, W z = (g (x₀ + s + z) : ℂ)) ∧
      (∀ x, ‖U x‖ ≤ 1) ∧ (∀ x, ‖V x‖ ≤ 1) ∧ (∀ x, ‖W x‖ ≤ 1) ∧
      (B.card : ℝ) * (J.card : ℝ) * θ ≤ (M : ℝ) *
        ‖∑ y ∈ B, ∑ x ∈ B, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y))‖ := by
  exact exists_local_twisted_correlation_rect g hg J B B s freqOffset ξ φ hpos haff hc

end TwistedCorrelation

section Exchange

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

private lemma sum_equal_sum_pairs_reindex (A B : Finset G) (K : G → G → ℂ) :
    (∑ p ∈ A ×ˢ B, ∑ q ∈ A ×ˢ B with q.1 + q.2 = p.1 + p.2, K p.1 p.2 * conj (K q.1 q.2)) =
      ∑ t ∈ A - B, ∑ a ∈ B, ∑ b ∈ B,
        if t + a ∈ A ∧ t + b ∈ A then K (t + a) b * conj (K (t + b) a) else 0 := by
  let D := ((A ×ˢ B) ×ˢ (A ×ˢ B)).filter (fun z => z.2.1 + z.2.2 = z.1.1 + z.1.2)
  let E := ((A - B) ×ˢ B ×ˢ B).filter (fun z => z.1 + z.2.1 ∈ A ∧ z.1 + z.2.2 ∈ A)
  let F (z : (G × G) × (G × G)) : G × G × G := (z.1.1 - z.2.2, z.2.2, z.1.2)
  let I (z : G × G × G) : (G × G) × (G × G) :=
    ((z.1 + z.2.1, z.2.2), (z.1 + z.2.2, z.2.1))
  have hInv (z : (G × G) × (G × G)) (hz : z ∈ D) : I (F z) = z := by
    have h := (Finset.mem_filter.mp hz).2
    apply Prod.ext
    · apply Prod.ext
      · change z.1.1 - z.2.2 + z.2.2 = z.1.1
        abel
      · rfl
    · apply Prod.ext
      · change z.1.1 - z.2.2 + z.1.2 = z.2.1
        calc
          _ = (z.1.1 + z.1.2) - z.2.2 := by abel
          _ = _ := by rw [← h]; abel
      · rfl
  calc
    _ = ∑ z ∈ D, K z.1.1 z.1.2 * conj (K z.2.1 z.2.2) := by
      unfold D
      simp only [Finset.sum_filter, Finset.sum_product]
    _ = ∑ z ∈ E, K (I z).1.1 (I z).1.2 * conj (K (I z).2.1 (I z).2.2) := by
      refine Finset.sum_bij (fun x _ => F x) ?_ ?_ ?_ ?_
      · intro x hx
        obtain ⟨hp, hq⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
        obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hp
        obtain ⟨hqA, hqB⟩ := Finset.mem_product.mp hq
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.sub_mem_sub hpA hqB,
          Finset.mem_product.mpr ⟨hqB, hpB⟩⟩, ?_⟩
        change (I (F x)).1.1 ∈ A ∧ (I (F x)).2.1 ∈ A
        rw [hInv x hx]
        exact ⟨hpA, hqA⟩
      · intro x hx y hy h
        rw [← hInv x hx, ← hInv y hy, h]
      · rintro ⟨t, a, b⟩ hz
        obtain ⟨hab, ht⟩ := Finset.mem_filter.mp hz
        obtain ⟨_, hab'⟩ := Finset.mem_product.mp hab
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab'
        refine ⟨((t + a, b), (t + b, a)), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
            Finset.mem_product.mpr ⟨ht.1, hb⟩, Finset.mem_product.mpr ⟨ht.2, ha⟩⟩, ?_⟩
          change t + b + a = t + a + b
          abel
        · simp [F]
      · intros x hx
        rw [hInv x hx]
    _ = _ := by
      unfold E
      rw [Finset.sum_filter, Finset.sum_product]
      simp_rw [Finset.sum_product]
      rfl

private lemma abs_sq_sum_le_card_sum_exchanged (A B : Finset G) (K : G → G → ℂ) :
    ‖∑ y ∈ B, ∑ x ∈ A, K x y‖ ^ 2 ≤ ((A + B).card : ℝ) *
      ∑ t ∈ A - B, ‖∑ a ∈ B, ∑ b ∈ B,
        if t + a ∈ A ∧ t + b ∈ A then K (t + a) b * conj (K (t + b) a) else 0‖ := by
  let F (z : G) := ∑ p ∈ A ×ˢ B with p.1 + p.2 = z, K p.1 p.2
  have hMaps : ((A ×ˢ B : Finset (G × G)) : Set (G × G)).MapsTo (fun p => p.1 + p.2) ((A + B : Finset G) : Set G) :=
    fun p hp => Finset.add_mem_add (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
  have hsum : (∑ z ∈ A + B, F z) = ∑ y ∈ B, ∑ x ∈ A, K x y := by
    unfold F
    rw [Finset.sum_fiberwise_of_maps_to hMaps, Finset.sum_product_right]
  have hF : ‖∑ z ∈ A + B, F z‖ ^ 2 ≤ ((A + B).card : ℝ) * ∑ z ∈ A + B, ‖F z‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le (A + B) F) 2
    have hc := Finset.sum_mul_sq_le_sq_mul_sq (A + B) (fun _ => (1 : ℝ)) (fun z => ‖F z‖)
    exact h.trans (by simpa using hc)
  have hReindex : (∑ z ∈ A + B, ((‖F z‖ ^ 2 : ℝ) : ℂ)) =
      ∑ t ∈ A - B, ∑ a ∈ B, ∑ b ∈ B,
        if t + a ∈ A ∧ t + b ∈ A then K (t + a) b * conj (K (t + b) a) else 0 := by
    rw [← sum_equal_sum_pairs_reindex]
    calc
      _ = ∑ z ∈ A + B, ∑ p ∈ A ×ˢ B with p.1 + p.2 = z,
          K p.1 p.2 * conj (F (p.1 + p.2)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [complex_ofReal_sq_norm]
        change ((∑ p ∈ A ×ˢ B with p.1 + p.2 = z, K p.1 p.2) * conj (F z)) = _
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
      _ = ∑ p ∈ A ×ˢ B, K p.1 p.2 * conj (F (p.1 + p.2)) :=
        Finset.sum_fiberwise_of_maps_to hMaps _
      _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        unfold F
        rw [map_sum, Finset.mul_sum]
  have hnorm : (∑ z ∈ A + B, ‖F z‖ ^ 2) ≤ ∑ t ∈ A - B,
      ‖∑ a ∈ B, ∑ b ∈ B,
        if t + a ∈ A ∧ t + b ∈ A then K (t + a) b * conj (K (t + b) a) else 0‖ := by
    rw [← Complex.ofReal_sum] at hReindex
    have h := congrArg norm hReindex
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    rw [h]
    exact norm_sum_le _ _
  rw [← hsum]
  exact hF.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))

end Exchange

section SkewCorrelation

variable {M : ℕ} [NeZero M]

private lemma exists_skew_correlation_from_twist (A B : Finset (ZMod M))
    (hA : A.Nonempty) (hB : B.Nonempty) (U V W : ZMod M → ℂ) (φ : ZMod M → ZMod M)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ x, ‖V x‖ ≤ 1) :
    ∃ t ∈ A - B, ∃ P : ZMod M → ℂ, (∀ x, ‖P x‖ ≤ 1) ∧
      ‖∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y))‖ ^ 2 ≤
        ((A + B).card : ℝ) * ((A - B).card : ℝ) *
          ‖∑ a ∈ B, ∑ b ∈ B, P a * conj (P b) * ((‖W (t + a + b)‖ ^ 2 : ℝ) : ℂ) *
            ZMod.stdAddChar (b * φ a - a * φ b)‖ := by
  classical
  let K (x y : ZMod M) := U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y))
  let Z (t : ZMod M) := ∑ a ∈ B, ∑ b ∈ B,
    if t + a ∈ A ∧ t + b ∈ A then K (t + a) b * conj (K (t + b) a) else 0
  have hAB : (A - B).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact ⟨a - b, Finset.sub_mem_sub ha hb⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image (A - B) (fun t => ‖Z t‖) hAB
  let P (x : ZMod M) := if t + x ∈ A then
    U (t + x) * conj (V x) * ZMod.stdAddChar (t * φ x) else 0
  have hP (x : ZMod M) : ‖P x‖ ≤ 1 := by
    unfold P
    split_ifs
    · rw [norm_mul, norm_stdAddChar, norm_mul, Complex.norm_conj, mul_one]
      calc
        _ ≤ (1 : ℝ) * 1 := by gcongr <;> first | apply hU | apply hV
        _ = 1 := by norm_num
    · simp
  refine ⟨t, ht, P, hP, ?_⟩
  have hTwist : ‖∑ y ∈ B, ∑ x ∈ A, K x y‖ ^ 2 ≤
      ((A + B).card : ℝ) * (((A - B).card : ℝ) * ‖Z t‖) := by
    refine (abs_sq_sum_le_card_sum_exchanged A B K).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc
      _ ≤ ∑ _ ∈ A - B, ‖Z t‖ := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hZ : Z t = ∑ a ∈ B, ∑ b ∈ B, P a * conj (P b) * ((‖W (t + a + b)‖ ^ 2 : ℝ) : ℂ) *
      ZMod.stdAddChar (b * φ a - a * φ b) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases ha : t + a ∈ A <;> by_cases hb : t + b ∈ A
    · simp only [ha, hb, and_self, ite_true, K, P, map_mul, conj_stdAddChar, neg_neg, Complex.conj_conj]
      rw [add_right_comm t b a]
      have hphase : ZMod.stdAddChar (-((t + a) * φ b)) * ZMod.stdAddChar ((t + b) * φ a) =
          ZMod.stdAddChar (t * φ a) * ZMod.stdAddChar (-(t * φ b)) *
            ZMod.stdAddChar (b * φ a - a * φ b) := by
        simp only [← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [complex_ofReal_sq_norm]
      linear_combination
        (U (t + a) * V b * W (t + a + b) * conj (U (t + b)) * conj (V a) *
          conj (W (t + a + b))) * hphase
    · simp [ha, hb, P]
    · simp [ha, hb, P]
    · simp [ha, hb, P]
  rw [hZ, ← mul_assoc] at hTwist
  exact hTwist

private lemma regular_bohr_add_sub_card (Ω : Finset (ZMod M)) {R γ η : ℝ}
    (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ)) :
    let A := bohrSet Ω R
    let B := bohrSet Ω γ
    ((A + B).card : ℝ) ≤ (1 + η) * (A.card : ℝ) ∧
      ((A - B).card : ℝ) ≤ (1 + η) * (A.card : ℝ) := by
  let A := bohrSet Ω R
  let B := bohrSet Ω γ
  let O := bohrSet Ω (R + γ)
  have hsum : A + B ⊆ O := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    exact add_mem_bohrSet ha hb
  have hdiff : A - B ⊆ O := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    exact diff_mem_bohrSet ha hb
  have hcard : (O.card : ℝ) ≤ (1 + η) * (A.card : ℝ) := by
    refine hband.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact_mod_cast Finset.card_le_card (bohrSet_mono (show R - γ ≤ R by linarith) :
      bohrSet Ω (R - γ) ⊆ A)
  exact ⟨(by exact_mod_cast Finset.card_le_card hsum : ((A + B).card : ℝ) ≤ O.card).trans hcard,
    (by exact_mod_cast Finset.card_le_card hdiff : ((A - B).card : ℝ) ≤ O.card).trans hcard⟩

end SkewCorrelation

section AveragedProducts

variable {X Y T : Type*}

private lemma norm_sum_sq_le_card {I : Type*} (A : Finset I) (f : I → ℂ) :
    ‖∑ a ∈ A, f a‖ ^ 2 ≤ (A.card : ℝ) * ∑ a ∈ A, ‖f a‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le A f) 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  exact h.trans (by simpa using hc)

private lemma norm_sum_product_sq_le_card (A : Finset X) (B : Finset Y)
    (f : X → Y → ℂ) :
    ‖∑ x ∈ A, ∑ y ∈ B, f x y‖ ^ 2 ≤ (A.card : ℝ) * (B.card : ℝ) *
      ∑ x ∈ A, ∑ y ∈ B, ‖f x y‖ ^ 2 := by
  simpa only [Finset.sum_product, Finset.card_product, Nat.cast_mul] using
    norm_sum_sq_le_card (A ×ˢ B) (fun z => f z.1 z.2)

private lemma sum_sq_averaged_products (A : Finset X) (B : Finset Y)
    (T₀ : Finset T) (P : T → X → ℂ) (Q : T → Y → ℂ) :
    ((∑ x ∈ A, ∑ y ∈ B, ‖∑ t ∈ T₀, P t x * Q t y‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ T₀, ∑ u ∈ T₀, (∑ x ∈ A, P t x * conj (P u x)) *
        (∑ y ∈ B, Q t y * conj (Q u y)) := by
  let F (x : X) (y : Y) (t u : T) :=
    (P t x * conj (P u x)) * (Q t y * conj (Q u y))
  calc
    _ = ∑ x ∈ A, ∑ y ∈ B, ∑ t ∈ T₀, ∑ u ∈ T₀, F x y t u := by
      simp only [Complex.ofReal_sum, complex_ofReal_sq_norm, map_sum, map_mul,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by dsimp [F]; ring
    _ = ∑ x ∈ A, ∑ t ∈ T₀, ∑ y ∈ B, ∑ u ∈ T₀, F x y t u :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ t ∈ T₀, ∑ x ∈ A, ∑ y ∈ B, ∑ u ∈ T₀, F x y t u := Finset.sum_comm
    _ = ∑ t ∈ T₀, ∑ u ∈ T₀, ∑ x ∈ A, ∑ y ∈ B, F x y t u := by
      refine Finset.sum_congr rfl fun t _ => ?_
      calc
        _ = ∑ x ∈ A, ∑ u ∈ T₀, ∑ y ∈ B, F x y t u :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]

private lemma norm_weighted_averaged_products (A : Finset X) (B : Finset Y)
    (T₀ : Finset T) (P : T → X → ℂ) (Q : T → Y → ℂ) (w : X → Y → ℂ)
    (hw : ∀ x ∈ A, ∀ y ∈ B, ‖w x y‖ ≤ 1)
    (hQ : ∀ t ∈ T₀, ∀ y ∈ B, ‖Q t y‖ ≤ 1) :
    ‖∑ x ∈ A, ∑ y ∈ B, w x y * ∑ t ∈ T₀, P t x * Q t y‖ ^ 2 ≤
      (A.card : ℝ) * (B.card : ℝ) ^ 2 *
        ∑ t ∈ T₀, ∑ u ∈ T₀, ‖∑ x ∈ A, P t x * conj (P u x)‖ := by
  have hC : (∑ x ∈ A, ∑ y ∈ B, ‖∑ t ∈ T₀, P t x * Q t y‖ ^ 2) ≤
      (B.card : ℝ) * ∑ t ∈ T₀, ∑ u ∈ T₀, ‖∑ x ∈ A, P t x * conj (P u x)‖ := by
    have h := congrArg norm (sum_sq_averaged_products A B T₀ P Q)
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    rw [h, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => ?_)
    rw [norm_mul, mul_comm (B.card : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      _ ≤ ∑ y ∈ B, ‖Q t y * conj (Q u y)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ B, (1 : ℝ) := by
        refine Finset.sum_le_sum fun y hy => ?_
        simpa only [norm_mul, Complex.norm_conj, one_mul] using
          (mul_le_mul (hQ t ht y hy) (hQ u hu y hy) (norm_nonneg _) zero_le_one)
      _ = (B.card : ℝ) := by simp
  calc
    _ ≤ (A.card : ℝ) * (B.card : ℝ) * ∑ x ∈ A, ∑ y ∈ B,
        ‖w x y * ∑ t ∈ T₀, P t x * Q t y‖ ^ 2 := norm_sum_product_sq_le_card _ _ _
    _ ≤ (A.card : ℝ) * (B.card : ℝ) * ∑ x ∈ A, ∑ y ∈ B, ‖∑ t ∈ T₀, P t x * Q t y‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x hx =>
        Finset.sum_le_sum fun y hy => ?_) (by positivity)
      rw [norm_mul]
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) (hw x hx y hy)
    _ ≤ (A.card : ℝ) * (B.card : ℝ) * ((B.card : ℝ) *
        ∑ t ∈ T₀, ∑ u ∈ T₀, ‖∑ x ∈ A, P t x * conj (P u x)‖) :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    _ = _ := by ring

end AveragedProducts

section AveragedSkew

variable {M : ℕ} [NeZero M]

private def skewForm (φ : ZMod M → ZMod M) (a b : ZMod M) : ZMod M :=
  b * φ a - a * φ b

omit [NeZero M] in
private lemma skewForm_opposite_translate {φ : ZMod M → ZMod M} {a b t : ZMod M}
    (ha : φ (a + t) = φ a + φ t) (hb : φ (b - t) = φ b - φ t)
    (hab : φ (a + b) = φ a + φ b) :
    skewForm φ (a + t) (b - t) + skewForm φ (a + b) t = skewForm φ a b := by
  unfold skewForm
  rw [ha, hb, hab]
  ring

private lemma sum_truncated_translate {G R : Type*} [DecidableEq G] [AddCommGroup G] [AddCommMonoid R]
    (A E : Finset G) (t : G) (F : G → R) (hE : ∀ a ∈ A, a + t ∈ E) :
    (∑ x ∈ E, if x - t ∈ A then F x else 0) = ∑ a ∈ A, F (a + t) := by
  have hfilter : E.filter (fun x => x - t ∈ A) = A.image (fun x => x + t) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨_, hx⟩
      exact ⟨x - t, hx, sub_add_cancel _ _⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨hE a ha, by simpa only [add_sub_cancel_right] using ha⟩
  rw [← Finset.sum_filter, hfilter, Finset.sum_image]
  exact fun x _ y _ h => add_right_cancel h

private noncomputable def skewTranslate (A : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) (t x : ZMod M) : ℂ :=
  if x - t ∈ A then P (x - t) * ZMod.stdAddChar (skewForm φ x t) else 0

private lemma norm_skewTranslate_le (A : Finset (ZMod M)) (φ : ZMod M → ZMod M)
    {P : ZMod M → ℂ} (hP : ∀ x, ‖P x‖ ≤ 1) (t x : ZMod M) :
    ‖skewTranslate A φ P t x‖ ≤ 1 := by
  unfold skewTranslate
  split_ifs with h
  · rw [norm_mul, norm_stdAddChar, mul_one]
    exact hP _
  · simp

private lemma skewWeight_to_translation_correlation (A B C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P Q W : ZMod M → ℂ)
    (hQ : ∀ x, ‖Q x‖ ≤ 1) (hW : ∀ x, ‖W x‖ ≤ 1)
    (haddA : ∀ a ∈ A, ∀ t ∈ C, φ (a + t) = φ a + φ t)
    (hsubB : ∀ b ∈ B, ∀ t ∈ C, φ (b - t) = φ b - φ t)
    (haddAB : ∀ a ∈ A, ∀ b ∈ B, φ (a + b) = φ a + φ b) :
    (C.card : ℝ) ^ 2 *
      ‖∑ a ∈ A, ∑ b ∈ B, P a * Q b * W (a + b) * ZMod.stdAddChar (skewForm φ a b)‖ ^ 2 ≤
      ((A + C).card : ℝ) * ((B - C).card : ℝ) ^ 2 *
        ∑ t ∈ C, ∑ u ∈ C, ‖∑ x ∈ A + C,
          skewTranslate A φ P t x * conj (skewTranslate A φ P u x)‖ := by
  let E := A + C
  let D := B - C
  let L := skewTranslate A φ P
  let R (t y : ZMod M) := if y + t ∈ B then Q (y + t) * ZMod.stdAddChar (skewForm φ y t) else 0
  let w (x y : ZMod M) := W (x + y) * ZMod.stdAddChar (skewForm φ x y)
  let S := ∑ a ∈ A, ∑ b ∈ B, P a * Q b * W (a + b) * ZMod.stdAddChar (skewForm φ a b)
  have hw (x : ZMod M) (_ : x ∈ E) (y : ZMod M) (_ : y ∈ D) : ‖w x y‖ ≤ 1 := by
    simpa only [w, norm_mul, norm_stdAddChar, mul_one] using hW (x + y)
  have hR (t : ZMod M) (_ : t ∈ C) (y : ZMod M) (_ : y ∈ D) : ‖R t y‖ ≤ 1 := by
    unfold R
    split_ifs
    · rw [norm_mul, norm_stdAddChar, mul_one]
      exact hQ _
    · simp
  have hshift (t : ZMod M) (ht : t ∈ C) :
      (∑ x ∈ E, ∑ y ∈ D, w x y * (L t x * R t y)) = S := by
    have hA : ∀ a ∈ A, a + t ∈ E := fun a ha => Finset.add_mem_add ha ht
    have hB : ∀ b ∈ B, b + (-t) ∈ D := by
      intro b hb
      rw [← sub_eq_add_neg]
      exact Finset.sub_mem_sub hb ht
    have houter (x : ZMod M) :
        (∑ y ∈ D, w x y * (L t x * R t y)) =
        if x - t ∈ A then
          ∑ y ∈ D, w x y *
            ((P (x - t) * ZMod.stdAddChar (skewForm φ x t)) * R t y)
        else 0 := by
      by_cases hx : x - t ∈ A <;> simp [L, skewTranslate, hx]
    simp only [houter]
    rw [sum_truncated_translate A E t _ hA]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [add_sub_cancel_right]
    have hinner (y : ZMod M) :
        w (a + t) y * ((P a * ZMod.stdAddChar (skewForm φ (a + t) t)) * R t y) =
        if y - (-t) ∈ B then
          w (a + t) y * ((P a * ZMod.stdAddChar (skewForm φ (a + t) t)) *
            (Q (y + t) * ZMod.stdAddChar (skewForm φ y t)))
        else 0 := by
      by_cases hy : y + t ∈ B <;> simp [R, hy]
    simp only [hinner]
    rw [sum_truncated_translate B D (-t) _ hB]
    refine Finset.sum_congr rfl fun b hb => ?_
    have harg : a + t + (b + -t) = a + b := by abel
    have hbilin : skewForm φ (a + t) t + skewForm φ (b + -t) t = skewForm φ (a + b) t := by
      unfold skewForm
      rw [haddA a ha t ht, show b + -t = b - t by abel, hsubB b hb t ht, haddAB a ha b hb]
      ring
    have hphase : ZMod.stdAddChar (skewForm φ (a + t) (b + -t)) *
        (ZMod.stdAddChar (skewForm φ (a + t) t) * ZMod.stdAddChar (skewForm φ (b + -t) t)) =
          ZMod.stdAddChar (skewForm φ a b) := by
      rw [← AddChar.map_add_eq_mul, hbilin, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg,
        skewForm_opposite_translate (haddA a ha t ht) (hsubB b hb t ht) (haddAB a ha b hb)]
    dsimp only [w]
    rw [harg, show b + -t + t = b by abel]
    linear_combination (P a * Q b * W (a + b)) * hphase
  have havg : (∑ x ∈ E, ∑ y ∈ D, w x y * ∑ t ∈ C, L t x * R t y) = (C.card : ℂ) * S := by
    simp only [Finset.mul_sum]
    calc
      _ = ∑ x ∈ E, ∑ t ∈ C, ∑ y ∈ D, w x y * (L t x * R t y) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ t ∈ C, ∑ x ∈ E, ∑ y ∈ D, w x y * (L t x * R t y) := Finset.sum_comm
      _ = _ := by
        rw [Finset.sum_congr rfl hshift]
        simp
  have h := norm_weighted_averaged_products E D C L R w hw hR
  rw [havg, norm_mul, Complex.norm_natCast, mul_pow] at h
  exact h

end AveragedSkew

section SkewCovariance

variable {M : ℕ} [NeZero M]

private lemma skewTranslate_comp (A : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) {d t : ZMod M}
    (hdt : φ (d + t) = φ d + φ t)
    (hlocal : ∀ a ∈ A, φ (a + t + d) = φ (a + t) + φ d) (x : ZMod M) :
    ZMod.stdAddChar (skewForm φ x d) * skewTranslate A φ P t (x - d) =
      ZMod.stdAddChar (-skewForm φ d t) * skewTranslate A φ P (d + t) x := by
  have hshift : x - d - t = x - (d + t) := by abel
  unfold skewTranslate
  rw [hshift]
  by_cases hx : x - (d + t) ∈ A
  · simp only [if_pos hx]
    have hx' := hlocal (x - (d + t)) hx
    have h₁ : x - (d + t) + t = x - d := by abel
    rw [h₁, sub_add_cancel] at hx'
    have hphase : skewForm φ x d + skewForm φ (x - d) t =
        -skewForm φ d t + skewForm φ x (d + t) := by
      unfold skewForm
      rw [hdt, show φ (x - d) = φ x - φ d by rw [hx']; ring]
      ring
    have h := congrArg ZMod.stdAddChar hphase
    simp only [AddChar.map_add_eq_mul] at h
    linear_combination P (x - (d + t)) * h
  · simp [hx]

private noncomputable def skewCovariance (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) (x y : ZMod M) : ℂ :=
  ∑ t ∈ C, skewTranslate A φ P t x * conj (skewTranslate A φ P t y)

private lemma skewCovariance_translation (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) {d : ZMod M}
    (hdt : ∀ t ∈ C, φ (d + t) = φ d + φ t)
    (hlocal : ∀ t ∈ C, ∀ a ∈ A, φ (a + t + d) = φ (a + t) + φ d)
    (x y : ZMod M) :
    ZMod.stdAddChar (skewForm φ x d) * conj (ZMod.stdAddChar (skewForm φ y d)) *
        skewCovariance A C φ P (x - d) (y - d) =
      skewCovariance A (C.image (fun t => t + d)) φ P x y := by
  classical
  unfold skewCovariance
  rw [Finset.mul_sum, Finset.sum_image (fun t _ u _ h => add_right_cancel h)]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hx := skewTranslate_comp A φ P (hdt t ht) (hlocal t ht) x
  have hy := congrArg conj (skewTranslate_comp A φ P (hdt t ht) (hlocal t ht) y)
  simp only [map_mul] at hy
  rw [add_comm t d]
  have hunit : ZMod.stdAddChar (-skewForm φ d t) *
      conj (ZMod.stdAddChar (-skewForm φ d t)) = 1 := by
    rw [← complex_ofReal_sq_norm, norm_stdAddChar]
    norm_num
  calc
    _ = (ZMod.stdAddChar (skewForm φ x d) * skewTranslate A φ P t (x - d)) *
        (conj (ZMod.stdAddChar (skewForm φ y d)) * conj (skewTranslate A φ P t (y - d))) := by ring
    _ = _ := by
      rw [hx, hy]
      linear_combination (skewTranslate A φ P (d + t) x *
        conj (skewTranslate A φ P (d + t) y)) * hunit

private lemma norm_sum_sub_sum_le_sdiff {I : Type*} [DecidableEq I]
    (A B : Finset I) (F : I → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) :
    ‖(∑ x ∈ A, F x) - ∑ x ∈ B, F x‖ ≤ ((A \ B).card : ℝ) + ((B \ A).card : ℝ) := by
  let D := A ∩ B
  have hA := Finset.sum_sdiff (f := F) (show D ⊆ A from Finset.inter_subset_left)
  have hB := Finset.sum_sdiff (f := F) (show D ⊆ B from Finset.inter_subset_right)
  rw [show A \ D = A \ B by ext x; simp [D]] at hA
  rw [show B \ D = B \ A by ext x; simp [D, and_comm]] at hB
  rw [← hA, ← hB, add_sub_add_right_eq_sub]
  have hsum (E : Finset I) : ‖∑ x ∈ E, F x‖ ≤ (E.card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ E, ‖F x‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ E, (1 : ℝ) := Finset.sum_le_sum fun x _ => hF x
      _ = _ := by simp
  exact (norm_sub_le _ _).trans (add_le_add (hsum _) (hsum _))

private lemma skewCovariance_approx_translation (A Ω : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) (hP : ∀ x, ‖P x‖ ≤ 1) {R γ η : ℝ}
    (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    {d : ZMod M} (hd : d ∈ bohrSet Ω γ)
    (hdt : ∀ t ∈ bohrSet Ω R, φ (d + t) = φ d + φ t)
    (hlocal : ∀ t ∈ bohrSet Ω R, ∀ a ∈ A, φ (a + t + d) = φ (a + t) + φ d)
    (x y : ZMod M) :
    let C := bohrSet Ω R
    ‖ZMod.stdAddChar (skewForm φ x d) * conj (ZMod.stdAddChar (skewForm φ y d)) *
        skewCovariance A C φ P (x - d) (y - d) - skewCovariance A C φ P x y‖ ≤
      2 * η * (C.card : ℝ) := by
  dsimp only
  rw [skewCovariance_translation A _ φ P hdt hlocal]
  let C := bohrSet Ω R
  let D := C.image (fun t => t + d)
  let F (t : ZMod M) := skewTranslate A φ P t x * conj (skewTranslate A φ P t y)
  have hF (t : ZMod M) : ‖F t‖ ≤ 1 := by
    simpa only [F, norm_mul, Complex.norm_conj, one_mul] using
      (mul_le_mul (norm_skewTranslate_le A φ hP t x) (norm_skewTranslate_le A φ hP t y)
        (norm_nonneg _) zero_le_one)
  have hc := bohr_band_translation_card Ω hγ hη hband hd
  change ((C \ D).card : ℝ) + ((D \ C).card : ℝ) ≤ 2 * η * (C.card : ℝ) at hc
  rw [add_comm ((C \ D).card : ℝ)] at hc
  exact (norm_sum_sub_sum_le_sdiff D C F hF).trans hc

private lemma sum_sq_skewCovariance (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) :
    (∑ x ∈ A + C, ∑ y ∈ A + C, ‖skewCovariance A C φ P x y‖ ^ 2) =
      ∑ t ∈ C, ∑ u ∈ C,
        ‖∑ x ∈ A + C, skewTranslate A φ P t x * conj (skewTranslate A φ P u x)‖ ^ 2 := by
  let F := skewTranslate A φ P
  apply Complex.ofReal_injective
  refine (sum_sq_averaged_products (A + C) (A + C) C F (fun t x => conj (F t x))).trans ?_
  simp only [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  rw [complex_ofReal_sq_norm]
  congr 1
  simp only [map_sum, map_mul, Complex.conj_conj, F]

private lemma skewWeight_to_covariance_norm (A B C : Finset (ZMod M)) (hC : C.Nonempty)
    (φ : ZMod M → ZMod M) (P Q W : ZMod M → ℂ)
    (hQ : ∀ x, ‖Q x‖ ≤ 1) (hW : ∀ x, ‖W x‖ ≤ 1)
    (haddA : ∀ a ∈ A, ∀ t ∈ C, φ (a + t) = φ a + φ t)
    (hsubB : ∀ b ∈ B, ∀ t ∈ C, φ (b - t) = φ b - φ t)
    (haddAB : ∀ a ∈ A, ∀ b ∈ B, φ (a + b) = φ a + φ b) :
    (C.card : ℝ) ^ 2 *
      ‖∑ a ∈ A, ∑ b ∈ B, P a * Q b * W (a + b) * ZMod.stdAddChar (skewForm φ a b)‖ ^ 4 ≤
      ((A + C).card : ℝ) ^ 2 * ((B - C).card : ℝ) ^ 4 *
        ∑ x ∈ A + C, ∑ y ∈ A + C, ‖skewCovariance A C φ P x y‖ ^ 2 := by
  let S := ∑ a ∈ A, ∑ b ∈ B, P a * Q b * W (a + b) * ZMod.stdAddChar (skewForm φ a b)
  let E := A + C
  let D := B - C
  let F (t u : ZMod M) := ‖∑ x ∈ E, skewTranslate A φ P t x * conj (skewTranslate A φ P u x)‖
  have h := skewWeight_to_translation_correlation A B C φ P Q W hQ hW haddA hsubB haddAB
  change (C.card : ℝ) ^ 2 * ‖S‖ ^ 2 ≤ (E.card : ℝ) * (D.card : ℝ) ^ 2 *
    ∑ t ∈ C, ∑ u ∈ C, F t u at h
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (C ×ˢ C) (fun _ => (1 : ℝ)) (fun z => F z.1 z.2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, Finset.card_product,
    Nat.cast_mul, mul_one, Finset.sum_product] at hc
  have hCp : 0 < (C.card : ℝ) ^ 2 := by
    have : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
    positivity
  rw [sum_sq_skewCovariance]
  change (C.card : ℝ) ^ 2 * ‖S‖ ^ 4 ≤ (E.card : ℝ) ^ 2 * (D.card : ℝ) ^ 4 *
    ∑ t ∈ C, ∑ u ∈ C, F t u ^ 2
  apply le_of_mul_le_mul_left _ hCp
  calc
    _ = ((C.card : ℝ) ^ 2 * ‖S‖ ^ 2) ^ 2 := by ring
    _ ≤ ((E.card : ℝ) * (D.card : ℝ) ^ 2 * ∑ t ∈ C, ∑ u ∈ C, F t u) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h _
    _ = (E.card : ℝ) ^ 2 * (D.card : ℝ) ^ 4 * (∑ t ∈ C, ∑ u ∈ C, F t u) ^ 2 := by ring
    _ ≤ (E.card : ℝ) ^ 2 * (D.card : ℝ) ^ 4 *
        ((C.card : ℝ) * (C.card : ℝ) * ∑ t ∈ C, ∑ u ∈ C, F t u ^ 2) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

private lemma skewCovariance_trace_bound (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) (hP : ∀ x, ‖P x‖ ≤ 1) :
    (∑ x ∈ A + C, (skewCovariance A C φ P x x).re) ≤ (C.card : ℝ) * (A.card : ℝ) := by
  have hre (t x : ZMod M) :
      (skewTranslate A φ P t x * conj (skewTranslate A φ P t x)).re =
        if x - t ∈ A then ‖P (x - t)‖ ^ 2 else 0 := by
    rw [← complex_ofReal_sq_norm, Complex.ofReal_re]
    unfold skewTranslate
    split_ifs
    · rw [norm_mul, norm_stdAddChar, mul_one]
    · simp
  simp only [skewCovariance, Complex.re_sum, hre]
  rw [Finset.sum_comm]
  rw [show (C.card : ℝ) * (A.card : ℝ) = ∑ _ ∈ C, (A.card : ℝ) by simp]
  apply Finset.sum_le_sum
  intro t ht
  rw [sum_truncated_translate A (A + C) t (fun x => ‖P (x - t)‖ ^ 2)
    (fun a ha => Finset.add_mem_add ha ht)]
  calc
    _ ≤ ∑ _ ∈ A, (1 : ℝ) := by
      refine Finset.sum_le_sum fun a _ => ?_
      rw [add_sub_cancel_right, ← one_pow 2]
      exact pow_le_pow_left₀ (norm_nonneg _) (hP _) 2
    _ = _ := by simp

end SkewCovariance

section ApproximateMatrixCommutation

private lemma norm_prod_sub_prod_le {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    {r ε : ℝ} (hr : 1 ≤ r) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ r) (hg : ∀ i ∈ S, ‖g i‖ ≤ r)
    (hd : ∀ i ∈ S, ‖f i - g i‖ ≤ ε) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ (S.card : ℝ) * ε * r ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hmem : ∀ j ∈ S, j ∈ insert i S := fun j hj => Finset.mem_insert_of_mem hj
    have h₁ := ih (fun j hj => hf j (hmem j hj)) (fun j hj => hg j (hmem j hj))
      (fun j hj => hd j (hmem j hj))
    have hfS : ‖∏ j ∈ S, f j‖ ≤ r ^ S.card := by
      calc
        _ ≤ ∏ j ∈ S, ‖f j‖ := Finset.norm_prod_le _ _
        _ ≤ ∏ _ ∈ S, r := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun j hj => hf j (hmem j hj))
        _ = _ := by simp
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    rw [show f i * (∏ j ∈ S, f j) - g i * (∏ j ∈ S, g j) =
        (f i - g i) * (∏ j ∈ S, f j) + g i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j) by ring]
    calc
      _ ≤ ‖(f i - g i) * ∏ j ∈ S, f j‖ +
          ‖g i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j)‖ := norm_add_le _ _
      _ ≤ ε * r ^ S.card + r * ((S.card : ℝ) * ε * r ^ S.card) := by
        rw [norm_mul, norm_mul]
        exact add_le_add
          (mul_le_mul (hd i (Finset.mem_insert_self _ _)) hfS (norm_nonneg _) hε)
          (mul_le_mul (hg i (Finset.mem_insert_self _ _)) h₁ (norm_nonneg _) (by linarith))
      _ ≤ ε * (r ^ S.card * r) + r * ((S.card : ℝ) * ε * r ^ S.card) := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) hr
      _ = _ := by push_cast; rw [pow_succ]; ring

private lemma norm_det_sub_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) {r ε : ℝ} (hr : 1 ≤ r) (hε : 0 ≤ ε)
    (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ r)
    (hd : ∀ i j, ‖A i j - B i j‖ ≤ ε) :
    ‖A.det - B.det‖ ≤ ((Fintype.card ι).factorial : ℝ) *
      ((Fintype.card ι : ℝ) * ε * r ^ (Fintype.card ι)) := by
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : Equiv.Perm ι, (Fintype.card ι : ℝ) * ε * r ^ (Fintype.card ι) := by
      refine Finset.sum_le_sum fun σ _ => ?_
      rw [← mul_sub, norm_mul]
      have hsign : ‖((↑(Equiv.Perm.sign σ) : ℤ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      rw [hsign, one_mul]
      simpa only [Finset.card_univ] using norm_prod_sub_prod_le Finset.univ
        (fun i => A (σ i) i) (fun i => B (σ i) i) hr hε
        (fun i _ => hA _ _) (fun i _ => hB _ _) (fun i _ => hd _ _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

private lemma norm_pow_sub_one_le_of_matrix_commutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix ι ι ℂ) (z : ℂ) {r ε μ : ℝ} (hr : 1 ≤ r) (hε : 0 ≤ ε) (hμ : 0 < μ)
    (hU : ∀ i j, ‖(U * V) i j‖ ≤ r) (hV : ∀ i j, ‖(z • (V * U)) i j‖ ≤ r)
    (hD : ∀ i j, ‖(U * V) i j - (z • (V * U)) i j‖ ≤ ε)
    (hdet : μ ≤ ‖U.det * V.det‖) :
    ‖z ^ Fintype.card ι - 1‖ ≤ ((Fintype.card ι).factorial : ℝ) *
      ((Fintype.card ι : ℝ) * ε * r ^ (Fintype.card ι)) / μ := by
  have h := norm_det_sub_det_le (U * V) (z • (V * U)) hr hε hU hV hD
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul] at h
  rw [show U.det * V.det - z ^ Fintype.card ι * (V.det * U.det) =
    -(z ^ Fintype.card ι - 1) * (U.det * V.det) by ring, norm_mul, norm_neg] at h
  rw [le_div_iff₀ hμ]
  exact (mul_le_mul_of_nonneg_left hdet (norm_nonneg _)).trans h

end ApproximateMatrixCommutation

section Reslice

variable {M : ℕ} [NeZero M]

private lemma exists_large_translatedSlice_from_difference (J B : Finset (ZMod M))
    (hJ : J.Nonempty) (hB : B.Nonempty) :
    ∃ s ∈ J - B, J.card * B.card ≤ (J - B).card * (translatedSlice J B s).card := by
  have hD : (J - B).Nonempty := by
    obtain ⟨a, ha⟩ := hJ
    obtain ⟨b, hb⟩ := hB
    exact ⟨a - b, Finset.sub_mem_sub ha hb⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image (J - B) (fun s => (translatedSlice J B s).card) hD
  refine ⟨s, hs, ?_⟩
  have hsum : ∑ t ∈ J - B, (translatedSlice J B t).card =
      ∑ t : ZMod M, (translatedSlice J B t).card := by
    refine Finset.sum_subset (Finset.subset_univ _) fun t _ ht => ?_
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨a, ha⟩
    have h := Finset.mem_filter.mp ha
    exact ht (by simpa only [sub_sub_cancel] using Finset.sub_mem_sub h.1 h.2)
  calc
    _ = ∑ t ∈ J - B, (translatedSlice J B t).card := by rw [hsum, sum_card_translatedSlice]
    _ ≤ ∑ _ ∈ J - B, (translatedSlice J B s).card := Finset.sum_le_sum hmax
    _ = _ := by simp

omit [NeZero M] in
private lemma card_sub_le_of_translated_subset (J A B : Finset (ZMod M)) (s : ZMod M)
    (hJ : ∀ a ∈ J, a - s ∈ A) : (J - B).card ≤ (A - B).card := by
  apply Finset.card_le_card_of_injOn (fun x => x - s)
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    have he : a - b - s = (a - s) - b := by abel
    change a - b - s ∈ A - B
    rw [he]
    exact Finset.sub_mem_sub (hJ a ha) hb
  · intro x _ y _ h
    exact sub_left_injective h

private lemma exists_dense_reslice_subset (J : Finset (ZMod M)) (hJ : J.Nonempty)
    (B : Finset (ZMod M)) (hB : B.Nonempty) (Ω : Finset (ZMod M)) {R γ η β : ℝ}
    (hγ : 0 ≤ γ) (hBγ : B ⊆ bohrSet Ω γ) (hη : 0 ≤ η) (hβ : 0 < β) (s : ZMod M)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    (hpos : ∀ a ∈ J, a - s ∈ bohrSet Ω R)
    (hcard : β * ((bohrSet Ω R).card : ℝ) ≤ (J.card : ℝ)) :
    ∃ s', let T := translatedSlice J B s'
      T.Nonempty ∧ (β / (1 + η)) * (B.card : ℝ) ≤ (T.card : ℝ) := by
  let A := bohrSet Ω R
  have hA : A.Nonempty := by
    obtain ⟨a, ha⟩ := hJ
    exact ⟨a - s, hpos a ha⟩
  obtain ⟨s', _, hs⟩ := exists_large_translatedSlice_from_difference J B hJ hB
  let T := translatedSlice J B s'
  have hsub := card_sub_le_of_translated_subset J A B s hpos
  have hdiff : A - B ⊆ A - bohrSet Ω γ := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.sub_mem_sub ha (hBγ hb)
  have hAB := (regular_bohr_add_sub_card Ω hγ hη hband).2
  have hJB : ((J - B).card : ℝ) ≤ (1 + η) * (A.card : ℝ) :=
    (show ((J - B).card : ℝ) ≤ ((A - bohrSet Ω γ).card : ℝ) by
      exact_mod_cast hsub.trans (Finset.card_le_card hdiff)).trans hAB
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hBpos : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hc : (β / (1 + η)) * (B.card : ℝ) ≤ (T.card : ℝ) := by
    apply le_of_mul_le_mul_right _ (show 0 < (1 + η) * (A.card : ℝ) by positivity)
    calc
      _ = (β * (A.card : ℝ)) * (B.card : ℝ) := by
        field_simp
      _ ≤ (J.card : ℝ) * (B.card : ℝ) := by gcongr
      _ ≤ ((J - B).card : ℝ) * (T.card : ℝ) := by exact_mod_cast hs
      _ ≤ (T.card : ℝ) * ((1 + η) * (A.card : ℝ)) := by
        rw [mul_comm (T.card : ℝ)]
        exact mul_le_mul_of_nonneg_right hJB (by positivity)
  refine ⟨s', ?_, hc⟩
  apply Finset.card_pos.mp
  exact_mod_cast ((by positivity : 0 < (β / (1 + η)) * (B.card : ℝ)).trans_le hc)

private lemma exists_dense_reslice (J : Finset (ZMod M)) (hJ : J.Nonempty)
    (Ω : Finset (ZMod M)) {R γ r η β : ℝ}
    (hr : 0 ≤ r) (hrγ : r ≤ γ) (hη : 0 ≤ η) (hβ : 0 < β) (s : ZMod M)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    (hpos : ∀ a ∈ J, a - s ∈ bohrSet Ω R)
    (hcard : β * ((bohrSet Ω R).card : ℝ) ≤ (J.card : ℝ)) :
    ∃ s', let T := translatedSlice J (bohrSet Ω r) s'
      T.Nonempty ∧ (β / (1 + η)) * ((bohrSet Ω r).card : ℝ) ≤ (T.card : ℝ) := by
  exact exists_dense_reslice_subset J hJ (bohrSet Ω r) (bohrSet_nonempty Ω hr)
    Ω (hr.trans hrγ) (bohrSet_mono hrγ) hη hβ s hband hpos hcard

end Reslice

section SkewWitness

variable {M : ℕ} [NeZero M]

private lemma bohr_band_mono (Ω : Finset (ZMod M)) {R γ r η : ℝ}
    (hrγ : r ≤ γ) (hη : 0 ≤ η)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ)) :
    ((bohrSet Ω (R + r)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - r)).card : ℝ) := by
  have ho : bohrSet Ω (R + r) ⊆ bohrSet Ω (R + γ) := bohrSet_mono (by linarith)
  have hi : bohrSet Ω (R - γ) ⊆ bohrSet Ω (R - r) := bohrSet_mono (by linarith)
  refine (show ((bohrSet Ω (R + r)).card : ℝ) ≤ ((bohrSet Ω (R + γ)).card : ℝ) by
    exact_mod_cast Finset.card_le_card ho).trans (hband.trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Finset.card_le_card hi

private lemma exists_skewWeight_on_regular_bohr (Ω : Finset (ZMod M)) {R r η α : ℝ}
    (hR : 0 ≤ R) (hr : 0 ≤ r) (hη : 0 ≤ η) (hα : 0 ≤ α)
    (hband : ((bohrSet Ω (R + r)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - r)).card : ℝ))
    (U V W : ZMod M → ℂ) (φ : ZMod M → ZMod M)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ x, ‖V x‖ ≤ 1) (hW : ∀ x, ‖W x‖ ≤ 1)
    (hTwist : α * ((bohrSet Ω R).card : ℝ) * ((bohrSet Ω r).card : ℝ) ≤
      ‖∑ y ∈ bohrSet Ω r, ∑ x ∈ bohrSet Ω R, U x * V y * W (x + y) *
        ZMod.stdAddChar (-(x * φ y))‖) :
    ∃ P F : ZMod M → ℂ, (∀ x, ‖P x‖ ≤ 1) ∧ (∀ x, ‖F x‖ ≤ 1) ∧
      (α / (1 + η)) ^ 2 * ((bohrSet Ω r).card : ℝ) ^ 2 ≤
        ‖∑ a ∈ bohrSet Ω r, ∑ b ∈ bohrSet Ω r,
          P a * conj (P b) * F (a + b) * ZMod.stdAddChar (skewForm φ a b)‖ := by
  let A := bohrSet Ω R
  let B := bohrSet Ω r
  let S := ∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y))
  have hA := bohrSet_nonempty Ω hR
  obtain ⟨t, _, P, hP, ht⟩ :=
    exists_skew_correlation_from_twist A B hA (bohrSet_nonempty Ω hr) U V W φ hU hV
  let F (z : ZMod M) := (‖W (t + z)‖ ^ 2 : ℝ)
  have hF (z : ZMod M) : ‖(F z : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by unfold F; positivity)]
    simpa only [F, one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hW (t + z)) 2
  let T := ∑ a ∈ B, ∑ b ∈ B, P a * conj (P b) * (F (a + b) : ℂ) * ZMod.stdAddChar (skewForm φ a b)
  have he (t a b : ZMod M) : t + a + b = t + (a + b) := add_assoc _ _ _
  simp only [he] at ht
  change ‖S‖ ^ 2 ≤ ((A + B).card : ℝ) * ((A - B).card : ℝ) * ‖T‖ at ht
  have hAB := regular_bohr_add_sub_card Ω hr hη hband
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hηpos : 0 < 1 + η := by positivity
  refine ⟨P, fun z => (F z : ℂ), hP, hF, ?_⟩
  change (α / (1 + η)) ^ 2 * (B.card : ℝ) ^ 2 ≤ ‖T‖
  apply le_of_mul_le_mul_left _ (show 0 < ((1 + η) * (A.card : ℝ)) ^ 2 by positivity)
  calc
    _ = (α * (A.card : ℝ) * (B.card : ℝ)) ^ 2 := by
      field_simp [hηpos.ne']
    _ ≤ ‖S‖ ^ 2 := pow_le_pow_left₀ (by positivity) hTwist 2
    _ ≤ ((A + B).card : ℝ) * ((A - B).card : ℝ) * ‖T‖ := ht
    _ ≤ _ := by rw [sq]; gcongr; exacts [hAB.1, hAB.2]

private lemma exists_relative_twist_after_reslice (g : ZMod M → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (Ω J A B : Finset (ZMod M)) (hJ : J.Nonempty) (hB : B.Nonempty)
    {R γ r η β θ : ℝ} (hγ : 0 ≤ γ) (hBγ : B ⊆ bohrSet Ω γ)
    (hr₄ : r ≤ 1 / 4) (hBr : B ⊆ bohrSet Ω r)
    (hη : 0 ≤ η) (hβ : 0 < β) (hθ : 0 ≤ θ)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    (s : ZMod M) (ξ φ : ZMod M → ZMod M)
    (hpos : ∀ a ∈ J, a - s ∈ bohrSet Ω R)
    (hcard : β * ((bohrSet Ω R).card : ℝ) ≤ (J.card : ℝ))
    (hc : ∀ a ∈ J, θ ≤ ‖fourier (cyclicDerivative g a) (ξ a)‖)
    (hφ : ∀ a ∈ J, ∀ b ∈ J, φ (a - b) = ξ a - ξ b)
    (hadd : ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b) :
    ∃ x₀ s₀ offset : ZMod M, ∃ U V W : ZMod M → ℂ,
      (∀ x, U x = (g (x₀ + x) : ℂ) * ZMod.stdAddChar (-(x * offset))) ∧
      (∀ z, W z = (g (x₀ + s₀ + z) : ℂ)) ∧
      (∀ x, ‖U x‖ ≤ 1) ∧ (∀ x, ‖V x‖ ≤ 1) ∧ (∀ x, ‖W x‖ ≤ 1) ∧
      (β / (1 + η) * θ / (M : ℝ)) * (A.card : ℝ) * (B.card : ℝ) ≤
        ‖∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y))‖ := by
  obtain ⟨s', hT, hTcard⟩ :=
    exists_dense_reslice_subset J hJ B hB Ω hγ hBγ hη hβ s hband hpos hcard
  let T := translatedSlice J B s'
  have hTJ : T ⊆ J := Finset.filter_subset _ _
  have hTpos (a : ZMod M) (ha : a ∈ T) : a - s' ∈ B := (Finset.mem_filter.mp ha).2
  obtain ⟨offset, hoffset⟩ := affine_frequency_on_slice hT hr₄ s' ξ φ
    (fun a ha => hBr (hTpos a ha)) (fun a ha b hb => hφ a (hTJ ha) b (hTJ hb)) hadd
  obtain ⟨x₀, U, V, W, hUeq, hWeq, hU, hV, hW, hTwist⟩ :=
    exists_local_twisted_correlation_rect g hg T A B s' offset ξ φ hTpos hoffset
      (fun a ha => hc a (hTJ ha))
  refine ⟨x₀, s', offset, U, V, W, hUeq, hWeq, hU, hV, hW, ?_⟩
  let α := β / (1 + η) * θ / (M : ℝ)
  let S := ∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y))
  change α * (A.card : ℝ) * (B.card : ℝ) ≤ ‖S‖
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  apply le_of_mul_le_mul_left _ hM
  calc
    _ = (A.card : ℝ) * ((β / (1 + η)) * (B.card : ℝ)) * θ := by unfold α; field_simp [hM.ne']
    _ ≤ (A.card : ℝ) * (T.card : ℝ) * θ := by gcongr
    _ ≤ _ := hTwist

private lemma exists_skewWeight_after_reslice (g : ZMod M → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (Ω J : Finset (ZMod M)) (hJ : J.Nonempty) {R γ r η β θ : ℝ}
    (hR : 0 ≤ R) (hr : 0 ≤ r) (hrγ : r ≤ γ) (hr₄ : r ≤ 1 / 4)
    (hη : 0 ≤ η) (hβ : 0 < β) (hθ : 0 ≤ θ)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    (s : ZMod M) (ξ φ : ZMod M → ZMod M)
    (hpos : ∀ a ∈ J, a - s ∈ bohrSet Ω R)
    (hcard : β * ((bohrSet Ω R).card : ℝ) ≤ (J.card : ℝ))
    (hc : ∀ a ∈ J, θ ≤ ‖fourier (cyclicDerivative g a) (ξ a)‖)
    (hφ : ∀ a ∈ J, ∀ b ∈ J, φ (a - b) = ξ a - ξ b)
    (hadd : ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b) :
    ∃ P F : ZMod M → ℂ, (∀ x, ‖P x‖ ≤ 1) ∧ (∀ x, ‖F x‖ ≤ 1) ∧
      (β / (1 + η) * θ / (M : ℝ) / (1 + η)) ^ 2 * ((bohrSet Ω r).card : ℝ) ^ 2 ≤
        ‖∑ a ∈ bohrSet Ω r, ∑ b ∈ bohrSet Ω r,
          P a * conj (P b) * F (a + b) * ZMod.stdAddChar (skewForm φ a b)‖ := by
  have hγ := hr.trans hrγ
  obtain ⟨_, _, _, U, V, W, _, _, hU, hV, hW, hTwist⟩ :=
    exists_relative_twist_after_reslice g hg Ω J (bohrSet Ω R) (bohrSet Ω r) hJ
      (bohrSet_nonempty Ω hr) hγ (bohrSet_mono hrγ) hr₄ (fun _ h => h) hη hβ hθ hband s ξ φ
      hpos hcard hc hφ hadd
  exact exists_skewWeight_on_regular_bohr Ω hR hr hη (by positivity)
    (bohr_band_mono Ω hrγ hη hband) U V W φ hU hV hW hTwist

end SkewWitness

section SpectralCut

variable {I : Type*} [Fintype I]

private lemma exists_spectral_cut (f : I → ℝ) (hf : ∀ i, 0 ≤ f i)
    (htrace : ∑ i, f i ≤ 1) {v : ℝ} (hv : 0 < v)
    (m : ℕ) (hm : 8 ≤ (m : ℝ) * v) :
    ∃ L : ℝ, v / 4 ≤ L ∧ L ≤ v / 2 ∧
      ∀ i, v / (12 * (m : ℝ)) ≤ |f i - L| := by
  classical
  have hmpos : 0 < (m : ℝ) := by
    have hm0 : m ≠ 0 := by
      intro h
      norm_num [h] at hm
    exact_mod_cast Nat.pos_of_ne_zero hm0
  let step := v / (4 * (m : ℝ))
  let gap := v / (12 * (m : ℝ))
  let L (n : ℕ) := v / 4 + (n : ℝ) * step
  let Hi := (Finset.univ : Finset I).filter (fun i => v / 8 ≤ f i)
  have hstep : 0 < step := by unfold step; positivity
  have hgap : 0 < gap := by unfold gap; positivity
  have hgap₁ : 2 * gap < step := by
    have h : step = 3 * gap := by dsimp [step, gap]; ring
    linarith
  have hgap₂ : gap ≤ v / 8 := by
    dsimp [gap]
    have hm₁ : (1 : ℝ) ≤ m := by
      have hNat : 0 < m := by exact_mod_cast hmpos
      exact_mod_cast hNat
    apply (div_le_iff₀ (by positivity : 0 < 12 * (m : ℝ))).mpr
    nlinarith
  have hLo (n : ℕ) : v / 4 ≤ L n := by dsimp [L]; exact le_add_of_nonneg_right (by positivity)
  have hLhi (n : ℕ) (hn : n ∈ Finset.range (m + 1)) : L n ≤ v / 2 := by
    have hn' : (n : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    dsimp [L]
    calc
      _ ≤ v / 4 + (m : ℝ) * step := by gcongr
      _ = _ := by dsimp [step]; field_simp [hmpos.ne']; ring
  have hHicard : Hi.card ≤ m := by
    have hsum : (Hi.card : ℝ) * (v / 8) ≤ 1 := by
      calc
        _ = ∑ _ ∈ Hi, v / 8 := by simp
        _ ≤ ∑ i ∈ Hi, f i := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
        _ ≤ ∑ i, f i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hf i)
        _ ≤ _ := htrace
    exact_mod_cast (le_of_mul_le_mul_right (by linarith only [hsum, hm] :
      (Hi.card : ℝ) * (v / 8) ≤ (m : ℝ) * (v / 8)) (by positivity : 0 < v / 8))
  by_contra! H
  have hfound (n : ℕ) (hn : n ∈ Finset.range (m + 1)) : ∃ i, |f i - L n| < gap :=
    H (L n) (hLo n) (hLhi n hn)
  let p (n : ℕ) (hn : n ∈ Finset.range (m + 1)) := (hfound n hn).choose
  have hp (n : ℕ) (hn : n ∈ Finset.range (m + 1)) : |f (p n hn) - L n| < gap :=
    (hfound n hn).choose_spec
  have hmap (n : ℕ) (hn : n ∈ Finset.range (m + 1)) : p n hn ∈ Hi := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h := (abs_lt.mp (hp n hn)).1
    linarith only [h, hLo n, hgap₂]
  have hsep (n k : ℕ) (hnk : n < k) : step ≤ L k - L n := by
    have hcast : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hnk
    dsimp [L]
    nlinarith only [mul_le_mul_of_nonneg_right hcast hstep.le]
  have hneq (n k : ℕ) (hn : n ∈ Finset.range (m + 1)) (hk : k ∈ Finset.range (m + 1))
      (hnk : n < k) : p n hn ≠ p k hk := by
    intro h
    have h₁ := (abs_lt.mp (hp n hn)).2
    have h₂ := (abs_lt.mp (hp k hk)).1
    rw [h] at h₁
    linarith only [h₁, h₂, hsep n k hnk, hgap₁]
  have hh : (Finset.range (m + 1)).attach.card ≤ Hi.card := by
    apply Finset.card_le_card_of_injOn (fun n : {a // a ∈ Finset.range (m + 1)} => p n.1 n.2)
      (s := (Finset.range (m + 1)).attach)
    · intro n _
      exact hmap n.1 n.2
    · intro n _ k _ h
      apply Subtype.ext
      rcases lt_trichotomy n.1 k.1 with hlt | he | hgt
      · exact False.elim (hneq _ _ n.2 k.2 hlt h)
      · exact he
      · exact False.elim (hneq _ _ k.2 n.2 hgt h.symm)
  simp only [Finset.card_attach, Finset.card_range] at hh
  omega

end SpectralCut

section MatrixEnergy

open scoped Matrix ComplexOrder

variable {I J : Type*} [Fintype I] [Fintype J]

private noncomputable def matrixEnergy (A : Matrix I J ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private lemma ofReal_matrixEnergy (A : Matrix I J ℂ) :
    (matrixEnergy A : ℂ) = (Aᴴ * A).trace := by
  unfold matrixEnergy Matrix.trace Matrix.diag
  simp only [Complex.ofReal_sum, complex_ofReal_sq_norm, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private lemma matrixEnergy_unitary_conj [DecidableEq I] (U A : Matrix I I ℂ)
    (hU : Uᴴ * U = 1) : matrixEnergy (U * A * Uᴴ) = matrixEnergy A := by
  apply Complex.ofReal_injective
  rw [ofReal_matrixEnergy, ofReal_matrixEnergy, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have he : (U * (Aᴴ * Uᴴ)) * (U * A * Uᴴ) = U * (Aᴴ * A) * Uᴴ := by
    calc
      _ = U * (Aᴴ * (Uᴴ * U) * A) * Uᴴ := by noncomm_ring
      _ = _ := by rw [hU, mul_one]
  rw [he, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, one_mul]

private lemma matrixEnergy_diagonal [DecidableEq I] (f : I → ℝ) :
    matrixEnergy (Matrix.diagonal (fun i => (f i : ℂ))) = ∑ i, (f i) ^ 2 := by
  unfold matrixEnergy
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

private lemma exists_eigenvalue_ge_matrixEnergy [Nonempty I] [DecidableEq I]
    (K : Matrix I I ℂ) (hK : K.PosSemidef) (ht : K.trace.re ≤ 1) :
    ∃ i, matrixEnergy K ≤ hK.1.eigenvalues i := by
  let f := hK.1.eigenvalues
  have hf (i : I) : 0 ≤ f i := hK.eigenvalues_nonneg i
  have ht' : ∑ i, f i ≤ 1 := by
    rw [hK.1.trace_eq_sum_eigenvalues] at ht
    simpa [f] using ht
  have hd : matrixEnergy K = ∑ i, f i ^ 2 := by
    let V : Matrix I I ℂ := hK.1.eigenvectorUnitary
    have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self hK.1.eigenvectorUnitary
    have hs : K = V * Matrix.diagonal (fun i => (f i : ℂ)) * Vᴴ := by
      rw [hK.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
      rfl
    rw [hs, matrixEnergy_unitary_conj V _ hV, matrixEnergy_diagonal]
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset I) f Finset.univ_nonempty
  refine ⟨i, ?_⟩
  rw [hd]
  calc
    _ ≤ ∑ j, f i * f j := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hi j hj) (hf j)
    _ = f i * ∑ j, f j := by rw [Finset.mul_sum]
    _ ≤ f i := mul_le_of_le_one_right (hf i) ht'

end MatrixEnergy

section OffBlocks

variable {I : Type*} [Fintype I] [DecidableEq I]

private lemma matrixEnergy_diagonal_commutator (f : I → ℝ) (U : Matrix I I ℂ) :
    let D := Matrix.diagonal (fun i => (f i : ℂ))
    matrixEnergy (D * U - U * D) =
      ∑ i, ∑ j, |f i - f j| ^ 2 * ‖U i j‖ ^ 2 := by
  dsimp only
  unfold matrixEnergy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_comm (U i j), ← sub_mul, ← Complex.ofReal_sub, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs]

private lemma sum_off_block_energy (f : I → ℝ) (U : Matrix I I ℂ)
    (p : I → Prop) [DecidablePred p] {ε gap : ℝ} (hgap : 0 < gap)
    (hsep : ∀ i j, p i → ¬p j → gap ≤ |f i - f j|)
    (hU : matrixEnergy (Matrix.diagonal (fun i => (f i : ℂ)) * U -
      U * Matrix.diagonal (fun i => (f i : ℂ))) ≤ ε) :
    (∀ i, p i → (∑ j : {j // ¬p j}, ‖U i j.1‖ ^ 2) ≤ ε / gap ^ 2) ∧
      (∀ i, p i → (∑ j : {j // ¬p j}, ‖U j.1 i‖ ^ 2) ≤ ε / gap ^ 2) := by
  rw [matrixEnergy_diagonal_commutator] at hU
  let F (i j : I) := |f i - f j| ^ 2 * ‖U i j‖ ^ 2
  have hFn (i j : I) : 0 ≤ F i j := by unfold F; positivity
  constructor
  · intro i hi
    rw [le_div_iff₀ (sq_pos_of_pos hgap), mul_comm, Finset.mul_sum]
    calc
      _ ≤ ∑ j : {j // ¬p j}, F i j.1 := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hgap.le (hsep i j.1 hi j.2) 2) (by positivity)
      _ ≤ ∑ j, F i j := by
        rw [← Fintype.sum_subtype_add_sum_subtype p (F i)]
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => hFn _ _)
      _ ≤ ∑ k, ∑ j, F k j :=
        Finset.single_le_sum (f := fun k => ∑ j, F k j)
          (fun k _ => Finset.sum_nonneg fun j _ => hFn k j) (Finset.mem_univ i)
      _ ≤ ε := hU
  · intro i hi
    rw [le_div_iff₀ (sq_pos_of_pos hgap), mul_comm, Finset.mul_sum]
    calc
      _ ≤ ∑ j : {j // ¬p j}, F j.1 i := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hj := hsep i j.1 hi j.2
        rw [abs_sub_comm] at hj
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hgap.le hj 2) (by positivity)
      _ ≤ ∑ j, F j i := by
        rw [← Fintype.sum_subtype_add_sum_subtype p (fun j => F j i)]
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => hFn _ _)
      _ ≤ ∑ k, ∑ j, F j k :=
        Finset.single_le_sum (f := fun k => ∑ j, F j k)
          (fun k _ => Finset.sum_nonneg fun j _ => hFn j k) (Finset.mem_univ i)
      _ ≤ ε := by rwa [Finset.sum_comm]

private def compressMatrix (p : I → Prop) (U : Matrix I I ℂ) : Matrix {i // p i} {i // p i} ℂ :=
  U.submatrix Subtype.val Subtype.val

omit [DecidableEq I] in
private lemma norm_compressMatrix_mul_error (p : I → Prop) [DecidablePred p]
    (U V : Matrix I I ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ i, p i → (∑ j : {j // ¬p j}, ‖U i j.1‖ ^ 2) ≤ ε)
    (hV : ∀ i, p i → (∑ j : {j // ¬p j}, ‖V j.1 i‖ ^ 2) ≤ ε)
    (i j : {i // p i}) :
    ‖(compressMatrix p U * compressMatrix p V) i j - (U * V) i.1 j.1‖ ≤ ε := by
  simp only [Matrix.mul_apply, compressMatrix, Matrix.submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun k => U i.1 k * V k j.1),
    sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  have h := norm_sum_mul_sq_le (fun k : {k // ¬p k} => U i.1 k.1) (fun k => V k.1 j.1)
  have hh := h.trans (mul_le_mul (hU i.1 i.2) (hV j.1 j.2) (by positivity) hε)
  nlinarith only [hh, hε, norm_nonneg (∑ k : {k // ¬p k}, U i.1 k.1 * V k.1 j.1)]

end OffBlocks

section CompressedPhase

open scoped Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

private lemma norm_matrix_entry_le_one_of_unitary (U : Matrix I I ℂ)
    (hU : Uᴴ * U = 1) (i j : I) : ‖U i j‖ ≤ 1 := by
  have hd := congrArg (fun A : Matrix I I ℂ => (A j j).re) hU
  change ((Uᴴ * U) j j).re = ((1 : Matrix I I ℂ) j j).re at hd
  have hprod (k : I) : conj (U k j) * U k j = ((‖U k j‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, ← complex_ofReal_sq_norm]
  have hsum : (∑ k, ‖U k j‖ ^ 2) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.star_def,
      hprod, ← Complex.ofReal_sum, Complex.ofReal_re, Complex.one_re] using hd
  have hle : ‖U i j‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun k => ‖U k j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ _)
  nlinarith only [hle, norm_nonneg (U i j)]

private lemma norm_submatrix_mul_le_of_unitaries
    (p : I → Prop) [DecidablePred p] (U V : Matrix I I ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hUr : ∀ i, p i → (∑ j : {j // ¬p j}, ‖U i j.1‖ ^ 2) ≤ ε)
    (hVc : ∀ i, p i → (∑ j : {j // ¬p j}, ‖V j.1 i‖ ^ 2) ≤ ε)
    (i j : {i // p i}) :
    ‖(compressMatrix p U * compressMatrix p V) i j‖ ≤ 2 := by
  have herr := norm_compressMatrix_mul_error p U V hε hUr hVc i j
  have hUV : (U * V)ᴴ * (U * V) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = Vᴴ * (Uᴴ * U) * V := by noncomm_ring
      _ = _ := by rw [hU, mul_one, hV]
  have hfull := norm_matrix_entry_le_one_of_unitary (U * V) hUV i.1 j.1
  calc
    _ = ‖((compressMatrix p U * compressMatrix p V) i j - (U * V) i.1 j.1) + (U * V) i.1 j.1‖ := by
      rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (by linarith only [herr, hfull, hε₁])

private lemma norm_det_compressMatrix_ge
    (p : I → Prop) [DecidablePred p] (U : Matrix I I ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hUr : ∀ i, p i → (∑ j : {j // ¬p j}, ‖U i j.1‖ ^ 2) ≤ ε)
    (hsmall : let d := Fintype.card {i // p i}
      (d.factorial : ℝ) * ((d : ℝ) * ε * 2 ^ d) ≤ 1 / 2) :
    1 / 2 ≤ ‖(compressMatrix p U).det‖ := by
  let U₀ := compressMatrix p U
  have hstar : compressMatrix p Uᴴ = U₀ᴴ := rfl
  have hStarU : (Uᴴ)ᴴ * Uᴴ = 1 := by simpa only [Matrix.conjTranspose_conjTranspose] using hU'
  have hUc : ∀ i, p i → (∑ j : {j // ¬p j}, ‖Uᴴ j.1 i‖ ^ 2) ≤ ε := by
    simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.norm_conj] using hUr
  have hprod := norm_submatrix_mul_le_of_unitaries p U Uᴴ hε hε₁ hU hStarU hUr hUc
  rw [hstar] at hprod
  have herr (i j : {i // p i}) : ‖(U₀ * U₀ᴴ) i j - (1 : Matrix _ _ ℂ) i j‖ ≤ ε := by
    have h := norm_compressMatrix_mul_error p U Uᴴ hε hUr hUc i j
    rw [hstar, hU'] at h
    simpa only [Matrix.one_apply, Subtype.coe_inj] using h
  have hone (i j : {i // p i}) : ‖(1 : Matrix _ _ ℂ) i j‖ ≤ 2 := by
    rw [Matrix.one_apply]
    split_ifs <;> norm_num
  have hdet := norm_det_sub_det_le (U₀ * U₀ᴴ) 1 (by norm_num : (1 : ℝ) ≤ 2) hε hprod hone herr
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hdet
  have hnorm : ‖U₀.det * conj U₀.det - 1‖ ≤ 1 / 2 := hdet.trans hsmall
  have htri := norm_sub_le (1 - U₀.det * conj U₀.det) (-(U₀.det * conj U₀.det))
  rw [show 1 - U₀.det * conj U₀.det - -(U₀.det * conj U₀.det) = 1 by ring,
    norm_one, norm_neg, norm_sub_rev, norm_mul, Complex.norm_conj] at htri
  nlinarith only [htri, hnorm, norm_nonneg U₀.det]

private lemma norm_pow_sub_one_le_of_compressed_commutation
    (p : I → Prop) [DecidablePred p] (U V : Matrix I I ℂ) {z : ℂ} (hz : ‖z‖ = 1) {ε : ℝ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (hUr : ∀ i, p i → (∑ j : {j // ¬p j}, ‖U i j.1‖ ^ 2) ≤ ε)
    (hUc : ∀ i, p i → (∑ j : {j // ¬p j}, ‖U j.1 i‖ ^ 2) ≤ ε)
    (hVr : ∀ i, p i → (∑ j : {j // ¬p j}, ‖V i j.1‖ ^ 2) ≤ ε)
    (hVc : ∀ i, p i → (∑ j : {j // ¬p j}, ‖V j.1 i‖ ^ 2) ≤ ε)
    (hW : ∀ i j, p i → p j → (U * V) i j = z * (V * U) i j)
    (hsmall : let d := Fintype.card {i // p i}
      (d.factorial : ℝ) * ((d : ℝ) * ε * 2 ^ d) ≤ 1 / 2) :
    let d := Fintype.card {i // p i}
    ‖z ^ d - 1‖ ≤ 8 * (d.factorial : ℝ) * (d : ℝ) * ε * 2 ^ d := by
  let U₀ := compressMatrix p U
  let V₀ := compressMatrix p V
  have hu := norm_submatrix_mul_le_of_unitaries p U V hε hε₁ hU hV hUr hVc
  have hv : ∀ i j, ‖(z • (V₀ * U₀)) i j‖ ≤ 2 := by
    intro i j
    have h := norm_submatrix_mul_le_of_unitaries p V U hε hε₁ hV hU hVr hUc i j
    simpa only [Matrix.smul_apply, smul_eq_mul, norm_mul, hz, one_mul] using h
  have hd (i j : {i // p i}) : ‖(U₀ * V₀) i j - (z • (V₀ * U₀)) i j‖ ≤ 2 * ε := by
    have hUV := norm_compressMatrix_mul_error p U V hε hUr hVc i j
    have hVU := norm_compressMatrix_mul_error p V U hε hVr hUc i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show (U₀ * V₀) i j - z * (V₀ * U₀) i j =
      ((U₀ * V₀) i j - (U * V) i.1 j.1) +
        -(z * ((V₀ * U₀) i j - (V * U) i.1 j.1)) by rw [hW _ _ i.2 j.2]; ring]
    apply (norm_add_le _ _).trans
    rw [norm_neg, norm_mul, hz, one_mul]
    linarith only [hUV, hVU]
  have hdet : (1 / 4 : ℝ) ≤ ‖U₀.det * V₀.det‖ := by
    rw [norm_mul]
    have h := mul_le_mul (norm_det_compressMatrix_ge p U hε hε₁ hU hU' hUr hsmall)
      (norm_det_compressMatrix_ge p V hε hε₁ hV hV' hVr hsmall) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (norm_nonneg U₀.det)
    linarith only [h]
  dsimp only
  exact (norm_pow_sub_one_le_of_matrix_commutation U₀ V₀ z (by norm_num : (1 : ℝ) ≤ 2)
    (by positivity : 0 ≤ 2 * ε) (by norm_num : (0 : ℝ) < 1 / 4) hu hv hd hdet).trans (by ring_nf; rfl)

end CompressedPhase

section SpectralWeyl

open scoped Matrix ComplexOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

private lemma matrixEnergy_mul_unitary (A U : Matrix I I ℂ) (hU : U * Uᴴ = 1) :
    matrixEnergy (A * U) = matrixEnergy A := by
  apply Complex.ofReal_injective
  rw [ofReal_matrixEnergy, ofReal_matrixEnergy, Matrix.conjTranspose_mul]
  have h : Uᴴ * Aᴴ * (A * U) = (Uᴴ * (Aᴴ * A)) * U := by noncomm_ring
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, one_mul]

omit [DecidableEq I] in
private lemma matrixEnergy_neg (A : Matrix I I ℂ) : matrixEnergy (-A) = matrixEnergy A := by
  simp only [matrixEnergy, Matrix.neg_apply, norm_neg]

private lemma matrixEnergy_commutator_le (K U : Matrix I I ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) {b : ℝ}
    (h : matrixEnergy (U * K * Uᴴ - K) ≤ b) :
    matrixEnergy (K * U - U * K) ≤ b := by
  have hmul : (U * K * Uᴴ - K) * U = -(K * U - U * K) := by
    rw [sub_mul, Matrix.mul_assoc (U * K) Uᴴ U, hU, mul_one, neg_sub]
  have he := matrixEnergy_mul_unitary (U * K * Uᴴ - K) U hU'
  rw [hmul, matrixEnergy_neg] at he
  exact he.le.trans h

private lemma bounded_dimension_controls_weyl_phase [Nonempty I]
    (K : Matrix I I ℂ) (hK : K.PosSemidef) (ht : K.trace.re ≤ 1)
    {v : ℝ} (hv : 0 < v) (hKv : v ≤ matrixEnergy K) (m : ℕ) (hm : 8 ≤ (m : ℝ) * v)
    {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hsmall : (m.factorial : ℝ) * ((m : ℝ) * ε * 2 ^ m) ≤ 1 / 2) :
    ∃ d : ℕ, 0 < d ∧ d ≤ m ∧ ∀ (U V : Matrix I I ℂ) (z : ℂ), ‖z‖ = 1 →
      Uᴴ * U = 1 → U * Uᴴ = 1 → Vᴴ * V = 1 → V * Vᴴ = 1 →
      matrixEnergy (U * K * Uᴴ - K) ≤ (v / (12 * (m : ℝ))) ^ 2 * ε →
      matrixEnergy (V * K * Vᴴ - K) ≤ (v / (12 * (m : ℝ))) ^ 2 * ε →
      (U * V - z • (V * U)) * K = 0 →
      ‖z ^ d - 1‖ ≤ 8 * (m.factorial : ℝ) * (m : ℝ) * ε * 2 ^ m := by
  classical
  let f := hK.1.eigenvalues
  have hf (i : I) : 0 ≤ f i := hK.eigenvalues_nonneg i
  have ht' : ∑ i, f i ≤ 1 := by
    rw [hK.1.trace_eq_sum_eigenvalues] at ht
    simpa [f] using ht
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalue_ge_matrixEnergy K hK ht
  obtain ⟨L, hLlo, hLhi, hcut⟩ := exists_spectral_cut f hf ht' hv m hm
  let gap := v / (12 * (m : ℝ))
  let p (i : I) := L ≤ f i
  let d := Fintype.card {i // p i}
  have hgap : 0 < gap := by
    have hm₀ : 0 < (m : ℝ) := by nlinarith only [hm, hv, Nat.cast_nonneg (α := ℝ) m]
    unfold gap
    positivity
  have hpv : p i₀ := by
    dsimp [p, f]
    linarith only [hLhi, hv, hi₀, hKv]
  have hd : 0 < d := by
    have : Nonempty {i // p i} := ⟨⟨i₀, hpv⟩⟩
    exact Fintype.card_pos
  have hdcap : d ≤ m := by
    have hpartial : (∑ i : {i // p i}, f i.1) ≤ ∑ i, f i := by
      rw [← Fintype.sum_subtype_add_sum_subtype p f]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hf i.1)
    have ha : (d : ℝ) * (v / 4) ≤ 1 := by
      calc
        _ = ∑ _ : {i // p i}, v / 4 := by simp [d]
        _ ≤ ∑ i : {i // p i}, f i.1 := Finset.sum_le_sum fun i _ => hLlo.trans i.2
        _ ≤ _ := hpartial.trans ht'
    have hb : (d : ℝ) * (v / 4) ≤ (m : ℝ) * (v / 4) := by linarith only [ha, hm]
    exact_mod_cast le_of_mul_le_mul_right hb (by positivity : 0 < v / 4)
  have hsep (i j : I) (hi : p i) (hj : ¬p j) : gap ≤ |f i - f j| := by
    change L ≤ f i at hi
    have hj' : f j < L := lt_of_not_ge hj
    have hg := hcut i
    change gap ≤ |f i - L| at hg
    rw [abs_of_nonneg (sub_nonneg.mpr hi)] at hg
    rw [abs_of_nonneg (sub_nonneg.mpr (hj'.le.trans hi))]
    linarith only [hg, hj']
  let E := hK.1.eigenvectorUnitary
  let Ψ := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (star E)
  let D := Matrix.diagonal (fun i => (f i : ℂ))
  have hΨK : Ψ K = D := hK.1.conjStarAlgAut_star_eigenvectorUnitary
  have hΨE (A : Matrix I I ℂ) : matrixEnergy (Ψ A) = matrixEnergy A := by
    change matrixEnergy ((↑(star E) : Matrix I I ℂ) * A *
      (↑(star E) : Matrix I I ℂ)ᴴ) = matrixEnergy A
    exact matrixEnergy_unitary_conj _ _ (Unitary.coe_star_mul_self (star E))
  have hoff (U : Matrix I I ℂ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
      (h : matrixEnergy (U * K * Uᴴ - K) ≤ gap ^ 2 * ε) :
      (∀ i, p i → (∑ j : {j // ¬p j}, ‖(Ψ U) i j.1‖ ^ 2) ≤ ε) ∧
        (∀ i, p i → (∑ j : {j // ¬p j}, ‖(Ψ U) j.1 i‖ ^ 2) ≤ ε) := by
    have hd' : matrixEnergy (D * Ψ U - Ψ U * D) ≤ gap ^ 2 * ε := by
      rw [← hΨK, ← map_mul, ← map_mul, ← map_sub, hΨE]
      exact matrixEnergy_commutator_le K U hU hU' h
    have hOff := sum_off_block_energy f (Ψ U) p hgap hsep hd'
    have he : gap ^ 2 * ε / gap ^ 2 = ε := by field_simp [hgap.ne']
    simpa only [he] using hOff
  have hscaled : (d.factorial : ℝ) * ((d : ℝ) * ε * 2 ^ d) ≤
      (m.factorial : ℝ) * ((m : ℝ) * ε * 2 ^ m) := by
    gcongr; norm_num
  refine ⟨d, hd, hdcap, ?_⟩
  intro U V z hz hU hU' hV hV' hEU hEV hW
  obtain ⟨hUr, hUc⟩ := hoff U hU hU' hEU
  obtain ⟨hVr, hVc⟩ := hoff V hV hV' hEV
  have hu : (Ψ U)ᴴ * (Ψ U) = 1 := by
    change star (Ψ U) * Ψ U = 1
    rw [← map_star, ← map_mul, show star U * U = 1 from hU, map_one]
  have hu' : (Ψ U) * (Ψ U)ᴴ = 1 := by
    change Ψ U * star (Ψ U) = 1
    rw [← map_star, ← map_mul, show U * star U = 1 from hU', map_one]
  have hv' : (Ψ V)ᴴ * (Ψ V) = 1 := by
    change star (Ψ V) * Ψ V = 1
    rw [← map_star, ← map_mul, show star V * V = 1 from hV, map_one]
  have hv'' : (Ψ V) * (Ψ V)ᴴ = 1 := by
    change Ψ V * star (Ψ V) = 1
    rw [← map_star, ← map_mul, show V * star V = 1 from hV', map_one]
  have hW' : (Ψ U * Ψ V - z • (Ψ V * Ψ U)) * D = 0 := by
    simpa only [map_mul, map_sub, map_smul, map_zero, hΨK] using congrArg Ψ hW
  have hW'' (i j : I) (_ : p i) (hj : p j) : (Ψ U * Ψ V) i j = z * (Ψ V * Ψ U) i j := by
    have h := congrArg (fun A : Matrix I I ℂ => A i j) hW'
    change ((Ψ U * Ψ V - z • (Ψ V * Ψ U)) * D) i j = (0 : Matrix I I ℂ) i j at h
    simp only [D, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] at h
    have hfj : (0 : ℝ) < f j := (by positivity : 0 < v / 4).trans_le (hLlo.trans hj)
    have hc : (f j : ℂ) ≠ 0 := by exact_mod_cast hfj.ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hc)
  have hphase := norm_pow_sub_one_le_of_compressed_commutation p (Ψ U) (Ψ V) hz hε hε₁
    hu hu' hv' hv'' hUr hUc hVr hVc hW'' (hscaled.trans hsmall)
  exact hphase.trans (by
    have h := mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 8)
    convert h using 1 <;> ring)

end SpectralWeyl

section ShiftMatrix

open scoped Matrix ComplexOrder

variable {M : ℕ} [NeZero M]

private noncomputable def phaseShiftMatrix (φ : ZMod M → ZMod M) (t : ZMod M) :
    Matrix (ZMod M) (ZMod M) ℂ :=
  fun i j => if j = i - t then ZMod.stdAddChar (skewForm φ i t) else 0

private lemma phaseShiftMatrix_mul (φ : ZMod M → ZMod M) (t : ZMod M)
    (A : Matrix (ZMod M) (ZMod M) ℂ) (i j : ZMod M) :
    (phaseShiftMatrix φ t * A) i j = ZMod.stdAddChar (skewForm φ i t) * A (i - t) j := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (i - t)]
  · simp [phaseShiftMatrix]
  · intro k _ hk
    simp [phaseShiftMatrix, hk]
  · simp

private lemma mul_phaseShiftMatrix_conjTranspose (φ : ZMod M → ZMod M) (t : ZMod M)
    (A : Matrix (ZMod M) (ZMod M) ℂ) (i j : ZMod M) :
    (A * (phaseShiftMatrix φ t)ᴴ) i j = A i (j - t) * conj (ZMod.stdAddChar (skewForm φ j t)) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (j - t)]
  · simp [phaseShiftMatrix, Matrix.conjTranspose_apply]
  · intro k _ hk
    simp [phaseShiftMatrix, Matrix.conjTranspose_apply, hk]
  · simp

private lemma stdAddChar_mul_conj_self (x : ZMod M) : ZMod.stdAddChar x * conj (ZMod.stdAddChar x) = 1 := by
  rw [← complex_ofReal_sq_norm, norm_stdAddChar]
  norm_num

private lemma phaseShiftMatrix_mul_star (φ : ZMod M → ZMod M) (t : ZMod M) :
    phaseShiftMatrix φ t * (phaseShiftMatrix φ t)ᴴ = 1 := by
  classical
  ext i j
  rw [mul_phaseShiftMatrix_conjTranspose, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simpa [phaseShiftMatrix] using stdAddChar_mul_conj_self (skewForm φ i t)
  · have hne : j - t ≠ i - t := fun e => h (sub_left_injective e).symm
    simp [phaseShiftMatrix, hne, h]

private lemma phaseShiftMatrix_star_mul (φ : ZMod M → ZMod M) (t : ZMod M) :
    (phaseShiftMatrix φ t)ᴴ * phaseShiftMatrix φ t = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (i + t), Matrix.one_apply]
  · rw [Matrix.conjTranspose_apply]
    by_cases h : i = j
    · subst j
      simpa [phaseShiftMatrix, Matrix.conjTranspose_apply, mul_comm] using
        stdAddChar_mul_conj_self (skewForm φ (i + t) t)
    · simp [phaseShiftMatrix, h, Ne.symm h]
  · intro k _ hk
    have he : i ≠ k - t := by
      intro h'
      apply hk
      rw [h', sub_add_cancel]
    simp [Matrix.conjTranspose_apply, phaseShiftMatrix, he]
  · simp

private lemma skewCovariance_eq_zero_of_row_notMem (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) {i : ZMod M} (hi : i ∉ A + C) (j : ZMod M) :
    skewCovariance A C φ P i j = 0 := by
  unfold skewCovariance
  apply Finset.sum_eq_zero
  intro t ht
  have h : i - t ∉ A := fun h => hi (by
    simpa only [sub_add_cancel] using Finset.add_mem_add h ht)
  simp [skewTranslate, h]

private lemma skewCovariance_eq_zero_of_col_notMem (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) (i : ZMod M) {j : ZMod M} (hj : j ∉ A + C) :
    skewCovariance A C φ P i j = 0 := by
  unfold skewCovariance
  apply Finset.sum_eq_zero
  intro t ht
  have h : j - t ∉ A := fun h => hj (by
    simpa only [sub_add_cancel] using Finset.add_mem_add h ht)
  simp [skewTranslate, h]

private lemma phaseShiftMatrix_pair_commute_on_covariance (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) {d e : ZMod M}
    (hd : ∀ a ∈ A + C, φ (a + e + d) = φ (a + e) + φ d)
    (he : ∀ a ∈ A + C, φ (a + d + e) = φ (a + d) + φ e) :
    (phaseShiftMatrix φ d * phaseShiftMatrix φ e -
      ZMod.stdAddChar (-2 * skewForm φ d e) • (phaseShiftMatrix φ e * phaseShiftMatrix φ d)) *
        (Matrix.of (skewCovariance A C φ P)) = 0 := by
  classical
  ext i j
  simp only [sub_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.zero_apply, phaseShiftMatrix_mul, Matrix.of_apply]
  let a := i - d - e
  have hai : a + e + d = i := by dsimp [a]; abel
  have ha'i : a + d + e = i := by dsimp [a]; abel
  have hai' : a + e = i - d := by dsimp [a]; abel
  have ha'i' : a + d = i - e := by dsimp [a]; abel
  have heq : i - e - d = a := by dsimp [a]; abel
  change ZMod.stdAddChar (skewForm φ i d) *
      (ZMod.stdAddChar (skewForm φ (i - d) e) * skewCovariance A C φ P a j) -
    ZMod.stdAddChar (-2 * skewForm φ d e) * (ZMod.stdAddChar (skewForm φ i e) *
      (ZMod.stdAddChar (skewForm φ (i - e) d) * skewCovariance A C φ P (i - e - d) j)) = 0
  rw [heq]
  by_cases ha : a ∈ A + C
  · have h₁ := hd a ha
    have h₂ := he a ha
    rw [hai, hai'] at h₁
    rw [ha'i, ha'i'] at h₂
    have hφd : φ (i - d) = φ i - φ d := by rw [h₁]; ring
    have hφe : φ (i - e) = φ i - φ e := by rw [h₂]; ring
    have hphase : skewForm φ i d + skewForm φ (i - d) e =
        -2 * skewForm φ d e + (skewForm φ i e + skewForm φ (i - e) d) := by
      unfold skewForm
      rw [hφd, hφe]
      ring
    have h := congrArg ZMod.stdAddChar hphase
    simp only [AddChar.map_add_eq_mul] at h
    linear_combination (skewCovariance A C φ P a j) * h
  · rw [skewCovariance_eq_zero_of_row_notMem A C φ P ha]
    simp

end ShiftMatrix

section NormalizedCovariance

open scoped Matrix ComplexOrder

variable {M : ℕ} [NeZero M]

private noncomputable def normalizedSkewMatrix (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) : Matrix (ZMod M) (ZMod M) ℂ :=
  (((A.card : ℝ) * (C.card : ℝ))⁻¹ : ℝ) • Matrix.of (skewCovariance A C φ P)

private lemma normalizedSkewMatrix_posSemidef (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) :
    (normalizedSkewMatrix A C φ P).PosSemidef := by
  let V : Matrix (ZMod M) C ℂ := fun i t => skewTranslate A φ P t.1 i
  have hV : V * Vᴴ = Matrix.of (skewCovariance A C φ P) := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply]
    change (∑ t : C, skewTranslate A φ P t.1 i * conj (skewTranslate A φ P t.1 j)) =
      ∑ t ∈ C, skewTranslate A φ P t i * conj (skewTranslate A φ P t j)
    exact Finset.sum_coe_sort C (fun t => skewTranslate A φ P t i * conj (skewTranslate A φ P t j))
  unfold normalizedSkewMatrix
  rw [← hV]
  exact (Matrix.posSemidef_self_mul_conjTranspose V).smul (by positivity)

private lemma normalizedSkewMatrix_apply (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) (i j : ZMod M) :
    normalizedSkewMatrix A C φ P i j =
      (((A.card : ℝ) * (C.card : ℝ))⁻¹ : ℝ) * skewCovariance A C φ P i j := by
  rfl

private lemma normalizedSkewMatrix_trace_le_one (A C : Finset (ZMod M))
    (hA : A.Nonempty) (hC : C.Nonempty) (φ : ZMod M → ZMod M) (P : ZMod M → ℂ)
    (hP : ∀ x, ‖P x‖ ≤ 1) : (normalizedSkewMatrix A C φ P).trace.re ≤ 1 := by
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hCpos : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  let ν := ((A.card : ℝ) * (C.card : ℝ))⁻¹
  unfold Matrix.trace Matrix.diag
  simp only [Complex.re_sum, normalizedSkewMatrix_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ← Finset.mul_sum]
  have htrace : (∑ x : ZMod M, (skewCovariance A C φ P x x).re) =
      ∑ x ∈ A + C, (skewCovariance A C φ P x x).re := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
    rw [skewCovariance_eq_zero_of_row_notMem A C φ P hx, Complex.zero_re]
  rw [htrace]
  calc
    _ ≤ ν * ((C.card : ℝ) * (A.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (skewCovariance_trace_bound A C φ P hP) (by dsimp [ν]; positivity)
    _ = _ := by dsimp [ν]; field_simp

private lemma matrixEnergy_eq_sum_if_supported {I : Type*} [Fintype I]
    (A : Matrix I I ℂ) (D : Finset I) (hr : ∀ i ∉ D, ∀ j, A i j = 0)
    (hc : ∀ j ∉ D, ∀ i, A i j = 0) :
    matrixEnergy A = ∑ i ∈ D, ∑ j ∈ D, ‖A i j‖ ^ 2 := by
  unfold matrixEnergy
  symm
  calc
    _ = ∑ i ∈ D, ∑ j, ‖A i j‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_subset (Finset.subset_univ _) ?_
      intro j _ hj
      simp [hc j hj i]
    _ = _ := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro i _ hi
      simp [hr i hi]

private lemma matrixEnergy_normalizedSkewMatrix (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) :
    matrixEnergy (normalizedSkewMatrix A C φ P) =
      (((A.card : ℝ) * (C.card : ℝ))⁻¹) ^ 2 *
        ∑ x ∈ A + C, ∑ y ∈ A + C, ‖skewCovariance A C φ P x y‖ ^ 2 := by
  have hr (i : ZMod M) (hi : i ∉ A + C) (j : ZMod M) :
      normalizedSkewMatrix A C φ P i j = 0 := by
    rw [normalizedSkewMatrix_apply, skewCovariance_eq_zero_of_row_notMem A C φ P hi, mul_zero]
  have hc (j : ZMod M) (hj : j ∉ A + C) (i : ZMod M) :
      normalizedSkewMatrix A C φ P i j = 0 := by
    rw [normalizedSkewMatrix_apply, skewCovariance_eq_zero_of_col_notMem A C φ P i hj, mul_zero]
  rw [matrixEnergy_eq_sum_if_supported _ _ hr hc]
  have hv : 0 ≤ ((A.card : ℝ) * (C.card : ℝ))⁻¹ := by positivity
  simp only [normalizedSkewMatrix_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv,
    mul_pow, Finset.mul_sum]

private lemma phaseShiftMatrix_pair_commute_on_normalizedSkewMatrix (A C : Finset (ZMod M))
    (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) {d e : ZMod M}
    (hd : ∀ a ∈ A + C, φ (a + e + d) = φ (a + e) + φ d)
    (he : ∀ a ∈ A + C, φ (a + d + e) = φ (a + d) + φ e) :
    (phaseShiftMatrix φ d * phaseShiftMatrix φ e -
      ZMod.stdAddChar (-2 * skewForm φ d e) • (phaseShiftMatrix φ e * phaseShiftMatrix φ d)) *
        normalizedSkewMatrix A C φ P = 0 := by
  unfold normalizedSkewMatrix
  rw [Matrix.mul_smul, phaseShiftMatrix_pair_commute_on_covariance A C φ P hd he, smul_zero]

private lemma matrixEnergy_normalizedSkewMatrix_translation (A Ω : Finset (ZMod M))
    (hA : A.Nonempty) (φ : ZMod M → ZMod M) (P : ZMod M → ℂ) (hP : ∀ x, ‖P x‖ ≤ 1)
    {R γ η L : ℝ} (hR : 0 ≤ R) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (_hL : 0 ≤ L)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    {d : ZMod M} (hd : d ∈ bohrSet Ω γ)
    (hdt : ∀ t ∈ bohrSet Ω R, φ (d + t) = φ d + φ t)
    (hlocal : ∀ t ∈ bohrSet Ω R, ∀ a ∈ A, φ (a + t + d) = φ (a + t) + φ d)
    (hsize : ((A + bohrSet Ω R).card : ℝ) ≤ L * (A.card : ℝ)) :
    let K := normalizedSkewMatrix A (bohrSet Ω R) φ P
    let U := phaseShiftMatrix φ d
    matrixEnergy (U * K * Uᴴ - K) ≤ (4 * η * L) ^ 2 := by
  classical
  dsimp only
  let C := bohrSet Ω R
  let K := normalizedSkewMatrix A C φ P
  let U := phaseShiftMatrix φ d
  let F := U * K * Uᴴ - K
  let ν := ((A.card : ℝ) * (C.card : ℝ))⁻¹
  let E := A + C
  let D := E ∪ E.image (fun x => x + d)
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hCpos : 0 < (C.card : ℝ) := by exact_mod_cast (bohrSet_nonempty Ω hR).card_pos
  have hF (i j : ZMod M) :
      F i j = (ν : ℂ) * (ZMod.stdAddChar (skewForm φ i d) *
        conj (ZMod.stdAddChar (skewForm φ j d)) * skewCovariance A C φ P (i - d) (j - d) -
          skewCovariance A C φ P i j) := by
    unfold F U K
    rw [Matrix.sub_apply, mul_phaseShiftMatrix_conjTranspose, phaseShiftMatrix_mul,
      normalizedSkewMatrix_apply, normalizedSkewMatrix_apply]
    ring
  have hnot (i : ZMod M) (hi : i ∉ D) : i ∉ E ∧ i - d ∉ E := by
    refine ⟨fun h => hi (Finset.mem_union_left _ h), fun h => hi (Finset.mem_union_right _ ?_)⟩
    exact Finset.mem_image.mpr ⟨i - d, h, sub_add_cancel _ _⟩
  have hrow (i : ZMod M) (hi : i ∉ D) (j : ZMod M) : F i j = 0 := by
    rw [hF, skewCovariance_eq_zero_of_row_notMem A C φ P (hnot i hi).1,
      skewCovariance_eq_zero_of_row_notMem A C φ P (hnot i hi).2]
    ring
  have hcol (j : ZMod M) (hj : j ∉ D) (i : ZMod M) : F i j = 0 := by
    rw [hF, skewCovariance_eq_zero_of_col_notMem A C φ P i (hnot j hj).1,
      skewCovariance_eq_zero_of_col_notMem A C φ P (i - d) (hnot j hj).2]
    ring
  have hen (i j : ZMod M) : ‖F i j‖ ≤ 2 * η / (A.card : ℝ) := by
    have hv : 0 ≤ ν := by unfold ν; positivity
    rw [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv]
    calc
      _ ≤ ν * (2 * η * (C.card : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (skewCovariance_approx_translation A Ω φ P hP hγ hη hband hd hdt hlocal i j) hv
      _ = _ := by unfold ν; field_simp
  have hD : (D.card : ℝ) ≤ 2 * L * (A.card : ℝ) := by
    have hi : (D.card : ℝ) ≤ (E.card : ℝ) + (E.card : ℝ) := by
      exact_mod_cast (Finset.card_union_le E (E.image (fun x => x + d))).trans
        (Nat.add_le_add_left Finset.card_image_le E.card)
    change (E.card : ℝ) ≤ L * (A.card : ℝ) at hsize
    linarith only [hi, hsize]
  change matrixEnergy F ≤ _
  rw [matrixEnergy_eq_sum_if_supported F D hrow hcol]
  calc
    _ ≤ ∑ _ ∈ D, ∑ _ ∈ D, (2 * η / (A.card : ℝ)) ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hen i j) 2
    _ = ((D.card : ℝ) * (2 * η / (A.card : ℝ))) ^ 2 := by simp [Finset.sum_const]; ring
    _ ≤ ((2 * L * (A.card : ℝ)) * (2 * η / (A.card : ℝ))) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hD (by positivity : 0 ≤ 2 * η / (A.card : ℝ))
      exact pow_le_pow_left₀ (by positivity) h 2
    _ = _ := by field_simp; ring

end NormalizedCovariance

section BohrWeyl

open scoped Matrix ComplexOrder

variable {M : ℕ} [NeZero M]

private lemma exists_bohr_skew_multiplier (Ω : Finset (ZMod M)) (φ : ZMod M → ZMod M)
    (P F : ZMod M → ℂ) (hP : ∀ x, ‖P x‖ ≤ 1) (hF : ∀ x, ‖F x‖ ≤ 1)
    {r s t η q : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hη : 0 ≤ η)
    (hrr : r + r ≤ 1 / 2) (hrst : r + s + t + t ≤ 1 / 2)
    (hb₁ : ((bohrSet Ω (r + s)).card : ℝ) ≤ 2 * ((bohrSet Ω (r - s)).card : ℝ))
    (hb₂ : ((bohrSet Ω (s + t)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (s - t)).card : ℝ))
    (hq : 0 < q) (hSkew : q * ((bohrSet Ω r).card : ℝ) ^ 2 ≤
      ‖∑ a ∈ bohrSet Ω r, ∑ b ∈ bohrSet Ω r,
        P a * conj (P b) * F (a + b) * ZMod.stdAddChar (skewForm φ a b)‖)
    (hadd : ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b)
    (m : ℕ) (hm : 8 ≤ (m : ℝ) * (q ^ 4 / 64)) {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hsmall : (m.factorial : ℝ) * ((m : ℝ) * ε * 2 ^ m) ≤ 1 / 2)
    (hpert : (8 * η) ^ 2 ≤ (q ^ 4 / 64 / (12 * (m : ℝ))) ^ 2 * ε) :
    ∃ j : ℕ, 0 < j ∧ j ≤ m ∧ ∀ d ∈ bohrSet Ω t, ∀ e ∈ bohrSet Ω t,
      ‖ZMod.stdAddChar (j • (-2 * skewForm φ d e)) - 1‖ ≤
        8 * (m.factorial : ℝ) * (m : ℝ) * ε * 2 ^ m := by
  classical
  let A := bohrSet Ω r
  let C := bohrSet Ω s
  let D := bohrSet Ω t
  let K := normalizedSkewMatrix A C φ P
  let v := q ^ 4 / 64
  let S := ∑ a ∈ A, ∑ b ∈ A, P a * conj (P b) * F (a + b) * ZMod.stdAddChar (skewForm φ a b)
  let T := ∑ x ∈ A + C, ∑ y ∈ A + C, ‖skewCovariance A C φ P x y‖ ^ 2
  have hA := bohrSet_nonempty Ω hr
  have hC := bohrSet_nonempty Ω hs
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hCpos : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  have hAB := regular_bohr_add_sub_card Ω hs (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [one_add_one_eq_two] using hb₁)
  change ((A + C).card : ℝ) ≤ _ ∧ ((A - C).card : ℝ) ≤ _ at hAB
  norm_num at hAB
  have hloc {x y : ZMod M} {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
      (hub : u + w ≤ 1 / 2) (hx : x ∈ bohrSet Ω u) (hy : y ∈ bohrSet Ω w) :
      φ (x + y) = φ x + φ y :=
    hadd x (bohrSet_mono (by linarith) hx) y (bohrSet_mono (by linarith) hy)
      (bohrSet_mono hub (add_mem_bohrSet hx hy))
  have hplus (a : ZMod M) (ha : a ∈ A) (b : ZMod M) (hb : b ∈ C) :
      φ (a + b) = φ a + φ b := hloc hr hs (by linarith) ha hb
  have hsub (a : ZMod M) (ha : a ∈ A) (b : ZMod M) (hb : b ∈ C) :
      φ (a - b) = φ a - φ b := by
    have hsum : a - b + b ∈ bohrSet Ω (1 / 2) := by
      rw [sub_add_cancel]
      exact bohrSet_mono (by linarith) ha
    have h := hadd (a - b) (bohrSet_mono (by linarith) (diff_mem_bohrSet ha hb))
      b (bohrSet_mono (by linarith) hb) hsum
    rw [sub_add_cancel] at h
    linear_combination -h
  have hQ (x : ZMod M) : ‖conj (P x)‖ ≤ 1 := by simpa only [Complex.norm_conj] using hP x
  have hc := skewWeight_to_covariance_norm A A C hC φ P (fun x => conj (P x)) F hQ hF
    hplus hsub (fun a ha b hb => hloc hr hr hrr ha hb)
  change (C.card : ℝ) ^ 2 * ‖S‖ ^ 4 ≤
    ((A + C).card : ℝ) ^ 2 * ((A - C).card : ℝ) ^ 4 * T at hc
  have hbound : v * ((A.card : ℝ) * (C.card : ℝ)) ^ 2 ≤ T := by
    apply le_of_mul_le_mul_left _ (show 0 < 64 * (A.card : ℝ) ^ 6 by positivity)
    calc
      _ = (C.card : ℝ) ^ 2 * (q * (A.card : ℝ) ^ 2) ^ 4 := by unfold v; ring
      _ ≤ (C.card : ℝ) ^ 2 * ‖S‖ ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hSkew _) (by positivity)
      _ ≤ ((A + C).card : ℝ) ^ 2 * ((A - C).card : ℝ) ^ 4 * T := hc
      _ ≤ (2 * (A.card : ℝ)) ^ 2 * (2 * (A.card : ℝ)) ^ 4 * T := by
        apply mul_le_mul_of_nonneg_right _ (by unfold T; positivity)
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) hAB.1 2)
          (pow_le_pow_left₀ (by positivity) hAB.2 4) (by positivity) (by positivity)
      _ = _ := by ring
  have hKv : v ≤ matrixEnergy K := by
    rw [matrixEnergy_normalizedSkewMatrix]
    change v ≤ (((A.card : ℝ) * (C.card : ℝ))⁻¹) ^ 2 * T
    have h := mul_le_mul_of_nonneg_left hbound
      (show 0 ≤ (((A.card : ℝ) * (C.card : ℝ))⁻¹) ^ 2 by positivity)
    calc
      _ = (((A.card : ℝ) * (C.card : ℝ))⁻¹) ^ 2 *
          (v * ((A.card : ℝ) * (C.card : ℝ)) ^ 2) := by field_simp
      _ ≤ _ := h
  have hEnergy (d : ZMod M) (hd : d ∈ D) :
      matrixEnergy (phaseShiftMatrix φ d * K * (phaseShiftMatrix φ d)ᴴ - K) ≤
        (8 * η) ^ 2 := by
    have h := matrixEnergy_normalizedSkewMatrix_translation A Ω hA φ P hP hs ht hη
      (by norm_num : (0 : ℝ) ≤ 2) hb₂ hd
      (fun u hu => hloc ht hs (by linarith) hd hu)
      (fun u hu a ha => hloc (by linarith : 0 ≤ r + s) ht (by linarith) (add_mem_bohrSet ha hu) hd)
      hAB.1
    convert h using 1; ring
  obtain ⟨j, hj, hjm, hPhase⟩ := bounded_dimension_controls_weyl_phase K
    (normalizedSkewMatrix_posSemidef A C φ P) (normalizedSkewMatrix_trace_le_one A C hA hC φ P hP)
    (show 0 < v by unfold v; positivity) hKv m hm hε hε₁ hsmall
  refine ⟨j, hj, hjm, ?_⟩
  intro d hd e he
  have hAC : A + C ⊆ bohrSet Ω (r + s) := by
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp ha
    exact add_mem_bohrSet hx hy
  have hcomm := phaseShiftMatrix_pair_commute_on_normalizedSkewMatrix A C φ P
    (fun a ha => hloc (by linarith : 0 ≤ r + s + t) ht hrst (add_mem_bohrSet (hAC ha) he) hd)
    (fun a ha => hloc (by linarith : 0 ≤ r + s + t) ht hrst (add_mem_bohrSet (hAC ha) hd) he)
  rw [AddChar.map_nsmul_eq_pow]
  exact hPhase (phaseShiftMatrix φ d) (phaseShiftMatrix φ e) _ (norm_stdAddChar _)
    (phaseShiftMatrix_star_mul _ _) (phaseShiftMatrix_mul_star _ _)
    (phaseShiftMatrix_star_mul _ _) (phaseShiftMatrix_mul_star _ _)
    ((hEnergy d hd).trans hpert) ((hEnergy e he).trans hpert) hcomm

end BohrWeyl

section NestedBohr

variable {M : ℕ} [NeZero M]

private lemma exists_nested_bohr_bands (Ω : Finset (ZMod M)) {γ η : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (k : ℕ) (hk : 1 ≤ (k : ℝ) * η) :
    let n := 15 * Ω.card + 1
    let γ₁ := (γ / 2) / (2 * (n : ℝ))
    let t := (γ₁ / 2) / (2 * ((k * n : ℕ) : ℝ))
    ∃ r s : ℝ, γ / 2 ≤ r ∧ r ≤ γ ∧ γ₁ / 2 ≤ s ∧ s ≤ γ₁ ∧
      ((bohrSet Ω (r + γ₁)).card : ℝ) ≤ 2 * ((bohrSet Ω (r - γ₁)).card : ℝ) ∧
      ((bohrSet Ω (s + t)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (s - t)).card : ℝ) := by
  dsimp only
  let n := 15 * Ω.card + 1
  let γ₁ := (γ / 2) / (2 * (n : ℝ))
  have hn : 0 < (n : ℝ) := by unfold n; positivity
  have hγ₁ : 0 < γ₁ := by unfold γ₁; positivity
  obtain ⟨r, hrlo, hrhi, hr⟩ := exists_bohr_band Ω
    (by positivity : 0 < γ / 2) (by norm_num : (0 : ℝ) < 1) 1 (by norm_num)
  obtain ⟨s, hslo, hshi, hs⟩ := exists_bohr_band Ω
    (by positivity : 0 < γ₁ / 2) hη k hk
  refine ⟨r, s, hrlo, by linarith only [hrhi], hslo, by linarith only [hshi], ?_, hs⟩
  simpa only [one_mul, one_add_one_eq_two, n, γ₁] using hr

end NestedBohr

private noncomputable def skewCorrelationRate (δ : ℝ) : ℝ :=
  (graphDensityRate δ * Real.sqrt (δ / 6) / 36) ^ 2

private lemma skewCorrelationRate_pos {δ : ℝ} (hδ : 0 < δ) : 0 < skewCorrelationRate δ := by
  have hr := graphDensityRate_pos hδ
  have hs : 0 < Real.sqrt (δ / 6) := Real.sqrt_pos.2 (by positivity)
  unfold skewCorrelationRate
  positivity

private lemma exists_skew_multiplier_of_regular_structure {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) {f : ℤ → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (hstructure : RegularLocalFrequencyStructure N δ 1 1 f)
    (m : ℕ) (hm : 8 ≤ (m : ℝ) * (skewCorrelationRate δ ^ 4 / 64))
    {ε η : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hη : 0 < η)
    (hsmall : (m.factorial : ℝ) * ((m : ℝ) * ε * 2 ^ m) ≤ 1 / 2)
    (hpert : (8 * η) ^ 2 ≤ (skewCorrelationRate δ ^ 4 / 64 / (12 * (m : ℝ))) ^ 2 * ε)
    (k : ℕ) (hk : 1 ≤ (k : ℝ) * η) :
    ∃ Ω J : Finset (ZMod (2 * N + 1)), ∃ ξ φ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
      ∃ c : ZMod (2 * N + 1), ∃ R : ℝ, ∃ j : ℕ,
      let n := 15 * Ω.card + 1
      let γ : ℝ := (1 / 16) / (2 * (n : ℝ))
      let t : ℝ := 1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))
      1 / 16 ≤ R ∧ R ≤ 1 / 8 ∧ J.Nonempty ∧
      (Ω.card : ℝ) * graphDensityRate δ ^ 2 ≤ 18 ∧
      ((bohrSet Ω (R + γ)).card : ℝ) ≤ 2 * ((bohrSet Ω (R - γ)).card : ℝ) ∧
      2 * N + 1 ≤ 32768 ^ (((k * n ^ 3).log2 + 6) * Ω.card) * (bohrSet Ω t).card ∧
      (graphDensityRate δ / 3) * ((bohrSet Ω R).card : ℝ) ≤ (J.card : ℝ) ∧
      (∀ a ∈ J, a - c ∈ bohrSet Ω R) ∧
      (∀ a ∈ J, Real.sqrt (δ / 6) * (N : ℝ) ≤
        ‖fourier (cyclicDerivative (periodize N f) a) (ξ a)‖) ∧
      (∀ a ∈ J, ∀ b ∈ J, φ (a - b) = ξ a - ξ b) ∧
      (∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
        a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b) ∧
      0 < j ∧ j ≤ m ∧ (∀ a ∈ bohrSet Ω t, ∀ b ∈ bohrSet Ω t,
        ‖ZMod.stdAddChar (j • (-2 * skewForm φ a b)) - 1‖ ≤
          8 * (m.factorial : ℝ) * (m : ℝ) * ε * 2 ^ m) := by
  obtain ⟨Ω, J, ξ, φ, c, R, hR, hRhi, hJ, hdim, hband, _, _, hsize, hpos, hξ, hφ, hadd⟩ := hstructure
  let n := 15 * Ω.card + 1
  let γ : ℝ := (1 / 16) / (2 * (n : ℝ))
  let γ₁ : ℝ := (γ / 2) / (2 * (n : ℝ))
  let t : ℝ := (γ₁ / 2) / (2 * ((k * n : ℕ) : ℝ))
  have hn : 1 ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : 1 ≤ k := by
    by_contra! h
    have he : k = 0 := by omega
    norm_num [he] at hk
  have hkn : (1 : ℝ) ≤ ((k * n : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hk' hn
  have hγ : 0 < γ := by unfold γ; positivity
  have hγ₁ : 0 < γ₁ := by unfold γ₁; positivity
  have ht : 0 < t := by unfold t; positivity
  have hγhi : γ ≤ 1 / 32 := by
    dsimp [γ]
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hγ₁hi : γ₁ ≤ γ / 4 := by
    dsimp [γ₁]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hγ, hn', mul_nonneg hγ.le (sub_nonneg.mpr hn')]
  have hthi : t ≤ γ₁ / 4 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hγ₁, hkn, mul_nonneg hγ₁.le (sub_nonneg.mpr hkn)]
  have htFormula : t = 1 / (512 * ((k * n ^ 3 : ℕ) : ℝ)) := by
    dsimp only [t, γ₁, γ]
    push_cast
    field_simp
    ring
  obtain ⟨r, s, hrlo, hrhi, hslo, hshi, hb₁, hb₂⟩ := exists_nested_bohr_bands Ω hγ hη k hk
  have hr : 0 ≤ r := by linarith only [hγ, hrlo]
  have hs : 0 ≤ s := by linarith only [hγ₁, hslo]
  have hForward : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + 1) * ((bohrSet Ω (R - γ)).card : ℝ) := by
    simpa only [one_mul] using hband
  have hrate := graphDensityRate_pos hδ
  have hcoef : 0 ≤ Real.sqrt (δ / 6) * (N : ℝ) := by positivity
  obtain ⟨P, F, hP, hF, hskew⟩ := exists_skewWeight_after_reslice (periodize N f)
    (fun x => hf (x.val : ℤ)) Ω J hJ (by linarith only [hR]) hr hrhi
    (by linarith only [hrhi, hγhi]) (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 < graphDensityRate δ / 3) hcoef hForward c ξ φ hpos hsize hξ
    (fun a ha b hb => (hφ a ha b hb).2) hadd
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hM : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hNM : (1 / 3 : ℝ) ≤ (N : ℝ) / ((2 * N + 1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hM).2
    push_cast
    linarith only [hN']
  have hrate' : graphDensityRate δ * Real.sqrt (δ / 6) / 36 ≤
      (graphDensityRate δ / 3 / (1 + 1) * (Real.sqrt (δ / 6) * (N : ℝ)) /
        ((2 * N + 1 : ℕ) : ℝ) / (1 + 1)) := by
    calc
      _ = (graphDensityRate δ * Real.sqrt (δ / 6) / 12) * (1 / 3) := by ring
      _ ≤ (graphDensityRate δ * Real.sqrt (δ / 6) / 12) *
          ((N : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hNM (by positivity)
      _ = _ := by ring
  have hskew' : skewCorrelationRate δ * ((bohrSet Ω r).card : ℝ) ^ 2 ≤
      ‖∑ a ∈ bohrSet Ω r, ∑ b ∈ bohrSet Ω r,
        P a * conj (P b) * F (a + b) * ZMod.stdAddChar (skewForm φ a b)‖ := by
    refine (mul_le_mul_of_nonneg_right ?_ (by positivity)).trans hskew
    exact pow_le_pow_left₀ (by positivity) hrate' 2
  have hb₁' : ((bohrSet Ω (r + s)).card : ℝ) ≤ 2 * ((bohrSet Ω (r - s)).card : ℝ) := by
    have h := bohr_band_mono Ω hshi (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [one_add_one_eq_two] using hb₁)
    simpa only [one_add_one_eq_two] using h
  obtain ⟨j, hj, hjm, hsym⟩ := exists_bohr_skew_multiplier Ω φ P F hP hF hr hs ht.le hη.le
    (by linarith only [hrhi, hγhi])
    (by linarith only [hrhi, hshi, hthi, hγ₁hi, hγhi])
    hb₁' hb₂ (skewCorrelationRate_pos hδ) hskew' hadd m hm hε hε₁ hsmall hpert
  have hCard : 2 * N + 1 ≤ 32768 ^ (((k * n ^ 3).log2 + 6) * Ω.card) * (bohrSet Ω t).card := by
    apply bohrSet_card_lower_small_radius Ω ht ((k * n ^ 3).log2 + 5)
    have hpow : ((k * n ^ 3 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((k * n ^ 3).log2 + 1) := by
      exact_mod_cast Nat.lt_log2_self.le
    rw [htFormula, pow_add, show (2 : ℝ) ^ 5 = 16 * 2 by norm_num]
    field_simp
    nlinarith only [hpow, pow_succ (2 : ℝ) (k * n ^ 3).log2]
  refine ⟨Ω, J, ξ, φ, c, R, j, hR, hRhi, hJ, hdim, ?_, ?_, hsize, hpos, hξ,
    (fun a ha b hb => (hφ a ha b hb).2), hadd, hj, hjm, ?_⟩
  · simpa only [one_add_one_eq_two] using hForward
  · change 2 * N + 1 ≤ 32768 ^ (((k * n ^ 3).log2 + 6) * Ω.card) *
      (bohrSet Ω (1 / (512 * ((k * n ^ 3 : ℕ) : ℝ)))).card
    rw [← htFormula]
    exact hCard
  · change ∀ a ∈ bohrSet Ω (1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))),
        ∀ b ∈ bohrSet Ω (1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))),
          ‖ZMod.stdAddChar (j • (-2 * skewForm φ a b)) - 1‖ ≤
            8 * (m.factorial : ℝ) * (m : ℝ) * ε * 2 ^ m
    rw [← htFormula]
    exact hsym

section BohrDilation

variable {M : ℕ} [NeZero M]

private lemma nsmul_mem_scaled_bohr (Ω : Finset (ZMod M)) {r : ℝ}
    {x : ZMod M} (hx : x ∈ bohrSet Ω r) (n : ℕ) :
    n • x ∈ bohrSet Ω ((n : ℝ) * r) := by
  induction n with
  | zero =>
    simp only [zero_nsmul, Nat.cast_zero, zero_mul]
    exact mem_bohrSet.mpr (fun k _ => by simp)
  | succ n ih =>
    have h := add_mem_bohrSet ih hx
    simpa only [succ_nsmul, Nat.cast_succ, add_mul, one_mul] using h

private lemma localAdditive_nsmul_on_bohr (Ω : Finset (ZMod M)) {R r : ℝ} (hr : 0 ≤ r)
    (φ : ZMod M → ZMod M)
    (hadd : ∀ a ∈ bohrSet Ω R, ∀ b ∈ bohrSet Ω R,
      a + b ∈ bohrSet Ω R → φ (a + b) = φ a + φ b)
    {x : ZMod M} (hx : x ∈ bohrSet Ω r) (n : ℕ) (hn : (n : ℝ) * r ≤ R) :
    φ (n • x) = n • φ x := by
  have hR : 0 ≤ R := (by positivity : 0 ≤ (n : ℝ) * r).trans hn
  induction n with
  | zero =>
    have hz : (0 : ZMod M) ∈ bohrSet Ω R := mem_bohrSet.mpr (fun k _ => by simpa using hR)
    have hh := hadd 0 hz 0 hz (by simpa using hz)
    simp only [zero_add] at hh
    simp only [zero_nsmul]
    exact add_left_cancel (a := φ 0) (by simpa using hh.symm)
  | succ n ih =>
    have he : ((n + 1 : ℕ) : ℝ) * r = (n : ℝ) * r + r := by push_cast; ring
    have hn' : (n : ℝ) * r ≤ R := by linarith only [hn, he, hr]
    have hr' : r ≤ R := by linarith only [hn, he, show 0 ≤ (n : ℝ) * r by positivity]
    have h₁ := bohrSet_mono hn' (nsmul_mem_scaled_bohr Ω hx n)
    have h₂ := bohrSet_mono hr' hx
    have h₃ : n • x + x ∈ bohrSet Ω R := by
      rw [← succ_nsmul]
      exact bohrSet_mono hn (nsmul_mem_scaled_bohr Ω hx (n + 1))
    simp only [succ_nsmul]
    rw [hadd _ h₁ _ h₂ h₃, ih hn']

private lemma card_le_mul_card_nsmul_image (A : Finset (ZMod M)) {k : ℕ} (hk : 0 < k) :
    A.card ≤ k * (A.image (fun x => k • x)).card := by
  let F (x : ZMod M) := (k * x.val / M, k • x)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h := Finset.card_le_card_of_injOn F
    (s := A) (t := Finset.range k ×ˢ A.image (fun x => k • x)) ?_ ?_
  · simpa only [Finset.card_product, Finset.card_range] using h
  · intro x hx
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    apply (Nat.div_lt_iff_lt_mul hM).2
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x) hk
  · intro x _ y _ he
    have hdiv : k * x.val / M = k * y.val / M := congrArg Prod.fst he
    have hval (z : ZMod M) : (k • z).val = (k * z.val) % M := by
      calc
        _ = ((k : ZMod M) * (z.val : ZMod M)).val := by
          rw [ZMod.natCast_zmod_val, nsmul_eq_mul]
        _ = _ := by rw [← Nat.cast_mul, ZMod.val_natCast]
    have hmod := congrArg (fun z : ℕ × ZMod M => z.2.val) he
    change (k • x).val = (k • y).val at hmod
    rw [hval, hval] at hmod
    have hxy : k * x.val = k * y.val := by
      rw [← Nat.mod_add_div (k * x.val) M, hdiv, hmod, Nat.mod_add_div]
    have h' := Nat.eq_of_mul_eq_mul_left hk hxy
    rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, h']

private lemma norm_stdAddChar_neg_sub_one {M : ℕ} [NeZero M] (a : ZMod M) :
    ‖ZMod.stdAddChar (-a) - 1‖ = ‖ZMod.stdAddChar a - 1‖ := by
  rw [show -a = 0 - a by simp, norm_stdAddChar_sub_one, AddChar.map_zero_eq_one, norm_sub_rev]

private lemma norm_polarizationDefect_on_dilate {N : ℕ}
    (Ω : Finset (ZMod (2 * N + 1))) {R r s : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r)
    (φ : ZMod (2 * N + 1) → ZMod (2 * N + 1))
    (hadd : ∀ a ∈ bohrSet Ω R, ∀ b ∈ bohrSet Ω R,
      a + b ∈ bohrSet Ω R → φ (a + b) = φ a + φ b)
    {j : ℕ} (hjs : ((4 * j : ℕ) : ℝ) * s ≤ R) {τ : ℝ}
    (hskew : ∀ x ∈ bohrSet Ω r, ∀ y ∈ bohrSet Ω r,
      ‖ZMod.stdAddChar (j • (-2 * skewForm φ x y)) - 1‖ ≤ τ)
    (x : ZMod (2 * N + 1)) (hx : x ∈ bohrSet Ω r)
    (y : ZMod (2 * N + 1)) (hy : y ∈ (bohrSet Ω s).image (fun z => (4 * j) • z)) :
    ‖ZMod.stdAddChar (polarizationDefect φ x y) - 1‖ ≤ τ := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hφ := localAdditive_nsmul_on_bohr Ω hs φ hadd hz (4 * j) hjs
  have he : polarizationDefect φ x ((4 * j) • z) =
      -(j • (-2 * skewForm φ x z)) := by
    unfold polarizationDefect skewForm
    rw [hφ]
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    linear_combination
      (2 * (j : ZMod (2 * N + 1)) * (z * φ x - x * φ z)) *
        (add_halfMod_self N)
  rw [he, norm_stdAddChar_neg_sub_one]
  exact hskew x hx z (bohrSet_mono hsr hz)

end BohrDilation

section PhaseUntwisting

private lemma norm_localQuadratic_twist_sub {N : ℕ}
    {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)} {x y : ZMod (2 * N + 1)}
    (hxy : φ (x + y) = φ x + φ y) :
    ‖ZMod.stdAddChar (-(x * φ y)) -
        ZMod.stdAddChar (localQuadratic φ x + localQuadratic φ y - localQuadratic φ (x + y))‖ =
      ‖ZMod.stdAddChar (polarizationDefect φ x y) - 1‖ := by
  rw [show localQuadratic φ x + localQuadratic φ y - localQuadratic φ (x + y) =
      -(localQuadratic φ (x + y) - localQuadratic φ x - localQuadratic φ y) by ring,
    ← conj_stdAddChar, ← conj_stdAddChar, ← map_sub, Complex.norm_conj, norm_sub_rev,
    norm_localQuadratic_polarization_error hxy]

private lemma quadratic_untwist_error {N : ℕ}
    (A B : Finset (ZMod (2 * N + 1))) (φ : ZMod (2 * N + 1) → ZMod (2 * N + 1))
    (U V W : ZMod (2 * N + 1) → ℂ) (hU : ∀ x, ‖U x‖ ≤ 1)
    (hV : ∀ x, ‖V x‖ ≤ 1) (hW : ∀ x, ‖W x‖ ≤ 1)
    (hadd : ∀ x ∈ A, ∀ y ∈ B, φ (x + y) = φ x + φ y) {τ : ℝ}
    (hsym : ∀ x ∈ A, ∀ y ∈ B, ‖ZMod.stdAddChar (polarizationDefect φ x y) - 1‖ ≤ τ) :
    let q := localQuadratic φ
    let U' := fun x => U x * ZMod.stdAddChar (q x)
    let V' := fun y => V y * ZMod.stdAddChar (q y)
    let W' := fun z => W z * ZMod.stdAddChar (-q z)
    ‖(∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y))) -
        (∑ y ∈ B, ∑ x ∈ A, U' x * V' y * W' (x + y))‖ ≤ τ * (A.card : ℝ) * (B.card : ℝ) := by
  dsimp only
  let q := localQuadratic φ
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ B, ∑ _ ∈ A, τ := by
      refine Finset.sum_le_sum fun y hy => (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun x hx => ?_
      have hc : ZMod.stdAddChar (q x) * ZMod.stdAddChar (q y) * ZMod.stdAddChar (-q (x + y)) =
          ZMod.stdAddChar (q x + q y - q (x + y)) := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg]
      have he :
          U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y)) -
              U x * ZMod.stdAddChar (q x) * (V y * ZMod.stdAddChar (q y)) *
                (W (x + y) * ZMod.stdAddChar (-q (x + y))) =
          (U x * V y * W (x + y)) *
            (ZMod.stdAddChar (-(x * φ y)) - ZMod.stdAddChar (q x + q y - q (x + y))) := by
        linear_combination -(U x * V y * W (x + y)) * hc
      change ‖_ - U x * ZMod.stdAddChar (q x) * (V y * ZMod.stdAddChar (q y)) *
          (W (x + y) * ZMod.stdAddChar (-q (x + y)))‖ ≤ τ
      rw [he, norm_mul, norm_localQuadratic_twist_sub (hadd x hx y hy)]
      refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hsym x hx y hy)
      simp only [norm_mul]
      calc
        ‖U x‖ * ‖V y‖ * ‖W (x + y)‖ ≤ (1 : ℝ) * 1 * 1 := by gcongr <;> first | apply hU | apply hV | apply hW
        _ = 1 := by norm_num
    _ = _ := by simp; ring

private lemma exists_quadratic_pair_after_reslice {N : ℕ}
    (g : ZMod (2 * N + 1) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (Ω J A B : Finset (ZMod (2 * N + 1))) (hJ : J.Nonempty) (hB : B.Nonempty)
    {R γ r η β θ σ : ℝ} (hγ : 0 ≤ γ) (hBγ : B ⊆ bohrSet Ω γ)
    (_hr : 0 ≤ r) (hr₄ : r ≤ 1 / 4) (hAr : A ⊆ bohrSet Ω r) (hBr : B ⊆ bohrSet Ω r)
    (hη : 0 ≤ η) (hβ : 0 < β) (hθ : 0 ≤ θ)
    (hσ : 2 * σ ≤ β / (1 + η) * θ / ((2 * N + 1 : ℕ) : ℝ))
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    (s : ZMod (2 * N + 1)) (ξ φ : ZMod (2 * N + 1) → ZMod (2 * N + 1))
    (hpos : ∀ a ∈ J, a - s ∈ bohrSet Ω R)
    (hcard : β * ((bohrSet Ω R).card : ℝ) ≤ (J.card : ℝ))
    (hc : ∀ a ∈ J, θ ≤ ‖fourier (cyclicDerivative g a) (ξ a)‖)
    (hφ : ∀ a ∈ J, ∀ b ∈ J, φ (a - b) = ξ a - ξ b)
    (hadd : ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b)
    (hsym : ∀ x ∈ A, ∀ y ∈ B, ‖ZMod.stdAddChar (polarizationDefect φ x y) - 1‖ ≤ σ) :
    ∃ x₀ s₀ offset : ZMod (2 * N + 1), ∃ V : ZMod (2 * N + 1) → ℂ,
      (∀ y, ‖V y‖ ≤ 1) ∧
      let q := localQuadratic φ
      let U := fun x => (g (x₀ + x) : ℂ) * ZMod.stdAddChar (q x - x * offset)
      let W := fun z => (g (x₀ + s₀ + z) : ℂ) * ZMod.stdAddChar (-q z)
      σ * (A.card : ℝ) * (B.card : ℝ) ≤ ‖∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y)‖ := by
  obtain ⟨x₀, s₀, offset, U, V, W, hUeq, hWeq, hU, hV, hW, hcorr⟩ :=
    exists_relative_twist_after_reslice g hg Ω J A B hJ hB hγ hBγ hr₄ hBr hη hβ hθ hband s ξ φ
      hpos hcard hc hφ hadd
  let q := localQuadratic φ
  let V' := fun y => V y * ZMod.stdAddChar (q y)
  have hV' (y : ZMod (2 * N + 1)) : ‖V' y‖ ≤ 1 := by simpa [V', norm_mul, norm_stdAddChar] using hV y
  have hadd' (x : ZMod (2 * N + 1)) (hx : x ∈ A) (y : ZMod (2 * N + 1)) (hy : y ∈ B) :
      φ (x + y) = φ x + φ y := by
    apply hadd
    · exact bohrSet_mono (by linarith) (hAr hx)
    · exact bohrSet_mono (by linarith) (hBr hy)
    · exact bohrSet_mono (by linarith) (add_mem_bohrSet (hAr hx) (hBr hy))
  have herr := quadratic_untwist_error A B φ U V W hU hV hW hadd' hsym
  let S := ∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y) * ZMod.stdAddChar (-(x * φ y))
  let T := ∑ y ∈ B, ∑ x ∈ A, (U x * ZMod.stdAddChar (q x)) * V' y *
    (W (x + y) * ZMod.stdAddChar (-q (x + y)))
  change ‖S - T‖ ≤ σ * (A.card : ℝ) * (B.card : ℝ) at herr
  have hsum : ‖S‖ ≤ ‖S - T‖ + ‖T‖ := by
    simpa only [sub_add_cancel] using norm_add_le (S - T) T
  have hhigh : 2 * σ * (A.card : ℝ) * (B.card : ℝ) ≤ ‖S‖ :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hσ (by positivity)) (by positivity)).trans hcorr
  have hT : σ * (A.card : ℝ) * (B.card : ℝ) ≤ ‖T‖ := by linarith only [hsum, hhigh, herr]
  refine ⟨x₀, s₀, offset, V', hV', ?_⟩
  have he (x : ZMod (2 * N + 1)) :
      U x * ZMod.stdAddChar (q x) = (g (x₀ + x) : ℂ) * ZMod.stdAddChar (q x - x * offset) := by
    rw [hUeq, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simpa only [T, he, hWeq] using hT

end PhaseUntwisting

private noncomputable def quadraticPairRate (δ : ℝ) : ℝ :=
  min 1 (graphDensityRate δ * Real.sqrt (δ / 6) / 36)

private lemma quadraticPairRate_pos {δ : ℝ} (hδ : 0 < δ) : 0 < quadraticPairRate δ := by
  have hr := graphDensityRate_pos hδ
  have hs : 0 < Real.sqrt (δ / 6) := Real.sqrt_pos.2 (by positivity)
  exact lt_min (by norm_num) (by positivity)

private def QuadraticPairStructure (N : ℕ) (δ : ℝ) (m k : ℕ) (f : ℤ → ℝ) : Prop :=
  ∃ Ω : Finset (ZMod (2 * N + 1)), ∃ φ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
    ∃ R : ℝ, ∃ B : Finset (ZMod (2 * N + 1)),
    ∃ x₀ s₀ offset : ZMod (2 * N + 1), ∃ V : ZMod (2 * N + 1) → ℂ,
    let n := 15 * Ω.card + 1
    let t : ℝ := 1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))
    let u := (t / 2) / (2 * (n : ℝ))
    let A := bohrSet Ω R
    let q := localQuadratic φ
    let g := periodize N f
    let U := fun x => (g (x₀ + x) : ℂ) * ZMod.stdAddChar (q x - x * offset)
    let W := fun z => (g (x₀ + s₀ + z) : ℂ) * ZMod.stdAddChar (-q z)
    t / 2 ≤ R ∧ R ≤ t ∧ B.Nonempty ∧ B ⊆ A ∧
    (Ω.card : ℝ) * graphDensityRate δ ^ 2 ≤ 18 ∧
    B ⊆ bohrSet Ω (u / 2) ∧
    ((bohrSet Ω (R + u)).card : ℝ) ≤ 2 * ((bohrSet Ω (R - u)).card : ℝ) ∧
    2 * N + 1 ≤ 32768 ^ (((m * k * n ^ 4).log2 + 11) * Ω.card) * (4 * m * B.card) ∧
    (∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b) ∧
    (∀ y, ‖V y‖ ≤ 1) ∧
    quadraticPairRate δ * (A.card : ℝ) * (B.card : ℝ) ≤
      ‖∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y)‖

private lemma quadraticPair_of_regular_structure {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) {f : ℤ → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (hstructure : RegularLocalFrequencyStructure N δ 1 1 f)
    (m : ℕ) (hm : 8 ≤ (m : ℝ) * (skewCorrelationRate δ ^ 4 / 64))
    {ε η : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hη : 0 < η)
    (hsmall : (m.factorial : ℝ) * ((m : ℝ) * ε * 2 ^ m) ≤ 1 / 2)
    (hpert : (8 * η) ^ 2 ≤ (skewCorrelationRate δ ^ 4 / 64 / (12 * (m : ℝ))) ^ 2 * ε)
    (hphase : 8 * (m.factorial : ℝ) * (m : ℝ) * ε * 2 ^ m ≤ quadraticPairRate δ)
    (k : ℕ) (hk : 1 ≤ (k : ℝ) * η) :
    QuadraticPairStructure N δ m k f := by
  obtain ⟨Ω, J, ξ, φ, c, R, j, hR, hRhi, hJ, hdim, hband, _, hJsize, hpos, hξ, hφ, hadd,
    hj, hjm, hsym⟩ :=
      exists_skew_multiplier_of_regular_structure hN hδ hf hstructure m hm hε hε₁ hη hsmall hpert k hk
  let n := 15 * Ω.card + 1
  let γ : ℝ := (1 / 16) / (2 * (n : ℝ))
  let t : ℝ := 1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))
  let u : ℝ := (t / 2) / (2 * (n : ℝ))
  let v : ℝ := (u / 2) / ((4 * m : ℕ) : ℝ)
  have hn : 1 ≤ n := by omega
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm₀ : 0 < m := hj.trans_le hjm
  have hk₀ : 0 < k := by
    by_contra! h
    have he : k = 0 := by omega
    norm_num [he] at hk
  have hkn : (0 : ℝ) < ((k * n ^ 3 : ℕ) : ℝ) := by positivity
  have hγ : 0 < γ := by unfold γ; positivity
  have ht : 0 < t := by unfold t; positivity
  have hu : 0 < u := by unfold u; positivity
  have hv : 0 < v := by unfold v; positivity
  have htn : t ≤ γ := by
    dsimp [t, γ]
    have hkn' : (n : ℝ) ≤ ((k * n ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ k * n ^ 3 by
        calc
          n ≤ n ^ 3 := by
            simpa only [pow_one] using Nat.pow_le_pow_right hn (by norm_num : 1 ≤ 3)
          _ ≤ _ := Nat.le_mul_of_pos_left _ hk₀)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    linarith only [hkn']
  have ht₄ : t ≤ 1 / 4 := by
    refine htn.trans ?_
    unfold γ
    apply (div_le_iff₀ (by positivity)).2
    linarith only [hnr]
  have hut : u ≤ t / 4 := by
    unfold u
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [ht, hnr, mul_nonneg ht.le (sub_nonneg.mpr hnr)]
  have hvt : v ≤ t := by
    have h4m : (1 : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 4) hm₀
    have h := div_le_self (show 0 ≤ u / 2 by positivity) h4m
    linarith only [show v ≤ u / 2 from h, hut, ht]
  obtain ⟨R₁, hRlo, hRup, hInner⟩ := exists_bohr_band Ω
    (by positivity : 0 < t / 2) (by norm_num : (0 : ℝ) < 1) 1 (by norm_num)
  have hRup' : R₁ ≤ t := by linarith only [hRup]
  have hInner' : ((bohrSet Ω (R₁ + u)).card : ℝ) ≤ (1 + 1) * ((bohrSet Ω (R₁ - u)).card : ℝ) := by
    simpa only [one_mul, u, n] using hInner
  let A := bohrSet Ω R₁
  let B₀ := bohrSet Ω v
  let B := B₀.image (fun x => (4 * j) • x)
  have hB : B.Nonempty := (bohrSet_nonempty Ω hv.le).image _
  have hScale : ((4 * j : ℕ) : ℝ) * v ≤ u / 2 := by
    have hjr : ((4 * j : ℕ) : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 4 hjm
    calc
      _ ≤ ((4 * m : ℕ) : ℝ) * v := mul_le_mul_of_nonneg_right hjr hv.le
      _ = _ := by dsimp [v]; field_simp
  have hBu : B ⊆ bohrSet Ω (u / 2) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact bohrSet_mono hScale (nsmul_mem_scaled_bohr Ω hy (4 * j))
  have huA : u / 2 ≤ R₁ := by linarith only [hut, hRlo, ht]
  have hut' : u / 2 ≤ t := by linarith only [hut, ht]
  have hBA : B ⊆ A := hBu.trans (bohrSet_mono huA)
  have hBt : B ⊆ bohrSet Ω t := hBu.trans (bohrSet_mono hut')
  have hAt : A ⊆ bohrSet Ω t := bohrSet_mono hRup'
  have hBγ : B ⊆ bohrSet Ω γ := hBt.trans (bohrSet_mono htn)
  have hvFormula : v = 1 / (16384 * ((m * k * n ^ 4 : ℕ) : ℝ)) := by
    dsimp only [v, u, t]
    push_cast
    field_simp
    ring
  have hBsize : 2 * N + 1 ≤ 32768 ^ (((m * k * n ^ 4).log2 + 11) * Ω.card) * (4 * m * B.card) := by
    have h₀ : 2 * N + 1 ≤ 32768 ^ (((m * k * n ^ 4).log2 + 11) * Ω.card) * B₀.card := by
      apply bohrSet_card_lower_small_radius Ω hv ((m * k * n ^ 4).log2 + 10)
      have hpow : ((m * k * n ^ 4 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((m * k * n ^ 4).log2 + 1) := by
        exact_mod_cast Nat.lt_log2_self.le
      rw [hvFormula, pow_add, show (2 : ℝ) ^ 10 = 512 * 2 by norm_num]
      field_simp
      nlinarith only [hpow, pow_succ (2 : ℝ) (m * k * n ^ 4).log2]
    have hB₀ : B₀.card ≤ (4 * m) * B.card :=
      (card_le_mul_card_nsmul_image B₀ (Nat.mul_pos (by decide : 0 < 4) hj)).trans
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hjm))
    exact h₀.trans (Nat.mul_le_mul_left _ hB₀)
  have hsym' (x : ZMod (2 * N + 1)) (hx : x ∈ A) (y : ZMod (2 * N + 1)) (hy : y ∈ B) :
      ‖ZMod.stdAddChar (polarizationDefect φ x y) - 1‖ ≤ quadraticPairRate δ := by
    refine (norm_polarizationDefect_on_dilate Ω hv.le hvt φ hadd
      (hScale.trans (by linarith only [hut, ht₄, ht])) hsym x (hAt hx) y hy).trans hphase
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hNM : (1 / 3 : ℝ) ≤ (N : ℝ) / ((2 * N + 1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hM).2
    push_cast
    linarith only [hN']
  have hσ : 2 * quadraticPairRate δ ≤ graphDensityRate δ / 3 / (1 + 1) *
      (Real.sqrt (δ / 6) * (N : ℝ)) / ((2 * N + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ 2 * (graphDensityRate δ * Real.sqrt (δ / 6) / 36) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ = (graphDensityRate δ * Real.sqrt (δ / 6) / 6) * (1 / 3) := by ring
      _ ≤ (graphDensityRate δ * Real.sqrt (δ / 6) / 6) *
          ((N : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) := by
        have hrate := graphDensityRate_pos hδ
        exact mul_le_mul_of_nonneg_left hNM (by positivity)
      _ = _ := by ring
  have hrate := graphDensityRate_pos hδ
  have hOuter : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + 1) * ((bohrSet Ω (R - γ)).card : ℝ) := by
    simpa only [one_add_one_eq_two] using hband
  obtain ⟨x₀, s₀, offset, V, hV, hpair⟩ := exists_quadratic_pair_after_reslice (periodize N f)
    (fun x => hf (x.val : ℤ)) Ω J A B hJ hB hγ.le hBγ ht.le ht₄ hAt hBt
    (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 < graphDensityRate δ / 3) (by positivity)
    hσ hOuter c ξ φ hpos hJsize hξ hφ hadd hsym'
  exact ⟨Ω, φ, R₁, B, x₀, s₀, offset, V, hRlo, hRup', hB, hBA, hdim, hBu, by simpa only [one_add_one_eq_two] using hInner', hBsize, hadd, hV, hpair⟩

section FourierSmoothing

variable {M : ℕ} [NeZero M]

private noncomputable def cyclicConvolution (P Q : ZMod M → ℂ) (z : ZMod M) : ℂ :=
  ∑ x, P x * Q (z - x)

private lemma dft_cyclicConvolution (P Q : ZMod M → ℂ) (k : ZMod M) :
    ZMod.dft (cyclicConvolution P Q) k = ZMod.dft P k * ZMod.dft Q k := by
  calc
    _ = ∑ x, ∑ z, ZMod.stdAddChar (-(z * k)) * (P x * Q (z - x)) := by
      simp only [ZMod.dft_apply, cyclicConvolution, smul_eq_mul]
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by
      simp only [ZMod.dft_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Finset.mul_sum]
      symm
      refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => ?_
      change (ZMod.stdAddChar (-(x * k)) * P x) * (ZMod.stdAddChar (-(y * k)) * Q y) =
        ZMod.stdAddChar (-((x + y) * k)) * (P x * Q (x + y - x))
      rw [add_sub_cancel_left]
      have h : -((x + y) * k) = -(x * k) + -(y * k) := by ring
      rw [h, AddChar.map_add_eq_mul]
      ring

private lemma dft_conj_neg (P : ZMod M → ℂ) (k : ZMod M) :
    ZMod.dft (fun x => conj (P x)) (-k) = conj (ZMod.dft P k) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, conj_stdAddChar, mul_neg, neg_neg]

private lemma sum_sq_dft (P : ZMod M → ℂ) :
    ∑ k, ‖ZMod.dft P k‖ ^ 2 = (M : ℝ) * ∑ x, ‖P x‖ ^ 2 := by
  have h := sum_dft_mul P (fun x => conj (P x))
  simp only [dft_conj_neg, ← complex_ofReal_sq_norm, ← Complex.ofReal_sum, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

private lemma sum_sq_dft_neg (P : ZMod M → ℂ) :
    ∑ k, ‖ZMod.dft P (-k)‖ ^ 2 = (M : ℝ) * ∑ x, ‖P x‖ ^ 2 := by
  rw [← sum_sq_dft P]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)

private lemma norm_sum_convolution_mul_sq_le (U V W : ZMod M → ℂ) {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (hV : ∀ k, ‖ZMod.dft V k‖ ≤ ρ) :
    ‖∑ z, cyclicConvolution U V z * W z‖ ^ 2 ≤
      ρ ^ 2 * (∑ x, ‖U x‖ ^ 2) * ∑ z, ‖W z‖ ^ 2 := by
  let u := ZMod.dft U
  let v := ZMod.dft V
  let w := ZMod.dft W
  let L := ∑ z, cyclicConvolution U V z * W z
  have h := sum_dft_mul (cyclicConvolution U V) W
  simp_rw [dft_cyclicConvolution, mul_assoc] at h
  change (∑ k, u k * (v k * w (-k))) = (M : ℂ) * L at h
  have hc := norm_sum_mul_sq_le u (fun k => v k * w (-k))
  rw [h, norm_mul, Complex.norm_natCast, mul_pow] at hc
  have hv : (∑ k, ‖v k * w (-k)‖ ^ 2) ≤ ρ ^ 2 * ∑ k, ‖w (-k)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hV k) _) (by positivity)
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  change ‖L‖ ^ 2 ≤ _
  apply le_of_mul_le_mul_left _ (sq_pos_of_pos hM)
  calc
    _ ≤ (∑ k, ‖u k‖ ^ 2) * ∑ k, ‖v k * w (-k)‖ ^ 2 := hc
    _ ≤ (∑ k, ‖u k‖ ^ 2) * (ρ ^ 2 * ∑ k, ‖w (-k)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by
      dsimp [u, w]
      rw [sum_sq_dft, sum_sq_dft_neg]
      ring

private noncomputable def restrictComplex (A : Finset (ZMod M)) (U : ZMod M → ℂ) (x : ZMod M) : ℂ :=
  if x ∈ A then U x else 0

private lemma sum_sq_restrictComplex_le_card (A : Finset (ZMod M)) (U : ZMod M → ℂ)
    (hU : ∀ x, ‖U x‖ ≤ 1) :
    ∑ x, ‖restrictComplex A U x‖ ^ 2 ≤ (A.card : ℝ) := by
  have he : ∑ x, ‖restrictComplex A U x‖ ^ 2 = ∑ x ∈ A, ‖U x‖ ^ 2 := by
    calc
      _ = ∑ x ∈ A, ‖restrictComplex A U x‖ ^ 2 := by
        symm
        exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by simp [restrictComplex, hx])
      _ = _ := Finset.sum_congr rfl fun x hx => by simp [restrictComplex, hx]
  rw [he]
  calc
    _ ≤ ∑ _ ∈ A, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hU x) 2
    _ = _ := by simp

private lemma norm_dft_restrictComplex_le_card (A : Finset (ZMod M)) (U : ZMod M → ℂ)
    (hU : ∀ x, ‖U x‖ ≤ 1) (k : ZMod M) : ‖ZMod.dft (restrictComplex A U) k‖ ≤ (A.card : ℝ) := by
  have he : ZMod.dft (restrictComplex A U) k = ∑ x ∈ A, ZMod.stdAddChar (-(x * k)) * U x := by
    have hA : (Finset.univ.filter fun x => x ∈ A) = A := by ext x; simp
    simp only [ZMod.dft_apply, smul_eq_mul, restrictComplex, mul_ite, mul_zero, ← Finset.sum_filter, hA]
  rw [he]
  refine (norm_sum_le _ _).trans ?_
  simpa only [norm_mul, norm_stdAddChar, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] using
    (show ∑ x ∈ A, ‖U x‖ ≤ ∑ x ∈ A, (1 : ℝ) from Finset.sum_le_sum fun x _ => hU x)

end FourierSmoothing

section RieszProduct

variable {M : ℕ} [NeZero M]

private noncomputable def rieszProduct (D : Finset (ZMod M)) (ζ : ZMod M → ℂ) (t : ℝ)
    (x : ZMod M) : ℂ := ∏ a ∈ D, (1 + (t : ℂ) * ζ a * ZMod.stdAddChar (-(a * x)))

private lemma prod_stdAddChar_eq (D : Finset (ZMod M)) (g : ZMod M → ZMod M) :
    (∏ a ∈ D, ZMod.stdAddChar (g a)) = ZMod.stdAddChar (∑ a ∈ D, g a) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a D ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, AddChar.map_add_eq_mul]

private lemma sum_sq_rieszProduct (D : Finset (ZMod M)) (hD : AddDissociated (D : Set (ZMod M)))
    (ζ : ZMod M → ℂ) (hζ : ∀ a ∈ D, ‖ζ a‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ∑ x, ‖rieszProduct D ζ t x‖ ^ 2 = (M : ℝ) * (1 + t ^ 2) ^ D.card := by
  classical
  let L := D.powerset
  let σ (U : Finset (ZMod M)) := ∑ a ∈ U, a
  let c (U : Finset (ZMod M)) := ∏ a ∈ U, (t : ℂ) * ζ a
  let E := L.image σ
  let F (k : ZMod M) := ∑ U ∈ L with σ U = k, c U
  have hi : Set.InjOn σ (L : Set (Finset (ZMod M))) := by
    intro U hU V hV he
    exact hD (by exact_mod_cast Finset.mem_powerset.mp hU)
      (by exact_mod_cast Finset.mem_powerset.mp hV) he
  have hF (U : Finset (ZMod M)) (hU : U ∈ L) : F (σ U) = c U := by
    unfold F
    rw [Finset.sum_eq_single U]
    · intro V hV hne
      exact False.elim (hne (hi (Finset.mem_filter.mp hV).1 hU (Finset.mem_filter.mp hV).2))
    · simp [hU]
  have hF₀ (k : ZMod M) (hk : k ∉ E) : F k = 0 := by
    unfold F
    refine Finset.sum_eq_zero fun U hU => ?_
    exact False.elim (hk (Finset.mem_image.mpr ⟨U, (Finset.mem_filter.mp hU).1,
      (Finset.mem_filter.mp hU).2⟩))
  have hdf (x : ZMod M) : ZMod.dft F x = rieszProduct D ζ t x := by
    unfold rieszProduct
    rw [Finset.prod_one_add, ZMod.dft_apply]
    simp only [smul_eq_mul]
    calc
      _ = ∑ k : ZMod M, ∑ U ∈ L with σ U = k, ZMod.stdAddChar (-(σ U * x)) * c U := by
        refine Finset.sum_congr rfl fun k _ => ?_
        unfold F
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun U hU => by rw [(Finset.mem_filter.mp hU).2]
      _ = ∑ U ∈ L, ZMod.stdAddChar (-(σ U * x)) * c U :=
        Finset.sum_fiberwise_of_maps_to (fun U (_ : U ∈ L) => Finset.mem_univ (σ U)) _
      _ = _ := by
        refine Finset.sum_congr rfl fun U _ => ?_
        unfold c σ
        rw [Finset.prod_mul_distrib (f := fun a => (t : ℂ) * ζ a)
          (g := fun a => ZMod.stdAddChar (-(a * x))), prod_stdAddChar_eq,
          Finset.sum_neg_distrib, ← Finset.sum_mul]
        exact mul_comm _ _
  have hsum : ∑ k, ‖F k‖ ^ 2 = (1 + t ^ 2) ^ D.card := by
    calc
      _ = ∑ k ∈ E, ‖F k‖ ^ 2 := by
        symm
        exact Finset.sum_subset (Finset.subset_univ E) (fun k _ hk => by simp [hF₀ k hk])
      _ = ∑ U ∈ L, ‖F (σ U)‖ ^ 2 := Finset.sum_image hi
      _ = ∑ U ∈ L, ∏ a ∈ U, t ^ 2 := by
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [hF U hU]
        unfold c
        rw [norm_prod, ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun a ha => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht, hζ a (Finset.mem_powerset.mp hU ha),
          mul_one]
      _ = _ := by rw [← Finset.prod_one_add D, Finset.prod_const]
  simp_rw [← hdf]
  rw [sum_sq_dft, hsum]

private lemma exp_le_norm_one_add_sq {z : ℂ} (hz : ‖z‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht₈ : t ≤ 1 / 8) :
    Real.exp (2 * t * z.re - 18 * t ^ 2) ≤ ‖1 + (t : ℂ) * z‖ ^ 2 := by
  let u := t ^ 2 + 2 * t * z.re
  have hre : |z.re| ≤ 1 := (Complex.abs_re_le_norm _).trans_eq hz
  have htsq : t ^ 2 ≤ t := by nlinarith only [ht, ht₈, mul_nonneg ht (show 0 ≤ 1 - t by linarith)]
  have hu : |u| ≤ 3 * t := by
    unfold u
    calc
      _ ≤ |t ^ 2| + |2 * t * z.re| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (sq_nonneg t), abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * t)]
        have h := mul_le_mul_of_nonneg_left hre (show 0 ≤ 2 * t by positivity)
        linarith only [htsq, h]
  have hu' : -(3 * t) ≤ u := (abs_le.mp hu).1
  have hpos : 0 < 1 + u := by linarith
  have hhalf : 1 / 2 ≤ 1 + u := by linarith
  have hsq : u ^ 2 ≤ (3 * t) ^ 2 := by
    rw [← sq_abs u]
    exact pow_le_pow_left₀ (abs_nonneg _) hu _
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hrewrite : 1 - (1 + u)⁻¹ = u - u ^ 2 / (1 + u) := by field_simp; ring
  rw [hrewrite] at hlog
  have hdiv : u ^ 2 / (1 + u) ≤ 2 * u ^ 2 := by
    apply (div_le_iff₀ hpos).2
    nlinarith only [mul_nonneg (sq_nonneg u) (show 0 ≤ 1 + u - 1 / 2 by linarith)]
  have hexp : Real.exp (2 * t * z.re - 18 * t ^ 2) ≤ 1 + u := by
    apply (Real.le_log_iff_exp_le hpos).mp
    dsimp [u] at hlog hdiv hsq ⊢
    linarith only [hlog, hdiv, hsq, sq_nonneg t]
  have hnorm : ‖1 + (t : ℂ) * z‖ ^ 2 = 1 + u := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      zero_add, add_zero]
    have h : z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hz, one_pow]
    unfold u
    linear_combination t ^ 2 * h
  rwa [hnorm]

private lemma exp_le_sq_rieszProduct (D : Finset (ZMod M)) {ζ : ZMod M → ℂ}
    (hζ : ∀ a ∈ D, ‖ζ a‖ = 1) {t : ℝ} (ht : 0 ≤ t) (ht₈ : t ≤ 1 / 8) (x : ZMod M) :
    Real.exp (2 * t * (∑ a ∈ D, (ζ a * ZMod.stdAddChar (-(a * x))).re) -
      18 * t ^ 2 * (D.card : ℝ)) ≤ ‖rieszProduct D ζ t x‖ ^ 2 := by
  rw [show 2 * t * (∑ a ∈ D, (ζ a * ZMod.stdAddChar (-(a * x))).re) - 18 * t ^ 2 * (D.card : ℝ) =
      ∑ a ∈ D, (2 * t * (ζ a * ZMod.stdAddChar (-(a * x))).re - 18 * t ^ 2) by
    simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring,
    Real.exp_sum, rieszProduct, norm_prod, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun _ _ => Real.exp_nonneg _) fun a ha => ?_
  have hz : ‖ζ a * ZMod.stdAddChar (-(a * x))‖ = 1 := by
    rw [norm_mul, hζ a ha, norm_stdAddChar, mul_one]
  simpa only [mul_assoc] using exp_le_norm_one_add_sq hz ht ht₈

end RieszProduct

section LargeSpectrumDimension

variable {M : ℕ} [NeZero M]

private def spectrumRotation : Fin 4 → ℂ := ![1, -1, -Complex.I, Complex.I]

private lemma norm_spectrumRotation (i : Fin 4) : ‖spectrumRotation i‖ = 1 := by
  fin_cases i <;> simp [spectrumRotation]

private lemma exists_spectrumRotation (z : ℂ) :
    ∃ i : Fin 4, ‖z‖ / 2 ≤ (spectrumRotation i * z).re := by
  have hz := Complex.norm_le_abs_re_add_abs_im z
  rcases le_total |z.im| |z.re| with h | h
  · rcases le_total 0 z.re with hp | hn
    · rw [abs_of_nonneg hp] at h hz
      exact ⟨0, by simp [spectrumRotation]; linarith only [h, hz]⟩
    · rw [abs_of_nonpos hn] at h hz
      exact ⟨1, by simp [spectrumRotation]; linarith only [h, hz]⟩
  · rcases le_total 0 z.im with hp | hn
    · rw [abs_of_nonneg hp] at h hz
      refine ⟨2, ?_⟩
      have he : (spectrumRotation 2 * z).re = z.im := by simp [spectrumRotation, Complex.mul_re]
      rw [he]
      linarith only [h, hz]
    · rw [abs_of_nonpos hn] at h hz
      refine ⟨3, ?_⟩
      have he : (spectrumRotation 3 * z).re = - z.im := by simp [spectrumRotation, Complex.mul_re]
      rw [he]
      linarith only [h, hz]

private noncomputable def relativeSpectrum (B : Finset (ZMod M)) (V : ZMod M → ℂ) (ε : ℝ) :
    Finset (ZMod M) :=
  Finset.univ.filter (fun k => ε * (B.card : ℝ) ≤ ‖ZMod.dft (restrictComplex B V) k‖)

private lemma dissociated_relativeSpectrum_card (B : Finset (ZMod M)) (hB : B.Nonempty)
    (V : ZMod M → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (D : Finset (ZMod M)) (hD : AddDissociated (D : Set (ZMod M))) (hsub : D ⊆ relativeSpectrum B V ε) :
    ε ^ 2 * (D.card : ℝ) / 512 ≤ Real.log (8 * (M : ℝ) / (ε * (B.card : ℝ))) := by
  classical
  have hBpos : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  by_cases hDne : D.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hDne, Finset.card_empty, Nat.cast_zero, mul_zero, zero_div]
    apply Real.log_nonneg
    have hBM : (B.card : ℝ) ≤ M := by exact_mod_cast (Finset.card_le_univ B).trans_eq (ZMod.card M)
    rw [le_div_iff₀ (by positivity), one_mul]
    have h := mul_le_of_le_one_left hBpos.le hε₁
    linarith only [h, hBM, hMpos]
  have hDpos : 0 < (D.card : ℝ) := by exact_mod_cast hDne.card_pos
  let c := ZMod.dft (restrictComplex B V)
  let ζ (a : ZMod M) := align (c a)
  let F (x : ZMod M) := ∑ a ∈ D, ζ a * ZMod.stdAddChar (-(a * x))
  let X := B.filter (fun x => ε * (D.card : ℝ) / 2 ≤ ‖F x‖)
  let t := ε / 128
  have ht : 0 < t := by unfold t; positivity
  have ht₈ : t ≤ 1 / 8 := by unfold t; linarith
  have hc (a : ZMod M) (ha : a ∈ D) : ε * (B.card : ℝ) ≤ ‖c a‖ :=
    (Finset.mem_filter.mp (hsub ha)).2
  have hζ (a : ZMod M) (ha : a ∈ D) : ‖ζ a‖ = 1 := by
    have hpos := (mul_pos hε hBpos).trans_le (hc a ha)
    unfold ζ align
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self hpos.ne']
  have hdft (a : ZMod M) : c a = ∑ x ∈ B, V x * ZMod.stdAddChar (-(a * x)) := by
    unfold c
    have hB' : (Finset.univ.filter fun x => x ∈ B) = B := by ext x; simp
    simp only [ZMod.dft_apply, smul_eq_mul, restrictComplex, mul_ite, mul_zero, ← Finset.sum_filter, hB']
    exact Finset.sum_congr rfl fun x _ => by rw [mul_comm a x, mul_comm]
  have hsum : (∑ x ∈ B, V x * F x) = ∑ a ∈ D, (‖c a‖ : ℂ) := by
    unfold F
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← align_mul (c a)]
    change _ = ζ a * c a
    rw [hdft, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hmass : (ε * (B.card : ℝ)) * (D.card : ℝ) ≤ ∑ x ∈ B, ‖F x‖ := by
    calc
      _ = ∑ _ ∈ D, ε * (B.card : ℝ) := by simp; ring
      _ ≤ ∑ a ∈ D, ‖c a‖ := Finset.sum_le_sum hc
      _ = ‖∑ x ∈ B, V x * F x‖ := by
        rw [hsum, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      _ ≤ ∑ x ∈ B, ‖V x * F x‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun x _ => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hV x)
  have hF (x : ZMod M) : ‖F x‖ ≤ D.card := by
    calc
      _ ≤ ∑ a ∈ D, ‖ζ a * ZMod.stdAddChar (-(a * x))‖ := norm_sum_le _ _
      _ = ∑ _ ∈ D, (1 : ℝ) := Finset.sum_congr rfl fun a ha => by
        rw [norm_mul, hζ a ha, norm_stdAddChar, mul_one]
      _ = _ := by simp
  have hX : ε * (B.card : ℝ) / 2 ≤ (X.card : ℝ) := by
    have h := card_filter_large_terms B (fun x => ‖F x‖)
      (by positivity : 0 ≤ ε * (D.card : ℝ) / 2) (fun x _ => hF x)
    change _ ≤ (X.card : ℝ) * (D.card : ℝ) + (B.card : ℝ) * (ε * (D.card : ℝ) / 2) at h
    apply le_of_mul_le_mul_right _ hDpos
    linarith only [hmass.trans h]
  let u := (ε * t / 2 - 18 * t ^ 2) * (D.card : ℝ)
  let P (i : Fin 4) := rieszProduct D (fun a => spectrumRotation i * ζ a) t
  have hrot (i : Fin 4) (a : ZMod M) (ha : a ∈ D) :
      ‖spectrumRotation i * ζ a‖ = 1 := by rw [norm_mul, norm_spectrumRotation, hζ a ha, one_mul]
  have hpoint (x : ZMod M) (hx : x ∈ X) : Real.exp u ≤ ∑ i : Fin 4, ‖P i x‖ ^ 2 := by
    obtain ⟨i, hi⟩ := exists_spectrumRotation (F x)
    have hx' : ε * (D.card : ℝ) / 2 ≤ ‖F x‖ := (Finset.mem_filter.mp hx).2
    have hlinear : ε * (D.card : ℝ) / 4 ≤ (spectrumRotation i * F x).re := by linarith only [hx', hi]
    have hsumRe : (spectrumRotation i * F x).re =
        ∑ a ∈ D, ((spectrumRotation i * ζ a) * ZMod.stdAddChar (-(a * x))).re := by
      simp only [F, Finset.mul_sum, Complex.re_sum, mul_assoc]
    rw [hsumRe] at hlinear
    calc
      _ ≤ Real.exp (2 * t * (∑ a ∈ D, ((spectrumRotation i * ζ a) * ZMod.stdAddChar (-(a * x))).re) -
          18 * t ^ 2 * (D.card : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hlinear (show 0 ≤ 2 * t by positivity)
        unfold u
        linarith only [h]
      _ ≤ ‖P i x‖ ^ 2 := exp_le_sq_rieszProduct D (hrot i) ht.le ht₈ x
      _ ≤ _ := Finset.single_le_sum (f := fun i : Fin 4 => ‖P i x‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hcSum : (ε * (B.card : ℝ) / 2) * Real.exp u ≤ 4 * (M : ℝ) * Real.exp (t ^ 2 * (D.card : ℝ)) := by
    calc
      _ ≤ (X.card : ℝ) * Real.exp u := mul_le_mul_of_nonneg_right hX (Real.exp_nonneg _)
      _ = ∑ _ ∈ X, Real.exp u := by simp
      _ ≤ ∑ x ∈ X, ∑ i : Fin 4, ‖P i x‖ ^ 2 := Finset.sum_le_sum hpoint
      _ ≤ ∑ x : ZMod M, ∑ i : Fin 4, ‖P i x‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X) (fun _ _ _ => by positivity)
      _ = 4 * (M : ℝ) * (1 + t ^ 2) ^ D.card := by
        rw [Finset.sum_comm]
        simp only [P, sum_sq_rieszProduct D hD _ (hrot _) ht.le, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_comm (t ^ 2), Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by positivity)
          (by simpa only [add_comm] using Real.add_one_le_exp (t ^ 2)) _
  apply (Real.le_log_iff_exp_le (by positivity)).2
  rw [le_div_iff₀ (by positivity)]
  apply le_of_mul_le_mul_right _ (Real.exp_pos (t ^ 2 * (D.card : ℝ)))
  calc
    _ = 2 * ((ε * (B.card : ℝ) / 2) *
        (Real.exp (ε ^ 2 * (D.card : ℝ) / 512) * Real.exp (t ^ 2 * (D.card : ℝ)))) := by ring
    _ ≤ 2 * ((ε * (B.card : ℝ) / 2) * Real.exp u) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← Real.exp_add, Real.exp_le_exp]
      dsimp [u, t]
      nlinarith only [mul_nonneg (sq_nonneg ε) (show 0 ≤ (D.card : ℝ) by positivity)]
    _ ≤ _ := by linarith only [hcSum]

private lemma exists_small_span_relativeSpectrum (B : Finset (ZMod M)) (hB : B.Nonempty)
    (V : ZMod M → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ Λ : Finset (ZMod M), Λ ⊆ relativeSpectrum B V ε ∧
      Λ.card ≤ ⌈512 * Real.log (8 * (M : ℝ) / (ε * (B.card : ℝ))) / ε ^ 2⌉₊ ∧
      relativeSpectrum B V ε ⊆ Λ.addSpan := by
  apply Finset.exists_subset_addSpan_card_le_of_forall_addDissociated
  intro D hsub hD
  have h := dissociated_relativeSpectrum_card B hB V hV hε hε₁ D hD hsub
  have h' : (D.card : ℝ) ≤ 512 * Real.log (8 * (M : ℝ) / (ε * (B.card : ℝ))) / ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    linarith only [h]
  exact_mod_cast h'.trans (Nat.le_ceil _)

end LargeSpectrumDimension

section SpectrumSmoothing

variable {M : ℕ} [NeZero M]

private lemma norm_stdAddChar_finset_sum_sub_one_le {I : Type*} (D : Finset I) (f : I → ZMod M) :
    ‖ZMod.stdAddChar (∑ a ∈ D, f a) - 1‖ ≤ ∑ a ∈ D, ‖ZMod.stdAddChar (f a) - 1‖ := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a D ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h := norm_stdAddChar_add_sub_le (f a) (∑ b ∈ D, f b) 0 0
    simp only [zero_add, AddChar.map_zero_eq_one] at h
    exact h.trans (add_le_add_right ih _)

private lemma norm_stdAddChar_of_mem_addSpan (Λ : Finset (ZMod M)) {k d : ZMod M}
    (hk : k ∈ Λ.addSpan) {r : ℝ} (hr : 0 ≤ r)
    (hd : ∀ a ∈ Λ, ‖ZMod.stdAddChar (a * d) - 1‖ ≤ r) :
    ‖ZMod.stdAddChar (k * d) - 1‖ ≤ (Λ.card : ℝ) * r := by
  obtain ⟨ε, hε, rfl⟩ := Finset.mem_addSpan.mp hk
  rw [Finset.sum_mul]
  refine (norm_stdAddChar_finset_sum_sub_one_le Λ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ Λ, r := by
      refine Finset.sum_le_sum fun a ha => ?_
      rcases hε a with h | h | h
      · simpa [h, norm_stdAddChar_neg_sub_one] using hd a ha
      · simp [h, hr]
      · simpa [h] using hd a ha
    _ = _ := by simp

private noncomputable def uniformComplex (D : Finset (ZMod M)) : ZMod M → ℂ :=
  restrictComplex D (fun _ => (D.card : ℂ)⁻¹)

private lemma dft_uniformComplex (D : Finset (ZMod M)) (k : ZMod M) :
    ZMod.dft (uniformComplex D) k = (D.card : ℂ)⁻¹ * ∑ d ∈ D, ZMod.stdAddChar (-(d * k)) := by
  have hD : (Finset.univ.filter fun x => x ∈ D) = D := by ext x; simp
  simp only [ZMod.dft_apply, uniformComplex, restrictComplex, smul_eq_mul, mul_ite, mul_zero,
    ← Finset.sum_filter, hD, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

private lemma norm_dft_uniformComplex_le_one (D : Finset (ZMod M)) (hD : D.Nonempty) (k : ZMod M) :
    ‖ZMod.dft (uniformComplex D) k‖ ≤ 1 := by
  have hx : (D.card : ℝ) ≠ 0 := by exact_mod_cast hD.card_ne_zero
  rw [dft_uniformComplex, norm_mul, norm_inv, Complex.norm_natCast]
  have h := norm_sum_le D (fun d => ZMod.stdAddChar (-(d * k)))
  simp only [norm_stdAddChar, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  calc
    _ ≤ (D.card : ℝ)⁻¹ * (D.card : ℝ) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := inv_mul_cancel₀ hx

private lemma norm_dft_uniformComplex_sub_one_le (D : Finset (ZMod M)) (hD : D.Nonempty)
    (k : ZMod M) {ε : ℝ} (hε : ∀ x ∈ D, ‖ZMod.stdAddChar (k * x) - 1‖ ≤ ε) :
    ‖ZMod.dft (uniformComplex D) k - 1‖ ≤ ε := by
  have hx : (D.card : ℝ) ≠ 0 := by exact_mod_cast hD.card_ne_zero
  have hx' : (D.card : ℂ) ≠ 0 := by exact_mod_cast hD.card_ne_zero
  have h1 : (D.card : ℂ)⁻¹ * ∑ _ ∈ D, (1 : ℂ) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hx']
  rw [dft_uniformComplex, ← h1, ← mul_sub, ← Finset.sum_sub_distrib,
    norm_mul, norm_inv, Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  calc
    _ ≤ (D.card : ℝ)⁻¹ * ∑ _ ∈ D, ε := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun d hd => ?_) (by positivity)
      rw [norm_stdAddChar_neg_sub_one, mul_comm]
      exact hε d hd
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]

private lemma exists_smoothing_bohr (Ω B : Finset (ZMod M)) (hB : B.Nonempty)
    (V : ZMod M → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hε₁ : ε ≤ 1) :
    ∃ Λ : Finset (ZMod M),
      Λ.card ≤ ⌈512 * Real.log (8 * (M : ℝ) / (ε * (B.card : ℝ))) / ε ^ 2⌉₊ ∧
      let r' := min r (ε / ((Λ.card : ℝ) + 1))
      let D := bohrSet (Ω ∪ Λ) r'
      0 < r' ∧ D.Nonempty ∧ D ⊆ bohrSet Ω r ∧
      ∀ k, ‖ZMod.dft (restrictComplex B V) k -
          ZMod.dft (restrictComplex B V) k * ZMod.dft (uniformComplex D) k‖ ≤ 2 * ε * (B.card : ℝ) := by
  obtain ⟨Λ, _, hΛ, hspan⟩ := exists_small_span_relativeSpectrum B hB V hV hε hε₁
  let r' := min r (ε / ((Λ.card : ℝ) + 1))
  let D := bohrSet (Ω ∪ Λ) r'
  have hr' : 0 < r' := lt_min hr (by positivity)
  have hD := bohrSet_nonempty (Ω ∪ Λ) hr'.le
  refine ⟨Λ, hΛ, hr', hD, ?_, ?_⟩
  · intro d hd
    exact mem_bohrSet.mpr (fun a ha => ((mem_bohrSet.mp hd) a (Finset.mem_union_left _ ha)).trans (min_le_left _ _))
  · intro k
    let c := ZMod.dft (restrictComplex B V) k
    let u := ZMod.dft (uniformComplex D) k
    change ‖c - c * u‖ ≤ 2 * ε * (B.card : ℝ)
    rw [show c - c * u = c * (1 - u) by ring, norm_mul]
    by_cases hk : k ∈ relativeSpectrum B V ε
    · have hu : ‖u - 1‖ ≤ ε := by
        apply norm_dft_uniformComplex_sub_one_le D hD k
        intro d hd
        apply (norm_stdAddChar_of_mem_addSpan Λ (hspan hk) hr'.le
          (fun a ha => (mem_bohrSet.mp hd) a (Finset.mem_union_right _ ha))).trans
        calc
          _ ≤ ((Λ.card : ℝ) + 1) * (ε / ((Λ.card : ℝ) + 1)) :=
            mul_le_mul (by linarith) (min_le_right _ _) hr'.le (by positivity)
          _ = _ := by field_simp
      rw [norm_sub_rev]
      have hc := norm_dft_restrictComplex_le_card B V hV k
      refine (mul_le_mul hc hu (norm_nonneg _) (by positivity)).trans ?_
      nlinarith only [mul_nonneg hε.le (show 0 ≤ (B.card : ℝ) by positivity)]
    · have hc : ‖c‖ ≤ ε * (B.card : ℝ) := by
        by_contra! h
        exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.le⟩)
      have hu : ‖1 - u‖ ≤ 2 := by
        calc
          _ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
          _ ≤ _ := by rw [norm_one]; linarith only [norm_dft_uniformComplex_le_one D hD k]
      exact (mul_le_mul hc hu (norm_nonneg _) (by positivity)).trans_eq (by ring)

end SpectrumSmoothing

section SmoothedCorrelation

variable {M : ℕ} [NeZero M]

private lemma sum_cyclicConvolution_mul (U V W : ZMod M → ℂ) :
    (∑ z, cyclicConvolution U V z * W z) = ∑ x, ∑ y, U x * V y * W (x + y) := by
  unfold cyclicConvolution
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  symm
  refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => ?_
  change U x * V y * W (x + y) = U x * V (x + y - x) * W (x + y)
  rw [add_sub_cancel_left]

private lemma sum_restrictComplex_mul (A : Finset (ZMod M)) (U F : ZMod M → ℂ) :
    (∑ x, restrictComplex A U x * F x) = ∑ x ∈ A, U x * F x := by
  have hA : (Finset.univ.filter fun x => x ∈ A) = A := by ext x; simp
  simp only [restrictComplex, ite_mul, zero_mul, ← Finset.sum_filter, hA]

private lemma sum_triple_cyclicConvolution_mul (U V L W : ZMod M → ℂ) :
    (∑ z, cyclicConvolution U (cyclicConvolution V L) z * W z) =
      ∑ x, ∑ y, ∑ d, U x * V y * L d * W (x + y + d) := by
  rw [sum_cyclicConvolution_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  calc
    _ = ∑ w, cyclicConvolution V L w * (U x * W (x + w)) :=
      Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ y, ∑ d, V y * L d * (U x * W (x + (y + d))) :=
      sum_cyclicConvolution_mul _ _ _
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [← add_assoc]; ring

private lemma norm_smoothed_correlation_error (A B D : Finset (ZMod M)) (_hD : D.Nonempty)
    (U V W : ZMod M → ℂ) (hU : ∀ x, ‖U x‖ ≤ 1) (hW : ∀ x, ‖W x‖ ≤ 1)
    (hSupport : A + B ⊆ A + B + D)
    (hE : (A + B + D).card ≤ 2 * A.card) {ε : ℝ} (hε : 0 ≤ ε)
    (hF : ∀ k, ‖ZMod.dft (restrictComplex B V) k -
          ZMod.dft (restrictComplex B V) k * ZMod.dft (uniformComplex D) k‖ ≤ 2 * ε * (B.card : ℝ)) :
    let Avg := fun z => (D.card : ℂ)⁻¹ * ∑ d ∈ D, W (z + d)
    ‖(∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y)) -
      ∑ y ∈ B, ∑ x ∈ A, U x * V y * Avg (x + y)‖ ≤ 4 * ε * (A.card : ℝ) * (B.card : ℝ) := by
  dsimp only
  let E := A + B + D
  let U₀ := restrictComplex A U
  let V₀ := restrictComplex B V
  let W₀ := restrictComplex E W
  let μ := uniformComplex D
  let F := V₀ - cyclicConvolution V₀ μ
  let Avg (z : ZMod M) := (D.card : ℂ)⁻¹ * ∑ d ∈ D, W (z + d)
  let S := ∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y)
  let T := ∑ y ∈ B, ∑ x ∈ A, U x * V y * Avg (x + y)
  have hF' (k : ZMod M) : ‖ZMod.dft F k‖ ≤ 2 * ε * (B.card : ℝ) := by
    unfold F
    rw [map_sub, Pi.sub_apply, dft_cyclicConvolution]
    exact hF k
  have h₁ : (∑ z, cyclicConvolution U₀ V₀ z * W₀ z) = S := by
    rw [sum_cyclicConvolution_mul]
    unfold S
    conv_rhs => rw [Finset.sum_comm]
    calc
      _ = ∑ x ∈ A, ∑ y, U x * V₀ y * W₀ (x + y) := by
        simp only [mul_assoc, ← Finset.mul_sum, U₀, sum_restrictComplex_mul]
      _ = ∑ x ∈ A, ∑ y ∈ B, U x * V y * W₀ (x + y) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [mul_assoc, ← Finset.mul_sum, V₀, sum_restrictComplex_mul]
      _ = _ := by
        refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
        have h : x + y ∈ E := hSupport (Finset.add_mem_add hx hy)
        simp [W₀, restrictComplex, h]
  have h₂ : (∑ z, cyclicConvolution U₀ (cyclicConvolution V₀ μ) z * W₀ z) = T := by
    rw [sum_triple_cyclicConvolution_mul]
    unfold T
    conv_rhs => rw [Finset.sum_comm]
    calc
      _ = ∑ x ∈ A, ∑ y, ∑ d, U x * V₀ y * μ d * W₀ (x + y + d) := by
        simp only [mul_assoc, ← Finset.mul_sum, U₀, sum_restrictComplex_mul]
      _ = ∑ x ∈ A, ∑ y ∈ B, ∑ d, U x * V y * μ d * W₀ (x + y + d) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [mul_assoc, ← Finset.mul_sum, V₀, sum_restrictComplex_mul]
      _ = _ := by
        refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
        simp only [mul_assoc, ← Finset.mul_sum, μ, uniformComplex, sum_restrictComplex_mul, Avg]
        have hcore : (∑ d ∈ D, W₀ (x + y + d)) = ∑ d ∈ D, W (x + y + d) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          have h : x + y + d ∈ E := Finset.add_mem_add (Finset.add_mem_add hx hy) hd
          simp [W₀, restrictComplex, h]
        rw [hcore]
  have heq : (∑ z, cyclicConvolution U₀ F z * W₀ z) = S - T := by
    rw [← h₁, ← h₂, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold F cyclicConvolution
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_mul]
  have hc := norm_sum_convolution_mul_sq_le U₀ F W₀
    (by positivity : 0 ≤ 2 * ε * (B.card : ℝ)) hF'
  have hb := sum_sq_restrictComplex_le_card A U hU
  have hw := sum_sq_restrictComplex_le_card E W hW
  have hE' : (E.card : ℝ) ≤ 2 * (A.card : ℝ) := by exact_mod_cast hE
  have hins : ‖S - T‖ ^ 2 ≤ (4 * ε * (A.card : ℝ) * (B.card : ℝ)) ^ 2 := by
    rw [heq] at hc
    calc
      _ ≤ (2 * ε * (B.card : ℝ)) ^ 2 * (∑ x, ‖U₀ x‖ ^ 2) * ∑ z, ‖W₀ z‖ ^ 2 := hc
      _ ≤ (2 * ε * (B.card : ℝ)) ^ 2 * (A.card : ℝ) * (2 * (A.card : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) (hw.trans hE') (by positivity) (by positivity)
      _ ≤ _ := by nlinarith only [sq_nonneg (ε * (A.card : ℝ) * (B.card : ℝ))]
  change ‖S - T‖ ≤ _
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hins

private lemma exists_large_smoothed_mean (A B D : Finset (ZMod M))
    (hA : A.Nonempty) (hB : B.Nonempty) (hD : D.Nonempty)
    (U V W : ZMod M → ℂ) (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ x, ‖V x‖ ≤ 1) (hW : ∀ x, ‖W x‖ ≤ 1)
    (hSupport : A + B ⊆ A + B + D) (hE : (A + B + D).card ≤ 2 * A.card)
    {σ ε : ℝ} (hε : 0 ≤ ε) (hεsmall : 8 * ε ≤ σ)
    (hF : ∀ k, ‖ZMod.dft (restrictComplex B V) k -
          ZMod.dft (restrictComplex B V) k * ZMod.dft (uniformComplex D) k‖ ≤ 2 * ε * (B.card : ℝ))
    (hS : σ * (A.card : ℝ) * (B.card : ℝ) ≤ ‖∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y)‖) :
    ∃ z ∈ A + B, σ / 2 * (D.card : ℝ) ≤ ‖∑ d ∈ D, W (z + d)‖ := by
  let Avg (z : ZMod M) := (D.card : ℂ)⁻¹ * ∑ d ∈ D, W (z + d)
  let S := ∑ y ∈ B, ∑ x ∈ A, U x * V y * W (x + y)
  let T := ∑ y ∈ B, ∑ x ∈ A, U x * V y * Avg (x + y)
  have he := norm_smoothed_correlation_error A B D hD U V W hU hW hSupport hE hε hF
  change ‖S - T‖ ≤ 4 * ε * (A.card : ℝ) * (B.card : ℝ) at he
  have h := norm_add_le (S - T) T
  rw [sub_add_cancel] at h
  have hε' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (show 4 * ε ≤ σ / 2 by linarith only [hεsmall]) (by positivity : 0 ≤ (A.card : ℝ)))
      (by positivity : 0 ≤ (B.card : ℝ))
  have hT : σ / 2 * (A.card : ℝ) * (B.card : ℝ) ≤ ‖T‖ := by
    change _ ≤ ‖S‖ at hS
    linarith only [hS, he, h, hε']
  have hAB : (A + B).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact ⟨a + b, Finset.add_mem_add ha hb⟩
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (A + B) (fun z => ‖Avg z‖) hAB
  have ht : ‖T‖ ≤ (A.card : ℝ) * (B.card : ℝ) * ‖Avg z‖ := by
    unfold T
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ B, ∑ _ ∈ A, ‖Avg z‖ := by
        refine Finset.sum_le_sum fun y hy => (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun x hx => ?_
        rw [norm_mul, norm_mul]
        have hp : ‖U x‖ * ‖V y‖ ≤ 1 := by
          simpa only [one_mul] using mul_le_mul (hU x) (hV y) (norm_nonneg _) zero_le_one
        exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans (hmax _ (Finset.add_mem_add hx hy))
      _ = _ := by simp; ring
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hBpos : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hav : σ / 2 ≤ ‖Avg z‖ := by
    refine le_of_mul_le_mul_right ?_ (mul_pos hApos hBpos)
    simpa only [mul_assoc, mul_comm (‖Avg z‖)] using hT.trans ht
  have hDpos : 0 < (D.card : ℝ) := by exact_mod_cast hD.card_pos
  refine ⟨z, hz, ?_⟩
  dsimp [Avg] at hav
  rw [norm_mul, norm_inv, Complex.norm_natCast, ← div_eq_inv_mul] at hav
  exact (le_div_iff₀ hDpos).mp hav

end SmoothedCorrelation

private def LocalQuadraticCorrelationStructure (N : ℕ) (δ : ℝ) (m k : ℕ) (f : ℤ → ℝ) : Prop :=
  ∃ Ω Λ : Finset (ZMod (2 * N + 1)), ∃ φ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
    ∃ b : ℕ, ∃ x₀ z : ZMod (2 * N + 1),
    let n := 15 * Ω.card + 1
    let t : ℝ := 1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))
    let u := (t / 2) / (2 * (n : ℝ))
    let ε := quadraticPairRate δ / 8
    let r := min (u / 2) (ε / ((Λ.card : ℝ) + 1))
    let D := bohrSet (Ω ∪ Λ) r
    0 < r ∧ D.Nonempty ∧ 0 < b ∧ b ≤ 2 * N + 1 ∧
    (Ω.card : ℝ) * graphDensityRate δ ^ 2 ≤ 18 ∧
    2 * N + 1 ≤ 32768 ^ (((m * k * n ^ 4).log2 + 11) * Ω.card) * (4 * m * b) ∧
    Λ.card ≤ ⌈512 * Real.log (8 * ((2 * N + 1 : ℕ) : ℝ) / (ε * (b : ℝ))) / ε ^ 2⌉₊ ∧
    z ∈ bohrSet Ω (t + u / 2) ∧
    (∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b) ∧
    quadraticPairRate δ / 2 * (D.card : ℝ) ≤
      ‖∑ d ∈ D, (periodize N f (x₀ + (z + d)) : ℂ) * ZMod.stdAddChar (-localQuadratic φ (z + d))‖

private lemma localQuadraticCorrelation_of_pair {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {m k : ℕ} (hk : 0 < k) {f : ℤ → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (hpair : QuadraticPairStructure N δ m k f) :
    LocalQuadraticCorrelationStructure N δ m k f := by
  obtain ⟨Ω, φ, R, B, x₀, s₀, offset, V, hR, hRhi, hB, _, hdim, hBu, hband, hBsize, hadd, hV, hL⟩ := hpair
  let n := 15 * Ω.card + 1
  let t : ℝ := 1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))
  let u := (t / 2) / (2 * (n : ℝ))
  let A := bohrSet Ω R
  let q := localQuadratic φ
  let g := periodize N f
  let U (x : ZMod (2 * N + 1)) := (g (x₀ + x) : ℂ) * ZMod.stdAddChar (q x - x * offset)
  let W (z : ZMod (2 * N + 1)) := (g (x₀ + s₀ + z) : ℂ) * ZMod.stdAddChar (-q z)
  let ε := quadraticPairRate δ / 8
  have hε : 0 < ε := by
    have h := quadraticPairRate_pos hδ
    unfold ε
    positivity
  have hε₁ : ε ≤ 1 := by
    have h : quadraticPairRate δ ≤ 1 := min_le_left _ _
    unfold ε
    linarith
  have ht : 0 < t := by unfold t; positivity
  have hu : 0 < u := by unfold u; positivity
  have hR₀ : 0 ≤ R := by
    change t / 2 ≤ R at hR
    linarith only [ht, hR]
  have hg (x : ZMod (2 * N + 1)) : ‖(g x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, g, periodize] using hf (x.val : ℤ)
  have hU (x : ZMod (2 * N + 1)) : ‖U x‖ ≤ 1 := by
    simpa only [U, norm_mul, norm_stdAddChar, mul_one] using hg (x₀ + x)
  have hW (z : ZMod (2 * N + 1)) : ‖W z‖ ≤ 1 := by
    simpa only [W, norm_mul, norm_stdAddChar, mul_one] using hg (x₀ + s₀ + z)
  obtain ⟨Λ, hΛ, hr, hD, hDu, hFS⟩ := exists_smoothing_bohr Ω B hB V hV
    (show 0 < u / 2 from half_pos hu) hε hε₁
  let r := min (u / 2) (ε / ((Λ.card : ℝ) + 1))
  let D := bohrSet (Ω ∪ Λ) r
  have hD₀ : (0 : ZMod (2 * N + 1)) ∈ D := mem_bohrSet.mpr (fun a _ => by
    simpa only [mul_zero, AddChar.map_zero_eq_one, sub_self, norm_zero] using (show 0 ≤ r from hr.le))
  have hSupport : A + B ⊆ A + B + D := by
    intro x hx
    simpa only [add_zero] using Finset.add_mem_add hx hD₀
  have hcard : (A + B + D).card ≤ 2 * A.card := by
    have hsub : A + B + D ⊆ A + bohrSet Ω u := by
      intro x hx
      obtain ⟨ab, hab, d, hd, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hab
      rw [add_assoc]
      apply Finset.add_mem_add ha
      exact bohrSet_mono (by linarith only : u / 2 + u / 2 ≤ u) (add_mem_bohrSet (hBu hb) (hDu hd))
    have h := (regular_bohr_add_sub_card Ω hu.le (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [one_add_one_eq_two] using hband)).1
    have h₂ : ((A + bohrSet Ω u).card : ℝ) ≤ (2 : ℝ) * (A.card : ℝ) := by
      simpa only [one_add_one_eq_two] using h
    exact (Finset.card_le_card hsub).trans (by exact_mod_cast h₂)
  have hεsmall : 8 * ε ≤ quadraticPairRate δ := by unfold ε; linarith
  obtain ⟨z, hz, hcorr⟩ := exists_large_smoothed_mean A B D (bohrSet_nonempty Ω hR₀) hB hD U V W
    hU hV hW hSupport hcard hε.le hεsmall hFS hL
  have hz' : z ∈ bohrSet Ω (t + u / 2) := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    exact bohrSet_mono (by linarith only [hRhi]) (add_mem_bohrSet ha (hBu hb))
  have hBM : B.card ≤ 2 * N + 1 :=
    (Finset.card_le_univ B).trans_eq (ZMod.card (2 * N + 1))
  exact ⟨Ω, Λ, φ, B.card, x₀ + s₀, z, hr, hD, hB.card_pos, hBM, hdim, hBsize, hΛ, hz', hadd, hcorr⟩

private noncomputable def quadraticPairParameters (δ : ℝ) : ℕ × ℕ :=
  let v := skewCorrelationRate δ ^ 4 / 64
  let m := ⌈8 / v⌉₊
  let prefactor := 8 * (m.factorial : ℝ) * (m : ℝ) * 2 ^ m
  let ε := quadraticPairRate δ / prefactor
  let η := v / (12 * (m : ℝ)) * ε / 8
  (m, ⌈1 / η⌉₊)

private lemma quadraticPair_of_local_frequency {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) {f : ℤ → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (hstructure : RegularLocalFrequencyStructure N δ 1 1 f) :
    QuadraticPairStructure N δ (quadraticPairParameters δ).1 (quadraticPairParameters δ).2 f := by
  let v := skewCorrelationRate δ ^ 4 / 64
  let m := ⌈8 / v⌉₊
  let A := 8 * (m.factorial : ℝ) * (m : ℝ) * 2 ^ m
  let ε := quadraticPairRate δ / A
  let gap := v / (12 * (m : ℝ))
  let η := gap * ε / 8
  let k := ⌈1 / η⌉₊
  change QuadraticPairStructure N δ m k f
  have hv : 0 < v := by
    have hq := skewCorrelationRate_pos hδ
    unfold v
    positivity
  have hτ : 0 < quadraticPairRate δ := quadraticPairRate_pos hδ
  have hτ₁ : quadraticPairRate δ ≤ 1 := min_le_left _ _
  have hm : (8 : ℝ) ≤ (m : ℝ) * v := (div_le_iff₀ hv).mp (Nat.le_ceil _)
  have hm' : 0 < (m : ℝ) := (by positivity : 0 < 8 / v).trans_le (Nat.le_ceil _)
  have hm₁ : 1 ≤ m := by
    have hp : 0 < m := by exact_mod_cast hm'
    omega
  have hApos : 0 < A := by unfold A; positivity
  have hA₁ : 1 ≤ A := by
    have hf₁ : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hm₁r : (1 : ℝ) ≤ m := by exact_mod_cast hm₁
    unfold A
    calc
      _ = (1 : ℝ) * 1 * 1 * 1 := by norm_num
      _ ≤ _ := by
        have hp : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
        gcongr; norm_num
  have hε : 0 < ε := div_pos hτ hApos
  have hε₁ : ε ≤ 1 := div_le_one_of_le₀ (hτ₁.trans hA₁) hApos.le
  have hη : 0 < η := by unfold η gap; positivity
  have hk : (1 : ℝ) ≤ (k : ℝ) * η := (div_le_iff₀ hη).mp (Nat.le_ceil _)
  have hsmall : (m.factorial : ℝ) * ((m : ℝ) * ε * 2 ^ m) ≤ 1 / 2 := by
    have he : (m.factorial : ℝ) * ((m : ℝ) * ε * 2 ^ m) = quadraticPairRate δ / 8 := by
      have h : A * ε = quadraticPairRate δ := by unfold ε; field_simp [hApos.ne']
      unfold A at h
      linarith only [show (8 * (m.factorial : ℝ) * (m : ℝ) * 2 ^ m) * ε =
        8 * ((m.factorial : ℝ) * ((m : ℝ) * ε * 2 ^ m)) by ring, h]
    linarith only [he, hτ₁]
  have hpert : (8 * η) ^ 2 ≤ gap ^ 2 * ε := by
    have hεsq : ε ^ 2 ≤ ε := by nlinarith only [mul_nonneg hε.le (sub_nonneg.mpr hε₁)]
    calc
      _ = gap ^ 2 * ε ^ 2 := by unfold η; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hεsq (sq_nonneg _)
  have hphase : 8 * (m.factorial : ℝ) * (m : ℝ) * ε * 2 ^ m ≤ quadraticPairRate δ := by
    calc
      _ = A * ε := by unfold A; ring
      _ = quadraticPairRate δ := by unfold ε; field_simp [hApos.ne']
      _ ≤ _ := le_rfl
  exact quadraticPair_of_regular_structure hN hδ hf hstructure m hm hε.le hε₁ hη hsmall hpert hphase k hk

private lemma graphDensityRate_le_one {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    graphDensityRate δ ≤ 1 := by
  have hbase : graphRate δ ≤ 1 := by
    unfold graphRate
    have h := pow_le_one₀ (show 0 ≤ δ / 6 by positivity) (show δ / 6 ≤ 1 by linarith) (n := 6)
    norm_num at *
    linarith
  have hratio : 0 ≤ differenceRatioBound δ ^ 13 := by unfold differenceRatioBound graphRate; positivity
  unfold graphDensityRate
  rw [div_le_iff₀ (by positivity), one_mul]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul hbase hδ₁ hδ.le zero_le_one
    _ ≤ 48 * (2 * (differenceRatioBound δ ^ 13 + 1)) ^ 30 := by
      have h : (1 : ℝ) ≤ 2 * (differenceRatioBound δ ^ 13 + 1) := by
        linarith only [hratio]
      have hp : (1 : ℝ) ≤ (2 * (differenceRatioBound δ ^ 13 + 1)) ^ 30 := one_le_pow₀ h
      linarith only [hp]

private lemma sqrt_div_six_ge_linear {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    δ * Real.sqrt (1 / 6) ≤ Real.sqrt (δ / 6) := by
  have h : δ ≤ Real.sqrt δ := by
    apply (Real.le_sqrt hδ.le hδ.le).mpr
    nlinarith only [mul_nonneg hδ.le (show 0 ≤ 1 - δ by linarith)]
  rw [show δ / 6 = δ * (1 / 6) by ring, Real.sqrt_mul hδ.le]
  exact mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)

private lemma quadraticPairRate_ge_monomial {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    quadraticPairRate 1 * δ ^ 23408 ≤ quadraticPairRate δ := by
  let a := quadraticPairRate 1
  have ha := quadraticPairRate_pos (by norm_num : (0 : ℝ) < 1)
  have ha₁ : a ≤ 1 := min_le_left _ _
  have hb : a ≤ graphDensityRate 1 * Real.sqrt (1 / 6) / 36 := min_le_right _ _
  refine le_min ?_ ?_
  · exact (mul_le_of_le_one_right ha.le (pow_le_one₀ hδ.le hδ₁)).trans ha₁
  · calc
      _ ≤ (graphDensityRate 1 * Real.sqrt (1 / 6) / 36) * δ ^ 23408 :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ = (graphDensityRate 1 * δ ^ 23407) * (δ * Real.sqrt (1 / 6)) / 36 := by
        rw [show (23408 : ℕ) = 23407 + 1 by decide, pow_succ]
        ring
      _ ≤ _ := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul (graphDensityRate_ge_monomial hδ hδ₁) (sqrt_div_six_ge_linear hδ hδ₁)
            (by positivity) (graphDensityRate_pos hδ).le) (by norm_num)

private lemma skew_variance_ge_monomial {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (quadraticPairRate 1 ^ 8 / 64) * δ ^ 187264 ≤ skewCorrelationRate δ ^ 4 / 64 := by
  have hτ : quadraticPairRate δ ≤ graphDensityRate δ * Real.sqrt (δ / 6) / 36 := min_le_right _ _
  have hlow := (quadraticPairRate_ge_monomial hδ hδ₁).trans hτ
  have ha := quadraticPairRate_pos (by norm_num : (0 : ℝ) < 1)
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 64)
  have h := pow_le_pow_left₀ (show 0 ≤ quadraticPairRate 1 * δ ^ 23408 by positivity) hlow 8
  rw [mul_pow, ← pow_mul] at h
  simpa only [skewCorrelationRate, ← pow_mul] using h

private lemma log_quadraticPair_band_param {v τ : ℝ} (hv : 0 < v) (hv₁ : v ≤ 1)
    (hτ : 0 < τ) (hτ₁ : τ ≤ 1) :
    let m := ⌈8 / v⌉₊
    let ε := τ / (8 * (m.factorial : ℝ) * (m : ℝ) * 2 ^ m)
    let η := v / (12 * (m : ℝ)) * ε / 8
    let k := ⌈1 / η⌉₊
    0 < k ∧ Real.log (k : ℝ) ≤ 1536 + v⁻¹ + τ⁻¹ + 4 * ((m : ℝ) + 1) ^ 2 := by
  dsimp only
  let m := ⌈8 / v⌉₊
  let ε := τ / (8 * (m.factorial : ℝ) * (m : ℝ) * 2 ^ m)
  let η := v / (12 * (m : ℝ)) * ε / 8
  let k := ⌈1 / η⌉₊
  have hm : 0 < (m : ℝ) := (by positivity : 0 < 8 / v).trans_le (Nat.le_ceil _)
  have hm₁ : (1 : ℝ) ≤ m := by
    have hNat : 0 < m := by exact_mod_cast hm
    exact_mod_cast hNat
  have hfac : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hp : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hε : 0 < ε := by unfold ε; positivity
  have hη : 0 < η := by unfold η; positivity
  have hk : 0 < (k : ℝ) := (by positivity : 0 < 1 / η).trans_le (Nat.le_ceil _)
  change 0 < k ∧ Real.log (k : ℝ) ≤ _
  refine ⟨(by exact_mod_cast hk), ?_⟩
  have hf : 1 / η = 768 * v⁻¹ * τ⁻¹ * ((m : ℝ) ^ 2 * (m.factorial : ℝ) * 2 ^ m) := by
    unfold η ε
    field_simp
    ring
  have hv' : 1 ≤ v⁻¹ := (one_le_inv₀ hv).2 hv₁
  have hτ' : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).2 hτ₁
  have hηinv : 1 ≤ 1 / η := by
    rw [hf]
    have hm₂ : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hm₁
    calc
      _ = (1 : ℝ) * 1 * 1 * (1 * 1 * 1) := by norm_num
      _ ≤ _ := by gcongr; norm_num
  have hK : (k : ℝ) ≤ 1536 * v⁻¹ * τ⁻¹ * ((m : ℝ) ^ 2 * (m.factorial : ℝ) * 2 ^ m) := by
    calc
      _ ≤ 1 / η + 1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / η)).le
      _ ≤ 2 * (1 / η) := by linarith only [hηinv]
      _ = _ := by rw [hf]; ring
  have hLog := Real.log_le_log hk hK
  have hFlog : Real.log (m.factorial : ℝ) ≤ (m : ℝ) * Real.log (m : ℝ) := by
    have hh : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
    exact (Real.log_le_log (by positivity) hh).trans_eq (Real.log_pow _ _)
  have hL (x : ℝ) (hx : 0 < x) : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx).trans (by linarith)
  have hLm := hL (m : ℝ) hm
  have hLmm := mul_le_mul_of_nonneg_left hLm hm.le
  have hLtwo := mul_le_mul_of_nonneg_left (hL 2 (by norm_num)) hm.le
  calc
    _ ≤ Real.log (1536 * v⁻¹ * τ⁻¹ * ((m : ℝ) ^ 2 * (m.factorial : ℝ) * 2 ^ m)) := hLog
    _ = Real.log 1536 + Real.log v⁻¹ + Real.log τ⁻¹ +
        (2 * Real.log (m : ℝ) + Real.log (m.factorial : ℝ) + (m : ℝ) * Real.log 2) := by
      repeat rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_pow, Real.log_pow]
      norm_num
    _ ≤ _ := by
      nlinarith only [hL 1536 (by norm_num), hL (v⁻¹) (by positivity), hL (τ⁻¹) (by positivity),
        hLm, hFlog, hLmm, hLtwo, hm, sq_nonneg (m : ℝ)]

private lemma inv_mul_le_inv_of_mul_le {a x y : ℝ} (ha : 0 < a) (hy : 0 < y) (h : a * x ≤ y) :
    y⁻¹ * x ≤ a⁻¹ := by
  rw [← div_eq_inv_mul, div_le_iff₀ hy]
  rw [← div_eq_inv_mul, le_div_iff₀ ha]
  simpa only [mul_comm] using h

private lemma exists_common_pair_parameter_bound :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      let X := L / (δ ^ 187264) ^ 2
      let m := (quadraticPairParameters δ).1
      let k := (quadraticPairParameters δ).2
      1 ≤ X ∧ 0 < m ∧ 0 < k ∧ (m : ℝ) ≤ X ∧ Real.log (k : ℝ) ≤ X ∧
      (quadraticPairRate δ)⁻¹ ≤ X ∧ 18 / graphDensityRate δ ^ 2 ≤ X := by
  let a := quadraticPairRate 1
  let b := graphDensityRate 1
  let A := (a ^ 8 / 64)⁻¹
  let B := a⁻¹
  let C := 18 / b ^ 2
  let L := 1540 + A + B + C + 4 * (8 * A + 2) ^ 2 + (8 * A + 1)
  have ha : 0 < a := quadraticPairRate_pos (by norm_num)
  have hb : 0 < b := graphDensityRate_pos (by norm_num)
  have hA : 0 < A := by unfold A; positivity
  have hB : 0 < B := by unfold B; positivity
  have hC : 0 < C := by unfold C; positivity
  have hL : 1 ≤ L := by unfold L; nlinarith only [hA, hB, hC, sq_nonneg (8 * A + 2)]
  refine ⟨L, hL, ?_⟩
  intro δ hδ hδ₁
  dsimp only
  let z := δ ^ 187264
  let v := skewCorrelationRate δ ^ 4 / 64
  let τ := quadraticPairRate δ
  let m := ⌈8 / v⌉₊
  let k := (quadraticPairParameters δ).2
  let X := L / z ^ 2
  change 1 ≤ X ∧ 0 < m ∧ 0 < k ∧ (m : ℝ) ≤ X ∧ Real.log (k : ℝ) ≤ X ∧
    τ⁻¹ ≤ X ∧ 18 / graphDensityRate δ ^ 2 ≤ X
  have hz : 0 < z := by unfold z; positivity
  have hz₁ : z ≤ 1 := pow_le_one₀ hδ.le hδ₁
  have hzz : z ^ 2 ≤ z := by nlinarith only [mul_nonneg hz.le (sub_nonneg.mpr hz₁)]
  have hτ : 0 < τ := quadraticPairRate_pos hδ
  have hτ₁ : τ ≤ 1 := min_le_left _ _
  have hv : 0 < v := by
    have hq := skewCorrelationRate_pos hδ
    unfold v
    positivity
  have hv₁ : v ≤ 1 := by
    have hs := (Real.sqrt_le_sqrt (by linarith : δ / 6 ≤ 1)).trans_eq Real.sqrt_one
    have h := mul_le_mul (graphDensityRate_le_one hδ hδ₁) hs (Real.sqrt_nonneg _) zero_le_one
    have hx : graphDensityRate δ * Real.sqrt (δ / 6) / 36 ≤ 1 := by linarith
    have hh : (graphDensityRate δ * Real.sqrt (δ / 6) / 36) ^ 2 ≤ 1 :=
      pow_le_one₀ (by have := graphDensityRate_pos hδ; positivity) hx
    have hhh : skewCorrelationRate δ ^ 4 ≤ 1 := pow_le_one₀ (skewCorrelationRate_pos hδ).le hh
    unfold v
    linarith
  have hvInv : v⁻¹ * z ≤ A :=
    inv_mul_le_inv_of_mul_le (by positivity : 0 < a ^ 8 / 64) hv (skew_variance_ge_monomial hδ hδ₁)
  have hτInv : τ⁻¹ * z ≤ B := by
    apply inv_mul_le_inv_of_mul_le ha hτ
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ.le hδ₁ (by decide : 23408 ≤ 187264))
      ha.le).trans (quadraticPairRate_ge_monomial hδ hδ₁)
  have hΩInv : (18 / graphDensityRate δ ^ 2) * z ≤ C := by
    have hgb := graphDensityRate_pos hδ
    have hg : b ^ 2 * z ≤ graphDensityRate δ ^ 2 := by
      have h := pow_le_pow_left₀ (show 0 ≤ b * δ ^ 23407 by positivity)
        (graphDensityRate_ge_monomial hδ hδ₁) 2
      rw [mul_pow, ← pow_mul] at h
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ.le hδ₁ (by decide :
        23407 * 2 ≤ 187264)) (sq_nonneg b)).trans h
    have h := inv_mul_le_inv_of_mul_le (sq_pos_of_pos hb) (sq_pos_of_pos hgb) hg
    simpa only [C, div_eq_mul_inv, mul_assoc] using
      mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 18)
  have hm₀ : (0 : ℝ) < m := (by positivity : 0 < 8 / v).trans_le (Nat.le_ceil _)
  have hm : (m : ℝ) * z ≤ 8 * A + 1 := by
    have hh : (m : ℝ) ≤ 8 / v + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    calc
      _ ≤ (8 / v + 1) * z := mul_le_mul_of_nonneg_right hh hz.le
      _ = 8 * (v⁻¹ * z) + z := by rw [div_eq_mul_inv]; ring
      _ ≤ _ := by linarith only [hvInv, hz₁]
  have hkand : 0 < k ∧ Real.log (k : ℝ) ≤ 1536 + v⁻¹ + τ⁻¹ + 4 * ((m : ℝ) + 1) ^ 2 := by
    exact log_quadraticPair_band_param hv hv₁ hτ hτ₁
  have hk : Real.log (k : ℝ) * z ^ 2 ≤ 1536 + A + B + 4 * (8 * A + 2) ^ 2 := by
    have hM : ((m : ℝ) + 1) * z ≤ 8 * A + 2 := by nlinarith only [hm, hz₁]
    calc
      _ ≤ (1536 + v⁻¹ + τ⁻¹ + 4 * ((m : ℝ) + 1) ^ 2) * z ^ 2 :=
        mul_le_mul_of_nonneg_right hkand.2 (by positivity)
      _ = 1536 * z ^ 2 + v⁻¹ * z ^ 2 + τ⁻¹ * z ^ 2 + 4 * (((m : ℝ) + 1) * z) ^ 2 := by ring
      _ ≤ _ := by
        have h₁ : 1536 * z ^ 2 ≤ 1536 := by linarith only [hzz, hz₁]
        have h₂ := (mul_le_mul_of_nonneg_left hzz (by positivity : 0 ≤ v⁻¹)).trans hvInv
        have h₃ := (mul_le_mul_of_nonneg_left hzz (by positivity : 0 ≤ τ⁻¹)).trans hτInv
        have h₄ := pow_le_pow_left₀ (show 0 ≤ ((m : ℝ) + 1) * z by positivity) hM 2
        linarith only [h₁, h₂, h₃, h₄]
  have hden := sq_pos_of_pos hz
  refine ⟨?_, (by exact_mod_cast hm₀), hkand.1, ?_, ?_, ?_, ?_⟩
  · unfold X
    apply (le_div_iff₀ hden).2
    linarith only [hL, hzz, hz₁]
  · unfold X
    apply (le_div_iff₀ hden).2
    have h := (mul_le_mul_of_nonneg_left hzz (by positivity : (0 : ℝ) ≤ m)).trans hm
    unfold L
    nlinarith only [h, hA, hB, hC, sq_nonneg (8 * A + 2)]
  · unfold X
    apply (le_div_iff₀ hden).2
    unfold L
    linarith only [hk, hA, hC]
  · unfold X
    apply (le_div_iff₀ hden).2
    have h := (mul_le_mul_of_nonneg_left hzz (by positivity : 0 ≤ τ⁻¹)).trans hτInv
    unfold L
    nlinarith only [h, hA, hC, sq_nonneg (8 * A + 2)]
  · unfold X
    apply (le_div_iff₀ hden).2
    have h := (mul_le_mul_of_nonneg_left hzz (by positivity : 0 ≤ 18 / graphDensityRate δ ^ 2)).trans hΩInv
    unfold L
    nlinarith only [h, hA, hB, sq_nonneg (8 * A + 2)]

section BohrLogarithm

variable {M : ℕ} [NeZero M]

private lemma log_card_ratio_bohr_le (Ω : Finset (ZMod M)) {r : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) :
    Real.log ((M : ℝ) / ((bohrSet Ω r).card : ℝ)) ≤
      Real.log 32768 * (Ω.card : ℝ) * (Real.log r⁻¹ / Real.log 2 + 2) := by
  have hTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ Real.log r⁻¹ := Real.log_nonneg ((one_le_inv₀ hr).2 hr₁)
  let j := ⌈Real.log r⁻¹ / Real.log 2⌉₊
  have hJ : Real.log r⁻¹ ≤ (j : ℝ) * Real.log 2 := (div_le_iff₀ hTwo).mp (Nat.le_ceil _)
  have hPow : r⁻¹ ≤ (2 : ℝ) ^ j := by
    apply (Real.log_le_log_iff (inv_pos.mpr hr) (by positivity)).mp
    rwa [Real.log_pow]
  have hScale : (1 / 32 : ℝ) ≤ (2 : ℝ) ^ j * r := by
    refine (by norm_num : (1 / 32 : ℝ) ≤ 1).trans ?_
    have h := mul_le_mul_of_nonneg_right hPow hr.le
    simpa only [inv_mul_cancel₀ hr.ne'] using h
  have hcard := bohrSet_card_lower_small_radius Ω hr j hScale
  have hB : 0 < ((bohrSet Ω r).card : ℝ) := by exact_mod_cast (bohrSet_nonempty Ω hr.le).card_pos
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hR : (M : ℝ) / ((bohrSet Ω r).card : ℝ) ≤ (32768 : ℝ) ^ ((j + 1) * Ω.card) :=
    (div_le_iff₀ hB).2 (by exact_mod_cast hcard)
  have hj' : (j : ℝ) ≤ Real.log r⁻¹ / Real.log 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hlog : 0 ≤ Real.log 32768 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ Real.log ((32768 : ℝ) ^ ((j + 1) * Ω.card)) := Real.log_le_log (div_pos hM hB) hR
    _ = Real.log 32768 * (Ω.card : ℝ) * ((j : ℝ) + 1) := by
      rw [Real.log_pow]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hj']) (by positivity)

private lemma log2_le_log_div_log_two {n : ℕ} (hn : 0 < n) :
    (n.log2 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hTwo, ← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.log2_self_le hn.ne')

end BohrLogarithm

private lemma exists_local_chart_loss_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (M m k b : ℕ) [NeZero M], 0 < m → 0 < k → 0 < b → b ≤ M →
      ∀ (Ω Λ : Finset (ZMod M)) (X ε : ℝ), 1 ≤ X → 0 < ε → ε ≤ 1 →
      (Ω.card : ℝ) ≤ X → (m : ℝ) ≤ X → Real.log (k : ℝ) ≤ X → ε⁻¹ ≤ 8 * X →
      let n := 15 * Ω.card + 1
      let t : ℝ := 1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))
      let u := (t / 2) / (2 * (n : ℝ))
      let r := min (u / 2) (ε / ((Λ.card : ℝ) + 1))
      M ≤ 32768 ^ (((m * k * n ^ 4).log2 + 11) * Ω.card) * (4 * m * b) →
      Λ.card ≤ ⌈512 * Real.log (8 * (M : ℝ) / (ε * (b : ℝ))) / ε ^ 2⌉₊ →
      0 < r ∧ r ≤ 1 / 16 ∧ t + u / 2 ≤ 1 / 16 ∧
        Real.log ((M : ℝ) / ((bohrSet (Ω ∪ Λ) r).card : ℝ)) ≤ C * X ^ 8 := by
  let L := Real.log 2
  let P := Real.log 32768
  let C₁ := (66 / L + 11) * P + 5
  let C₂ := 32768 * (C₁ + 16) + 1
  let C₃ := 4170 + C₂
  let C := P * (C₂ + 1) * (C₃ / L + 2)
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hP : 0 < P := Real.log_pos (by norm_num)
  have hC₁ : 0 < C₁ := by unfold C₁; positivity
  have hC₂ : 0 < C₂ := by unfold C₂; positivity
  have hC₃ : 0 < C₃ := by unfold C₃; positivity
  have hC : 0 < C := by unfold C; positivity
  refine ⟨C, hC, ?_⟩
  intro M m k b _ hm hk hb hbM Ω Λ X ε hX hε hε₁ hΩ hmX hkX hεX
  dsimp only
  let n := 15 * Ω.card + 1
  let t : ℝ := 1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))
  let u := (t / 2) / (2 * (n : ℝ))
  let r := min (u / 2) (ε / ((Λ.card : ℝ) + 1))
  let s := m * k * n ^ 4
  intro hSize hΛ
  have hX₀ : 0 < X := by linarith
  have hn₀ : 0 < n := by unfold n; omega
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn₀
  have hnX : (n : ℝ) ≤ 16 * X := by
    unfold n
    push_cast
    linarith only [hΩ, hX]
  have hm₀ : 0 < (m : ℝ) := by exact_mod_cast hm
  have hk₀ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnR : 0 < (n : ℝ) := by positivity
  have hMR : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hbMR : (b : ℝ) ≤ M := by exact_mod_cast hbM
  have hlog (x : ℝ) (h : 0 < x) : Real.log x ≤ x := (Real.log_le_sub_one_of_pos h).trans (by linarith)
  have hmLog := (hlog _ hm₀).trans hmX
  have hnLog := (hlog _ hnR).trans hnX
  have hsLog : Real.log (s : ℝ) ≤ 66 * X := by
    unfold s
    push_cast
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul hm₀.ne' hk₀.ne', Real.log_pow]
    norm_num
    linarith only [hmLog, hkX, hnLog]
  have hs2 : (s.log2 : ℝ) ≤ (66 / L) * X := by
    refine (log2_le_log_div_log_two (show 0 < s by unfold s; positivity)).trans ?_
    change Real.log (s : ℝ) / L ≤ _
    calc
      _ ≤ (66 * X) / L := div_le_div_of_nonneg_right hsLog hL.le
      _ = _ := by ring
  have hX₂ : X ≤ X ^ 2 := by
    nlinarith only [mul_nonneg hX₀.le (sub_nonneg.mpr hX)]
  have hX₄ : X ^ 2 ≤ X ^ 4 := by
    have h := pow_le_pow_right₀ hX (by norm_num : 2 ≤ 4)
    simpa using h
  have hMb : Real.log ((M : ℝ) / b) ≤ C₁ * X ^ 2 := by
    have hcast : (M : ℝ) / b ≤ (32768 : ℝ) ^ ((s.log2 + 11) * Ω.card) * (4 * (m : ℝ)) := by
      apply (div_le_iff₀ hbR).2
      have h : (M : ℝ) ≤ (32768 : ℝ) ^ ((s.log2 + 11) * Ω.card) * (4 * (m : ℝ) * (b : ℝ)) := by
        exact_mod_cast hSize
      simpa only [mul_assoc] using h
    calc
      _ ≤ Real.log ((32768 : ℝ) ^ ((s.log2 + 11) * Ω.card) * (4 * (m : ℝ))) :=
        Real.log_le_log (div_pos hMR hbR) hcast
      _ = P * ((s.log2 : ℝ) + 11) * (Ω.card : ℝ) + Real.log 4 + Real.log (m : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_mul (by norm_num) hm₀.ne']
        push_cast
        unfold P
        ring
      _ ≤ C₁ * X ^ 2 := by
        have h₁ : (s.log2 : ℝ) + 11 ≤ (66 / L + 11) * X := by
          have h := mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 11)
          linarith only [h, hs2]
        have h₂ := mul_le_mul (mul_le_mul_of_nonneg_left h₁ hP.le) hΩ (by positivity) (by positivity)
        have h₃ := hlog 4 (by norm_num)
        unfold C₁
        nlinarith only [h₂, h₃, hmLog, hX, hX₂]
  have hεlog : Real.log ε⁻¹ ≤ 8 * X := (hlog _ (inv_pos.mpr hε)).trans hεX
  have hMassLog : Real.log (8 * (M : ℝ) / (ε * (b : ℝ))) ≤ (C₁ + 16) * X ^ 2 := by
    have he : 8 * (M : ℝ) / (ε * (b : ℝ)) = 8 * ((M : ℝ) / b) * ε⁻¹ := by field_simp
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    nlinarith only [hMb, hεlog, hlog 8 (by norm_num), hX, hX₂]
  have hΛX : (Λ.card : ℝ) ≤ C₂ * X ^ 4 := by
    have hMassNonneg : 0 ≤ Real.log (8 * (M : ℝ) / (ε * (b : ℝ))) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity), one_mul]
      have h := mul_le_of_le_one_left hbR.le hε₁
      linarith only [h, hbMR, hMR]
    have hce : (Λ.card : ℝ) ≤ 512 * Real.log (8 * (M : ℝ) / (ε * (b : ℝ))) / ε ^ 2 + 1 := by
      have h := Nat.ceil_lt_add_one (by positivity :
        0 ≤ 512 * Real.log (8 * (M : ℝ) / (ε * (b : ℝ))) / ε ^ 2)
      exact (by exact_mod_cast hΛ : (Λ.card : ℝ) ≤ (⌈512 *
        Real.log (8 * (M : ℝ) / (ε * (b : ℝ))) / ε ^ 2⌉₊ : ℝ)).trans h.le
    calc
      _ ≤ 512 * Real.log (8 * (M : ℝ) / (ε * (b : ℝ))) / ε ^ 2 + 1 := hce
      _ ≤ 512 * ((C₁ + 16) * X ^ 2) * (8 * X) ^ 2 + 1 := by
        rw [div_eq_mul_inv, ← inv_pow]
        gcongr
      _ ≤ _ := by
        unfold C₂
        nlinarith only [hX, hX₂, hX₄]
  have ht : 0 < t := by unfold t; positivity
  have hu : 0 < u := by unfold u; positivity
  have hr : 0 < r := lt_min (half_pos hu) (by positivity)
  have hSmall : t + u / 2 ≤ 1 / 16 := by
    have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkn : (1 : ℝ) ≤ (k : ℝ) * (n : ℝ) ^ 3 :=
      one_le_mul_of_one_le_of_one_le hk₁ (one_le_pow₀ hn₁)
    have ht₁ : t ≤ 1 / 512 := by
      unfold t
      push_cast
      apply (div_le_iff₀ (by positivity)).2
      nlinarith only [hkn]
    have hu₁ : u ≤ t / 4 := by
      unfold u
      apply (div_le_iff₀ (by positivity)).2
      nlinarith only [mul_nonneg ht.le (sub_nonneg.mpr hn₁)]
    linarith only [ht₁, hu₁]
  have hr₁ : r ≤ 1 / 16 := (min_le_left _ _).trans (by linarith only [hSmall, ht])
  have hRlog : Real.log r⁻¹ ≤ C₃ * X ^ 4 := by
    by_cases h : u / 2 ≤ ε / ((Λ.card : ℝ) + 1)
    · have he : (u / 2)⁻¹ = 4096 * (k : ℝ) * (n : ℝ) ^ 4 := by
        unfold u t
        push_cast
        field_simp
        ring
      unfold r
      rw [min_eq_left h, he, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) hk₀.ne', Real.log_pow]
      norm_num
      unfold C₃
      nlinarith only [hlog 4096 (by norm_num), hkX, hnLog, hX, hX₂, hX₄,
        mul_nonneg hC₂.le (pow_nonneg hX₀.le 4)]
    · unfold r
      rw [min_eq_right (le_of_not_ge h), inv_div, div_eq_mul_inv, Real.log_mul (by positivity) (by positivity)]
      have hl := hlog ((Λ.card : ℝ) + 1) (by positivity)
      unfold C₃
      nlinarith only [hl, hΛX, hεlog, hX, hX₂, hX₄]
  have hdim : ((Ω ∪ Λ).card : ℝ) ≤ (C₂ + 1) * X ^ 4 := by
    have h := Finset.card_union_le Ω Λ
    have h' : ((Ω ∪ Λ).card : ℝ) ≤ (Ω.card : ℝ) + (Λ.card : ℝ) := by exact_mod_cast h
    nlinarith only [h', hΩ, hΛX, hX₂, hX₄]
  refine ⟨hr, hr₁, hSmall, ?_⟩
  refine (log_card_ratio_bohr_le (Ω ∪ Λ) hr (hr₁.trans (by norm_num))).trans ?_
  have hfac : Real.log r⁻¹ / L + 2 ≤ (C₃ / L + 2) * X ^ 4 := by
    have hh := div_le_div_of_nonneg_right hRlog hL.le
    nlinarith only [hh, hX, hX₂, hX₄, show C₃ * X ^ 4 / L = C₃ / L * X ^ 4 by ring]
  have hRnonneg : 0 ≤ Real.log r⁻¹ := Real.log_nonneg ((one_le_inv₀ hr).2 (by linarith only [hr₁]))
  calc
    _ ≤ P * ((C₂ + 1) * X ^ 4) * ((C₃ / L + 2) * X ^ 4) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdim hP.le) hfac (by positivity) (by positivity)
    _ = _ := by unfold C; ring

private lemma exists_quantitative_localQuadraticCorrelation :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : ℤ → ℝ, (∀ x, |f x| ≤ 1) →
      QuadraticPairStructure N δ (quadraticPairParameters δ).1 (quadraticPairParameters δ).2 f →
      ∃ Ω Λ : Finset (ZMod (2 * N + 1)), ∃ φ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
      ∃ x₀ z : ZMod (2 * N + 1), ∃ r : ℝ,
      let D := bohrSet (Ω ∪ Λ) r
      0 < r ∧ r ≤ 1 / 16 ∧ z ∈ bohrSet Ω (1 / 16) ∧
      δ ^ (187264 * 16 : ℕ) * Real.log (((2 * N + 1 : ℕ) : ℝ) / (D.card : ℝ)) ≤ C ∧
      (∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
        a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b) ∧
      quadraticPairRate δ / 2 * (D.card : ℝ) ≤
        ‖∑ d ∈ D, (periodize N f (x₀ + (z + d)) : ℂ) * ZMod.stdAddChar (-localQuadratic φ (z + d))‖ := by
  obtain ⟨L, hL, hparams⟩ := exists_common_pair_parameter_bound
  obtain ⟨C, hC, hscale⟩ := exists_local_chart_loss_bound
  have hLpos : 0 < L := by linarith
  refine ⟨C * L ^ 8, by positivity, ?_⟩
  intro N δ hδ hδ₁ f hf hpair
  let m := (quadraticPairParameters δ).1
  let k := (quadraticPairParameters δ).2
  let p := δ ^ 187264
  let X := L / p ^ 2
  obtain ⟨hX, hm, hk, hmX, hkX, hτX, hG⟩ := hparams δ hδ hδ₁
  obtain ⟨Ω, Λ, φ, b, x₀, z, hr, hD, hb, hbM, hdim, hBsize, hΛ, hz, hadd, hcorr⟩ :=
    localQuadraticCorrelation_of_pair hδ hk hf hpair
  let n := 15 * Ω.card + 1
  let t : ℝ := 1 / (512 * ((k * n ^ 3 : ℕ) : ℝ))
  let u := (t / 2) / (2 * (n : ℝ))
  let ε := quadraticPairRate δ / 8
  let r := min (u / 2) (ε / ((Λ.card : ℝ) + 1))
  let D := bohrSet (Ω ∪ Λ) r
  have hε : 0 < ε := div_pos (quadraticPairRate_pos hδ) (by norm_num)
  have hε₁ : ε ≤ 1 := by
    have h : quadraticPairRate δ ≤ 1 := min_le_left _ _
    unfold ε
    linarith
  have hεX : ε⁻¹ ≤ 8 * X := by
    unfold ε
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hτX (by norm_num)
  have hΩ : (Ω.card : ℝ) ≤ X :=
    ((le_div_iff₀ (sq_pos_of_pos (graphDensityRate_pos hδ))).mpr hdim).trans hG
  obtain ⟨_, hr₁, hz₁, hDsize⟩ := hscale (2 * N + 1) m k b hm hk hb hbM Ω Λ X ε
    hX hε hε₁ hΩ hmX hkX hεX hBsize hΛ
  refine ⟨Ω, Λ, φ, x₀, z, r, hr, hr₁, bohrSet_mono hz₁ hz, ?_, hadd, hcorr⟩
  have hp : 0 < p := by unfold p; positivity
  have he : δ ^ (187264 * 16 : ℕ) = p ^ 16 := by rw [pow_mul]
  rw [he]
  calc
    _ ≤ p ^ 16 * (C * X ^ 8) := mul_le_mul_of_nonneg_left hDsize (by positivity)
    _ = _ := by unfold X; field_simp

private lemma sqrt_card_le_of_log_ratio {M : ℕ} [NeZero M] {D : Finset (ZMod M)}
    (hD : D.Nonempty)
    (h : Real.log ((M : ℝ) / (D.card : ℝ)) ≤ Real.log (M : ℝ) / 2) :
    Real.sqrt (M : ℝ) ≤ (D.card : ℝ) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hCard : 0 < (D.card : ℝ) := by exact_mod_cast hD.card_pos
  rw [Real.log_div hM.ne' hCard.ne'] at h
  apply (Real.log_le_log_iff (Real.sqrt_pos.mpr hM) hCard).mp
  rw [Real.log_sqrt hM.le]
  linarith only [h]

private lemma bohr_quadratic_progression_on_chart {N : ℕ}
    (Ω Λ : Finset (ZMod (2 * N + 1))) {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)} {r : ℝ}
    (hr : r ≤ 1 / 16) {z x d : ZMod (2 * N + 1)} (hz : z ∈ bohrSet Ω (1 / 16))
    (hx : x ∈ bohrSet (Ω ∪ Λ) r) (hd : d ∈ bohrSet (Ω ∪ Λ) r)
    (hadd : ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b) :
    localQuadratic φ (z + x + 3 * d) - 3 * localQuadratic φ (z + x + 2 * d) +
      3 * localQuadratic φ (z + x + d) - localQuadratic φ (z + x) = 0 := by
  have hsub : bohrSet (Ω ∪ Λ) r ⊆ bohrSet Ω (1 / 16) := by
    intro a ha
    exact mem_bohrSet.mpr fun k hk => ((mem_bohrSet.mp ha) k (Finset.mem_union_left _ hk)).trans hr
  refine localQuadratic_bohr_progression Ω hadd ?_ ?_ (by norm_num)
  · refine bohrSet_mono ?_ (add_mem_bohrSet hz (hsub hx))
    norm_num
  · exact bohrSet_mono (by norm_num) (hsub hd)

section PhaseEnergy

variable {X I : Type*} [DecidableEq I]

private lemma norm_correlation_to_phase_energy (S : Finset X) (P : X → I) (f : X → ℝ)
    (hf : ∀ x ∈ S, |f x| ≤ 1) (w : X → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    {σ : ℝ} (hσ : 0 ≤ σ) (L : ℕ) (hL : 0 < L) (hσL : 4 / (L : ℝ) ≤ σ)
    (hc : σ * (S.card : ℝ) ≤
      ‖∑ x ∈ S, ((f x - partMean S P f x : ℝ) : ℂ) * w x‖) :
    ∃ Q : X → I × ℤ, (Prod.fst ∘ Q) = P ∧
      (S.image Q).card ≤ (S.image P).card * (2 * L + 1) ∧
      (∑ x ∈ S, partMean S P f x ^ 2) + (σ / 2) ^ 2 * (S.card : ℝ) ≤
        ∑ x ∈ S, partMean S Q f x ^ 2 := by
  let R (x : X) := f x - partMean S P f x
  let c := ∑ x ∈ S, (R x : ℂ) * w x
  let W (x : X) := (align c * w x).re
  let j (x : X) := ⌊(L : ℝ) * W x⌋
  let Q (x : X) := (P x, j x)
  let V (i : I × ℤ) := max (-1 : ℝ) (min 1 ((i.2 : ℝ) / L))
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
  have hW (x : X) : |W x| ≤ 1 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (norm_align_le c) (hw x) (norm_nonneg _) zero_le_one
  have hJ (x : X) : -(L : ℤ) ≤ j x ∧ j x ≤ (L : ℤ) := by
    constructor
    · apply Int.le_floor.mpr
      push_cast
      have h := mul_le_mul_of_nonneg_left (abs_le.mp (hW x)).1 hL'.le
      simpa only [mul_neg_one] using h
    · have h := (Int.floor_le ((L : ℝ) * W x)).trans
        (mul_le_of_le_one_right hL'.le (abs_le.mp (hW x)).2)
      exact_mod_cast h
  have hbounds (i : I × ℤ) : |V i| ≤ 1 := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hNear (x : X) : |W x - V (Q x)| ≤ 1 / (L : ℝ) := by
    have hjlo : -(1 : ℝ) ≤ (j x : ℝ) / L := by
      apply (le_div_iff₀ hL').2
      simpa only [neg_mul, one_mul] using (show -(L : ℝ) ≤ (j x : ℝ) by exact_mod_cast (hJ x).1)
    have hjhi : (j x : ℝ) / L ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast (hJ x).2) hL'.le
    have hjW : (j x : ℝ) / L ≤ W x := by
      apply (div_le_iff₀ hL').2
      rw [mul_comm]
      exact Int.floor_le _
    have hlt : W x - (j x : ℝ) / L ≤ 1 / (L : ℝ) := by
      apply (le_div_iff₀ hL').2
      have hlt := (Int.lt_floor_add_one ((L : ℝ) * W x)).le
      rw [sub_mul, div_mul_cancel₀ _ hL'.ne', mul_comm (W x)]
      linarith only [hlt]
    unfold V Q
    rw [show min (1 : ℝ) ((j x : ℝ) / L) = ((j x : ℝ) / L) from min_eq_right hjhi,
      max_eq_right hjlo, abs_of_nonneg (sub_nonneg.mpr hjW)]
    exact hlt
  have hR (x : X) (hx : x ∈ S) : |R x| ≤ 2 := by
    unfold R
    have h := abs_partMean_le_one S P f hf x
    calc
      _ ≤ |f x| + |partMean S P f x| := by simpa [sub_eq_add_neg] using abs_add_le (f x) (-partMean S P f x)
      _ ≤ _ := by linarith only [hf x hx, h]
  have hsum : ∑ x ∈ S, R x * W x = ‖c‖ := by
    have h := congrArg Complex.re (align_mul c)
    change (align c * ∑ x ∈ S, (R x : ℂ) * w x).re = _ at h
    rw [Finset.mul_sum, Complex.re_sum, Complex.ofReal_re] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold W
    rw [show align c * ((R x : ℂ) * w x) = (R x : ℂ) * (align c * w x) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hdiff : (∑ x ∈ S, R x * W x) - ∑ x ∈ S, R x * V (Q x) ≤ (2 / (L : ℝ)) * (S.card : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ x ∈ S, |R x| * |W x - V (Q x)| := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← mul_sub, ← abs_mul]
        exact le_abs_self _
      _ ≤ ∑ _ ∈ S, 2 / (L : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        simpa only [mul_one_div] using
          mul_le_mul (hR x hx) (hNear x) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      _ = _ := by simp; ring
  have hlow : σ / 2 * (S.card : ℝ) ≤ |∑ x ∈ S, R x * V (Q x)| := by
    have he : (2 / (L : ℝ)) * (S.card : ℝ) ≤ σ / 2 * (S.card : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith only [hσL, show 4 / (L : ℝ) = 2 * (2 / (L : ℝ)) by ring]
    change σ * (S.card : ℝ) ≤ ‖c‖ at hc
    have h := le_abs_self (∑ x ∈ S, R x * V (Q x))
    rw [hsum] at hdiff
    linarith only [hc, he, h, hdiff]
  refine ⟨Q, rfl, ?_, ?_⟩
  · have hsub : S.image Q ⊆ S.image P ×ˢ Finset.Icc (-(L : ℤ)) (L : ℤ) := by
      intro i hi
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_Icc.mpr (hJ x)⟩
    have hCard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
      rw [Int.card_Icc]
      omega
    have h := Finset.card_le_card hsub
    rwa [Finset.card_product, hCard] at h
  · exact partMean_energy_increment S Q Prod.fst f V hbounds (by positivity) hlow

end PhaseEnergy

section ModelProgressions

variable {I G : Type*} [DecidableEq I] [AddCommGroup G]

private noncomputable def localProgressionSum (A : Finset G) (D : G → Finset G)
    (w : G → G → ℝ) (f₀ f₁ f₂ f₃ : G → ℝ) : ℝ :=
  ∑ x ∈ A, ∑ d ∈ D x,
    w x d * f₀ x * f₁ (x + d) * f₂ (x + 2 • d) * f₃ (x + 3 • d)

omit [AddCommGroup G] in
private lemma nonneg_partMean (A : Finset G) (P : G → I) (f : G → ℝ)
    (hf : ∀ x ∈ A, 0 ≤ f x) (x : G) : 0 ≤ partMean A P f x := by
  unfold partMean fibreMean
  exact div_nonneg (Finset.sum_nonneg fun y hy => hf y (Finset.mem_filter.mp hy).1) (by positivity)

private lemma fourth_power_sum_le_card_cube_mul_sum {X : Type*} (A : Finset X) (f : X → ℝ) :
    (∑ x ∈ A, f x) ^ 4 ≤ (A.card : ℝ) ^ 3 * ∑ x ∈ A, f x ^ 4 := by
  have h (g : X → ℝ) : (∑ x ∈ A, g x) ^ 2 ≤ (A.card : ℝ) * ∑ x ∈ A, g x ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) g
  calc
    _ = ((∑ x ∈ A, f x) ^ 2) ^ 2 := by ring
    _ ≤ ((A.card : ℝ) * ∑ x ∈ A, f x ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) (h f) _
    _ = (A.card : ℝ) ^ 2 * (∑ x ∈ A, f x ^ 2) ^ 2 := by ring
    _ ≤ (A.card : ℝ) ^ 2 * ((A.card : ℝ) * ∑ x ∈ A, (f x ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (h (fun x => f x ^ 2)) (by positivity)
    _ = _ := by
      simp only [← pow_mul]
      ring

private lemma localProgressionSum_model_lower (A : Finset G) (D : G → Finset G)
    (P : G → I) (f : G → ℝ) (hf : ∀ x ∈ A, 0 ≤ f x)
    (w : G → G → ℝ) (hw : ∀ x d, 0 ≤ w x d) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hreturn : ∀ x ∈ A, ρ ≤
      ∑ d ∈ (D x).filter (fun d => P (x + d) = P x ∧ P (x + 2 • d) = P x ∧ P (x + 3 • d) = P x),
        w x d) :
    let F := partMean A P f
    ρ * (∑ x ∈ A, f x) ^ 4 ≤ (A.card : ℝ) ^ 3 * localProgressionSum A D w F F F F := by
  dsimp only
  let F := partMean A P f
  let C (x : G) := (D x).filter (fun d => P (x + d) = P x ∧ P (x + 2 • d) = P x ∧ P (x + 3 • d) = P x)
  have hF (x : G) : 0 ≤ F x := nonneg_partMean A P f hf x
  have hFsum : ∑ x ∈ A, F x = ∑ x ∈ A, f x := by
    simpa only [F, mul_one] using sum_partMean_mul_label A P f (fun _ => 1)
  have hC (x : G) (hx : x ∈ A) :
      ρ * F x ^ 4 ≤ ∑ d ∈ D x, w x d * F x * F (x + d) * F (x + 2 • d) * F (x + 3 • d) := by
    calc
      _ ≤ (∑ d ∈ C x, w x d) * F x ^ 4 := mul_le_mul_of_nonneg_right (hreturn x hx) (by positivity)
      _ = ∑ d ∈ C x, w x d * F x * F (x + d) * F (x + 2 • d) * F (x + 3 • d) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun d hd => ?_
        obtain ⟨h₁, h₂, h₃⟩ := (Finset.mem_filter.mp hd).2
        unfold F partMean
        rw [h₁, h₂, h₃]
        ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun d _ _ => by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hw x d) (hF x)) (hF _)) (hF _)) (hF _))
  have he : ρ * ∑ x ∈ A, F x ^ 4 ≤ localProgressionSum A D w F F F F := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hC
  rw [← hFsum]
  calc
    _ ≤ ρ * ((A.card : ℝ) ^ 3 * ∑ x ∈ A, F x ^ 4) :=
      mul_le_mul_of_nonneg_left (fourth_power_sum_le_card_cube_mul_sum A F) hρ
    _ = (A.card : ℝ) ^ 3 * (ρ * ∑ x ∈ A, F x ^ 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

private lemma localProgressionSum_sub_model (A : Finset G) (D : G → Finset G) (w : G → G → ℝ)
    (f F : G → ℝ) :
    let R := fun x => f x - F x
    localProgressionSum A D w f f f f - localProgressionSum A D w F F F F =
      localProgressionSum A D w R f f f + localProgressionSum A D w F R f f +
        localProgressionSum A D w F F R f + localProgressionSum A D w F F F R := by
  dsimp only
  unfold localProgressionSum
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => by ring

private lemma exists_large_progression_residual (A : Finset G) (D : G → Finset G) (w : G → G → ℝ)
    (f F : G → ℝ) {η : ℝ}
    (hGap : 4 * η ≤ localProgressionSum A D w F F F F - localProgressionSum A D w f f f f) :
    let R := fun x => f x - F x
    η ≤ |localProgressionSum A D w R f f f| ∨ η ≤ |localProgressionSum A D w F R f f| ∨
      η ≤ |localProgressionSum A D w F F R f| ∨ η ≤ |localProgressionSum A D w F F F R| := by
  dsimp only
  have h := localProgressionSum_sub_model A D w f F
  dsimp only at h
  by_contra! hn
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hn
  linarith only [hGap, h, (abs_lt.mp h₁).1, (abs_lt.mp h₂).1, (abs_lt.mp h₃).1, (abs_lt.mp h₄).1]

end ModelProgressions

section PhaseRecurrence

private lemma norm_stdAddChar_nsmul_sub_one_le {M : ℕ} [NeZero M] (a : ZMod M) (n : ℕ) :
    ‖ZMod.stdAddChar (n • a) - 1‖ ≤ (n : ℝ) * ‖ZMod.stdAddChar a - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, Nat.cast_succ, add_mul, one_mul]
    have h := norm_stdAddChar_add_sub_le (n • a) a 0 0
    simp only [zero_add, AddChar.map_zero_eq_one] at h
    exact h.trans (add_le_add_left ih _)

private def localQuadraticBilinear {N : ℕ}
    (φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)) (x d : ZMod (2 * N + 1)) :
    ZMod (2 * N + 1) := halfMod N * (x * φ d + d * φ x)

private lemma localQuadratic_nsmul_increment {N : ℕ}
    {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)} {x d : ZMod (2 * N + 1)} {n : ℕ}
    (hφ : φ (n • d) = n • φ d) (hadd : φ (x + n • d) = φ x + φ (n • d)) :
    localQuadratic φ (x + n • d) - localQuadratic φ x =
      n • localQuadraticBilinear φ x d + n ^ 2 • localQuadratic φ d := by
  unfold localQuadratic localQuadraticBilinear
  rw [hadd, hφ]
  simp only [nsmul_eq_mul, Nat.cast_pow]
  ring

private lemma norm_phase_progression_le {N : ℕ}
    (Ω : Finset (ZMod (2 * N + 1))) {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)}
    {x d : ZMod (2 * N + 1)} (hx : x ∈ bohrSet Ω (1 / 8)) (hd : d ∈ bohrSet Ω (1 / 16))
    (hadd : ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b)
    {n : ℕ} (hn : n ≤ 3) {ε₁ ε₂ : ℝ}
    (h₁ : ‖ZMod.stdAddChar (localQuadraticBilinear φ x d) - 1‖ ≤ ε₁)
    (h₂ : ‖ZMod.stdAddChar (localQuadratic φ d) - 1‖ ≤ ε₂) :
    ‖ZMod.stdAddChar (localQuadratic φ (x + n • d)) - ZMod.stdAddChar (localQuadratic φ x)‖ ≤
      (n : ℝ) * ε₁ + ((n ^ 2 : ℕ) : ℝ) * ε₂ := by
  have hn' : (n : ℝ) ≤ 3 := by exact_mod_cast hn
  have hg : ((n : ℝ) * (1 / 16)) ≤ 1 / 2 := by linarith only [hn']
  have hd' := nsmul_mem_scaled_bohr Ω hd n
  have hxd : x + n • d ∈ bohrSet Ω (1 / 2) :=
    bohrSet_mono (by linarith only [hn']) (add_mem_bohrSet hx hd')
  have hφ := localAdditive_nsmul_on_bohr Ω (by norm_num : (0 : ℝ) ≤ 1 / 16) φ hadd hd n hg
  rw [← norm_stdAddChar_sub_one, localQuadratic_nsmul_increment hφ
    (hadd _ (bohrSet_mono (by norm_num) hx) _ (bohrSet_mono hg hd') hxd)]
  have h := norm_stdAddChar_add_sub_le (n • localQuadraticBilinear φ x d)
    (n ^ 2 • localQuadratic φ d) 0 0
  simp only [zero_add, AddChar.map_zero_eq_one] at h
  exact h.trans (add_le_add
    ((norm_stdAddChar_nsmul_sub_one_le _ _).trans (mul_le_mul_of_nonneg_left h₁ (by positivity)))
    ((norm_stdAddChar_nsmul_sub_one_le _ _).trans (mul_le_mul_of_nonneg_left h₂ (by positivity))))

end PhaseRecurrence

private lemma cyclic_four_ap_off_diagonal_eq_zero_of_count {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N)
    (hcount : let g := indicatorCyclic (cyclicLift N S)
      ∑ a, ∑ d, g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) = (S.card : ℝ))
    (a d : ZMod (2 * N + 1)) (hd : d ≠ 0) :
    let g := indicatorCyclic (cyclicLift N S)
    g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) = 0 := by
  classical
  let g := indicatorCyclic (cyclicLift N S)
  let P (a d : ZMod (2 * N + 1)) := g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d)
  let H : Finset (ZMod (2 * N + 1)) := Finset.univ.erase 0
  have hP (x y : ZMod (2 * N + 1)) : 0 ≤ P x y := by
    have hg (x : ZMod (2 * N + 1)) : 0 ≤ g x := by unfold g indicatorCyclic; split_ifs <;> norm_num
    unfold P
    exact mul_nonneg (mul_nonneg (mul_nonneg (hg _) (hg _)) (hg _)) (hg _)
  have hdiag : ∑ x, P x 0 = (S.card : ℝ) := by
    calc
      _ = ∑ x, g x ^ 4 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [P, mul_zero, add_zero]
        ring
      _ = ((cyclicLift N S).card : ℝ) := sum_indicatorCyclic_pow _ (by decide : (4 : ℕ) ≠ 0)
      _ = _ := by rw [card_cyclicLift hS]
  have hsplit : ∑ x, ∑ d, P x d = (∑ x, P x 0) + ∑ x, ∑ y ∈ H, P x y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by
      rw [add_comm (P x 0)]
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ 0)).symm
  change (∑ x, ∑ d, P x d) = (S.card : ℝ) at hcount
  have hzero : ∑ x, ∑ y ∈ H, P x y = 0 := by linarith only [hcount, hsplit, hdiag]
  have hdH : d ∈ H := Finset.mem_erase.mpr ⟨hd, Finset.mem_univ _⟩
  have hbound : P a d ≤ 0 :=
    (Finset.single_le_sum (f := P a) (fun y _ => hP a y) hdH).trans
      ((Finset.single_le_sum (f := fun x => ∑ y ∈ H, P x y)
        (fun x _ => Finset.sum_nonneg fun y _ => hP x y) (Finset.mem_univ a)).trans_eq hzero)
  exact le_antisymm hbound (hP _ _)

private lemma localProgressionSum_of_cyclic_count_le {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N)
    (hcount : let g := indicatorCyclic (cyclicLift N S)
      ∑ a, ∑ d, g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) = (S.card : ℝ))
    (A : Finset (ZMod (2 * N + 1))) (D : ZMod (2 * N + 1) → Finset (ZMod (2 * N + 1)))
    (w : ZMod (2 * N + 1) → ZMod (2 * N + 1) → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ x ∈ A, w x 0 ≤ ρ) :
    let g := indicatorCyclic (cyclicLift N S)
    localProgressionSum A D w g g g g ≤ ρ * (A.card : ℝ) := by
  classical
  dsimp only
  let g := indicatorCyclic (cyclicLift N S)
  have hterm (a d : ZMod (2 * N + 1)) (hd : d ≠ 0) :
      w a d * g a * g (a + d) * g (a + 2 • d) * g (a + 3 • d) = 0 := by
    rw [show (2 : ℕ) • d = 2 * d by simp [nsmul_eq_mul],
      show (3 : ℕ) • d = 3 * d by simp [nsmul_eq_mul]]
    have hz := cyclic_four_ap_off_diagonal_eq_zero_of_count hS hcount a d hd
    change g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) = 0 at hz
    linear_combination (w a d) * hz
  unfold localProgressionSum
  rw [show ρ * (A.card : ℝ) = ∑ _ ∈ A, ρ by simp [mul_comm]]
  refine Finset.sum_le_sum fun a ha => ?_
  by_cases hD : 0 ∈ D a
  · rw [Finset.sum_eq_single_of_mem 0 hD (fun d _ hd => hterm a d hd)]
    simp only [nsmul_zero, add_zero]
    have hg : g a = 0 ∨ g a = 1 := by unfold g indicatorCyclic; split_ifs <;> simp
    change w a 0 * g a * g a * g a * g a ≤ ρ
    rcases hg with h | h <;> simp [h, hρ, hw a ha]
  · rw [Finset.sum_eq_zero fun d hd => hterm a d (by intro he; exact hD (he ▸ hd))]
    exact hρ

section LocalCauchySchwarz

variable {G : Type*} [AddCommGroup G]

private def SumTranslationBound (A : Finset G) (t : G) (η : ℝ) : Prop :=
  ∀ F : G → ℝ, (∀ x, |F x| ≤ 1) →
    |(∑ x ∈ A, F (x + t)) - ∑ x ∈ A, F x| ≤ η * (A.card : ℝ)

private lemma sumTranslationBound_product {I : Type*} [AddCommGroup I]
    (A : Finset G) (B : Finset I) {t : G} {η : ℝ} (h : SumTranslationBound A t η) :
    SumTranslationBound (A ×ˢ B) (t, (0 : I)) η := by
  intro F hF
  simp only [Finset.sum_product_right, Prod.mk_add_mk, add_zero, Finset.card_product, Nat.cast_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b ∈ B, |(∑ a ∈ A, F (a + t, b)) - ∑ a ∈ A, F (a, b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ B, η * (A.card : ℝ) :=
      Finset.sum_le_sum fun b _ => h (fun a => F (a, b)) (fun a => hF (a, b))
    _ = _ := by simp; ring

private lemma sumTranslationBound_of_bohr_band {M : ℕ} [NeZero M]
    (Ω : Finset (ZMod M)) {R γ η : ℝ} (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (hband : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    {t : ZMod M} (ht : t ∈ bohrSet Ω γ) : SumTranslationBound (bohrSet Ω R) t (2 * η) := by
  exact bohr_band_translation_sum Ω hγ hη hband ht

private lemma local_cauchySchwarz_remove_factor {H : Type*} (A : Finset G) (B : Finset H)
    (hA : A.Nonempty) (t : H → G) (f g : G → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1)
    {α η : ℝ} (_hη : 0 ≤ η) (hαη : η ≤ α)
    (htrans : ∀ b ∈ B, SumTranslationBound A (t b) η)
    (hfix : ∀ b ∈ B, ∀ x, f (x + t b) = f x)
    (hlarge : α * (A.card : ℝ) ≤ |∑ x ∈ A, f x * g x|) :
    (α - η) ^ 2 * ((A ×ˢ B ×ˢ B).card : ℝ) ≤
      ∑ p ∈ A ×ˢ B ×ˢ B, g (p.1 + t p.2.1) * g (p.1 + t p.2.2) := by
  let S := ∑ x ∈ A, f x * g x
  let T := ∑ b ∈ B, ∑ x ∈ A, f (x + t b) * g (x + t b)
  let G (x : G) := ∑ b ∈ B, g (x + t b)
  have hT : T = ∑ x ∈ A, f x * G x := by
    unfold T G
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb => by rw [hfix b hb x]
  have hdiff : |T - (B.card : ℝ) * S| ≤ (B.card : ℝ) * (η * (A.card : ℝ)) := by
    unfold T
    rw [show (B.card : ℝ) * S = ∑ _ ∈ B, S by simp, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ b ∈ B, |(∑ x ∈ A, f (x + t b) * g (x + t b)) - S| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ B, η * (A.card : ℝ) := by
        refine Finset.sum_le_sum fun b hb => htrans b hb (fun x => f x * g x) ?_
        intro x
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul (hf x) (hg x) (abs_nonneg _) zero_le_one
      _ = _ := by simp
  have htri : (B.card : ℝ) * |S| ≤ |T - (B.card : ℝ) * S| + |T| := by
    have hh := abs_add_le ((B.card : ℝ) * S - T) T
    rw [sub_add_cancel, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (B.card : ℝ)), abs_sub_comm] at hh
    exact hh
  have hTbig : (α - η) * (A.card : ℝ) * (B.card : ℝ) ≤ |T| := by
    have h := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ (B.card : ℝ))
    change (B.card : ℝ) * (α * (A.card : ℝ)) ≤ (B.card : ℝ) * |S| at h
    nlinarith only [h, hdiff, htri]
  have hCS : |T| ^ 2 ≤ (A.card : ℝ) * ∑ x ∈ A, G x ^ 2 := by
    rw [hT, sq_abs]
    refine (Finset.sum_mul_sq_le_sq_mul_sq A f G).trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ ∑ _ ∈ A, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
        rw [← sq_abs]
        simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hf x) 2
      _ = _ := by simp
  have hSq : ((α - η) * (A.card : ℝ) * (B.card : ℝ)) ^ 2 ≤ (A.card : ℝ) * ∑ x ∈ A, G x ^ 2 :=
    (pow_le_pow_left₀ (by positivity : 0 ≤ (α - η) * (A.card : ℝ) * (B.card : ℝ)) hTbig 2).trans hCS
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have heq : (∑ x ∈ A, G x ^ 2) =
      ∑ p ∈ A ×ˢ B ×ˢ B, g (p.1 + t p.2.1) * g (p.1 + t p.2.2) := by
    simp only [G, sq, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun b' _ => mul_comm _ _
  rw [← heq]
  simp only [Finset.card_product, Nat.cast_mul]
  apply le_of_mul_le_mul_left _ hApos
  exact (show (A.card : ℝ) * ((α - η) ^ 2 * ((A.card : ℝ) * ((B.card : ℝ) * (B.card : ℝ)))) =
    ((α - η) * (A.card : ℝ) * (B.card : ℝ)) ^ 2 by ring).le.trans hSq

end LocalCauchySchwarz

section LocalBoxCauchySchwarz

variable {G H I J : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup I] [AddCommGroup J]

private def doubleAlong {X Y : Type*} [Add X] (t : Y → X) (f : X → ℝ) (p : X × Y × Y) : ℝ :=
  f (p.1 + t p.2.1) * f (p.1 + t p.2.2)

private lemma abs_mul_le_one_of_abs {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul hx hy (abs_nonneg _) zero_le_one

private lemma abs_doubleAlong_le_one {X Y : Type*} [Add X] (t : Y → X) (f : X → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (p : X × Y × Y) : |doubleAlong t f p| ≤ 1 :=
  abs_mul_le_one_of_abs (hf _) (hf _)

private lemma doubleAlong_preserves_translation {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (t : Y → X) (f : X → ℝ) {u : X} (hf : ∀ x, f (x + u) = f x) (p : X × Y × Y) :
    doubleAlong t f (p + (u, 0)) = doubleAlong t f p := by
  rcases p with ⟨x, a, b⟩
  change f (x + u + t (a + 0)) * f (x + u + t (b + 0)) = f (x + t a) * f (x + t b)
  simp only [add_zero, add_right_comm x u, hf]

omit [AddCommGroup J] in
private lemma local_cauchySchwarz_three_factors
    (A : Finset G) (B₁ : Finset H) (B₂ : Finset I) (B₃ : Finset J)
    (hA : A.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (t₁ : H → G) (t₂ : I → G) (t₃ : J → G)
    (f₀ f₁ f₂ f₃ : G → ℝ)
    (h₀ : ∀ x, |f₀ x| ≤ 1) (h₁ : ∀ x, |f₁ x| ≤ 1) (h₂ : ∀ x, |f₂ x| ≤ 1) (h₃ : ∀ x, |f₃ x| ≤ 1)
    {α e₁ e₂ e₃ : ℝ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (he₃ : 0 ≤ e₃)
    (he₁' : e₁ ≤ α) (he₂' : e₂ ≤ (α - e₁) ^ 2) (he₃' : e₃ ≤ ((α - e₁) ^ 2 - e₂) ^ 2)
    (hT₁ : ∀ b ∈ B₁, SumTranslationBound A (t₁ b) e₁)
    (hT₂ : ∀ b ∈ B₂, SumTranslationBound A (t₂ b) e₂)
    (hT₃ : ∀ b ∈ B₃, SumTranslationBound A (t₃ b) e₃)
    (hfix₁ : ∀ b ∈ B₁, ∀ x, f₁ (x + t₁ b) = f₁ x)
    (hfix₂ : ∀ b ∈ B₂, ∀ x, f₂ (x + t₂ b) = f₂ x)
    (hfix₃ : ∀ b ∈ B₃, ∀ x, f₃ (x + t₃ b) = f₃ x)
    (hCorr : α * (A.card : ℝ) ≤ |∑ x ∈ A, f₁ x * (f₂ x * (f₃ x * f₀ x))|) :
    let A₁ := A ×ˢ B₁ ×ˢ B₁
    let t₂' : I → G × H × H := fun b => (t₂ b, 0)
    let A₂ := A₁ ×ˢ B₂ ×ˢ B₂
    let t₃' : J → (G × H × H) × I × I := fun b => ((t₃ b, 0), 0)
    let A₃ := A₂ ×ˢ B₃ ×ˢ B₃
    (((α - e₁) ^ 2 - e₂) ^ 2 - e₃) ^ 2 * (A₃.card : ℝ) ≤
      ∑ p ∈ A₃, doubleAlong t₃' (doubleAlong t₂' (doubleAlong t₁ f₀)) p := by
  dsimp only
  let A₁ := A ×ˢ B₁ ×ˢ B₁
  let t₂' : I → G × H × H := fun b => (t₂ b, 0)
  let A₂ := A₁ ×ˢ B₂ ×ˢ B₂
  let t₃' : J → (G × H × H) × I × I := fun b => ((t₃ b, 0), 0)
  let A₃ := A₂ ×ˢ B₃ ×ˢ B₃
  let f₁₂ := doubleAlong t₁ f₂
  let f₁₃ := doubleAlong t₁ f₃
  let f₁₀ := doubleAlong t₁ f₀
  let f₂₃ := doubleAlong t₂' f₁₃
  let f₂₀ := doubleAlong t₂' f₁₀
  have hStep₁ := local_cauchySchwarz_remove_factor A B₁ hA t₁ f₁
    (fun x => f₂ x * (f₃ x * f₀ x)) h₁
    (fun x => abs_mul_le_one_of_abs (h₂ x) (abs_mul_le_one_of_abs (h₃ x) (h₀ x)))
    he₁ he₁' hT₁ hfix₁ hCorr
  have hsum₁ : (α - e₁) ^ 2 * (A₁.card : ℝ) ≤
      |∑ p ∈ A₁, f₁₂ p * (f₁₃ p * f₁₀ p)| := by
    refine hStep₁.trans ?_
    have hEq : (∑ p ∈ A₁, (f₂ (p.1 + t₁ p.2.1) * (f₃ (p.1 + t₁ p.2.1) * f₀ (p.1 + t₁ p.2.1))) *
        (f₂ (p.1 + t₁ p.2.2) * (f₃ (p.1 + t₁ p.2.2) * f₀ (p.1 + t₁ p.2.2)))) =
        ∑ p ∈ A₁, f₁₂ p * (f₁₃ p * f₁₀ p) :=
      Finset.sum_congr rfl fun p _ => by dsimp [f₁₂, f₁₃, f₁₀, doubleAlong]; ring
    rw [hEq]
    exact le_abs_self _
  have hA₁ : A₁.Nonempty := hA.product (hB₁.product hB₁)
  have hA₂ : A₂.Nonempty := hA₁.product (hB₂.product hB₂)
  have hStep₂ := local_cauchySchwarz_remove_factor A₁ B₂ hA₁ t₂' f₁₂
    (fun p => f₁₃ p * f₁₀ p) (abs_doubleAlong_le_one t₁ f₂ h₂)
    (fun p => abs_mul_le_one_of_abs (abs_doubleAlong_le_one t₁ f₃ h₃ p) (abs_doubleAlong_le_one t₁ f₀ h₀ p))
    he₂ he₂' (fun b hb => sumTranslationBound_product A (B₁ ×ˢ B₁) (hT₂ b hb))
    (fun b hb p => doubleAlong_preserves_translation t₁ f₂ (hfix₂ b hb) p) hsum₁
  have hsum₂ : ((α - e₁) ^ 2 - e₂) ^ 2 * (A₂.card : ℝ) ≤ |∑ p ∈ A₂, f₂₃ p * f₂₀ p| := by
    refine hStep₂.trans ?_
    have hEq : (∑ p ∈ A₂, (f₁₃ (p.1 + t₂' p.2.1) * f₁₀ (p.1 + t₂' p.2.1)) *
        (f₁₃ (p.1 + t₂' p.2.2) * f₁₀ (p.1 + t₂' p.2.2))) =
        ∑ p ∈ A₂, f₂₃ p * f₂₀ p :=
      Finset.sum_congr rfl fun p _ => by dsimp [f₂₃, f₂₀, doubleAlong]; ring
    rw [hEq]
    exact le_abs_self _
  exact local_cauchySchwarz_remove_factor A₂ B₃ hA₂ t₃' f₂₃ f₂₀
    (abs_doubleAlong_le_one t₂' f₁₃ (abs_doubleAlong_le_one t₁ f₃ h₃))
    (abs_doubleAlong_le_one t₂' f₁₀ (abs_doubleAlong_le_one t₁ f₀ h₀))
    he₃ he₃'
    (fun b hb => sumTranslationBound_product A₁ (B₂ ×ˢ B₂)
      (sumTranslationBound_product A (B₁ ×ˢ B₁) (hT₃ b hb)))
    (fun b hb p => doubleAlong_preserves_translation t₂' f₁₃
      (doubleAlong_preserves_translation t₁ f₃ (hfix₃ b hb)) p) hsum₂

end LocalBoxCauchySchwarz

section LocalProgressionCauchySchwarz

private lemma sumTranslationBound_add {G : Type*} [AddCommGroup G] (A : Finset G)
    {t u : G} {η θ : ℝ} (ht : SumTranslationBound A t η) (hu : SumTranslationBound A u θ) :
    SumTranslationBound A (t + u) (η + θ) := by
  intro F hF
  have h₁ := ht (fun x => F (x + u)) (fun x => hF (x + u))
  simp only [add_assoc] at h₁
  have h₂ := hu F hF
  calc
    _ ≤ |(∑ x ∈ A, F (x + (t + u))) - ∑ x ∈ A, F (x + u)| +
        |(∑ x ∈ A, F (x + u)) - ∑ x ∈ A, F x| := abs_sub_le _ _ _
    _ ≤ η * (A.card : ℝ) + θ * (A.card : ℝ) := add_le_add h₁ h₂
    _ = _ := by ring

private lemma sumTranslationBound_product_two {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (A : Finset G) (B : Finset H) {t : G} {u : H} {η θ : ℝ}
    (ht : SumTranslationBound A t η) (hu : SumTranslationBound B u θ) :
    SumTranslationBound (A ×ˢ B) (t, u) (η + θ) := by
  have h₀ : SumTranslationBound (A ×ˢ B) ((0 : G), u) θ := by
    intro F hF
    simp only [Finset.sum_product, Prod.mk_add_mk, add_zero, Finset.card_product, Nat.cast_mul]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ a ∈ A, |(∑ b ∈ B, F (a, b + u)) - ∑ b ∈ B, F (a, b)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ A, θ * (B.card : ℝ) :=
        Finset.sum_le_sum fun a _ => hu (fun b => F (a, b)) (fun b => hF (a, b))
      _ = _ := by simp; ring
  simpa only [Prod.mk_add_mk, zero_add, add_zero] using
    sumTranslationBound_add (A ×ˢ B) (sumTranslationBound_product A B ht) h₀

private def progressionDirection {G : Type*} [AddCommGroup G] (c : ℕ) (h : G) : G × G :=
  (c • h, -h)

private def progressionLinearForm {G : Type*} [AddCommGroup G] (c : ℕ) (p : G × G) : G :=
  p.1 + c • p.2

private lemma progressionLinearForm_const_on_direction {G : Type*} [AddCommGroup G]
    (c : ℕ) (p : G × G) (h : G) :
    progressionLinearForm c (p + progressionDirection c h) = progressionLinearForm c p := by
  change p.1 + c • h + c • (p.2 + -h) = p.1 + c • p.2
  rw [nsmul_add, smul_neg]
  abel

private lemma neg_mem_bohrSet {M : ℕ} [NeZero M] {Ω : Finset (ZMod M)} {r : ℝ} {x : ZMod M}
    (hx : x ∈ bohrSet Ω r) : -x ∈ bohrSet Ω r := by
  apply mem_bohrSet.mpr
  intro a ha
  rw [mul_neg, norm_stdAddChar_neg_sub_one]
  exact (mem_bohrSet.mp hx) a ha

private lemma local_bohr_progression_cauchySchwarz {M : ℕ} [NeZero M]
    (Ω : Finset (ZMod M)) {R r γ γ' s η θ α : ℝ}
    (hR : 0 ≤ R) (hr : 0 ≤ r) (hs : 0 ≤ s) (hsA : 3 * s ≤ γ) (hsB : s ≤ γ')
    (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    (hbandA : ((bohrSet Ω (R + γ)).card : ℝ) ≤ (1 + η) * ((bohrSet Ω (R - γ)).card : ℝ))
    (hbandB : ((bohrSet Ω (r + γ')).card : ℝ) ≤ (1 + θ) * ((bohrSet Ω (r - γ')).card : ℝ))
    (h₁ : 2 * η + 2 * θ ≤ α) (h₂ : 2 * η + 2 * θ ≤ (α - (2 * η + 2 * θ)) ^ 2)
    (h₃ : 2 * η + 2 * θ ≤ ((α - (2 * η + 2 * θ)) ^ 2 - (2 * η + 2 * θ)) ^ 2)
    (c₀ c₁ c₂ c₃ : ℕ) (hc₁ : c₁ ≤ 3) (hc₂ : c₂ ≤ 3) (hc₃ : c₃ ≤ 3)
    (f₀ f₁ f₂ f₃ : ZMod M → ℝ)
    (hf₀ : ∀ x, |f₀ x| ≤ 1) (hf₁ : ∀ x, |f₁ x| ≤ 1) (hf₂ : ∀ x, |f₂ x| ≤ 1) (hf₃ : ∀ x, |f₃ x| ≤ 1)
    (hCorr : α * (((bohrSet Ω R).card : ℝ) * ((bohrSet Ω r).card : ℝ)) ≤
      |∑ x ∈ bohrSet Ω R, ∑ d ∈ bohrSet Ω r, f₀ (x + c₀ • d) * f₁ (x + c₁ • d) *
        f₂ (x + c₂ • d) * f₃ (x + c₃ • d)|) :
    let e := 2 * η + 2 * θ
    let H := bohrSet Ω s
    let A := bohrSet Ω R ×ˢ bohrSet Ω r
    let A₁ := A ×ˢ H ×ˢ H
    let A₂ := A₁ ×ˢ H ×ˢ H
    let A₃ := A₂ ×ˢ H ×ˢ H
    let t₂ : ZMod M → (ZMod M × ZMod M) × ZMod M × ZMod M :=
      fun h => (progressionDirection c₂ h, 0)
    let t₃ : ZMod M → ((ZMod M × ZMod M) × ZMod M × ZMod M) × ZMod M × ZMod M :=
      fun h => ((progressionDirection c₃ h, 0), 0)
    (((α - e) ^ 2 - e) ^ 2 - e) ^ 2 * (A₃.card : ℝ) ≤
      ∑ p ∈ A₃, doubleAlong t₃ (doubleAlong t₂
        (doubleAlong (progressionDirection c₁) (f₀ ∘ progressionLinearForm c₀))) p := by
  let e := 2 * η + 2 * θ
  let A := bohrSet Ω R ×ˢ bohrSet Ω r
  let H := bohrSet Ω s
  have hA : A.Nonempty := (bohrSet_nonempty Ω hR).product (bohrSet_nonempty Ω hr)
  have hH : H.Nonempty := bohrSet_nonempty Ω hs
  have htrans (c : ℕ) (hc : c ≤ 3) (b : ZMod M) (hb : b ∈ H) :
      SumTranslationBound A (progressionDirection c b) e := by
    have hγ : 0 ≤ γ := (by positivity : 0 ≤ 3 * s).trans hsA
    have hγ' : 0 ≤ γ' := hs.trans hsB
    have hc' : (c : ℝ) ≤ 3 := by exact_mod_cast hc
    have hbA : c • b ∈ bohrSet Ω γ := bohrSet_mono (by
      have h := mul_le_mul_of_nonneg_right hc' hs
      exact h.trans hsA) (nsmul_mem_scaled_bohr Ω hb c)
    have hbB : -b ∈ bohrSet Ω γ' := bohrSet_mono hsB (neg_mem_bohrSet hb)
    exact sumTranslationBound_product_two _ _
      (sumTranslationBound_of_bohr_band Ω hγ hη hbandA hbA)
      (sumTranslationBound_of_bohr_band Ω hγ' hθ hbandB hbB)
  have hfix (c : ℕ) (f : ZMod M → ℝ) (b : ZMod M) (p : ZMod M × ZMod M) :
      (f ∘ progressionLinearForm c) (p + progressionDirection c b) =
        (f ∘ progressionLinearForm c) p := by
    simp only [Function.comp_apply, progressionLinearForm_const_on_direction]
  have hlarge : α * (A.card : ℝ) ≤
      |∑ p ∈ A, (f₁ ∘ progressionLinearForm c₁) p * ((f₂ ∘ progressionLinearForm c₂) p *
        ((f₃ ∘ progressionLinearForm c₃) p * (f₀ ∘ progressionLinearForm c₀) p))| := by
    have he : (∑ p ∈ A, (f₁ ∘ progressionLinearForm c₁) p * ((f₂ ∘ progressionLinearForm c₂) p *
          ((f₃ ∘ progressionLinearForm c₃) p * (f₀ ∘ progressionLinearForm c₀) p))) =
        ∑ x ∈ bohrSet Ω R, ∑ d ∈ bohrSet Ω r, f₀ (x + c₀ • d) * f₁ (x + c₁ • d) *
          f₂ (x + c₂ • d) * f₃ (x + c₃ • d) := by
      unfold A
      rw [Finset.sum_product]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => by
        simp only [Function.comp_apply, progressionLinearForm]
        ring
    rw [he]
    simpa only [A, Finset.card_product, Nat.cast_mul] using hCorr
  exact local_cauchySchwarz_three_factors A H H H hA hH hH
    (progressionDirection c₁) (progressionDirection c₂) (progressionDirection c₃)
    (f₀ ∘ progressionLinearForm c₀) (f₁ ∘ progressionLinearForm c₁)
    (f₂ ∘ progressionLinearForm c₂) (f₃ ∘ progressionLinearForm c₃)
    (fun _ => hf₀ _) (fun _ => hf₁ _) (fun _ => hf₂ _) (fun _ => hf₃ _)
    (by positivity) (by positivity) (by positivity)
    h₁ h₂ h₃ (htrans c₁ hc₁) (htrans c₂ hc₂) (htrans c₃ hc₃)
    (fun b _ => hfix c₁ f₁ b) (fun b _ => hfix c₂ f₂ b) (fun b _ => hfix c₃ f₃ b) hlarge

end LocalProgressionCauchySchwarz

section LocalCubeDerivatives

variable {G H I J : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup I]

private lemma doubleAlong_translate {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (t : Y → X) (f : X → ℝ) (u : X) (p : X × Y × Y) :
    doubleAlong t f (p + (u, 0)) = doubleAlong t (fun x => f (x + u)) p := by
  rcases p with ⟨x, a, b⟩
  change f (x + u + t (a + 0)) * f (x + u + t (b + 0)) =
    f (x + t a + u) * f (x + t b + u)
  simp only [add_zero, add_right_comm x u]

private lemma doubleAlong_mul {X Y : Type*} [Add X] (t : Y → X) (f g : X → ℝ)
    (p : X × Y × Y) :
    doubleAlong t (fun x => f x * g x) p = doubleAlong t f p * doubleAlong t g p := by
  unfold doubleAlong
  ring

private lemma local_cube_product_eq_derivative
    (t₁ : H → G) (t₂ : I → G) (t₃ : J → G) (f : G → ℝ)
    (p : ((G × H × H) × I × I) × J × J) :
    let u := t₃ p.2.1
    let v := t₃ p.2.2
    let g := fun x => f x * f (x + (v - u))
    let t₂' : I → G × H × H := fun h => (t₂ h, 0)
    let t₃' : J → (G × H × H) × I × I := fun h => ((t₃ h, 0), 0)
    doubleAlong t₃' (doubleAlong t₂' (doubleAlong t₁ f)) p =
      doubleAlong t₂' (doubleAlong t₁ g) (p.1 + ((u, 0), 0)) := by
  dsimp only
  let t₂' : I → G × H × H := fun h => (t₂ h, 0)
  let u := t₃ p.2.1
  let v := t₃ p.2.2
  let g := fun x => f x * f (x + (v - u))
  change
    doubleAlong t₂' (doubleAlong t₁ f) (p.1 + ((u, 0), 0)) *
      doubleAlong t₂' (doubleAlong t₁ f) (p.1 + ((v, 0), 0)) =
    doubleAlong t₂' (doubleAlong t₁ g) (p.1 + ((u, 0), 0))
  simp only [doubleAlong_translate, ← doubleAlong_mul]
  have he (x : G) : x + u + (v - u) = x + v := by abel
  simp only [g, he]

private lemma many_large_local_derivative_pairs
    (A : Finset G) (H₁ : Finset H) (H₂ : Finset I) (H₃ : Finset J)
    (hA : A.Nonempty) (hH₁ : H₁.Nonempty) (hH₂ : H₂.Nonempty)
    (t₁ : H → G) (t₂ : I → G) (t₃ : J → G) (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1)
    {τ η : ℝ} (hτ : 0 ≤ τ)
    (htrans : ∀ b ∈ H₃, SumTranslationBound A (t₃ b) η)
    (hCube :
      let A₂ := (A ×ˢ H₁ ×ˢ H₁) ×ˢ H₂ ×ˢ H₂
      let A₃ := A₂ ×ˢ H₃ ×ˢ H₃
      let t₂' : I → G × H × H := fun h => (t₂ h, 0)
      let t₃' : J → (G × H × H) × I × I := fun h => ((t₃ h, 0), 0)
      τ * (A₃.card : ℝ) ≤ ∑ p ∈ A₃, doubleAlong t₃' (doubleAlong t₂' (doubleAlong t₁ f)) p) :
    let A₂ := (A ×ˢ H₁ ×ˢ H₁) ×ˢ H₂ ×ˢ H₂
    let t₂' : I → G × H × H := fun h => (t₂ h, 0)
    let F (q : J × J) := ∑ p ∈ A₂, doubleAlong t₂'
      (doubleAlong t₁ (fun x => f x * f (x + (t₃ q.2 - t₃ q.1)))) p
    τ / 2 * (H₃.card : ℝ) ^ 2 ≤
      (((H₃ ×ˢ H₃).filter (fun q => (τ / 2 - η) * (A₂.card : ℝ) ≤ F q)).card : ℝ) := by
  classical
  dsimp only at hCube ⊢
  let A₁ := A ×ˢ H₁ ×ˢ H₁
  let A₂ := A₁ ×ˢ H₂ ×ˢ H₂
  let t₂' : I → G × H × H := fun h => (t₂ h, 0)
  let t₃' : J → (G × H × H) × I × I := fun h => ((t₃ h, 0), 0)
  let B := H₃ ×ˢ H₃
  let K (q : J × J) (p : (G × H × H) × I × I) := doubleAlong t₂'
      (doubleAlong t₁ (fun x => f x * f (x + (t₃ q.2 - t₃ q.1)))) p
  let F (q : J × J) := ∑ p ∈ A₂, K q p
  let F' (q : J × J) := ∑ p ∈ A₂, K q (p + ((t₃ q.1, 0), 0))
  have hK (q : J × J) (p : (G × H × H) × I × I) : |K q p| ≤ 1 :=
    abs_doubleAlong_le_one t₂' _ (abs_doubleAlong_le_one t₁ _
      (fun x => abs_mul_le_one_of_abs (hf _) (hf _))) p
  have hbig : τ * ((A₂ ×ˢ B).card : ℝ) ≤ ∑ q ∈ B, F' q := by
    change τ * ((A₂ ×ˢ B).card : ℝ) ≤
      ∑ p ∈ A₂ ×ˢ B, doubleAlong t₃' (doubleAlong t₂' (doubleAlong t₁ f)) p at hCube
    refine hCube.trans_eq ?_
    rw [Finset.sum_product_right]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ =>
      local_cube_product_eq_derivative t₁ t₂ t₃ f (p, q)
  have hF' (q : J × J) : F' q ≤ (A₂.card : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ A₂, (1 : ℝ) :=
        Finset.sum_le_sum fun p _ => (le_abs_self _).trans (hK q _)
      _ = _ := by simp
  let L := B.filter (fun q => τ / 2 * (A₂.card : ℝ) ≤ F' q)
  have hA₂ : A₂.Nonempty := (hA.product (hH₁.product hH₁)).product (hH₂.product hH₂)
  have hApos : 0 < (A₂.card : ℝ) := by exact_mod_cast hA₂.card_pos
  have hL : τ / 2 * (B.card : ℝ) ≤ (L.card : ℝ) := by
    have h := card_filter_large_terms B F' (by positivity : 0 ≤ τ / 2 * (A₂.card : ℝ)) (fun q _ => hF' q)
    change _ ≤ (L.card : ℝ) * (A₂.card : ℝ) + (B.card : ℝ) * (τ / 2 * (A₂.card : ℝ)) at h
    rw [Finset.card_product, Nat.cast_mul] at hbig
    apply le_of_mul_le_mul_right _ hApos
    nlinarith only [hbig.trans h]
  have hsub : L ⊆ B.filter (fun q => (τ / 2 - η) * (A₂.card : ℝ) ≤ F q) := by
    intro q hq
    obtain ⟨hqB, hqF⟩ := Finset.mem_filter.mp hq
    have htrans' := sumTranslationBound_product A₁ (H₂ ×ˢ H₂)
      (sumTranslationBound_product A (H₁ ×ˢ H₁) (htrans q.1 (Finset.mem_product.mp hqB).1))
      (K q) (hK q)
    change |F' q - F q| ≤ η * (A₂.card : ℝ) at htrans'
    refine Finset.mem_filter.mpr ⟨hqB, ?_⟩
    change τ / 2 * (A₂.card : ℝ) ≤ F' q at hqF
    have h := (abs_le.mp htrans').2
    linarith only [h, hqF]
  change τ / 2 * (H₃.card : ℝ) ^ 2 ≤ ((B.filter (fun q => (τ / 2 - η) * (A₂.card : ℝ) ≤ F q)).card : ℝ)
  rw [sq, ← Nat.cast_mul, ← Finset.card_product]
  exact hL.trans (by exact_mod_cast Finset.card_le_card hsub)

end LocalCubeDerivatives

section LocalBoxFourier

variable {M : ℕ} [NeZero M]

private lemma sum_local_convolution_eq (A B E : Finset (ZMod M)) (hE : A + B ⊆ E)
    (U V W : ZMod M → ℂ) :
    (∑ z, cyclicConvolution (restrictComplex A U) (restrictComplex B V) z * restrictComplex E W z) =
      ∑ x ∈ A, ∑ y ∈ B, U x * V y * W (x + y) := by
  rw [sum_cyclicConvolution_mul]
  calc
    _ = ∑ x ∈ A, ∑ y, U x * restrictComplex B V y * restrictComplex E W (x + y) := by
      simp only [mul_assoc, ← Finset.mul_sum, sum_restrictComplex_mul]
    _ = ∑ x ∈ A, ∑ y ∈ B, U x * V y * restrictComplex E W (x + y) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [mul_assoc, ← Finset.mul_sum, sum_restrictComplex_mul]
    _ = _ := by
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      simp only [restrictComplex, if_pos (hE (Finset.add_mem_add hx hy))]

private lemma local_trilinear_has_fourier {M : ℕ} [NeZero M] (A B : Finset (ZMod M))
    (hA : A.Nonempty) (hsize : (A + B).card ≤ 2 * A.card) (U V W : ZMod M → ℂ)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hW : ∀ x, ‖W x‖ ≤ 1) {α : ℝ} (hα : 0 ≤ α)
    (hR : α * (A.card : ℝ) * (B.card : ℝ) ≤ ‖∑ x ∈ A, ∑ y ∈ B, U x * V y * W (x + y)‖) :
    ∃ k : ZMod M, α / 2 * (B.card : ℝ) ≤ ‖ZMod.dft (restrictComplex B V) k‖ := by
  let L := ∑ z, cyclicConvolution (restrictComplex A U) (restrictComplex B V) z * restrictComplex (A + B) W z
  have hL : L = ∑ x ∈ A, ∑ y ∈ B, U x * V y * W (x + y) :=
    sum_local_convolution_eq A B (A + B) (fun _ h => h) U V W
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod M))
    (fun k => ‖ZMod.dft (restrictComplex B V) k‖) Finset.univ_nonempty
  let C := ‖ZMod.dft (restrictComplex B V) k‖
  have hLow : α * (A.card : ℝ) * (B.card : ℝ) ≤ ‖L‖ := by simpa only [hL] using hR
  have hUpper : ‖L‖ ^ 2 ≤ C ^ 2 * (A.card : ℝ) * (2 * (A.card : ℝ)) := by
    have h := norm_sum_convolution_mul_sq_le (restrictComplex A U) (restrictComplex B V)
      (restrictComplex (A + B) W) (norm_nonneg _) (fun j => hk j (Finset.mem_univ _))
    apply h.trans
    have hsize' : ((A + B).card : ℝ) ≤ 2 * (A.card : ℝ) := by exact_mod_cast hsize
    exact mul_le_mul (mul_le_mul_of_nonneg_left (sum_sq_restrictComplex_le_card A U hU) (by positivity))
      ((sum_sq_restrictComplex_le_card (A + B) W hW).trans hsize') (by positivity) (by positivity)
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hSq : (α * (B.card : ℝ)) ^ 2 ≤ 2 * C ^ 2 := by
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos hApos)
    calc
      _ = (α * (A.card : ℝ) * (B.card : ℝ)) ^ 2 := by ring
      _ ≤ ‖L‖ ^ 2 := pow_le_pow_left₀ (by positivity) hLow 2
      _ ≤ _ := hUpper.trans_eq (by ring)
  refine ⟨k, ?_⟩
  change α / 2 * (B.card : ℝ) ≤ C
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  nlinarith only [hSq, sq_nonneg C]

private lemma local_box_sum_has_fourier (A B : Finset (ZMod M))
    (hA : A.Nonempty) (hB : B.Nonempty) (hsize : (A + B).card ≤ 2 * A.card)
    (F : ZMod M → ℝ) (hF : ∀ x, |F x| ≤ 1) {α : ℝ} (hα : 0 ≤ α)
    (hBox : α * (A.card : ℝ) ^ 2 * (B.card : ℝ) ^ 2 ≤
      ∑ a' ∈ A, ∑ b' ∈ B, ∑ a ∈ A, ∑ b ∈ B,
        F (a + b) * F (a' + b) * F (a + b') * F (a' + b')) :
    ∃ a' ∈ A, ∃ k : ZMod M, α / 2 * (B.card : ℝ) ≤
      ‖ZMod.dft (restrictComplex B (fun b => (F (a' + b) : ℂ))) k‖ := by
  let T (a' b' : ZMod M) := ∑ a ∈ A, ∑ b ∈ B, F (a + b) * F (a' + b) * F (a + b')
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (A ×ˢ B) (fun z => |T z.1 z.2|) (hA.product hB)
  obtain ⟨a', b'⟩ := p
  obtain ⟨ha', hb'⟩ := Finset.mem_product.mp hp
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hBpos : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hT : α * (A.card : ℝ) * (B.card : ℝ) ≤ |T a' b'| := by
    apply le_of_mul_le_mul_left _ (mul_pos hApos hBpos)
    calc
      _ = α * (A.card : ℝ) ^ 2 * (B.card : ℝ) ^ 2 := by ring
      _ ≤ ∑ a'' ∈ A, ∑ b'' ∈ B, ∑ a ∈ A, ∑ b ∈ B,
          F (a + b) * F (a'' + b) * F (a + b'') * F (a'' + b'') := hBox
      _ = ∑ a'' ∈ A, ∑ b'' ∈ B, T a'' b'' * F (a'' + b'') := by
        unfold T
        simp only [Finset.sum_mul]
      _ ≤ ∑ _ ∈ A, ∑ _ ∈ B, |T a' b'| := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
        calc
          _ ≤ |T a b * F (a + b)| := le_abs_self _
          _ ≤ |T a b| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hF _)
          _ ≤ _ := hmax (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)
      _ = _ := by simp; ring
  let U (a : ZMod M) := (F (a + b') : ℂ)
  let V (b : ZMod M) := (F (a' + b) : ℂ)
  let W (z : ZMod M) := (F z : ℂ)
  have hU (x : ZMod M) : ‖U x‖ ≤ 1 := by
    simpa only [U, Complex.norm_real, Real.norm_eq_abs] using hF _
  have hW (x : ZMod M) : ‖W x‖ ≤ 1 := by
    simpa only [W, Complex.norm_real, Real.norm_eq_abs] using hF x
  have he : (T a' b' : ℂ) = ∑ x ∈ A, ∑ y ∈ B, U x * V y * W (x + y) := by
    simp only [T, Complex.ofReal_sum, Complex.ofReal_mul, U, V, W]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hR : α * (A.card : ℝ) * (B.card : ℝ) ≤ ‖∑ x ∈ A, ∑ y ∈ B, U x * V y * W (x + y)‖ := by
    rw [← he, Complex.norm_real, Real.norm_eq_abs]
    exact hT
  obtain ⟨k, hk⟩ := local_trilinear_has_fourier A B hA hsize U V W hU hW hα hR
  exact ⟨a', ha', k, hk⟩

end LocalBoxFourier

section CommonLocalCentre

variable {M : ℕ} [NeZero M]

private noncomputable def localDerivativeBoxFibre (A B : Finset (ZMod M)) (f : ZMod M → ℝ)
    (p : ZMod M × ZMod M × ZMod M) (q : ZMod M × ZMod M) : ℝ :=
  let g := cyclicDerivative f (q.2 - q.1)
  let x := p.1
  let a' := p.2.1
  let b' := p.2.2
  ∑ a ∈ A, ∑ b ∈ B, g (x + (a + b)) * g (x + (a' + b)) * g (x + (a + b')) * g (x + (a' + b'))

private lemma cube_fibres_have_common_local_fourier (X A B C : Finset (ZMod M))
    (hX : X.Nonempty) (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hsize : (A + B).card ≤ 2 * A.card) (f : ZMod M → ℝ) (hf : ∀ x, |f x| ≤ 1)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hcube : τ * ((X ×ˢ A ×ˢ B).card : ℝ) * ((C ×ˢ C).card : ℝ) * (A.card : ℝ) * (B.card : ℝ) ≤
      ∑ p ∈ X ×ˢ A ×ˢ B, ∑ q ∈ C ×ˢ C, localDerivativeBoxFibre A B f p q) :
    ∃ x₀ ∈ X + A, ∃ J ⊆ C - C, τ / 2 * (C.card : ℝ) ≤ (J.card : ℝ) ∧
      ∀ a ∈ J, ∃ k : ZMod M, τ / 4 * (B.card : ℝ) ≤
        ‖ZMod.dft (restrictComplex B (fun b => (cyclicDerivative f a (x₀ + b) : ℂ))) k‖ := by
  classical
  let T := X ×ˢ A ×ˢ B
  let Q := C ×ˢ C
  let F := localDerivativeBoxFibre A B f
  let z := (A.card : ℝ) * (B.card : ℝ)
  let E (p : ZMod M × ZMod M × ZMod M) := Q.filter (fun q => τ / 2 * z ≤ F p q)
  have hz : 0 < z := mul_pos (by exact_mod_cast hA.card_pos) (by exact_mod_cast hB.card_pos)
  have hN (p : ZMod M × ZMod M × ZMod M) (q : ZMod M × ZMod M) : F p q ≤ z := by
    have hg (x : ZMod M) : |cyclicDerivative f (q.2 - q.1) x| ≤ 1 :=
      abs_mul_le_one_of_abs (hf _) (hf _)
    unfold F localDerivativeBoxFibre
    calc
      _ ≤ ∑ _ ∈ A, ∑ _ ∈ B, (1 : ℝ) := by
        refine Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => (le_abs_self _).trans ?_
        exact abs_mul_le_one_of_abs (abs_mul_le_one_of_abs
          (abs_mul_le_one_of_abs (hg _) (hg _)) (hg _)) (hg _)
      _ = _ := by simp [z]
  have hc : τ / 2 * (T.card : ℝ) * (Q.card : ℝ) ≤ ∑ p ∈ T, ((E p).card : ℝ) := by
    have hUpper : (∑ p ∈ T, ∑ q ∈ Q, F p q) ≤
        (∑ p ∈ T, (E p).card : ℝ) * z + (T.card : ℝ) * ((Q.card : ℝ) * (τ / 2 * z)) := by
      calc
        _ ≤ ∑ p ∈ T, (((E p).card : ℝ) * z + (Q.card : ℝ) * (τ / 2 * z)) :=
          Finset.sum_le_sum fun p _ => card_filter_large_terms Q (F p)
            (t := τ / 2 * z) (by positivity) (fun q _ => hN p q)
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]; simp
    have hBig : τ * (T.card : ℝ) * (Q.card : ℝ) * z ≤ ∑ p ∈ T, ∑ q ∈ Q, F p q := by
      unfold z
      rw [← mul_assoc]
      exact hcube
    apply le_of_mul_le_mul_right _ hz
    nlinarith only [hBig.trans hUpper]
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image T (fun p => (E p).card) (hX.product (hA.product hB))
  have hpcount : τ / 2 * (Q.card : ℝ) ≤ ((E p).card : ℝ) := by
    have hTpos : 0 < (T.card : ℝ) := by exact_mod_cast (hX.product (hA.product hB)).card_pos
    apply le_of_mul_le_mul_left _ hTpos
    calc
      _ = τ / 2 * (T.card : ℝ) * (Q.card : ℝ) := by ring
      _ ≤ ∑ p ∈ T, ((E p).card : ℝ) := hc
      _ ≤ ∑ _ ∈ T, ((E p).card : ℝ) := Finset.sum_le_sum fun q hq => by exact_mod_cast hmax q hq
      _ = _ := by simp
  let J := (E p).image (fun q => q.2 - q.1)
  have hpC : τ / 2 * (C.card : ℝ) ≤ (J.card : ℝ) := by
    have hE : (E p).card ≤ C.card * J.card := by
      rw [← Finset.card_product]
      apply Finset.card_le_card_of_injOn (fun q : ZMod M × ZMod M => (q.1, q.2 - q.1))
      · intro q hq
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1,
          Finset.mem_image_of_mem _ hq⟩
      · intro q _ r _ h
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        change q.1 = r.1 at h₁
        apply Prod.ext h₁
        change q.2 - q.1 = r.2 - r.1 at h₂
        rw [h₁] at h₂
        exact sub_left_injective h₂
    have hE' : ((E p).card : ℝ) ≤ (C.card : ℝ) * (J.card : ℝ) := by exact_mod_cast hE
    have hn : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
    rw [show (Q.card : ℝ) = (C.card : ℝ) * (C.card : ℝ) by simp [Q]] at hpcount
    apply le_of_mul_le_mul_left _ hn
    nlinarith only [hpcount.trans hE']
  let x₀ := p.1 + p.2.1
  refine ⟨x₀, Finset.add_mem_add (Finset.mem_product.mp hp).1
    (Finset.mem_product.mp (Finset.mem_product.mp hp).2).1, J, ?_, hpC, ?_⟩
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    have h := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
    exact Finset.sub_mem_sub h.2 h.1
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    let g := cyclicDerivative f (q.2 - q.1)
    let U (x : ZMod M) := (g (p.1 + (x + p.2.2)) : ℂ)
    let V (y : ZMod M) := (g (x₀ + y) : ℂ)
    let W (z : ZMod M) := (g (p.1 + z) : ℂ)
    have hg (x : ZMod M) : |g x| ≤ 1 := abs_mul_le_one_of_abs (hf _) (hf _)
    have hU (x : ZMod M) : ‖U x‖ ≤ 1 := by
      simpa only [U, Complex.norm_real, Real.norm_eq_abs] using hg _
    have hW (x : ZMod M) : ‖W x‖ ≤ 1 := by
      simpa only [W, Complex.norm_real, Real.norm_eq_abs] using hg _
    have hCorr : τ / 2 * (A.card : ℝ) * (B.card : ℝ) ≤ ‖∑ x ∈ A, ∑ y ∈ B, U x * V y * W (x + y)‖ := by
      have hτ' := (Finset.mem_filter.mp hq).2
      change τ / 2 * z ≤ F p q at hτ'
      let L := ∑ x ∈ A, ∑ y ∈ B, g (p.1 + (x + p.2.2)) * g (x₀ + y) * g (p.1 + (x + y))
      have he : F p q = L * g (p.1 + (p.2.1 + p.2.2)) := by
        unfold F localDerivativeBoxFibre L
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        change _ = g (p.1 + (x + p.2.2)) * g (x₀ + y) * g (p.1 + (x + y)) *
          g (p.1 + (p.2.1 + p.2.2))
        unfold x₀
        rw [add_assoc p.1 p.2.1 y]
        ring
      have hL : F p q ≤ |L| := by
        rw [he]
        exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hg _))
      have he' : (L : ℂ) = ∑ x ∈ A, ∑ y ∈ B, U x * V y * W (x + y) := by
        simp only [L, U, V, W, Complex.ofReal_sum, Complex.ofReal_mul]
      rw [← he', Complex.norm_real, Real.norm_eq_abs]
      simpa only [z, mul_assoc] using hτ'.trans hL
    obtain ⟨k, hk⟩ := local_trilinear_has_fourier A B hA hsize U V W hU hW (by positivity) hCorr
    refine ⟨k, ?_⟩
    convert hk using 1; ring

end CommonLocalCentre

private lemma localProgressionSum_model_lower_with_exceptions
    {I G : Type*} [DecidableEq I] [DecidableEq G] [AddCommGroup G]
    (A Bad : Finset G) (hBad : Bad ⊆ A) (D : G → Finset G) (P : G → I)
    (f : G → ℝ) (hf₀ : ∀ x ∈ A, 0 ≤ f x) (hf₁ : ∀ x ∈ A, |f x| ≤ 1)
    (w : G → G → ℝ) (hw : ∀ x d, 0 ≤ w x d) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hreturn : ∀ x ∈ A, x ∉ Bad → ρ ≤
      ∑ d ∈ (D x).filter (fun d => P (x + d) = P x ∧ P (x + 2 • d) = P x ∧ P (x + 3 • d) = P x),
        w x d) :
    let F := partMean A P f
    ρ * (∑ x ∈ A, f x) ^ 4 ≤ (A.card : ℝ) ^ 3 *
      (localProgressionSum A D w F F F F + ρ * (Bad.card : ℝ)) := by
  dsimp only
  let F := partMean A P f
  let T (x d : G) := w x d * F x * F (x + d) * F (x + 2 • d) * F (x + 3 • d)
  have hF (x : G) : 0 ≤ F x := nonneg_partMean A P f hf₀ x
  have hT (x d : G) : 0 ≤ T x d := by
    unfold T
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hw x d) (hF x)) (hF _)) (hF _)) (hF _)
  have hpoint (x : G) (hx : x ∈ A) :
      ρ * F x ^ 4 ≤ (∑ d ∈ D x, T x d) + if x ∈ Bad then ρ else 0 := by
    by_cases hb : x ∈ Bad
    · rw [if_pos hb]
      have hF₁ : F x ≤ 1 := (le_abs_self _).trans (abs_partMean_le_one A P f hf₁ x)
      have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hF x) hF₁ 4) hρ
      have hsum : 0 ≤ ∑ d ∈ D x, T x d := Finset.sum_nonneg fun d _ => hT x d
      norm_num only [one_pow, mul_one] at h
      linarith only [h, hsum]
    · rw [if_neg hb, add_zero]
      let K := (D x).filter (fun d => P (x + d) = P x ∧ P (x + 2 • d) = P x ∧ P (x + 3 • d) = P x)
      calc
        _ ≤ (∑ d ∈ K, w x d) * F x ^ 4 := mul_le_mul_of_nonneg_right (hreturn x hx hb) (by positivity)
        _ = ∑ d ∈ K, T x d := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun d hd => ?_
          obtain ⟨h₁,h₂,h₃⟩ := (Finset.mem_filter.mp hd).2
          unfold T F partMean
          rw [h₁, h₂, h₃]
          ring
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun d _ _ => hT x d)
  have hBsum : ∑ x ∈ A, (if x ∈ Bad then ρ else 0) = ρ * (Bad.card : ℝ) := by
    rw [← Finset.sum_filter]
    have he : A.filter (fun x => x ∈ Bad) = Bad := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hx => ⟨hBad hx, hx⟩⟩
    rw [he]
    simp [mul_comm]
  have hsum : ρ * ∑ x ∈ A, F x ^ 4 ≤ localProgressionSum A D w F F F F + ρ * (Bad.card : ℝ) := by
    have h := Finset.sum_le_sum hpoint
    rw [Finset.sum_add_distrib, hBsum, ← Finset.mul_sum] at h
    exact h
  have hFsum : ∑ x ∈ A, F x = ∑ x ∈ A, f x := by
    simpa only [F, mul_one] using sum_partMean_mul_label A P f (fun _ => 1)
  rw [← hFsum]
  calc
    _ ≤ ρ * ((A.card : ℝ) ^ 3 * ∑ x ∈ A, F x ^ 4) :=
      mul_le_mul_of_nonneg_left (fourth_power_sum_le_card_cube_mul_sum A F) hρ
    _ = (A.card : ℝ) ^ 3 * (ρ * ∑ x ∈ A, F x ^ 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

private lemma exists_large_cyclic_progression_residual {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N)
    (hcount : let g := indicatorCyclic (cyclicLift N S)
      ∑ a, ∑ d, g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) = (S.card : ℝ))
    {I : Type*} [DecidableEq I] (A : Finset (ZMod (2 * N + 1))) (hA : A.Nonempty)
    (D : ZMod (2 * N + 1) → Finset (ZMod (2 * N + 1))) (P : ZMod (2 * N + 1) → I)
    (w : ZMod (2 * N + 1) → ZMod (2 * N + 1) → ℝ) (hw : ∀ x d, 0 ≤ w x d)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hDensity : δ * (A.card : ℝ) ≤ ∑ x ∈ A, indicatorCyclic (cyclicLift N S) x)
    (hreturn : ∀ x ∈ A, ρ ≤
      ∑ d ∈ (D x).filter (fun d => P (x + d) = P x ∧ P (x + 2 • d) = P x ∧ P (x + 3 • d) = P x),
        w x d)
    (hdiag : ∀ x ∈ A, w x 0 ≤ ρ * δ ^ 4 / 2) :
    let g := indicatorCyclic (cyclicLift N S)
    let F := partMean A P g
    let R := fun x => g x - F x
    let η := (ρ * δ ^ 4 / 8) * (A.card : ℝ)
    η ≤ |localProgressionSum A D w R g g g| ∨ η ≤ |localProgressionSum A D w F R g g| ∨
      η ≤ |localProgressionSum A D w F F R g| ∨ η ≤ |localProgressionSum A D w F F F R| := by
  dsimp only
  let g := indicatorCyclic (cyclicLift N S)
  let F := partMean A P g
  have hg (x : ZMod (2 * N + 1)) (_ : x ∈ A) : 0 ≤ g x := by
    unfold g indicatorCyclic
    split_ifs <;> norm_num
  have hm := localProgressionSum_model_lower A D P g hg w hw hρ hreturn
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hModel : ρ * δ ^ 4 * (A.card : ℝ) ≤ localProgressionSum A D w F F F F := by
    apply le_of_mul_le_mul_left _ (show 0 < (A.card : ℝ) ^ 3 by positivity)
    calc
      _ = ρ * (δ * (A.card : ℝ)) ^ 4 := by ring
      _ ≤ ρ * (∑ x ∈ A, g x) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hDensity 4) hρ
      _ ≤ _ := hm
  have hActual := localProgressionSum_of_cyclic_count_le hS hcount A D w
    (show 0 ≤ ρ * δ ^ 4 / 2 by positivity) hdiag
  apply exists_large_progression_residual A D w g F
  linarith only [hModel, hActual]

private lemma no_long_partition_refinement_with_fixed_increment {X I : Type*} [DecidableEq I]
    (A : Finset X) (hA : A.Nonempty) (f : X → ℝ) (hf : ∀ x ∈ A, |f x| ≤ 1)
    (L : ℕ) {η : ℝ} (hη : 0 < η) (hL : 1 < (L : ℝ) * η ^ 2)
    (admissible : ℕ → (X → I) → Prop)
    (hstart : ∃ P, admissible 0 P)
    (hstep : ∀ n < L, ∀ P, admissible n P →
      ∃ Q : X → I, ∃ p : I → I, ∃ w : I → ℝ, admissible (n + 1) Q ∧ (p ∘ Q) = P ∧
        (∀ i, |w i| ≤ 1) ∧ η * (A.card : ℝ) ≤ |∑ x ∈ A, (f x - partMean A P f x) * w (Q x)|) :
    False := by
  have hiter (n : ℕ) (hn : n ≤ L) :
      ∃ P, admissible n P ∧ (n : ℝ) * η ^ 2 * (A.card : ℝ) ≤ ∑ x ∈ A, partMean A P f x ^ 2 := by
    induction n with
    | zero =>
      obtain ⟨P, hP⟩ := hstart
      refine ⟨P, hP, ?_⟩
      simp only [Nat.cast_zero, zero_mul]
      positivity
    | succ n ih =>
      obtain ⟨P, hP, hE⟩ := ih (by omega)
      obtain ⟨Q, p, w, hQ, hp, hw, hc⟩ := hstep n (by omega) P hP
      have h := partMean_energy_increment A Q p f w hw hη.le (by rwa [hp])
      rw [hp] at h
      refine ⟨Q, hQ, ?_⟩
      rw [Nat.cast_succ, add_mul, add_mul, one_mul]
      exact (add_le_add_left hE _).trans h
  obtain ⟨P, _, hP⟩ := hiter L le_rfl
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have h := hP.trans (partMean_sq_sum_le_card A P f hf)
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hL hpos)) (by simpa only [one_mul] using h)

section LinearPhaseRecurrence

variable {M : ℕ} [NeZero M]

private lemma norm_stdAddChar_double_ge {a : ZMod M}
    (ha : ‖ZMod.stdAddChar a - 1‖ ≤ 1 / 32) :
    (3 / 2 : ℝ) * ‖ZMod.stdAddChar a - 1‖ ≤ ‖ZMod.stdAddChar ((2 : ℕ) • a) - 1‖ := by
  let z := ZMod.stdAddChar a
  have h := norm_sub_le (z + 1) (z - 1)
  have h₁ : (3 / 2 : ℝ) ≤ ‖z + 1‖ := by
    rw [show z + 1 - (z - 1) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    change ‖z - 1‖ ≤ 1 / 32 at ha
    linarith only [ha, h]
  calc
    _ ≤ ‖z + 1‖ * ‖z - 1‖ := mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
    _ = _ := by
      rw [← norm_mul, two_nsmul, AddChar.map_add_eq_mul]
      dsimp [z]
      congr 1
      ring

private lemma norm_stdAddChar_small_of_small_dyadic {a : ZMod M} (m : ℕ)
    (h : ∀ j ≤ m, ‖ZMod.stdAddChar (((2 : ℕ) ^ j) • a) - 1‖ ≤ 1 / 32) :
    ‖ZMod.stdAddChar a - 1‖ ≤ (2 / 3 : ℝ) ^ m / 32 := by
  induction m generalizing a with
  | zero =>
    simpa only [pow_zero, one_nsmul] using h 0 le_rfl
  | succ m ih =>
    have ha : ‖ZMod.stdAddChar a - 1‖ ≤ 1 / 32 := by
      simpa only [pow_zero, one_nsmul] using h 0 (Nat.zero_le _)
    have hb : ‖ZMod.stdAddChar ((2 : ℕ) • a) - 1‖ ≤ (2 / 3 : ℝ) ^ m / 32 := by
      apply ih
      intro j hj
      rw [← mul_nsmul, mul_comm (2 : ℕ), ← pow_succ]
      exact h _ (Nat.succ_le_succ hj)
    have hd := (norm_stdAddChar_double_ge ha).trans hb
    rw [pow_succ]
    linarith only [hd, show (2 / 3 : ℝ) ^ m * (2 / 3) / 32 =
      (2 / 3 : ℝ) * ((2 / 3 : ℝ) ^ m / 32) by ring]

private lemma exists_many_simultaneous_linear_phase_returns {I : Type*} (I₀ : Finset I)
    (A : Finset (ZMod M)) (hA : A.Nonempty) (ℓ : I → ZMod M → ZMod M)
    (hsub : ∀ i ∈ I₀, ∀ a ∈ A, ∀ b ∈ A, ℓ i (a - b) = ℓ i a - ℓ i b)
    (m : ℕ) :
    ∃ D : Finset (ZMod M), D ⊆ A - A ∧ A.card ≤ 32768 ^ (I₀.card * (m + 1)) * D.card ∧
      ∀ i ∈ I₀, ∀ d ∈ D, ‖ZMod.stdAddChar (ℓ i d) - 1‖ ≤ (2 / 3 : ℝ) ^ m / 32 := by
  let T := I₀ ×ˢ Finset.range (m + 1)
  let g (p : I × ℕ) (x : ZMod M) := ZMod.stdAddChar (((2 : ℕ) ^ p.2) • ℓ p.1 x)
  obtain ⟨A', hA', hcard, hphase⟩ := exists_simultaneous_bins A g T.toList
    (fun _ _ _ _ => (norm_stdAddChar _).le)
  have hA'ne : A'.Nonempty := by
    by_contra! h
    rw [h, Finset.card_empty, mul_zero] at hcard
    exact (Nat.not_lt_of_ge hcard) hA.card_pos
  obtain ⟨x₀, hx₀⟩ := hA'ne
  let D := A'.image (fun x => x - x₀)
  have hDcard : D.card = A'.card := Finset.card_image_of_injective _ (fun x y h => sub_left_injective h)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.sub_mem_sub (hA' hx) (hA' hx₀)
  · rw [hDcard]
    simpa only [Finset.length_toList, T, Finset.card_product, Finset.card_range] using hcard
  · intro i hi d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    apply norm_stdAddChar_small_of_small_dyadic m
    intro j hj
    have hj' : (i, j) ∈ T.toList :=
      Finset.mem_toList.mpr (Finset.mem_product.mpr ⟨hi, Finset.mem_range.mpr (Nat.lt_succ_of_le hj)⟩)
    rw [hsub i hi x (hA' hx) x₀ (hA' hx₀), nsmul_sub, norm_stdAddChar_sub_one]
    exact hphase (i, j) hj' x hx x₀ hx₀

end LinearPhaseRecurrence

private lemma localQuadraticBilinear_sub_right {N : ℕ} {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)}
    {x a b : ZMod (2 * N + 1)} (h : φ (a - b) = φ a - φ b) :
    localQuadraticBilinear φ x (a - b) = localQuadraticBilinear φ x a - localQuadraticBilinear φ x b := by
  unfold localQuadraticBilinear
  rw [h]
  ring

private lemma exists_many_bilinear_phase_returns {N : ℕ} {I : Type*}
    (I₀ : Finset I) (Ω : Finset (ZMod (2 * N + 1))) {r : ℝ} (hr : 0 ≤ r)
    (hr₂ : r + r ≤ 1 / 2) (φ : I → ZMod (2 * N + 1) → ZMod (2 * N + 1))
    (x : ZMod (2 * N + 1))
    (hadd : ∀ i ∈ I₀, ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ i (a + b) = φ i a + φ i b)
    (m : ℕ) :
    ∃ D : Finset (ZMod (2 * N + 1)), D ⊆ bohrSet Ω (r + r) ∧
      (bohrSet Ω r).card ≤ 32768 ^ (I₀.card * (m + 1)) * D.card ∧
      ∀ i ∈ I₀, ∀ d ∈ D,
        ‖ZMod.stdAddChar (localQuadraticBilinear (φ i) x d) - 1‖ ≤ (2 / 3 : ℝ) ^ m / 32 := by
  let A := bohrSet Ω r
  have hA : A.Nonempty := bohrSet_nonempty Ω hr
  have hsub (i : I) (hi : i ∈ I₀) (a : ZMod (2 * N + 1)) (ha : a ∈ A)
      (b : ZMod (2 * N + 1)) (hb : b ∈ A) :
      localQuadraticBilinear (φ i) x (a - b) =
        localQuadraticBilinear (φ i) x a - localQuadraticBilinear (φ i) x b := by
    apply localQuadraticBilinear_sub_right
    have hw : a - b + b ∈ bohrSet Ω (1 / 2) := by
      rw [sub_add_cancel]
      exact bohrSet_mono (by linarith) ha
    have h := hadd i hi (a - b) (bohrSet_mono hr₂ (diff_mem_bohrSet ha hb))
      b (bohrSet_mono (by linarith) hb) hw
    rw [sub_add_cancel] at h
    linear_combination -h
  obtain ⟨D, hD, hc, hret⟩ := exists_many_simultaneous_linear_phase_returns I₀ A hA
    (fun i => localQuadraticBilinear (φ i) x) hsub m
  refine ⟨D, hD.trans ?_, hc, hret⟩
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hd
  exact diff_mem_bohrSet ha hb

private lemma localQuadratic_nsmul {N : ℕ}
    {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)} {a : ZMod (2 * N + 1)} {n : ℕ}
    (h : φ (n • a) = n • φ a) :
    localQuadratic φ (n • a) = n ^ 2 • localQuadratic φ a := by
  unfold localQuadratic
  rw [h]
  simp only [nsmul_eq_mul, Nat.cast_pow]
  ring

private lemma localQuadraticBilinear_nsmul_right {N : ℕ}
    {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)} {x a : ZMod (2 * N + 1)} {n : ℕ}
    (h : φ (n • a) = n • φ a) :
    localQuadraticBilinear φ x (n • a) = n • localQuadraticBilinear φ x a := by
  unfold localQuadraticBilinear
  rw [h]
  simp only [nsmul_eq_mul]
  ring

private lemma square_phase_returns_from_bounded_multiples {N L : ℕ} (hL : 0 < L)
    {I : Type*} (I₀ : Finset I) (Ω A : Finset (ZMod (2 * N + 1))) {r ε : ℝ}
    (hr : 0 ≤ r) (hLr : (L : ℝ) * r ≤ 1 / 2) (hA : A ⊆ bohrSet Ω r)
    (φ : I → ZMod (2 * N + 1) → ZMod (2 * N + 1)) (z : I → ZMod (2 * N + 1))
    (hadd : ∀ i ∈ I₀, ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ i (a + b) = φ i a + φ i b)
    (_hε : 0 ≤ ε)
    (hlinear : ∀ x ∈ A, ∀ i ∈ I₀,
      ‖ZMod.stdAddChar (localQuadraticBilinear (φ i) (z i) x) - 1‖ ≤ ε / (L : ℝ))
    (hsquare : ∀ x ∈ A, ∃ n ∈ Finset.Icc 1 L, ∀ i ∈ I₀,
      ‖ZMod.stdAddChar (n ^ 2 • localQuadratic (φ i) x) - 1‖ ≤ ε) :
    ∃ D : Finset (ZMod (2 * N + 1)), D ⊆ bohrSet Ω ((L : ℝ) * r) ∧ A.card ≤ L ^ 2 * D.card ∧
      ∀ d ∈ D, ∀ i ∈ I₀,
        ‖ZMod.stdAddChar (localQuadratic (φ i) d) - 1‖ ≤ ε ∧
        ‖ZMod.stdAddChar (localQuadraticBilinear (φ i) (z i) d) - 1‖ ≤ ε := by
  classical
  let Q := Finset.Icc 1 L
  let E (n : ℕ) := A.filter (fun x => ∀ i ∈ I₀,
    ‖ZMod.stdAddChar (n ^ 2 • localQuadratic (φ i) x) - 1‖ ≤ ε)
  have hQ : Q.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩⟩
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image Q (fun n => (E n).card) hQ
  have hn₁ : 0 < n := (Finset.mem_Icc.mp hn).1
  have hn₂ : n ≤ L := (Finset.mem_Icc.mp hn).2
  let D := (E n).image (fun x => n • x)
  have hcover : A ⊆ Q.biUnion E := by
    intro x hx
    obtain ⟨m, hm, hx'⟩ := hsquare x hx
    exact Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_filter.mpr ⟨hx, hx'⟩⟩
  have hCount : A.card ≤ L * (E n).card := by
    calc
      _ ≤ (Q.biUnion E).card := Finset.card_le_card hcover
      _ ≤ Q.card * (E n).card := Finset.card_biUnion_le_card_mul Q E _ hmax
      _ = _ := by simp [Q]
  have hLoss : A.card ≤ L ^ 2 * D.card := by
    calc
      _ ≤ L * (E n).card := hCount
      _ ≤ L * (n * D.card) := Nat.mul_le_mul_left _ (card_le_mul_card_nsmul_image (E n) hn₁)
      _ ≤ L * (L * D.card) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hn₂)
      _ = _ := by ring
  have hnR : (n : ℝ) ≤ L := by exact_mod_cast hn₂
  have hnscale : (n : ℝ) * r ≤ (L : ℝ) * r := mul_le_mul_of_nonneg_right hnR hr
  refine ⟨D, ?_, hLoss, ?_⟩
  · intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact bohrSet_mono hnscale (nsmul_mem_scaled_bohr Ω (hA (Finset.mem_filter.mp hx).1) n)
  · intro d hd i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hxA, hx'⟩ := Finset.mem_filter.mp hx
    have hφ := localAdditive_nsmul_on_bohr Ω hr (φ i) (hadd i hi)
      (hA hxA) n (hnscale.trans hLr)
    constructor
    · rw [localQuadratic_nsmul hφ]
      exact hx' i hi
    · rw [localQuadraticBilinear_nsmul_right hφ]
      calc
        _ ≤ (n : ℝ) * ‖ZMod.stdAddChar (localQuadraticBilinear (φ i) (z i) x) - 1‖ :=
          norm_stdAddChar_nsmul_sub_one_le _ _
        _ ≤ (L : ℝ) * (ε / (L : ℝ)) :=
          mul_le_mul hnR (hlinear x hxA i hi) (norm_nonneg _) (by positivity)
        _ = _ := by
          have h : 0 < (L : ℝ) := by exact_mod_cast hL
          field_simp

private lemma floor_eq_of_abs_sub_le_and_margin {a b μ : ℝ} (hab : |b - a| ≤ μ)
    (hlo : (⌊a⌋ : ℝ) + μ ≤ a) (hhi : a + μ < (⌊a⌋ : ℝ) + 1) : ⌊b⌋ = ⌊a⌋ := by
  apply Int.floor_eq_iff.mpr
  rcases abs_le.mp hab with ⟨h₁, h₂⟩
  constructor <;> linarith only [hlo, hhi, h₁, h₂]

private lemma quadratic_phase_floor_stays_constant {N : ℕ}
    (Ω : Finset (ZMod (2 * N + 1))) {φ : ZMod (2 * N + 1) → ZMod (2 * N + 1)}
    {x d : ZMod (2 * N + 1)} (hx : x ∈ bohrSet Ω (1 / 8)) (hd : d ∈ bohrSet Ω (1 / 16))
    (hadd : ∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h₁ : ‖ZMod.stdAddChar (localQuadraticBilinear φ x d) - 1‖ ≤ ε)
    (h₂ : ‖ZMod.stdAddChar (localQuadratic φ d) - 1‖ ≤ ε)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (ω L : ℝ) (hL : 0 ≤ L)
    (hlo : let v := ω + L * (c * ZMod.stdAddChar (localQuadratic φ x)).re
      (⌊v⌋ : ℝ) + L * (12 * ε) ≤ v)
    (hhi : let v := ω + L * (c * ZMod.stdAddChar (localQuadratic φ x)).re
      v + L * (12 * ε) < (⌊v⌋ : ℝ) + 1)
    {n : ℕ} (hn : n ≤ 3) :
    ⌊ω + L * (c * ZMod.stdAddChar (localQuadratic φ (x + n • d))).re⌋ =
      ⌊ω + L * (c * ZMod.stdAddChar (localQuadratic φ x)).re⌋ := by
  let z := ZMod.stdAddChar (localQuadratic φ x)
  let z' := ZMod.stdAddChar (localQuadratic φ (x + n • d))
  have hNear : ‖z' - z‖ ≤ 12 * ε := by
    have h := norm_phase_progression_le Ω hx hd hadd hn h₁ h₂
    have hn' : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    have hn₂ : (((n ^ 2 : ℕ) : ℝ)) ≤ 9 := by
      exact_mod_cast (pow_le_pow_left' hn 2 : n ^ 2 ≤ 3 ^ 2)
    refine h.trans ?_
    have h' := mul_le_mul_of_nonneg_right hn' hε
    have h'' := mul_le_mul_of_nonneg_right hn₂ hε
    linarith only [h', h'']
  have hRe : |(c * z').re - (c * z).re| ≤ 12 * ε := by
    rw [← Complex.sub_re, ← mul_sub]
    exact (Complex.abs_re_le_norm _).trans (by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans hNear)
  apply floor_eq_of_abs_sub_le_and_margin _ hlo hhi
  change |(ω + L * (c * z').re) - (ω + L * (c * z).re)| ≤ L * (12 * ε)
  rw [show (ω + L * (c * z').re) - (ω + L * (c * z).re) =
    L * ((c * z').re - (c * z).re) by ring, abs_mul, abs_of_nonneg hL]
  exact mul_le_mul_of_nonneg_left hRe hL

private lemma grid_shift_near_integer_unique {m j k : ℕ} (hm : 0 < m)
    (hj : j < m) (hk : k < m) (u : ℝ) {a b : ℤ}
    (ha : |u + (j : ℝ) / m - (a : ℝ)| ≤ 1 / (4 * (m : ℝ)))
    (hb : |u + (k : ℝ) / m - (b : ℝ)| ≤ 1 / (4 * (m : ℝ))) : j = k := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hv : |u + (j : ℝ) / m - (a : ℝ) - (u + (k : ℝ) / m - (b : ℝ))| ≤ 2 * (1 / (4 * (m : ℝ))) := by
    have h := abs_sub_le (u + (j : ℝ) / m - (a : ℝ)) 0 (u + (k : ℝ) / m - (b : ℝ))
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith only [h, ha, hb]
  let e : ℤ := (j : ℤ) - (k : ℤ) - (m : ℤ) * (a - b)
  have he : (e : ℝ) = (m : ℝ) *
      (u + (j : ℝ) / m - (a : ℝ) - (u + (k : ℝ) / m - (b : ℝ))) := by
    unfold e
    push_cast
    field_simp
    ring
  have hE : |(e : ℝ)| ≤ 1 / 2 := by
    rw [he, abs_mul, abs_of_nonneg hm'.le]
    refine (mul_le_mul_of_nonneg_left hv hm'.le).trans_eq ?_
    field_simp
    norm_num
  have he₀ : e = 0 := by
    by_contra! h
    have h' : e ≤ -1 ∨ 1 ≤ e := by omega
    rcases h' with hneg | hpos
    · have hn : (e : ℝ) ≤ -1 := by exact_mod_cast hneg
      linarith only [hn, (abs_le.mp hE).1]
    · have hp : (1 : ℝ) ≤ e := by exact_mod_cast hpos
      linarith only [hp, (abs_le.mp hE).2]
  have hJk : (j : ℝ) - (k : ℝ) = (m : ℝ) * ((a : ℝ) - (b : ℝ)) := by
    have h : (e : ℝ) = 0 := by exact_mod_cast he₀
    unfold e at h
    push_cast at h
    linarith only [h]
  have hj' : (j : ℝ) < m := by exact_mod_cast hj
  have hk' : (k : ℝ) < m := by exact_mod_cast hk
  rcases lt_trichotomy a b with hab | hab | hba
  · have hab' : (a : ℝ) - (b : ℝ) ≤ -1 := by
      exact_mod_cast (show a - b ≤ -1 by omega)
    have h := mul_le_mul_of_nonneg_left hab' hm'.le
    linarith only [h, hJk, hk', Nat.cast_nonneg (α := ℝ) j]
  · have h : (j : ℝ) = (k : ℝ) := by
      simp only [hab, sub_self, mul_zero] at hJk
      exact sub_eq_zero.mp hJk
    exact_mod_cast h
  · have hab' : (1 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by
      exact_mod_cast (show 1 ≤ a - b by omega)
    have h := mul_le_mul_of_nonneg_left hab' hm'.le
    linarith only [h, hJk, hj', Nat.cast_nonneg (α := ℝ) k]

private lemma exists_common_grid_shift {X I : Type*} (A : Finset X) (I₀ : Finset I)
    (u : I → X → ℝ) (m : ℕ) (hm : 0 < m) :
    ∃ j < m, ∃ B ⊆ A, m * B.card ≤ A.card * I₀.card ∧
      ∀ x ∈ A, x ∉ B → ∀ i ∈ I₀,
        let v := u i x + (j : ℝ) / m
        (⌊v⌋ : ℝ) + 1 / (4 * (m : ℝ)) ≤ v ∧
          v + 1 / (4 * (m : ℝ)) < (⌊v⌋ : ℝ) + 1 := by
  classical
  let T := Finset.range m
  let μ := 1 / (4 * (m : ℝ))
  let R (x : X) (j : ℕ) :=
    ∃ i ∈ I₀, ∃ a : ℤ, |u i x + (j : ℝ) / m - (a : ℝ)| ≤ μ
  have hRows (x : X) :
      (leftNeighbors T (fun j x => R x j) x).card ≤ I₀.card := by
    let F (i : I) : Finset ℕ := T.filter (fun j : ℕ => ∃ a : ℤ, |u i x + (j : ℝ) / m - (a : ℝ)| ≤ μ)
    have hF (i : I) : (F i).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj k hk
      obtain ⟨hjT, a, ha⟩ := Finset.mem_filter.mp hj
      obtain ⟨hkT, b, hb⟩ := Finset.mem_filter.mp hk
      exact grid_shift_near_integer_unique hm (Finset.mem_range.mp hjT) (Finset.mem_range.mp hkT) (u i x) ha hb
    have hs : leftNeighbors T (fun j x => R x j) x ⊆ I₀.biUnion F := by
      intro j hj
      obtain ⟨hjT, i, hi, a, ha⟩ := mem_leftNeighbors.mp hj
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hjT, a, ha⟩⟩
    have h := (Finset.card_le_card hs).trans (Finset.card_biUnion_le_card_mul I₀ F 1 (fun i _ => hF i))
    simpa only [mul_one] using h
  have hT : T.Nonempty := ⟨0, Finset.mem_range.mpr hm⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image T (fun j => (leftNeighbors A R j).card) hT
  let B := leftNeighbors A R j
  have hjm : j < m := Finset.mem_range.mp hj
  have hB : B ⊆ A := fun x hx => (mem_leftNeighbors.mp hx).1
  have hc : m * B.card ≤ A.card * I₀.card := by
    calc
      _ = ∑ _ ∈ T, B.card := by simp [T]
      _ ≤ ∑ k ∈ T, (leftNeighbors A R k).card := Finset.sum_le_sum hmin
      _ = (relPairs A T R).card := (card_relPairs_eq_sum_right A T R).symm
      _ = ∑ x ∈ A, (leftNeighbors T (fun k x => R x k) x).card := card_relPairs_eq_sum_left A T R
      _ ≤ ∑ _ ∈ A, I₀.card := Finset.sum_le_sum fun x _ => hRows x
      _ = _ := by simp
  refine ⟨j, hjm, B, hB, hc, ?_⟩
  intro x hx hxB i hi
  let v := u i x + (j : ℝ) / m
  have hn (a : ℤ) : μ < |v - (a : ℝ)| := by
    apply lt_of_not_ge
    intro ha
    exact hxB (mem_leftNeighbors.mpr ⟨hx, i, hi, a, ha⟩)
  have h₁ := hn ⌊v⌋
  have h₂ := hn (⌊v⌋ + 1)
  rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le v))] at h₁
  have hlt := Int.lt_floor_add_one v
  push_cast at h₂
  rw [abs_of_nonpos (by linarith only [hlt] : v - ((⌊v⌋ : ℝ) + 1) ≤ 0)] at h₂
  change (⌊v⌋ : ℝ) + μ ≤ v ∧ v + μ < (⌊v⌋ : ℝ) + 1
  exact ⟨by linarith only [h₁], by linarith only [h₂]⟩

private def LargeQuadraticChart (N : ℕ) (δ : ℝ) (f : ℤ → ℝ) : Prop :=
  ∃ Ω Λ : Finset (ZMod (2 * N + 1)), ∃ φ : ZMod (2 * N + 1) → ZMod (2 * N + 1),
    ∃ x₀ z : ZMod (2 * N + 1), ∃ r : ℝ,
    let D := bohrSet (Ω ∪ Λ) r
    0 < r ∧ r ≤ 1 / 16 ∧ z ∈ bohrSet Ω (1 / 16) ∧
    Real.sqrt ((2 * N + 1 : ℕ) : ℝ) ≤ (D.card : ℝ) ∧
    (∀ a ∈ bohrSet Ω (1 / 2), ∀ b ∈ bohrSet Ω (1 / 2),
      a + b ∈ bohrSet Ω (1 / 2) → φ (a + b) = φ a + φ b) ∧
    quadraticPairRate δ / 2 * (D.card : ℝ) ≤
      ‖∑ d ∈ D, (periodize N f (x₀ + (z + d)) : ℂ) * ZMod.stdAddChar (-localQuadratic φ (z + d))‖

private lemma exists_large_quadraticChart_of_pair :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      2 * C ≤ δ ^ (187264 * 16 : ℕ) * Real.log ((2 * N + 1 : ℕ) : ℝ) →
      ∀ f : ℤ → ℝ, (∀ x, |f x| ≤ 1) →
      QuadraticPairStructure N δ (quadraticPairParameters δ).1 (quadraticPairParameters δ).2 f →
      LargeQuadraticChart N δ f := by
  obtain ⟨C, hC, hchart⟩ := exists_quantitative_localQuadraticCorrelation
  refine ⟨C, hC, ?_⟩
  intro N δ hδ hδ₁ hScale f hf hpair
  obtain ⟨Ω, Λ, φ, x₀, z, r, hr, hr₁, hz, hsize, hadd, hcorr⟩ := hchart N δ hδ hδ₁ f hf hpair
  let D := bohrSet (Ω ∪ Λ) r
  refine ⟨Ω, Λ, φ, x₀, z, r, hr, hr₁, hz, ?_, hadd, hcorr⟩
  have hD : D.Nonempty := bohrSet_nonempty (Ω ∪ Λ) hr.le
  apply sqrt_card_le_of_log_ratio hD
  have hx : C ≤ δ ^ (187264 * 16 : ℕ) * (Real.log ((2 * N + 1 : ℕ) : ℝ) / 2) := by
    rw [← mul_div_assoc, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm C 2]
    exact hScale
  exact le_of_mul_le_mul_left (hsize.trans hx) (pow_pos hδ _)

private lemma scale_bound_of_large_quadratic_chart (K : ℕ) (κ : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) :
    ∃ p : ℕ, 0 < p ∧ ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, max 3 N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → S.Nonempty →
        (let g := indicatorCyclic (cyclicLift N S)
         ∑ a, ∑ d, g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) = (S.card : ℝ)) →
        (let δ := κ * density N S ^ K
         QuadraticPairStructure N δ (quadraticPairParameters δ).1 (quadraticPairParameters δ).2
           (balanced N S) ∧ LargeQuadraticChart N δ (balanced N S)) →
        (density N S) ^ p * Real.log (N : ℝ) ≤ B := by
  sorry

private lemma scale_bound_of_quadratic_pair_structure (K : ℕ) (κ : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) :
    ∃ p : ℕ, 0 < p ∧ ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, max 3 N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → S.Nonempty →
        (let g := indicatorCyclic (cyclicLift N S)
         ∑ a, ∑ d, g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) = (S.card : ℝ)) →
        (let δ := κ * density N S ^ K
         QuadraticPairStructure N δ (quadraticPairParameters δ).1 (quadraticPairParameters δ).2
           (balanced N S)) →
        (density N S) ^ p * Real.log (N : ℝ) ≤ B := by
  obtain ⟨C, hC, hchart⟩ := exists_large_quadraticChart_of_pair
  obtain ⟨p₀, hp₀, B₀, hB₀, N₀, hlarge⟩ := scale_bound_of_large_quadratic_chart K κ hκ hκ₁
  let q := 187264 * 16
  let p₁ := K * q
  let p := max p₀ p₁
  let B := max B₀ (2 * C / κ ^ q)
  refine ⟨p, lt_of_lt_of_le hp₀ (le_max_left _ _), B, lt_of_lt_of_le hB₀ (le_max_left _ _), N₀, ?_⟩
  intro N hN S hS hS₀ hcount hpair
  let d := density N S
  let δ := κ * d ^ K
  have hN₁ : 1 ≤ N := by omega
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN₁)
  have hd : 0 < d := div_pos (by exact_mod_cast hS₀.card_pos) (by exact_mod_cast hN₁)
  have hd₁ : d ≤ 1 := (density_mem_unitInterval hS).2
  have hδ : 0 < δ := mul_pos hκ (pow_pos hd _)
  have hδ₁ : δ ≤ 1 := by
    unfold δ
    simpa only [mul_one] using mul_le_mul hκ₁ (pow_le_one₀ hd.le hd₁) (pow_nonneg hd.le _) zero_le_one
  by_cases hSmall : δ ^ q * Real.log ((2 * N + 1 : ℕ) : ℝ) ≤ 2 * C
  · have hle : d ^ p₁ * Real.log (N : ℝ) ≤ 2 * C / κ ^ q := by
      apply (le_div_iff₀ (pow_pos hκ q)).2
      have hLog : Real.log (N : ℝ) ≤ Real.log ((2 * N + 1 : ℕ) : ℝ) := by
        apply Real.log_le_log (by exact_mod_cast (show 0 < N by omega))
        exact_mod_cast (show N ≤ 2 * N + 1 by omega)
      calc
        _ = δ ^ q * Real.log (N : ℝ) := by unfold δ p₁; rw [mul_pow, pow_mul]; ring
        _ ≤ δ ^ q * Real.log ((2 * N + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hLog (pow_nonneg hδ.le _)
        _ ≤ _ := hSmall
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hd.le hd₁ (le_max_right p₀ p₁)) hlog).trans
      (hle.trans (le_max_right _ _))
  · have hQ := hchart N δ hδ hδ₁ (le_of_not_ge hSmall) (balanced N S) (abs_balanced_le_one hS) hpair
    have he := hlarge N hN S hS hS₀ hcount ⟨hpair, hQ⟩
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hd.le hd₁ (le_max_left p₀ p₁)) hlog).trans
      (he.trans (le_max_left _ _))


private lemma scale_bound_of_regular_local_frequency_structure (K : ℕ) (κ : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) :
    ∃ p : ℕ, 0 < p ∧ ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, max 3 N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → S.Nonempty →
        (let g := indicatorCyclic (cyclicLift N S)
         ∑ a, ∑ d, g a * g (a + d) * g (a + 2 * d) * g (a + 3 * d) = (S.card : ℝ)) →
        (∀ η : ℝ, 0 < η → ∀ m : ℕ, 1 ≤ (m : ℝ) * η →
          RegularLocalFrequencyStructure N (κ * density N S ^ K) η m (balanced N S)) →
        (density N S) ^ p * Real.log (N : ℝ) ≤ B := by
  obtain ⟨p, hp, B, hB, N₀, hscale⟩ := scale_bound_of_quadratic_pair_structure K κ hκ hκ₁
  refine ⟨p, hp, B, hB, N₀, ?_⟩
  intro N hN S hS hSne hcount hstructure
  have hN₁ : 1 ≤ N := by omega
  have hδ : 0 < κ * density N S ^ K := by
    have hd : 0 < density N S := div_pos (by exact_mod_cast hSne.card_pos) (by exact_mod_cast hN₁)
    positivity
  exact hscale N hN S hS hSne hcount <|
    quadraticPair_of_local_frequency hN₁ hδ (abs_balanced_le_one hS)
      (hstructure 1 (by norm_num) 1 (by norm_num))

end Erdos3Structured

open Erdos3Structured in
theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_green_tao_R2.H2 := by
  intro K κ hκ
  let κ' := min κ 1
  have hκ' : 0 < κ' := lt_min hκ (by norm_num)
  have hκ'₁ : κ' ≤ 1 := min_le_right _ _
  obtain ⟨p, hp, B, hB, N₀, hscale⟩ := scale_bound_of_regular_local_frequency_structure K κ' hκ' hκ'₁
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨(p : ℝ)⁻¹, by positivity, B ^ ((p : ℝ)⁻¹), by positivity, max 3 N₀, ?_⟩
  intro N hN S hS hfree hlarge
  have hN₃ : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hN₁ : 1 ≤ N := by omega
  by_cases hSne : S.Nonempty
  · apply log_density_bound_from_scale hN₃ hp hB
    apply hscale N hN S hS hSne (cyclic_four_ap_sum_of_free hS hfree)
    have hd : 0 < density N S := by
      unfold density
      exact div_pos (by exact_mod_cast hSne.card_pos) (by exact_mod_cast hN₁)
    have hLargeCube : κ * density N S ^ K * (N : ℝ) ^ 4 ≤ cubeSum N (balanced N S) :=
      le_of_not_gt hlarge
    have hLargeCube' : κ' * density N S ^ K * (N : ℝ) ^ 4 ≤ cubeSum N (balanced N S) := by
      have hκ'κ : κ' ≤ κ := min_le_left _ _
      exact (by gcongr : κ' * density N S ^ K * (N : ℝ) ^ 4 ≤ κ * density N S ^ K * (N : ℝ) ^ 4).trans
        hLargeCube
    intro η hη m hm
    exact large_cube_has_regular_local_frequency_structure (fun x hx => balanced_eq_zero hS hx)
      (abs_balanced_le_one hS) hN₁ (mul_pos hκ' (pow_pos hd _)) hLargeCube' hη m hm
  · have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN₁)
    rw [Finset.not_nonempty_iff_eq_empty.mp hSne, Finset.card_empty, Nat.cast_zero]
    positivity
