import FormalConjectures.GreensOpenProblems.«65»
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Combination

/-!
# Ben Green's Open Problem 65 -- prime minus one

Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/65.lean:85
(declaration Green65.green_65.variants.prime_minus_one).

## Credit
- Finite Fourier reduction on ZMod (2*N+1) adapted from @connoranderson
  (PR #17898, https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17898,
   file reductions/Green65.green_65.variants.prime_minus_one.R1.lean).
- Zero Fourier mode quadratic form lower bound adapted from @amp2600
  (PR #18378, https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18378,
   file proofs/Green65.green_65.variants.prime_minus_one.R1.H2.lean).
- Hahn-Banach minimax duality reduction from Green's Theorem 1.2 (arXiv:2206.08001, Section 2)
  to the dual finite-measure shifted-prime cosine lower bound is original.
-/

namespace OMA.Green65PrimeMinusOne

open Filter Finset
open scoped Pointwise ComplexConjugate

lemma char_conj {M : ℕ} [NeZero M] (x : ZMod M) :
    ZMod.stdAddChar (-x) = conj (ZMod.stdAddChar x) := by
  change (↑(ZMod.toCircle (-x)) : ℂ) = conj (↑(ZMod.toCircle x) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma symmetrized_spectrum {M : ℕ} [NeZero M] (a : ZMod M → ℝ) (r : ZMod M) :
    ZMod.dft (fun u => (((a u + a (-u)) / 2 : ℝ) : ℂ)) r =
      ((∑ j : ZMod M, a j * (ZMod.stdAddChar (j * r)).re : ℝ) : ℂ) := by
  have hneg : (∑ j : ZMod M, ZMod.stdAddChar (-(j * r)) * (a (-j) : ℂ)) =
      ∑ j : ZMod M, ZMod.stdAddChar (j * r) * (a j : ℂ) := by
    exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by simp)
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat,
    mul_div_assoc', mul_add, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hneg, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [char_conj, ← add_mul, add_comm (conj _), Complex.add_conj]
  push_cast
  ring

lemma char_to_cos {M : ℕ} [NeZero M] (d : ℕ) (r : ZMod M) :
    (ZMod.stdAddChar ((d : ZMod M) * r)).re =
      Real.cos (2 * Real.pi * d * ((r.val : ℝ) / M)) := by
  have he : (d : ZMod M) * r = (((d : ℤ) * (r.val : ℤ) : ℤ) : ZMod M) := by simp
  rw [he, ZMod.stdAddChar_coe, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

lemma kernel_of_cosine (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ p ≤ N)
    (c : ℝ) (b : ℕ → ℝ) (hmean : c + ∑ p ∈ P, b p = 1)
    (hpos : ∀ t : ℝ, 0 ≤ c + ∑ p ∈ P, b p * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t)) :
    ∃ K : ZMod (2 * N + 1) → ℝ,
      (∑ x, K x) = 1 ∧
      (∀ r, ∃ t : ℝ, 0 ≤ t ∧ ZMod.dft (fun x => (K x : ℂ)) r = (t : ℂ)) ∧
      (∀ x, x ≠ 0 → K x ≠ 0 → ∃ p : ℕ, p.Prime ∧ p ≤ N ∧
        (x = (p : ZMod (2 * N + 1)) - 1 ∨ x = -((p : ZMod (2 * N + 1)) - 1))) ∧
      K 0 = c := by
  classical
  let d (p : ℕ) : ZMod (2 * N + 1) := ↑(p - 1)
  let a (x : ZMod (2 * N + 1)) :=
    (if x = 0 then c else 0) + ∑ p ∈ P, if d p = x then b p else 0
  have hw (f : ZMod (2 * N + 1) → ℝ) :
      ∑ x, a x * f x = c * f 0 + ∑ p ∈ P, b p * f (d p) := by
    simp only [a, add_mul, Finset.sum_add_distrib, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm (s := univ) (t := P)]
    simp
  have hd (p : ℕ) (hp : p ∈ P) : d p ≠ 0 := by
    have h2 := (hP p hp).1.two_le
    have hn := (hP p hp).2
    intro h
    have := congrArg ZMod.val h
    rw [show (d p).val = p - 1 from ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at this
    omega
  have haz : a 0 = c := by simp [a, Finset.sum_eq_zero (fun p hp => if_neg (hd p hp))]
  have hs (x : ZMod (2 * N + 1)) (hx : x ≠ 0) (h : a x ≠ 0) : ∃ p ∈ P, d p = x := by
    by_contra! hn
    exact h (by simp [a, hx, Finset.sum_eq_zero (fun p hp => if_neg (hn p hp))])
  refine ⟨fun x => (a x + a (-x)) / 2, ?_, ?_, ?_, ?_⟩
  · have ha : ∑ x, a x = 1 := by simpa using (hw (fun _ => 1)).trans (by simpa using hmean)
    have hf : ∑ x, a (-x) = ∑ x, a x := Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
    rw [← Finset.sum_div, Finset.sum_add_distrib, hf, ha]
    norm_num
  · intro r
    have hc := hw (fun x => (ZMod.stdAddChar (x * r)).re)
    simp only [zero_mul, AddChar.map_zero_eq_one, Complex.one_re, mul_one, d, char_to_cos] at hc
    refine ⟨_, hpos ((r.val : ℝ) / (2 * N + 1 : ℕ)), ?_⟩
    rw [symmetrized_spectrum, hc]
  · intro x hx hK
    have hn : a x ≠ 0 ∨ a (-x) ≠ 0 := by
      by_contra! h
      simp [h.1, h.2] at hK
    rcases hn with h | h
    · obtain ⟨p, hp, hpx⟩ := hs x hx h
      refine ⟨p, (hP p hp).1, (hP p hp).2, Or.inl ?_⟩
      simpa [d, Nat.cast_sub (hP p hp).1.one_le] using hpx.symm
    · obtain ⟨p, hp, hpx⟩ := hs (-x) (neg_ne_zero.mpr hx) h
      refine ⟨p, (hP p hp).1, (hP p hp).2, Or.inr ?_⟩
      simpa [d, Nat.cast_sub (hP p hp).1.one_le] using congrArg Neg.neg hpx.symm
  · simp [haz]

lemma zero_mode_quadratic_bound (M : ℕ) [NeZero M] (A : Finset (ZMod M)) (K : ZMod M → ℝ)
    (hsum : (∑ x, K x) = 1)
    (hpos : ∀ r, ∃ t : ℝ, 0 ≤ t ∧ ZMod.dft (fun x => (K x : ℂ)) r = (t : ℂ)) :
    (A.card : ℝ) ^ 2 ≤ (M : ℝ) * ∑ x ∈ A, ∑ y ∈ A, K (x - y) := by
  classical
  choose t ht0 htK using hpos
  have hinv : ∀ z : ZMod M,
      (M : ℂ) * (K z : ℂ) = ∑ r, ZMod.stdAddChar (r * z) * (t r : ℂ) := by
    intro z
    have h := congrFun (ZMod.dft_dft (fun x => (K x : ℂ))) (-z)
    rw [ZMod.dft_apply] at h
    simp only [htK, smul_eq_mul, neg_neg, mul_neg] at h
    rw [← h]
  have hsplit : ∀ r x y : ZMod M, ZMod.stdAddChar (r * (x - y)) =
      ZMod.stdAddChar (r * x) * conj (ZMod.stdAddChar (r * y)) := by
    intro r x y
    rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, char_conj]
  set S : ZMod M → ℂ := fun r => ∑ x ∈ A, ZMod.stdAddChar (r * x) with hS
  have hkey : ((M : ℝ) * ∑ x ∈ A, ∑ y ∈ A, K (x - y) : ℝ) =
      ∑ r, t r * Complex.normSq (S r) := by
    apply Complex.ofReal_injective
    push_cast
    calc (M : ℂ) * ∑ x ∈ A, ∑ y ∈ A, (K (x - y) : ℂ)
        = ∑ x ∈ A, ∑ y ∈ A, (M : ℂ) * (K (x - y) : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ x ∈ A, ∑ y ∈ A, ∑ r, ZMod.stdAddChar (r * (x - y)) * (t r : ℂ) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          exact hinv (x - y)
      _ = ∑ x ∈ A, ∑ y ∈ A, ∑ r,
            (t r : ℂ) * (ZMod.stdAddChar (r * x) * conj (ZMod.stdAddChar (r * y))) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun r _ => ?_
          rw [hsplit]
          ring
      _ = ∑ x ∈ A, ∑ r, ∑ y ∈ A,
            (t r : ℂ) * (ZMod.stdAddChar (r * x) * conj (ZMod.stdAddChar (r * y))) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ r, ∑ x ∈ A, ∑ y ∈ A,
            (t r : ℂ) * (ZMod.stdAddChar (r * x) * conj (ZMod.stdAddChar (r * y))) :=
          Finset.sum_comm
      _ = ∑ r, (t r : ℂ) * (S r * conj (S r)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [hS, map_sum, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm
      _ = ∑ r, (t r : ℂ) * (Complex.normSq (S r) : ℂ) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Complex.mul_conj]
  have ht1 : t 0 = 1 := by
    have h := htK 0
    rw [ZMod.dft_apply_zero] at h
    have h' : ((∑ x, K x : ℝ) : ℂ) = (t 0 : ℂ) := by
      push_cast
      exact h
    rw [hsum] at h'
    exact_mod_cast h'.symm
  have hS0 : S 0 = ((A.card : ℝ) : ℂ) := by
    simp [hS]
  have hle : t 0 * Complex.normSq (S 0) ≤ ∑ r, t r * Complex.normSq (S r) :=
    Finset.single_le_sum (f := fun r => t r * Complex.normSq (S r))
      (fun r _ => mul_nonneg (ht0 r) (Complex.normSq_nonneg _)) (Finset.mem_univ 0)
  rw [ht1, one_mul, hS0, Complex.normSq_ofReal] at hle
  rw [← hkey] at hle
  nlinarith [hle]

lemma lift_bounded_residue {N : ℕ} {x y : ℤ} (hx : -(N : ℤ) ≤ x ∧ x ≤ N)
    (hy : -(N : ℤ) ≤ y ∧ y ≤ N)
    (h : (x : ZMod (2 * N + 1)) = (y : ZMod (2 * N + 1))) : x = y := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub x y (2 * N + 1)).mp h
  have hlt : |y - x| < ((2 * N + 1 : ℕ) : ℤ) := by
    rw [abs_lt]
    push_cast
    omega
  have hz := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega

lemma interval_image_card {N : ℕ} (A : Finset ℤ) (hA : A ⊆ Finset.Icc 1 (N : ℤ)) :
    (A.image (fun a : ℤ => (a : ZMod (2 * N + 1)))).card = A.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp (hA ha)
  obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp (hA hb)
  exact lift_bounded_residue (by constructor <;> omega) (by constructor <;> omega) hab

lemma interval_prime_witness {N : ℕ} (A : Finset ℤ) (hA : A ⊆ Finset.Icc 1 (N : ℤ))
    {a b : ZMod (2 * N + 1)}
    (ha : a ∈ A.image (fun z : ℤ => (z : ZMod (2 * N + 1))))
    (hb : b ∈ A.image (fun z : ℤ => (z : ZMod (2 * N + 1))))
    {p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hd : a - b = (p : ZMod (2 * N + 1)) - 1 ∨ a - b = -((p : ZMod (2 * N + 1)) - 1)) :
    ∃ d ∈ A - A, Green65.IsPrimeMinusOne d := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hx1, hxN⟩ := Finset.mem_Icc.mp (hA hx)
  obtain ⟨hy1, hyN⟩ := Finset.mem_Icc.mp (hA hy)
  have hp0 := hp.two_le
  have h₁ : -(N : ℤ) ≤ (p : ℤ) - 1 ∧ (p : ℤ) - 1 ≤ N := by omega
  rcases hd with hd | hd
  · refine ⟨x - y, Finset.sub_mem_sub hx hy, p, hp, ?_⟩
    exact lift_bounded_residue (by constructor <;> omega) h₁ (by push_cast; exact hd)
  · refine ⟨y - x, Finset.sub_mem_sub hy hx, p, hp, ?_⟩
    apply lift_bounded_residue (by constructor <;> omega) h₁
    push_cast
    linear_combination -hd

lemma interval_image_kernel_sum {N : ℕ} (A : Finset ℤ) (hA : A ⊆ Finset.Icc 1 (N : ℤ))
    (havoid : ¬ ∃ d ∈ A - A, Green65.IsPrimeMinusOne d)
    (K : ZMod (2 * N + 1) → ℝ)
    (hK : ∀ t, t ≠ 0 → K t ≠ 0 → ∃ p : ℕ, p.Prime ∧ p ≤ N ∧
      (t = (p : ZMod (2 * N + 1)) - 1 ∨ t = -((p : ZMod (2 * N + 1)) - 1))) :
    let S := A.image (fun z : ℤ => (z : ZMod (2 * N + 1)))
    ∑ a ∈ S, ∑ b ∈ S, K (a - b) = (A.card : ℝ) * K 0 := by
  classical
  dsimp only
  set S := A.image (fun z : ℤ => (z : ZMod (2 * N + 1)))
  have hinner (a) (ha : a ∈ S) : ∑ b ∈ S, K (a - b) = K 0 := by
    rw [Finset.sum_eq_single_of_mem a ha, sub_self]
    intro b hb hba
    by_contra hne
    obtain ⟨p, hp, hpN, hd⟩ := hK (a - b) (sub_ne_zero.mpr hba.symm) hne
    exact havoid (interval_prime_witness A hA ha hb hp hpN hd)
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  rw [show S.card = A.card from interval_image_card A hA]

/-- Reduction of Ben Green's Open Problem 65 (prime minus one) to the existence of a
nonnegative cosine polynomial supported on shifted primes with power-saving constant term
(Green 2022, Theorem 1.2). -/
lemma prime_minus_one_of_cosine_poly
    (hcert_ex : ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ (P : Finset ℕ) (c : ℝ) (b : ℕ → ℝ),
        (∀ p ∈ P, p.Prime ∧ p ≤ N) ∧ (c + ∑ p ∈ P, b p = 1) ∧
        (∀ t : ℝ, 0 ≤ c + ∑ p ∈ P, b p * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t)) ∧
        c ≤ C * (N : ℝ) ^ (-η)) :
    Green65.LargeDifferencePattern Green65.IsPrimeMinusOne := by
  classical
  obtain ⟨η, C, hη, hC, hcert⟩ := hcert_ex
  let c := min (η / 2) (1 / 2 : ℝ)
  have hc : 0 < c := lt_min (by linarith) (by norm_num)
  have hcη : c < η := lt_of_le_of_lt (min_le_left ..) (by linarith)
  refine ⟨c, hc, lt_of_le_of_lt (min_le_right ..) (by norm_num), ?_⟩
  have hgrowth := (tendsto_rpow_atTop (sub_pos.mpr hcη)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hcert, hgrowth.eventually_gt_atTop (3 * C), eventually_ge_atTop (1 : ℕ)] with
    N hK hlarge hN
  obtain ⟨P, a, b, hP, hnorm, hpospoly, ha⟩ := hK
  obtain ⟨K, hmass, hspec, hsupp, hK0⟩ := kernel_of_cosine N P hP a b hnorm hpospoly
  have hzero := hK0.le.trans ha
  intro A hA hcard
  by_contra havoid
  let S := A.image (fun a : ℤ => (a : ZMod (2 * N + 1)))
  have hsize : S.card = A.card := interval_image_card A hA
  have hdiag : ∑ x ∈ S, ∑ y ∈ S, K (x - y) = (A.card : ℝ) * K 0 :=
    interval_image_kernel_sum A hA havoid K hsupp
  have hquad := zero_mode_quadratic_bound (2 * N + 1) S K hmass hspec
  rw [hdiag, hsize] at hquad
  push_cast at hquad
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos := (Real.rpow_pos_of_pos hn (1 - c)).trans_le hcard
  have hlin : (A.card : ℝ) ≤ (2 * N + 1 : ℝ) * K 0 := by
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hquad]
  have hupper : (A.card : ℝ) ≤ (3 * C) * (N : ℝ) ^ (1 - η) := calc
    _ ≤ (2 * N + 1 : ℝ) * (C * (N : ℝ) ^ (-η)) := hlin.trans (by gcongr)
    _ ≤ (3 * N : ℝ) * (C * (N : ℝ) ^ (-η)) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = (3 * C) * (N : ℝ) ^ (1 - η) := by
      rw [sub_eq_add_neg, Real.rpow_add hn, Real.rpow_one]
      ring
  have hstrict := mul_lt_mul_of_pos_right (show 3 * C < (N : ℝ) ^ (η - c) from hlarge)
    (Real.rpow_pos_of_pos hn (1 - η))
  rw [← Real.rpow_add hn, show η - c + (1 - η) = 1 - c by ring] at hstrict
  exact (not_lt_of_ge (hcard.trans hupper)) hstrict

/-- Hahn-Banach minimax duality (Green 2022, Section 2): for fixed N and eps >= 0,
if every finitely supported probability distribution on R admits a prime p <= N whose
shifted cosine average is at least -eps, then there is a nonnegative cosine polynomial
c + sum_{p in P} b p cos(2 pi (p - 1) t) >= 0 with c + sum b p = 1 and c <= eps. -/
lemma cosine_poly_of_dual_fixed (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hdual : ∀ (ι : Type) [Fintype ι] (t : ι → ℝ) (w : ι → ℝ),
      (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
      ∃ p : ℕ, p.Prime ∧ p ≤ N ∧
        -ε ≤ ∑ i, w i * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t i)) :
    ∃ (P : Finset ℕ) (c : ℝ) (b : ℕ → ℝ),
      (∀ p ∈ P, p.Prime ∧ p ≤ N) ∧ (c + ∑ p ∈ P, b p = 1) ∧
      (∀ t : ℝ, 0 ≤ c + ∑ p ∈ P, b p * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t)) ∧
      c ≤ ε := by
  classical
  let P : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  have hP : ∀ p ∈ P, p.Prime ∧ p ≤ N := fun p hp => by
    have hp' := Finset.mem_filter.mp hp
    exact ⟨hp'.2, (Finset.mem_Icc.mp hp'.1).2⟩
  have hPmem : ∀ {p : ℕ}, p.Prime → p ≤ N → p ∈ P := fun hp hpN =>
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpN⟩, hp⟩
  let E := {p : ℕ // p ∈ P} → ℝ
  let v : ℝ → E := fun t p => Real.cos (2 * Real.pi * (p.1 - 1 : ℕ) * t)
  let U : Set E := {x : E | ∀ p, x p < -ε}
  let K : Set E := convexHull ℝ (Set.range v)
  have hU_conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab p
    change a * x p + b * y p < -ε
    have hx' : x p < -ε := hx p
    have hy' : y p < -ε := hy p
    have hmul : a * x p + b * y p < a * (-ε) + b * (-ε) := by
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        subst hb1
        linarith
      · have h1 : a * x p < a * (-ε) := mul_lt_mul_of_pos_left hx' ha'
        have h2 : b * y p ≤ b * (-ε) := mul_le_mul_of_nonneg_left hy'.le hb
        linarith
    have heq : a * (-ε) + b * (-ε) = -ε := by linear_combination (-ε) * hab
    linarith
  have hU_open : IsOpen U := by
    have hUeq : U = ⋂ p : {p : ℕ // p ∈ P}, (fun x : E => x p) ⁻¹' Set.Iio (-ε) := by
      ext x
      simp [U]
    rw [hUeq]
    exact isOpen_iInter_of_finite fun p => isOpen_Iio.preimage (continuous_apply p)
  have hK_conv : Convex ℝ K := convex_convexHull ℝ (Set.range v)
  have hdisj : Disjoint U K := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    obtain ⟨ι, hfin, w, z, hw0, hw1, hz, rfl⟩ := mem_convexHull_iff_exists_fintype.mp hxK
    choose t ht using hz
    obtain ⟨p, hp, hpN, hcos⟩ := hdual ι t w hw0 hw1
    have hpP : p ∈ P := hPmem hp hpN
    have hlt : (∑ i, w i • z i) ⟨p, hpP⟩ < -ε := hxU ⟨p, hpP⟩
    have heval : (∑ i, w i • z i) ⟨p, hpP⟩ =
        ∑ i, w i * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t i) := by
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← ht i]
      rfl
    linarith
  obtain ⟨f, s, hfU, hfK⟩ := geometric_hahn_banach_open hU_conv hU_open hK_conv hdisj
  let a : {p : ℕ // p ∈ P} → ℝ := fun p => f (Pi.single p 1)
  have hf_eq : ∀ x : E, f x = ∑ p, a p * x p := by
    intro x
    have hx : x = ∑ p, x p • Pi.single p (1 : ℝ) := by
      ext q
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have ha_nonneg : ∀ p, 0 ≤ a p := by
    intro p
    by_contra hneg
    push Not at hneg
    let x₀ : E := fun _ => -ε - 1
    let M : ℝ := max 1 ((s - f x₀) / (-a p) + 1)
    have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    let xM : E := x₀ - M • Pi.single p 1
    have hxM : xM ∈ U := by
      intro q
      change (-ε - 1) - M * ((Pi.single p (1 : ℝ) : E) q) < -ε
      by_cases hq : q = p
      · subst hq
        rw [Pi.single_eq_same]
        linarith
      · rw [Pi.single_eq_of_ne hq]
        linarith
    have hlt : f xM < s := hfU xM hxM
    have hfxM : f xM = f x₀ - M * a p := by
      simp [xM, map_sub, map_smul, smul_eq_mul, a]
    have hMge : (s - f x₀) / (-a p) + 1 ≤ M := le_max_right _ _
    have hpos_neg_a : 0 < -a p := by linarith
    have hprod : s - f x₀ + (-a p) ≤ M * (-a p) := by
      have := mul_le_mul_of_nonneg_right hMge hpos_neg_a.le
      rwa [add_mul, div_mul_cancel₀ _ hpos_neg_a.ne', one_mul] at this
    linarith
  have hS_pos : 0 < ∑ p, a p := by
    have hS_nonneg : 0 ≤ ∑ p, a p := Finset.sum_nonneg fun p _ => ha_nonneg p
    rcases eq_or_lt_of_le hS_nonneg with hS0 | hSpos
    · exfalso
      have ha0 : ∀ p, a p = 0 := fun p => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => ha_nonneg q)).mp hS0.symm
        exact this p (Finset.mem_univ p)
      have hf0 : ∀ x : E, f x = 0 := fun x => by
        rw [hf_eq]
        exact Finset.sum_eq_zero fun p _ => by simp [ha0 p]
      have hxU : (fun _ : {p : ℕ // p ∈ P} => -ε - 1) ∈ U := fun _ => by linarith
      have hvK : v 0 ∈ K := subset_convexHull ℝ (Set.range v) ⟨0, rfl⟩
      have h1 : f (fun _ => -ε - 1) < s := hfU _ hxU
      have h2 : s ≤ f (v 0) := hfK _ hvK
      rw [hf0] at h1 h2
      linarith
    · exact hSpos
  set S : ℝ := ∑ p, a p
  have hs_ge : -ε * S ≤ s := by
    by_contra hlt
    push Not at hlt
    let δ : ℝ := (-ε * S - s) / (2 * S)
    have hδ : 0 < δ := div_pos (by linarith) (by positivity)
    let xδ : E := fun _ => -ε - δ
    have hxδ : xδ ∈ U := fun _ => by linarith
    have hfxδ : f xδ = (-ε - δ) * S := by
      rw [hf_eq]
      simp only [xδ, ← Finset.sum_mul, S]
      ring
    have h1 : f xδ < s := hfU xδ hxδ
    have hδS : δ * S = (-ε * S - s) / 2 := by
      dsimp [δ]
      field_simp [hS_pos.ne']
    linarith
  let c : ℝ := ε / (1 + ε)
  let b : ℕ → ℝ := fun n => if h : n ∈ P then a ⟨n, h⟩ / (S * (1 + ε)) else 0
  have h1ε : 0 < 1 + ε := by linarith
  have hsum_b : ∑ p ∈ P, b p = 1 / (1 + ε) := by
    have h1 : ∑ p ∈ P, b p = ∑ p : {p : ℕ // p ∈ P}, a p / (S * (1 + ε)) := by
      rw [← Finset.sum_attach P]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [b, p.2]
    rw [h1, ← Finset.sum_div]
    change S / (S * (1 + ε)) = 1 / (1 + ε)
    field_simp [hS_pos.ne', h1ε.ne']
  refine ⟨P, c, b, hP, ?_, ?_, ?_⟩
  · rw [hsum_b]
    dsimp [c]
    field_simp [h1ε.ne']
    ring
  · intro t
    have hvtK : v t ∈ K := subset_convexHull ℝ (Set.range v) ⟨t, rfl⟩
    have hfvt : -ε * S ≤ ∑ p, a p * Real.cos (2 * Real.pi * (p.1 - 1 : ℕ) * t) := by
      have := hs_ge.trans (hfK (v t) hvtK)
      rwa [hf_eq] at this
    have hsum_cos : ∑ p ∈ P, b p * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t) =
        (∑ p : {p : ℕ // p ∈ P}, a p * Real.cos (2 * Real.pi * (p.1 - 1 : ℕ) * t)) /
          (S * (1 + ε)) := by
      rw [← Finset.sum_attach P, Finset.sum_div]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [b, p.2, dite_true]
      ring
    rw [hsum_cos]
    have hdenom : 0 < S * (1 + ε) := mul_pos hS_pos h1ε
    have hc_eq : c = (ε * S) / (S * (1 + ε)) := by
      dsimp [c]
      field_simp [hS_pos.ne', h1ε.ne']
    rw [hc_eq, ← add_div]
    exact div_nonneg (by linarith) hdenom.le
  · dsimp [c]
    rw [div_le_iff₀ h1ε]
    nlinarith

/-- Probabilistic / averaging step: to witness a prime p <= N with shifted cosine average
at least -eps against a finite distribution (w, t), it suffices to provide any nonnegative
weight mu supported on primes P <= N with positive total mass whose weighted cosine sum is
at least -eps * (sum_{p in P} mu p). -/
lemma exists_prime_cosine_ge_of_weighted_sum (N : ℕ) (ε : ℝ)
    {ι : Type} [Fintype ι] (t : ι → ℝ) (w : ι → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ N)
    (μ : ℕ → ℝ) (hμ0 : ∀ p ∈ P, 0 ≤ μ p) (hμpos : 0 < ∑ p ∈ P, μ p)
    (havg : -ε * (∑ p ∈ P, μ p) ≤
      ∑ i, w i * ∑ p ∈ P, μ p * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t i)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ N ∧
      -ε ≤ ∑ i, w i * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t i) := by
  by_contra h
  push Not at h
  have hlt : ∑ p ∈ P, μ p * (∑ i, w i * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t i)) <
      ∑ p ∈ P, μ p * (-ε) := by
    have hPne : ∃ p ∈ P, 0 < μ p := by
      by_contra h0
      push Not at h0
      have hsum0 : ∑ p ∈ P, μ p = 0 :=
        Finset.sum_eq_zero fun p hp => le_antisymm (h0 p hp) (hμ0 p hp)
      linarith
    obtain ⟨p₀, hp₀P, hμp₀⟩ := hPne
    refine Finset.sum_lt_sum ?_ ⟨p₀, hp₀P, ?_⟩
    · intro p hp
      have h1 := h p (hP p hp).1 (hP p hp).2
      exact mul_le_mul_of_nonneg_left h1.le (hμ0 p hp)
    · have h1 := h p₀ (hP p₀ hp₀P).1 (hP p₀ hp₀P).2
      exact mul_lt_mul_of_pos_left h1 hμp₀
  have hswap : ∑ p ∈ P, μ p * (∑ i, w i * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t i)) =
      ∑ i, w i * ∑ p ∈ P, μ p * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hswap, ← Finset.sum_mul] at hlt
  linarith

/-- Dual form of Green 2022 Theorem 1.2 (arXiv:2206.08001): there exist eta > 0 and C >= 0
such that for all sufficiently large N and every finitely supported probability measure on R,
some prime p <= N satisfies sum_i w_i cos(2 pi (p - 1) t_i) >= -C N^(-eta).
Note: this statement directly implies Linnik's theorem for primes 1 mod M (take t_j = j/M,
1 <= j < M, with uniform weights 1/(M-1)) and requires Gallagher's log-free zero-density
estimate, Deuring-Heilbronn repulsion, Vaughan's identity, and Green's major/minor arc
analysis. -/
lemma dual_shifted_prime_cosine_bound :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ι : Type) [Fintype ι] (t : ι → ℝ) (w : ι → ℝ),
        (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
        ∃ p : ℕ, p.Prime ∧ p ≤ N ∧
          -(C * (N : ℝ) ^ (-η)) ≤
            ∑ i, w i * Real.cos (2 * Real.pi * (p - 1 : ℕ) * t i) := by
  sorry

end OMA.Green65PrimeMinusOne

theorem OMA.solution : type_of% @Green65.green_65.variants.prime_minus_one := by
  apply OMA.Green65PrimeMinusOne.prime_minus_one_of_cosine_poly
  obtain ⟨η, C, hη, hC, hdual⟩ := OMA.Green65PrimeMinusOne.dual_shifted_prime_cosine_bound
  refine ⟨η, C, hη, hC, ?_⟩
  filter_upwards [hdual] with N hNdual
  exact OMA.Green65PrimeMinusOne.cosine_poly_of_dual_fixed N (C * (N : ℝ) ^ (-η))
    (by positivity) hNdual
