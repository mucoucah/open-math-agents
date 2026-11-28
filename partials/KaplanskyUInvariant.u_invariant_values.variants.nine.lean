import FormalConjectures.Paper.KaplanskyUInvariant

/-!
# Izhboldin's theorem: existence of a field of u-invariant 9

Reduces `KaplanskyUInvariant.u_invariant_values.variants.nine` via diagonalization, direct limits
of `ℕ`-indexed chains of fields, and Cantor dovetailing to the single one-step invariant
preservation hypothesis `OMA.Nine.izhboldin_one_step_exists`.
-/

-- Problem: Izhboldin's theorem
-- Upstream: formal-conjectures FormalConjectures/Paper/KaplanskyUInvariant.lean:189 (declaration KaplanskyUInvariant.u_invariant_values.variants.nine)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open QuadraticForm

namespace OMA.Nine

/-- Zero extension `Fin k → F` into `Fin m → F` for `k ≤ m`. -/
def zext (F : Type) [Field F] (k m : ℕ) : (Fin k → F) →ₗ[F] (Fin m → F) :=
  LinearMap.pi fun i : Fin m =>
    if h : (i : ℕ) < k then LinearMap.proj (R := F) (φ := fun _ : Fin k => F) ⟨i, h⟩ else 0

theorem zext_apply_castLE (F : Type) [Field F] {k m : ℕ} (hkm : k ≤ m) (v : Fin k → F)
    (i : Fin k) : zext F k m v (Fin.castLE hkm i) = v i := by
  simp [zext, i.isLt]

theorem zext_injective (F : Type) [Field F] {k m : ℕ} (hkm : k ≤ m) :
    Function.Injective (zext F k m) := by
  intro v w h
  funext i
  have := congrFun h (Fin.castLE hkm i)
  rwa [zext_apply_castLE, zext_apply_castLE] at this

/-- Anisotropic dimensions are downward closed (characteristic not two). -/
theorem mem_of_le (F : Type) [Field F] [NeZero (2 : F)] {k m : ℕ} (hkm : k ≤ m)
    (h : m ∈ anisotropicDims F) : k ∈ anisotropicDims F := by
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp h
  refine mem_anisotropicDims_iff.mpr ⟨Q.comp (zext F k m), fun v hv => ?_⟩
  have h0 : zext F k m v = 0 := hQ _ hv
  exact zext_injective F hkm (by rw [h0, map_zero])

/-- Glue: a field of characteristic not two in which some 9-dimensional form is anisotropic
but every 10-dimensional form is isotropic has u-invariant 9. -/
theorem isUInvariant_nine_of (F : Type) [Field F] [NeZero (2 : F)]
    (h9 : 9 ∈ anisotropicDims F) (h10 : 10 ∉ anisotropicDims F) :
    KaplanskyUInvariant.IsUInvariant 9 := by
  refine ⟨F, inferInstance, inferInstance, h9, fun n hn => ?_⟩
  by_contra hlt
  exact h10 (mem_of_le F (by omega) hn)

/-- If every `m`-dimensional diagonal quadratic form over a field `F` of characteristic not two
is isotropic, then `m ∉ anisotropicDims F`. -/
theorem not_mem_anisotropicDims_of_diag_iso (F : Type) [Field F] [NeZero (2 : F)] (m : ℕ)
    (hdiag : ∀ w : Fin m → F, ∃ v : Fin m → F, v ≠ 0 ∧ ∑ i : Fin m, w i * v i ^ 2 = 0) :
    m ∉ anisotropicDims F := by
  intro hm
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp hm
  have : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne 2)
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hdim : Module.finrank F (Fin m → F) = m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  generalize Module.finrank F (Fin m → F) = k at w e hdim
  subst hdim
  obtain ⟨v, hv0, hvsum⟩ := hdiag w
  have hQv : Q (e.symm v) = 0 := by
    rw [e.symm.map_app, QuadraticMap.weightedSumSquares_apply]
    simpa [smul_eq_mul, sq] using hvsum
  have h0 : e.symm v = 0 := hQ _ hQv
  exact hv0 (e.symm.toLinearEquiv.map_eq_zero_iff.mp h0)

/-- An `ℕ`-indexed chain of fields of characteristic not two. -/
structure FieldChain where
  carrier : ℕ → Type
  field : ∀ n, Field (carrier n)
  neZeroTwo : ∀ n, NeZero (2 : carrier n)
  step : ∀ n, carrier n →+* carrier (n + 1)

instance (C : FieldChain) (n : ℕ) : Field (C.carrier n) := C.field n
instance (C : FieldChain) (n : ℕ) : NeZero (2 : C.carrier n) := C.neZeroTwo n

namespace FieldChain

/-- Transition ring homomorphism from level `m` to level `n` for `m ≤ n`. -/
def trans (C : FieldChain) (m : ℕ) : ∀ {n : ℕ}, m ≤ n → C.carrier m →+* C.carrier n
  | 0, h => by
      have hm : m = 0 := Nat.eq_zero_of_le_zero h
      subst hm
      exact RingHom.id _
  | n + 1, h =>
      if hlt : m ≤ n then
        (C.step n).comp (C.trans m hlt)
      else by
        have heq : m = n + 1 := by omega
        subst heq
        exact RingHom.id _

theorem trans_refl (C : FieldChain) (m : ℕ) : C.trans m (le_refl m) = RingHom.id _ := by
  cases m with
  | zero => rfl
  | succ n =>
      have h : ¬ n + 1 ≤ n := by omega
      simp [trans, h]

theorem trans_succ (C : FieldChain) {m n : ℕ} (h : m ≤ n) :
    C.trans m (Nat.le_succ_of_le h) = (C.step n).comp (C.trans m h) := by
  simp [trans, h]

theorem trans_trans (C : FieldChain) {l m n : ℕ} (h1 : l ≤ m) (h2 : m ≤ n) :
    (C.trans m h2).comp (C.trans l h1) = C.trans l (h1.trans h2) := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero h2
      have hl : l = 0 := Nat.eq_zero_of_le_zero (h1.trans h2)
      subst hm; subst hl
      simp [trans_refl]
  | succ n ih =>
      by_cases hm : m ≤ n
      · have hl : l ≤ n := h1.trans hm
        rw [trans_succ C hm, trans_succ C hl, RingHom.comp_assoc, ih hm]
      · have heq : m = n + 1 := by omega
        subst heq
        rw [trans_refl, RingHom.id_comp]

theorem trans_apply_trans (C : FieldChain) {l m n : ℕ} (h1 : l ≤ m) (h2 : m ≤ n)
    (x : C.carrier l) :
    C.trans m h2 (C.trans l h1 x) = C.trans l (h1.trans h2) x := by
  simpa using congrArg (fun f => f x) (C.trans_trans h1 h2)

/-- Equivalence relation on the disjoint union `Σ n, C.carrier n` for the direct limit. -/
def Rel (C : FieldChain) (x y : Σ n, C.carrier n) : Prop :=
  C.trans x.1 (le_max_left x.1 y.1) x.2 = C.trans y.1 (le_max_right x.1 y.1) y.2

theorem rel_iff_exists (C : FieldChain) (x y : Σ n, C.carrier n) :
    C.Rel x y ↔ ∃ (N : ℕ) (hx : x.1 ≤ N) (hy : y.1 ≤ N),
      C.trans x.1 hx x.2 = C.trans y.1 hy y.2 := by
  constructor
  · intro h
    exact ⟨max x.1 y.1, le_max_left _ _, le_max_right _ _, h⟩
  · rintro ⟨N, hx, hy, h⟩
    let M := max (max x.1 y.1) N
    have hM1 : max x.1 y.1 ≤ M := le_max_left _ _
    have hM2 : N ≤ M := le_max_right _ _
    apply (C.trans (max x.1 y.1) hM1).injective
    rw [C.trans_apply_trans, C.trans_apply_trans]
    calc
      C.trans x.1 ((le_max_left x.1 y.1).trans hM1) x.2
          = C.trans N hM2 (C.trans x.1 hx x.2) := by rw [C.trans_apply_trans]
      _ = C.trans N hM2 (C.trans y.1 hy y.2) := by rw [h]
      _ = C.trans y.1 ((le_max_right x.1 y.1).trans hM1) y.2 := by rw [C.trans_apply_trans]

theorem rel_equivalence (C : FieldChain) : Equivalence C.Rel where
  refl x := (C.rel_iff_exists x x).mpr ⟨x.1, le_refl _, le_refl _, rfl⟩
  symm h := by
    obtain ⟨N, hx, hy, hxy⟩ := (C.rel_iff_exists _ _).mp h
    exact (C.rel_iff_exists _ _).mpr ⟨N, hy, hx, hxy.symm⟩
  trans h1 h2 := by
    obtain ⟨N1, hx1, hy1, hxy⟩ := (C.rel_iff_exists _ _).mp h1
    obtain ⟨N2, hy2, hz2, hyz⟩ := (C.rel_iff_exists _ _).mp h2
    refine (C.rel_iff_exists _ _).mpr
      ⟨max N1 N2, hx1.trans (le_max_left _ _), hz2.trans (le_max_right _ _), ?_⟩
    calc
      C.trans _ (hx1.trans (le_max_left N1 N2)) _
          = C.trans N1 (le_max_left N1 N2) (C.trans _ hx1 _) := by rw [C.trans_apply_trans]
      _ = C.trans N1 (le_max_left N1 N2) (C.trans _ hy1 _) := by rw [hxy]
      _ = C.trans _ (hy2.trans (le_max_right N1 N2)) _ := by
            rw [C.trans_apply_trans]
      _ = C.trans N2 (le_max_right N1 N2) (C.trans _ hy2 _) := by rw [C.trans_apply_trans]
      _ = C.trans N2 (le_max_right N1 N2) (C.trans _ hz2 _) := by rw [hyz]
      _ = C.trans _ (hz2.trans (le_max_right N1 N2)) _ := by rw [C.trans_apply_trans]

def setoid (C : FieldChain) : Setoid (Σ n, C.carrier n) :=
  ⟨C.Rel, C.rel_equivalence⟩

/-- Direct limit carrier of an `ℕ`-indexed chain of fields. -/
def Lim (C : FieldChain) : Type := Quotient C.setoid

/-- Canonical map from level `n` into the direct limit `C.Lim`. -/
def of (C : FieldChain) (n : ℕ) (x : C.carrier n) : C.Lim :=
  Quotient.mk C.setoid ⟨n, x⟩

theorem of_eq_of_iff (C : FieldChain) {m n : ℕ} (x : C.carrier m) (y : C.carrier n) :
    C.of m x = C.of n y ↔ ∃ (N : ℕ) (hm : m ≤ N) (hn : n ≤ N),
      C.trans m hm x = C.trans n hn y := by
  change Quotient.mk C.setoid ⟨m, x⟩ = Quotient.mk C.setoid ⟨n, y⟩ ↔ _
  rw [Quotient.eq]
  exact C.rel_iff_exists ⟨m, x⟩ ⟨n, y⟩

theorem of_trans (C : FieldChain) {m n : ℕ} (h : m ≤ n) (x : C.carrier m) :
    C.of n (C.trans m h x) = C.of m x :=
  (C.of_eq_of_iff _ _).mpr ⟨n, le_refl n, h, by simp [C.trans_refl]⟩

theorem of_injective (C : FieldChain) (n : ℕ) : Function.Injective (C.of n) := by
  intro x y h
  obtain ⟨N, hn, _, hxy⟩ := (C.of_eq_of_iff x y).mp h
  exact (C.trans n hn).injective hxy

theorem exists_lift_fin (C : FieldChain) {k : ℕ} (v : Fin k → C.Lim) :
    ∃ (N : ℕ) (u : Fin k → C.carrier N), ∀ i, C.of N (u i) = v i := by
  have hrep : ∀ i : Fin k, ∃ p : Σ n, C.carrier n, C.of p.1 p.2 = v i :=
    fun i => Quotient.exists_rep (v i)
  choose p hp using hrep
  let N := Finset.univ.sup (fun i : Fin k => (p i).1)
  refine ⟨N, fun i => C.trans (p i).1 (Finset.le_sup (f := fun j => (p j).1) (Finset.mem_univ i))
    (p i).2, fun i => ?_⟩
  rw [C.of_trans, hp i]

theorem exists_lift2 (C : FieldChain) (a b : C.Lim) :
    ∃ (N : ℕ) (x y : C.carrier N), C.of N x = a ∧ C.of N y = b := by
  obtain ⟨N, u, hu⟩ := C.exists_lift_fin ![a, b]
  exact ⟨N, u 0, u 1, hu 0, hu 1⟩

theorem exists_lift3 (C : FieldChain) (a b c : C.Lim) :
    ∃ (N : ℕ) (x y z : C.carrier N), C.of N x = a ∧ C.of N y = b ∧ C.of N z = c := by
  obtain ⟨N, u, hu⟩ := C.exists_lift_fin ![a, b, c]
  exact ⟨N, u 0, u 1, u 2, hu 0, hu 1, hu 2⟩

instance instZero (C : FieldChain) : Zero C.Lim := ⟨C.of 0 0⟩
instance instOne (C : FieldChain) : One C.Lim := ⟨C.of 0 1⟩

instance instAdd (C : FieldChain) : Add C.Lim where
  add := Quotient.lift₂
    (fun x y => C.of (max x.1 y.1)
      (C.trans x.1 (le_max_left x.1 y.1) x.2 + C.trans y.1 (le_max_right x.1 y.1) y.2))
    (by
      intro x₁ y₁ x₂ y₂ hx hy
      obtain ⟨N1, hx1, hx2, hxe⟩ := (C.rel_iff_exists x₁ x₂).mp hx
      obtain ⟨N2, hy1, hy2, hye⟩ := (C.rel_iff_exists y₁ y₂).mp hy
      let M := max (max (max x₁.1 y₁.1) (max x₂.1 y₂.1)) (max N1 N2)
      have h1 : max x₁.1 y₁.1 ≤ M := (le_max_left _ _).trans (le_max_left _ _)
      have h2 : max x₂.1 y₂.1 ≤ M := (le_max_right _ _).trans (le_max_left _ _)
      have hN1 : N1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
      have hN2 : N2 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
      refine (C.of_eq_of_iff _ _).mpr ⟨M, h1, h2, ?_⟩
      simp only [map_add, C.trans_apply_trans]
      congr 1
      · calc
          C.trans x₁.1 _ x₁.2 = C.trans N1 hN1 (C.trans x₁.1 hx1 x₁.2) := by
            rw [C.trans_apply_trans]
          _ = C.trans N1 hN1 (C.trans x₂.1 hx2 x₂.2) := by rw [hxe]
          _ = C.trans x₂.1 _ x₂.2 := by rw [C.trans_apply_trans]
      · calc
          C.trans y₁.1 _ y₁.2 = C.trans N2 hN2 (C.trans y₁.1 hy1 y₁.2) := by
            rw [C.trans_apply_trans]
          _ = C.trans N2 hN2 (C.trans y₂.1 hy2 y₂.2) := by rw [hye]
          _ = C.trans y₂.1 _ y₂.2 := by rw [C.trans_apply_trans])

instance instMul (C : FieldChain) : Mul C.Lim where
  mul := Quotient.lift₂
    (fun x y => C.of (max x.1 y.1)
      (C.trans x.1 (le_max_left x.1 y.1) x.2 * C.trans y.1 (le_max_right x.1 y.1) y.2))
    (by
      intro x₁ y₁ x₂ y₂ hx hy
      obtain ⟨N1, hx1, hx2, hxe⟩ := (C.rel_iff_exists x₁ x₂).mp hx
      obtain ⟨N2, hy1, hy2, hye⟩ := (C.rel_iff_exists y₁ y₂).mp hy
      let M := max (max (max x₁.1 y₁.1) (max x₂.1 y₂.1)) (max N1 N2)
      have h1 : max x₁.1 y₁.1 ≤ M := (le_max_left _ _).trans (le_max_left _ _)
      have h2 : max x₂.1 y₂.1 ≤ M := (le_max_right _ _).trans (le_max_left _ _)
      have hN1 : N1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
      have hN2 : N2 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
      refine (C.of_eq_of_iff _ _).mpr ⟨M, h1, h2, ?_⟩
      simp only [map_mul, C.trans_apply_trans]
      congr 1
      · calc
          C.trans x₁.1 _ x₁.2 = C.trans N1 hN1 (C.trans x₁.1 hx1 x₁.2) := by
            rw [C.trans_apply_trans]
          _ = C.trans N1 hN1 (C.trans x₂.1 hx2 x₂.2) := by rw [hxe]
          _ = C.trans x₂.1 _ x₂.2 := by rw [C.trans_apply_trans]
      · calc
          C.trans y₁.1 _ y₁.2 = C.trans N2 hN2 (C.trans y₁.1 hy1 y₁.2) := by
            rw [C.trans_apply_trans]
          _ = C.trans N2 hN2 (C.trans y₂.1 hy2 y₂.2) := by rw [hye]
          _ = C.trans y₂.1 _ y₂.2 := by rw [C.trans_apply_trans])

instance instNeg (C : FieldChain) : Neg C.Lim where
  neg := Quotient.lift (fun x => C.of x.1 (-x.2)) (by
    intro x y h
    obtain ⟨N, hx, hy, hxy⟩ := (C.rel_iff_exists x y).mp h
    exact (C.of_eq_of_iff _ _).mpr ⟨N, hx, hy, by simp [hxy]⟩)

instance instInv (C : FieldChain) : Inv C.Lim where
  inv := Quotient.lift (fun x => C.of x.1 (x.2⁻¹)) (by
    intro x y h
    obtain ⟨N, hx, hy, hxy⟩ := (C.rel_iff_exists x y).mp h
    exact (C.of_eq_of_iff _ _).mpr ⟨N, hx, hy, by simp [map_inv₀, hxy]⟩)

theorem of_zero (C : FieldChain) (n : ℕ) : C.of n 0 = 0 :=
  (C.of_eq_of_iff _ _).mpr ⟨n, le_refl n, Nat.zero_le n, by simp⟩

theorem of_one (C : FieldChain) (n : ℕ) : C.of n 1 = 1 :=
  (C.of_eq_of_iff _ _).mpr ⟨n, le_refl n, Nat.zero_le n, by simp⟩

theorem of_add (C : FieldChain) (n : ℕ) (x y : C.carrier n) :
    C.of n (x + y) = C.of n x + C.of n y := by
  change C.of n (x + y) = C.of (max n n) (C.trans n (le_max_left n n) x +
    C.trans n (le_max_right n n) y)
  refine (C.of_eq_of_iff _ _).mpr ⟨n, le_refl n, max_le (le_refl n) (le_refl n), ?_⟩
  simp [C.trans_refl, C.trans_apply_trans]

theorem of_mul (C : FieldChain) (n : ℕ) (x y : C.carrier n) :
    C.of n (x * y) = C.of n x * C.of n y := by
  change C.of n (x * y) = C.of (max n n) (C.trans n (le_max_left n n) x *
    C.trans n (le_max_right n n) y)
  refine (C.of_eq_of_iff _ _).mpr ⟨n, le_refl n, max_le (le_refl n) (le_refl n), ?_⟩
  simp [C.trans_refl, C.trans_apply_trans]

theorem of_neg (C : FieldChain) (n : ℕ) (x : C.carrier n) :
    C.of n (-x) = -(C.of n x) := rfl

theorem of_inv (C : FieldChain) (n : ℕ) (x : C.carrier n) :
    C.of n (x⁻¹) = (C.of n x)⁻¹ := rfl

instance instCommRing (C : FieldChain) : CommRing C.Lim where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  mul := (· * ·)
  one := 1
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec
  add_assoc a b c := by
    obtain ⟨N, x, y, z, rfl, rfl, rfl⟩ := C.exists_lift3 a b c
    simp only [← C.of_add, add_assoc]
  zero_add a := by
    obtain ⟨⟨N, x⟩, rfl⟩ := Quotient.exists_rep a
    change (0 : C.Lim) + C.of N x = C.of N x
    rw [← C.of_zero N, ← C.of_add, zero_add]
  add_zero a := by
    obtain ⟨⟨N, x⟩, rfl⟩ := Quotient.exists_rep a
    change C.of N x + (0 : C.Lim) = C.of N x
    rw [← C.of_zero N, ← C.of_add, add_zero]
  add_comm a b := by
    obtain ⟨N, x, y, rfl, rfl⟩ := C.exists_lift2 a b
    simp only [← C.of_add, add_comm]
  neg_add_cancel a := by
    obtain ⟨⟨N, x⟩, rfl⟩ := Quotient.exists_rep a
    change -(C.of N x) + C.of N x = 0
    rw [← C.of_neg, ← C.of_add, neg_add_cancel, C.of_zero]
  mul_assoc a b c := by
    obtain ⟨N, x, y, z, rfl, rfl, rfl⟩ := C.exists_lift3 a b c
    simp only [← C.of_mul, mul_assoc]
  one_mul a := by
    obtain ⟨⟨N, x⟩, rfl⟩ := Quotient.exists_rep a
    change (1 : C.Lim) * C.of N x = C.of N x
    rw [← C.of_one N, ← C.of_mul, one_mul]
  mul_one a := by
    obtain ⟨⟨N, x⟩, rfl⟩ := Quotient.exists_rep a
    change C.of N x * (1 : C.Lim) = C.of N x
    rw [← C.of_one N, ← C.of_mul, mul_one]
  mul_comm a b := by
    obtain ⟨N, x, y, rfl, rfl⟩ := C.exists_lift2 a b
    simp only [← C.of_mul, mul_comm]
  left_distrib a b c := by
    obtain ⟨N, x, y, z, rfl, rfl, rfl⟩ := C.exists_lift3 a b c
    simp only [← C.of_add, ← C.of_mul, left_distrib]
  right_distrib a b c := by
    obtain ⟨N, x, y, z, rfl, rfl, rfl⟩ := C.exists_lift3 a b c
    simp only [← C.of_add, ← C.of_mul, right_distrib]
  zero_mul a := by
    obtain ⟨⟨N, x⟩, rfl⟩ := Quotient.exists_rep a
    change (0 : C.Lim) * C.of N x = 0
    rw [← C.of_zero N, ← C.of_mul, zero_mul, C.of_zero]
  mul_zero a := by
    obtain ⟨⟨N, x⟩, rfl⟩ := Quotient.exists_rep a
    change C.of N x * (0 : C.Lim) = 0
    rw [← C.of_zero N, ← C.of_mul, mul_zero, C.of_zero]

instance instField (C : FieldChain) : Field C.Lim where
  inv := Inv.inv
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (C.of_injective 0 h)⟩
  mul_inv_cancel a ha := by
    obtain ⟨⟨N, x⟩, rfl⟩ := Quotient.exists_rep a
    have hx : x ≠ 0 := fun h0 => ha (by change C.of N x = 0; rw [h0, C.of_zero])
    change C.of N x * (C.of N x)⁻¹ = 1
    rw [← C.of_inv, ← C.of_mul, mul_inv_cancel₀ hx, C.of_one]
  inv_zero := by
    change (C.of 0 0)⁻¹ = C.of 0 0
    rw [← C.of_inv, inv_zero]
  nnqsmul := _
  qsmul := _

/-- Canonical ring homomorphism from level `n` into `C.Lim`. -/
def ofHom (C : FieldChain) (n : ℕ) : C.carrier n →+* C.Lim where
  toFun := C.of n
  map_one' := C.of_one n
  map_mul' := C.of_mul n
  map_zero' := C.of_zero n
  map_add' := C.of_add n

theorem ofHom_trans (C : FieldChain) {m n : ℕ} (h : m ≤ n) (x : C.carrier m) :
    C.ofHom n (C.trans m h x) = C.ofHom m x :=
  C.of_trans h x

instance instNeZeroTwo (C : FieldChain) : NeZero (2 : C.Lim) := by
  refine ⟨fun h => ?_⟩
  have h0 : C.ofHom 0 (2 : C.carrier 0) = C.ofHom 0 0 := by
    simpa [map_ofNat] using h
  exact NeZero.ne (2 : C.carrier 0) ((C.ofHom 0).injective h0)

end FieldChain

/-- A single countable field stage carrying a 9-dimensional diagonal form satisfying `P`
together with an enumeration of all 10-dimensional diagonal forms over the stage. -/
structure Stage (P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop) where
  F : Type
  instField : Field F
  instNeZero : NeZero (2 : F)
  instCountable : Countable F
  a : Fin 9 → F
  hP : P F a
  enum : ℕ → (Fin 10 → F)
  enum_surj : Function.Surjective enum

instance {P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop} (s : Stage P) :
    Field s.F := s.instField

instance {P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop} (s : Stage P) :
    NeZero (2 : s.F) := s.instNeZero

instance {P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop} (s : Stage P) :
    Countable s.F := s.instCountable

/-- One extension step of a finite tower. -/
structure ChainStep (P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop)
    (Prev : Type 1) (lastOf : Prev → Stage P) : Type 1 where
  prev : Prev
  top : Stage P
  hom : (lastOf prev).F →+* top.F
  compat : top.a = hom ∘ (lastOf prev).a

/-- Recursive pair `(ChainUpTo P n, last)` with definitional reduction at every level. -/
def ChainData (P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop) :
    ℕ → Σ (T : Type 1), T → Stage P
  | 0 => ⟨Stage P, id⟩
  | n + 1 => ⟨ChainStep P (ChainData P n).1 (ChainData P n).2, ChainStep.top⟩

/-- Finite initial segment of a tower of length `n + 1`. -/
abbrev ChainUpTo (P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop) (n : ℕ) :
    Type 1 :=
  (ChainData P n).1

namespace ChainUpTo

variable {P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop}

/-- The top stage of a finite tower `ChainUpTo P n`. -/
abbrev last {n : ℕ} (c : ChainUpTo P n) : Stage P :=
  (ChainData P n).2 c

/-- Drop a finite tower `ChainUpTo P n` to level `k ≤ n` together with its transition hom. -/
def dropPair : ∀ {n : ℕ} (c : ChainUpTo P n) (k : ℕ), k ≤ n →
    Σ (c' : ChainUpTo P k), (last c').F →+* (last c).F
  | 0, c, k, h => by
      have hk : k = 0 := Nat.eq_zero_of_le_zero h
      subst hk
      exact ⟨c, RingHom.id _⟩
  | n + 1, c, k, h =>
      if hk : k ≤ n then
        let p := dropPair c.prev k hk
        ⟨p.1, c.hom.comp p.2⟩
      else by
        have heq : k = n + 1 := by omega
        subst heq
        exact ⟨c, RingHom.id _⟩

/-- Drop a finite tower `ChainUpTo P n` to level `k ≤ n`. -/
abbrev drop {n : ℕ} (c : ChainUpTo P n) (k : ℕ) (h : k ≤ n) : ChainUpTo P k :=
  (dropPair c k h).1

/-- Transition ring homomorphism from level `k ≤ n` to level `n` inside a finite tower. -/
abbrev dropHom {n : ℕ} (c : ChainUpTo P n) (k : ℕ) (h : k ≤ n) :
    (last (drop c k h)).F →+* (last c).F :=
  (dropPair c k h).2

theorem dropPair_of_le {n : ℕ} (c : ChainUpTo P (n + 1)) {k : ℕ} (hk : k ≤ n) :
    dropPair c k (Nat.le_succ_of_le hk) =
      ⟨(dropPair c.prev k hk).1, c.hom.comp (dropPair c.prev k hk).2⟩ := by
  simp [dropPair, hk]

theorem dropPair_self {n : ℕ} (c : ChainUpTo P n) :
    dropPair c n (le_refl n) = ⟨c, RingHom.id _⟩ := by
  cases n with
  | zero => rfl
  | succ n =>
      have h : ¬ n + 1 ≤ n := by omega
      simp [dropPair, h]

theorem dropPair_apply_eq {n k : ℕ} {c : ChainUpTo P n}
    {p₁ p₂ : Σ (c' : ChainUpTo P k), (last c').F →+* (last c).F} (hp : p₁ = p₂)
    {c₀ : ChainUpTo P k} (h₁ : p₁.1 = c₀) (h₂ : p₂.1 = c₀) (x : (last c₀).F) :
    p₁.2 (h₁ ▸ x) = p₂.2 (h₂ ▸ x) := by
  subst hp
  rfl

end ChainUpTo

/-- Abstract Merkurjev-Izhboldin tower theorem: any predicate `P` on 9-dimensional diagonal
forms over fields of characteristic not two that guarantees anisotropy, is realized over some
countable base field, and is preserved when killing any 10-dimensional diagonal form over a
countable field yields a field of u-invariant 9 (i.e. `izhboldin_core`). -/
theorem izhboldin_core_of_one_step
    (P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop)
    (hBase : ∃ (F₀ : Type) (_ : Field F₀) (_ : NeZero (2 : F₀)) (_ : Countable F₀)
      (a₀ : Fin 9 → F₀), P F₀ a₀)
    (hAniso : ∀ (K : Type) [Field K] [NeZero (2 : K)] (a : Fin 9 → K),
      P K a → ∀ v : Fin 9 → K, (∑ i : Fin 9, a i * v i ^ 2 = 0) → v = 0)
    (hStep : ∀ (K : Type) [Field K] [NeZero (2 : K)] [Countable K]
      (a : Fin 9 → K), P K a → ∀ w : Fin 10 → K,
      ∃ (L : Type) (_ : Field L) (_ : NeZero (2 : L)) (_ : Countable L) (f : K →+* L),
        (∃ v : Fin 10 → L, v ≠ 0 ∧ ∑ i : Fin 10, f (w i) * v i ^ 2 = 0) ∧
        P L (f ∘ a)) :
    ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F)),
      9 ∈ anisotropicDims F ∧ 10 ∉ anisotropicDims F := by
  classical
  -- Base stage
  obtain ⟨F₀, instF₀, inst2₀, instC₀, a₀, hP₀⟩ := hBase
  obtain ⟨e₀, he₀⟩ := exists_surjective_nat (Fin 10 → F₀)
  let s₀ : Stage P := ⟨F₀, instF₀, inst2₀, instC₀, a₀, hP₀, e₀, he₀⟩
  -- One-step extension of a finite tower killing the Cantor-dovetailing target at step `n`
  let nextData (n : ℕ) (c : ChainUpTo P n) :
      Σ' (s : Stage P) (f : (ChainUpTo.last c).F →+* s.F),
        (s.a = f ∘ (ChainUpTo.last c).a) ∧
        (∃ v : Fin 10 → s.F, v ≠ 0 ∧
          ∑ i : Fin 10,
            f (ChainUpTo.dropHom c (Nat.unpair n).1 (Nat.unpair_left_le n)
              ((ChainUpTo.last (ChainUpTo.drop c (Nat.unpair n).1 (Nat.unpair_left_le n))).enum
                (Nat.unpair n).2 i)) * v i ^ 2 = 0) := by
    let k := (Nat.unpair n).1
    let m := (Nat.unpair n).2
    have hk : k ≤ n := Nat.unpair_left_le n
    let w : Fin 10 → (ChainUpTo.last c).F :=
      fun i => ChainUpTo.dropHom c k hk ((ChainUpTo.last (ChainUpTo.drop c k hk)).enum m i)
    let h := hStep (ChainUpTo.last c).F (ChainUpTo.last c).a (ChainUpTo.last c).hP w
    let L := Classical.choose h
    let h1 := Classical.choose_spec h
    letI : Field L := Classical.choose h1
    let h2 := Classical.choose_spec h1
    letI : NeZero (2 : L) := Classical.choose h2
    let h3 := Classical.choose_spec h2
    letI : Countable L := Classical.choose h3
    let h4 := Classical.choose_spec h3
    let f : (ChainUpTo.last c).F →+* L := Classical.choose h4
    let hf := Classical.choose_spec h4
    let heL := exists_surjective_nat (Fin 10 → L)
    let sL : Stage P :=
      ⟨L, inferInstance, inferInstance, inferInstance, f ∘ (ChainUpTo.last c).a, hf.2,
        Classical.choose heL, Classical.choose_spec heL⟩
    exact ⟨sL, f, rfl, hf.1⟩
  -- Build the infinite sequence of finite towers
  let chain : ∀ n : ℕ, ChainUpTo P n := Nat.rec s₀ (fun n c =>
    let d := nextData n c
    { prev := c, top := d.1, hom := d.2.1, compat := d.2.2.1 })
  -- Compatibility of `drop` with `chain`
  have hdrop : ∀ (n k : ℕ) (h : k ≤ n), ChainUpTo.drop (chain n) k h = chain k := by
    intro n
    induction n with
    | zero =>
        intro k h
        have hk : k = 0 := Nat.eq_zero_of_le_zero h
        subst hk; rfl
    | succ n ih =>
        intro k h
        by_cases hk : k ≤ n
        · simp only [chain, ChainUpTo.drop, ChainUpTo.dropPair, hk, ↓reduceDIte]
          exact ih k hk
        · have heq : k = n + 1 := by omega
          subst heq
          simp only [chain, ChainUpTo.drop, ChainUpTo.dropPair, hk, ↓reduceDIte]
          rfl
  -- Extract the FieldChain
  let C : FieldChain := {
    carrier := fun n => (ChainUpTo.last (chain n)).F
    field := fun n => (ChainUpTo.last (chain n)).instField
    neZeroTwo := fun n => (ChainUpTo.last (chain n)).instNeZero
    step := fun n => (nextData n (chain n)).2.1
  }
  -- `C.trans` carries `a 0` to `a n`
  have ha_compat : ∀ n : ℕ,
      (ChainUpTo.last (chain n)).a = C.trans 0 (Nat.zero_le n) ∘ (ChainUpTo.last (chain 0)).a := by
    intro n
    induction n with
    | zero =>
        rw [C.trans_refl]
        rfl
    | succ n ih =>
        rw [C.trans_succ (Nat.zero_le n)]
        funext i
        have h1 := congrFun (nextData n (chain n)).2.2.1 i
        have h2 := congrFun ih i
        change (nextData n (chain n)).1.a i =
          C.step n (C.trans 0 (Nat.zero_le n) ((ChainUpTo.last (chain 0)).a i))
        rw [h1, Function.comp_apply, h2]
        rfl
  -- `ChainUpTo.dropHom` agrees with `C.trans` via `hdrop`
  have hdropHom : ∀ (n k : ℕ) (h : k ≤ n) (x : C.carrier k),
      ChainUpTo.dropHom (chain n) k h (hdrop n k h ▸ x) = C.trans k h x := by
    intro n
    induction n with
    | zero =>
        intro k h x
        have hk : k = 0 := Nat.eq_zero_of_le_zero h
        subst hk
        simp [ChainUpTo.dropHom, ChainUpTo.dropPair, C.trans_refl]
        rfl
    | succ n ih =>
        intro k h x
        by_cases hk : k ≤ n
        · rw [C.trans_succ hk]
          have hstep := ChainUpTo.dropPair_apply_eq
            (ChainUpTo.dropPair_of_le (chain (n + 1)) hk)
            (hdrop (n + 1) k h) (hdrop n k hk) x
          rw [hstep]
          exact congrArg (C.step n) (ih k hk x)
        · have heq : k = n + 1 := by omega
          subst heq
          rw [C.trans_refl]
          exact ChainUpTo.dropPair_apply_eq
            (ChainUpTo.dropPair_self (chain (n + 1)))
            (hdrop (n + 1) (n + 1) h) rfl x
  -- Witness the direct limit field `C.Lim`
  refine ⟨C.Lim, inferInstance, inferInstance, ?_, ?_⟩
  · -- 9 ∈ anisotropicDims C.Lim via the pushed-forward base form `a₀`
    let aLim : Fin 9 → C.Lim := C.ofHom 0 ∘ (ChainUpTo.last (chain 0)).a
    refine mem_anisotropicDims_iff.mpr ⟨QuadraticMap.weightedSumSquares C.Lim aLim, ?_⟩
    intro v hv
    obtain ⟨N, u, hu⟩ := C.exists_lift_fin v
    have hsumLim : C.ofHom N (∑ i : Fin 9, (ChainUpTo.last (chain N)).a i * u i ^ 2) = 0 := by
      rw [map_sum]
      have hterm : ∀ i : Fin 9,
          C.ofHom N ((ChainUpTo.last (chain N)).a i * u i ^ 2) = aLim i * v i ^ 2 := by
        intro i
        rw [map_mul, map_pow, ha_compat N]
        change C.ofHom N (C.trans 0 (Nat.zero_le N) ((ChainUpTo.last (chain 0)).a i)) *
            (C.of N (u i)) ^ 2 = _
        rw [C.ofHom_trans, hu i]
        rfl
      simp_rw [hterm]
      simpa [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, sq] using hv
    have hsumN : ∑ i : Fin 9, (ChainUpTo.last (chain N)).a i * u i ^ 2 = 0 :=
      (C.ofHom N).injective (by simpa [map_zero] using hsumLim)
    have hu0 : u = 0 :=
      hAniso (ChainUpTo.last (chain N)).F (ChainUpTo.last (chain N)).a
        (ChainUpTo.last (chain N)).hP u hsumN
    funext i
    rw [← hu i, hu0, Pi.zero_apply, C.of_zero]
    rfl
  · -- 10 ∉ anisotropicDims C.Lim via diagonalization and Cantor dovetailing
    apply not_mem_anisotropicDims_of_diag_iso C.Lim 10
    intro w
    obtain ⟨k, wk, hwk⟩ := C.exists_lift_fin w
    obtain ⟨m, hm⟩ := (ChainUpTo.last (chain k)).enum_surj wk
    let n := Nat.pair k m
    have hunp : Nat.unpair n = (k, m) := Nat.unpair_pair k m
    have hkn : k ≤ n := Nat.left_le_pair k m
    have hkill := (nextData n (chain n)).2.2.2
    obtain ⟨v0, hv0, hvsum0⟩ := hkill
    let v : Fin 10 → C.carrier (n + 1) := v0
    have hv : v ≠ 0 := hv0
    have hvsum : ∑ i : Fin 10,
        C.step n (ChainUpTo.dropHom (chain n) (Nat.unpair n).1 (Nat.unpair_left_le n)
          ((ChainUpTo.last (ChainUpTo.drop (chain n) (Nat.unpair n).1
            (Nat.unpair_left_le n))).enum (Nat.unpair n).2 i)) * v i ^ 2 = 0 := hvsum0
    refine ⟨fun i => C.ofHom (n + 1) (v i), ?_, ?_⟩
    · intro h0
      apply hv
      funext i
      exact (C.ofHom (n + 1)).injective ((congrFun h0 i).trans (map_zero _).symm)
    · have hcoeff : ∀ i : Fin 10,
          w i = C.ofHom (n + 1)
            (C.step n (ChainUpTo.dropHom (chain n) (Nat.unpair n).1 (Nat.unpair_left_le n)
              ((ChainUpTo.last (ChainUpTo.drop (chain n) (Nat.unpair n).1
                (Nat.unpair_left_le n))).enum (Nat.unpair n).2 i))) := by
        intro i
        have hdrop_eq :
            ChainUpTo.dropHom (chain n) (Nat.unpair n).1 (Nat.unpair_left_le n)
              ((ChainUpTo.last (ChainUpTo.drop (chain n) (Nat.unpair n).1
                (Nat.unpair_left_le n))).enum (Nat.unpair n).2 i) =
            C.trans k hkn (wk i) := by
          have hk1 : k = (Nat.unpair n).1 := (congrArg Prod.fst hunp).symm
          have hm1 : m = (Nat.unpair n).2 := (congrArg Prod.snd hunp).symm
          have hcast : ∀ (k' : ℕ) (hk' : k' ≤ n) (m' : ℕ) (hek : k = k') (hem : m = m'),
              ChainUpTo.dropHom (chain n) k' hk'
                ((ChainUpTo.last (ChainUpTo.drop (chain n) k' hk')).enum m' i) =
              C.trans k hkn (wk i) := by
            rintro _ hk' _ rfl rfl
            have h1 := hdropHom n k hk' ((ChainUpTo.last (chain k)).enum m i)
            have hcast_enum : ∀ {c₁ c₂ : ChainUpTo P k} (he : c₁ = c₂),
                (ChainUpTo.last c₁).enum m i = he ▸ ((ChainUpTo.last c₂).enum m i) := by
              rintro c _ rfl; rfl
            rw [hcast_enum (hdrop n k hk'), h1, hm]
          exact hcast _ _ _ hk1 hm1
        rw [hdrop_eq]
        have hstep_trans : C.step n (C.trans k hkn (wk i)) =
            C.trans k (Nat.le_succ_of_le hkn) (wk i) := by
          rw [C.trans_succ hkn]
          rfl
        rw [hstep_trans, C.ofHom_trans, ← hwk i]
        rfl
      calc
        ∑ i : Fin 10, w i * (C.ofHom (n + 1) (v i)) ^ 2
            = ∑ i : Fin 10, C.ofHom (n + 1)
                (C.step n (ChainUpTo.dropHom (chain n) (Nat.unpair n).1 (Nat.unpair_left_le n)
                  ((ChainUpTo.last (ChainUpTo.drop (chain n) (Nat.unpair n).1
                    (Nat.unpair_left_le n))).enum (Nat.unpair n).2 i)) * v i ^ 2) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_mul, map_pow, hcoeff i]
        _ = C.ofHom (n + 1) _ := by rw [← map_sum]
        _ = 0 := by rw [hvsum, map_zero]

/-- The single remaining deep algebraic-geometric step (Izhboldin 2001 / Vishik 2009 /
Karpenko 2026): existence of a preservation invariant `P` on 9-dimensional diagonal forms
over countable fields of characteristic not two that guarantees anisotropy and is preserved
when killing any 10-dimensional diagonal form. -/
theorem izhboldin_one_step_exists :
    ∃ (P : ∀ (K : Type) [Field K] [NeZero (2 : K)], (Fin 9 → K) → Prop),
      (∃ (F₀ : Type) (_ : Field F₀) (_ : NeZero (2 : F₀)) (_ : Countable F₀)
        (a₀ : Fin 9 → F₀), P F₀ a₀) ∧
      (∀ (K : Type) [Field K] [NeZero (2 : K)] (a : Fin 9 → K),
        P K a → ∀ v : Fin 9 → K, (∑ i : Fin 9, a i * v i ^ 2 = 0) → v = 0) ∧
      (∀ (K : Type) [Field K] [NeZero (2 : K)] [Countable K]
        (a : Fin 9 → K), P K a → ∀ w : Fin 10 → K,
        ∃ (L : Type) (_ : Field L) (_ : NeZero (2 : L)) (_ : Countable L) (f : K →+* L),
          (∃ v : Fin 10 → L, v ≠ 0 ∧ ∑ i : Fin 10, f (w i) * v i ^ 2 = 0) ∧
          P L (f ∘ a)) := by
  sorry

/-- The core of Izhboldin's theorem (Ann. of Math. 2001): existence of such a field. -/
theorem izhboldin_core : ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F)),
    9 ∈ anisotropicDims F ∧ 10 ∉ anisotropicDims F := by
  obtain ⟨P, hBase, hAniso, hStep⟩ := izhboldin_one_step_exists
  exact izhboldin_core_of_one_step P hBase hAniso hStep

end OMA.Nine

theorem OMA.solution : type_of% @KaplanskyUInvariant.u_invariant_values.variants.nine := by
  obtain ⟨F, _, _, h9, h10⟩ := OMA.Nine.izhboldin_core
  exact OMA.Nine.isUInvariant_nine_of F h9 h10
