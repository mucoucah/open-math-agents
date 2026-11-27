import FormalConjectures.ErdosProblems.«99»

/-! Perturbation criteria for diameter-minimizing finite planar packings. -/

-- Problem: Erdős Problem 99
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/99.lean:48 (declaration Erdos99.erdos_99)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Set Metric EuclideanGeometry Filter
open scoped InnerProductSpace Topology

namespace OMA.Erdos99

private lemma exists_dist_eq_diam (A : Finset ℝ²) (hA : A.Nonempty) :
    ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) := by
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (A ×ˢ A)
    (fun z : ℝ² × ℝ² => dist z.1 z.2) (hA.product hA)
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hz
  refine ⟨z.1, hp, z.2, hq, le_antisymm
    (dist_le_diam_of_mem A.finite_toSet.isBounded hp hq) ?_⟩
  exact diam_le_of_forall_dist_le (dist_nonneg (x := z.1) (y := z.2))
    (fun p hp q hq => hmax (p, q) (Finset.mem_product.mpr ⟨hp, hq⟩))

/-- A competitor with distances at least one can be rescaled to attain distance one. -/
private lemma no_separated_improvement {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (f : ℝ² → ℝ²)
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist (f p) (f q)) :
    ¬ (∀ p ∈ A, ∀ q ∈ A, dist (f p) (f q) < diam (A : Set ℝ²)) := by
  classical
  intro hsmall
  let pairs := (A ×ˢ A).filter (fun z => z.1 ≠ z.2)
  obtain ⟨p, hp, q, hq, hpq⟩ := hA.2
  have hpq_ne : p ≠ q := by
    intro h
    subst q
    simp at hpq
  have hpair : pairs.Nonempty :=
    ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq_ne⟩⟩
  obtain ⟨z, hz, hzmin⟩ :=
    Finset.exists_min_image pairs (fun w => dist (f w.1) (f w.2)) hpair
  obtain ⟨hzA, hz_ne⟩ := Finset.mem_filter.mp hz
  obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hzA
  let d := dist (f z.1) (f z.2)
  have hd : 1 ≤ d := hsep z.1 hz₁ z.2 hz₂ hz_ne
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  let g := fun p => d⁻¹ • f p
  have hscale (p q : ℝ²) : dist (g p) (g q) = d⁻¹ * dist (f p) (f q) := by
    simp [g, dist_smul₀, Real.norm_eq_abs, abs_of_pos hdpos]
  have hgsep (p : ℝ²) (hp : p ∈ A) (q : ℝ²) (hq : q ∈ A) (hne : p ≠ q) :
      1 ≤ dist (g p) (g q) := by
    rw [hscale, ← div_eq_inv_mul, le_div_iff₀ hdpos, one_mul]
    exact hzmin (p, q) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hne⟩)
  have hginj : Set.InjOn g (A : Set ℝ²) := by
    intro p hp q hq heq
    by_contra hne
    have hh := hgsep p hp q hq hne
    rw [heq, dist_self] at hh
    norm_num at hh
  let B := A.image g
  have hB : Erdos99.HasMinDist1 B := by
    constructor
    · intro x hx y hy hxy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact hgsep p hp q hq (fun heq => hxy (congrArg g heq))
    · refine ⟨g z.1, Finset.mem_image_of_mem g hz₁, g z.2, Finset.mem_image_of_mem g hz₂, ?_⟩
      rw [hscale]
      exact inv_mul_cancel₀ hdpos.ne'
  have hBmem : B ∈ {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} :=
    ⟨Finset.card_image_of_injOn hginj, hB⟩
  have hcompare : diam (A : Set ℝ²) ≤ diam (B : Set ℝ²) := hmin hBmem
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_dist_eq_diam B
    ⟨g p, Finset.mem_image_of_mem g hp⟩
  obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hy
  have hinv : d⁻¹ ≤ 1 := (inv_le_one₀ hdpos).mpr hd
  have hlt : dist (g p') (g q') < diam (A : Set ℝ²) := by
    rw [hscale]
    exact (mul_le_of_le_one_left dist_nonneg hinv).trans_lt (hsmall p' hp' q' hq')
  exact (not_lt_of_ge hcompare) (hxy ▸ hlt)

private def HasSeparatedImprovement (A : Finset ℝ²) : Prop :=
  ∃ f : ℝ² → ℝ²,
    (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist (f p) (f q)) ∧
    (∀ p ∈ A, ∀ q ∈ A, dist (f p) (f q) < diam (A : Set ℝ²))

private lemma isMinOn_iff_no_separated_improvement {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A) :
    IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A ↔
    ¬ HasSeparatedImprovement A := by
  classical
  constructor
  · rintro hm ⟨f, hs, hd⟩
    exact no_separated_improvement hA hm f hs hd
  · intro h B hB
    change B.card = A.card ∧ Erdos99.HasMinDist1 B at hB
    change diam (A : Set ℝ²) ≤ diam (B : Set ℝ²)
    by_contra! hbetter
    let e : A ≃ B := Finset.equivOfCardEq hB.1.symm
    let f (p : ℝ²) : ℝ² := if hp : p ∈ A then (e ⟨p, hp⟩ : ℝ²) else p
    have hf (p : ℝ²) (hp : p ∈ A) : f p = (e ⟨p, hp⟩ : ℝ²) := by simp [f, hp]
    have hmem (p : ℝ²) (hp : p ∈ A) : f p ∈ B := by
      rw [hf p hp]
      exact (e ⟨p, hp⟩).property
    refine h ⟨f, ?_, fun p hp q hq =>
      (dist_le_diam_of_mem B.finite_toSet.isBounded (hmem p hp) (hmem q hq)).trans_lt hbetter⟩
    intro p hp q hq hpq
    apply hB.2.1 _ (hmem p hp) _ (hmem q hq)
    rw [hf p hp, hf q hq]
    intro heq
    exact hpq (congrArg Subtype.val (e.injective (Subtype.ext heq)))

/-- At a minimum, no velocity can preserve the contacts to first order while
strictly shortening every diametral pair to first order. -/
private lemma no_contracting_velocity {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (v : ℝ² → ℝ²)
    (hunit : ∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 ≤ ⟪p - q, v p - v q⟫_ℝ) :
    ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧
      0 ≤ ⟪p - q, v p - v q⟫_ℝ := by
  by_contra! hdiam
  let move (t : ℝ) (x : ℝ²) := x + t • v x
  have hsquare (t : ℝ) (p q : ℝ²) :
      dist (move t p) (move t q) ^ 2 =
        dist p q ^ 2 + 2 * ⟪p - q, v p - v q⟫_ℝ * t + t ^ 2 * ‖v p - v q‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : move t p - move t q = (p - q) + t • (v p - v q) := by
      dsimp [move]
      rw [smul_sub]
      abel
    rw [heq, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have hpairs (p : ℝ²) (hp : p ∈ A) (q : ℝ²) (hq : q ∈ A) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), (p ≠ q → 1 ≤ dist (move t p) (move t q)) ∧
        dist (move t p) (move t q) < diam (A : Set ℝ²) := by
    have hc : Continuous (fun t : ℝ => dist (move t p) (move t q)) := by
      unfold move
      fun_prop
    have hzero : dist (move 0 p) (move 0 q) = dist p q := by simp [move]
    refine Eventually.and ?_ ?_
    · by_cases hu : dist p q = 1
      · filter_upwards [self_mem_nhdsWithin] with t ht _
        have htpos : 0 ≤ t := (show 0 < t from ht).le
        rw [← sq_le_sq₀ zero_le_one dist_nonneg, hsquare, hu]
        have hlinear := mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
          (hunit p hp q hq hu)) htpos
        have hquadratic := mul_nonneg (sq_nonneg t) (sq_nonneg ‖v p - v q‖)
        linarith
      · by_cases hpq : p = q
        · exact Eventually.of_forall (fun _ hne => (hne hpq).elim)
        · have hstrict : 1 < dist (move 0 p) (move 0 q) :=
            hzero ▸ lt_of_le_of_ne (hA.1 p hp q hq hpq) (Ne.symm hu)
          exact (eventually_nhdsWithin_of_eventually_nhds
            (continuousAt_const.eventually_lt hc.continuousAt hstrict)).mono
              (fun _ ht _ => ht.le)
    · by_cases hd : dist p q = diam (A : Set ℝ²)
      · let coeff (t : ℝ) := 2 * ⟪p - q, v p - v q⟫_ℝ + t * ‖v p - v q‖ ^ 2
        have hcoeff : Continuous coeff := by unfold coeff; fun_prop
        have hneg : coeff 0 < 0 := by
          simpa [coeff] using mul_neg_of_pos_of_neg
            (by norm_num : (0 : ℝ) < 2) (hdiam p hp q hq hd)
        have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), coeff t < 0 :=
          eventually_nhdsWithin_of_eventually_nhds
            (hcoeff.continuousAt.eventually_lt continuousAt_const hneg)
        filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
        rw [← hd, ← sq_lt_sq₀ dist_nonneg dist_nonneg, hsquare]
        have hprod := mul_neg_of_pos_of_neg (show 0 < t from htpos) ht
        dsimp [coeff] at hprod
        nlinarith only [hprod]
      · have hstrict : dist (move 0 p) (move 0 q) < diam (A : Set ℝ²) := by
          rw [hzero]
          exact lt_of_le_of_ne (dist_le_diam_of_mem A.finite_toSet.isBounded hp hq) hd
        exact eventually_nhdsWithin_of_eventually_nhds
          (hc.continuousAt.eventually_lt continuousAt_const hstrict)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p ∈ A, ∀ q ∈ A,
      (p ≠ q → 1 ≤ dist (move t p) (move t q)) ∧
        dist (move t p) (move t q) < diam (A : Set ℝ²) :=
    (Finset.eventually_all A).mpr fun p hp =>
      (Finset.eventually_all A).mpr fun q hq => hpairs p hp q hq
  obtain ⟨t, ht⟩ := hall.exists
  exact no_separated_improvement hA hmin (move t)
    (fun p hp q hq => (ht p hp q hq).1) (fun p hp q hq => (ht p hp q hq).2)

/-- Some diametral pair of a minimizing configuration has a unit contact at each endpoint. -/
private lemma exists_diametral_pair_with_contacts {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A) :
    ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧
      (∃ x ∈ A, dist p x = 1) ∧ (∃ y ∈ A, dist q y = 1) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hA.2
  let touches (p : ℝ²) : Prop := ∃ x ∈ A, dist p x = 1
  have ha_contact : touches a := ⟨b, hb, hab⟩
  let v (p : ℝ²) : ℝ² := if touches p then 0 else a - p
  have hunit (p : ℝ²) (hp : p ∈ A) (q : ℝ²) (hq : q ∈ A) (hu : dist p q = 1) :
      0 ≤ ⟪p - q, v p - v q⟫_ℝ := by
    have hp_contact : touches p := ⟨q, hq, hu⟩
    have hq_contact : touches q := ⟨p, hp, (dist_comm q p).trans hu⟩
    simp [v, hp_contact, hq_contact]
  have hvel (p q : ℝ²) (hq : q ∈ A) (hd : dist p q = diam (A : Set ℝ²)) :
      ⟪p - q, v p⟫_ℝ ≤ 0 ∧ (0 ≤ ⟪p - q, v p⟫_ℝ → touches p) := by
    by_cases h : touches p
    · simp [v, h]
    · have hne : p ≠ a := fun heq => h (heq ▸ ha_contact)
      have hbound : ‖(p - q) - (p - a)‖ ≤ ‖p - q‖ := by
        have heq : (p - q) - (p - a) = a - q := by abel
        rw [heq, ← dist_eq_norm, ← dist_eq_norm, hd]
        exact dist_le_diam_of_mem A.finite_toSet.isBounded ha hq
      have hnorm := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hbound
      rw [norm_sub_sq_real] at hnorm
      have hpos : 0 < ‖p - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hneg : ⟪p - q, v p⟫_ℝ < 0 := by
        simp only [v, if_neg h, ← neg_sub p a, inner_neg_right]
        nlinarith [sq_pos_of_pos hpos]
      exact ⟨hneg.le, fun hh => (not_le_of_gt hneg hh).elim⟩
  obtain ⟨p, hp, q, hq, hd, hnonneg⟩ := no_contracting_velocity hA hmin v hunit
  have hl := hvel p q hq hd
  have hr := hvel q p hp ((dist_comm q p).trans hd)
  have heq : ⟪p - q, v q⟫_ℝ = -⟪q - p, v q⟫_ℝ := by
    rw [← neg_sub q p, inner_neg_left]
  rw [inner_sub_right, heq] at hnonneg
  exact ⟨p, hp, q, hq, hd, hl.2 (by linarith [hr.1]), hr.2 (by linarith [hl.1])⟩

private def UnitContact (A : Finset ℝ²) (p q : ℝ²) : Prop :=
  p ∈ A ∧ q ∈ A ∧ dist p q = 1

private def UnitConnected (A : Finset ℝ²) : ℝ² → ℝ² → Prop :=
  Relation.EqvGen (UnitContact A)

/-- Some component of the unit-contact graph spans at least half the diameter.
Move each component toward the origin at the velocity of its chosen representative. -/
private lemma exists_wide_contact_component {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A) :
    ∃ p ∈ A, ∃ q ∈ A, UnitConnected A p q ∧ diam (A : Set ℝ²) / 2 ≤ dist p q := by
  classical
  let center (p : ℝ²) := (Quot.mk (UnitContact A) p).out
  have hconnected (p : ℝ²) : UnitConnected A p (center p) :=
    Quot.eqvGen_exact (Quot.out_eq (Quot.mk (UnitContact A) p)).symm
  have hmem {p q : ℝ²} (h : UnitConnected A p q) : p ∈ A ↔ q ∈ A := by
    induction h with
    | rel _ _ hu => exact ⟨fun _ => hu.2.1, fun _ => hu.1⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let v (p : ℝ²) := -center p
  have hunit (p : ℝ²) (hp : p ∈ A) (q : ℝ²) (hq : q ∈ A) (hu : dist p q = 1) :
      0 ≤ ⟪p - q, v p - v q⟫_ℝ := by
    have hc : center p = center q :=
      congrArg Quot.out (Quot.sound (r := UnitContact A) ⟨hp, hq, hu⟩)
    change 0 ≤ ⟪p - q, -center p - -center q⟫_ℝ
    rw [hc, sub_self, inner_zero_right]
  obtain ⟨p, hp, q, hq, hd, hnonneg⟩ := no_contracting_velocity hA hmin v hunit
  have hv : v p - v q = -(center p - center q) := by dsimp [v]; abel
  rw [hv, inner_neg_right] at hnonneg
  have hbound : dist p q ≤ dist p (center p) + dist q (center q) := by
    simp only [dist_eq_norm]
    calc
      ‖p - q‖ ≤ ‖(p - q) - (center p - center q)‖ := by
        apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [norm_sub_sq_real (p - q) (center p - center q)]
        linarith only [hnonneg, sq_nonneg ‖center p - center q‖]
      _ = ‖(p - center p) - (q - center q)‖ := by congr 1; abel
      _ ≤ ‖p - center p‖ + ‖q - center q‖ := norm_sub_le _ _
  by_cases h : diam (A : Set ℝ²) / 2 ≤ dist p (center p)
  · exact ⟨p, hp, center p, (hmem (hconnected p)).mp hp, hconnected p, h⟩
  · exact ⟨q, hq, center q, (hmem (hconnected q)).mp hq, hconnected q, by linarith⟩

private abbrev Configuration (A : Finset ℝ²) := PiLp 2 (fun _ : A => ℝ²)

private noncomputable def pairGradient {A : Finset ℝ²} (p q : A) : Configuration A := by
  classical
  exact PiLp.single 2 p ((p : ℝ²) - q) - PiLp.single 2 q ((p : ℝ²) - q)

private lemma inner_pairGradient {A : Finset ℝ²} (p q : A) (v : Configuration A) :
    ⟪pairGradient p q, v⟫_ℝ = ⟪(p : ℝ²) - q, v p - v q⟫_ℝ := by
  classical
  have hsingle (x : A) (z : ℝ²) :
      ⟪(PiLp.single 2 x z : Configuration A), v⟫_ℝ = ⟪z, v x⟫_ℝ := by
    rw [PiLp.inner_apply, Finset.sum_eq_single x]
    · simp
    · intro b _ hne
      simp [hne]
    · simp
  rw [pairGradient, inner_sub_left, hsingle, hsingle, inner_sub_right]

private def signedGradients (A : Finset ℝ²) : Set (Configuration A) :=
  {g | ∃ p q : A, dist (p : ℝ²) q = 1 ∧ g = pairGradient p q} ∪
  {g | ∃ p q : A, dist (p : ℝ²) q = diam (A : Set ℝ²) ∧ g = -pairGradient p q}

/-- The gradients of unit contacts and the negatives of the gradients of diametral
pairs admit a convex combination equal to zero. -/
private lemma zero_mem_convexHull_signedGradients {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A) :
    (0 : Configuration A) ∈ convexHull ℝ (signedGradients A) := by
  classical
  let _ : NormedSpace ℝ (Configuration A) := PiLp.normedSpace 2 ℝ (fun _ : A => ℝ²)
  have : IsBoundedSMul ℝ (Configuration A) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := Configuration A)
  have : ContinuousSMul ℝ (Configuration A) := IsBoundedSMul.continuousSMul
  have : LocallyConvexSpace ℝ (Configuration A) := NormedSpace.toLocallyConvexSpace
  have : CompleteSpace (Configuration A) := PiLp.completeSpace 2 (fun _ : A => ℝ²)
  have hfinite : (signedGradients A).Finite := by
    refine ((Set.finite_range (fun z : A × A => pairGradient z.1 z.2)).union
      (Set.finite_range (fun z : A × A => -pairGradient z.1 z.2))).subset ?_
    rintro _ (⟨p, q, _, rfl⟩ | ⟨p, q, _, rfl⟩)
    · exact Or.inl ⟨(p, q), rfl⟩
    · exact Or.inr ⟨(p, q), rfl⟩
  by_contra h
  obtain ⟨f, c, hc, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ _) (hfinite.isClosed_convexHull ℝ) h
  have hcpos : 0 < c := by simpa using hc
  have hpos {g} (hg : g ∈ signedGradients A) : 0 < f g :=
    hcpos.trans (hsep g (subset_convexHull ℝ _ hg))
  let w : Configuration A := (InnerProductSpace.toDual ℝ (Configuration A)).symm f
  let v (p : ℝ²) : ℝ² := if hp : p ∈ A then w ⟨p, hp⟩ else 0
  have hdot (p q : A) : f (pairGradient p q) = ⟪(p : ℝ²) - q, w p - w q⟫_ℝ := by
    calc
      f (pairGradient p q) = ⟪w, pairGradient p q⟫_ℝ :=
        (InnerProductSpace.toDual_symm_apply (x := pairGradient p q) (y := f)).symm
      _ = ⟪(p : ℝ²) - q, w p - w q⟫_ℝ :=
        (real_inner_comm _ _).trans (inner_pairGradient p q w)
  have hunit (p : ℝ²) (hp : p ∈ A) (q : ℝ²) (hq : q ∈ A) (hu : dist p q = 1) :
      0 ≤ ⟪p - q, v p - v q⟫_ℝ := by
    have hpq : pairGradient (⟨p, hp⟩ : A) ⟨q, hq⟩ ∈ signedGradients A :=
      Or.inl ⟨⟨p, hp⟩, ⟨q, hq⟩, hu, rfl⟩
    have hpos := (hpos hpq).le
    have hh := hpos.trans (hdot ⟨p, hp⟩ ⟨q, hq⟩).le
    simpa only [v, dif_pos hp, dif_pos hq] using hh
  obtain ⟨p, hp, q, hq, hd, hnonneg⟩ := no_contracting_velocity hA hmin v hunit
  have hpq : -pairGradient (⟨p, hp⟩ : A) ⟨q, hq⟩ ∈ signedGradients A :=
    Or.inr ⟨⟨p, hp⟩, ⟨q, hq⟩, hd, rfl⟩
  have hneg := hpos hpq
  rw [map_neg, hdot ⟨p, hp⟩ ⟨q, hq⟩] at hneg
  simp only [v, dif_pos hp, dif_pos hq] at hnonneg
  exact (not_lt_of_ge hnonneg) (neg_pos.mp hneg)

/-- With fixed separation, a bounded diameter imposes a uniform bound on cardinality. -/
private lemma eventually_diam_gt (R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², A.card = n →
      Erdos99.HasMinDist1 A → R < diam (A : Set ℝ²) := by
  classical
  obtain ⟨centers, hfinite, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : ℝ²) R).totallyBounded (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop (hfinite.toFinset.card + 1)] with n hn A hcard hA
  by_contra! hR
  obtain ⟨a, ha, _, _, _⟩ := hA.2
  have hcenter (x : A) : ∃ c : hfinite.toFinset, dist ((x : ℝ²) - a) c < 1 / 2 := by
    have hball : (x : ℝ²) - a ∈ closedBall (0 : ℝ²) R := by
      rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
      exact (dist_le_diam_of_mem A.finite_toSet.isBounded x.property ha).trans hR
    obtain ⟨c, hc⟩ := mem_iUnion.mp (hcover hball)
    obtain ⟨hct, hxc⟩ := mem_iUnion.mp hc
    exact ⟨⟨c, hfinite.mem_toFinset.mpr hct⟩, mem_ball.mp hxc⟩
  choose c hc using hcenter
  have hinj : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hdist : dist (x : ℝ²) y = dist ((x : ℝ²) - a) ((y : ℝ²) - a) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    have htri := dist_triangle ((x : ℝ²) - a) (c x : ℝ²) ((y : ℝ²) - a)
    rw [dist_comm (c x : ℝ²), hxy] at htri
    have hsep := hA.1 x x.property y y.property hne
    have hcx := hc x
    rw [hxy] at hcx
    linarith only [hdist, htri, hsep, hcx, hc y]
  have hbound := Finset.card_le_card_of_injective hinj
  omega

/-- A long contact component meets each unit-width annulus about one endpoint. -/
private lemma exists_unitConnected_in_annulus {A : Finset ℝ²} {p q : ℝ²}
    (hp : p ∈ A) (hpq : UnitConnected A p q) {r : ℝ} (hr : 0 ≤ r)
    (hrq : r ≤ dist p q) :
    ∃ x ∈ A, UnitConnected A p x ∧ r ≤ dist p x ∧ dist p x < r + 1 := by
  by_contra h
  have hrpos : 0 < r := by
    by_contra! hneg
    have heq : r = 0 := le_antisymm hneg hr
    exact h ⟨p, hp, Relation.EqvGen.refl _, by simp [heq]⟩
  have hsame {x y : ℝ²} (hc : UnitConnected A x y) :
      UnitConnected A p x → (dist p x < r ↔ dist p y < r) := by
    induction hc with
    | rel x y hu =>
      intro hpx
      have hpy : UnitConnected A p y := Relation.EqvGen.trans p x y hpx (Relation.EqvGen.rel _ _ hu)
      obtain ⟨hx, hy, hxy⟩ := hu
      constructor
      · intro hxr
        by_contra! hyr
        have htri := dist_triangle p x y
        exact h ⟨y, hy, hpy, hyr, by linarith⟩
      · intro hyr
        by_contra! hxr
        have htri := dist_triangle p y x
        rw [dist_comm y x] at htri
        exact h ⟨x, hx, hpx, hxr, by linarith⟩
    | refl => simp
    | symm x y hxy ih =>
      intro hpy
      exact (ih (Relation.EqvGen.trans p y x hpy hxy.symm)).symm
    | trans x y z hxy _ ihxy ihyz =>
      intro hpx
      exact (ihxy hpx).trans (ihyz (Relation.EqvGen.trans p x y hpx hxy))
  have hclose : dist p p < r := by simpa using hrpos
  exact (not_lt_of_ge hrq) ((hsame hpq (Relation.EqvGen.refl p)).mp hclose)

private lemma exists_contact_component_card_ge {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (k : ℕ) (hk : (k : ℝ) ≤ diam (A : Set ℝ²) / 2) :
    ∃ p ∈ A, ∃ C : Finset ℝ², C ⊆ A ∧ k + 1 ≤ C.card ∧ ∀ x ∈ C, UnitConnected A p x := by
  classical
  obtain ⟨p, hp, q, _, hpq, hwide⟩ := exists_wide_contact_component hA hmin
  let C := A.filter (UnitConnected A p)
  refine ⟨p, hp, C, Finset.filter_subset _ _, ?_, fun x hx => (Finset.mem_filter.mp hx).2⟩
  have hw (j : Finset.range (k + 1)) :
      ∃ x : C, (j.val : ℝ) ≤ dist p x ∧ dist p x < (j.val : ℝ) + 1 := by
    have hj : j.val ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp j.property)
    obtain ⟨x, hx, hconn, hlow, hhigh⟩ := exists_unitConnected_in_annulus hp hpq
      (Nat.cast_nonneg j.val) ((Nat.cast_le.mpr hj).trans (hk.trans hwide))
    exact ⟨⟨x, Finset.mem_filter.mpr ⟨hx, hconn⟩⟩, hlow, hhigh⟩
  choose f hf using hw
  have hfloor (j : Finset.range (k + 1)) : ⌊dist p (f j : ℝ²)⌋₊ = j.val := by
    apply le_antisymm _ (Nat.le_floor (hf j).1)
    have hle := Nat.floor_le (dist_nonneg (x := p) (y := (f j : ℝ²)))
    have hlt : (↑⌊dist p (f j : ℝ²)⌋₊ : ℝ) < (j.val : ℝ) + 1 :=
      hle.trans_lt (hf j).2
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    rw [← hfloor i, ← hfloor j, hij]
  simpa only [Finset.card_range] using Finset.card_le_card_of_injective hinj

/-- Every fixed size is eventually exceeded by some unit-contact component of any minimizer. -/
private lemma eventually_exists_large_contact_component (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², A.card = n → Erdos99.HasMinDist1 A →
      IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
        {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A →
      ∃ p ∈ A, ∃ C : Finset ℝ², C ⊆ A ∧ k + 1 ≤ C.card ∧ ∀ x ∈ C, UnitConnected A p x := by
  filter_upwards [eventually_diam_gt (2 * (k : ℝ))] with n hn A hcard hA hmin
  have hd := hn A hcard hA
  exact exists_contact_component_card_ge hA hmin k (by linarith)

private noncomputable def unitNeighbors (A : Finset ℝ²) (p : ℝ²) : Finset ℝ² := by
  classical
  exact A.filter (fun q => dist p q = 1)

/-- In a separated planar configuration with no unit triangle, each point has
at most five unit neighbors. -/
private lemma card_unitNeighbors_le_five {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hfree : ¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, Erdos99.FormsEquilateralTriangle p q r)
    (p : ℝ²) (hp : p ∈ A) : (unitNeighbors A p).card ≤ 5 := by
  classical
  let N := A.filter (fun q => dist p q = 1)
  change N.card ≤ 5
  rcases N.eq_empty_or_nonempty with hN | ⟨q₀, hq₀⟩
  · simp [hN]
  have hunit (q : ℝ²) (hq : q ∈ N) : dist p q = 1 := (Finset.mem_filter.mp hq).2
  have hsep (q : ℝ²) (hq : q ∈ N) (r : ℝ²) (hr : r ∈ N) (hne : q ≠ r) :
      1 < dist q r := by
    have hqA := (Finset.mem_filter.mp hq).1
    have hrA := (Finset.mem_filter.mp hr).1
    exact lt_of_le_of_ne (hA.1 q hqA r hrA hne)
      (fun heq => hfree ⟨p, hp, q, hqA, r, hrA, hunit q hq, heq.symm, hunit r hr⟩)
  let coord (x : ℝ²) : ℂ := ⟨x.ofLp 0, x.ofLp 1⟩
  have hsub (x y : ℝ²) : coord x - coord y = coord (x - y) := by
    apply Complex.ext <;> rfl
  have hnorm (x : ℝ²) : ‖coord x‖ = ‖x‖ := by
    have hsq : ‖coord x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp only [Real.norm_eq_abs, sq_abs]
      change x.ofLp 0 * x.ofLp 0 + x.ofLp 1 * x.ofLp 1 = x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2
      ring
    simpa only [Real.sqrt_sq (norm_nonneg _)] using congrArg Real.sqrt hsq
  have hpitch (q : ℝ²) (hq : q ∈ N) : ‖coord (q - p)‖ = 1 := by
    rw [hnorm, ← dist_eq_norm, dist_comm, hunit q hq]
  let z (q : ℝ²) := coord (q - p) / coord (q₀ - p)
  have hz (q : ℝ²) (hq : q ∈ N) : ‖z q‖ = 1 := by
    simp only [z, norm_div, hpitch q hq, hpitch q₀ hq₀, div_one]
  let angle (q : ℝ²) := (z q).arg
  have hangle₀ : angle q₀ = 0 := by
    simp [angle, z]
  have hdist (q r : ℝ²) : ‖z q - z r‖ = dist q r := by
    have heq : q - p - (r - p) = q - r := by abel
    dsimp only [z]
    rw [div_sub_div_same, norm_div, hpitch q₀ hq₀, div_one, hsub, heq, hnorm, dist_eq_norm]
  have hgap (q : ℝ²) (hq : q ∈ N) (r : ℝ²) (hr : r ∈ N) (hne : q ≠ r) :
      Real.pi / 3 < |angle q - angle r| := by
    by_contra! hsmall
    have hcos : (1 : ℝ) / 2 ≤ Real.cos (angle q - angle r) := by
      have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
        hsmall
      rwa [Real.cos_pi_div_three, Real.cos_abs] at hcos
    have hre (x : ℝ²) (hx : x ∈ N) : (z x).re = Real.cos (angle x) := by
      simpa only [hz x hx, one_mul, angle] using (Complex.norm_mul_cos_arg (z x)).symm
    have him (x : ℝ²) (hx : x ∈ N) : (z x).im = Real.sin (angle x) := by
      simpa only [hz x hx, one_mul, angle] using (Complex.norm_mul_sin_arg (z x)).symm
    have hsquare : dist q r ^ 2 = 2 - 2 * Real.cos (angle q - angle r) := by
      rw [← hdist, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        hre q hq, hre r hr, him q hq, him r hr, Real.cos_sub]
      nlinarith only [Real.cos_sq_add_sin_sq (angle q), Real.cos_sq_add_sin_sq (angle r)]
    have hgt := (sq_lt_sq₀ zero_le_one dist_nonneg).mpr (hsep q hq r hr hne)
    linarith only [hsquare, hgt, hcos]
  let score (q : ℝ²) := (Real.pi - angle q) / (Real.pi / 3)
  let sector (q : ℝ²) := ⌊score q⌋₊
  have hwidth : 0 < Real.pi / 3 := by positivity
  have hsnonneg (q : ℝ²) : 0 ≤ score q :=
    div_nonneg (sub_nonneg.mpr (Complex.arg_le_pi (z q))) hwidth.le
  have hslt (q : ℝ²) : sector q < 6 := by
    apply (Nat.floor_lt (hsnonneg q)).mpr
    apply (div_lt_iff₀ hwidth).mpr
    have ha := Complex.neg_pi_lt_arg (z q)
    change -Real.pi < angle q at ha
    norm_num
    linarith
  let allowed : Finset ℕ := {0, 1, 4, 5}
  have hmap : Set.MapsTo sector (↑(N.erase q₀) : Set ℝ²) (allowed : Set ℕ) := by
    intro q hq
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hq
    have hw := hgap q hmem q₀ hq₀ hne
    rw [hangle₀, sub_zero] at hw
    have hlt := hslt q
    change sector q ∈ allowed
    by_cases hs : 0 ≤ angle q
    · rw [abs_of_nonneg hs] at hw
      have hle : sector q < 2 := by
        apply (Nat.floor_lt (hsnonneg q)).mpr
        apply (div_lt_iff₀ hwidth).mpr
        norm_num
        linarith
      simp [allowed]
      omega
    · rw [abs_of_neg (lt_of_not_ge hs)] at hw
      have hle : 4 ≤ sector q := by
        apply Nat.le_floor
        apply (le_div_iff₀ hwidth).mpr
        norm_num
        linarith
      simp [allowed]
      omega
  have hinj : Set.InjOn sector (↑(N.erase q₀) : Set ℝ²) := by
    intro q hq r hr heq
    by_contra hne
    have hlowq := Nat.floor_le (hsnonneg q)
    have hlowr := Nat.floor_le (hsnonneg r)
    have hhighq := Nat.lt_floor_add_one (score q)
    have hhighr := Nat.lt_floor_add_one (score r)
    change ⌊score q⌋₊ = ⌊score r⌋₊ at heq
    rw [heq] at hlowq hhighq
    have hclose : |score q - score r| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    change |(Real.pi - angle q) / (Real.pi / 3) -
      (Real.pi - angle r) / (Real.pi / 3)| < 1 at hclose
    rw [← sub_div, show Real.pi - angle q - (Real.pi - angle r) =
      -(angle q - angle r) by ring, abs_div, abs_neg, abs_of_pos hwidth, div_lt_iff₀ hwidth,
      one_mul] at hclose
    exact (not_lt_of_ge hclose.le)
      (hgap q (Finset.mem_of_mem_erase hq) r (Finset.mem_of_mem_erase hr) hne)
  have hcard := Finset.card_le_card_of_injOn sector hmap hinj
  have hallowed : allowed.card = 4 := by decide
  rw [hallowed, Finset.card_erase_of_mem hq₀] at hcard
  omega

/-- An oversized separated configuration of strictly smaller diameter contains
an equal-cardinality improvement. -/
private lemma hasSeparatedImprovement_of_short_packing {A B : Finset ℝ²}
    (hcard : A.card ≤ B.card)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q)
    (hshort : ∀ p ∈ B, ∀ q ∈ B, dist p q < diam (A : Set ℝ²)) :
    HasSeparatedImprovement A := by
  classical
  obtain ⟨C, hCB, hCA⟩ := Finset.exists_subset_card_eq hcard
  let e : A ≃ C := Finset.equivOfCardEq hCA.symm
  let f (p : ℝ²) : ℝ² := if hp : p ∈ A then (e ⟨p, hp⟩ : ℝ²) else p
  have hf (p : ℝ²) (hp : p ∈ A) : f p = (e ⟨p, hp⟩ : ℝ²) := by simp [f, hp]
  have hmem (p : ℝ²) (hp : p ∈ A) : f p ∈ B := by
    rw [hf p hp]
    exact hCB (e ⟨p, hp⟩).property
  refine ⟨f, ?_, fun p hp q hq => hshort _ (hmem p hp) _ (hmem q hq)⟩
  intro p hp q hq hne
  apply hsep _ (hmem p hp) _ (hmem q hq)
  rw [hf p hp, hf q hq]
  intro heq
  exact hne (congrArg Subtype.val (e.injective (Subtype.ext heq)))

/-- To obtain a strict improvement, a competitor may discard vertices meeting
every pair at or above the old diameter. -/
private lemma card_lt_add_of_diametral_cover {A B S : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun C : Finset ℝ² => diam (C : Set ℝ²))
      {C : Finset ℝ² | C.card = A.card ∧ Erdos99.HasMinDist1 C} A)
    (hSB : S ⊆ B)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q)
    (hcover : ∀ p ∈ B, ∀ q ∈ B, diam (A : Set ℝ²) ≤ dist p q → p ∈ S ∨ q ∈ S) :
    B.card < A.card + S.card := by
  classical
  by_contra! hcard
  have heq := Finset.card_sdiff_add_card_eq_card hSB
  refine (isMinOn_iff_no_separated_improvement hA).mp hmin
    (hasSeparatedImprovement_of_short_packing (B := B \ S) (by omega) ?_ ?_)
  · intro p hp q hq hne
    exact hsep p (Finset.mem_sdiff.mp hp).1 q (Finset.mem_sdiff.mp hq).1 hne
  · intro p hp q hq
    obtain ⟨hpB, hpS⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hqB, hqS⟩ := Finset.mem_sdiff.mp hq
    exact lt_of_not_ge (fun h => (hcover p hpB q hqB h).elim hpS hqS)

private def hexIndices (m : ℕ) : Finset (Fin 3 × ℕ × ℕ) :=
  Finset.univ ×ˢ (Finset.Icc 1 m ×ˢ Finset.Icc 0 m)

private def hexIndex (x : Fin 3 × ℕ × ℕ) : ℤ × ℤ :=
  let a := (x.2.1 : ℤ)
  let b := (x.2.2 : ℤ)
  if x.1 = 0 then (a, b) else if x.1 = 1 then (-b, a - b) else (b - a, -a)

private lemma hexIndex_injOn (m : ℕ) : Set.InjOn hexIndex (hexIndices m : Set _) := by
  rintro ⟨k, a, b⟩ hx ⟨l, c, d⟩ hy h
  change (k, a, b) ∈ hexIndices m at hx
  change (l, c, d) ∈ hexIndices m at hy
  obtain ⟨ha, _⟩ := Finset.mem_product.mp (Finset.mem_product.mp hx).2
  obtain ⟨hc, _⟩ := Finset.mem_product.mp (Finset.mem_product.mp hy).2
  have ha₀ : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hc₀ : 1 ≤ c := (Finset.mem_Icc.mp hc).1
  fin_cases k <;> fin_cases l <;> simp [hexIndex] at h
  all_goals first | (exfalso; omega) | (congr 1; apply Prod.ext <;> omega)

private noncomputable def latticePoint (i : ℤ × ℤ) : ℝ² :=
  WithLp.toLp 2 ![(i.1 : ℝ) - (i.2 : ℝ) / 2, Real.sqrt 3 * (i.2 : ℝ) / 2]

private def hexQuadratic (a b : ℤ) : ℤ := a ^ 2 - a * b + b ^ 2

private lemma latticePoint_dist_sq (u v : ℤ × ℤ) :
    dist (latticePoint u) (latticePoint v) ^ 2 =
      (hexQuadratic (u.1 - v.1) (u.2 - v.2) : ℝ) := by
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  change (((u.1 : ℝ) - (u.2 : ℝ) / 2) - ((v.1 : ℝ) - (v.2 : ℝ) / 2)) ^ 2 +
    (Real.sqrt 3 * (u.2 : ℝ) / 2 - Real.sqrt 3 * (v.2 : ℝ) / 2) ^ 2 = _
  simp only [hexQuadratic, Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_mul]
  rw [show (Real.sqrt 3 * (u.2 : ℝ) / 2 - Real.sqrt 3 * (v.2 : ℝ) / 2) ^ 2 =
      (Real.sqrt 3) ^ 2 * ((u.2 : ℝ) - (v.2 : ℝ)) ^ 2 / 4 by ring,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

private lemma one_le_latticePoint_dist {u v : ℤ × ℤ} (hne : u ≠ v) :
    1 ≤ dist (latticePoint u) (latticePoint v) := by
  let a := u.1 - v.1
  let b := u.2 - v.2
  have hpos : 0 < hexQuadratic a b := by
    have heq : 4 * hexQuadratic a b = (2 * a - b) ^ 2 + 3 * b ^ 2 := by
      unfold hexQuadratic
      ring
    have hsum : 0 < (2 * a - b) ^ 2 + 3 * b ^ 2 := by
      by_cases hb : b = 0
      · have ha : a ≠ 0 := by
          intro ha
          exact hne (Prod.ext (sub_eq_zero.mp ha) (sub_eq_zero.mp hb))
        simpa [hb] using sq_pos_of_ne_zero (mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) ha)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_ne_zero hb))
    omega
  have hle : 1 ≤ hexQuadratic a b := by omega
  apply (sq_le_sq₀ zero_le_one dist_nonneg).mp
  rw [latticePoint_dist_sq, one_pow]
  exact_mod_cast hle

private lemma latticePoint_injective : Function.Injective latticePoint := by
  intro u v heq
  by_contra hne
  have hd := one_le_latticePoint_dist hne
  rw [heq, dist_self] at hd
  norm_num at hd

private lemma latticePoint_zero : latticePoint (0, 0) = 0 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [latticePoint]

private lemma hexQuadratic_le_sq {a b r : ℤ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b)
    (ha : a ≤ r) (hb : b ≤ r) : hexQuadratic a b ≤ r ^ 2 := by
  have hr : 0 ≤ r := ha₀.trans ha
  rcases le_total a b with hab | hba
  · calc
      hexQuadratic a b = b ^ 2 + a * (a - b) := by unfold hexQuadratic; ring
      _ ≤ b ^ 2 := by
        have h := mul_nonpos_of_nonneg_of_nonpos ha₀ (sub_nonpos.mpr hab)
        omega
      _ ≤ r ^ 2 := (sq_le_sq₀ hb₀ hr).mpr hb
  · calc
      hexQuadratic a b = a ^ 2 + b * (b - a) := by unfold hexQuadratic; ring
      _ ≤ a ^ 2 := by
        have h := mul_nonpos_of_nonneg_of_nonpos hb₀ (sub_nonpos.mpr hba)
        omega
      _ ≤ r ^ 2 := (sq_le_sq₀ ha₀ hr).mpr ha

private lemma norm_latticePoint_hexIndex_le {m : ℕ} {x : Fin 3 × ℕ × ℕ}
    (hx : x ∈ hexIndices m) : ‖latticePoint (hexIndex x)‖ ≤ (m : ℝ) := by
  obtain ⟨k, a, b⟩ := x
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_product.mp hx).2
  have hquad : hexQuadratic (a : ℤ) (b : ℤ) ≤ (m : ℤ) ^ 2 :=
    hexQuadratic_le_sq (by positivity) (by positivity)
      (by exact_mod_cast (Finset.mem_Icc.mp ha).2) (by exact_mod_cast (Finset.mem_Icc.mp hb).2)
  have hrot : hexQuadratic (hexIndex (k, a, b)).1 (hexIndex (k, a, b)).2 =
      hexQuadratic (a : ℤ) (b : ℤ) := by
    fin_cases k <;> simp [hexIndex, hexQuadratic] <;> ring
  have hd := latticePoint_dist_sq (hexIndex (k, a, b)) (0, 0)
  simp only [latticePoint_zero, dist_zero_right, sub_zero, hrot] at hd
  apply (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg m)).mp
  rw [hd]
  exact_mod_cast hquad

/-- Three sectors of the triangular lattice and the origin give the hexagonal
packing of radius `m`, including its outer boundary. -/
private lemma exists_hexagonal_packing (m : ℕ) :
    ∃ B : Finset ℝ², B.card = 3 * m * (m + 1) + 1 ∧
      (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧
      ∀ p ∈ B, ∀ q ∈ B, dist p q ≤ 2 * (m : ℝ) := by
  classical
  let L := (hexIndices m).image hexIndex
  let C := insert (0, 0) L
  let B := C.image latticePoint
  have hnot : (0, 0) ∉ L := by
    intro hz
    obtain ⟨⟨k, a, b⟩, hmem, heq⟩ := Finset.mem_image.mp hz
    obtain ⟨ha, _⟩ := Finset.mem_product.mp (Finset.mem_product.mp hmem).2
    have ha₀ : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    fin_cases k <;> simp [hexIndex] at heq <;> omega
  have hradius (u : ℤ × ℤ) (hu : u ∈ C) : ‖latticePoint u‖ ≤ (m : ℝ) := by
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rw [latticePoint_zero, norm_zero]
      positivity
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      exact norm_latticePoint_hexIndex_le hx
  refine ⟨B, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn latticePoint_injective.injOn, Finset.card_insert_of_notMem hnot,
      Finset.card_image_of_injOn (hexIndex_injOn m)]
    simp [hexIndices, Nat.card_Icc, Nat.mul_assoc]
  · intro p hp q hq hne
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq
    exact one_le_latticePoint_dist (fun heq => hne (congrArg latticePoint heq))
  · intro p hp q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    have htri := dist_triangle (latticePoint x) 0 (latticePoint y)
    rw [dist_zero_right, dist_zero_left] at htri
    linarith only [htri, hradius x hx, hradius y hy]

private lemma diam_le_two_mul_of_card_le {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (m : ℕ) (hm : A.card ≤ 3 * m * (m + 1) + 1) : diam (A : Set ℝ²) ≤ 2 * (m : ℝ) := by
  by_contra! hdiam
  obtain ⟨B, hcard, hsep, hshort⟩ := exists_hexagonal_packing m
  exact (isMinOn_iff_no_separated_improvement hA).mp hmin
    (hasSeparatedImprovement_of_short_packing (hm.trans hcard.symm.le) hsep
      (fun p hp q hq => (hshort p hp q hq).trans_lt hdiam))

open MeasureTheory
open scoped ENNReal

/-- A set of volume greater than `n` fundamental domains contains `n` points
of some translate of the lattice. -/
private lemma exists_translate_finset_of_volume {L : AddSubgroup ℝ²} [Countable L]
    {F S : Set ℝ²} (hF : IsAddFundamentalDomain L F volume) (hS : MeasurableSet S)
    {n : ℕ} (hvol : (n : ℝ≥0∞) * volume F < volume S) :
    ∃ x : ℝ², ∃ C : Finset L, C.card = n ∧ ∀ p ∈ C, (p : ℝ²) + x ∈ S := by
  classical
  by_contra! hnone
  let f (l : L) (x : ℝ²) : ℝ≥0∞ := S.indicator (fun _ => 1) ((l : ℝ²) + x)
  have hf (l : L) : Measurable (f l) :=
    (measurable_const.indicator hS).comp (measurable_const.add measurable_id)
  have hpointwise (x : ℝ²) : (∑' l : L, f l x) ≤ (n : ℝ≥0∞) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun C => ?_
    let T := C.filter (fun l : L => (l : ℝ²) + x ∈ S)
    have hcard : T.card ≤ n := by
      by_contra! hbig
      obtain ⟨U, hUT, hcard⟩ := Finset.exists_subset_card_eq hbig.le
      obtain ⟨p, hpU, hpS⟩ := hnone x U hcard
      exact hpS (Finset.mem_filter.mp (hUT hpU)).2
    have hsum : (∑ l ∈ C, f l x) = (T.card : ℝ≥0∞) := by
      simp [f, T, Set.indicator_apply]
    rw [hsum]
    exact Nat.cast_le.mpr hcard
  have hle : volume S ≤ (n : ℝ≥0∞) * volume F := calc
    volume S = ∫⁻ x, S.indicator (fun _ => 1) x := by
      rw [lintegral_indicator hS, setLIntegral_one]
    _ = ∑' l : L, ∫⁻ x in F, f l x := hF.lintegral_eq_tsum'' _
    _ = ∫⁻ x in F, ∑' l : L, f l x := (lintegral_tsum (fun l => (hf l).aemeasurable)).symm
    _ ≤ ∫⁻ _ in F, (n : ℝ≥0∞) := lintegral_mono hpointwise
    _ = (n : ℝ≥0∞) * volume F := by simp
  exact (not_lt_of_ge hle) hvol

private noncomputable def hexCoordinateEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![x 0 - x 1 / 2, (Real.sqrt 3 / 2) * x 1]
  invFun y := ![y 0 + (y 1 / (Real.sqrt 3 / 2)) / 2, y 1 / (Real.sqrt 3 / 2)]
  left_inv x := by
    have hr : Real.sqrt 3 / 2 ≠ 0 := by positivity
    funext i
    fin_cases i <;> simp
  right_inv y := by
    have hr : Real.sqrt 3 / 2 ≠ 0 := by positivity
    funext i
    fin_cases i
    · simp
    · simp
      field_simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

private noncomputable def hexBasisPi : Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
  (Pi.basisFun ℝ (Fin 2)).map hexCoordinateEquiv

private noncomputable def hexBasis : Module.Basis (Fin 2) ℝ ℝ² :=
  hexBasisPi.map (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm

private lemma hexBasis_repr (x : ℝ²) (i : Fin 2) :
    hexBasis.repr x i = hexCoordinateEquiv.symm x.ofLp i := by
  simp [hexBasis, hexBasisPi, Module.Basis.map_repr]

private lemma hexFundamentalDomain_volume :
    volume (ZSpan.fundamentalDomain hexBasis) = ENNReal.ofReal (Real.sqrt 3 / 2) := by
  have hmeas := ZSpan.fundamentalDomain_measurableSet hexBasis
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage hmeas.nullMeasurableSet]
  have hpre : (WithLp.toLp 2) ⁻¹' ZSpan.fundamentalDomain hexBasis =
      ZSpan.fundamentalDomain hexBasisPi := by
    ext x
    simp [ZSpan.mem_fundamentalDomain, hexBasis, Module.Basis.map_repr]
  rw [hpre, ZSpan.volume_fundamentalDomain, Matrix.det_fin_two]
  have hr : 0 ≤ Real.sqrt 3 / 2 := by positivity
  simp [hexBasisPi, hexCoordinateEquiv, Matrix.of_apply, Pi.basisFun_apply, abs_of_nonneg hr]

private lemma mem_hexSpan_iff_exists_latticePoint (x : ℝ²) :
    x ∈ Submodule.span ℤ (Set.range hexBasis) ↔ ∃ u : ℤ × ℤ, latticePoint u = x := by
  rw [hexBasis.mem_span_iff_repr_mem ℤ]
  have hcoord (u : ℤ × ℤ) : (latticePoint u).ofLp =
      hexCoordinateEquiv ![(u.1 : ℝ), (u.2 : ℝ)] := by
    funext i
    fin_cases i <;> simp [latticePoint, hexCoordinateEquiv]
    ring
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := hx 0
    obtain ⟨b, hb⟩ := hx 1
    refine ⟨(a, b), ?_⟩
    apply PiLp.ext
    have heq : ![(a : ℝ), (b : ℝ)] = hexCoordinateEquiv.symm x.ofLp := by
      funext i
      fin_cases i <;> simp [← hexBasis_repr, ← ha, ← hb]
    rw [hcoord, heq, LinearEquiv.apply_symm_apply]
    exact fun _ => rfl
  · rintro ⟨u, rfl⟩ i
    rw [hexBasis_repr, hcoord, LinearEquiv.symm_apply_apply]
    fin_cases i
    · exact ⟨u.1, rfl⟩
    · exact ⟨u.2, rfl⟩

/-- Averaging over translations produces a unit-separated subset of any
measurable region with sufficient area. -/
private lemma exists_separated_finset_of_volume {S : Set ℝ²} (hS : MeasurableSet S)
    {n : ℕ} (hvol : (n : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 3 / 2) < volume S) :
    ∃ B : Finset ℝ², B.card = n ∧ (B : Set ℝ²) ⊆ S ∧
      ∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q := by
  classical
  let L := (Submodule.span ℤ (Set.range hexBasis)).toAddSubgroup
  let : Countable L := inferInstanceAs (Countable (Submodule.span ℤ (Set.range hexBasis)))
  have hF : IsAddFundamentalDomain L (ZSpan.fundamentalDomain hexBasis) volume :=
    ZSpan.isAddFundamentalDomain' hexBasis volume
  obtain ⟨x, C, hcard, hmem⟩ := exists_translate_finset_of_volume hF hS
    (by simpa only [hexFundamentalDomain_volume] using hvol)
  let f (p : L) : ℝ² := (p : ℝ²) + x
  have hfinj : Function.Injective f := fun _ _ h => Subtype.ext (add_right_cancel h)
  let B := C.image f
  refine ⟨B, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hfinj.injOn, hcard]
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    exact hmem u hu
  · intro p hp q hq hne
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨i, hi⟩ := (mem_hexSpan_iff_exists_latticePoint u).mp u.property
    obtain ⟨j, hj⟩ := (mem_hexSpan_iff_exists_latticePoint v).mp v.property
    have hne' : i ≠ j := by
      intro h
      subst j
      exact hne (congrArg f (Subtype.ext (hi.symm.trans hj)))
    change 1 ≤ dist ((u : ℝ²) + x) ((v : ℝ²) + x)
    rw [dist_add_right, ← hi, ← hj]
    exact one_le_latticePoint_dist hne'

/-- A translate of the triangular lattice supplies a disk competitor whenever
the disk area exceeds the cardinality times the lattice covolume. -/
private lemma diam_lt_two_mul_of_disk_area {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    {r : ℝ} (hr : 0 ≤ r) (harea : (A.card : ℝ) * (Real.sqrt 3 / 2) < r ^ 2 * Real.pi) :
    diam (A : Set ℝ²) < 2 * r := by
  classical
  by_contra! hd
  have hvol : (A.card : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 3 / 2) <
      volume (ball (0 : ℝ²) r) := by
    rw [EuclideanSpace.volume_ball_fin_two,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (sq_nonneg r)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr harea
  obtain ⟨B, hcard, hmem, hsep⟩ := exists_separated_finset_of_volume isOpen_ball.measurableSet hvol
  refine (isMinOn_iff_no_separated_improvement hA).mp hmin
    (hasSeparatedImprovement_of_short_packing hcard.ge hsep ?_)
  intro p hp q hq
  have htri := dist_triangle p 0 q
  rw [dist_comm 0 q] at htri
  have hlp : dist p 0 < r := mem_ball.mp (hmem hp)
  have hlq : dist q 0 < r := mem_ball.mp (hmem hq)
  linarith

private lemma diam_sq_le_lattice_density {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A) :
    (diam (A : Set ℝ²) / 2) ^ 2 * Real.pi ≤ (A.card : ℝ) * (Real.sqrt 3 / 2) := by
  by_contra! harea
  have hdiam := diam_lt_two_mul_of_disk_area hA hmin (by positivity) harea
  linarith

/-- After retaining a strictly narrower subset, a region compatible with it
has area at most the triangular-lattice allowance for the discarded points. -/
private lemma volume_le_of_retained_subset {A K : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (hKA : K ⊆ A) (hK : ∀ p ∈ K, ∀ q ∈ K, dist p q < diam (A : Set ℝ²))
    {S : Set ℝ²} (hS : MeasurableSet S)
    (hSshort : ∀ p ∈ S, ∀ q ∈ S, dist p q < diam (A : Set ℝ²))
    (hcross : ∀ p ∈ K, ∀ q ∈ S, 1 ≤ dist p q ∧ dist p q < diam (A : Set ℝ²)) :
    volume S ≤ ((A.card - K.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 3 / 2) := by
  classical
  by_contra! hvolume
  obtain ⟨B, hBcard, hBS, hBsep⟩ := exists_separated_finset_of_volume hS hvolume
  have hdisj : Disjoint K B := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hsep := (hcross _ hp _ (hBS hq)).1
    rw [dist_self] at hsep
    norm_num at hsep
  have hcard : A.card ≤ (K ∪ B).card := by
    rw [Finset.card_union_of_disjoint hdisj, hBcard]
    omega
  refine (isMinOn_iff_no_separated_improvement hA).mp hmin
    (hasSeparatedImprovement_of_short_packing hcard ?_ ?_)
  · intro p hp q hq hne
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · exact hA.1 p (hKA hp) q (hKA hq) hne
    · exact (hcross p hp q (hBS hq)).1
    · rw [dist_comm]
      exact (hcross q hq p (hBS hp)).1
    · exact hBsep p hp q hq hne
  · intro p hp q hq
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · exact hK p hp q hq
    · exact (hcross p hp q (hBS hq)).2
    · rw [dist_comm]
      exact (hcross q hq p (hBS hp)).2
    · exact hSshort p (hBS hp) q (hBS hq)

private def replacementRegion (A K : Finset ℝ²) (c : ℝ²) : Set ℝ² :=
  ball c (diam (A : Set ℝ²) / 2) ∩
    ⋂ p : K, (ball (p : ℝ²) (diam (A : Set ℝ²)) \ ball (p : ℝ²) 1)

private lemma volume_replacementRegion_le {A K : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (hKA : K ⊆ A) (hK : ∀ p ∈ K, ∀ q ∈ K, dist p q < diam (A : Set ℝ²)) (c : ℝ²) :
    volume (replacementRegion A K c) ≤
      ((A.card - K.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 3 / 2) := by
  apply volume_le_of_retained_subset hA hmin hKA hK
  · exact isOpen_ball.measurableSet.inter
      (MeasurableSet.iInter fun _ => isOpen_ball.measurableSet.diff isOpen_ball.measurableSet)
  · intro p hp q hq
    have hpc := mem_ball.mp hp.1
    have hqc := mem_ball.mp hq.1
    have htri := dist_triangle p c q
    rw [dist_comm c q] at htri
    linarith
  · intro p hp q hq
    have ⟨hupper, hlower⟩ := mem_iInter.mp hq.2 (⟨p, hp⟩ : K)
    rw [dist_comm]
    exact ⟨le_of_not_gt (fun h => hlower (mem_ball.mpr h)), mem_ball.mp hupper⟩

private def HasReplacementVolumeBounds (A : Finset ℝ²) : Prop :=
  ∀ K : Finset ℝ², K ⊆ A → (∀ p ∈ K, ∀ q ∈ K, dist p q < diam (A : Set ℝ²)) →
    ∀ c : ℝ², volume (replacementRegion A K c) ≤
      ((A.card - K.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 3 / 2)

end OMA.Erdos99

theorem OMA.solution : type_of% @Erdos99.erdos_99 := by
  suffices improve : ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℝ², A.card = n →
      Erdos99.HasMinDist1 A →
      (∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧
        (∃ x ∈ A, dist p x = 1) ∧ (∃ y ∈ A, dist q y = 1)) →
      (∃ p ∈ A, ∃ q ∈ A, OMA.Erdos99.UnitConnected A p q ∧
        diam (A : Set ℝ²) / 2 ≤ dist p q) →
      (∃ p ∈ A, ∃ C : Finset ℝ², C ⊆ A ∧ ⌊diam (A : Set ℝ²) / 2⌋₊ + 1 ≤ C.card ∧
        ∀ x ∈ C, OMA.Erdos99.UnitConnected A p x) →
      (∀ p ∈ A, (OMA.Erdos99.unitNeighbors A p).card ≤ 5) →
      (∀ m : ℕ, A.card ≤ 3 * m * (m + 1) + 1 → diam (A : Set ℝ²) ≤ 2 * (m : ℝ)) →
      ((diam (A : Set ℝ²) / 2) ^ 2 * Real.pi ≤ (A.card : ℝ) * (Real.sqrt 3 / 2)) →
      OMA.Erdos99.HasReplacementVolumeBounds A →
      (0 : OMA.Erdos99.Configuration A) ∈ convexHull ℝ (OMA.Erdos99.signedGradients A) →
      (¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, Erdos99.FormsEquilateralTriangle p q r) →
      OMA.Erdos99.HasSeparatedImprovement A by
    filter_upwards [improve] with n hn
    intro A hcard hA hmin
    have hmin' : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
        {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A := by
      simpa only [hcard] using hmin
    have hc := OMA.Erdos99.exists_diametral_pair_with_contacts hA hmin'
    have hw := OMA.Erdos99.exists_wide_contact_component hA hmin'
    have hlarge := OMA.Erdos99.exists_contact_component_card_ge hA hmin'
      ⌊diam (A : Set ℝ²) / 2⌋₊ (Nat.floor_le (by positivity))
    have hs := OMA.Erdos99.zero_mem_convexHull_signedGradients hA hmin'
    by_contra htriangle
    exact (OMA.Erdos99.isMinOn_iff_no_separated_improvement hA).mp hmin'
      (hn A hcard hA hc hw hlarge
        (OMA.Erdos99.card_unitNeighbors_le_five hA htriangle)
        (OMA.Erdos99.diam_le_two_mul_of_card_le hA hmin')
        (OMA.Erdos99.diam_sq_le_lattice_density hA hmin')
        (fun _ hKA hK c => OMA.Erdos99.volume_replacementRegion_le hA hmin' hKA hK c)
        hs htriangle)
  sorry
