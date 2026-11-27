import FormalConjectures.ErdosProblems.«97»

/-! Bounds for convex cuts with three unit-distance neighbors at every vertex. -/

-- Problem: Erdős Problem 97 — three unit distance cut min
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/97.lean:140 (declaration Erdos97.erdos_97.variants.three_unit_distance_cut_min)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Erdos97 EuclideanGeometry
open scoped BigOperators

private lemma planar_dist_sq (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma cross_unit_midpoints {a a' b b' : ℝ²}
    (ha : a ≠ a') (hb : b ≠ b')
    (hab : dist a b = 1) (hab' : dist a b' = 1)
    (ha'b : dist a' b = 1) (ha'b' : dist a' b' = 1) :
    midpoint ℝ a a' = midpoint ℝ b b' := by
  have dist_sq_one {x y : ℝ²} (h : dist x y = 1) :
      (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = 1 := by
    rw [← planar_dist_sq, h, one_pow]
  have e₁ := dist_sq_one hab
  have e₂ := dist_sq_one hab'
  have e₃ := dist_sq_one ha'b
  have e₄ := dist_sq_one ha'b'
  let u : ℝ² := a - a'
  let v : ℝ² := b - b'
  let w : ℝ² := a + a' - (b + b')
  have huv : u 0 * v 0 + u 1 * v 1 = 0 := by
    change (a 0 - a' 0) * (b 0 - b' 0) + (a 1 - a' 1) * (b 1 - b' 1) = 0
    linear_combination (-e₁ + e₂ + e₃ - e₄) / 2
  have huw : u 0 * w 0 + u 1 * w 1 = 0 := by
    change (a 0 - a' 0) * (a 0 + a' 0 - (b 0 + b' 0)) +
      (a 1 - a' 1) * (a 1 + a' 1 - (b 1 + b' 1)) = 0
    linear_combination (e₁ + e₂ - e₃ - e₄) / 2
  have hvw : v 0 * w 0 + v 1 * w 1 = 0 := by
    change (b 0 - b' 0) * (a 0 + a' 0 - (b 0 + b' 0)) +
      (b 1 - b' 1) * (a 1 + a' 1 - (b 1 + b' 1)) = 0
    linear_combination (-e₁ + e₂ - e₃ + e₄) / 2
  have normSq_ne {x : ℝ²} (hx : x ≠ 0) : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hdet : u 0 * w 1 - u 1 * w 0 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (normSq_ne (sub_ne_zero.mpr hb : v ≠ 0))
    linear_combination (v 0 * w 1 - v 1 * w 0) * huv +
      (v 1 * u 0 - v 0 * u 1) * hvw
  have hw₀ : w 0 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (normSq_ne (sub_ne_zero.mpr ha : u ≠ 0))
    linear_combination u 0 * huw - u 1 * hdet
  have hw₁ : w 1 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (normSq_ne (sub_ne_zero.mpr ha : u ≠ 0))
    linear_combination u 1 * huw + u 0 * hdet
  have hw : w = 0 := by
    ext i
    fin_cases i
    · exact hw₀
    · exact hw₁
  rw [midpoint_eq_smul_add, midpoint_eq_smul_add, sub_eq_zero.mp hw]

private lemma no_cross_unit_four_cycle {A B : Finset ℝ²}
    (h : Disjoint (convexHull ℝ (A : Set ℝ²)) (convexHull ℝ (B : Set ℝ²)))
    {a a' b b' : ℝ²} (ha : a ∈ A) (ha' : a' ∈ A)
    (hb : b ∈ B) (hb' : b' ∈ B) (haa' : a ≠ a') (hbb' : b ≠ b')
    (hab : dist a b = 1) (hab' : dist a b' = 1)
    (ha'b : dist a' b = 1) (ha'b' : dist a' b' = 1) : False := by
  have hA := (convex_convexHull ℝ (A : Set ℝ²)).midpoint_mem
    (subset_convexHull ℝ _ ha) (subset_convexHull ℝ _ ha')
  have hB := (convex_convexHull ℝ (B : Set ℝ²)).midpoint_mem
    (subset_convexHull ℝ _ hb) (subset_convexHull ℝ _ hb')
  rw [cross_unit_midpoints haa' hbb' hab hab' ha'b ha'b'] at hA
  exact Set.disjoint_left.mp h hA hB

private lemma twice_degree_add_one_le_side_card {A B : Finset ℝ²}
    (h : Disjoint (convexHull ℝ (A : Set ℝ²)) (convexHull ℝ (B : Set ℝ²)))
    (hAB : HasNUnitDistancePointsOn 3 A B) {a : ℝ²} (ha : a ∈ A) :
    2 * (B.filter fun b ↦ dist a b = 1).card + 1 ≤ A.card := by
  classical
  let T := B.filter fun b ↦ dist a b = 1
  let N (b : ℝ²) := (A.filter fun x ↦ dist b x = 1).erase a
  have hN : ∀ b ∈ T, 2 ≤ (N b).card := by
    intro b hb
    obtain ⟨hbB, hba⟩ := Finset.mem_filter.mp hb
    have hcard : 3 ≤ (A.filter fun x ↦ dist b x = 1).card := hAB b hbB
    have hmem : a ∈ A.filter (fun x ↦ dist b x = 1) :=
      Finset.mem_filter.mpr ⟨ha, (dist_comm b a).trans hba⟩
    change 2 ≤ ((A.filter fun x ↦ dist b x = 1).erase a).card
    rw [Finset.card_erase_of_mem hmem]
    omega
  have hdisj : (T : Set ℝ²).PairwiseDisjoint N := by
    intro b hb b' hb' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨hbB, hab⟩ := Finset.mem_filter.mp (show b ∈ T from hb)
    obtain ⟨hb'B, hab'⟩ := Finset.mem_filter.mp (show b' ∈ T from hb')
    obtain ⟨hxa, hxA, hbx⟩ := Finset.mem_erase.mp hx
      |>.imp_right Finset.mem_filter.mp
    have hb'x := (Finset.mem_filter.mp (Finset.mem_erase.mp hx').2).2
    exact no_cross_unit_four_cycle h ha hxA hbB hb'B hxa.symm hne
      hab hab' ((dist_comm x b).trans hbx) ((dist_comm x b').trans hb'x)
  have hsub : T.biUnion N ⊆ A.erase a := by
    intro x hx
    obtain ⟨b, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_erase.mpr ⟨hne, (Finset.mem_filter.mp hx).1⟩
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.card_erase_of_mem ha] at hcount
  have hsum : T.card * 2 ≤ ∑ b ∈ T, (N b).card := by
    calc
      T.card * 2 = ∑ _ ∈ T, 2 := (Finset.sum_const_nat fun _ _ ↦ rfl).symm
      _ ≤ _ := Finset.sum_le_sum hN
  change 2 * T.card + 1 ≤ A.card
  rw [Nat.mul_comm 2]
  exact (Nat.add_le_add_right (hsum.trans hcount) 1).trans_eq
    (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨a, ha⟩))

private lemma seven_le_side_card {A B : Finset ℝ²}
    (h : Disjoint (convexHull ℝ (A : Set ℝ²)) (convexHull ℝ (B : Set ℝ²)))
    (hne : A.Nonempty) (hBA : HasNUnitDistancePointsOn 3 B A)
    (hAB : HasNUnitDistancePointsOn 3 A B) : 7 ≤ A.card := by
  obtain ⟨a, ha⟩ := hne
  have h₁ := twice_degree_add_one_le_side_card h hAB ha
  have h₂ : 3 ≤ (B.filter fun b ↦ dist a b = 1).card := hBA a ha
  omega

private lemma degree_eq_three_of_side_card_le_eight {A B : Finset ℝ²}
    (h : Disjoint (convexHull ℝ (A : Set ℝ²)) (convexHull ℝ (B : Set ℝ²)))
    (hBA : HasNUnitDistancePointsOn 3 B A) (hAB : HasNUnitDistancePointsOn 3 A B)
    (hcard : A.card ≤ 8) {a : ℝ²} (ha : a ∈ A) :
    (B.filter fun b ↦ dist a b = 1).card = 3 := by
  have hupper := twice_degree_add_one_le_side_card h hAB ha
  have hlower : 3 ≤ (B.filter fun b ↦ dist a b = 1).card := hBA a ha
  omega

private lemma pair_has_common_unit_neighbor_of_card_seven {A B : Finset ℝ²}
    (hhulls : Disjoint (convexHull ℝ (A : Set ℝ²)) (convexHull ℝ (B : Set ℝ²)))
    (hcard : A.card = 7)
    (hBA : HasNUnitDistancePointsOn 3 B A) (hAB : HasNUnitDistancePointsOn 3 A B)
    {a a' : ℝ²} (ha : a ∈ A) (ha' : a' ∈ A) (hne : a ≠ a') :
    ∃ b ∈ B, dist a b = 1 ∧ dist a' b = 1 := by
  classical
  by_contra! hno
  let T := B.filter fun b ↦ dist a b = 1
  have hT : T ⊆ B := Finset.filter_subset _ _
  have hhulls' :
      Disjoint (convexHull ℝ (↑(A.erase a') : Set ℝ²)) (convexHull ℝ (T : Set ℝ²)) :=
    hhulls.mono (convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _)))
      (convexHull_mono (Finset.coe_subset.mpr hT))
  have hAB' : HasNUnitDistancePointsOn 3 (A.erase a') T := by
    intro b hb
    obtain ⟨hbB, hab⟩ := Finset.mem_filter.mp (show b ∈ T from hb)
    have hnot : dist b a' ≠ 1 := by
      rw [dist_comm]
      exact hno b hbB hab
    have heq : (A.erase a').filter (fun x ↦ dist b x = 1) =
        A.filter (fun x ↦ dist b x = 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · exact fun ⟨⟨_, hx⟩, hd⟩ ↦ ⟨hx, hd⟩
      · intro ⟨hx, hd⟩
        exact ⟨⟨fun he ↦ hnot (he ▸ hd), hx⟩, hd⟩
    change 3 ≤ ((A.erase a').filter fun x ↦ dist b x = 1).card
    rw [heq]
    exact hAB b hbB
  have hbound := twice_degree_add_one_le_side_card hhulls' hAB'
    (Finset.mem_erase.mpr ⟨hne, ha⟩)
  have hdeg : 3 ≤ T.card := hBA a ha
  have hidem : T.filter (fun b ↦ dist a b = 1) = T :=
    Finset.filter_eq_self.mpr fun b hb ↦ (Finset.mem_filter.mp (show b ∈ T from hb)).2
  rw [hidem, Finset.card_erase_of_mem ha', hcard] at hbound
  omega

private lemma pair_has_unique_unit_neighbor_of_card_seven {A B : Finset ℝ²}
    (hhulls : Disjoint (convexHull ℝ (A : Set ℝ²)) (convexHull ℝ (B : Set ℝ²)))
    (hcard : A.card = 7)
    (hBA : HasNUnitDistancePointsOn 3 B A) (hAB : HasNUnitDistancePointsOn 3 A B)
    {a a' : ℝ²} (ha : a ∈ A) (ha' : a' ∈ A) (hne : a ≠ a') :
    ∃! b, b ∈ B ∧ dist a b = 1 ∧ dist a' b = 1 := by
  obtain ⟨b, hb, hab, ha'b⟩ :=
    pair_has_common_unit_neighbor_of_card_seven hhulls hcard hBA hAB ha ha' hne
  refine ⟨b, ⟨hb, hab, ha'b⟩, ?_⟩
  rintro b' ⟨hb', hab', ha'b'⟩
  by_contra hbb'
  exact no_cross_unit_four_cycle hhulls ha ha' hb hb' hne (fun he ↦ hbb' he.symm)
    hab hab' ha'b ha'b'

private lemma sum_cross_unit_degrees_swap (A B : Finset ℝ²) :
    (∑ a ∈ A, (B.filter fun b ↦ dist a b = 1).card) =
      ∑ b ∈ B, (A.filter fun a ↦ dist b a = 1).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun a _ ↦ by rw [dist_comm a b]

private lemma other_side_card_le_of_side_card_le_eight {A B : Finset ℝ²}
    (hhulls : Disjoint (convexHull ℝ (A : Set ℝ²)) (convexHull ℝ (B : Set ℝ²)))
    (hAB : HasNUnitDistancePointsOn 3 A B) (hA : A.card ≤ 8) : B.card ≤ A.card := by
  classical
  have hUpper : ∀ a ∈ A, (B.filter fun b ↦ dist a b = 1).card ≤ 3 := by
    intro a ha
    have := twice_degree_add_one_le_side_card hhulls hAB ha
    omega
  have hLower : ∀ b ∈ B, 3 ≤ (A.filter fun a ↦ dist b a = 1).card := hAB
  have hu := Finset.sum_le_sum hUpper
  have hl := Finset.sum_le_sum hLower
  rw [sum_cross_unit_degrees_swap A B] at hu
  have haSum : ∑ _ ∈ A, 3 = A.card * 3 := Finset.sum_const_nat fun _ _ ↦ rfl
  have hbSum : ∑ _ ∈ B, 3 = B.card * 3 := Finset.sum_const_nat fun _ _ ↦ rfl
  rw [haSum] at hu
  rw [hbSum] at hl
  omega

private lemma fourteen_le_cut_card {V A B : Finset ℝ²}
    (hA : A.Nonempty) (hB : B.Nonempty) (hcut : IsCut V A B)
    (hBA : HasNUnitDistancePointsOn 3 B A) (hAB : HasNUnitDistancePointsOn 3 A B) :
    14 ≤ V.card := by
  obtain ⟨rfl, hdisj, hhulls⟩ := hcut
  have ha := seven_le_side_card hhulls hA hBA hAB
  have hb := seven_le_side_card hhulls.symm hB hAB hBA
  rw [Finset.card_union_of_disjoint hdisj]
  omega

private lemma small_cut_card_pairs {V A B : Finset ℝ²}
    (hA : A.Nonempty) (hcut : IsCut V A B)
    (hBA : HasNUnitDistancePointsOn 3 B A) (hAB : HasNUnitDistancePointsOn 3 A B)
    (horder : A.card ≤ B.card) (hsmall : V.card < 20) :
    (A.card, B.card) ∈ ({(7, 7), (8, 8), (9, 9), (9, 10)} : Set (ℕ × ℕ)) := by
  obtain ⟨rfl, hdisj, hhulls⟩ := hcut
  have ha := seven_le_side_card hhulls hA hBA hAB
  rw [Finset.card_union_of_disjoint hdisj] at hsmall
  have hbalance : A.card ≤ 8 → B.card ≤ A.card :=
    other_side_card_le_of_side_card_le_eight hhulls hAB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  by_cases h : A.card ≤ 8
  · have := hbalance h
    omega
  · omega

private lemma convexIndep_of_support {V : Set ℝ²}
    (h : ∀ x ∈ V, ∃ f : ℝ² →ₗ[ℝ] ℝ, ∀ y ∈ V, y ≠ x → f y < f x) :
    ConvexIndep V := by
  intro x hx hHull
  obtain ⟨f, hf⟩ := h x hx
  have hsub : V \ {x} ⊆ {y | f y < f x} := by
    intro y hy
    exact hf y hy.1 (by simpa using hy.2)
  have hlt := convexHull_min hsub (convex_halfSpace_lt f.isLinear (f x)) hHull
  exact (lt_irrefl (f x)) hlt

private lemma isCut_union_of_separator {A B : Finset ℝ²}
    {f : ℝ² →ₗ[ℝ] ℝ} {r : ℝ}
    (hA : ∀ a ∈ A, f a < r) (hB : ∀ b ∈ B, r < f b) :
    IsCut (A ∪ B) A B := by
  refine ⟨rfl, Finset.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · intro p hpA hpB
    exact (lt_asymm (hA p hpA)) (hB p hpB)
  · intro p hpA hpB
    have hl : f p < r := convexHull_min (fun p hp ↦ hA p hp)
      (convex_halfSpace_lt f.isLinear r) hpA
    have hr : r < f p := convexHull_min (fun p hp ↦ hB p hp)
      (convex_halfSpace_gt f.isLinear r) hpB
    exact (lt_asymm hl) hr

private lemma strict_distance_monge_of_crossing {a a' b b' p : ℝ²}
    (hab' : Wbtw ℝ a p b') (ha'b : Wbtw ℝ a' p b) (hab : ¬ Wbtw ℝ a p b) :
    dist a b + dist a' b' < dist a b' + dist a' b := by
  have h₁ := lt_of_le_of_ne (dist_triangle a p b)
    (Ne.symm fun h ↦ hab (dist_add_dist_eq_iff.mp h))
  have h₂ := dist_triangle a' p b'
  have h₃ := dist_add_dist_eq_iff.mpr hab'
  have h₄ := dist_add_dist_eq_iff.mpr ha'b
  linarith

private lemma not_collinear_of_convexIndep {V : Set ℝ²} (hV : ConvexIndep V)
    {a b c : ℝ²} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ¬ Collinear ℝ ({a, b, c} : Set ℝ²) := by
  have no_between {x y z : ℝ²} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V)
      (hxy : x ≠ y) (hzy : z ≠ y) (h : Wbtw ℝ x y z) : False := by
    apply hV y hy
    have hsub : ({x, z} : Set ℝ²) ⊆ V \ {y} := by
      intro p hp
      rcases Set.mem_insert_iff.mp hp with rfl | hp
      · exact ⟨hx, hxy⟩
      · obtain rfl := Set.mem_singleton_iff.mp hp
        exact ⟨hz, hzy⟩
    apply convexHull_mono hsub
    rw [convexHull_pair]
    exact mem_segment_iff_wbtw.mpr h
  intro h
  rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact no_between ha hb hc hab hbc.symm h
  · exact no_between hb hc ha hbc hca.symm h
  · exact no_between hc ha hb hca hab.symm h

private lemma sbtw_of_line_mem_hull_without_endpoints {V T : Set ℝ²}
    (hV : ConvexIndep V) (hT : T ⊆ V) {a b p : ℝ²}
    (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (haT : a ∉ T) (hbT : b ∉ T)
    (hp : p ∈ line[ℝ, a, b]) (hpT : p ∈ convexHull ℝ T) : Sbtw ℝ a p b := by
  have inHull {u : ℝ²} (huT : u ∉ T) : p ∈ convexHull ℝ (V \ {u}) := by
    apply convexHull_mono ?_ hpT
    intro x hx
    exact ⟨hT hx, fun he ↦ huT ((show x = u from he) ▸ hx)⟩
  have outside {u v : ℝ²} (hu : u ∈ V) (hv : v ∈ V) (huT : u ∉ T)
      (hvu : v ≠ u) (h : Wbtw ℝ v u p) : False := by
    have hv' : v ∈ V \ {u} := ⟨hv, hvu⟩
    exact hV u hu ((convex_convexHull ℝ (V \ {u})).segment_subset
      (subset_convexHull ℝ _ hv') (inHull huT) (mem_segment_iff_wbtw.mpr h))
  have hc : Collinear ℝ ({p, a, b} : Set ℝ²) := collinear_insert_of_mem_affineSpan_pair hp
  have hw : Wbtw ℝ a p b := by
    rcases hc.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact (outside ha hb haT hab.symm h.symm).elim
    · exact (outside hb ha hbT hab h).elim
    · exact h.symm
  refine ⟨hw, ?_, ?_⟩
  · intro he
    subst p
    exact hV a ha (inHull haT)
  · intro he
    subst p
    exact hV b hb (inHull hbT)

private lemma cut_line_disjoint_opposite_hull {V A B : Finset ℝ²}
    (hV : ConvexIndep V) (hcut : IsCut V A B)
    {a a' : ℝ²} (ha : a ∈ A) (ha' : a' ∈ A) (hne : a ≠ a') :
    Disjoint (line[ℝ, a, a'] : Set ℝ²) (convexHull ℝ (B : Set ℝ²)) := by
  obtain ⟨rfl, hAB, hHulls⟩ := hcut
  apply Set.disjoint_left.mpr
  intro x hxLine hxB
  have hmem {u : ℝ²} (hu : u ∈ A) : u ∉ (B : Set ℝ²) :=
    fun hb ↦ Finset.disjoint_left.mp hAB hu hb
  have hp := sbtw_of_line_mem_hull_without_endpoints hV
    (fun b hb ↦ Finset.mem_union_right A hb)
    (Finset.mem_union_left B ha) (Finset.mem_union_left B ha') hne
    (hmem ha) (hmem ha') hxLine hxB
  have hxA := (convex_convexHull ℝ (A : Set ℝ²)).segment_subset
    (subset_convexHull ℝ _ ha) (subset_convexHull ℝ _ ha') (mem_segment_iff_wbtw.mpr hp.wbtw)
  exact Set.disjoint_left.mp hHulls hxA hxB

private lemma strict_distance_monge_of_convex_crossing {V : Set ℝ²}
    (hV : ConvexIndep V) {a a' b b' p : ℝ²}
    (ha : a ∈ V) (hb : b ∈ V) (hb' : b' ∈ V) (hab : a ≠ b) (hbb' : b ≠ b')
    (hcross : Sbtw ℝ a p b') (hcross' : Wbtw ℝ a' p b) :
    dist a b + dist a' b' < dist a b' + dist a' b := by
  apply strict_distance_monge_of_crossing hcross.wbtw hcross'
  intro h
  have hle : line[ℝ, a, p] ≤ line[ℝ, a, b'] :=
    affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair _ _ _) hcross.wbtw.mem_affineSpan
  have hbLine : b ∈ line[ℝ, a, b'] :=
    hle (h.right_mem_affineSpan_of_left_ne hcross.left_ne)
  exact not_collinear_of_convexIndep hV hb ha hb' hab.symm hcross.left_ne_right hbb'.symm
    (collinear_insert_of_mem_affineSpan_pair hbLine)

private lemma no_ordered_unit_six_cycle {m n : ℕ} {D : Fin m → Fin n → ℝ}
    (hm : ∀ ⦃i i' j j'⦄, i < i' → j < j' → D i j + D i' j' < D i j' + D i' j)
    {i i₁ i₂ : Fin m} {j₁ j j₂ : Fin n}
    (hi₁ : i < i₁) (hi₂ : i < i₂) (hj₁ : j₁ < j) (hj₂ : j < j₂)
    (h₁ : D i j₁ = 1) (h₂ : D i₁ j₁ = 1) (h₃ : D i₁ j = 1)
    (h₄ : D i j₂ = 1) (h₅ : D i₂ j₂ = 1) (h₆ : D i₂ j = 1) : False := by
  have hleft := hm hi₁ hj₁
  have hright := hm hi₂ hj₂
  linarith

private lemma unit_path_missing_entry_lt_one_iff {m n : ℕ} {D : Fin m → Fin n → ℝ}
    (hm : ∀ ⦃i i' j j'⦄, i < i' → j < j' → D i j + D i' j' < D i j' + D i' j)
    {i i' : Fin m} {j j' : Fin n} (hi : i ≠ i') (hj : j ≠ j')
    (h₁ : D i j' = 1) (h₂ : D i' j' = 1) (h₃ : D i' j = 1) :
    D i j < 1 ↔ (i < i' ∧ j < j') ∨ (i' < i ∧ j' < j) := by
  rcases lt_or_gt_of_ne hi with hil | hir <;> rcases lt_or_gt_of_ne hj with hjl | hjr
  · have h : D i j < 1 := by linarith [hm hil hjl]
    simp [h, hil, hjl]
  · have h : ¬ D i j < 1 := by linarith [hm hil hjr]
    simp [h, hjr.not_gt, hil.not_gt]
  · have h : ¬ D i j < 1 := by linarith [hm hir hjl]
    simp [h, hir.not_gt, hjl.not_gt]
  · have h : D i j < 1 := by linarith [hm hir hjr]
    simp [h, hir, hjr]

private lemma extreme_row_units_between {m n : ℕ} {D : Fin m → Fin n → ℝ}
    (hm : ∀ ⦃i i' j j'⦄, i < i' → j < j' → D i j + D i' j' < D i j' + D i' j)
    (common : ∀ ⦃j j'⦄, j ≠ j' → ∃ i, D i j = 1 ∧ D i j' = 1)
    {i : Fin m} (hextreme : (∀ i', i ≤ i') ∨ ∀ i', i' ≤ i)
    {j₁ j j₂ : Fin n} (hj₁ : j₁ < j) (hj₂ : j < j₂)
    (h₁ : D i j₁ = 1) (h₂ : D i j₂ = 1) : D i j = 1 := by
  by_contra h
  obtain ⟨i₁, ha₁, hb₁⟩ := common hj₁.ne
  obtain ⟨i₂, hb₂, ha₂⟩ := common hj₂.ne
  have hi₁ : i₁ ≠ i := fun he ↦ h (he ▸ hb₁)
  have hi₂ : i₂ ≠ i := fun he ↦ h (he ▸ hb₂)
  rcases hextreme with hmin | hmax
  · exact no_ordered_unit_six_cycle hm
      (lt_of_le_of_ne (hmin i₁) hi₁.symm) (lt_of_le_of_ne (hmin i₂) hi₂.symm)
      hj₁ hj₂ h₁ ha₁ hb₁ h₂ ha₂ hb₂
  · have hleft := hm (lt_of_le_of_ne (hmax i₁) hi₁) hj₁
    have hright := hm (lt_of_le_of_ne (hmax i₂) hi₂) hj₂
    linarith

private lemma extreme_row_units_consecutive {m n : ℕ} {D : Fin m → Fin n → ℝ}
    (hm : ∀ ⦃i i' j j'⦄, i < i' → j < j' → D i j + D i' j' < D i j' + D i' j)
    (common : ∀ ⦃j j'⦄, j ≠ j' → ∃ i, D i j = 1 ∧ D i j' = 1)
    {i : Fin m} (hextreme : (∀ i', i ≤ i') ∨ ∀ i', i' ≤ i)
    (hdeg : (Finset.univ.filter fun j ↦ D i j = 1).card = 3) :
    ∃ k : ℕ, ∀ j : Fin n, D i j = 1 ↔ k ≤ j.val ∧ j.val ≤ k + 2 := by
  classical
  let S := Finset.univ.filter fun j ↦ D i j = 1
  have hc : S.card = 3 := hdeg
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  let lo := S.min' hne
  let hi := S.max' hne
  have hlo : lo ∈ S := S.min'_mem hne
  have hhi : hi ∈ S := S.max'_mem hne
  have hmem {j : Fin n} : j ∈ S ↔ D i j = 1 := by simp [S]
  have hS : S = Finset.Icc lo hi := by
    ext j
    rw [Finset.mem_Icc]
    refine ⟨fun hj ↦ ⟨S.min'_le _ hj, S.le_max' _ hj⟩, ?_⟩
    rintro ⟨hl, hr⟩
    rcases hl.eq_or_lt with rfl | hl
    · exact hlo
    rcases hr.eq_or_lt with rfl | hr
    · exact hhi
    exact hmem.mpr (extreme_row_units_between hm common hextreme hl hr
      (hmem.mp hlo) (hmem.mp hhi))
  rw [hS, Fin.card_Icc] at hc
  have hval : hi.val = lo.val + 2 := by omega
  refine ⟨lo.val, fun j ↦ ?_⟩
  rw [← hmem, hS, Finset.mem_Icc]
  change (lo.val ≤ j.val ∧ j.val ≤ hi.val) ↔ _
  rw [hval]

private def turn (a b c : ℝ²) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

private lemma turn_rotate (a b c : ℝ²) : turn b c a = turn a b c := by
  unfold turn
  ring

private lemma turn_swap (a b c : ℝ²) : turn a c b = -turn a b c := by
  unfold turn
  ring

private lemma turn_lineMap (a b c d : ℝ²) (t : ℝ) :
    turn a b (AffineMap.lineMap c d t) = (1 - t) * turn a b c + t * turn a b d := by
  simp only [turn, AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private lemma turn_zero_iff_mem_line {a b c : ℝ²} (hab : a ≠ b) :
    turn a b c = 0 ↔ c ∈ line[ℝ, a, b] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · intro h
    unfold turn at h
    by_cases hz : b 0 - a 0 = 0
    · have hz' : b 0 = a 0 := sub_eq_zero.mp hz
      have h₁ : b 1 - a 1 ≠ 0 := by
        intro hzero
        apply hab
        ext i
        fin_cases i
        · exact hz'.symm
        · exact (sub_eq_zero.mp hzero).symm
      have hprod : (b 1 - a 1) * (c 0 - a 0) = 0 := by
        rw [hz, zero_mul, zero_sub, neg_eq_zero] at h
        exact h
      have hc₀ : c 0 = a 0 := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left h₁)
      refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
      ext i
      fin_cases i
      · change (c 1 - a 1) / (b 1 - a 1) * (b 0 - a 0) + a 0 = c 0
        simpa only [hz, mul_zero, zero_add] using hc₀.symm
      · change (c 1 - a 1) / (b 1 - a 1) * (b 1 - a 1) + a 1 = c 1
        field_simp
        ring
    · refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
      ext i
      fin_cases i
      · change (c 0 - a 0) / (b 0 - a 0) * (b 0 - a 0) + a 0 = c 0
        field_simp
        ring
      · change (c 0 - a 0) / (b 0 - a 0) * (b 1 - a 1) + a 1 = c 1
        field_simp
        linear_combination -h
  · rintro ⟨t, rfl⟩
    rw [turn_lineMap]
    unfold turn
    ring

private lemma segment_crosses_line_of_turn_mul_neg {a b c d : ℝ²}
    (hab : a ≠ b) (hcd : c ≠ d) (h : turn a b c * turn a b d < 0) :
    ∃ p ∈ line[ℝ, a, b], Sbtw ℝ c p d := by
  let t := turn a b c / (turn a b c - turn a b d)
  have hsign := mul_neg_iff.mp h
  have ht : 0 < t ∧ t < 1 := by
    unfold t
    rcases hsign with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hpos : 0 < turn a b c - turn a b d := by linarith
      exact ⟨div_pos h₁ hpos, (div_lt_one hpos).mpr (by linarith)⟩
    · have hneg : turn a b c - turn a b d < 0 := by linarith
      exact ⟨div_pos_of_neg_of_neg h₁ hneg, (div_lt_one_of_neg hneg).mpr (by linarith)⟩
  have hne : turn a b c - turn a b d ≠ 0 := by
    rcases hsign with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith
  refine ⟨AffineMap.lineMap c d t, (turn_zero_iff_mem_line hab).mp ?_, ?_⟩
  · rw [turn_lineMap]
    dsimp [t]
    field_simp
    ring
  · exact sbtw_iff_mem_image_Ioo_and_ne.mpr ⟨⟨t, ht, rfl⟩, hcd⟩

private lemma cut_turn_mul_pos {V A B : Finset ℝ²}
    (hV : ConvexIndep V) (hcut : IsCut V A B)
    {a a' b b' : ℝ²} (ha : a ∈ A) (ha' : a' ∈ A) (haa' : a ≠ a')
    (hb : b ∈ B) (hb' : b' ∈ B) :
    0 < turn a a' b * turn a a' b' := by
  have hd := Set.disjoint_left.mp (cut_line_disjoint_opposite_hull hV hcut ha ha' haa')
  have hne {c : ℝ²} (hc : c ∈ B) : turn a a' c ≠ 0 :=
    fun h ↦ hd ((turn_zero_iff_mem_line haa').mp h) (subset_convexHull ℝ _ hc)
  refine lt_of_le_of_ne (le_of_not_gt ?_) (mul_ne_zero (hne hb) (hne hb')).symm
  intro hneg
  have hbb' : b ≠ b' := by
    intro he
    rw [he] at hneg
    exact (mul_self_nonneg _).not_gt hneg
  obtain ⟨p, hp, hs⟩ := segment_crosses_line_of_turn_mul_neg haa' hbb' hneg
  exact hd hp ((convex_convexHull ℝ (B : Set ℝ²)).segment_subset
    (subset_convexHull ℝ _ hb) (subset_convexHull ℝ _ hb')
    (mem_segment_iff_wbtw.mpr hs.wbtw))

private lemma strict_distance_monge_of_opposite_turns {V A B : Finset ℝ²}
    (hV : ConvexIndep V) (hcut : IsCut V A B) {a a' b b' : ℝ²}
    (ha : a ∈ A) (ha' : a' ∈ A) (haa' : a ≠ a')
    (hb : b ∈ B) (hb' : b' ∈ B) (hbb' : b ≠ b')
    (h : turn a a' b' * turn b b' a < 0) :
    dist a b + dist a' b' < dist a b' + dist a' b := by
  have left_mem {x : ℝ²} (hx : x ∈ A) : x ∈ (V : Set ℝ²) := by
    rw [← hcut.1]
    exact Finset.mem_union_left B hx
  have right_mem {x : ℝ²} (hx : x ∈ B) : x ∈ (V : Set ℝ²) := by
    rw [← hcut.1]
    exact Finset.mem_union_right A hx
  have cross_ne {x y : ℝ²} (hx : x ∈ A) (hy : y ∈ B) : x ≠ y := by
    rintro rfl
    exact Finset.disjoint_left.mp hcut.2.1 hx hy
  have hsign₂ : turn a b' b = -turn b b' a := by
    rw [turn_swap, turn_rotate a b b']
  have hs : turn a b' a' * turn a b' b < 0 := by
    rw [turn_swap a a' b', hsign₂, neg_mul_neg]
    exact h
  obtain ⟨p, hpLine, hp⟩ := segment_crosses_line_of_turn_mul_neg
    (cross_ne ha hb') (cross_ne ha' hb) hs
  have hT : ({a', b} : Set ℝ²) ⊆ (V : Set ℝ²) := by
    exact Set.insert_subset_iff.mpr ⟨left_mem ha', Set.singleton_subset_iff.mpr (right_mem hb)⟩
  have haT : a ∉ ({a', b} : Set ℝ²) := by simp [haa', cross_ne ha hb]
  have hb'T : b' ∉ ({a', b} : Set ℝ²) := by simp [(cross_ne ha' hb').symm, hbb'.symm]
  have hpT : p ∈ convexHull ℝ ({a', b} : Set ℝ²) := by
    rw [convexHull_pair]
    exact mem_segment_iff_wbtw.mpr hp.wbtw
  have hp' := sbtw_of_line_mem_hull_without_endpoints hV hT
    (left_mem ha) (right_mem hb') (cross_ne ha hb') haT hb'T hpLine hpT
  exact strict_distance_monge_of_convex_crossing hV (left_mem ha) (right_mem hb)
    (right_mem hb') (cross_ne ha hb) hbb' hp' hp.wbtw

private lemma neg_mul_iff_of_mul_pos {x x' y : ℝ} (h : 0 < x * x') :
    x * y < 0 ↔ x' * y < 0 := by
  rcases mul_pos_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp [mul_neg_iff, h₁, h₂, h₁.not_gt, h₂.not_gt]
  · simp [mul_neg_iff, h₁, h₂, h₁.not_gt, h₂.not_gt]

private lemma isCut_swap {V A B : Finset ℝ²} (h : IsCut V A B) : IsCut V B A :=
  ⟨(Finset.union_comm B A).trans h.1, h.2.1.symm, h.2.2.symm⟩

private lemma distance_monge_iff_turn_mul_neg {V A B : Finset ℝ²}
    (hV : ConvexIndep V) (hcut : IsCut V A B) {a a' b b' : ℝ²}
    (ha : a ∈ A) (ha' : a' ∈ A) (haa' : a ≠ a')
    (hb : b ∈ B) (hb' : b' ∈ B) (hbb' : b ≠ b') :
    dist a b + dist a' b' < dist a b' + dist a' b ↔
      turn a a' b * turn b b' a < 0 := by
  have hprod := cut_turn_mul_pos hV hcut ha ha' haa' hb hb'
  have hprod' := cut_turn_mul_pos hV (isCut_swap hcut) hb hb' hbb' ha ha'
  have negative : turn a a' b * turn b b' a < 0 →
      dist a b + dist a' b' < dist a b' + dist a' b :=
    fun h ↦ strict_distance_monge_of_opposite_turns hV hcut ha ha' haa' hb hb' hbb'
      ((neg_mul_iff_of_mul_pos hprod).mp h)
  refine ⟨fun h ↦ ?_, negative⟩
  by_contra! hn
  have hne : turn a a' b * turn b b' a ≠ 0 := by
    intro he
    rcases mul_eq_zero.mp he with he | he
    · simp [he] at hprod
    · simp [he] at hprod'
  have hpos := lt_of_le_of_ne hn hne.symm
  have hrev : turn b' b a = -turn b b' a := by
    unfold turn
    ring
  have hneg : turn a a' b * turn b' b a < 0 := by
    rw [hrev, mul_neg]
    exact neg_neg_of_pos hpos
  exact lt_asymm h
    (strict_distance_monge_of_opposite_turns hV hcut ha ha' haa' hb' hb hbb'.symm hneg)

private lemma cross_distance_four_sum_ne {V A B : Finset ℝ²}
    (hV : ConvexIndep V) (hcut : IsCut V A B) {a a' b b' : ℝ²}
    (ha : a ∈ A) (ha' : a' ∈ A) (haa' : a ≠ a')
    (hb : b ∈ B) (hb' : b' ∈ B) (hbb' : b ≠ b') :
    dist a b + dist a' b' ≠ dist a b' + dist a' b := by
  have hturnA : turn a a' b ≠ 0 := by
    intro h
    simpa [h] using cut_turn_mul_pos hV hcut ha ha' haa' hb hb'
  have hturnB : turn b b' a ≠ 0 := by
    intro h
    simpa [h] using cut_turn_mul_pos hV (isCut_swap hcut) hb hb' hbb' ha ha'
  rcases lt_or_gt_of_ne (mul_ne_zero hturnA hturnB) with hneg | hpos
  · exact (distance_monge_iff_turn_mul_neg hV hcut ha ha' haa' hb hb' hbb').mpr hneg |>.ne
  · have hreversal : turn b' b a = -turn b b' a := by unfold turn; ring
    have hneg : turn a a' b * turn b' b a < 0 := by
      rw [hreversal, mul_neg]
      exact neg_neg_of_pos hpos
    exact (strict_distance_monge_of_opposite_turns hV hcut ha ha' haa' hb' hb hbb'.symm hneg).ne.symm

private lemma exists_strict_distance_monge_order {V A B : Finset ℝ²}
    (hV : ConvexIndep V) (hcut : IsCut V A B) (hAsize : 1 < A.card) (hBsize : 1 < B.card) :
    ∃ (a : Fin A.card ≃ A) (b : Fin B.card ≃ B), ∀ ⦃i i' j j'⦄, i < i' → j < j' →
      dist (a i : ℝ²) (b j) + dist (a i' : ℝ²) (b j') <
        dist (a i : ℝ²) (b j') + dist (a i' : ℝ²) (b j) := by
  classical
  obtain ⟨a₀, ha₀, a₁, ha₁, haa⟩ := Finset.one_lt_card.mp hAsize
  obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.mp hBsize
  have hne := cross_distance_four_sum_ne hV hcut ha₀ ha₁ haa hb hb' hbb
  obtain ⟨b₀, b₁, hb₀, hb₁, hb₀₁, hbase⟩ :
      ∃ b₀ b₁, b₀ ∈ B ∧ b₁ ∈ B ∧ b₀ ≠ b₁ ∧
        dist a₀ b₀ + dist a₁ b₁ < dist a₀ b₁ + dist a₁ b₀ := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨b, b', hb, hb', hbb, hlt⟩
    · exact ⟨b', b, hb', hb, hbb.symm, hgt⟩
  let sA (a : A) := dist (a : ℝ²) b₀ - dist (a : ℝ²) b₁
  let sB (b : B) := dist a₀ (b : ℝ²) - dist a₁ (b : ℝ²)
  have sAinj : Function.Injective sA := by
    intro a a' he
    apply Subtype.ext
    by_contra hne
    apply cross_distance_four_sum_ne hV hcut a.property a'.property hne hb₀ hb₁ hb₀₁
    dsimp only [sA] at he
    linarith
  have sBinj : Function.Injective sB := by
    intro b b' he
    apply Subtype.ext
    by_contra hne
    apply cross_distance_four_sum_ne hV hcut ha₀ ha₁ haa b.property b'.property hne
    dsimp only [sB] at he
    linarith
  let : LinearOrder A := LinearOrder.lift' sA sAinj
  let : LinearOrder B := LinearOrder.lift' sB sBinj
  let eA := Fintype.orderIsoFinOfCardEq A (Fintype.card_coe A)
  let eB := Fintype.orderIsoFinOfCardEq B (Fintype.card_coe B)
  refine ⟨eA.toEquiv, eB.toEquiv, ?_⟩
  intro i i' j j' hi hj
  let a := eA i
  let a' := eA i'
  let b := eB j
  let b' := eB j'
  have ha : (a : ℝ²) ≠ a' := fun he ↦ hi.ne (eA.injective (Subtype.ext he))
  have hb : (b : ℝ²) ≠ b' := fun he ↦ hj.ne (eB.injective (Subtype.ext he))
  have hi' : sA a < sA a' := eA.strictMono hi
  have hj' : sB b < sB b' := eB.strictMono hj
  have hfirst : turn a a' b₀ * turn b₀ b₁ a < 0 := by
    apply (distance_monge_iff_turn_mul_neg hV hcut a.property a'.property ha hb₀ hb₁ hb₀₁).mp
    dsimp only [sA] at hi'
    linarith
  have hfirst' : turn a a' b₀ * turn b₀ b₁ a₀ < 0 := by
    rw [mul_comm] at hfirst ⊢
    exact (neg_mul_iff_of_mul_pos
      (cut_turn_mul_pos hV (isCut_swap hcut) hb₀ hb₁ hb₀₁ a.property ha₀)).mp hfirst
  have hsecond : turn a₀ a₁ b * turn b b' a₀ < 0 := by
    apply (distance_monge_iff_turn_mul_neg hV hcut ha₀ ha₁ haa b.property b'.property hb).mp
    dsimp only [sB] at hj'
    linarith
  have hsecond' : turn a₀ a₁ b₀ * turn b b' a₀ < 0 :=
    (neg_mul_iff_of_mul_pos (cut_turn_mul_pos hV hcut ha₀ ha₁ haa b.property hb₀)).mp hsecond
  have hbase' := (distance_monge_iff_turn_mul_neg hV hcut ha₀ ha₁ haa hb₀ hb₁ hb₀₁).mp hbase
  have htarget : turn a a' b₀ * turn b b' a₀ < 0 := by
    by_contra! h
    have hpositive := mul_pos_of_neg_of_neg hfirst' hsecond'
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos h hbase'.le
    nlinarith only [hpositive, hnonpos]
  have htarget' : turn a a' b * turn b b' a₀ < 0 :=
    (neg_mul_iff_of_mul_pos (cut_turn_mul_pos hV hcut a.property a'.property ha hb₀ b.property)).mp htarget
  have htarget'' : turn a a' b * turn b b' a < 0 := by
    rw [mul_comm] at htarget' ⊢
    exact (neg_mul_iff_of_mul_pos
      (cut_turn_mul_pos hV (isCut_swap hcut) b.property b'.property hb ha₀ a.property)).mp htarget'
  exact (distance_monge_iff_turn_mul_neg hV hcut a.property a'.property ha b.property b'.property hb).mpr htarget''

private lemma card_filter_of_equiv_finset {α β : Type*} [Fintype α]
    {S : Finset β} (e : α ≃ S) (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i ↦ p (e i : β)).card = (S.filter p).card := by
  refine Finset.card_bij (fun i _ ↦ (e i : β)) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(e i).property, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ he
    exact e.injective (Subtype.ext he)
  · intro b hb
    obtain ⟨hbS, hbp⟩ := Finset.mem_filter.mp hb
    refine ⟨e.symm ⟨b, hbS⟩, ?_, ?_⟩
    · simp [hbp]
    · simp

private lemma exists_ordered_cut_distance_matrix {V A B : Finset ℝ²}
    (hV : ConvexIndep V) (hcut : IsCut V A B)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : HasNUnitDistancePointsOn 3 B A) (hAB : HasNUnitDistancePointsOn 3 A B) :
    ∃ D : Fin A.card → Fin B.card → ℝ,
      (∀ ⦃i i' j j'⦄, i < i' → j < j' → D i j + D i' j' < D i j' + D i' j) ∧
      (∀ i, 3 ≤ (Finset.univ.filter fun j ↦ D i j = 1).card) ∧
      (∀ j, 3 ≤ (Finset.univ.filter fun i ↦ D i j = 1).card) := by
  classical
  have ha := seven_le_side_card hcut.2.2 hA hBA hAB
  have hb := seven_le_side_card hcut.2.2.symm hB hAB hBA
  obtain ⟨a, b, hm⟩ := exists_strict_distance_monge_order hV hcut
    (by omega : 1 < A.card) (by omega : 1 < B.card)
  let D (i : Fin A.card) (j : Fin B.card) := dist (a i : ℝ²) (b j)
  refine ⟨D, hm, ?_, ?_⟩
  · intro i
    change 3 ≤ (Finset.univ.filter fun j ↦ dist (a i : ℝ²) (b j : ℝ²) = 1).card
    rw [card_filter_of_equiv_finset b (fun q ↦ dist (a i : ℝ²) q = 1)]
    exact hBA _ (a i).property
  · intro j
    change 3 ≤ (Finset.univ.filter fun i ↦ dist (a i : ℝ²) (b j : ℝ²) = 1).card
    simp_rw [dist_comm _ (b j : ℝ²)]
    rw [card_filter_of_equiv_finset a (fun q ↦ dist (b j : ℝ²) q = 1)]
    exact hAB _ (b j).property

theorem OMA.solution : type_of% @Erdos97.erdos_97.variants.three_unit_distance_cut_min := by
  classical
  let S : Set ℕ := {n | ∃ (V A B : Finset ℝ²),
    n = V.card ∧ ConvexIndep V ∧ A.Nonempty ∧ B.Nonempty ∧ IsCut V A B ∧
    HasNUnitDistancePointsOn 3 B A ∧ HasNUnitDistancePointsOn 3 A B}
  change sInf S = 20
  have hremaining : 20 ∈ S ∧
      ∀ (V A B : Finset ℝ²), ConvexIndep V → A.Nonempty → B.Nonempty → IsCut V A B →
      HasNUnitDistancePointsOn 3 B A → HasNUnitDistancePointsOn 3 A B →
      (A.card, B.card) ∉ ({(7, 7), (8, 8), (9, 9), (9, 10)} : Set (ℕ × ℕ)) := by
    sorry
  refine le_antisymm (csInf_le' hremaining.1) (le_csInf ⟨20, hremaining.1⟩ ?_)
  intro n hn
  obtain ⟨V, A, B, hcard, hconv, hA, hB, hcut, hBA, hAB⟩ := hn
  by_contra! hn
  have hsmall : V.card < 20 := hcard ▸ hn
  rcases le_total A.card B.card with h | h
  · exact hremaining.2 V A B hconv hA hB hcut hBA hAB
      (small_cut_card_pairs hA hcut hBA hAB h hsmall)
  · have hswap := isCut_swap hcut
    exact hremaining.2 V B A hconv hB hA hswap hAB hBA
      (small_cut_card_pairs hB hswap hAB hBA h hsmall)
