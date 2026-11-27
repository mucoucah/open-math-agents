import FormalConjectures.ErdosProblems.«604»

/-! Bounds from geometric covers for pinned distances in the plane. -/

-- Problem: Erdős Problem 604 — sqrt log
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/604.lean:92 (declaration Erdos604.erdos_604.variants.sqrt_log)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Finset
open scoped Asymptotics EuclideanGeometry RealInnerProductSpace

open Classical in
private theorem card_distance_image (A : Finset ℝ²) (x : ℝ²) :
    ((A.erase x).image fun z => dist z x).card = distinctDistancesFrom A x := by
  classical
  unfold distinctDistancesFrom
  congr 1
  ext r
  simp only [Finset.mem_image, Finset.mem_erase]

private theorem card_le_two_of_two_distances
    (B : Finset ℝ²) {x y : ℝ²} (hxy : x ≠ y) {r s : ℝ}
    (h : ∀ z ∈ B, dist z x = r ∧ dist z y = s) : B.card ≤ 2 := by
  classical
  by_cases hB : 1 < B.card
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hB
    have hsub : B ⊆ {a, b} := by
      intro z hz
      obtain ⟨har, has⟩ := h a ha
      obtain ⟨hbr, hbs⟩ := h b hb
      obtain ⟨hzr, hzs⟩ := h z hz
      simpa using EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
        (V := ℝ²) (by simp) hxy hab har hbr hzr has hbs hzs
    calc
      B.card ≤ ({a, b} : Finset ℝ²).card := Finset.card_le_card hsub
      _ = 2 := by simp [hab]
  · omega

open Classical in
private noncomputable def circlesAtDistance (x : ℝ²) (C : Finset (ℝ² × ℝ)) (r : ℝ) :
    Finset (ℝ² × ℝ) :=
  C.filter fun c => |dist c.1 x - c.2| ≤ r ∧ r ≤ dist c.1 x + c.2

open Classical in
private theorem mem_circlesAtDistance {x z : ℝ²} {C : Finset (ℝ² × ℝ)} {c : ℝ² × ℝ}
    (hc : c ∈ C) (hz : dist z c.1 = c.2) :
    c ∈ circlesAtDistance x C (dist z x) := by
  have h1 : dist c.1 x ≤ c.2 + dist z x := by
    simpa only [dist_comm c.1 z, hz] using dist_triangle c.1 z x
  have h2 : c.2 ≤ dist z x + dist c.1 x := by
    simpa only [dist_comm x c.1, hz] using dist_triangle z x c.1
  have h3 : dist z x ≤ c.2 + dist c.1 x := by
    simpa only [hz] using dist_triangle z c.1 x
  refine Finset.mem_filter.mpr ⟨hc, abs_le.mpr ⟨?_, ?_⟩, ?_⟩ <;>
    linarith only [h1, h2, h3]

open Classical in
/-- Each distance fiber meets a covering circle in at most two points.
Only circles whose radial interval contains the pinned distance enter the bound. -/
private theorem card_le_of_circle_cover_overlap (A B : Finset ℝ²) (x : ℝ²)
    (C : Finset (ℝ² × ℝ)) (hB : B ⊆ A.erase x)
    (hcenter : ∀ c ∈ C, c.1 ≠ x)
    (hcover : ∀ z ∈ B, ∃ c ∈ C, dist z c.1 = c.2)
    (k : ℕ) (hk : ∀ r ∈ (A.erase x).image (fun z => dist z x),
      (circlesAtDistance x C r).card ≤ k) :
    B.card ≤ 2 * k * distinctDistancesFrom A x := by
  classical
  rw [← card_distance_image]
  apply Finset.card_le_mul_card_image_of_maps_to
    (f := fun z : ℝ² => dist z x) (t := (A.erase x).image (fun z => dist z x))
  · exact fun z hz => Finset.mem_image_of_mem _ (hB hz)
  · intro r hr
    let F := B.filter fun z => dist z x = r
    let T := circlesAtDistance x C r
    let S := fun c : ℝ² × ℝ => F.filter fun z => dist z c.1 = c.2
    have hsub : F ⊆ T.biUnion S := by
      intro z hz
      obtain ⟨hzB, hzr⟩ := Finset.mem_filter.mp hz
      obtain ⟨c, hc, hzc⟩ := hcover z hzB
      have hcT : c ∈ T := by
        simpa only [T, hzr] using (mem_circlesAtDistance (x := x) hc hzc)
      exact Finset.mem_biUnion.mpr ⟨c, hcT, Finset.mem_filter.mpr ⟨hz, hzc⟩⟩
    have hS : ∀ c ∈ T, (S c).card ≤ 2 := by
      intro c hc
      have hcC : c ∈ C := (Finset.mem_filter.mp hc).1
      apply card_le_two_of_two_distances (S c) (Ne.symm (hcenter c hcC))
      intro z hz
      obtain ⟨hzF, hzc⟩ := Finset.mem_filter.mp hz
      exact ⟨(Finset.mem_filter.mp hzF).2, hzc⟩
    calc
      F.card ≤ (T.biUnion S).card := Finset.card_le_card hsub
      _ ≤ T.card * 2 := Finset.card_biUnion_le_card_mul T S 2 hS
      _ ≤ k * 2 := Nat.mul_le_mul_right 2 (hk r hr)
      _ = 2 * k := Nat.mul_comm _ _

open Classical in
private theorem card_le_of_circle_cover (A B : Finset ℝ²) (x : ℝ²)
    (C : Finset (ℝ² × ℝ)) (hB : B ⊆ A.erase x)
    (hcenter : ∀ c ∈ C, c.1 ≠ x)
    (hcover : ∀ z ∈ B, ∃ c ∈ C, dist z c.1 = c.2) :
    B.card ≤ 2 * C.card * distinctDistancesFrom A x := by
  classical
  refine card_le_of_circle_cover_overlap A B x C hB hcenter hcover C.card ?_
  intro r _
  exact Finset.card_le_card (Finset.filter_subset _ _)

open Classical in
/-- Well-separated distance levels from one pin give distinct groups of
distances from a nearby pin. Each group has at most two points per distance. -/
private theorem card_le_of_separated_radii (A B : Finset ℝ²) {x y : ℝ²} (hxy : x ≠ y)
    (R : Finset ℝ) (hB : B ⊆ A.erase y) (hR : ∀ z ∈ B, dist z x ∈ R)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 2 * dist x y < |r - s|) :
    B.card ≤ 2 * distinctDistancesFrom A y := by
  classical
  let C := R.image fun r => (x, r)
  have hcenter : ∀ c ∈ C, c.1 ≠ y := by
    intro c hc
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hc
    exact hxy
  have hcover : ∀ z ∈ B, ∃ c ∈ C, dist z c.1 = c.2 := by
    intro z hz
    exact ⟨(x, dist z x), Finset.mem_image_of_mem _ (hR z hz), rfl⟩
  have hcard (d : ℝ) : (circlesAtDistance y C d).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haC, ha1, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbC, hb1, hb2⟩ := Finset.mem_filter.mp hb
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp haC
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hbC
    change |dist x y - r| ≤ d at ha1
    change |dist x y - s| ≤ d at hb1
    change d ≤ dist x y + r at ha2
    change d ≤ dist x y + s at hb2
    have har := (neg_le_abs (dist x y - r)).trans ha1
    have hbs := (neg_le_abs (dist x y - s)).trans hb1
    have hdiff : |r - s| ≤ 2 * dist x y := by
      apply abs_le.mpr
      constructor <;> linarith only [har, hbs, ha2, hb2]
    have hrs : r = s := by
      by_contra hn
      exact (not_lt_of_ge hdiff) (hsep r hr s hs hn)
    rw [hrs]
  simpa only [Nat.mul_one] using
    card_le_of_circle_cover_overlap A B y C hB hcenter hcover 1 (fun d _ => hcard d)

private theorem card_le_of_two_pins (A : Finset ℝ²) {x y : ℝ²} (hxy : x ≠ y) :
    A.card ≤ 2 * distinctDistancesFrom A y * distinctDistancesFrom A x + 2 := by
  classical
  let R := (A.erase y).image fun z => dist z y
  let C := R.image fun r => (y, r)
  let B := (A.erase x).erase y
  have hC : C.card ≤ distinctDistancesFrom A y := by
    rw [← card_distance_image]
    exact Finset.card_image_le
  have hbound := card_le_of_circle_cover A B x C (Finset.erase_subset _ _) (by
    intro c hc
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hc
    exact hxy.symm) (by
    intro z hz
    have hzA : z ∈ A.erase y := Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hz).1, Finset.erase_subset _ _ (Finset.mem_erase.mp hz).2⟩
    exact ⟨(y, dist z y), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hzA), rfl⟩)
  have hcard : A.card ≤ B.card + 2 := by
    have hx := Finset.pred_card_le_card_erase (s := A) (a := x)
    have hy := Finset.pred_card_le_card_erase (s := A.erase x) (a := y)
    change (A.erase x).card - 1 ≤ B.card at hy
    omega
  calc
    _ ≤ B.card + 2 := hcard
    _ ≤ 2 * C.card * distinctDistancesFrom A x + 2 := Nat.add_le_add_right hbound _
    _ ≤ _ := by gcongr

private def OnLine (ℓ : ℝ² × ℝ²) (z : ℝ²) : Prop :=
  ∃ t : ℝ, t • ℓ.2 + ℓ.1 = z

private theorem card_le_two_on_line_at_distance (B : Finset ℝ²) (x : ℝ²)
    (ℓ : ℝ² × ℝ²) (r : ℝ)
    (h : ∀ z ∈ B, OnLine ℓ z ∧ dist z x = r) : B.card ≤ 2 := by
  classical
  by_cases hv : ℓ.2 = 0
  · have hsub : B ⊆ {ℓ.1} := by
      intro z hz
      obtain ⟨t, ht⟩ := (h z hz).1
      simpa [hv, eq_comm] using ht
    exact (Finset.card_le_card hsub).trans (by simp)
  by_cases hB : B.Nonempty
  · obtain ⟨a, ha⟩ := hB
    obtain ⟨⟨t, ht⟩, har⟩ := h a ha
    let b : ℝ² := (-2 * ⟪ℓ.2, a -ᵥ x⟫ / ⟪ℓ.2, ℓ.2⟫) • ℓ.2 +ᵥ a
    have hsub : B ⊆ {a, b} := by
      intro z hz
      obtain ⟨⟨s, hs⟩, hzr⟩ := h z hz
      have hzparam : (s - t) • ℓ.2 +ᵥ a = z := by
        change (s - t) • ℓ.2 + a = z
        rw [← ht, ← hs, sub_smul]
        abel
      have hzdist : dist ((s - t) • ℓ.2 +ᵥ a) x = dist a x := by
        rw [hzparam, hzr, har]
      rcases (EuclideanGeometry.dist_smul_vadd_eq_dist a x hv (s - t)).mp hzdist with hz0 | hzb
      · rw [hz0, zero_smul, zero_vadd] at hzparam
        simp [← hzparam]
      · rw [hzb] at hzparam
        exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hzparam.symm)
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp hB]

open Classical in
private theorem card_le_of_line_cover (A B : Finset ℝ²) (x : ℝ²)
    (D : Finset (ℝ² × ℝ²)) (hB : B ⊆ A.erase x)
    (hcover : ∀ z ∈ B, ∃ ℓ ∈ D, OnLine ℓ z) :
    B.card ≤ 2 * D.card * distinctDistancesFrom A x := by
  classical
  rw [← card_distance_image]
  apply Finset.card_le_mul_card_image_of_maps_to
    (f := fun z : ℝ² => dist z x) (t := (A.erase x).image (fun z => dist z x))
  · exact fun z hz => Finset.mem_image_of_mem _ (hB hz)
  · intro r _
    let F := B.filter fun z => dist z x = r
    let S := fun ℓ : ℝ² × ℝ² => F.filter (OnLine ℓ)
    have hsub : F ⊆ D.biUnion S := by
      intro z hz
      obtain ⟨ℓ, hℓ, hzℓ⟩ := hcover z (Finset.mem_filter.mp hz).1
      exact Finset.mem_biUnion.mpr ⟨ℓ, hℓ, Finset.mem_filter.mpr ⟨hz, hzℓ⟩⟩
    have hS (ℓ : ℝ² × ℝ²) : (S ℓ).card ≤ 2 := by
      refine card_le_two_on_line_at_distance (S ℓ) x ℓ r ?_
      intro z hz
      obtain ⟨hzF, hzℓ⟩ := Finset.mem_filter.mp hz
      exact ⟨hzℓ, (Finset.mem_filter.mp hzF).2⟩
    calc
      F.card ≤ (D.biUnion S).card := Finset.card_le_card hsub
      _ ≤ D.card * 2 := Finset.card_biUnion_le_card_mul D S 2 (fun ℓ _ => hS ℓ)
      _ = 2 * D.card := Nat.mul_comm _ _

open Classical in
private theorem card_le_of_mixed_cover (A B : Finset ℝ²) (x : ℝ²)
    (C : Finset (ℝ² × ℝ)) (D : Finset (ℝ² × ℝ²)) (hB : B ⊆ A.erase x)
    (hcenter : ∀ c ∈ C, c.1 ≠ x)
    (hcover : ∀ z ∈ B, (∃ c ∈ C, dist z c.1 = c.2) ∨ (∃ ℓ ∈ D, OnLine ℓ z))
    (k : ℕ) (hk : ∀ r ∈ (A.erase x).image (fun z => dist z x),
      (circlesAtDistance x C r).card ≤ k) :
    B.card ≤ 2 * (k + D.card) * distinctDistancesFrom A x := by
  classical
  let p := fun z : ℝ² => ∃ c ∈ C, dist z c.1 = c.2
  let S := B.filter p
  let T := B.filter fun z => ¬ p z
  have hS := card_le_of_circle_cover_overlap A S x C
    ((Finset.filter_subset _ _).trans hB) hcenter
    (fun z hz => (Finset.mem_filter.mp hz).2) k hk
  have hT := card_le_of_line_cover A T x D ((Finset.filter_subset _ _).trans hB) (by
    intro z hz
    obtain ⟨hzB, hzp⟩ := Finset.mem_filter.mp hz
    exact (hcover z hzB).resolve_left hzp)
  calc
    B.card = S.card + T.card := (Finset.card_filter_add_card_filter_not p).symm
    _ ≤ 2 * k * distinctDistancesFrom A x + 2 * D.card * distinctDistancesFrom A x :=
      Nat.add_le_add hS hT
    _ = _ := by ring

open Classical in
private noncomputable def lightTargets (A : Finset ℝ²) (x : ℝ²) (L : ℝ) :
    Finset ℝ² :=
  (A.erase x).filter fun z =>
    (((A.erase x).filter fun w => dist w x = dist z x).card : ℝ) ≤ L

open Classical in
private theorem card_lightTargets_le (A : Finset ℝ²) (x : ℝ²) {L : ℝ} (hL : 0 ≤ L) :
    ((lightTargets A x L).card : ℝ) ≤ L * (distinctDistancesFrom A x : ℝ) := by
  classical
  let R := (A.erase x).image fun z => dist z x
  let S := lightTargets A x L
  have hmaps : ∀ z ∈ S, dist z x ∈ R :=
    fun z hz => Finset.mem_image_of_mem _ ((Finset.mem_filter.mp hz).1)
  have hfiber (r : ℝ) : (((S.filter fun z => dist z x = r).card : ℕ) : ℝ) ≤ L := by
    by_cases h : (S.filter fun z => dist z x = r).Nonempty
    · obtain ⟨z, hz⟩ := h
      obtain ⟨hzS, hzr⟩ := Finset.mem_filter.mp hz
      have hlight := (Finset.mem_filter.mp hzS).2
      rw [hzr] at hlight
      refine le_trans ?_ hlight
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
    · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty, Nat.cast_zero]
      exact hL
  calc
    (S.card : ℝ) = ∑ r ∈ R, ((S.filter fun z => dist z x = r).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _r ∈ R, L := Finset.sum_le_sum fun r _ => hfiber r
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [card_distance_image]

open Classical in
/-- Each pin has few targets in light fibers. Covers by lines and circles centered
away from the pin capture little mass relative to the line count and radial overlap. -/
private def SparseConfiguration (A : Finset ℝ²) (L : ℝ) : Prop :=
  (∀ x ∈ A, 2 * ((lightTargets A x L).card : ℝ) ≤ (A.card : ℝ)) ∧
    ∀ x ∈ A, ∀ C : Finset (ℝ² × ℝ), (∀ c ∈ C, c.1 ≠ x) →
      ∀ D : Finset (ℝ² × ℝ²), ∀ B ⊆ A.erase x,
        (∀ z ∈ B, (∃ c ∈ C, dist z c.1 = c.2) ∨ (∃ ℓ ∈ D, OnLine ℓ z)) →
          ∀ k : ℕ, (∀ r ∈ (A.erase x).image (fun z => dist z x),
            (circlesAtDistance x C r).card ≤ k) →
              (B.card : ℝ) * L ≤ ((k + D.card : ℕ) : ℝ) * (A.card : ℝ)

open Classical in
private theorem sharp_bound_of_not_sparse (A : Finset ℝ²) {L : ℝ} (hL : 0 < L)
    (h : ¬ SparseConfiguration A L) :
    (1 / 2 : ℝ) * ((A.card : ℝ) / L) ≤ ((A.sup (distinctDistancesFrom A) : ℕ) : ℝ) := by
  classical
  let M := A.sup (distinctDistancesFrom A)
  change (1 / 2 : ℝ) * ((A.card : ℝ) / L) ≤ (M : ℝ)
  rw [← mul_div_assoc, div_le_iff₀ hL]
  have hsup (x : ℝ²) (hx : x ∈ A) :
      (distinctDistancesFrom A x : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Finset.le_sup hx : distinctDistancesFrom A x ≤ _)
  unfold SparseConfiguration at h
  rw [not_and_or] at h
  rcases h with hlight | hdense
  · push Not at hlight
    obtain ⟨x, hx, hlight⟩ := hlight
    have hbound := (card_lightTargets_le A x hL.le).trans
      (mul_le_mul_of_nonneg_left (hsup x hx) hL.le)
    rw [mul_comm L] at hbound
    linarith only [hbound, hlight]
  · push Not at hdense
    obtain ⟨x, hx, C, hcenter, D, B, hB, hcover, k, hk, hdense⟩ := hdense
    let m := k + D.card
    have hcount : (B.card : ℝ) ≤ 2 * (m : ℝ) * (distinctDistancesFrom A x : ℝ) := by
      exact_mod_cast card_le_of_mixed_cover A B x C D hB hcenter hcover k hk
    have hmul : (m : ℝ) * (A.card : ℝ) < (m : ℝ) * (2 * (M : ℝ) * L) := by
      calc
        _ < (B.card : ℝ) * L := hdense
        _ ≤ (2 * (m : ℝ) * (distinctDistancesFrom A x : ℝ)) * L :=
          mul_le_mul_of_nonneg_right hcount hL.le
        _ ≤ (2 * (m : ℝ) * (M : ℝ)) * L := by
          gcongr
          exact Finset.le_sup hx
        _ = _ := by ring
    have hbound := lt_of_mul_lt_mul_left hmul (Nat.cast_nonneg m)
    linarith only [hbound]

private theorem minimum_attained (n : ℕ) :
    ∃ A : Finset ℝ², A.card = n ∧
      A.sup (distinctDistancesFrom A) = Erdos604.pinnedDistinctDistances n := by
  obtain ⟨B, hB⟩ := Infinite.exists_subset_card_eq ℝ² n
  let sizes : Set ℕ := {m | ∃ A : Finset ℝ², A.card = n ∧
    A.sup (distinctDistancesFrom A) = m}
  have hBsize : B.sup (distinctDistancesFrom B) ∈ sizes := ⟨B, hB, rfl⟩
  exact Nat.sInf_mem (Set.nonempty_of_mem hBsize)

private theorem sharp_of_sparse_configurations
    (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², A.card = n →
      SparseConfiguration A (Real.sqrt (Real.log (n : ℝ))) →
        c * ((n : ℝ) / Real.sqrt (Real.log (n : ℝ))) ≤
          ((A.sup (distinctDistancesFrom A) : ℕ) : ℝ)) :
    (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log (n : ℝ))) =O[atTop]
      (fun n => (Erdos604.pinnedDistinctDistances n : ℝ)) := by
  obtain ⟨c, hc, h⟩ := h
  let k := min c (1 / 2 : ℝ)
  have hk : 0 < k := lt_min hc (by norm_num)
  refine Asymptotics.isBigO_iff.mpr ⟨k⁻¹, ?_⟩
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  let L := Real.sqrt (Real.log (n : ℝ))
  have hL : 0 < L := Real.sqrt_pos_of_pos (Real.log_pos (by exact_mod_cast
    (show 1 < n by omega)))
  obtain ⟨A, hA, hmin⟩ := minimum_attained n
  have hq : 0 ≤ (n : ℝ) / L := div_nonneg (Nat.cast_nonneg n) hL.le
  have hbound : k * ((n : ℝ) / L) ≤ (Erdos604.pinnedDistinctDistances n : ℝ) := by
    rw [← hmin]
    by_cases hs : SparseConfiguration A L
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hq).trans (hn A hA hs)
    · refine (mul_le_mul_of_nonneg_right (min_le_right _ _) hq).trans ?_
      simpa only [hA] using sharp_bound_of_not_sparse A hL hs
  change ‖(n : ℝ) / L‖ ≤ k⁻¹ * ‖(Erdos604.pinnedDistinctDistances n : ℝ)‖
  rw [Real.norm_of_nonneg hq, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [← div_eq_inv_mul, le_div_iff₀ hk]
  simpa only [mul_comm] using hbound

theorem OMA.solution : type_of% @Erdos604.erdos_604.variants.sqrt_log := by
  apply sharp_of_sparse_configurations
  sorry

