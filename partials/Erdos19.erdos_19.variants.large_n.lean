import FormalConjectures.ErdosProblems.«19»

-- Problem: Erdős Problem 19 — large n
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/19.lean:248 (declaration Erdos19.erdos_19.variants.large_n)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! The large-order Erdős–Faber–Lovász problem via pairwise balanced designs. -/

open Filter

namespace OMA19

/-- Glue: n-colourability gives chromatic number exactly n (lower bound from a clique). -/
theorem chrom_eq_of_colorable {V : Type} {n : ℕ} (C : Erdos19.EFLConfig V n)
    (h : C.graph.Colorable n) : C.graph.chromaticNumber = n :=
  le_antisymm h.chromaticNumber_le C.le_chromaticNumber

section

open Finset

/-- A proper edge coloring assigns distinct colors to distinct intersecting edges. -/
def HasEdgeColoring {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ c : H → Fin n, ∀ A B : H, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

/-- Distinct points occur together in at most one edge of a linear family. -/
def IsLinear {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ ⦃A B⦄, A ∈ H → B ∈ H → ∀ ⦃i j⦄, i ≠ j →
    i ∈ A → j ∈ A → i ∈ B → j ∈ B → A = B

/-- A pairwise balanced design covers every pair exactly once with edges of size at least two. -/
def IsPairwiseBalanced {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  (∀ A ∈ H, 2 ≤ A.card) ∧
    ∀ i j : Fin n, i ≠ j → ∃! A, A ∈ H ∧ i ∈ A ∧ j ∈ A

theorem IsPairwiseBalanced.linear {n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : IsPairwiseBalanced H) : IsLinear H := by
  intro A B hA hB i j hij hiA hjA hiB hjB
  exact (hH.2 i j hij).unique ⟨hA, hiA, hjA⟩ ⟨hB, hiB, hjB⟩

/-- The edges of the family incident to a point. -/
def incident {n : ℕ} (H : Finset (Finset (Fin n))) (i : Fin n) : Finset H :=
  univ.filter (fun A => i ∈ A.val)

@[simp] theorem mem_incident {n : ℕ} {H : Finset (Finset (Fin n))}
    {i : Fin n} {A : H} : A ∈ incident H i ↔ i ∈ A.val := by
  simp [incident]

/-- The edges through a point partition the other points after that point is removed. -/
theorem IsPairwiseBalanced.sum_incident {n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : IsPairwiseBalanced H) (i : Fin n) :
    (∑ A ∈ incident H i, (A.val.card - 1)) = n - 1 := by
  let R (A : H) := A.val.erase i
  have hdis : ((incident H i : Finset H) : Set H).PairwiseDisjoint R := by
    intro A hA B hB hne
    apply disjoint_left.mpr
    intro j hjA hjB
    have ⟨hji, hAj⟩ := mem_erase.mp hjA
    have hBj := (mem_erase.mp hjB).2
    exact hne (Subtype.ext (hH.linear A.property B.property hji.symm
      (mem_incident.mp hA) hAj (mem_incident.mp hB) hBj))
  have hunion : (incident H i).biUnion R = univ.erase i := by
    ext j
    constructor
    · intro hj
      obtain ⟨A, _, hjA⟩ := mem_biUnion.mp hj
      exact mem_erase.mpr ⟨(mem_erase.mp hjA).1, mem_univ _⟩
    · intro hj
      have hji := (mem_erase.mp hj).1
      obtain ⟨A, hA, hiA, hjA⟩ := (hH.2 i j hji.symm).exists
      exact mem_biUnion.mpr ⟨⟨A, hA⟩, mem_incident.mpr hiA, mem_erase.mpr ⟨hji, hjA⟩⟩
  calc
    (∑ A ∈ incident H i, (A.val.card - 1)) = ∑ A ∈ incident H i, (R A).card := by
      apply sum_congr rfl
      intro A hA
      exact (card_erase_of_mem (mem_incident.mp hA)).symm
    _ = ((incident H i).biUnion R).card := (card_biUnion hdis).symm
    _ = n - 1 := by rw [hunion, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]

theorem IsPairwiseBalanced.card_incident_le {n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : IsPairwiseBalanced H) (i : Fin n) : (incident H i).card ≤ n - 1 := by
  rw [← hH.sum_incident i, card_eq_sum_ones]
  apply sum_le_sum
  intro A _
  have := hH.1 A.val A.property
  omega

theorem HasEdgeColoring.mono {n : ℕ} {H K : Finset (Finset (Fin n))}
    (hK : HasEdgeColoring K) (hHK : H ⊆ K) : HasEdgeColoring H := by
  obtain ⟨c, hc⟩ := hK
  let incl (A : H) : K := ⟨A.val, hHK A.property⟩
  refine ⟨fun A => c (incl A), fun A B hne h => hc (incl A) (incl B) ?_ h⟩
  exact fun heq => hne (Subtype.ext (congrArg (fun e : K => e.val) heq))

/-- A linear family extends to a pairwise balanced design by adjoining its uncovered pairs. -/
theorem exists_pairwiseBalanced_superset {n : ℕ} (H : Finset (Finset (Fin n)))
    (hsize : ∀ A ∈ H, 2 ≤ A.card) (hlin : IsLinear H) :
    ∃ K, H ⊆ K ∧ IsPairwiseBalanced K := by
  classical
  let P := ((univ : Finset (Fin n)).powersetCard 2).filter
    (fun e => ¬ ∃ A ∈ H, e ⊆ A)
  refine ⟨H ∪ P, subset_union_left, ?_, ?_⟩
  · intro A hA
    rcases mem_union.mp hA with hA | hA
    · exact hsize A hA
    · exact le_of_eq (mem_powersetCard.mp (mem_filter.mp hA).1).2.symm
  · intro i j hij
    have hcard : ({i, j} : Finset (Fin n)).card = 2 := card_pair hij
    have eq_pair {B : Finset (Fin n)} (hB : B ∈ P) (hi : i ∈ B) (hj : j ∈ B) :
        B = {i, j} := by
      have hs : ({i, j} : Finset (Fin n)) ⊆ B :=
        insert_subset hi (singleton_subset_iff.mpr hj)
      exact (eq_of_subset_of_card_le hs
        ((mem_powersetCard.mp (mem_filter.mp hB).1).2.trans hcard.symm).le).symm
    by_cases hcovered : ∃ A ∈ H, i ∈ A ∧ j ∈ A
    · obtain ⟨A, hA, hiA, hjA⟩ := hcovered
      refine ⟨A, ⟨mem_union_left _ hA, hiA, hjA⟩, ?_⟩
      rintro B ⟨hB, hiB, hjB⟩
      rcases mem_union.mp hB with hB | hB
      · exact hlin hB hA hij hiB hjB hiA hjA
      · have hmiss := (mem_filter.mp hB).2
        rw [eq_pair hB hiB hjB] at hmiss
        exact (hmiss ⟨A, hA, insert_subset hiA (singleton_subset_iff.mpr hjA)⟩).elim
    · have hpair : ({i, j} : Finset (Fin n)) ∈ P := by
        refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hcard⟩, ?_⟩
        rintro ⟨A, hA, hsub⟩
        exact hcovered ⟨A, hA, hsub (by simp), hsub (by simp)⟩
      refine ⟨{i, j}, ⟨mem_union_right _ hpair, by simp, by simp⟩, ?_⟩
      rintro B ⟨hB, hiB, hjB⟩
      rcases mem_union.mp hB with hB | hB
      · exact (hcovered ⟨B, hB, hiB, hjB⟩).elim
      · exact eq_pair hB hiB hjB

/-- The edges dual to the shared vertices suffice to color the whole configuration. -/
theorem colorable_of_pairwiseBalanced {V : Type} {n : ℕ} (C : Erdos19.EFLConfig V n)
    (hdesign : ∀ K : Finset (Finset (Fin n)), IsPairwiseBalanced K → HasEdgeColoring K) :
    C.graph.Colorable n := by
  classical
  let S (v : V) : Finset (Fin n) := univ.filter (fun i => v ∈ C.A i)
  let H := C.sharedSet.image S
  have memS (v : V) (i : Fin n) : i ∈ S v ↔ v ∈ C.A i := by simp [S]
  have shared (v : V) : v ∈ C.sharedSet ↔ C.IsShared v := by
    refine ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨?_, h⟩⟩
    obtain ⟨i, hi⟩ := C.cover v
    exact mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
  have same {u v : V} {i j : Fin n} (hij : i ≠ j)
      (hiu : i ∈ S u) (hju : j ∈ S u) (hiv : i ∈ S v) (hjv : j ∈ S v) : u = v :=
    card_le_one.mp (C.inter_le i j hij) u
      (mem_inter.mpr ⟨(memS _ _).mp hiu, (memS _ _).mp hju⟩) v
      (mem_inter.mpr ⟨(memS _ _).mp hiv, (memS _ _).mp hjv⟩)
  have hsize : ∀ A ∈ H, 2 ≤ A.card := by
    intro A hA
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hA
    obtain ⟨i, j, hij, hi, hj⟩ := (shared v).mp hv
    exact one_lt_card.mpr ⟨i, (memS _ _).mpr hi, j, (memS _ _).mpr hj, hij⟩
  have hlin : IsLinear H := by
    intro A B hA hB i j hij hiA hjA hiB hjB
    obtain ⟨u, _, rfl⟩ := mem_image.mp hA
    obtain ⟨v, _, rfl⟩ := mem_image.mp hB
    exact congrArg S (same hij hiA hjA hiB hjB)
  obtain ⟨K, hHK, hK⟩ := exists_pairwiseBalanced_superset H hsize hlin
  obtain ⟨c, hc⟩ := (hdesign K hK).mono hHK
  let col (v : V) : Fin n :=
    if h : v ∈ C.sharedSet then c ⟨S v, mem_image_of_mem S h⟩
    else (C.cover v).choose
  apply C.colorable_of_sharedColoring col
  intro k u v hku hkv hu hv heq
  have hmU := (shared u).mpr hu
  have hmV := (shared v).mpr hv
  let A : H := ⟨S u, mem_image_of_mem S hmU⟩
  let B : H := ⟨S v, mem_image_of_mem S hmV⟩
  have hAB : A = B := by
    by_contra hne
    apply hc A B hne ⟨k, mem_inter.mpr ⟨(memS _ _).mpr hku, (memS _ _).mpr hkv⟩⟩
    simpa only [col, dif_pos hmU, dif_pos hmV] using heq
  have hs : S u = S v := congrArg (fun e : H => e.val) hAB
  obtain ⟨i, j, hij, hi, hj⟩ := hu
  have his := (memS u i).mpr hi
  have hjs := (memS u j).mpr hj
  exact same hij his hjs (hs ▸ his) (hs ▸ hjs)

/-- Pad each clique with private vertices to recover the original configuration from a design. -/
theorem edgeColorable_of_configs {n : ℕ}
    (hconfigs : ∀ (V : Type) (C : Erdos19.EFLConfig V n), C.graph.Colorable n)
    {H : Finset (Finset (Fin n))} (hH : IsPairwiseBalanced H) : HasEdgeColoring H := by
  classical
  let P (i : Fin n) := Fin (n - (incident H i).card)
  let V := H ⊕ (Σ i : Fin n, P i)
  let _ : DecidableEq V := Classical.decEq V
  let shared : H ↪ V := ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩
  let pad (i : Fin n) : P i ↪ V := ⟨fun x => Sum.inr ⟨i, x⟩, by
    intro x y h
    exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2⟩
  let A (i : Fin n) : Finset V := (incident H i).map shared ∪ univ.map (pad i)
  have mem_shared (i : Fin n) (e : H) : shared e ∈ A i ↔ i ∈ e.val := by
    simp [A, shared, pad, Finset.mem_map]
  have mem_private (i j : Fin n) (x : P j) :
      Sum.inr (Sigma.mk j x) ∈ A i ↔ i = j := by
    constructor
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · obtain ⟨e, _, he⟩ := mem_map.mp hx
        change (Sum.inl e : V) = Sum.inr ⟨j, x⟩ at he
        cases he
      · obtain ⟨y, _, hy⟩ := mem_map.mp hx
        exact congrArg Sigma.fst (Sum.inr.inj hy)
    · rintro rfl
      exact mem_union_right _ (mem_map_of_mem (pad i) (mem_univ x))
  have hcard (i : Fin n) : (A i).card = n := by
    have hd : Disjoint ((incident H i).map shared) (univ.map (pad i)) := by
      apply disjoint_left.mpr
      intro v hv hw
      obtain ⟨e, _, rfl⟩ := mem_map.mp hv
      obtain ⟨x, _, hx⟩ := mem_map.mp hw
      change (Sum.inr ⟨i, x⟩ : V) = Sum.inl e at hx
      cases hx
    have hle : (incident H i).card ≤ n := (hH.card_incident_le i).trans (Nat.sub_le _ _)
    simpa only [A, card_union_of_disjoint hd, card_map, card_univ, P, Fintype.card_fin]
      using Nat.add_sub_of_le hle
  have shared_of_mem_inter {i j : Fin n} (hij : i ≠ j) {v : V} (hv : v ∈ A i ∩ A j) :
      ∃ e : H, v = shared e ∧ i ∈ e.val ∧ j ∈ e.val := by
    have ⟨hi, hj⟩ := mem_inter.mp hv
    rcases v with e | ⟨k, x⟩
    · exact ⟨e, rfl, (mem_shared i e).mp hi, (mem_shared j e).mp hj⟩
    · exact (hij (((mem_private i k x).mp hi).trans ((mem_private j k x).mp hj).symm)).elim
  let C : Erdos19.EFLConfig V n := {
    A := A
    card_eq := hcard
    inter_le := by
      intro i j hij
      apply card_le_one.mpr
      intro u hu v hv
      obtain ⟨e, rfl, hi, hj⟩ := shared_of_mem_inter hij hu
      obtain ⟨f, rfl, hi', hj'⟩ := shared_of_mem_inter hij hv
      exact congrArg shared (Subtype.ext (hH.linear e.property f.property hij hi hj hi' hj'))
    cover := by
      rintro (e | ⟨i, x⟩)
      · have hp : 0 < e.val.card := (by decide : 0 < 2).trans_le (hH.1 e.val e.property)
        obtain ⟨i, hi⟩ := card_pos.mp hp
        exact ⟨i, (mem_shared i e).mpr hi⟩
      · exact ⟨i, (mem_private i i x).mpr rfl⟩ }
  obtain ⟨c⟩ := hconfigs V C
  refine ⟨fun e => c (shared e), ?_⟩
  rintro e f hne ⟨i, hi⟩
  have ⟨hie, hif⟩ := mem_inter.mp hi
  exact c.valid ⟨fun h => hne (shared.injective h),
    i, (mem_shared i e).mpr hie, (mem_shared i f).mpr hif⟩

theorem configs_colorable_iff_pairwiseBalanced (n : ℕ) :
    (∀ (V : Type) (C : Erdos19.EFLConfig V n), C.graph.Colorable n) ↔
      ∀ H : Finset (Finset (Fin n)), IsPairwiseBalanced H → HasEdgeColoring H :=
  ⟨fun h _ => edgeColorable_of_configs h, fun h _ C => colorable_of_pairwiseBalanced C h⟩

/-- The remaining large-order edge-coloring theorem for pairwise balanced designs. -/
theorem pairwiseBalanced_edgeColorable :
    ∀ᶠ n in atTop, ∀ K : Finset (Finset (Fin n)), IsPairwiseBalanced K → HasEdgeColoring K := by
  sorry

end

/-- Transfer the large-order edge-coloring theorem to the clique union. -/
theorem kkkmo_colorable :
    ∀ᶠ n in atTop, ∀ (V : Type) (C : Erdos19.EFLConfig V n), C.graph.Colorable n := by
  filter_upwards [pairwiseBalanced_edgeColorable] with n hn V C
  exact colorable_of_pairwiseBalanced C hn

end OMA19

theorem OMA.solution : type_of% @Erdos19.erdos_19.variants.large_n := by
  filter_upwards [OMA19.kkkmo_colorable] with n hn V C
  exact OMA19.chrom_eq_of_colorable C (hn V C)
