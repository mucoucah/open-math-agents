import OMAReductions.R_Erdos19_erdos_19_variants_kahn_R1

-- Step Erdos19.erdos_19.variants.kahn.R1.H1: hypothesis H1 of reduction Erdos19.erdos_19.variants.kahn.R1
/-! The case q = 1 uses greedy colouring. The general case reduces to a
matching that meets every demand vertex in the assignment hypergraph. -/

open Finset

namespace OMAH1

theorem meet_le {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (d : ℕ) (hd : ∀ i ∈ A, (H.filter (fun A => i ∈ A)).card ≤ d) :
    (H.filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * d := by
  have heq : H.filter (fun B => (A ∩ B).Nonempty) =
      A.biUnion (fun i => H.filter (fun A => i ∈ A)) := by
    ext B
    simp only [mem_filter, mem_biUnion, Finset.Nonempty, mem_inter]
    constructor
    · rintro ⟨hB, i, hiA, hiB⟩
      exact ⟨i, hiA, hB, hiB⟩
    · rintro ⟨i, hiA, hB, hiB⟩
      exact ⟨hB, i, hiA, hiB⟩
  rw [heq]
  calc (A.biUnion (fun i => H.filter (fun A => i ∈ A))).card
      ≤ ∑ i ∈ A, (H.filter (fun A => i ∈ A)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, d := Finset.sum_le_sum hd
    _ = A.card * d := by simp

/-- Greedy list colouring. -/
theorem greedy {n m : ℕ} (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hm : 0 < m)
    (hL : ∀ A ∈ H, ((H.erase A).filter (fun B => (A ∩ B).Nonempty)).card < (L A).card) :
    ∃ c : Finset (Fin n) → Fin m,
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  induction H using Finset.strongInductionOn with
  | _ H ih =>
    by_cases hH : H.Nonempty
    · obtain ⟨A, hA⟩ := hH
      let K := H.erase A
      have hKH : K ⊆ H := Finset.erase_subset _ _
      obtain ⟨c, hc, hcL⟩ := ih K (Finset.erase_ssubset hA) (by
        intro B hB
        refine lt_of_le_of_lt ?_ (hL B (hKH hB))
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        exact Finset.erase_subset_erase _ hKH)
      let blocked := (K.filter (fun B => (A ∩ B).Nonempty)).image c
      have hblocked : blocked.card < (L A).card :=
        lt_of_le_of_lt Finset.card_image_le (hL A hA)
      have hfree : (L A \ blocked).Nonempty := by
        apply Finset.card_pos.mp
        have := Finset.le_card_sdiff blocked (L A)
        omega
      obtain ⟨w, hw⟩ := hfree
      have hne : ∀ B ∈ K, (A ∩ B).Nonempty → w ≠ c B := by
        intro B hB hi he
        exact (mem_sdiff.mp hw).2 (he ▸ mem_image_of_mem c (mem_filter.mpr ⟨hB, hi⟩))
      refine ⟨fun B => if B = A then w else c B, ?_, ?_⟩
      · intro B hB D hD hBD hi
        by_cases hBA : B = A
        · subst B
          have hDA := Ne.symm hBD
          simpa only [if_pos rfl, if_true, if_neg hDA] using hne D (mem_erase.mpr ⟨hDA, hD⟩) hi
        by_cases hDA : D = A
        · subst D
          have hi' : (A ∩ B).Nonempty := by simpa only [Finset.inter_comm] using hi
          simpa only [if_pos rfl, if_true, if_neg hBA] using
            (hne B (mem_erase.mpr ⟨hBA, hB⟩) hi').symm
        simpa only [if_neg hBA, if_neg hDA] using
          hc B (mem_erase.mpr ⟨hBA, hB⟩) D (mem_erase.mpr ⟨hDA, hD⟩) hBD hi
      · intro B hB
        by_cases hBA : B = A
        · subst B; simpa using (mem_sdiff.mp hw).1
        · simpa only [if_neg hBA] using hcL B (mem_erase.mpr ⟨hBA, hB⟩)
    · exact ⟨fun _ => ⟨0, hm⟩, fun A hA => (hH ⟨A, hA⟩).elim, fun A hA => (hH ⟨A, hA⟩).elim⟩

/-- Neighbourhood bound in a hypergraph of maximum degree D. -/
theorem nbhd_le {n : ℕ} (H : Finset (Finset (Fin n))) (D : ℕ) (A : Finset (Fin n)) (hA : A ∈ H)
    (hdeg : ∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) :
    ((H.erase A).filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * (D - 1) := by
  apply meet_le
  intro i hi
  have : (H.erase A).filter (fun B => i ∈ B) = (H.filter (fun B => i ∈ B)).erase A := by
    ext B; simp [mem_filter, mem_erase]; tauto
  rw [this, Finset.card_erase_of_mem (mem_filter.mpr ⟨hA, hi⟩)]
  have := hdeg i
  omega

/-- The case q = 1 (rank at most 2): greedy works with lists of size 2D. -/
theorem case_one : ∃ D₀ : ℕ, ∀ n D m : ℕ, D₀ ≤ D → 0 < m →
    ∀ (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ 2 * 1) →
      (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) → (∀ A ∈ H, D + D / 1 ≤ (L A).card) →
      ∃ c : Finset (Fin n) → Fin m,
        (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  refine ⟨1, fun n D m hD hm H L _ hsize hdeg hL => greedy H L hm ?_⟩
  intro A hA
  have h1 := nbhd_le H D A hA hdeg
  have h2 := hsize A hA
  have h3 := hL A hA
  rw [Nat.div_one] at h3
  have h4 : A.card * (D - 1) ≤ 2 * (D - 1) := Nat.mul_le_mul_right _ h2.2
  omega

/-- A bipartite matching principle, with one demand vertex and at most r resource
vertices per edge. Edges are indexed, and codegrees count indices. -/
def OneSidedMatching (r q : ℕ) : Prop :=
  ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    ∀ {X Y I : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq I]
      (V : Finset X) (F : Finset I) (demand : I → X) (resource : I → Finset Y),
      (∀ e ∈ F, demand e ∈ V ∧ (resource e).card ≤ r) →
      (∀ x ∈ V, D + D / q ≤ (F.filter (fun e => demand e = x)).card) →
      (∀ y, (F.filter (fun e => y ∈ resource e)).card ≤ D) →
      (∀ x y, (F.filter (fun e => demand e = x ∧ y ∈ resource e)).card ≤ 1) →
      (∀ y z, y ≠ z → (F.filter (fun e => y ∈ resource e ∧ z ∈ resource e)).card ≤ 1) →
      ∃ M ⊆ F, (∀ x ∈ V, ∃ e ∈ M, demand e = x) ∧
        (M : Set I).Pairwise (fun e f => Disjoint (resource e) (resource f))

abbrev Choice (n m : ℕ) := Finset (Fin n) × Fin m

def choices {n m : ℕ} (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)) :
    Finset (Choice n m) :=
  H.biUnion fun A => (L A).image (Prod.mk A)

theorem mem_choices {n m : ℕ} {H : Finset (Finset (Fin n))}
    {L : Finset (Fin n) → Finset (Fin m)} {e : Choice n m} :
    e ∈ choices H L ↔ e.1 ∈ H ∧ e.2 ∈ L e.1 := by
  rcases e with ⟨A, c⟩
  simp [choices]

def slots {n m : ℕ} (e : Choice n m) : Finset (Fin n × Fin m) :=
  e.1.image (fun v => (v, e.2))

theorem mem_slots {n m : ℕ} {e : Choice n m} {y : Fin n × Fin m} :
    y ∈ slots e ↔ y.1 ∈ e.1 ∧ y.2 = e.2 := by
  rcases y with ⟨v, c⟩
  simp [slots, eq_comm]

theorem slots_card {n m : ℕ} (e : Choice n m) : (slots e).card = e.1.card :=
  Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

theorem choice_degree {n m : ℕ} (H : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) {A : Finset (Fin n)} (hA : A ∈ H) :
    ((choices H L).filter (fun e => e.1 = A)).card = (L A).card := by
  have h : (choices H L).filter (fun e => e.1 = A) = (L A).image (Prod.mk A) := by
    ext e
    rcases e with ⟨B, c⟩
    simp only [mem_filter, mem_choices, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, hc⟩, rfl⟩
      exact ⟨c, hc, rfl, rfl⟩
    · rintro ⟨a, ha, rfl, rfl⟩
      exact ⟨⟨hA, ha⟩, rfl⟩
  rw [h, Finset.card_image_of_injective _ (fun _ _ he => congrArg Prod.snd he)]

theorem slot_degree {n m : ℕ} (H : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) (y : Fin n × Fin m) :
    ((choices H L).filter (fun e => y ∈ slots e)).card ≤
      (H.filter (fun A => y.1 ∈ A)).card := by
  apply Finset.card_le_card_of_injOn (f := Prod.fst)
  · intro e he
    have ⟨he, hy⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨(mem_choices.mp he).1, (mem_slots.mp hy).1⟩
  · intro e he f hf h
    exact Prod.ext h ((mem_slots.mp (mem_filter.mp he).2).2.symm.trans
      (mem_slots.mp (mem_filter.mp hf).2).2)

theorem demand_slot_codegree {n m : ℕ} (F : Finset (Choice n m))
    (A : Finset (Fin n)) (y : Fin n × Fin m) :
    (F.filter (fun e => e.1 = A ∧ y ∈ slots e)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  have ⟨heA, hey⟩ := (mem_filter.mp he).2
  have ⟨hfA, hfy⟩ := (mem_filter.mp hf).2
  exact Prod.ext (heA.trans hfA.symm) ((mem_slots.mp hey).2.symm.trans (mem_slots.mp hfy).2)

theorem slot_codegree {n m : ℕ} (H : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m))
    (hlinear : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (y z : Fin n × Fin m) (hyz : y ≠ z) :
    ((choices H L).filter (fun e => y ∈ slots e ∧ z ∈ slots e)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  have ⟨he, hey, hez⟩ := mem_filter.mp he
  have ⟨hf, hfy, hfz⟩ := mem_filter.mp hf
  have ⟨hey, heyc⟩ := mem_slots.mp hey
  have ⟨hez, hezc⟩ := mem_slots.mp hez
  have ⟨hfy, hfyc⟩ := mem_slots.mp hfy
  have ⟨hfz, _⟩ := mem_slots.mp hfz
  have hvw : y.1 ≠ z.1 := fun h => hyz (Prod.ext h (heyc.trans hezc.symm))
  have heq : e.1 = f.1 := by
    by_contra hne
    have hbound := hlinear e.1 (mem_choices.mp he).1 f.1 (mem_choices.mp hf).1 hne
    have hsub : {y.1, z.1} ⊆ e.1 ∩ f.1 := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_inter.mpr ⟨hey, hfy⟩
      · rcases mem_singleton.mp hv with rfl
        exact mem_inter.mpr ⟨hez, hfz⟩
    have hcard := Finset.card_le_card hsub
    simp [hvw] at hcard
    omega
  exact Prod.ext heq (heyc.symm.trans hfyc)

theorem colour_of_matching {n m : ℕ} (hm : 0 < m) (H : Finset (Finset (Fin n)))
    (L : Finset (Fin n) → Finset (Fin m)) {M : Finset (Choice n m)}
    (hsub : M ⊆ choices H L) (hcover : ∀ A ∈ H, ∃ e ∈ M, e.1 = A)
    (hdisj : (M : Set (Choice n m)).Pairwise (fun e f => Disjoint (slots e) (slots f))) :
    ∃ c : Finset (Fin n) → Fin m,
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  classical
  let e (A : Finset (Fin n)) (hA : A ∈ H) : Choice n m := Classical.choose (hcover A hA)
  have he (A : Finset (Fin n)) (hA : A ∈ H) : e A hA ∈ M ∧ (e A hA).1 = A :=
    Classical.choose_spec (hcover A hA)
  let c (A : Finset (Fin n)) : Fin m := if hA : A ∈ H then (e A hA).2 else ⟨0, hm⟩
  have hc (A : Finset (Fin n)) (hA : A ∈ H) : c A = (e A hA).2 := dif_pos hA
  refine ⟨c, ?_, ?_⟩
  · rintro A hA B hB hAB ⟨v, hv⟩ heq
    have ⟨hvA, hvB⟩ := mem_inter.mp hv
    have hne : e A hA ≠ e B hB := by
      intro hab
      exact hAB ((he A hA).2.symm.trans ((congrArg Prod.fst hab).trans (he B hB).2))
    have hd := hdisj (he A hA).1 (he B hB).1 hne
    have ha : (v, c A) ∈ slots (e A hA) :=
      mem_slots.mpr ⟨by simpa [(he A hA).2] using hvA, hc A hA⟩
    have hb : (v, c A) ∈ slots (e B hB) :=
      mem_slots.mpr ⟨by simpa [(he B hB).2] using hvB, heq.trans (hc B hB)⟩
    exact Finset.disjoint_left.mp hd ha hb
  · intro A hA
    have h := (mem_choices.mp (hsub (he A hA).1)).2
    simpa only [hc A hA, (he A hA).2] using h

theorem case_of_matching (q : ℕ) (hmatch : OneSidedMatching (2 * q) q) :
    ∃ D₀ : ℕ, ∀ n D m : ℕ, D₀ ≤ D → 0 < m →
      ∀ (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
        (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
        (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ 2 * q) →
        (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) →
        (∀ A ∈ H, D + D / q ≤ (L A).card) →
        ∃ c : Finset (Fin n) → Fin m,
          (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  obtain ⟨D₀, hmatch⟩ := hmatch
  refine ⟨D₀, ?_⟩
  intro n D m hD hm H L hlinear hsize hdeg hL
  obtain ⟨M, hM, hcover, hdisj⟩ := hmatch D hD H (choices H L) Prod.fst slots
    (fun e he => ⟨(mem_choices.mp he).1, (slots_card e).trans_le (hsize _ (mem_choices.mp he).1).2⟩)
    (fun A hA => (hL A hA).trans_eq (choice_degree H L hA).symm)
    (fun y => (slot_degree H L y).trans (hdeg y.1))
    (demand_slot_codegree (choices H L)) (slot_codegree H L hlinear)
  exact colour_of_matching hm H L hM hcover hdisj

/-- Trim the candidates for each demand independently to a common size. -/
theorem truncate_choices {X I : Type} [DecidableEq X] [DecidableEq I]
    (V : Finset X) (F : Finset I) (demand : I → X) (ℓ : ℕ)
    (hℓ : ∀ x ∈ V, ℓ ≤ (F.filter (fun e => demand e = x)).card) :
    ∃ F' ⊆ F, (∀ e ∈ F', demand e ∈ V) ∧
      ∀ x ∈ V, (F'.filter (fun e => demand e = x)).card = ℓ := by
  classical
  have hpick (x : X) (hx : x ∈ V) :
      ∃ T ⊆ F.filter (fun e => demand e = x), T.card = ℓ :=
    Finset.exists_subset_card_eq (hℓ x hx)
  let pick (x : X) : Finset I := if hx : x ∈ V then Classical.choose (hpick x hx) else ∅
  have hsub (x : X) (hx : x ∈ V) : pick x ⊆ F.filter (fun e => demand e = x) := by
    simpa only [pick, dif_pos hx] using (Classical.choose_spec (hpick x hx)).1
  have hcard (x : X) (hx : x ∈ V) : (pick x).card = ℓ := by
    simpa only [pick, dif_pos hx] using (Classical.choose_spec (hpick x hx)).2
  refine ⟨V.biUnion pick, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, hx, hex⟩ := mem_biUnion.mp he
    exact (mem_filter.mp (hsub x hx hex)).1
  · intro e he
    obtain ⟨x, hx, hex⟩ := mem_biUnion.mp he
    rwa [(mem_filter.mp (hsub x hx hex)).2]
  · intro x hx
    have heq : (V.biUnion pick).filter (fun e => demand e = x) = pick x := by
      ext e
      constructor
      · intro he
        obtain ⟨he, hd⟩ := mem_filter.mp he
        obtain ⟨z, hz, hez⟩ := mem_biUnion.mp he
        have hzx := (mem_filter.mp (hsub z hz hez)).2.symm.trans hd
        rwa [← hzx]
      · intro he
        exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨x, hx, he⟩, (mem_filter.mp (hsub x hx he)).2⟩
    rw [heq, hcard x hx]

theorem greedy_residual {n m r d : ℕ} (hm : 0 < m) (K : Finset (Finset (Fin n)))
    (R : Finset (Fin n) → Finset (Fin m))
    (hsize : ∀ A ∈ K, A.card ≤ r)
    (hdeg : ∀ v, (K.filter (fun A => v ∈ A)).card ≤ d)
    (hR : ∀ A ∈ K, r * (d - 1) < (R A).card) :
    ∃ c : Finset (Fin n) → Fin m,
      (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ K, c A ∈ R A := by
  apply greedy K R hm
  intro A hA
  exact ((nbhd_le K d A hA hdeg).trans (Nat.mul_le_mul_right _ (hsize A hA))).trans_lt (hR A hA)

/-- A colouring of the already covered edges extends if the unused lists are
large enough for the maximum degree of the uncovered edges. -/
theorem finish_with_reserve {n m r d : ℕ} (hm : 0 < m) (H K : Finset (Finset (Fin n)))
    (L R : Finset (Fin n) → Finset (Fin m)) (c : Finset (Fin n) → Fin m)
    (hproper : ∀ A ∈ H \ K, ∀ B ∈ H \ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B)
    (hc : ∀ A ∈ H \ K, c A ∈ L A)
    (hsize : ∀ A ∈ K, A.card ≤ r)
    (hdeg : ∀ v, (K.filter (fun A => v ∈ A)).card ≤ d)
    (hR : ∀ A ∈ K, r * (d - 1) < (R A).card ∧ R A ⊆ L A)
    (hfree : ∀ A ∈ K, ∀ B ∈ H \ K, (A ∩ B).Nonempty → c B ∉ R A) :
    ∃ f : Finset (Fin n) → Fin m,
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → f A ≠ f B) ∧ ∀ A ∈ H, f A ∈ L A := by
  obtain ⟨g, hg, hgR⟩ := greedy_residual hm K R hsize hdeg (fun A hA => (hR A hA).1)
  refine ⟨fun A => if A ∈ K then g A else c A, ?_, ?_⟩
  · intro A hA B hB hAB hi
    by_cases hAK : A ∈ K <;> by_cases hBK : B ∈ K <;> simp only [hAK, hBK, if_true, if_false]
    · exact hg A hAK B hBK hAB hi
    · exact fun he => hfree A hAK B (mem_sdiff.mpr ⟨hB, hBK⟩) hi (he ▸ hgR A hAK)
    · have hi' : (B ∩ A).Nonempty := by simpa only [Finset.inter_comm] using hi
      exact fun he => hfree B hBK A (mem_sdiff.mpr ⟨hA, hAK⟩) hi' (he.symm ▸ hgR B hBK)
    · exact hproper A (mem_sdiff.mpr ⟨hA, hAK⟩) B (mem_sdiff.mpr ⟨hB, hBK⟩) hAB hi
  · intro A hA
    by_cases hAK : A ∈ K
    · simpa only [if_pos hAK] using (hR A hAK).2 (hgR A hAK)
    · simpa only [if_neg hAK] using hc A (mem_sdiff.mpr ⟨hA, hAK⟩)

/- Independent Bernoulli marks: exponential moments, tails and a local lemma. -/

section Bernoulli
variable {I : Type} [DecidableEq I]

noncomputable def markWeight (p : I → ℝ) (T S : Finset I) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ T \ S, (1 - p i)

noncomputable def markAvg (p : I → ℝ) (T : Finset I) (g : Finset I → ℝ) : ℝ :=
  ∑ S ∈ T.powerset, markWeight p T S * g S

theorem markAvg_insert (p : I → ℝ) (T : Finset I) (g : Finset I → ℝ) {i : I} (hi : i ∉ T) :
    markAvg p (insert i T) g =
      (1 - p i) * markAvg p T g + p i * markAvg p T (fun S => g (insert i S)) := by
  have hs {S : Finset I} (hS : S ⊆ T) : i ∉ S := fun h => hi (hS h)
  have hdisj : Disjoint T.powerset (T.powerset.image (insert i)) := by
    rw [Finset.disjoint_left]
    intro S hS hSi
    obtain ⟨U, _, rfl⟩ := mem_image.mp hSi
    exact hs (mem_powerset.mp hS) (mem_insert_self _ _)
  unfold markAvg
  rw [powerset_insert, sum_union hdisj, sum_image, mul_sum, mul_sum]
  · congr 1
    · apply sum_congr rfl
      intro S hS
      have hSi := hs (mem_powerset.mp hS)
      have heq : insert i T \ S = insert i (T \ S) := by
        ext j
        by_cases h : j = i
        · subst j
          simp [hSi]
        · simp [h]
      rw [markWeight, heq, prod_insert (fun h => hi (mem_sdiff.mp h).1), markWeight]
      ring
    · apply sum_congr rfl
      intro S hS
      have hSi := hs (mem_powerset.mp hS)
      have heq : insert i T \ insert i S = T \ S := by
        ext j
        by_cases h : j = i
        · subst j
          simp [hi]
        · simp [h]
      rw [markWeight, heq, prod_insert hSi, markWeight]
      ring
  · intro S hS U hU h
    have hS' := hs (mem_powerset.mp hS)
    have hU' := hs (mem_powerset.mp hU)
    simpa [hS', hU'] using congrArg (fun Z : Finset I => Z.erase i) h

theorem markAvg_const (p : I → ℝ) (T : Finset I) (c : ℝ) : markAvg p T (fun _ => c) = c := by
  induction T using Finset.induction_on with
  | empty => simp [markAvg, markWeight]
  | insert i T hi ih =>
    simp only [markAvg_insert p T _ hi, ih]
    ring

theorem markAvg_mono (p : I → ℝ) (T : Finset I) {f g : Finset I → ℝ}
    (hp : ∀ i ∈ T, 0 ≤ p i ∧ p i ≤ 1) (hfg : ∀ S ⊆ T, f S ≤ g S) :
    markAvg p T f ≤ markAvg p T g := by
  unfold markAvg markWeight
  apply sum_le_sum
  intro S hS
  have hsub := mem_powerset.mp hS
  apply mul_le_mul_of_nonneg_left (hfg S hsub)
  exact mul_nonneg (prod_nonneg fun i hi => (hp i (hsub hi)).1)
    (prod_nonneg fun i hi => sub_nonneg.mpr (hp i (mem_sdiff.mp hi).1).2)

theorem markAvg_mul (p : I → ℝ) (T : Finset I) (f : Finset I → ℝ) (c : ℝ) :
    markAvg p T (fun S => c * f S) = c * markAvg p T f := by
  simp only [markAvg, Finset.mul_sum]
  exact sum_congr rfl (fun S _ => by ring)

theorem markAvg_sub (p : I → ℝ) (T : Finset I) (f g : Finset I → ℝ) :
    markAvg p T (fun S => f S - g S) = markAvg p T f - markAvg p T g := by
  simp only [markAvg, mul_sub, sum_sub_distrib]

theorem bernoulli_exp_bound {p x : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hx : |x| ≤ 1) :
    (1 - p) * Real.exp (-p * x) + p * Real.exp ((1 - p) * x) ≤ Real.exp (p * x ^ 2) := by
  have hp0 : 0 ≤ 1 - p := sub_nonneg.mpr hp'
  have hq1 : 1 - p ≤ 1 := by linarith
  have ha : |-p * x| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hp]
    exact (mul_le_mul_of_nonneg_left hx hp).trans (by simpa using hp')
  have hb : |(1 - p) * x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hp0]
    exact (mul_le_mul_of_nonneg_left hx hp0).trans (by simpa using hq1)
  have exp_quad (y : ℝ) (hy : |y| ≤ 1) : Real.exp y ≤ 1 + y + y ^ 2 := by
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hy)).2
    linarith
  calc
    _ ≤ (1 - p) * (1 + (-p * x) + (-p * x) ^ 2) +
        p * (1 + (1 - p) * x + ((1 - p) * x) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (exp_quad _ ha) hp0) (mul_le_mul_of_nonneg_left (exp_quad _ hb) hp)
    _ = 1 + p * x ^ 2 - p ^ 2 * x ^ 2 := by ring
    _ ≤ 1 + p * x ^ 2 := sub_le_self _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ _ := by linarith [Real.add_one_le_exp (p * x ^ 2)]

theorem markAvg_exp_centered (p b : I → ℝ) (T : Finset I) (g : Finset I → ℝ) (t : ℝ)
    (hp : ∀ i ∈ T, 0 ≤ p i ∧ p i ≤ 1)
    (hb : ∀ i ∈ T, 0 ≤ b i ∧ |t| * b i ≤ 1)
    (hflip : ∀ i ∈ T, ∀ S ⊆ T, i ∉ S → |g (insert i S) - g S| ≤ b i) :
    markAvg p T (fun S => Real.exp (t * (g S - markAvg p T g))) ≤
      Real.exp (∑ i ∈ T, p i * (t * b i)^2) := by
  induction T using Finset.induction_on generalizing g with
  | empty => simp [markAvg, markWeight]
  | insert i T hi ih =>
    let g₁ : Finset I → ℝ := fun S => g (insert i S)
    let a := markAvg p T g
    let a₁ := markAvg p T g₁
    let u := (1 - p i) * a + p i * a₁
    let C := ∑ j ∈ T, p j * (t * b j)^2
    have hu : markAvg p (insert i T) g = u := markAvg_insert p T g hi
    have hpi := hp i (mem_insert_self i T)
    have hisub : T ⊆ insert i T := subset_insert i T
    have hpT : ∀ j ∈ T, 0 ≤ p j ∧ p j ≤ 1 := fun j hj => hp j (hisub hj)
    have hbT : ∀ j ∈ T, 0 ≤ b j ∧ |t| * b j ≤ 1 := fun j hj => hb j (hisub hj)
    have hdiff : |a₁ - a| ≤ b i := by
      apply abs_le.mpr
      rw [show a₁ - a = markAvg p T (fun S => g₁ S - g S) from (markAvg_sub p T g₁ g).symm]
      constructor
      · rw [← markAvg_const p T (-b i)]
        exact markAvg_mono p T hpT fun S hS =>
          (abs_le.mp (hflip i (mem_insert_self i T) S (hS.trans hisub) (fun h => hi (hS h)))).1
      · rw [← markAvg_const p T (b i)]
        exact markAvg_mono p T hpT fun S hS =>
          (abs_le.mp (hflip i (mem_insert_self i T) S (hS.trans hisub) (fun h => hi (hS h)))).2
    have hg : markAvg p T (fun S => Real.exp (t * (g S - a))) ≤ Real.exp C :=
      ih g hpT hbT (fun j hj S hS hjS => hflip j (hisub hj) S (hS.trans hisub) hjS)
    have hg₁ : markAvg p T (fun S => Real.exp (t * (g₁ S - a₁))) ≤ Real.exp C := by
      apply ih g₁ hpT hbT
      intro j hj S hS hjS
      have hji : j ≠ i := ne_of_mem_of_not_mem hj hi
      change |g (insert i (insert j S)) - g (insert i S)| ≤ b j
      rw [Finset.insert_comm i j]
      exact hflip j (hisub hj) (insert i S) (insert_subset_insert i hS) (by simp [hji, hjS])
    have split_avg (f : Finset I → ℝ) (c : ℝ) :
        markAvg p T (fun S => Real.exp (t * (f S - u))) =
          Real.exp (t * (c - u)) * markAvg p T (fun S => Real.exp (t * (f S - c))) := by
      rw [← markAvg_mul]
      congr 1
      funext S
      rw [← Real.exp_add]
      congr 1
      ring
    have hterm : |t * (a₁ - a)| ≤ |t| * b i := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg t)
    have hbern := bernoulli_exp_bound hpi.1 hpi.2 (hterm.trans (hb i (mem_insert_self i T)).2)
    have htermsq : (t * (a₁ - a))^2 ≤ (t * b i)^2 := by
      apply sq_le_sq.mpr
      rwa [abs_mul t (b i), abs_of_nonneg (hb i (mem_insert_self i T)).1]
    have hber : (1 - p i) * Real.exp (t * (a - u)) + p i * Real.exp (t * (a₁ - u)) ≤
        Real.exp (p i * (t * b i)^2) := by
      have ha : t * (a - u) = -p i * (t * (a₁ - a)) := by dsimp only [u]; ring
      have ha₁ : t * (a₁ - u) = (1 - p i) * (t * (a₁ - a)) := by dsimp only [u]; ring
      rw [ha, ha₁]
      exact hbern.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htermsq hpi.1))
    rw [hu, markAvg_insert p T _ hi, sum_insert hi]
    change (1 - p i) * markAvg p T (fun S => Real.exp (t * (g S - u))) +
      p i * markAvg p T (fun S => Real.exp (t * (g₁ S - u))) ≤ Real.exp (p i * (t * b i)^2 + C)
    rw [split_avg g a, split_avg g₁ a₁]
    calc
      _ ≤ (1 - p i) * (Real.exp (t * (a - u)) * Real.exp C) +
          p i * (Real.exp (t * (a₁ - u)) * Real.exp C) :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (Real.exp_nonneg _))
          (sub_nonneg.mpr hpi.2)) (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hg₁ (Real.exp_nonneg _)) hpi.1)
      _ = ((1 - p i) * Real.exp (t * (a - u)) + p i * Real.exp (t * (a₁ - u))) *
          Real.exp C := by ring
      _ ≤ _ := by
        rw [Real.exp_add]
        exact mul_le_mul_of_nonneg_right hber (Real.exp_nonneg _)

noncomputable def markProb (p : I → ℝ) (T : Finset I) (A : Finset I → Prop) : ℝ :=
  open Classical in
  markAvg p T (fun S => if A S then 1 else 0)

theorem markProb_tail (p b : I → ℝ) (T : Finset I) (g : Finset I → ℝ) (t a : ℝ)
    (hp : ∀ i ∈ T, 0 ≤ p i ∧ p i ≤ 1)
    (hb : ∀ i ∈ T, 0 ≤ b i ∧ |t| * b i ≤ 1)
    (hflip : ∀ i ∈ T, ∀ S ⊆ T, i ∉ S → |g (insert i S) - g S| ≤ b i) :
    markProb p T (fun S => a ≤ t * (g S - markAvg p T g)) ≤
      Real.exp ((∑ i ∈ T, p i * (t * b i)^2) - a) := by
  classical
  rw [markProb]
  have hcomp : (Real.exp a) *
      markAvg p T (fun S => if a ≤ t * (g S - markAvg p T g) then 1 else 0) ≤
      markAvg p T (fun S => Real.exp (t * (g S - markAvg p T g))) := by
    rw [← markAvg_mul]
    apply markAvg_mono p T hp
    intro S _
    split_ifs with h
    · simpa only [mul_one] using Real.exp_le_exp.mpr h
    · simpa only [mul_zero] using Real.exp_nonneg _
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos a), mul_comm _ (Real.exp a)]
  exact hcomp.trans (markAvg_exp_centered p b T g t hp hb hflip)

theorem markAvg_mul_disjoint (p : I → ℝ) (T U V : Finset I) (hUV : Disjoint U V)
    (f g : Finset I → ℝ) :
    markAvg p T (fun S => f (S ∩ U) * g (S ∩ V)) =
      markAvg p T (fun S => f (S ∩ U)) * markAvg p T (fun S => g (S ∩ V)) := by
  induction T using Finset.induction_on generalizing f g with
  | empty => simp [markAvg, markWeight]
  | insert i T hi ih =>
    simp only [markAvg_insert p T _ hi]
    by_cases hU : i ∈ U
    · have hV : i ∉ V := fun hV => Finset.disjoint_left.mp hUV hU hV
      simp only [insert_inter_of_mem hU, insert_inter_of_notMem hV, ih,
        ih (fun S => f (insert i S)) g]
      ring
    · by_cases hV : i ∈ V
      · simp only [insert_inter_of_notMem hU, insert_inter_of_mem hV, ih,
          ih f (fun S => g (insert i S))]
        ring
      · simp only [insert_inter_of_notMem hU, insert_inter_of_notMem hV, ih]
        ring

theorem markProb_and_disjoint (p : I → ℝ) (T U V : Finset I) (hUV : Disjoint U V)
    (A B : Finset I → Prop) :
    markProb p T (fun S => A (S ∩ U) ∧ B (S ∩ V)) =
      markProb p T (fun S => A (S ∩ U)) * markProb p T (fun S => B (S ∩ V)) := by
  classical
  unfold markProb
  rw [← markAvg_mul_disjoint p T U V hUV (fun S => if A S then 1 else 0)
    (fun S => if B S then 1 else 0)]
  congr 1
  funext S
  by_cases hA : A (S ∩ U) <;> by_cases hB : B (S ∩ V) <;> simp [hA, hB]

theorem markProb_congr (p : I → ℝ) (T : Finset I) {A B : Finset I → Prop}
    (h : ∀ S ⊆ T, A S ↔ B S) : markProb p T A = markProb p T B := by
  classical
  unfold markProb markAvg
  exact sum_congr rfl (fun S hS => by simp only [h S (mem_powerset.mp hS)])

theorem markProb_mono (p : I → ℝ) (T : Finset I) {A B : Finset I → Prop}
    (hp : ∀ i ∈ T, 0 ≤ p i ∧ p i ≤ 1) (h : ∀ S ⊆ T, A S → B S) :
    markProb p T A ≤ markProb p T B := by
  classical
  apply markAvg_mono p T hp
  intro S hS
  by_cases hA : A S
  · simp [hA, h S hS hA]
  · by_cases hB : B S <;> simp [hA, hB]

theorem markProb_partition (p : I → ℝ) (T : Finset I) (A B : Finset I → Prop) :
    markProb p T (fun S => A S ∧ B S) + markProb p T (fun S => A S ∧ ¬ B S) =
      markProb p T A := by
  classical
  unfold markProb markAvg
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro S hS
  by_cases hA : A S <;> by_cases hB : B S <;> simp [hA, hB]

theorem markProb_true (p : I → ℝ) (T : Finset I) :
    markProb p T (fun _ => True) = 1 := by
  simpa [markProb] using markAvg_const p T 1

theorem exists_of_markProb_pos (p : I → ℝ) (T : Finset I) (A : Finset I → Prop)
    (h : 0 < markProb p T A) : ∃ S ⊆ T, A S := by
  classical
  by_contra hn
  push Not at hn
  have hz : markProb p T A = 0 := by
    rw [markProb_congr p T (B := fun _ => False) (fun S hS => iff_false_intro (hn S hS))]
    simpa [markProb] using markAvg_const p T 0
  linarith

/-- Symmetric local lemma for events supported on sets of independent marks. -/
theorem exists_avoid_marks {J : Type} [DecidableEq J] (p : I → ℝ) (T : Finset I)
    (hp : ∀ i ∈ T, 0 ≤ p i ∧ p i ≤ 1) (J₀ : Finset J) (U : J → Finset I)
    (bad : J → Finset I → Prop) (N : ℕ) {x : ℝ} (hx : 0 < x) (hx' : x < 1)
    (hlocal : ∀ j ∈ J₀, ∀ S, bad j S ↔ bad j (S ∩ U j))
    (hcount : ∀ j ∈ J₀, ((J₀.erase j).filter (fun k => ¬ Disjoint (U j) (U k))).card ≤ N)
    (hprob : ∀ j ∈ J₀, markProb p T (bad j) ≤ x * (1 - x)^N) :
    ∃ S ⊆ T, ∀ j ∈ J₀, ¬ bad j S := by
  classical
  let P := markProb p T
  let avoid (A : Finset J) (S : Finset I) := ∀ j ∈ A, ¬ bad j S
  have hbase : P (avoid ∅) = 1 := by
    rw [show avoid ∅ = fun _ => True by ext S; simp [avoid]]
    exact markProb_true p T
  have hstep (A : Finset J) (j : J) :
      P (fun S => avoid A S ∧ bad j S) + P (avoid (insert j A)) = P (avoid A) := by
    rw [show avoid (insert j A) = (fun S => avoid A S ∧ ¬ bad j S) by
      ext S
      simp [avoid, forall_mem_insert, and_comm]]
    exact markProb_partition p T (avoid A) (bad j)
  have havpos (A : Finset J) (hA : A ⊆ J₀)
      (hcond : ∀ B ⊂ A, ∀ j ∈ J₀, j ∉ B → P (fun S => avoid B S ∧ bad j S) ≤ x * P (avoid B)) :
      0 < P (avoid A) := by
    induction A using Finset.induction_on with
    | empty => simpa [hbase]
    | insert j B hj ih =>
      have hB : B ⊂ insert j B := Finset.ssubset_insert hj
      have hjJ := hA (mem_insert_self j B)
      have hBpos := ih (hB.subset.trans hA) (fun C hC => hcond C (hC.trans hB))
      have hn := hcond B hB j hjJ hj
      have hs := hstep B j
      have hm : 0 < (1-x) * P (avoid B) := mul_pos (sub_pos.mpr hx') hBpos
      linarith
  have hcond : ∀ A ⊆ J₀, ∀ j ∈ J₀, j ∉ A → P (fun S => avoid A S ∧ bad j S) ≤ x * P (avoid A) := by
    intro A
    induction A using Finset.strongInductionOn with
    | _ A ih =>
      intro hA j hj hjA
      let B := A.filter (fun k => ¬ Disjoint (U j) (U k))
      let C := A \ B
      have hBA : B ⊆ A := filter_subset _ _
      have hCA : C ⊆ A := sdiff_subset
      have hBC : B ∪ C = A := Finset.union_sdiff_of_subset hBA
      have hdisj : Disjoint B C := Finset.disjoint_sdiff
      have hpC : 0 ≤ P (avoid C) := by
        apply le_of_lt
        apply havpos C (hCA.trans hA)
        intro S hS
        exact ih S (hS.trans_le hCA) (hS.subset.trans (hCA.trans hA))
      have hN : B.card ≤ N := by
        apply (Finset.card_le_card (t := (J₀.erase j).filter (fun k => ¬ Disjoint (U j) (U k))) ?_).trans (hcount j hj)
        intro k hk
        obtain ⟨hkA, hkdep⟩ := mem_filter.mp hk
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨fun h => hjA (h ▸ hkA), hA hkA⟩, hkdep⟩
      have hUC : Disjoint (C.biUnion U) (U j) := by
        rw [Finset.disjoint_left]
        intro i hi hij
        obtain ⟨k, hk, hik⟩ := mem_biUnion.mp hi
        have hkB := (mem_sdiff.mp hk).2
        exact hkB (mem_filter.mpr ⟨hCA hk, by
          intro h
          exact Finset.disjoint_left.mp h hij hik⟩)
      have hlocalC (S : Finset I) : avoid C S ↔ avoid C (S ∩ C.biUnion U) := by
        apply forall₂_congr
        intro k hk
        have hsub : U k ⊆ C.biUnion U := fun i hi => mem_biUnion.mpr ⟨k, hk, hi⟩
        rw [hlocal k (hA (hCA hk)) S, hlocal k (hA (hCA hk)) (S ∩ C.biUnion U),
          inter_assoc, inter_eq_right.mpr hsub]
      have hfactor : P (fun S => avoid C S ∧ bad j S) = P (avoid C) * P (bad j) := by
        calc
          _ = P (fun S => avoid C (S ∩ C.biUnion U) ∧ bad j (S ∩ U j)) :=
            markProb_congr p T (fun S _ => (hlocalC S).and (hlocal j hj S))
          _ = P (fun S => avoid C (S ∩ C.biUnion U)) * P (fun S => bad j (S ∩ U j)) :=
            markProb_and_disjoint p T _ _ hUC (avoid C) (bad j)
          _ = _ := by
            dsimp only [P]
            rw [markProb_congr p T (fun S _ => (hlocalC S).symm),
              markProb_congr p T (fun S _ => (hlocal j hj S).symm)]
      have hprod : ∀ K ⊆ B, (1 - x)^K.card * P (avoid C) ≤ P (avoid (K ∪ C)) := by
        intro K
        induction K using Finset.induction_on with
        | empty => simp
        | insert k K hk ihK =>
          intro hkB
          have hk' : k ∈ B := hkB (mem_insert_self k K)
          have hKB : K ⊆ B := (subset_insert _ _).trans hkB
          have hkC : k ∉ C := fun h => Finset.disjoint_left.mp hdisj hk' h
          have hkn : k ∉ K ∪ C := by simp [hk, hkC]
          have hstrict : K ∪ C ⊂ A := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨union_subset (hKB.trans hBA) hCA, ?_⟩
            intro he
            exact hkn (he ▸ hBA hk')
          have hn := ih (K ∪ C) hstrict (hstrict.subset.trans hA) k (hA (hBA hk')) hkn
          have hs := hstep (K ∪ C) k
          have hpeel : (1 - x) * P (avoid (K ∪ C)) ≤ P (avoid (insert k (K ∪ C))) := by linarith
          rw [card_insert_of_notMem hk, pow_succ, mul_comm ((1-x)^K.card), mul_assoc, insert_union]
          exact (mul_le_mul_of_nonneg_left (ihK hKB) (sub_nonneg.mpr hx'.le)).trans hpeel
      have hpow : (1 - x)^N ≤ (1 - x)^B.card :=
        pow_le_pow_of_le_one (sub_nonneg.mpr hx'.le) (by linarith) hN
      calc
        _ ≤ P (fun S => avoid C S ∧ bad j S) :=
          markProb_mono p T hp (fun S _ hs => ⟨fun k hk => hs.1 k (hCA hk), hs.2⟩)
        _ = P (avoid C) * P (bad j) := hfactor
        _ ≤ P (avoid C) * (x * (1 - x)^N) := mul_le_mul_of_nonneg_left (hprob j hj) hpC
        _ ≤ x * ((1 - x)^B.card * P (avoid C)) := by
          rw [mul_left_comm, mul_comm (P (avoid C))]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hpC) hx.le
        _ ≤ _ := mul_le_mul_of_nonneg_left (hBC ▸ hprod B (Subset.refl B)) hx.le
  exact exists_of_markProb_pos p T (avoid J₀)
    (havpos J₀ (Subset.refl J₀) (fun A hA => hcond A hA.subset))

theorem markAvg_congr {p : I → ℝ} {T : Finset I} {f g : Finset I → ℝ}
    (h : ∀ S ⊆ T, f S = g S) : markAvg p T f = markAvg p T g :=
  sum_congr rfl (fun S hS => congrArg (markWeight p T S * ·) (h S (mem_powerset.mp hS)))

theorem markProb_pattern (p : I → ℝ) (T U : Finset I) (hU : U ⊆ T) (w : I → Bool) :
    markProb p T (fun S => ∀ i ∈ U, i ∈ S ↔ w i = true) =
      ∏ i ∈ U, if w i then p i else 1 - p i := by
  classical
  induction T using Finset.induction_on generalizing U with
  | empty =>
    have he : U = ∅ := subset_empty.mp hU
    simp [he, markProb_true]
  | insert i T hi ih =>
    let event (U S : Finset I) := ∀ j ∈ U, j ∈ S ↔ w j = true
    let f (U S : Finset I) : ℝ := @ite ℝ (event U S) (Classical.propDecidable _) 1 0
    change markAvg p (insert i T) (f U) = _
    rw [markAvg_insert p T _ hi]
    by_cases hui : i ∈ U
    · let U' := U.erase i
      have hsub : U' ⊆ T := by
        intro j hj
        exact (mem_insert.mp (hU (mem_erase.mp hj).2)).resolve_left (mem_erase.mp hj).1
      have hprod : (∏ j ∈ U, if w j then p j else 1 - p j) =
          (if w i then p i else 1 - p i) * ∏ j ∈ U', if w j then p j else 1 - p j := by
        conv_lhs => rw [← insert_erase hui]
        exact prod_insert (notMem_erase _ _)
      -- The two assignments to the distinguished mark agree on every other index.
      have hother (S : Finset I) : event U' (insert i S) ↔ event U' S := by
        apply forall₂_congr
        intro j hj
        simp [(mem_erase.mp hj).1]
      have hfirst : markAvg p T (f U) =
          if w i then 0 else markAvg p T (f U') := by
        cases hwi : w i
        · simp only [Bool.false_eq_true, if_false]
          apply markAvg_congr
          intro S hS
          have his : i ∉ S := fun h => hi (hS h)
          have he : event U S ↔ event U' S := by
            conv_lhs => rw [show U = insert i U' from (insert_erase hui).symm]
            simp [event, forall_mem_insert, his, hwi]
          simp [f, he]
        · simp only [if_true]
          rw [← markAvg_const p T 0]
          apply markAvg_congr
          intro S hS
          have hn : ¬ event U S := fun h => hi (hS ((h i hui).mpr hwi))
          simp [f, hn]
      have hnext : markAvg p T (fun S => f U (insert i S)) =
          if w i then markAvg p T (f U') else 0 := by
        cases hwi : w i
        · simp only [Bool.false_eq_true, if_false]
          rw [← markAvg_const p T 0]
          apply markAvg_congr
          intro S hS
          have hn : ¬ event U (insert i S) := by
            intro h
            have := (h i hui).mp (mem_insert_self i S)
            simp [hwi] at this
          simp [f, hn]
        · simp only [if_true]
          apply markAvg_congr
          intro S hS
          have he : event U (insert i S) ↔ event U' S := by
            calc
              event U (insert i S) ↔ event U' (insert i S) := by
                conv_lhs => rw [show U = insert i U' from (insert_erase hui).symm]
                simp [event, forall_mem_insert, hwi]
              _ ↔ _ := hother S
          simp [f, he]
      have hind : markAvg p T (f U') = ∏ j ∈ U', if w j then p j else 1 - p j := ih U' hsub
      rw [hprod, hfirst, hnext, hind]
      cases w i <;> simp
    · have hsub : U ⊆ T := by
        intro j hj
        exact (mem_insert.mp (hU hj)).resolve_left (fun h => hui (h ▸ hj))
      have hupdate : (fun S => f U (insert i S)) = f U := by
        funext S
        have he : event U (insert i S) ↔ event U S := by
          apply forall₂_congr
          intro j hj
          have hji : j ≠ i := fun h => hui (h ▸ hj)
          simp [hji]
        simp [f, he]
      rw [hupdate, show
        (1 - p i) * markAvg p T (f U) + p i * markAvg p T (f U) = markAvg p T (f U) by ring]
      exact ih U hsub

theorem markAvg_empty (p : I → ℝ) (g : Finset I → ℝ) : markAvg p ∅ g = g ∅ := by
  simp [markAvg, markWeight]

theorem markAvg_add (p : I → ℝ) (T : Finset I) (f g : Finset I → ℝ) :
    markAvg p T (fun S => f S + g S) = markAvg p T f + markAvg p T g := by
  simp only [markAvg, mul_add, sum_add_distrib]

/-- Two-stage exposure: averaging over the marks in a disjoint union is an iterated average. -/
theorem markAvg_union (p : I → ℝ) (U V : Finset I) (hUV : Disjoint U V) (g : Finset I → ℝ) :
    markAvg p (U ∪ V) g =
      markAvg p U (fun S₁ => markAvg p V (fun S₂ => g (S₁ ∪ S₂))) := by
  induction V using Finset.induction_on generalizing g with
  | empty => simp [markAvg_empty]
  | insert i V hi ih =>
    have hiU : i ∉ U := fun h => (Finset.disjoint_left.mp hUV h) (mem_insert_self i V)
    have hUV' : Disjoint U V := hUV.mono_right (subset_insert i V)
    have hiUV : i ∉ U ∪ V := by simp [hiU, hi]
    have hfun : (fun S₁ => markAvg p (insert i V) (fun S₂ => g (S₁ ∪ S₂))) =
        fun S₁ => (1 - p i) * markAvg p V (fun S₂ => g (S₁ ∪ S₂)) +
          p i * markAvg p V (fun S₂ => g (insert i (S₁ ∪ S₂))) := by
      funext S₁
      rw [markAvg_insert p V _ hi]
      simp only [union_insert]
    rw [union_insert, markAvg_insert p (U ∪ V) g hiUV, ih hUV' g,
      ih hUV' (fun S => g (insert i S)), hfun, markAvg_add, markAvg_mul, markAvg_mul]

theorem markProb_le_one (p : I → ℝ) (T : Finset I) (hp : ∀ i ∈ T, 0 ≤ p i ∧ p i ≤ 1)
    (A : Finset I → Prop) : markProb p T A ≤ 1 :=
  (markProb_mono p T hp (fun _ _ _ => trivial)).trans_eq (markProb_true p T)

theorem markProb_union (p : I → ℝ) (U V : Finset I) (hUV : Disjoint U V)
    (A : Finset I → Prop) :
    markProb p (U ∪ V) A = markAvg p U (fun S₁ => markProb p V (fun S₂ => A (S₁ ∪ S₂))) := by
  classical
  simp only [markProb]
  exact markAvg_union p U V hUV _

/-- Conditional (two-stage) bound: if the first-stage marks are good outside a small
event, and every good first stage makes the second-stage event unlikely, the whole event
is unlikely. -/
theorem markProb_two_stage (p : I → ℝ) (U V : Finset I) (hUV : Disjoint U V)
    (hpU : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (hpV : ∀ i ∈ V, 0 ≤ p i ∧ p i ≤ 1)
    (A G : Finset I → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hcond : ∀ S₁ ⊆ U, G S₁ → markProb p V (fun S₂ => A (S₁ ∪ S₂)) ≤ ε) :
    markProb p (U ∪ V) A ≤ markProb p U (fun S₁ => ¬ G S₁) + ε := by
  classical
  rw [markProb_union p U V hUV A]
  have hle : markAvg p U (fun S₁ => markProb p V (fun S₂ => A (S₁ ∪ S₂))) ≤
      markAvg p U (fun S₁ => (if ¬ G S₁ then (1 : ℝ) else 0) + ε) := by
    apply markAvg_mono p U hpU
    intro S₁ hS₁
    by_cases hG : G S₁
    · simpa [hG] using hcond S₁ hS₁ hG
    · have h1 := markProb_le_one p V hpV (fun S₂ => A (S₁ ∪ S₂))
      simp only [hG, not_false_eq_true, if_true]
      linarith
  refine hle.trans_eq ?_
  rw [markAvg_add, markAvg_const]
  congr 1
  unfold markProb
  apply markAvg_congr
  intro S _
  by_cases h : G S <;> simp [h]

/-- Union bound for two events. -/
theorem markProb_or_le (p : I → ℝ) (T : Finset I) (hp : ∀ i ∈ T, 0 ≤ p i ∧ p i ≤ 1)
    (A B : Finset I → Prop) :
    markProb p T (fun S => A S ∨ B S) ≤ markProb p T A + markProb p T B := by
  classical
  unfold markProb
  rw [← markAvg_add]
  apply markAvg_mono p T hp
  intro S _
  by_cases hA : A S <;> by_cases hB : B S <;> simp [hA, hB]

/-- Union bound over a finite family of events. -/
theorem markProb_exists_le {J : Type} [DecidableEq J] (p : I → ℝ) (T : Finset I)
    (hp : ∀ i ∈ T, 0 ≤ p i ∧ p i ≤ 1) (J₀ : Finset J) (A : J → Finset I → Prop) :
    markProb p T (fun S => ∃ j ∈ J₀, A j S) ≤ ∑ j ∈ J₀, markProb p T (A j) := by
  classical
  induction J₀ using Finset.induction_on with
  | empty => simp [markProb, markAvg_const]
  | insert j J₀ hj ih =>
    rw [sum_insert hj, markProb_congr p T (B := fun S => A j S ∨ ∃ k ∈ J₀, A k S)
      (fun S _ => exists_mem_insert j J₀ (fun k => A k S))]
    exact (markProb_or_le p T hp _ _).trans (by linarith)

end Bernoulli

end OMAH1

theorem OMA.solution : OMA.R_Erdos19_erdos_19_variants_kahn_R1.H1 := by
  unfold OMA.R_Erdos19_erdos_19_variants_kahn_R1.H1
  intro q hq
  rcases Nat.lt_or_ge q 2 with h | h
  · have : q = 1 := by omega
    subst this
    exact OMAH1.case_one
  · apply OMAH1.case_of_matching q
    sorry
