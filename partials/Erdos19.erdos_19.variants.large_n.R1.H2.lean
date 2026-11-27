import OMAReductions.R_Erdos19_erdos_19_variants_large_n_R1

-- Step Erdos19.erdos_19.variants.large_n.R1.H2: hypothesis H2 of reduction Erdos19.erdos_19.variants.large_n.R1
-- Credit: @<handle>
-- H2 := ∀ᶠ n in Filter.atTop, ∀ K : Finset (Finset (Fin n)),     (∀ A ∈ K, 2 ≤ A.card) → (∃ A ∈ K, n < A.card * A.card) →     (∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A) →     ∃ c : {x // x ∈ K} → Fin n, ∀ A B : {x // x ∈ K}, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

namespace OMA19H2

/-- In a pairwise balanced design two distinct blocks share at most one point. -/
theorem inter_card_le_one {n : ℕ} (K : Finset (Finset (Fin n)))
    (hK : ∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A)
    {A B : Finset (Fin n)} (hA : A ∈ K) (hB : B ∈ K) (hAB : A ≠ B) :
    (A ∩ B).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  by_contra hij
  rw [Finset.mem_inter] at hi hj
  obtain ⟨C, _, hC⟩ := hK i j hij
  have h1 := hC A ⟨hA, hi.1, hj.1⟩
  have h2 := hC B ⟨hB, hi.2, hj.2⟩
  exact hAB (h1.trans h2.symm)

open Finset
open scoped BigOperators

/-- A neighboring block contributes one pair for every one of its points outside A. -/
theorem neighbor_rank_sum_eq {n : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    {A : Finset (Fin n)} (hA : A ∈ K) :
    ∑ B ∈ (K.erase A).filter (fun B => (A ∩ B).Nonempty), (B.card - 1) =
      A.card * (n - A.card) := by
  classical
  let through (i : Fin n) := (K.erase A).filter (fun B => i ∈ B)
  have hmem {i : Fin n} {B : Finset (Fin n)} (hB : B ∈ through i) :
      B ≠ A ∧ B ∈ K ∧ i ∈ B := by
    have ⟨hB', hi⟩ := mem_filter.mp hB
    have ⟨hne, hBK⟩ := mem_erase.mp hB'
    exact ⟨hne, hBK, hi⟩
  have hdis : (A : Set (Fin n)).PairwiseDisjoint through := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro B hiB hjB
    have ⟨hne, hBK, hi'⟩ := hmem hiB
    have hj' := (hmem hjB).2.2
    exact hij (card_le_one.mp (inter_card_le_one K hK hA hBK hne.symm) i
      (mem_inter.mpr ⟨hi, hi'⟩) j (mem_inter.mpr ⟨hj, hj'⟩))
  have hneighbors : (K.erase A).filter (fun B => (A ∩ B).Nonempty) =
      A.biUnion through := by
    ext B
    constructor
    · intro hB
      obtain ⟨hBK, i, hi⟩ := mem_filter.mp hB
      obtain ⟨hiA, hiB⟩ := mem_inter.mp hi
      exact mem_biUnion.mpr ⟨i, hiA, mem_filter.mpr ⟨hBK, hiB⟩⟩
    · intro hB
      obtain ⟨i, hiA, hBi⟩ := mem_biUnion.mp hB
      obtain ⟨hBK, hiB⟩ := mem_filter.mp hBi
      exact mem_filter.mpr ⟨hBK, i, mem_inter.mpr ⟨hiA, hiB⟩⟩
  have hpoint (i : Fin n) (hi : i ∈ A) :
      ∑ B ∈ through i, (B.card - 1) = n - A.card := by
    have hsizes {B : Finset (Fin n)} (hB : B ∈ through i) :
        B.card - 1 = (B \ A).card := by
      have ⟨hne, hBK, hiB⟩ := hmem hB
      have hcard : (A ∩ B).card = 1 := by
        have hpos := card_pos.mpr ⟨i, mem_inter.mpr ⟨hi, hiB⟩⟩
        have hle := inter_card_le_one K hK hA hBK hne.symm
        omega
      rw [card_sdiff, hcard]
    have hparts : (through i : Set (Finset (Fin n))).PairwiseDisjoint (fun B => B \ A) := by
      intro B hB C hC hne
      apply disjoint_left.mpr
      intro j hjB hjC
      obtain ⟨hjB', hjA⟩ := mem_sdiff.mp hjB
      have ⟨_, hBK, hiB⟩ := hmem hB
      have ⟨_, hCK, hiC⟩ := hmem hC
      have hji := card_le_one.mp (inter_card_le_one K hK hBK hCK hne) j
        (mem_inter.mpr ⟨hjB', (mem_sdiff.mp hjC).1⟩) i (mem_inter.mpr ⟨hiB, hiC⟩)
      exact hjA (hji ▸ hi)
    have hcover : (through i).biUnion (fun B => B \ A) = Aᶜ := by
      ext j
      constructor
      · intro hj
        obtain ⟨B, _, hjB⟩ := mem_biUnion.mp hj
        exact mem_compl.mpr (mem_sdiff.mp hjB).2
      · intro hj
        have hjA := mem_compl.mp hj
        have hij : i ≠ j := fun he => hjA (he ▸ hi)
        obtain ⟨B, ⟨hBK, hiB, hjB⟩, _⟩ := hK i j hij
        have hne : B ≠ A := fun he => hjA (he ▸ hjB)
        exact mem_biUnion.mpr ⟨B, mem_filter.mpr ⟨mem_erase.mpr ⟨hne, hBK⟩, hiB⟩,
          mem_sdiff.mpr ⟨hjB, hjA⟩⟩
    calc
      _ = ∑ B ∈ through i, (B \ A).card := sum_congr rfl fun _ hB => hsizes hB
      _ = ((through i).biUnion (fun B => B \ A)).card := (card_biUnion hparts).symm
      _ = _ := by rw [hcover, card_compl, Fintype.card_fin]
  rw [hneighbors, sum_biUnion hdis]
  calc
    _ = ∑ _i ∈ A, (n - A.card) := sum_congr rfl hpoint
    _ = _ := by simp

/-- A block of rank above the square root has fewer than n neighbors of at least its rank. -/
theorem fewer_than_n_neighbors_of_ge_rank {n : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    {A : Finset (Fin n)} (hA : A ∈ K) (hs : 2 ≤ A.card)
    (hbig : n < A.card * A.card) :
    ((K.erase A).filter (fun B => (A ∩ B).Nonempty ∧ A.card ≤ B.card)).card < n := by
  classical
  let N := (K.erase A).filter (fun B => (A ∩ B).Nonempty ∧ A.card ≤ B.card)
  have hsub : N ⊆ (K.erase A).filter (fun B => (A ∩ B).Nonempty) := by
    intro B hB
    obtain ⟨hm, hi, _⟩ := mem_filter.mp hB
    exact mem_filter.mpr ⟨hm, hi⟩
  have hweight : N.card * (A.card - 1) ≤ A.card * (n - A.card) := calc
    _ = ∑ _B ∈ N, (A.card - 1) := by simp
    _ ≤ ∑ B ∈ N, (B.card - 1) :=
      sum_le_sum fun _ hB => Nat.sub_le_sub_right (mem_filter.mp hB).2.2 1
    _ ≤ ∑ B ∈ (K.erase A).filter (fun B => (A ∩ B).Nonempty), (B.card - 1) :=
      sum_le_sum_of_subset hsub
    _ = _ := neighbor_rank_sum_eq hK hA
  have hlt : A.card * (n - A.card) < n * (A.card - 1) := by
    have hAn : A.card ≤ n := by simpa using card_le_univ A
    have hleft : A.card * (n - A.card) + A.card * A.card = n * A.card := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hAn, Nat.mul_comm]
    have hright : n * (A.card - 1) + n = n * A.card := by
      calc
        _ = n * (A.card - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = _ := by rw [Nat.sub_add_cancel (show 1 ≤ A.card by omega)]
    omega
  exact lt_of_not_ge fun h => (not_le_of_gt hlt) ((Nat.mul_le_mul_right _ h).trans hweight)

/-- Disjoint blocks have a distinct joining block for each pair across them. -/
theorem cross_pairs_le_neighbors {n : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    {A L : Finset (Fin n)} (hA : A ∈ K) (hL : L ∈ K) (hd : Disjoint A L) :
    A.card * L.card ≤ ((K.erase A).filter (fun B => (A ∩ B).Nonempty)).card := by
  classical
  let N := (K.erase A).filter (fun B => (A ∩ B).Nonempty)
  have hex (p : A × L) : ∃ B ∈ N, p.1.val ∈ B ∧ p.2.val ∈ B := by
    have hne : p.1.val ≠ p.2.val := fun he =>
      disjoint_left.mp hd (he ▸ p.1.property) p.2.property
    obtain ⟨B, ⟨hBK, hpA, hpL⟩, _⟩ := hK p.1.val p.2.val hne
    have hBA : B ≠ A := fun he => disjoint_left.mp hd (he ▸ hpL) p.2.property
    exact ⟨B, mem_filter.mpr ⟨mem_erase.mpr ⟨hBA, hBK⟩,
      p.1.val, mem_inter.mpr ⟨p.1.property, hpA⟩⟩, hpA, hpL⟩
  choose f hf hfirst hsecond using hex
  let join (p : A × L) : N := ⟨f p, hf p⟩
  have hinj : Function.Injective join := by
    intro p q he
    have hsame : f p = f q := congrArg Subtype.val he
    obtain ⟨hneA, hfK⟩ := mem_erase.mp (mem_filter.mp (hf p)).1
    have hneL : f p ≠ L := by
      intro heL
      have hp := hfirst p
      rw [heL] at hp
      exact disjoint_left.mp hd p.1.property hp
    apply Prod.ext
    · apply Subtype.ext
      exact card_le_one.mp (inter_card_le_one K hK hA hfK hneA.symm) _
        (mem_inter.mpr ⟨p.1.property, hfirst p⟩) _
        (mem_inter.mpr ⟨q.1.property, hsame.symm ▸ hfirst q⟩)
    · apply Subtype.ext
      exact card_le_one.mp (inter_card_le_one K hK hL hfK hneL.symm) _
        (mem_inter.mpr ⟨p.2.property, hsecond p⟩) _
        (mem_inter.mpr ⟨q.2.property, hsame.symm ▸ hsecond q⟩)
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective join hinj

/-- The square-root boundary for a minimum-rank block is impossible in the presence
of a large block in the ambient design. -/
theorem min_rank_sq_lt_of_large_block {n : ℕ} {K S : Finset (Finset (Fin n))}
    (hsize : ∀ B ∈ K, 2 ≤ B.card)
    (hK : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hSK : S ⊆ K) {A L : Finset (Fin n)} (hA : A ∈ S) (hL : L ∈ K)
    (hlarge : n < L.card * L.card) (hmin : ∀ B ∈ S, A.card ≤ B.card)
    (hdegree : n ≤ ((S.erase A).filter (fun B => (A ∩ B).Nonempty)).card) :
    A.card * A.card < n := by
  classical
  let T := (S.erase A).filter (fun B => (A ∩ B).Nonempty)
  let N := (K.erase A).filter (fun B => (A ∩ B).Nonempty)
  have hAK := hSK hA
  have hs := hsize A hAK
  have hsubRank : T ⊆ (K.erase A).filter (fun B => (A ∩ B).Nonempty ∧ A.card ≤ B.card) := by
    intro B hB
    obtain ⟨hE, hmeet⟩ := mem_filter.mp hB
    obtain ⟨hne, hBS⟩ := mem_erase.mp hE
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨hne, hSK hBS⟩, hmeet, hmin B hBS⟩
  have hle : A.card * A.card ≤ n := by
    by_contra! hgt
    exact (not_le_of_gt (fewer_than_n_neighbors_of_ge_rank hK hAK hs hgt))
      (hdegree.trans (card_le_card hsubRank))
  apply lt_of_le_of_ne hle
  intro heq
  have hsub : T ⊆ N := by
    intro B hB
    obtain ⟨hE, hmeet, _⟩ := mem_filter.mp (hsubRank hB)
    exact mem_filter.mpr ⟨hE, hmeet⟩
  have hmono : ∀ B ∈ T, A.card - 1 ≤ B.card - 1 := by
    intro B hB
    exact Nat.sub_le_sub_right (mem_filter.mp (hsubRank hB)).2.2 _
  have hsumN : ∑ B ∈ N, (B.card - 1) = n * (A.card - 1) := by
    rw [show _ = A.card * (n - A.card) from neighbor_rank_sum_eq hK hAK]
    have hsub' : n - A.card = A.card * (A.card - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, heq]
    rw [hsub', ← Nat.mul_assoc, heq]
  have hlo : n * (A.card - 1) ≤ ∑ _B ∈ T, (A.card - 1) := by
    rw [sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hdegree
  have hweight := sum_le_sum hmono
  have hsubsum : ∑ B ∈ T, (B.card - 1) ≤ ∑ B ∈ N, (B.card - 1) :=
    sum_le_sum_of_subset hsub
  have hTN : T = N := by
    apply hsub.antisymm
    intro B hB
    by_contra hBT
    have hBsize := hsize B (mem_erase.mp (mem_filter.mp hB).1).2
    have hlt := sum_lt_sum_of_subset hsub hB hBT (by omega : 0 < B.card - 1)
      (fun C _ _ => Nat.zero_le (C.card - 1))
    exact (not_lt_of_ge (hsumN.le.trans (hlo.trans hweight))) hlt
  have hsame : ∀ B ∈ N, B.card = A.card := by
    rw [← hTN]
    intro B hB
    have hAB := (mem_filter.mp (hsubRank hB)).2.2
    by_contra hne
    have hlt := sum_lt_sum hmono ⟨B, hB, (by omega : A.card - 1 < B.card - 1)⟩
    exact (not_lt_of_ge ((hsubsum.trans_eq hsumN).trans hlo)) hlt
  have hcard : N.card = n := by
    have hmul : N.card * (A.card - 1) = n * (A.card - 1) := calc
      _ = ∑ _B ∈ N, (A.card - 1) := by simp
      _ = ∑ B ∈ N, (B.card - 1) := sum_congr rfl fun B hB => by rw [hsame B hB]
      _ = _ := hsumN
    exact Nat.mul_right_cancel (by omega : 0 < A.card - 1) hmul
  have hAL : A.card < L.card := by
    by_contra! hn
    exact (not_lt_of_ge ((Nat.mul_le_mul hn hn).trans_eq heq)) hlarge
  have hne : L ≠ A := fun h => (ne_of_gt hAL) (congrArg Finset.card h)
  have hd : Disjoint A L := by
    by_contra h
    have hLN : L ∈ N := mem_filter.mpr
      ⟨mem_erase.mpr ⟨hne, hL⟩, not_disjoint_iff_nonempty_inter.mp h⟩
    exact (ne_of_gt hAL) (hsame L hLN)
  have hprod := cross_pairs_le_neighbors hK hAK hL hd
  change A.card * L.card ≤ N.card at hprod
  have hprod' := hprod.trans_eq (hcard.trans heq.symm)
  exact (not_le_of_gt (Nat.mul_lt_mul_of_pos_left hAL (by omega))) hprod'

/-- Inserting a block with fewer than n neighbors preserves n-colorability. -/
theorem colorable_insert_of_lt {n : ℕ} {S : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    (hA : A ∉ S) (hcount : (S.filter (fun B => (A ∩ B).Nonempty)).card < n)
    (hS : ∃ c : Finset (Fin n) → Fin n,
      ∀ B ∈ S, ∀ D ∈ S, B ≠ D → (B ∩ D).Nonempty → c B ≠ c D) :
    ∃ c : Finset (Fin n) → Fin n,
      ∀ B ∈ insert A S, ∀ D ∈ insert A S, B ≠ D → (B ∩ D).Nonempty → c B ≠ c D := by
  classical
  obtain ⟨c, hc⟩ := hS
  let used := (S.filter (fun B => (A ∩ B).Nonempty)).image c
  have hused : used.card < (univ : Finset (Fin n)).card := by
    simpa using (card_image_le (f := c)).trans_lt hcount
  obtain ⟨w, _, hw⟩ := exists_mem_notMem_of_card_lt_card hused
  have hfresh {D : Finset (Fin n)} (hD : D ∈ S) (hAD : (A ∩ D).Nonempty) : w ≠ c D := by
    intro he
    apply hw
    rw [he]
    exact mem_image_of_mem c (mem_filter.mpr ⟨hD, hAD⟩)
  have hneA {D : Finset (Fin n)} (hD : D ∈ S) : D ≠ A := fun he => hA (he ▸ hD)
  refine ⟨Function.update c A w, ?_⟩
  intro B hB D hD hne hmeet
  rcases mem_insert.mp hB with hBA | hBS <;> rcases mem_insert.mp hD with hDA | hDS
  · exact (hne (hBA.trans hDA.symm)).elim
  · subst B
    simpa only [Function.update_self, Function.update_of_ne (hneA hDS)]
      using hfresh hDS hmeet
  · subst D
    rw [inter_comm] at hmeet
    simpa only [Function.update_self, Function.update_of_ne (hneA hBS)]
      using (hfresh hBS hmeet).symm
  · rw [Function.update_of_ne (hneA hBS), Function.update_of_ne (hneA hDS)]
    exact hc B hBS D hDS hne hmeet

/-- The large blocks of a pairwise balanced design admit a proper n-coloring. -/
theorem colorable_of_large_min_rank {n : ℕ} (hn : 0 < n)
    {K : Finset (Finset (Fin n))} (hsize : ∀ A ∈ K, 2 ≤ A.card)
    (hK : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B) :
    ∀ S : Finset (Finset (Fin n)), S ⊆ K → (∀ A ∈ S, n < A.card * A.card) →
      ∃ c : Finset (Fin n) → Fin n,
        ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  classical
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hSK hbig
    by_cases hS : S.Nonempty
    · obtain ⟨A, hA, hmin⟩ := S.exists_min_image Finset.card hS
      have hsub : (S.erase A).filter (fun B => (A ∩ B).Nonempty) ⊆
          (K.erase A).filter (fun B => (A ∩ B).Nonempty ∧ A.card ≤ B.card) := by
        intro B hB
        obtain ⟨hBerase, hmeet⟩ := mem_filter.mp hB
        obtain ⟨hne, hBS⟩ := mem_erase.mp hBerase
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨hne, hSK hBS⟩, hmeet, hmin B hBS⟩
      have hcount := (card_le_card hsub).trans_lt
        (fewer_than_n_neighbors_of_ge_rank hK (hSK hA) (hsize A (hSK hA)) (hbig A hA))
      have hrest := ih (S.erase A) (erase_ssubset hA)
        ((erase_subset A S).trans hSK) (fun B hB => hbig B (mem_of_mem_erase hB))
      simpa only [insert_erase hA] using colorable_insert_of_lt (notMem_erase A S) hcount hrest
    · exact ⟨fun _ => ⟨0, hn⟩, fun A hA => (hS ⟨A, hA⟩).elim⟩

/-- It suffices to color subfamilies in which each block meets at least n others. -/
theorem colorable_of_colorable_cores {n : ℕ} {K : Finset (Finset (Fin n))}
    (hcores : ∀ S ⊆ K,
      (∀ A ∈ S, n ≤ ((S.erase A).filter (fun B => (A ∩ B).Nonempty)).card) →
      ∃ c : Finset (Fin n) → Fin n,
        ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) :
    ∃ c : Finset (Fin n) → Fin n,
      ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  classical
  suffices h : ∀ S ⊆ K, ∃ c : Finset (Fin n) → Fin n,
      ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B from
    h K (fun _ hA => hA)
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hSK
    by_cases hdegree : ∀ A ∈ S, n ≤ ((S.erase A).filter (fun B => (A ∩ B).Nonempty)).card
    · exact hcores S hSK hdegree
    · push Not at hdegree
      obtain ⟨A, hA, hcount⟩ := hdegree
      have hrest := ih (S.erase A) (erase_ssubset hA) ((erase_subset A S).trans hSK)
      simpa only [insert_erase hA] using colorable_insert_of_lt (notMem_erase A S) hcount hrest

/-- Adjoin a block on the new points, then complete all uncovered pairs. -/
theorem exists_padded_design {m k : ℕ} (H : Finset (Finset (Fin m)))
    (hk : 2 ≤ k) (hsize : ∀ A ∈ H, 2 ≤ A.card)
    (hlin : ∀ ⦃A B⦄, A ∈ H → B ∈ H → ∀ ⦃i j : Fin m⦄,
      i ≠ j → i ∈ A → j ∈ A → i ∈ B → j ∈ B → A = B) :
    ∃ K : Finset (Finset (Fin (m + k))),
      (∀ A ∈ H, A.map (Fin.castAddEmb k) ∈ K) ∧
      (∃ L ∈ K, L.card = k) ∧
      (∀ A ∈ K, 2 ≤ A.card) ∧
      ∀ i j : Fin (m + k), i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A := by
  classical
  let e : Fin m ↪ Fin (m + k) := Fin.castAddEmb k
  let L := (univ : Finset (Fin k)).map (Fin.natAddEmb m)
  let J := insert L (H.image (Finset.map e))
  have hLcard : L.card = k := by simp [L]
  have hdisj {A : Finset (Fin m)} {x : Fin (m + k)}
      (hx : x ∈ A.map e) (hy : x ∈ L) : False := by
    obtain ⟨i, _, hi⟩ := mem_map.mp hx
    obtain ⟨j, _, hj⟩ := mem_map.mp hy
    have hi' : x.val = i.val := (congrArg Fin.val hi).symm
    have hj' : x.val = m + j.val := (congrArg Fin.val hj).symm
    omega
  have hJsize : ∀ A ∈ J, 2 ≤ A.card := by
    intro A hA
    rcases mem_insert.mp hA with rfl | hA
    · rwa [hLcard]
    · obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
      simpa only [card_map] using hsize B hB
  have hJlin : ∀ ⦃A B⦄, A ∈ J → B ∈ J → ∀ ⦃i j : Fin (m + k)⦄,
      i ≠ j → i ∈ A → j ∈ A → i ∈ B → j ∈ B → A = B := by
    intro A B hA hB i j hij hiA hjA hiB hjB
    rcases mem_insert.mp hA with rfl | hA <;> rcases mem_insert.mp hB with rfl | hB
    · rfl
    · obtain ⟨B, _, rfl⟩ := mem_image.mp hB
      exact (hdisj hiB hiA).elim
    · obtain ⟨A, _, rfl⟩ := mem_image.mp hA
      exact (hdisj hiA hiB).elim
    · obtain ⟨A, hAH, rfl⟩ := mem_image.mp hA
      obtain ⟨B, hBH, rfl⟩ := mem_image.mp hB
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hiA
      obtain ⟨b, hb, rfl⟩ := mem_map.mp hjA
      obtain ⟨a', ha', hea⟩ := mem_map.mp hiB
      obtain ⟨b', hb', heb⟩ := mem_map.mp hjB
      cases e.injective hea
      cases e.injective heb
      exact congrArg (Finset.map e) (hlin hAH hBH (fun h => hij (congrArg e h)) ha hb ha' hb')
  obtain ⟨K, hJK, hKsize, hKpairs⟩ :=
    OMA.R_Erdos19_erdos_19_variants_large_n_R1.exists_pairwiseBalanced_superset
      J hJsize hJlin
  exact ⟨K, fun A hA => hJK (mem_insert_of_mem (mem_image_of_mem _ hA)),
    ⟨L, hJK (mem_insert_self _ _), hLcard⟩, hKsize, hKpairs⟩

/-- H2 would give square-root additive slack for every sufficiently large linear family. -/
theorem eventually_color_with_sqrt_slack
    (h : OMA.R_Erdos19_erdos_19_variants_large_n_R1.H2) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ H : Finset (Finset (Fin m)),
      (∀ A ∈ H, 2 ≤ A.card) →
      (∀ ⦃A B⦄, A ∈ H → B ∈ H → ∀ ⦃i j : Fin m⦄,
        i ≠ j → i ∈ A → j ∈ A → i ∈ B → j ∈ B → A = B) →
      ∃ c : {A // A ∈ H} → Fin (m + (m.sqrt + 2)),
        ∀ A B : {A // A ∈ H}, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  classical
  rw [OMA.R_Erdos19_erdos_19_variants_large_n_R1.H2, Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  rw [Filter.eventually_atTop]
  refine ⟨N, fun m hm H hsize hlin => ?_⟩
  let k := m.sqrt + 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hmk : m + k < k * k := by
    have hs := Nat.lt_succ_sqrt m
    simp only [Nat.succ_eq_add_one] at hs
    dsimp [k]
    nlinarith
  obtain ⟨K, hHK, ⟨L, hL, hLcard⟩, hKsize, hKpairs⟩ :=
    exists_padded_design H hk hsize hlin
  obtain ⟨c, hc⟩ := hN (m + k) (by omega) K hKsize
    ⟨L, hL, by rwa [hLcard]⟩ hKpairs
  let liftBlock (A : H) : K := ⟨A.val.map (Fin.castAddEmb k), hHK _ A.property⟩
  refine ⟨fun A => c (liftBlock A), fun A B hAB hinter => hc _ _ ?_ ?_⟩
  · exact fun he => hAB (Subtype.ext
      (Finset.map_injective (Fin.castAddEmb k) (congrArg Subtype.val he)))
  · change (A.val.map _ ∩ B.val.map _).Nonempty
    rw [← Finset.map_inter, Finset.map_nonempty]
    exact hinter

end OMA19H2

theorem OMA.solution : OMA.R_Erdos19_erdos_19_variants_large_n_R1.H2 := by
  classical
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, ∀ K : Finset (Finset (Fin n)),
      (∀ A ∈ K, 2 ≤ A.card) → (∃ L ∈ K, n < L.card * L.card) →
      (∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A) →
      ∀ S ⊆ K, (∃ A ∈ S, A.card * A.card < n) →
        (∀ A ∈ S, n ≤ ((S.erase A).filter (fun B => (A ∩ B).Nonempty)).card) →
        ∃ c : Finset (Fin n) → Fin n,
          ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
    sorry
  unfold OMA.R_Erdos19_erdos_19_variants_large_n_R1.H2
  filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with n hsmall_n hn
  intro K hsize hlarge hK
  obtain ⟨c, hc⟩ := OMA19H2.colorable_of_colorable_cores (K := K) (by
    intro S hSK hdegree
    by_cases hallLarge : ∀ A ∈ S, n < A.card * A.card
    · exact OMA19H2.colorable_of_large_min_rank hn hsize hK S hSK hallLarge
    · push Not at hallLarge
      obtain ⟨A, hA, hAmin⟩ := S.exists_min_image Finset.card
        (by obtain ⟨B, hB, _⟩ := hallLarge; exact ⟨B, hB⟩)
      obtain ⟨L, hL, hLlarge⟩ := hlarge
      have hs := OMA19H2.min_rank_sq_lt_of_large_block hsize hK hSK hA hL hLlarge hAmin
        (hdegree A hA)
      exact hsmall_n K hsize ⟨L, hL, hLlarge⟩ hK S hSK ⟨A, hA, hs⟩ hdegree)
  exact ⟨fun A => c A.val, fun A B hne hmeet =>
    hc A.val A.property B.val B.property (fun h => hne (Subtype.ext h)) hmeet⟩
