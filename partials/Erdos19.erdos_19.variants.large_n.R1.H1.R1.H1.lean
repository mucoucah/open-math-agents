import OMAReductions.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex

-- Step Erdos19.erdos_19.variants.large_n.R1.H1.R1.H1: hypothesis H1 of reduction Erdos19.erdos_19.variants.large_n.R1.H1.R1
-- Credit: @<handle>
-- H1 := ∀ R : ℕ, ∀ᶠ n in Filter.atTop, ∀ K L : Finset (Finset (Fin n)),     (∀ A ∈ K, 2 ≤ A.card ∧ A.card * A.card ≤ n) →     (∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B) →     L ⊆ K → (∀ A ∈ L, A.card ≤ R) →     (¬ ∃ c : Finset (Fin n) → Fin n, (∀ X ∈ L, ∀ Y ∈ L, X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) →     (∀ A ∈ L, (∃ c : Finset (Fin n) → Fin n, (∀ X ∈ (L.erase A), ∀ Y ∈ (L.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) ∧       n ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty).card) →     (∀ A ∈ L, ∀ c : Finset (Fin n) → Fin n, (∀ X ∈ (L.erase A), ∀ Y ∈ (L.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y) →       ((L.erase A).filter (fun B => (A ∩ B).Nonempty)).image c = Finset.univ) →     (∃ A ∈ L, 3 ≤ A.card) →     (∃ A ∈ L, A.card * A.card < n) →     (∀ A ∈ L, A.card = 2 →       4 ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty ∧ B.card = 2).card) →     False

/-! Incidence bounds and colour constraints for a critical subfamily. -/

open Finset
open scoped BigOperators
open OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1

private theorem point_rank_budget {n : ℕ} {K L : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hLK : L ⊆ K) (hsize : ∀ B ∈ L, 2 ≤ B.card) (x : Fin n) :
    (L.filter (fun B => x ∈ B)).card +
      ∑ B ∈ L.filter (fun B => x ∈ B), (B.card - 2) ≤ n - 1 := by
  classical
  calc
    _ = ∑ B ∈ L.filter (fun B => x ∈ B), (1 + (B.card - 2)) := by
      rw [sum_add_distrib]
      simp
    _ = ∑ B ∈ L.filter (fun B => x ∈ B), (B.card - 1) := by
      apply sum_congr rfl
      intro B hB
      have := hsize B (mem_filter.mp hB).1
      omega
    _ ≤ ∑ B ∈ K.filter (fun B => x ∈ B), (B.card - 1) :=
      sum_le_sum_of_subset (filter_subset_filter _ hLK)
    _ = n - 1 := link_weight_eq hpair x

private theorem pair_neighborhood_card {n : ℕ} {L : Finset (Finset (Fin n))}
    {x y : Fin n} (hA : {x, y} ∈ L)
    (hlinear : ∀ B ∈ L, x ∈ B → y ∈ B → B = {x, y}) :
    (((L.erase {x, y}).filter fun B => ({x, y} ∩ B).Nonempty).card) + 2 =
      (L.filter (fun B => x ∈ B)).card + (L.filter (fun B => y ∈ B)).card := by
  classical
  let X := (L.erase {x, y}).filter (fun B => x ∈ B)
  let Y := (L.erase {x, y}).filter (fun B => y ∈ B)
  have hdisj : Disjoint X Y := by
    apply disjoint_left.mpr
    intro B hBX hBY
    obtain ⟨⟨hn, hB⟩, hx⟩ := mem_erase.mp (mem_filter.mp hBX).1, (mem_filter.mp hBX).2
    exact hn (hlinear B hB hx (mem_filter.mp hBY).2)
  have hN : (L.erase {x, y}).filter (fun B => ({x, y} ∩ B).Nonempty) = X ∪ Y := by
    ext B
    simp only [X, Y, mem_filter, mem_union, Finset.Nonempty, mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hB, z, rfl | rfl, hz⟩
      · exact Or.inl ⟨hB, hz⟩
      · exact Or.inr ⟨hB, hz⟩
    · rintro (⟨hB, hx⟩ | ⟨hB, hy⟩)
      · exact ⟨hB, x, Or.inl rfl, hx⟩
      · exact ⟨hB, y, Or.inr rfl, hy⟩
  have hcount (z : Fin n) (hz : z ∈ ({x, y} : Finset (Fin n))) :
      ((L.erase {x, y}).filter (fun B => z ∈ B)).card + 1 =
        (L.filter (fun B => z ∈ B)).card := by
    have hswap : (L.erase {x, y}).filter (fun B => z ∈ B) =
        (L.filter (fun B => z ∈ B)).erase {x, y} := by
      ext B
      simp only [mem_filter, mem_erase]
      tauto
    rw [hswap]
    exact card_erase_add_one (mem_filter.mpr ⟨hA, hz⟩)
  have hx := hcount x (by simp)
  have hy := hcount y (by simp)
  rw [hN, card_union_of_disjoint hdisj]
  change X.card + 1 = _ at hx
  change Y.card + 1 = _ at hy
  omega

private abbrev ProperOn {n : ℕ} {C : Type} (L : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → C) : Prop :=
  ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B

private abbrev Proper {n : ℕ} (L : Finset (Finset (Fin n))) (c : Finset (Fin n) → Fin n) : Prop :=
  ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B

private theorem card_incident_colors {n : ℕ} {L : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → Fin n} (hc : Proper L c) (v : Fin n) :
    ((L.filter (fun B => v ∈ B)).image c).card = (L.filter (fun B => v ∈ B)).card := by
  apply card_image_of_injOn
  intro A hA B hB h
  obtain ⟨hA, hvA⟩ := mem_filter.mp hA
  obtain ⟨hB, hvB⟩ := mem_filter.mp hB
  by_contra hab
  exact hc A hA B hB hab ⟨v, mem_inter.mpr ⟨hvA, hvB⟩⟩ h

private theorem pair_missing_disjoint {n : ℕ} {L : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → Fin n} {x y : Fin n}
    (hblocked : ((L.erase {x, y}).filter (fun B => ({x, y} ∩ B).Nonempty)).image c = univ) :
    Disjoint
      (univ \ (((L.erase {x, y}).filter (fun B => x ∈ B)).image c))
      (univ \ (((L.erase {x, y}).filter (fun B => y ∈ B)).image c)) := by
  apply disjoint_left.mpr
  intro a hx hy
  have ha : a ∈ ((L.erase {x, y}).filter (fun B => ({x, y} ∩ B).Nonempty)).image c :=
    hblocked.symm ▸ mem_univ a
  obtain ⟨B, hB, rfl⟩ := mem_image.mp ha
  obtain ⟨hB, z, hz⟩ := mem_filter.mp hB
  have hzy : z = x ∨ z = y := by simpa using (mem_inter.mp hz).1
  have hzB := (mem_inter.mp hz).2
  rcases hzy with rfl | rfl
  · exact (mem_sdiff.mp hx).2 (mem_image_of_mem c (mem_filter.mpr ⟨hB, hzB⟩))
  · exact (mem_sdiff.mp hy).2 (mem_image_of_mem c (mem_filter.mpr ⟨hB, hzB⟩))

/-- Exchanging two colours on a set closed under bichromatic adjacency preserves properness. -/
private theorem proper_swap_colors {n : ℕ} {C : Type} [DecidableEq C] {L S : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → C} (hc : ProperOn L c) (a b : C)
    (hclosed : ∀ A ∈ L, A ∈ S → ∀ B ∈ L, B ∉ S →
      (A ∩ B).Nonempty → ¬ ((c A = a ∧ c B = b) ∨ (c A = b ∧ c B = a))) :
    ProperOn L (fun A => if A ∈ S then Equiv.swap a b (c A) else c A) := by
  classical
  intro A hA B hB hAB hmeet
  have hne := hc A hA B hB hAB hmeet
  have cross (X Y : Finset (Fin n)) (hX : X ∈ L) (hY : Y ∈ L)
      (hXS : X ∈ S) (hYS : Y ∉ S) (hXY : (X ∩ Y).Nonempty)
      (hne : c X ≠ c Y) : Equiv.swap a b (c X) ≠ c Y := by
    intro he
    apply hclosed X hX hXS Y hY hYS hXY
    by_cases ha : c X = a
    · exact Or.inl ⟨ha, by simpa [ha] using he.symm⟩
    by_cases hb : c X = b
    · exact Or.inr ⟨hb, by simpa [hb] using he.symm⟩
    exfalso
    exact hne (by simpa only [Equiv.swap_apply_of_ne_of_ne ha hb] using he)
  by_cases hAS : A ∈ S <;> by_cases hBS : B ∈ S
  · simpa [hAS, hBS] using hne
  · simpa [hAS, hBS] using cross A B hA hB hAS hBS hmeet hne
  · have hmeet' : (B ∩ A).Nonempty := by rwa [inter_comm]
    simpa [hAS, hBS] using (cross B A hB hA hBS hAS hmeet' hne.symm).symm
  · simpa [hAS, hBS] using hne

/-- A rank-two deletion cannot separate the unique endpoint blockers of two missing colours. -/
private theorem pair_swap_obstruction {n : ℕ} {L S : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → Fin n} {x y a b : Fin n} {E F : Finset (Fin n)}
    (hc : Proper (L.erase {x, y}) c)
    (hbad : ¬ ∃ d, Proper L d)
    (hx : ∀ B ∈ L.erase {x, y}, x ∈ B → c B ≠ a)
    (hy : ∀ B ∈ L.erase {x, y}, y ∈ B → c B ≠ b)
    (hE : E ∈ L.erase {x, y}) (hyE : y ∈ E) (haE : c E = a)
    (hF : F ∈ L.erase {x, y}) (hxF : x ∈ F) (hbF : c F = b)
    (hES : E ∈ S) (hFS : F ∉ S) :
    ∃ A ∈ L.erase {x, y}, A ∈ S ∧ ∃ B ∈ L.erase {x, y}, B ∉ S ∧
      (A ∩ B).Nonempty ∧ ((c A = a ∧ c B = b) ∨ (c A = b ∧ c B = a)) := by
  classical
  by_contra hcut
  push Not at hcut
  let d (A : Finset (Fin n)) := if A ∈ S then Equiv.swap a b (c A) else c A
  have hd : Proper (L.erase {x, y}) d :=
    proper_swap_colors hc a b fun A hA hAS B hB hBS hm => by
      have h := hcut A hA hAS B hB hBS hm
      tauto
  have hab : a ≠ b := fun h => hy E hE hyE (haE.trans h)
  have hfree_x (B : Finset (Fin n)) (hB : B ∈ L.erase {x, y}) (hxB : x ∈ B) :
      d B ≠ a := by
    by_cases hBS : B ∈ S
    · have hbB : c B ≠ b := by
        intro he
        have hBF : B = F := by
          by_contra hne
          exact hc B hB F hF hne ⟨x, mem_inter.mpr ⟨hxB, hxF⟩⟩ (he.trans hbF.symm)
        exact hFS (hBF ▸ hBS)
      simp [d, hBS, Equiv.swap_apply_of_ne_of_ne (hx B hB hxB) hbB, hx B hB hxB]
    · simpa [d, hBS] using hx B hB hxB
  have hfree_y (B : Finset (Fin n)) (hB : B ∈ L.erase {x, y}) (hyB : y ∈ B) :
      d B ≠ a := by
    by_cases hBS : B ∈ S
    · by_cases haB : c B = a
      · simpa [d, hBS, haB] using hab.symm
      · simp [d, hBS, Equiv.swap_apply_of_ne_of_ne haB (hy B hB hyB), haB]
    · have haB : c B ≠ a := by
        intro he
        have hBE : B = E := by
          by_contra hne
          exact hc B hB E hE hne ⟨y, mem_inter.mpr ⟨hyB, hyE⟩⟩ (he.trans haE.symm)
        exact hBS (hBE.symm ▸ hES)
      simpa [d, hBS] using haB
  apply hbad (extend_coloring_of_unused (A := {x, y}) (v := a) hd ?_)
  intro ha
  obtain ⟨B, hB, he⟩ := mem_image.mp ha
  obtain ⟨hB, z, hz⟩ := mem_filter.mp hB
  have hzy : z = x ∨ z = y := by simpa using (mem_inter.mp hz).1
  have hzB := (mem_inter.mp hz).2
  rcases hzy with rfl | rfl
  · exact hfree_x B hB hzB he
  · exact hfree_y B hB hzB he

/-- Sorting the vertices by a key makes every fibre an interval of labels. -/
private theorem consecutive_fibres {n : ℕ} (key : Fin n → Fin n) :
    ∃ p : Fin n ≃ Fin n, ∀ ⦃x y z : Fin n⦄,
      key x = key z → p x ≤ p y → p y ≤ p z → key y = key x := by
  classical
  let f (x : Fin n) : Lex (Fin n × Fin n) := toLex (key x, x)
  have hf : Function.Injective f := fun _ _ h => congrArg (fun t => (ofLex t).2) h
  let T := (univ : Finset (Fin n)).image f
  have hT : T.card = n := by
    simpa [T] using (card_image_of_injective (univ : Finset (Fin n)) hf)
  let e : Fin n ≃ T :=
    Equiv.ofBijective (fun x => ⟨f x, mem_image_of_mem f (mem_univ x)⟩)
      ⟨fun _ _ h => hf (congrArg Subtype.val h), fun ⟨u, hu⟩ => by
        obtain ⟨x, _, rfl⟩ := mem_image.mp hu
        exact ⟨x, rfl⟩⟩
  let g := T.orderIsoOfFin hT
  let p := e.trans g.symm.toEquiv
  refine ⟨p, ?_⟩
  have hg (x : Fin n) : g (p x) = e x := g.apply_symm_apply (e x)
  have hkey ⦃x y : Fin n⦄ (h : p x ≤ p y) : key x ≤ key y := by
    have h' := g.monotone h
    rw [hg, hg] at h'
    exact Prod.Lex.monotone_fst (f x) (f y) (show f x ≤ f y from h')
  intro x y z hxz hxy hyz
  exact le_antisymm ((hkey hyz).trans_eq hxz.symm) (hkey hxy)

/-- Pair blocks can use endpoint sums when the larger blocks are disjoint. -/
private theorem color_disjoint_large_blocks {n : ℕ} [NeZero n]
    {K L : Finset (Finset (Fin n))} (hLK : L ⊆ K)
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ L, 2 ≤ A.card)
    (hdisj : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → 3 ≤ A.card → 3 ≤ B.card → Disjoint A B) :
    ∃ c, Proper L c := by
  classical
  let Large (A : Finset (Fin n)) : Prop := A ∈ L ∧ 3 ≤ A.card
  have hnonempty {A : Finset (Fin n)} (hA : Large A) : A.Nonempty :=
    card_pos.mp (by have := hA.2; omega)
  let Q (x : Fin n) := ∃ A, Large A ∧ x ∈ A
  let key (x : Fin n) : Fin n :=
    if h : Q x then h.choose.min' (hnonempty h.choose_spec.1) else x
  have hkey (A : Finset (Fin n)) (hA : Large A) (x : Fin n) :
      key x = A.min' (hnonempty hA) ↔ x ∈ A := by
    by_cases hx : Q x
    · have hb := hx.choose_spec
      dsimp only [key]
      rw [dif_pos hx]
      constructor
      · intro h
        have he : hx.choose = A := by
          by_contra hne
          apply disjoint_left.mp (hdisj _ hb.1.1 _ hA.1 hne hb.1.2 hA.2)
            (min'_mem hx.choose (hnonempty hb.1))
          rw [h]
          exact min'_mem _ _
        exact he ▸ hb.2
      · intro hxA
        have he : hx.choose = A := by
          by_contra hne
          exact disjoint_left.mp (hdisj _ hb.1.1 _ hA.1 hne hb.1.2 hA.2) hb.2 hxA
        subst A
        rfl
    · dsimp only [key]
      rw [dif_neg hx]
      constructor
      · rintro rfl
        exact min'_mem _ _
      · exact fun hxA => (hx ⟨A, hA, hxA⟩).elim
  obtain ⟨p, hp⟩ := consecutive_fibres key
  let col (A : Finset (Fin n)) : Fin n :=
    if A.card = 2 then ∑ x ∈ A, p x else
      if h : (A.image p).Nonempty then (A.image p).min' h + (A.image p).max' h else 0
  have hreflect (A : Finset (Fin n)) (hA : Large A) (x : Fin n) (hx : x ∈ A) :
      ∃ y ∈ A, col A = p x + p y := by
    let T := A.image p
    have hT : T.Nonempty := (hnonempty hA).image _
    let a := T.min' hT
    let b := T.max' hT
    have ha : a ∈ T := min'_mem _ _
    have hb : b ∈ T := max'_mem _ _
    have hpx : p x ∈ T := mem_image_of_mem _ hx
    have hl : a ≤ p x := min'_le _ _ hpx
    have hu : p x ≤ b := le_max' _ _ hpx
    have hval₁ : (a : ℕ) ≤ (p x : ℕ) := hl
    have hval₂ : (p x : ℕ) ≤ (b : ℕ) := hu
    let t : Fin n := ⟨(a : ℕ) + (b : ℕ) - (p x : ℕ), by have := b.isLt; omega⟩
    have ht₁ : a ≤ t := by change (a : ℕ) ≤ (t : ℕ); dsimp [t]; omega
    have ht₂ : t ≤ b := by change (t : ℕ) ≤ (b : ℕ); dsimp [t]; omega
    obtain ⟨u, huA, hu'⟩ := mem_image.mp ha
    obtain ⟨v, hvA, hv'⟩ := mem_image.mp hb
    let y := p.symm t
    have hy : p y = t := p.apply_symm_apply t
    have huKey := (hkey A hA u).mpr huA
    have hvKey := (hkey A hA v).mpr hvA
    have hyKey := hp (x := u) (y := y) (z := v) (huKey.trans hvKey.symm) (by rwa [hu', hy]) (by rwa [hy, hv'])
    refine ⟨y, (hkey A hA y).mp (hyKey.trans huKey), ?_⟩
    have hne : A.card ≠ 2 := by have := hA.2; omega
    have hT' : (A.image p).Nonempty := hT
    simp only [col, if_neg hne, dif_pos hT', hy]
    apply Fin.ext
    change (↑(a + b) : ℕ) = ↑(p x + t)
    rw [Fin.val_add, Fin.val_add]
    congr 1
    dsimp [t]
    omega
  have hsum {A : Finset (Fin n)} {x : Fin n} (hx : x ∈ A) (hA : A.card = 2) :
      ∃ y ≠ x, A = {x,y} ∧ col A = p x + p y := by
    obtain ⟨y, hy, rfl⟩ := pair_of_mem_of_card_two hx hA
    exact ⟨y, hy, rfl, by simp only [col, if_pos hA, sum_pair hy.symm]⟩
  have hmixed {A B : Finset (Fin n)} (hA : A ∈ L) (hB : Large B) (hAB : A ≠ B)
      {x : Fin n} (hxA : x ∈ A) (hxB : x ∈ B) (hA₂ : A.card = 2) :
      col A ≠ col B := by
    obtain ⟨y, hy, rfl, ha⟩ := hsum hxA hA₂
    obtain ⟨z, hz, hb⟩ := hreflect B hB x hxB
    intro he
    have heq : y = z := p.injective (add_left_cancel (ha.symm.trans (he.trans hb)))
    subst z
    exact hAB (block_eq_of_pair hpair (hLK hA) (hLK hB.1)
      hy.symm (by simp) (by simp) hxB hz)
  refine ⟨col, ?_⟩
  intro A hA B hB hAB hmeet
  obtain ⟨x, hx⟩ := hmeet
  obtain ⟨hxA, hxB⟩ := mem_inter.mp hx
  by_cases hA₂ : A.card = 2 <;> by_cases hB₂ : B.card = 2
  · obtain ⟨y, _, rfl, ha⟩ := hsum hxA hA₂
    obtain ⟨z, _, rfl, hb⟩ := hsum hxB hB₂
    intro he
    have heq : y = z := p.injective (add_left_cancel (ha.symm.trans (he.trans hb)))
    exact hAB (congrArg (fun w => ({x, w} : Finset (Fin n))) heq)
  · exact hmixed hA ⟨hB, by have := hsize B hB; omega⟩ hAB hxA hxB hA₂
  · exact (hmixed hB ⟨hA, by have := hsize A hA; omega⟩ hAB.symm hxB hxA hB₂).symm
  · have h₁ := hsize A hA
    have h₂ := hsize B hB
    exact (disjoint_left.mp (hdisj A hA B hB hAB (by omega) (by omega)) hxA hxB).elim

/-- A balanced bipartite graph has a perfect matching if both sides
    have at most half a side's worth of non-neighbours at each vertex. -/
private theorem dense_bipartite_matching {α β : Type*} [Fintype α] [Fintype β]
    (r : α → β → Prop) [DecidableRel r] {d : ℕ}
    (hcard : Fintype.card α = Fintype.card β)
    (hd : 2 * d ≤ Fintype.card β)
    (hleft : ∀ a, ((univ : Finset β).filter fun b => ¬ r a b).card ≤ d)
    (hright : ∀ b, ((univ : Finset α).filter fun a => ¬ r a b).card ≤ d) :
    ∃ e : α ≃ β, ∀ x, r x (e x) := by
  classical
  obtain ⟨f, hf, hr⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp (by
      intro S
      let N := (univ : Finset β).filter fun b => ∃ a ∈ S, r a b
      change S.card ≤ N.card
      by_cases hS : S.Nonempty
      · by_cases hsmall : S.card ≤ d
        · obtain ⟨a, ha⟩ := hS
          have hsub : ((univ : Finset β).filter fun b => r a b) ⊆ N := by
            intro b hb
            exact mem_filter.mpr ⟨mem_univ _, a, ha, (mem_filter.mp hb).2⟩
          have hp := card_filter_add_card_filter_not (s := (univ : Finset β)) (fun b => r a b)
          rw [card_univ] at hp
          have hh := hleft a
          have hi := card_le_card hsub
          omega
        · have hfull : N = univ := by
            apply eq_univ_of_forall
            intro b
            by_contra hb
            have hsub : S ⊆ (univ : Finset α).filter (fun a => ¬ r a b) := by
              intro a ha
              exact mem_filter.mpr ⟨mem_univ _, fun h => hb (mem_filter.mpr ⟨mem_univ _, a, ha, h⟩)⟩
            exact hsmall ((card_le_card hsub).trans (hright b))
          rw [hfull, card_univ, ← hcard]
          exact card_le_univ S
      · rw [not_nonempty_iff_eq_empty.mp hS, card_empty]
        exact Nat.zero_le _)
  let e := Equiv.ofBijective f ⟨hf, (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩ |>.2⟩
  exact ⟨e, hr⟩

/-- An even set of free vertices can be covered by unused pair blocks if the
    graph of available pairs is sufficiently dense on the free vertices. -/
private theorem dense_pair_matching {n d : ℕ} (P : Finset (Fin n))
    (G : Finset (Finset (Fin n))) (heven : Even P.card) (hd : 4 * d ≤ P.card)
    (hmiss : ∀ x ∈ P, (P.filter fun y => y ≠ x ∧ ({x,y} : Finset (Fin n)) ∉ G).card ≤ d) :
    ∃ M ⊆ G, (∀ B ∈ M, B.card = 2) ∧
      (∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B) ∧ M.biUnion id = P := by
  classical
  obtain ⟨m, hm⟩ := heven
  obtain ⟨X, hXP, hX⟩ := exists_subset_card_eq (s := P) (n := m) (by omega)
  let Y := P \ X
  have hY : Y.card = m := by
    dsimp [Y]
    rw [card_sdiff_of_subset hXP, hX, hm]
    omega
  have hYX : ∀ y ∈ Y, y ∉ X := fun y hy => (mem_sdiff.mp hy).2
  have hYP : Y ⊆ P := sdiff_subset
  let r (x : X) (y : Y) : Prop := ({x.val, y.val} : Finset (Fin n)) ∈ G
  have hl (x : X) : ((univ : Finset Y).filter fun y => ¬ r x y).card ≤ d := by
    refine (card_le_card_of_injOn (fun y : Y => y.val) ?_ Subtype.val_injective.injOn).trans
      (hmiss x (hXP x.property))
    intro y hy
    have hy' := (mem_filter.mp (mem_coe.mp hy)).2
    refine mem_coe.mpr (mem_filter.mpr ⟨hYP y.property, ?_, hy'⟩)
    intro he
    exact hYX y y.property (by
      change y.val = x.val at he
      rw [he]
      exact x.property)
  have hr (y : Y) : ((univ : Finset X).filter fun x => ¬ r x y).card ≤ d := by
    refine (card_le_card_of_injOn (fun x : X => x.val) ?_ Subtype.val_injective.injOn).trans
      (hmiss y (hYP y.property))
    intro x hx
    have hx' := (mem_filter.mp (mem_coe.mp hx)).2
    refine mem_coe.mpr (mem_filter.mpr ⟨hXP x.property, ?_, ?_⟩)
    · intro he
      exact hYX y y.property (he ▸ x.property)
    · simpa only [r, pair_comm] using hx'
  have hX' : Fintype.card X = m := by simpa using hX
  have hY' : Fintype.card Y = m := by simpa using hY
  obtain ⟨e, he⟩ := dense_bipartite_matching r (hX'.trans hY'.symm) (by omega) hl hr
  let edge (x : X) : Finset (Fin n) := {x.val, (e x).val}
  let M := (univ : Finset X).image edge
  have hex {B : Finset (Fin n)} (hB : B ∈ M) : ∃ x : X, edge x = B := by
    obtain ⟨x, _, hx⟩ := mem_image.mp hB
    exact ⟨x, hx⟩
  have hem (x : X) : edge x ∈ M := mem_image_of_mem _ (mem_univ x)
  have hpairX (x : X) : (x : Fin n) ≠ (e x : Fin n) := by
    intro he
    exact hYX (e x) (e x).property (he ▸ x.property)
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨x, rfl⟩ := hex hB
    exact he x
  · intro B hB
    obtain ⟨x, rfl⟩ := hex hB
    exact card_pair (hpairX x)
  · intro A hA B hB hAB
    obtain ⟨x, rfl⟩ := hex hA
    obtain ⟨y, rfl⟩ := hex hB
    apply disjoint_left.mpr
    intro z hx hy
    change z ∈ ({x.val, (e x).val} : Finset (Fin n)) at hx
    change z ∈ ({y.val, (e y).val} : Finset (Fin n)) at hy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hAB (congrArg edge (Subtype.ext (hx.symm.trans hy)))
    · exact hYX (e y) (e y).property ((hx.symm.trans hy) ▸ x.property)
    · exact hYX (e x) (e x).property ((hy.symm.trans hx) ▸ y.property)
    · exact hAB (congrArg edge (e.injective (Subtype.ext (hx.symm.trans hy))))
  · ext z
    constructor
    · intro hz
      obtain ⟨B, hB, hzB⟩ := mem_biUnion.mp hz
      obtain ⟨x, rfl⟩ := hex hB
      change z ∈ ({x.val, (e x).val} : Finset (Fin n)) at hzB
      simp only [mem_insert, mem_singleton] at hzB
      rcases hzB with rfl | rfl
      · exact hXP x.property
      · exact hYP (e x).property
    · intro hz
      by_cases hzX : z ∈ X
      · exact mem_biUnion.mpr ⟨edge ⟨z, hzX⟩, hem ⟨z, hzX⟩, by simp [edge]⟩
      · let y : Y := ⟨z, mem_sdiff.mpr ⟨hz, hzX⟩⟩
        obtain ⟨x, hx⟩ := e.surjective y
        exact mem_biUnion.mpr ⟨edge x, hem x, by
          change y.val ∈ ({x.val, (e x).val} : Finset (Fin n))
          simp [hx]⟩

private theorem pair_label_inj {n : ℕ} (x : Fin n) {y z : Fin n}
    (hy : y ≠ x)
    (h : ({x, y} : Finset (Fin n)) = {x, z}) : y = z := by
  have hy' : y ∈ ({x, z} : Finset (Fin n)) := h ▸ (by simp)
  simpa [hy] using hy'

private theorem card_used_pairs_at {n t : ℕ} {M : Finset (Finset (Fin n))}
    {f : Finset (Fin n) → ℕ}
    (hcap : ∀ A ∈ M, f A < t)
    (hf : ∀ A ∈ M, ∀ B ∈ M, A ≠ B → (A ∩ B).Nonempty → f A ≠ f B)
    (x : Fin n) :
    ((univ : Finset (Fin n)).filter (fun y => y ≠ x ∧ {x,y} ∈ M)).card ≤ t := by
  rw [← card_range t]
  apply card_le_card_of_injOn (fun y : Fin n => f {x,y})
  · intro y hy
    exact mem_coe.mpr (mem_range.mpr (hcap _ (mem_filter.mp (mem_coe.mp hy)).2.2))
  · intro y hy z hz h
    obtain ⟨hyx, hyM⟩ := (mem_filter.mp (mem_coe.mp hy)).2
    obtain ⟨_, hzM⟩ := (mem_filter.mp (mem_coe.mp hz)).2
    refine pair_label_inj x hyx ?_
    by_contra hne
    exact hf _ hyM _ hzM hne ⟨x, by simp⟩ h

/-- Extend each precoloured class with pair blocks until all of its specified
    vertices are covered. The omitted vertices handle the parity constraint. -/
private theorem cover_precolored_classes {n k d : ℕ} (G H : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → ℕ) (omitted : ℕ → Finset (Fin n))
    (hg : ∀ x : Fin n, ((univ : Finset (Fin n)).filter
      (fun y => y ≠ x ∧ {x,y} ∉ G)).card ≤ d)
    (hroom : ∀ i < k, 4 * (d + i) ≤
      ((univ : Finset (Fin n)) \ (((H.filter fun A => c A = i).biUnion id) ∪ omitted i)).card)
    (hparity : ∀ i < k, Even
      ((univ : Finset (Fin n)) \ (((H.filter fun A => c A = i).biUnion id) ∪ omitted i)).card) :
    ∃ M ⊆ G, ∃ f : Finset (Fin n) → ℕ,
      (∀ A ∈ M, f A < k ∧ A.card = 2) ∧
      (∀ A ∈ M, ∀ B ∈ M, A ≠ B → (A ∩ B).Nonempty → f A ≠ f B) ∧
      (∀ A ∈ M, ∀ B ∈ H, (A ∩ B).Nonempty → f A ≠ c B) ∧
      (∀ i < k, (univ : Finset (Fin n)) \ omitted i ⊆
        ((M.filter fun A => f A = i).biUnion id) ∪ ((H.filter fun B => c B = i).biUnion id)) := by
  classical
  induction k with
  | zero =>
    exact ⟨∅, empty_subset _, fun A => c A, by simp, by simp, by simp, by simp⟩
  | succ t ih =>
    obtain ⟨M, hMG, f, hcap, hf, hmix, hcover⟩ :=
      ih (fun i hi => hroom i (Nat.lt_succ_of_lt hi)) (fun i hi => hparity i (Nat.lt_succ_of_lt hi))
    let C := (H.filter fun A => c A = t).biUnion id
    let P := (univ : Finset (Fin n)) \ (C ∪ omitted t)
    have hmiss (x : Fin n) (hx : x ∈ P) :
        (P.filter fun y => y ≠ x ∧ {x,y} ∉ G \ M).card ≤ d + t := by
      let D := (univ : Finset (Fin n)).filter (fun y => y ≠ x ∧ {x,y} ∉ G)
      let U := (univ : Finset (Fin n)).filter (fun y => y ≠ x ∧ {x,y} ∈ M)
      have hs : (P.filter fun y => y ≠ x ∧ {x,y} ∉ G \ M) ⊆ D ∪ U := by
        intro y hy
        simp only [D, U, mem_filter, mem_union, mem_univ, true_and, mem_sdiff] at hy ⊢
        tauto
      exact (card_le_card hs).trans ((card_union_le D U).trans
        (Nat.add_le_add (hg x) (card_used_pairs_at (fun A hA => (hcap A hA).1) hf x)))
    obtain ⟨N, hNGM, hNsize, hNdisj, hNcover⟩ :=
      dense_pair_matching P (G \ M) (hparity t (Nat.lt_succ_self t))
        (hroom t (Nat.lt_succ_self t)) hmiss
    have hNM {A : Finset (Fin n)} (hA : A ∈ N) : A ∉ M := (mem_sdiff.mp (hNGM hA)).2
    have hNpoint {A : Finset (Fin n)} (hA : A ∈ N) {x : Fin n} (hx : x ∈ A) :
        x ∈ P := hNcover ▸ mem_biUnion.mpr ⟨A, hA, hx⟩
    let g (A : Finset (Fin n)) := if A ∈ N then t else f A
    refine ⟨M ∪ N, union_subset hMG (fun A hA => (mem_sdiff.mp (hNGM hA)).1), g, ?_, ?_, ?_, ?_⟩
    · intro A hA
      rcases mem_union.mp hA with hA | hA
      · have hnot : A ∉ N := fun h => hNM h hA
        exact ⟨by simpa only [g, if_neg hnot] using Nat.lt_succ_of_lt (hcap A hA).1, (hcap A hA).2⟩
      · exact ⟨by simp [g, hA], hNsize A hA⟩
    · intro A hA B hB hAB hmeet
      rcases mem_union.mp hA with hA | hA <;> rcases mem_union.mp hB with hB | hB
      · have ha : A ∉ N := fun h => hNM h hA
        have hb : B ∉ N := fun h => hNM h hB
        simpa only [g, if_neg ha, if_neg hb] using hf A hA B hB hAB hmeet
      · have ha : A ∉ N := fun h => hNM h hA
        simpa only [g, if_neg ha, if_pos hB] using (hcap A hA).1.ne
      · have hb : B ∉ N := fun h => hNM h hB
        simpa only [g, if_pos hA, if_neg hb] using (hcap B hB).1.ne'
      · obtain ⟨x, hx⟩ := hmeet
        exact (Finset.disjoint_left.mp (hNdisj A hA B hB hAB)
          (mem_inter.mp hx).1 (mem_inter.mp hx).2).elim
    · intro A hA B hB hmeet
      rcases mem_union.mp hA with hA | hA
      · have ha : A ∉ N := fun h => hNM h hA
        simpa only [g, if_neg ha] using hmix A hA B hB hmeet
      · intro he
        obtain ⟨x, hx⟩ := hmeet
        have hxP := hNpoint hA (mem_inter.mp hx).1
        have he' : c B = t := by simpa only [g, if_pos hA] using he.symm
        have hxC : x ∈ C := mem_biUnion.mpr ⟨B, mem_filter.mpr ⟨hB, he'⟩, (mem_inter.mp hx).2⟩
        exact (mem_sdiff.mp hxP).2 (mem_union_left _ hxC)
    · intro i hi x hx
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · rcases mem_union.mp (hcover i hlt hx) with hx | hx
        · obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp hx
          obtain ⟨hAM, hfi⟩ := mem_filter.mp hA
          have hnot : A ∉ N := fun h => hNM h hAM
          exact mem_union_left _ (mem_biUnion.mpr ⟨A,
            mem_filter.mpr ⟨mem_union_left _ hAM, by simpa only [g, if_neg hnot] using hfi⟩, hxA⟩)
        · exact mem_union_right _ hx
      · by_cases hxC : x ∈ C
        · exact mem_union_right _ hxC
        · have hxP : x ∈ P := mem_sdiff.mpr ⟨mem_univ _, fun hu => (mem_union.mp hu).elim
              hxC (mem_sdiff.mp hx).2⟩
          obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp (hNcover.symm ▸ hxP)
          exact mem_union_left _ (mem_biUnion.mpr ⟨A,
            mem_filter.mpr ⟨mem_union_right _ hA, by simp only [g, if_pos hA]⟩, hxA⟩)

/-- The coverage construction leaves a pair graph of degree below the number
    of remaining colours when each omitted incidence is paid for by degree slack. -/
private theorem dense_coloring_of_pair_degree_coloring {n k d : ℕ}
    (G H : Finset (Finset (Fin n))) (hG : ∀ A ∈ G, A.card = 2)
    (hGH : Disjoint G H) (hk : k < n)
    (c : Finset (Fin n) → ℕ) (omitted : ℕ → Finset (Fin n))
    (hc : ∀ A ∈ H, c A < k)
    (hh : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B)
    (hg : ∀ x : Fin n, ((univ : Finset (Fin n)).filter
      (fun y => y ≠ x ∧ {x,y} ∉ G)).card ≤ d)
    (hroom : ∀ i < k, 4 * (d + i) ≤
      ((univ : Finset (Fin n)) \ (((H.filter fun A => c A = i).biUnion id) ∪ omitted i)).card)
    (hparity : ∀ i < k, Even
      ((univ : Finset (Fin n)) \ (((H.filter fun A => c A = i).biUnion id) ∪ omitted i)).card)
    (hslack : ∀ x : Fin n, ((G ∪ H).filter (fun A => x ∈ A)).card +
      ((range k).filter (fun i => x ∈ omitted i)).card < n)
    (hgraph : ∀ P : Finset (Finset (Fin n)), (∀ A ∈ P, A.card = 2) →
      (∀ x : Fin n, (P.filter (fun A => x ∈ A)).card < n - k) →
      ∃ g : Finset (Fin n) → Fin (n - k),
        ∀ A ∈ P, ∀ B ∈ P, A ≠ B → (A ∩ B).Nonempty → g A ≠ g B) :
    ∃ f, Proper (G ∪ H) f := by
  classical
  obtain ⟨M, hMG, f, hf, hproper, hmix, hcover⟩ :=
    cover_precolored_classes (k := k) G H c omitted hg hroom hparity
  let C := M ∪ H
  let P := G \ M
  have hCP : C ∪ P = G ∪ H := by
    ext A
    simp only [C, P, mem_union, mem_sdiff]
    constructor
    · rintro ((hA | hA) | ⟨hA, _⟩)
      · exact Or.inl (hMG hA)
      · exact Or.inr hA
      · exact Or.inl hA
    · rintro (hA | hA)
      · by_cases hm : A ∈ M
        · exact Or.inl (Or.inl hm)
        · exact Or.inr ⟨hA, hm⟩
      · exact Or.inl (Or.inr hA)
  have hdisj : Disjoint C P := by
    apply disjoint_left.mpr
    intro A hAC hAP
    obtain ⟨hAG, hAM⟩ := mem_sdiff.mp hAP
    rcases mem_union.mp hAC with hAM' | hAH
    · exact hAM hAM'
    · exact disjoint_left.mp hGH hAG hAH
  let col (A : Finset (Fin n)) := if A ∈ M then f A else c A
  have hcol_lt (A : Finset (Fin n)) (hA : A ∈ C) : col A < k := by
    rcases mem_union.mp hA with hAM | hAH
    · simpa only [col, if_pos hAM] using (hf A hAM).1
    · have hAM : A ∉ M := fun hm => disjoint_left.mp hGH (hMG hm) hAH
      simpa only [col, if_neg hAM] using hc A hAH
  have hgood (A : Finset (Fin n)) (hA : A ∈ C) (B : Finset (Fin n)) (hB : B ∈ C)
      (hne : A ≠ B) (hmeet : (A ∩ B).Nonempty) : col A ≠ col B := by
    have hnM {D : Finset (Fin n)} (hD : D ∈ H) : D ∉ M :=
      fun h => disjoint_left.mp hGH (hMG h) hD
    rcases mem_union.mp hA with hAM | hAH <;> rcases mem_union.mp hB with hBM | hBH
    · simpa only [col, if_pos hAM, if_pos hBM] using hproper A hAM B hBM hne hmeet
    · simpa only [col, if_pos hAM, if_neg (hnM hBH)] using hmix A hAM B hBH hmeet
    · have hmeet' : (B ∩ A).Nonempty := by rwa [inter_comm]
      simpa only [col, if_pos hBM, if_neg (hnM hAH)] using (hmix B hBM A hAH hmeet').symm
    · simpa only [col, if_neg (hnM hAH), if_neg (hnM hBH)] using hh A hAH B hBH hne hmeet
  have hdegrees (x : Fin n) : (P.filter (fun A => x ∈ A)).card < n - k := by
    let Good := (range k).filter (fun i => x ∉ omitted i)
    let Missing := (range k).filter (fun i => x ∈ omitted i)
    let I := C.filter (fun A => x ∈ A)
    have hpartition : Good.card + Missing.card = k := by
      simpa only [Good, Missing, add_comm, card_range] using
        card_filter_add_card_filter_not (s := range k) (fun i => x ∈ omitted i)
    have hused : Good ⊆ I.image col := by
      intro i hi
      have hi' := (mem_filter.mp hi).2
      have hik := mem_range.mp (mem_filter.mp hi).1
      have hx := hcover i hik (mem_sdiff.mpr ⟨mem_univ _, hi'⟩)
      rcases mem_union.mp hx with hx | hx
      · obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp hx
        obtain ⟨hAM, hfi⟩ := mem_filter.mp hA
        exact mem_image.mpr ⟨A, mem_filter.mpr ⟨mem_union_left _ hAM, hxA⟩,
          by simpa only [col, if_pos hAM] using hfi⟩
      · obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp hx
        obtain ⟨hAH, hci⟩ := mem_filter.mp hA
        have hAM : A ∉ M := fun hm => disjoint_left.mp hGH (hMG hm) hAH
        exact mem_image.mpr ⟨A, mem_filter.mpr ⟨mem_union_right _ hAH, hxA⟩,
          by simpa only [col, if_neg hAM] using hci⟩
    have hcards : Good.card ≤ I.card := (card_le_card hused).trans card_image_le
    have hsplit : ((G ∪ H).filter (fun A => x ∈ A)).card =
        I.card + (P.filter (fun A => x ∈ A)).card := by
      rw [← hCP, filter_union, card_union_of_disjoint (hdisj.mono
        (filter_subset _ _) (filter_subset _ _))]
    have hs := hslack x
    change ((G ∪ H).filter (fun A => x ∈ A)).card + Missing.card < n at hs
    rw [hsplit] at hs
    omega
  obtain ⟨g, hg'⟩ := hgraph P (fun A hA => hG A (mem_sdiff.mp hA).1) hdegrees
  let colC (A : Finset (Fin n)) (hA : A ∈ C) : Fin n :=
    ⟨col A, (hcol_lt A hA).trans hk⟩
  let colP (A : Finset (Fin n)) : Fin n := ⟨k + (g A).val, by have := (g A).isLt; omega⟩
  refine ⟨fun A => if hA : A ∈ C then colC A hA else colP A, ?_⟩
  rw [← hCP]
  intro A hA B hB hab hmeet heq
  have he := congrArg Fin.val heq
  by_cases hAC : A ∈ C <;> by_cases hBC : B ∈ C
  · apply hgood A hAC B hBC hab hmeet
    simpa only [dif_pos hAC, dif_pos hBC, colC] using he
  · simp only [dif_pos hAC, dif_neg hBC, colC, colP] at he
    have := hcol_lt A hAC
    omega
  · simp only [dif_neg hAC, dif_pos hBC, colC, colP] at he
    have := hcol_lt B hBC
    omega
  · have hAP := (mem_union.mp hA).resolve_left hAC
    have hBP := (mem_union.mp hB).resolve_left hBC
    apply hg' A hAP B hBP hab hmeet
    apply Fin.ext
    simp only [dif_neg hAC, dif_neg hBC, colP] at he
    omega

/-- A connected graph of maximum degree two has at most two vertices of
    degree at most one. This bounds the number of usable endpoints in a
    two-colour component of a pair graph. -/
private theorem connected_degree_two_endpoints {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hd : ∀ v, G.degree v ≤ 2) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : G.degree x ≤ 1) (hy : G.degree y ≤ 1) (hz : G.degree z ≤ 1) : False := by
  classical
  let T : Finset V := {x, y, z}
  have hT : T.card = 3 := by simp [T, hxy, hxz, hyz]
  have hnum : (∑ v : V, (if v ∈ T then 1 else 0 : ℕ)) = 3 := by
    rw [← sum_filter]
    simpa using hT
  have hsum : (∑ v : V, G.degree v) + 3 ≤ 2 * Fintype.card V := by
    rw [← hnum, ← sum_add_distrib, mul_comm]
    calc
      (∑ v : V, (G.degree v + if v ∈ T then 1 else 0)) ≤ ∑ _v : V, 2 := by
        apply sum_le_sum
        intro v _
        by_cases hv : v ∈ T
        · have hv' : v = x ∨ v = y ∨ v = z := by simpa [T] using hv
          rcases hv' with rfl | rfl | rfl <;> simp only [if_pos hv] <;> omega
        · simp only [if_neg hv, add_zero]
          exact hd v
      _ = _ := by simp
  have hcard : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hc.card_vert_le_card_edgeSet_add_one
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  omega

private theorem component_degree_two_endpoints {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ v, G.degree v ≤ 2)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : G.degree x ≤ 1) (hy : G.degree y ≤ 1) (hz : G.degree z ≤ 1)
    (haxy : G.Reachable x y) (haxz : G.Reachable x z) : False := by
  classical
  let C := G.connectedComponentMk x
  have hmem (v : V) (hv : G.Reachable x v) : v ∈ C.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C v).mpr (SimpleGraph.ConnectedComponent.sound hv.symm)
  let x' : C.supp := ⟨x, hmem x SimpleGraph.Reachable.rfl⟩
  let y' : C.supp := ⟨y, hmem y haxy⟩
  let z' : C.supp := ⟨z, hmem z haxz⟩
  let J := C.toSimpleGraph
  have hsub (v : C.supp) : J.degree v ≤ G.degree v := by
    rw [SimpleGraph.degree, SimpleGraph.degree]
    exact card_le_card_of_injOn (fun w : C.supp => w.val)
      (fun w hw => by
        apply mem_coe.mpr
        apply (G.mem_neighborFinset v.val w.val).mpr
        exact (J.mem_neighborFinset v w).mp (mem_coe.mp hw))
      Subtype.val_injective.injOn
  exact connected_degree_two_endpoints J C.connected_toSimpleGraph
    (fun v => (hsub v).trans (hd v.val))
    (x := x') (y := y') (z := z')
    (fun h => hxy (congrArg Subtype.val h))
    (fun h => hxz (congrArg Subtype.val h))
    (fun h => hyz (congrArg Subtype.val h))
    ((hsub x').trans hx) ((hsub y').trans hy) ((hsub z').trans hz)

private abbrev Missing {n : ℕ} {C : Type} (L : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → C) (x : Fin n) (a : C) : Prop :=
  ∀ A ∈ L, x ∈ A → c A ≠ a

private theorem proper_insert_free {n : ℕ} {C : Type} {L : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → C} {A : Finset (Fin n)} {a : C} (hc : ProperOn L c)
    (ha : ∀ B ∈ L, (A ∩ B).Nonempty → c B ≠ a) :
    ProperOn (insert A L) (Function.update c A a) := by
  intro B hB D hD hBD hmeet
  by_cases hBA : B = A
  · subst B
    have hDL := (mem_insert.mp hD).resolve_left hBD.symm
    simpa only [Function.update_self, Function.update_of_ne hBD.symm] using (ha D hDL hmeet).symm
  by_cases hDA : D = A
  · subst D
    have hBL := (mem_insert.mp hB).resolve_left hBA
    have hm : (A ∩ B).Nonempty := by rwa [inter_comm]
    simpa only [Function.update_of_ne hBA, Function.update_self] using ha B hBL hm
  simpa only [Function.update_of_ne hBA, Function.update_of_ne hDA] using
    hc B ((mem_insert.mp hB).resolve_left hBA) D ((mem_insert.mp hD).resolve_left hDA) hBD hmeet

private theorem pair_free_extension {n : ℕ} {C : Type} {L : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → C} {x y : Fin n} {a : C} (hA : {x,y} ∈ L)
    (hc : ProperOn (L.erase {x,y}) c)
    (hx : Missing (L.erase {x,y}) c x a) (hy : Missing (L.erase {x,y}) c y a) :
    ∃ d : Finset (Fin n) → C, ProperOn L d := by
  rw [← insert_erase hA]
  refine ⟨Function.update c {x,y} a, proper_insert_free hc ?_⟩
  intro B hB hmeet
  obtain ⟨z, hz⟩ := hmeet
  have he : z = x ∨ z = y := by simpa using (mem_inter.mp hz).1
  rcases he with rfl | rfl
  · exact hx B hB (mem_inter.mp hz).2
  · exact hy B hB (mem_inter.mp hz).2

private theorem move_pair_gap {n : ℕ} {C : Type} {L : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → C} {x y z : Fin n} (hA : {x,y} ∈ L) (hB : {x,z} ∈ L.erase {x,y})
    (hc : ProperOn (L.erase {x,y}) c)
    (hy : Missing (L.erase {x,y}) c y (c {x,z})) :
    ProperOn (L.erase {x,z}) (Function.update c {x,y} (c {x,z})) := by
  let F := (L.erase ({x,y} : Finset (Fin n))).erase {x,z}
  have hi : insert {x,y} F = L.erase {x,z} := by
    ext E
    simp only [F, mem_insert, mem_erase]
    have hn := (mem_erase.mp hB).1
    constructor
    · rintro (rfl | ⟨hE, _, hEL⟩)
      · exact ⟨hn.symm, hA⟩
      · exact ⟨hE, hEL⟩
    · intro hE
      by_cases he : E = {x,y}
      · exact Or.inl he
      · exact Or.inr ⟨hE.1, he, hE.2⟩
  rw [← hi]
  apply proper_insert_free (A := {x,y})
  · intro A hAF B hBF
    exact hc A (mem_of_mem_erase hAF) B (mem_of_mem_erase hBF)
  · intro E hE hm
    obtain ⟨w, hw⟩ := hm
    have hw' : w = x ∨ w = y := by simpa using (mem_inter.mp hw).1
    rcases hw' with rfl | rfl
    · exact hc E (mem_of_mem_erase hE) {w,z} hB (mem_erase.mp hE).1
        ⟨w, mem_inter.mpr ⟨(mem_inter.mp hw).2, by simp⟩⟩
    · exact hy E (mem_of_mem_erase hE) (mem_inter.mp hw).2

private abbrev FanStep {n : ℕ} {C : Type} (F : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → C) (x u v : Fin n) : Prop :=
  {x,v} ∈ F ∧ Missing F c u (c {x,v})

/-- Move the uncoloured pair along a fan and fill the final gap with a
    colour missing at the centre and at the last vertex. -/
private theorem color_of_fan {n : ℕ} {C : Type} {L : Finset (Finset (Fin n))}
    (x : Fin n) (l : List (Fin n)) {y : Fin n} {c : Finset (Fin n) → C} {a : C}
    (hA : {x,y} ∈ L) (hxy : y ≠ x) (hx : x ∉ l) (hN : (y :: l).Nodup)
    (hc : ProperOn (L.erase {x,y}) c)
    (hchain : (y :: l).IsChain (FanStep (L.erase {x,y}) c x))
    (hcenter : Missing (L.erase {x,y}) c x a)
    (hfinal : Missing (L.erase {x,y}) c (l.getLastD y) a) :
    ∃ d : Finset (Fin n) → C, ProperOn L d := by
  induction l generalizing y c with
  | nil => exact pair_free_extension hA hc hcenter hfinal
  | cons z l ih =>
    obtain ⟨hfirst, hchain'⟩ := List.isChain_cons_cons.mp hchain
    obtain ⟨hz, hmiss⟩ := hfirst
    let d := Function.update c ({x,y} : Finset (Fin n)) (c {x,z})
    have hd := move_pair_gap hA hz hc hmiss
    have hz' : z ≠ x := fun he => hx (by simp [he])
    have htail := (List.nodup_cons.mp hN).2
    have hyn : y ∉ z :: l := (List.nodup_cons.mp hN).1
    have hnq (q : Fin n) (hq : q ∈ z :: l) : {x,q} ≠ ({x,y} : Finset (Fin n)) :=
      fun he => hyn (pair_label_inj x hxy he.symm ▸ hq)
    have hpreserve (v : Fin n) (hvx : v ≠ x) (hvy : v ≠ y) (b : C)
        (hb : Missing (L.erase {x,y}) c v b) :
        Missing (L.erase {x,z}) d v b := by
      intro E hE hvE
      have hE' : E ≠ ({x,y} : Finset (Fin n)) := by
        rintro rfl
        simp [hvx, hvy] at hvE
      simpa only [d, Function.update_of_ne hE'] using
        hb E (mem_erase.mpr ⟨hE', mem_of_mem_erase hE⟩) hvE
    refine ih (y := z) (c := d) (mem_of_mem_erase hz) hz'
      (fun h => hx (List.mem_cons_of_mem _ h)) htail hd ?_ ?_ ?_
    · apply hchain'.imp_of_mem_tail_imp
      intro u v hu hv huv
      have hv' := List.mem_cons_of_mem z hv
      obtain ⟨hvE, hmiss'⟩ := huv
      have hvz : v ≠ z := fun he => (List.nodup_cons.mp htail).1 (he ▸ hv)
      have hvE' : {x,v} ≠ ({x,z} : Finset (Fin n)) := fun he =>
        hvz (pair_label_inj x (fun he' => hx (he' ▸ hv')) he)
      have huX : u ≠ x := fun he => hx (he ▸ hu)
      have huY : u ≠ y := fun he => hyn (he ▸ hu)
      refine ⟨mem_erase.mpr ⟨hvE', mem_of_mem_erase hvE⟩, ?_⟩
      simpa only [d, Function.update_of_ne (hnq v hv')] using
        hpreserve u huX huY (c {x,v}) hmiss'
    · intro E hE hxE
      by_cases hE' : E = ({x,y} : Finset (Fin n))
      · subst E
        simpa only [d, Function.update_self] using hcenter {x,z} hz (by simp)
      · simpa only [d, Function.update_of_ne hE'] using
          hcenter E (mem_erase.mpr ⟨hE', mem_of_mem_erase hE⟩) hxE
    · rw [List.getLastD_cons] at hfinal
      have hv : l.getLastD z ∈ z :: l := List.getLastD_mem_cons
      exact hpreserve _ (fun he => hx (he ▸ hv)) (fun he => hyn (he ▸ hv)) a hfinal

private def twoColorPairGraph {n : ℕ} {C : Type} (F : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → C) (a b : C) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ {x,y} ∈ F ∧ (c {x,y} = a ∨ c {x,y} = b)
  symm := ⟨by
    intro x y h
    rcases h with ⟨hxy, hF, hc⟩
    rw [pair_comm y x]
    exact ⟨hxy.symm, hF, hc⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance {n : ℕ} {C : Type} [DecidableEq C] (F : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → C) (a b : C) : DecidableRel (twoColorPairGraph F c a b).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ {x,y} ∈ F ∧ (c {x,y} = a ∨ c {x,y} = b)))

private theorem two_color_degree_le {n : ℕ} {C : Type} [DecidableEq C]
    {F : Finset (Finset (Fin n))} {c : Finset (Fin n) → C} (hc : ProperOn F c) (a b : C)
    (x : Fin n) (T : Finset C)
    (ht : ∀ y, (twoColorPairGraph F c a b).Adj x y → c {x,y} ∈ T) :
    (twoColorPairGraph F c a b).degree x ≤ T.card := by
  classical
  let J := twoColorPairGraph F c a b
  change J.degree x ≤ T.card
  rw [SimpleGraph.degree]
  apply card_le_card_of_injOn (fun y : Fin n => c {x,y})
  · intro y hy
    exact mem_coe.mpr (ht y ((J.mem_neighborFinset x y).mp (mem_coe.mp hy)))
  · intro y hy z hz he
    have ha : x ≠ y ∧ {x,y} ∈ F ∧ (c {x,y} = a ∨ c {x,y} = b) :=
      (J.mem_neighborFinset x y).mp (mem_coe.mp hy)
    have hb : x ≠ z ∧ {x,z} ∈ F ∧ (c {x,z} = a ∨ c {x,z} = b) :=
      (J.mem_neighborFinset x z).mp (mem_coe.mp hz)
    apply pair_label_inj x ha.1.symm
    by_contra hn
    exact hc _ ha.2.1 _ hb.2.1 hn ⟨x, by simp⟩ he

private theorem two_color_max_degree {n : ℕ} {C : Type} [DecidableEq C]
    {F : Finset (Finset (Fin n))} {c : Finset (Fin n) → C} (hc : ProperOn F c)
    (a b : C) (x : Fin n) : (twoColorPairGraph F c a b).degree x ≤ 2 := by
  have h := two_color_degree_le hc a b x ({a,b} : Finset C) (by
    intro y hy
    simpa using hy.2.2)
  exact h.trans (card_insert_le _ _ |>.trans (by simp))

private theorem two_color_endpoint {n : ℕ} {C : Type} [DecidableEq C]
    {F : Finset (Finset (Fin n))} {c : Finset (Fin n) → C} (hc : ProperOn F c)
    (a b : C) (x : Fin n) (hx : Missing F c x a ∨ Missing F c x b) :
    (twoColorPairGraph F c a b).degree x ≤ 1 := by
  rcases hx with hx | hx
  · simpa using two_color_degree_le hc a b x ({b} : Finset C) (by
      intro y hy
      exact mem_singleton.mpr (hy.2.2.resolve_left (hx _ hy.2.1 (by simp))))
  · simpa using two_color_degree_le hc a b x ({a} : Finset C) (by
      intro y hy
      exact mem_singleton.mpr (hy.2.2.resolve_right (hx _ hy.2.1 (by simp))))

private theorem reachable_across_two_color_pair {n : ℕ} {C : Type}
    {F : Finset (Finset (Fin n))} {c : Finset (Fin n) → C} {a b : C}
    {E : Finset (Fin n)} (hE : E ∈ F) (hcard : E.card = 2)
    (hcol : c E = a ∨ c E = b) {r x y : Fin n} (hx : x ∈ E) (hy : y ∈ E)
    (hreach : (twoColorPairGraph F c a b).Reachable r x) :
    (twoColorPairGraph F c a b).Reachable r y := by
  by_cases hxy : x = y
  · simpa only [hxy] using hreach
  have he : E = {x,y} := by
    apply (eq_of_subset_of_card_le (insert_subset hx (singleton_subset_iff.mpr hy)) ?_).symm
    rw [card_pair hxy, hcard]
  subst E
  exact hreach.trans (SimpleGraph.Adj.reachable ⟨hxy, hE, hcol⟩)

open Classical in
private noncomputable def kempeColor {n : ℕ} {C : Type} (F : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → C) (a b : C) (r : Fin n) (E : Finset (Fin n)) : C :=
  if ∃ x ∈ E, (twoColorPairGraph F c a b).Reachable r x then
    Equiv.swap a b (c E) else c E

private theorem proper_kempe_color {n : ℕ} {C : Type}
    {F : Finset (Finset (Fin n))} {c : Finset (Fin n) → C}
    (hc : ProperOn F c) (hsize : ∀ E ∈ F, E.card = 2) (a b : C) (r : Fin n) :
    ProperOn F (kempeColor F c a b r) := by
  classical
  let J := twoColorPairGraph F c a b
  let S := F.filter (fun E => ∃ x ∈ E, J.Reachable r x)
  have hc' := proper_swap_colors (S := S) hc a b (by
    intro A hA hAS B hB hBS hmeet hcol
    obtain ⟨v, hvA, hv⟩ := (mem_filter.mp hAS).2
    obtain ⟨w, hw⟩ := hmeet
    obtain ⟨hwA, hwB⟩ := mem_inter.mp hw
    have hAw : J.Reachable r w := reachable_across_two_color_pair hA (hsize A hA)
      (hcol.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)) hvA hwA hv
    exact hBS (mem_filter.mpr ⟨hB, w, hwB, hAw⟩))
  intro A hA B hB hne hmeet
  simpa only [kempeColor, S, J, mem_filter, hA, hB, true_and] using hc' A hA B hB hne hmeet

private theorem kempe_color_far {n : ℕ} {C : Type}
    {F : Finset (Finset (Fin n))} {c : Finset (Fin n) → C} {a b : C}
    {r v : Fin n} (hv : ¬ (twoColorPairGraph F c a b).Reachable r v)
    {E : Finset (Fin n)} (hE : E ∈ F) (hsize : E.card = 2) (hvE : v ∈ E) :
    kempeColor F c a b r E = c E := by
  classical
  by_cases ha : c E = a
  · have hno : ¬ ∃ x ∈ E, (twoColorPairGraph F c a b).Reachable r x := by
      rintro ⟨x, hx, hr⟩
      exact hv (reachable_across_two_color_pair hE hsize (Or.inl ha) hx hvE hr)
    simp only [kempeColor, if_neg hno]
  by_cases hb : c E = b
  · have hno : ¬ ∃ x ∈ E, (twoColorPairGraph F c a b).Reachable r x := by
      rintro ⟨x, hx, hr⟩
      exact hv (reachable_across_two_color_pair hE hsize (Or.inr hb) hx hvE hr)
    simp only [kempeColor, if_neg hno]
  simp [kempeColor, Equiv.swap_apply_of_ne_of_ne ha hb]

private theorem kempe_color_missing_other {n : ℕ} {C : Type}
    {F : Finset (Finset (Fin n))} {c : Finset (Fin n) → C} {a b d : C}
    {r v : Fin n} (ha : d ≠ a) (hb : d ≠ b)
    (hmiss : Missing F c v d) : Missing F (kempeColor F c a b r) v d := by
  classical
  intro E hE hvE
  unfold kempeColor
  split
  · intro he
    have he' := congrArg (Equiv.swap a b) he
    simpa only [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne ha hb] using
      (hmiss E hE hvE (by simpa [Equiv.swap_apply_of_ne_of_ne ha hb] using he'))
  · exact hmiss E hE hvE

private theorem kempe_color_missing_at_root {n : ℕ} {C : Type}
    {F : Finset (Finset (Fin n))} {c : Finset (Fin n) → C} {a b : C}
    {r : Fin n} (hmiss : Missing F c r b) : Missing F (kempeColor F c a b r) r a := by
  classical
  intro E hE hr
  have he : ∃ x ∈ E, (twoColorPairGraph F c a b).Reachable r x :=
    ⟨r, hr, SimpleGraph.Reachable.rfl⟩
  simp only [kempeColor, if_pos he]
  intro he
  apply hmiss E hE hr
  simpa using congrArg (Equiv.swap a b) he

private theorem getLast_cons_eq_getLastD {α : Type*} (l : List α) (a : α) :
    (a :: l).getLast? = some (l.getLastD a) := by
  have h := List.getLast?_eq_some_getLast (l := a :: l) (by simp)
  rw [← List.getLastD_cons (a := a)]
  simp [List.getLastD_eq_getLast?, h]

private theorem maximal_color_fan {n : ℕ} {C : Type} (F : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → C) {x y : Fin n} (hxy : y ≠ x) :
    ∃ l : List (Fin n), x ∉ y :: l ∧ (y :: l).Nodup ∧
      (y :: l).IsChain (FanStep F c x) ∧
      ∀ z, z ≠ x → FanStep F c x (l.getLastD y) z → z ∈ y :: l := by
  classical
  let P (k : ℕ) := ∃ l : List (Fin n), (y :: l).length = k ∧
    x ∉ y :: l ∧ (y :: l).Nodup ∧ (y :: l).IsChain (FanStep F c x)
  have hp : P 1 := ⟨[], rfl, by simpa using hxy.symm, by simp, by simp⟩
  have hn : 1 ≤ n := by have := x.isLt; omega
  obtain ⟨l, hk, hx, hN, hchain⟩ := Nat.findGreatest_spec (P := P) hn hp
  refine ⟨l, hx, hN, hchain, ?_⟩
  intro z hzx hs
  by_contra hz
  have hnew : (y :: (l ++ [z])).Nodup := by
    rw [← List.cons_append]
    apply List.Nodup.append hN (by simp)
    intro u hu hv
    have he : u = z := by simpa using hv
    exact hz (he ▸ hu)
  have hnewchain : (y :: (l ++ [z])).IsChain (FanStep F c x) := by
    rw [← List.cons_append]
    apply hchain.append (by simp)
    intro u hu v hv
    rw [getLast_cons_eq_getLastD] at hu
    have hu' : u = l.getLastD y := by simpa [eq_comm] using hu
    have hv' : v = z := by simpa [eq_comm] using hv
    simpa only [hu', hv'] using hs
  have hbound : (y :: (l ++ [z])).length ≤ n := by simpa using hnew.length_le_card
  have hlarge : Nat.findGreatest P n < (y :: (l ++ [z])).length := by
    simp only [List.length_cons, List.length_append] at hk ⊢
    omega
  exact Nat.findGreatest_is_greatest hlarge hbound
    ⟨l ++ [z], rfl, by simpa [hzx.symm] using hx, hnew, hnewchain⟩

private theorem exists_missing_color {n m : ℕ} {F : Finset (Finset (Fin n))}
    (c : Finset (Fin n) → Fin m) (x : Fin n) (h : (F.filter (fun A => x ∈ A)).card < m) :
    ∃ a, Missing F c x a := by
  let U := (F.filter (fun A => x ∈ A)).image c
  have hu : U.card < m := card_image_le.trans_lt h
  have hn : ((univ : Finset (Fin m)) \ U).Nonempty := by
    apply card_pos.mp
    rwa [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, Nat.sub_pos_iff_lt]
  obtain ⟨a, ha⟩ := hn
  refine ⟨a, ?_⟩
  intro A hA hx hca
  exact (mem_sdiff.mp ha).2 (mem_image.mpr ⟨A, mem_filter.mpr ⟨hA, hx⟩, hca⟩)

private theorem vizing_pair_extension {n m : ℕ} {L : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → Fin m} {x y : Fin n} (hxy : y ≠ x) (hA : {x,y} ∈ L)
    (hc : ProperOn (L.erase {x,y}) c)
    (hsize : ∀ B ∈ L, B.card = 2)
    (hdeg : ∀ z : Fin n, ((L.erase {x,y}).filter (fun B => z ∈ B)).card < m) :
    ∃ d : Finset (Fin n) → Fin m, ProperOn L d := by
  classical
  let F := L.erase ({x,y} : Finset (Fin n))
  have hG (B : Finset (Fin n)) (hB : B ∈ F) : B.card = 2 := hsize B (mem_of_mem_erase hB)
  obtain ⟨a, ha⟩ := exists_missing_color (F := F) c x (hdeg x)
  obtain ⟨l, hxn, hN, hchain, hmax⟩ := maximal_color_fan F c hxy
  obtain ⟨b, hb⟩ := exists_missing_color (F := F) c (l.getLastD y) (hdeg _)
  have hxnl : x ∉ l := fun h => hxn (List.mem_cons_of_mem _ h)
  by_cases hfree : Missing F c x b
  · exact color_of_fan x l hA hxy hxnl hN hc hchain hfree hb
  have hE : ∃ B ∈ F, x ∈ B ∧ c B = b := by
    by_contra he
    apply hfree
    intro B hB hx hcol
    exact he ⟨B, hB, hx, hcol⟩
  obtain ⟨B, hB, hxB, hbB⟩ := hE
  obtain ⟨z, hzx, rfl⟩ := pair_of_mem_of_card_two hxB (hG B hB)
  have hzL := hmax z hzx ⟨hB, by rwa [hbB]⟩
  have hzy : z ≠ y := by
    intro he
    subst z
    exact (mem_erase.mp hB).1 rfl
  have hzl : z ∈ l := (List.mem_cons.mp hzL).resolve_left hzy
  obtain ⟨pre, post, rfl, _⟩ := List.eq_append_cons_of_mem hzl
  let p := pre.getLastD y
  let q := (pre ++ z :: post).getLastD y
  let J := twoColorPairGraph F c a b
  have hN' : ((y :: pre) ++ z :: post).Nodup := hN
  obtain ⟨hNp, hNz, hdj⟩ := List.nodup_append'.mp hN'
  have hpm : p ∈ y :: pre := List.getLastD_mem_cons
  have hq_eq : q = post.getLastD z := by
    have hlast : (pre ++ z :: post).getLast? = some (post.getLastD z) := by
      rw [List.getLast?_append, getLast_cons_eq_getLastD]
      rfl
    change (pre ++ z :: post).getLastD y = _
    simp only [List.getLastD_eq_getLast?, hlast, Option.getD_some]
  have hqm : q ∈ z :: post := hq_eq ▸ List.getLastD_mem_cons
  have hpq : p ≠ q := fun he => hdj hpm (he.symm ▸ hqm)
  have hpx : p ≠ x := fun he => hxn (show x ∈ (y :: pre) ++ z :: post from List.mem_append_left _ (he ▸ hpm))
  have hqx : q ≠ x := fun he => hxn (show x ∈ (y :: pre) ++ z :: post from List.mem_append_right (y :: pre) (he ▸ hqm))
  have hchain' : ((y :: pre) ++ z :: post).IsChain (FanStep F c x) := hchain
  obtain ⟨hpre, hpost, hlink⟩ := List.isChain_append.mp hchain'
  have hstep : FanStep F c x p z :=
    hlink p (by simp [getLast_cons_eq_getLastD, p]) z (by simp)
  have hbp : Missing F c p b := by simpa only [hbB] using hstep.2
  have hpEnd : J.degree p ≤ 1 := two_color_endpoint hc a b p (Or.inr hbp)
  have hqEnd : J.degree q ≤ 1 := two_color_endpoint hc a b q (Or.inr hb)
  have hxEnd : J.degree x ≤ 1 := two_color_endpoint hc a b x (Or.inl ha)
  have hkeep_step (r u v : Fin n) (hvz : v ≠ z) (hs : FanStep F c x u v) :
      FanStep F (kempeColor F c a b r) x u v := by
    have ha' : c {x,v} ≠ a := ha _ hs.1 (by simp)
    have hb' : c {x,v} ≠ b := by
      intro he
      have hn : {x,v} ≠ ({x,z} : Finset (Fin n)) := fun he' =>
        hvz ((pair_label_inj x hzx he'.symm).symm)
      exact hc _ hs.1 _ hB hn ⟨x, by simp⟩ (he.trans hbB.symm)
    have hcol : kempeColor F c a b r {x,v} = c {x,v} := by
      unfold kempeColor
      split
      · exact @Equiv.swap_apply_of_ne_of_ne (Fin m) (Classical.decEq _) a b _ ha' hb'
      · rfl
    refine ⟨hs.1, ?_⟩
    rw [hcol]
    exact kempe_color_missing_other ha' hb' hs.2
  have hpre_swap (r : Fin n) : (y :: pre).IsChain (FanStep F (kempeColor F c a b r) x) := by
    apply hpre.imp_of_mem_imp
    intro u v hu hv huv
    exact hkeep_step r u v (fun he => hdj hv (by simp [he])) huv
  have hcenter (r : Fin n) (hr : ¬ J.Reachable r x) :
      Missing F (kempeColor F c a b r) x a := by
    intro E hE hxE
    rw [kempe_color_far hr hE (hG E hE) hxE]
    exact ha E hE hxE
  by_cases hxp : J.Reachable x p
  · have hqFar : ¬ J.Reachable q x := by
      intro h
      exact component_degree_two_endpoints J (two_color_max_degree hc a b)
        hpx.symm hqx.symm hpq hxEnd hpEnd hqEnd hxp h.symm
    have hpFar : ¬ J.Reachable q p := fun h => hqFar (h.trans hxp.symm)
    have hpost_swap : (z :: post).IsChain (FanStep F (kempeColor F c a b q) x) := by
      apply hpost.imp_of_mem_tail_imp
      intro u v hu hv huv
      exact hkeep_step q u v (fun he => (List.nodup_cons.mp hNz).1 (he ▸ hv)) huv
    have hnew : ((y :: pre) ++ z :: post).IsChain (FanStep F (kempeColor F c a b q) x) := by
      apply (hpre_swap q).append hpost_swap
      intro u hu v hv
      have hu' : u = p := by simpa [getLast_cons_eq_getLastD, p, eq_comm] using hu
      have hv' : v = z := by simpa [eq_comm] using hv
      subst u
      subst v
      refine ⟨hB, ?_⟩
      rw [kempe_color_far hqFar hB (hG _ hB) (by simp), hbB]
      intro E hE hpE
      rw [kempe_color_far hpFar hE (hG E hE) hpE]
      exact hbp E hE hpE
    exact color_of_fan x (pre ++ z :: post) hA hxy hxnl hN (proper_kempe_color hc hG a b q)
      hnew (hcenter q hqFar) (kempe_color_missing_at_root hb)
  · have hpFar : ¬ J.Reachable p x := fun h => hxp h.symm
    exact color_of_fan x pre hA hxy (fun h => hxnl (List.mem_append_left _ h)) hNp
      (proper_kempe_color hc hG a b p) (hpre_swap p) (hcenter p hpFar)
      (kempe_color_missing_at_root hbp)

/-- Vizing's bound for a family of pairs, expressed in the same edge format
    as the bounded-rank colouring problem. -/
private theorem color_pairs_of_degree_lt {n m : ℕ} (hm : 0 < m)
    (L : Finset (Finset (Fin n))) (hsize : ∀ A ∈ L, A.card = 2)
    (hdeg : ∀ x : Fin n, (L.filter (fun A => x ∈ A)).card < m) :
    ∃ c : Finset (Fin n) → Fin m, ProperOn L c := by
  classical
  induction L using Finset.strongInductionOn with
  | _ L ih =>
    by_cases hempty : L.Nonempty
    · obtain ⟨A, hA⟩ := hempty
      obtain ⟨x, hx⟩ := card_pos.mp (by rw [hsize A hA]; decide)
      obtain ⟨y, hxy, rfl⟩ := pair_of_mem_of_card_two hx (hsize A hA)
      have hsub := erase_subset ({x,y} : Finset (Fin n)) L
      have hD (z : Fin n) : (((L.erase {x,y}).filter fun B => z ∈ B)).card < m :=
        (card_le_card (filter_subset_filter _ hsub)).trans_lt (hdeg z)
      obtain ⟨c, hc⟩ := ih _ (erase_ssubset hA) (fun B hB => hsize B (hsub hB)) hD
      exact vizing_pair_extension hxy hA hc hsize hD
    · exact ⟨fun _ => ⟨0, hm⟩, fun A hA => (hempty ⟨A, hA⟩).elim⟩

private theorem meeting_blocks_bound {n D : ℕ} (H : Finset (Finset (Fin n)))
    (A : Finset (Fin n)) (hdeg : ∀ x : Fin n, (H.filter (fun B => x ∈ B)).card ≤ D) :
    (H.filter fun B => (A ∩ B).Nonempty).card ≤ A.card * D := by
  have he : H.filter (fun B => (A ∩ B).Nonempty) =
      A.biUnion (fun x => H.filter (fun B => x ∈ B)) := by
    ext B
    simp only [mem_filter, Finset.Nonempty, mem_inter, mem_biUnion]
    tauto
  rw [he]
  calc
    _ ≤ ∑ x ∈ A, (H.filter (fun B => x ∈ B)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ A, D := sum_le_sum (fun x _ => hdeg x)
    _ = _ := by simp

private theorem capped_greedy_coloring {n k R D s : ℕ} (H : Finset (Finset (Fin n)))
    (hk : 0 < k) (hbudget : H.card < s * (k - R * D))
    (hsize : ∀ A ∈ H, A.card ≤ R)
    (hdeg : ∀ x : Fin n, (H.filter (fun B => x ∈ B)).card ≤ D) :
    ∃ c : Finset (Fin n) → Fin k, ProperOn H c ∧
      ∀ i : Fin k, (H.filter (fun B => c B = i)).card ≤ s := by
  classical
  induction H using Finset.strongInductionOn with
  | _ H ih =>
    by_cases hH : H.Nonempty
    · obtain ⟨A, hA⟩ := hH
      let F := H.erase A
      have hsub : F ⊆ H := erase_subset _ _
      have hFD (x : Fin n) : (F.filter (fun B => x ∈ B)).card ≤ D :=
        (card_le_card (filter_subset_filter _ hsub)).trans (hdeg x)
      obtain ⟨c, hc, hcap⟩ := ih F (erase_ssubset hA)
        ((card_le_card hsub).trans_lt hbudget) (fun B hB => hsize B (hsub hB)) hFD
      let Used := (F.filter (fun B => (A ∩ B).Nonempty)).image c
      let T (i : Fin k) := F.filter fun B => c B = i
      let Full := (univ : Finset (Fin k)).filter fun i => s ≤ (T i).card
      have hu : Used.card ≤ R * D :=
        card_image_le.trans ((meeting_blocks_bound F A hFD).trans
          (Nat.mul_le_mul_right _ (hsize A hA)))
      have hdisj : (Full : Set (Fin k)).PairwiseDisjoint T := by
        intro i hi j hj hne
        apply disjoint_left.mpr
        intro B hBi hBj
        exact hne (((mem_filter.mp hBi).2).symm.trans (mem_filter.mp hBj).2)
      have hfull : s * Full.card ≤ H.card := by
        calc
          _ = ∑ _i ∈ Full, s := by simp [Nat.mul_comm]
          _ ≤ ∑ i ∈ Full, (T i).card :=
            sum_le_sum (fun i hi => (mem_filter.mp hi).2)
          _ = (Full.biUnion T).card := (card_biUnion hdisj).symm
          _ ≤ H.card := by
            apply card_le_card
            intro B hB
            obtain ⟨i, _, hBi⟩ := mem_biUnion.mp hB
            exact hsub (mem_filter.mp hBi).1
      have hlt : Full.card < k - R * D := by
        by_contra! h
        exact hbudget.not_ge ((Nat.mul_le_mul_left s h).trans hfull)
      have hforbidden : (Used ∪ Full).card < k := by
        have hh := card_union_le Used Full
        omega
      have hfree : ((univ : Finset (Fin k)) \ (Used ∪ Full)).Nonempty := by
        apply card_pos.mp
        rwa [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, Nat.sub_pos_iff_lt]
      obtain ⟨i, hi⟩ := hfree
      have hinU : i ∉ Used := fun h => (mem_sdiff.mp hi).2 (mem_union_left _ h)
      have hinF : i ∉ Full := fun h => (mem_sdiff.mp hi).2 (mem_union_right _ h)
      have hsmall : (T i).card < s := by
        by_contra! h
        exact hinF (mem_filter.mpr ⟨mem_univ _, h⟩)
      let f := Function.update c A i
      have hf : ProperOn H f := by
        rw [← insert_erase hA]
        apply proper_insert_free hc
        intro B hB hm hBi
        exact hinU (mem_image.mpr ⟨B, mem_filter.mpr ⟨hB, hm⟩, hBi⟩)
      refine ⟨f, hf, fun j => ?_⟩
      by_cases hji : j = i
      · subst j
        have hs : (H.filter (fun B => f B = i)) ⊆ insert A (T i) := by
          intro B hB
          obtain ⟨hBH, hcol⟩ := mem_filter.mp hB
          by_cases hBA : B = A
          · exact mem_insert.mpr (Or.inl hBA)
          · exact mem_insert.mpr (Or.inr (mem_filter.mpr
              ⟨mem_erase.mpr ⟨hBA, hBH⟩, by
                simpa only [f, Function.update_of_ne hBA] using hcol⟩))
        exact (card_le_card hs).trans ((card_insert_le _ _).trans (by omega))
      · have hs : (H.filter (fun B => f B = j)) ⊆ T j := by
          intro B hB
          obtain ⟨hBH, hcol⟩ := mem_filter.mp hB
          have hBA : B ≠ A := by
            rintro rfl
            exact hji (by simpa only [f, Function.update_self] using hcol.symm)
          exact mem_filter.mpr ⟨mem_erase.mpr ⟨hBA, hBH⟩, by
            simpa only [f, Function.update_of_ne hBA] using hcol⟩
        exact (card_le_card hs).trans (hcap j)
    · refine ⟨fun _ => ⟨0, hk⟩, fun A hA => (hH ⟨A, hA⟩).elim, ?_⟩
      rw [not_nonempty_iff_eq_empty.mp hH]
      simp

private def blockIncidences {n : ℕ} (H : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n) × Fin n) :=
  (H.product S).filter (fun p => p.2 ∈ p.1)

private theorem card_incidences_by_point {n : ℕ} (H : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    (blockIncidences H S).card = ∑ x ∈ S, (H.filter (fun A => x ∈ A)).card := by
  classical
  let T (x : Fin n) := (H.filter (fun A => x ∈ A)).image (fun A => (A, x))
  have he : S.biUnion T = blockIncidences H S := by
    ext ⟨A, x⟩
    simp [T, blockIncidences, and_assoc, and_left_comm]
    tauto
  have hdisj : (S : Set (Fin n)).PairwiseDisjoint T := by
    intro x hx y hy hxy
    apply disjoint_left.mpr
    intro ⟨A, z⟩ hz hz'
    simp [T] at hz hz'
    have hx' : x = z := hz.2
    have hy' : y = z := hz'.2
    exact hxy (hx'.trans hy'.symm)
  rw [← he, card_biUnion hdisj]
  apply sum_congr rfl
  intro x _
  exact card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

private theorem card_incidences_by_block {n : ℕ} (H : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    (blockIncidences H S).card = ∑ A ∈ H, (A ∩ S).card := by
  classical
  let T (A : Finset (Fin n)) := (A ∩ S).image (fun x => (A, x))
  have he : H.biUnion T = blockIncidences H S := by
    ext ⟨A, x⟩
    simp [T, blockIncidences, and_assoc, and_left_comm]
  have hdisj : (H : Set (Finset (Fin n))).PairwiseDisjoint T := by
    intro A hA B hB hAB
    apply disjoint_left.mpr
    intro ⟨D, x⟩ hDA hDB
    simp [T] at hDA hDB
    have ha : A = D := hDA.2
    have hb : B = D := hDB.2
    exact hAB (ha.trans hb.symm)
  rw [← he, card_biUnion hdisj]
  apply sum_congr rfl
  intro A _
  exact card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)

private theorem card_incidences_compl {n : ℕ} (H : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    (blockIncidences H (univ \ S)).card + (blockIncidences H S).card =
      (blockIncidences H univ).card := by
  have hdisj : Disjoint (blockIncidences H (univ \ S)) (blockIncidences H S) := by
    apply disjoint_left.mpr
    intro ⟨A, x⟩ h hx
    simp [blockIncidences] at h hx
    tauto
  rw [← card_union_of_disjoint hdisj]
  congr 1
  ext ⟨A, x⟩
  simp [blockIncidences]
  tauto

private theorem parity_omissions {n k : ℕ} (H : Finset (Finset (Fin n)))
    (covered : ℕ → Finset (Fin n))
    (heligible : ∀ i < k, k ≤ (blockIncidences H (univ \ covered i)).card) :
    ∃ omitted : ℕ → Finset (Fin n),
      (∀ i < k, (omitted i).card ≤ 1) ∧
      (∀ i < k, Even ((univ : Finset (Fin n)) \ (covered i ∪ omitted i)).card) ∧
      ∀ x : Fin n, ((range k).filter (fun i => x ∈ omitted i)).card ≤
        (H.filter (fun A => x ∈ A)).card := by
  classical
  let T (i : Fin k) := blockIncidences H (univ \ covered i.val)
  obtain ⟨f, hf, hT⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp (by
    intro I
    by_cases hI : I.Nonempty
    · obtain ⟨i, hi⟩ := hI
      have hl : I.card ≤ k := by simpa using card_le_univ I
      apply hl.trans ((heligible i.val i.isLt).trans (card_le_card ?_))
      exact fun p hp => mem_biUnion.mpr ⟨i, hi, hp⟩
    · rw [not_nonempty_iff_eq_empty.mp hI, card_empty]
      exact Nat.zero_le _)
  let omitted (i : ℕ) : Finset (Fin n) :=
    if hi : i < k then
      if Even ((univ : Finset (Fin n)) \ covered i).card then ∅ else {(f ⟨i, hi⟩).2}
    else ∅
  refine ⟨omitted, ?_, ?_, ?_⟩
  · intro i hi
    dsimp only [omitted]
    rw [dif_pos hi]
    split <;> simp
  · intro i hi
    let S := (univ : Finset (Fin n)) \ covered i
    dsimp only [omitted]
    rw [dif_pos hi]
    change Even (((univ : Finset (Fin n)) \ (covered i ∪
      if Even S.card then ∅ else {(f ⟨i,hi⟩).2})).card)
    by_cases he : Even S.card
    · simpa [if_pos he, S] using he
    · rw [if_neg he]
      have hx : (f ⟨i,hi⟩).2 ∈ S := by
        have h := hT ⟨i,hi⟩
        exact (mem_product.mp (mem_filter.mp h).1).2
      have hset : (univ : Finset (Fin n)) \ (covered i ∪ {(f ⟨i,hi⟩).2}) =
          S.erase (f ⟨i,hi⟩).2 := by
        ext x
        simp only [S, mem_sdiff, mem_union, mem_singleton, mem_erase]
        tauto
      rw [hset]
      have hc := card_erase_add_one hx
      rw [Nat.even_iff] at he ⊢
      omega
  · intro x
    let I := (range k).filter (fun i => x ∈ omitted i)
    let e (i : I) : Fin k := ⟨i.val, mem_range.mp (mem_filter.mp i.property).1⟩
    have hmem (i : I) : (f (e i)).2 = x := by
      have hi : i.val < k := (e i).isLt
      have hx := (mem_filter.mp i.property).2
      change x ∈ omitted i.val at hx
      dsimp only [omitted] at hx
      rw [dif_pos hi] at hx
      split at hx
      · simp at hx
      · exact (mem_singleton.mp hx).symm
    have hle : (univ : Finset I).card ≤ (blockIncidences H {x}).card := by
      apply card_le_card_of_injOn (fun i : I => f (e i))
      · intro i _
        have h := hT (e i)
        obtain ⟨hprod, hp⟩ := mem_filter.mp h
        exact mem_coe.mpr (mem_filter.mpr
          ⟨mem_product.mpr ⟨(mem_product.mp hprod).1, mem_singleton.mpr (hmem i)⟩, hp⟩)
      · intro i _ j _ h
        exact Subtype.ext (congrArg Fin.val (hf h))
    rw [card_incidences_by_point, sum_singleton, card_univ, Fintype.card_coe] at hle
    exact hle

private theorem large_degree_le_pair_deficit {n : ℕ} {K L : Finset (Finset (Fin n))}
    (hLK : L ⊆ K)
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (x : Fin n) :
    ((L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)).card ≤
      ((univ : Finset (Fin n)).filter
        (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card := by
  classical
  let I := (L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)
  have hex (A : I) : ∃ y : Fin n, y ≠ x ∧ y ∈ A.val := by
    have hx := (mem_filter.mp A.property).2
    have hA := (mem_filter.mp (mem_filter.mp A.property).1).2
    have hpos : 0 < (A.val.erase x).card := by
      rw [card_erase_of_mem hx]
      omega
    obtain ⟨y, hy⟩ := card_pos.mp hpos
    exact ⟨y, mem_erase.mp hy⟩
  choose f hf using hex
  have hA (A : I) : A.val ∈ K := hLK (mem_filter.mp (mem_filter.mp A.property).1).1
  have hx (A : I) : x ∈ A.val := (mem_filter.mp A.property).2
  rw [← Fintype.card_coe I, ← card_univ]
  apply card_le_card_of_injOn f
  · intro A _
    apply mem_coe.mpr
    refine mem_filter.mpr ⟨mem_univ _, (hf A).1, ?_⟩
    intro hp
    obtain ⟨hPL, hsize⟩ := mem_filter.mp hp
    have he := block_eq_of_pair hpair (hA A) (hLK hPL) (hf A).1.symm
      (hx A) (hf A).2 (by simp) (by simp)
    have hc := (mem_filter.mp (mem_filter.mp A.property).1).2
    rw [he, hsize] at hc
    omega
  · intro A _ B _ he
    exact Subtype.ext (block_eq_of_pair hpair (hA A) (hA B)
      (hf A).1.symm (hx A) (hf A).2 (hx B) (he.symm ▸ (hf B).2))

private theorem large_degree_le_excess {n : ℕ} (L : Finset (Finset (Fin n))) (x : Fin n) :
    ((L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)).card ≤
      ∑ A ∈ L.filter (fun A => x ∈ A), (A.card - 2) := by
  let I := (L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)
  have hsub : I ⊆ L.filter (fun A => x ∈ A) := by
    intro A hA
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hA).1).1, (mem_filter.mp hA).2⟩
  calc
    _ = ∑ _A ∈ I, 1 := by simp [I]
    _ ≤ ∑ A ∈ I, (A.card - 2) := by
      apply sum_le_sum
      intro A hA
      have h := (mem_filter.mp (mem_filter.mp hA).1).2
      omega
    _ ≤ _ := sum_le_sum_of_subset hsub

private theorem single_block_eligible {n : ℕ} (H : Finset (Finset (Fin n)))
    (hH : 2 ≤ H.card) (hsize : ∀ A ∈ H, 3 ≤ A.card)
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (A : Finset (Fin n)) (hA : A ∈ H) :
    H.card ≤ (blockIncidences H (univ \ A)).card := by
  rw [card_incidences_by_block]
  calc
    H.card ≤ (H.card - 1) * 2 := by omega
    _ = ∑ _B ∈ H.erase A, 2 := by simp [card_erase_of_mem hA]
    _ ≤ ∑ B ∈ H.erase A, (B ∩ (univ \ A)).card := by
      apply sum_le_sum
      intro B hB
      obtain ⟨hBA, hBH⟩ := mem_erase.mp hB
      have hb := hsize B hBH
      have hi := hlin B hBH A hA hBA
      have he : B ∩ (univ \ A) = B \ A := by
        ext x
        simp
      rw [he, card_sdiff, inter_comm A B]
      omega
    _ ≤ _ := sum_le_sum_of_subset (erase_subset A H)

private theorem precolor_large_blocks {n R D : ℕ} (H : Finset (Finset (Fin n)))
    (hH : 2 ≤ H.card)
    (hsize : ∀ A ∈ H, 3 ≤ A.card ∧ A.card ≤ R)
    (hdeg : ∀ x : Fin n, (H.filter (fun A => x ∈ A)).card ≤ D)
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) :
    ∃ k ≤ 6 * R * D + 1, ∃ c : Finset (Fin n) → ℕ,
      (∀ A ∈ H, c A < k) ∧ ProperOn H c ∧
      ∀ i < k, let S := (H.filter (fun A => c A = i)).biUnion id
        6 * S.card ≤ n + 6 * R ∧ k ≤ (blockIncidences H (univ \ S)).card := by
  classical
  let w := R * D
  have htotal : 3 * H.card ≤ (blockIncidences H univ).card := by
    rw [card_incidences_by_block]
    calc
      _ = ∑ _A ∈ H, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum (fun A hA => by simpa using (hsize A hA).1)
  have hIncBound (S : Finset (Fin n)) : (blockIncidences H S).card ≤ S.card * D := by
    rw [card_incidences_by_point]
    calc
      _ ≤ ∑ _x ∈ S, D := sum_le_sum (fun x _ => hdeg x)
      _ = _ := by simp
  have hnD : 3 * H.card ≤ n * D := htotal.trans (by simpa using hIncBound univ)
  have hDpos : 0 < D := by
    by_contra! hd
    have hzero : D = 0 := by omega
    rw [hzero, Nat.mul_zero] at hnD
    omega
  obtain ⟨A, hA⟩ := card_pos.mp (show 0 < H.card by omega)
  have hRpos : 0 < R := by have := hsize A hA; omega
  have hw : 0 < w := Nat.mul_pos hRpos hDpos
  by_cases hsmall : H.card ≤ 6 * R * D + 1
  · let e : H ≃ Fin H.card := Fintype.equivFinOfCardEq (by simp)
    let c (A : Finset (Fin n)) : ℕ := if hA : A ∈ H then (e ⟨A, hA⟩).val else 0
    have hcol (A : Finset (Fin n)) (hA : A ∈ H) : c A = (e ⟨A, hA⟩).val := by
      simp [c, hA]
    have hinj (A : Finset (Fin n)) (hA : A ∈ H) (B : Finset (Fin n)) (hB : B ∈ H)
        (he : c A = c B) : A = B := by
      rw [hcol A hA, hcol B hB] at he
      exact congrArg Subtype.val (e.injective (Fin.ext he))
    refine ⟨H.card, hsmall, c, fun B hB => by rw [hcol B hB]; exact (e ⟨B,hB⟩).isLt,
      fun A hA B hB hne _ he => hne (hinj A hA B hB he), ?_⟩
    intro i hi
    let T := H.filter (fun A => c A = i)
    by_cases ht : T.Nonempty
    · obtain ⟨B, hB⟩ := ht
      have hBH := (mem_filter.mp hB).1
      have hT : T = {B} := by
        ext A
        constructor
        · intro hA
          obtain ⟨hAH, hcA⟩ := mem_filter.mp hA
          exact mem_singleton.mpr (hinj A hAH B hBH (hcA.trans (mem_filter.mp hB).2.symm))
        · intro hA
          simpa only [mem_singleton.mp hA] using hB
      change 6 * (T.biUnion id).card ≤ n + 6 * R ∧
        H.card ≤ (blockIncidences H (univ \ T.biUnion id)).card
      simp only [hT, singleton_biUnion, id_eq]
      exact ⟨by have := (hsize B hBH).2; omega,
        single_block_eligible H hH (fun A hA => (hsize A hA).1) hlin B hBH⟩
    · change 6 * (T.biUnion id).card ≤ n + 6 * R ∧
        H.card ≤ (blockIncidences H (univ \ T.biUnion id)).card
      simp only [not_nonempty_iff_eq_empty.mp ht, biUnion_empty, sdiff_empty, card_empty]
      exact ⟨by omega, by omega⟩
  · let k := 6 * R * D + 1
    let s := H.card / (2 * w)
    have hk_eq : k = 6 * w + 1 := by dsimp [k, w]; ring
    have hk : 0 < k := by omega
    have hkh : k ≤ H.card := by dsimp only [k]; omega
    have h2w : 0 < 2 * w := by omega
    have hs : 0 < s := by
      apply Nat.div_pos
      · omega
      · exact h2w
    have hmod := Nat.mod_add_div H.card (2 * w)
    have hmod' := Nat.mod_lt H.card h2w
    change H.card % (2 * w) + (2 * w) * s = H.card at hmod
    have hlow : 2 * w * s ≤ H.card := by omega
    have hupper : H.card < 2 * w * (s + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hdiff : k - R * D = 5 * w + 1 := by change k - w = _; omega
    have hbudget : H.card < s * (k - R * D) := by
      rw [hdiff]
      have hm := Nat.mul_le_mul_left w (show 1 ≤ s by omega)
      nlinarith [hupper]
    obtain ⟨f, hf, hcap⟩ := capped_greedy_coloring H hk hbudget
      (fun A hA => (hsize A hA).2) hdeg
    let c (A : Finset (Fin n)) := (f A).val
    refine ⟨k, le_rfl, c, fun A _ => (f A).isLt,
      fun A hA B hB hn hi he => hf A hA B hB hn hi (Fin.ext he), ?_⟩
    intro i hi
    let T := H.filter (fun A => c A = i)
    let S := T.biUnion id
    have hT : T.card ≤ s := by
      have heq : T = H.filter (fun A => f A = ⟨i, hi⟩) := by
        ext A
        simp [T, c, Fin.ext_iff]
      rw [heq]
      exact hcap ⟨i, hi⟩
    have hS : S.card ≤ s * R := by
      calc
        _ ≤ ∑ A ∈ T, A.card := card_biUnion_le
        _ ≤ ∑ _A ∈ T, R := sum_le_sum (fun A hA => (hsize A (mem_filter.mp hA).1).2)
        _ = T.card * R := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hT
    have hSsmall : 6 * S.card ≤ n := by
      have hdense : (6 * (s * R)) * D ≤ n * D := by
        calc
          _ = 3 * (2 * w * s) := by dsimp [w]; ring
          _ ≤ 3 * H.card := Nat.mul_le_mul_left 3 hlow
          _ ≤ _ := hnD
      exact (Nat.mul_le_mul_left 6 hS).trans (Nat.le_of_mul_le_mul_right hdense hDpos)
    have hcovered : (blockIncidences H S).card ≤ H.card := by
      calc
        _ ≤ S.card * D := hIncBound S
        _ ≤ (s * R) * D := Nat.mul_le_mul_right _ hS
        _ ≤ H.card := by
          dsimp only [w] at hlow
          nlinarith
    have hcpl := card_incidences_compl H S
    change 6 * S.card ≤ n + 6 * R ∧ k ≤ (blockIncidences H (univ \ S)).card
    exact ⟨by omega, by omega⟩

/-- A bounded-rank linear family with an everywhere dense pair graph can be
    coloured exactly. The threshold leaves room to complete the larger
    block classes before applying the pair-graph degree bound. -/
private theorem color_bounded_dense_pairs {n R d : ℕ} {K L : Finset (Finset (Fin n))}
    (hn : 12 * (d + 6 * R * d + R + 2) ≤ n)
    (hLK : L ⊆ K)
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R)
    (hH : 2 ≤ (L.filter (fun A => 3 ≤ A.card)).card)
    (hd : ∀ x : Fin n, ((univ : Finset (Fin n)).filter
      (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card ≤ d) :
    ∃ c, Proper L c := by
  classical
  let G := L.filter (fun A => A.card = 2)
  let H := L.filter (fun A => 3 ≤ A.card)
  have hGH : Disjoint G H := by
    apply disjoint_left.mpr
    intro A hAG hAH
    have ha := (mem_filter.mp hAG).2
    have hb := (mem_filter.mp hAH).2
    omega
  have hUnion : G ∪ H = L := by
    ext A
    simp only [G, H, mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hA
      have hmin := (hsize A hA).1
      by_cases h₂ : A.card = 2
      · exact Or.inl ⟨hA, h₂⟩
      · exact Or.inr ⟨hA, by omega⟩
  have hsizeH (A : Finset (Fin n)) (hA : A ∈ H) : 3 ≤ A.card ∧ A.card ≤ R :=
    ⟨(mem_filter.mp hA).2, (hsize A (mem_filter.mp hA).1).2⟩
  have hlin (A : Finset (Fin n)) (hA : A ∈ H) (B : Finset (Fin n)) (hB : B ∈ H)
      (hab : A ≠ B) : (A ∩ B).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra hn
    exact hab (block_eq_of_pair hpair (hLK (mem_filter.mp hA).1) (hLK (mem_filter.mp hB).1) hn
      (mem_inter.mp hx).1 (mem_inter.mp hy).1 (mem_inter.mp hx).2 (mem_inter.mp hy).2)
  have hdegH (x : Fin n) : (H.filter (fun A => x ∈ A)).card ≤ d :=
    (large_degree_le_pair_deficit hLK hpair x).trans (hd x)
  obtain ⟨k, hk, f, hf, hfc, hclasses⟩ := precolor_large_blocks H hH hsizeH hdegH hlin
  let S (i : ℕ) := (H.filter (fun A => f A = i)).biUnion id
  obtain ⟨omitted, hcard, hparity, hcount⟩ :=
    parity_omissions (k := k) H S (fun i hi => (hclasses i hi).2)
  have hkn : k < n := by omega
  have hroom (i : ℕ) (hi : i < k) :
      4 * (d + i) ≤ ((univ : Finset (Fin n)) \ (S i ∪ omitted i)).card := by
    have hS : 6 * (S i).card ≤ n + 6 * R := (hclasses i hi).1
    have hO := hcard i hi
    have hu := card_union_le (S i) (omitted i)
    have hcompl := card_sdiff_add_card_eq_card (subset_univ (S i ∪ omitted i))
    rw [card_univ, Fintype.card_fin] at hcompl
    omega
  have hslack (x : Fin n) : ((G ∪ H).filter (fun A => x ∈ A)).card +
      ((range k).filter (fun i => x ∈ omitted i)).card < n := by
    rw [hUnion]
    have hv := point_rank_budget hpair hLK (fun A hA => (hsize A hA).1) x
    have hle := (hcount x).trans (large_degree_le_excess L x)
    omega
  rw [← hUnion]
  exact dense_coloring_of_pair_degree_coloring G H (fun A hA => (mem_filter.mp hA).2) hGH hkn
    f omitted hf hfc hd hroom hparity hslack
    (fun P hs hd => color_pairs_of_degree_lt (by omega) P hs hd)

/-- Adding exactly the uncovered pairs preserves the rank cap and all
    blocks of size at least three. -/
private theorem bounded_pair_completion {n R : ℕ} (L : Finset (Finset (Fin n)))
    (hR : 2 ≤ R)
    (hsize : ∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R)
    (hlin : ∀ A ∈ L, ∀ B ∈ L, ∀ ⦃x y : Fin n⦄,
      x ≠ y → x ∈ A → y ∈ A → x ∈ B → y ∈ B → A = B) :
    ∃ C, L ⊆ C ∧ (∀ A ∈ C, 2 ≤ A.card ∧ A.card ≤ R) ∧
      (∀ x y : Fin n, x ≠ y → ∃! A, A ∈ C ∧ x ∈ A ∧ y ∈ A) ∧
      C.filter (fun A => 3 ≤ A.card) = L.filter (fun A => 3 ≤ A.card) ∧
      (∀ x y : Fin n, x ≠ y → {x,y} ∉ C.filter (fun A => A.card = 2) →
        ∃ A ∈ L.filter (fun A => 3 ≤ A.card), x ∈ A ∧ y ∈ A) := by
  classical
  let H := L.filter (fun A => 3 ≤ A.card)
  let P := ((univ : Finset (Fin n)).powersetCard 2).filter
    (fun B => ∀ A ∈ H, ¬ B ⊆ A)
  let C := H ∪ P
  have hHL (A : Finset (Fin n)) (hA : A ∈ H) : A ∈ L := (mem_filter.mp hA).1
  have hP (B : Finset (Fin n)) : B ∈ P ↔ B.card = 2 ∧ ∀ A ∈ H, ¬ B ⊆ A := by
    simp [P, mem_powersetCard]
  have hLC : L ⊆ C := by
    intro B hB
    by_cases hBH : B ∈ H
    · exact mem_union_left _ hBH
    · have hbc : B.card = 2 := by
        have hlow := (hsize B hB).1
        by_contra hb
        exact hBH (mem_filter.mpr ⟨hB, by omega⟩)
      apply mem_union_right
      refine (hP B).mpr ⟨hbc, ?_⟩
      intro A hA hsub
      obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (show 1 < B.card by omega)
      have he := hlin B hB A (hHL A hA) hxy hx hy (hsub hx) (hsub hy)
      exact hBH (he.symm ▸ hA)
  have hsizeC (A : Finset (Fin n)) (hA : A ∈ C) : 2 ≤ A.card ∧ A.card ≤ R := by
    rcases mem_union.mp hA with hA | hA
    · exact hsize A (mem_filter.mp hA).1
    · simpa only [(hP A).mp hA |>.1] using And.intro (le_refl 2) hR
  have hCover (x y : Fin n) (hxy : x ≠ y) :
      ∃! A, A ∈ C ∧ x ∈ A ∧ y ∈ A := by
    let e : Finset (Fin n) := {x,y}
    have he₂ : e.card = 2 := card_pair hxy
    have heq (B : Finset (Fin n)) (hB : B ∈ P) (hx : x ∈ B) (hy : y ∈ B) : B = e :=
      (eq_of_subset_of_card_le (insert_subset hx (singleton_subset_iff.mpr hy))
        (le_of_eq (((hP B).mp hB).1.trans he₂.symm))).symm
    by_cases hc : ∃ A ∈ H, x ∈ A ∧ y ∈ A
    · obtain ⟨A, hA, hx, hy⟩ := hc
      refine ⟨A, ⟨mem_union_left _ hA, hx, hy⟩, ?_⟩
      rintro B ⟨hB, hxB, hyB⟩
      rcases mem_union.mp hB with hB | hB
      · exact hlin B (hHL B hB) A (hHL A hA) hxy hxB hyB hx hy
      · exact (((hP B).mp hB).2 A hA (heq B hB hxB hyB ▸
            insert_subset hx (singleton_subset_iff.mpr hy))).elim
    · have hp : e ∈ P := (hP e).mpr ⟨he₂, fun A hA hs => hc ⟨A, hA, hs (by simp [e]),
        hs (by simp [e])⟩⟩
      refine ⟨e, ⟨mem_union_right _ hp, by simp [e], by simp [e]⟩, ?_⟩
      rintro B ⟨hB, hxB, hyB⟩
      rcases mem_union.mp hB with hB | hB
      · exact (hc ⟨B, hB, hxB, hyB⟩).elim
      · exact heq B hB hxB hyB
  have hHC : C.filter (fun A => 3 ≤ A.card) = H := by
    ext A
    constructor
    · intro ha
      obtain ⟨hu, hr⟩ := mem_filter.mp ha
      rcases mem_union.mp hu with hm | hm
      · exact hm
      · have hh := ((hP A).mp hm).1
        omega
    · intro ha
      exact mem_filter.mpr ⟨mem_union_left _ ha, (mem_filter.mp ha).2⟩
  refine ⟨C, hLC, hsizeC, hCover, hHC, ?_⟩
  intro x y hxy hno
  by_contra hc
  have hs : ({x,y} : Finset (Fin n)) ∈ P := (hP _).mpr
    ⟨card_pair hxy, fun A hA hs => hc ⟨A, hA, hs (by simp), hs (by simp)⟩⟩
  exact hno (mem_filter.mpr ⟨mem_union_right _ hs, card_pair hxy⟩)

/-- Complete the family by adding uncovered pairs. A point of large-block
    degree at most D then misses at most D * (R - 1) pair neighbours. -/
private theorem color_of_sparse_large_blocks {n R D : ℕ} {K L : Finset (Finset (Fin n))}
    (hn : 12 * (D * (R - 1) + 6 * R * (D * (R - 1)) + R + 2) ≤ n)
    (hLK : L ⊆ K)
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R)
    (hH : 2 ≤ (L.filter (fun A => 3 ≤ A.card)).card)
    (hdeg : ∀ x : Fin n, ((L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)).card ≤ D) :
    ∃ c, Proper L c := by
  classical
  let H := L.filter (fun A => 3 ≤ A.card)
  have hR : 2 ≤ R := by
    have hH' : 2 ≤ H.card := hH
    obtain ⟨A, hA⟩ := card_pos.mp (show 0 < H.card by omega)
    exact (hsize A (mem_filter.mp hA).1).1.trans (hsize A (mem_filter.mp hA).1).2
  obtain ⟨C, hLC, hsizeC, hCover, hHC, hUncovered⟩ :=
    bounded_pair_completion L hR hsize (fun A hA B hB _ _ hxy hxA hyA hxB hyB =>
      block_eq_of_pair hpair (hLK hA) (hLK hB) hxy hxA hyA hxB hyB)
  have hDense (x : Fin n) : ((univ : Finset (Fin n)).filter
      (fun y => y ≠ x ∧ {x,y} ∉ C.filter (fun A => A.card = 2))).card ≤ D * (R - 1) := by
    let S := H.filter (fun A => x ∈ A)
    have hs : ((univ : Finset (Fin n)).filter
        (fun y => y ≠ x ∧ {x,y} ∉ C.filter (fun A => A.card = 2))) ⊆
        S.biUnion (fun A => A.erase x) := by
      intro y hy
      obtain ⟨hne, hno⟩ := (mem_filter.mp hy).2
      obtain ⟨A, hA, hx, hy⟩ := hUncovered x y hne.symm hno
      exact mem_biUnion.mpr ⟨A, mem_filter.mpr ⟨hA, hx⟩, mem_erase.mpr ⟨hne, hy⟩⟩
    calc
      _ ≤ (S.biUnion (fun A => A.erase x)).card := card_le_card hs
      _ ≤ ∑ A ∈ S, (A.erase x).card := card_biUnion_le
      _ ≤ ∑ _A ∈ S, (R - 1) := by
        apply sum_le_sum
        intro A hA
        have ha := (hsize A (mem_filter.mp (mem_filter.mp hA).1).1).2
        rw [card_erase_of_mem (mem_filter.mp hA).2]
        omega
      _ = S.card * (R - 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (hdeg x)
  obtain ⟨c, hc⟩ := color_bounded_dense_pairs (K := C) hn (Subset.rfl) hCover hsizeC
    (hHC.symm ▸ hH) hDense
  exact ⟨c, fun A hA B hB => hc A (hLC hA) B (hLC hB)⟩

private theorem pair_star_and_deficit {n : ℕ} (L : Finset (Finset (Fin n))) (x : Fin n) :
    ((L.filter (fun A => A.card = 2)).filter (fun A => x ∈ A)).card +
      ((univ : Finset (Fin n)).filter
        (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card = n - 1 := by
  classical
  let G := L.filter (fun A => A.card = 2)
  let U := (univ : Finset (Fin n)).erase x
  let S := U.filter (fun y => ({x,y} : Finset (Fin n)) ∈ G)
  have hS : S.image (fun y => ({x,y} : Finset (Fin n))) = G.filter (fun A => x ∈ A) := by
    ext A
    constructor
    · intro hA
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hA
      exact mem_filter.mpr ⟨(mem_filter.mp hy).2, by simp⟩
    · intro hA
      obtain ⟨hA, hx⟩ := mem_filter.mp hA
      obtain ⟨y, hy, rfl⟩ := pair_of_mem_of_card_two hx (mem_filter.mp hA).2
      exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_erase.mpr ⟨hy, mem_univ _⟩, hA⟩)
  have hcard := card_image_of_injOn (s := S) (f := fun y => ({x,y} : Finset (Fin n))) (by
    intro y hy z _ h
    have hne := (mem_erase.mp (mem_filter.mp (mem_coe.mp hy)).1).1
    exact pair_label_inj x hne h)
  rw [hS] at hcard
  have hpart := card_filter_add_card_filter_not (s := U)
    (fun y => ({x,y} : Finset (Fin n)) ∈ G)
  change S.card + (U.filter (fun y => ({x,y} : Finset (Fin n)) ∉ G)).card = U.card at hpart
  have hu : U.card = n - 1 := by
    simp [U, card_erase_of_mem (mem_univ x)]
  have heq : U.filter (fun y => ({x,y} : Finset (Fin n)) ∉ G) =
      (univ : Finset (Fin n)).filter (fun y => y ≠ x ∧ {x,y} ∉ G) := by
    ext y
    simp [U]
  rw [hcard, ← heq, hpart, hu]

/-- If a point lacks many pair neighbours, the total block degree there has
    at least half that much slack. -/
private theorem total_degree_lt_from_pair_deficit {n : ℕ} {K L : Finset (Finset (Fin n))}
    (hLK : L ⊆ K)
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ L, 2 ≤ A.card) (x : Fin n) :
    2 * (L.filter (fun A => x ∈ A)).card +
      ((univ : Finset (Fin n)).filter
        (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card ≤ 2 * (n - 1) := by
  let T := L.filter (fun A => x ∈ A)
  let G := (L.filter (fun A => A.card = 2)).filter (fun A => x ∈ A)
  let H := (L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)
  have hcover : G ∪ H = T := by
    ext A
    simp only [G, H, T, mem_union, mem_filter]
    constructor
    · rintro (⟨⟨hA, _⟩, hx⟩ | ⟨⟨hA, _⟩, hx⟩) <;> exact ⟨hA, hx⟩
    · rintro ⟨hA, hx⟩
      have ha := hsize A hA
      by_cases he : A.card = 2
      · exact Or.inl ⟨⟨hA, he⟩, hx⟩
      · exact Or.inr ⟨⟨hA, by omega⟩, hx⟩
  have hdisj : Disjoint G H := by
    apply disjoint_left.mpr
    intro A hg hh
    have h₂ := (mem_filter.mp (mem_filter.mp hg).1).2
    have h₃ := (mem_filter.mp (mem_filter.mp hh).1).2
    omega
  have hcount : T.card = G.card + H.card := by
    rw [← hcover, card_union_of_disjoint hdisj]
  have hbudget := point_rank_budget hpair hLK hsize x
  have hlarge := large_degree_le_excess L x
  have hstar := pair_star_and_deficit L x
  change T.card + _ ≤ _ at hbudget
  change H.card ≤ _ at hlarge
  change G.card + _ = _ at hstar
  change 2 * T.card + _ ≤ _
  omega

/-- The critical-family formulation is equivalent to eventual edge
    colourability of all bounded-rank linear families. -/
private theorem critical_hypothesis_iff_bounded_rank :
    OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1.H1 ↔
      ∀ R : ℕ, ∀ᶠ n in Filter.atTop, ∀ L : Finset (Finset (Fin n)),
        (∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R) →
        (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).card ≤ 1) →
        ∃ c, Proper L c := by
  classical
  constructor
  · intro h R
    filter_upwards [h R, Filter.eventually_gt_atTop (R * R)] with n hcrit hn
    intro L hsize hlin
    have : NeZero n := ⟨by omega⟩
    by_cases hR : 2 ≤ R
    · have hp (A : Finset (Fin n)) (hA : A ∈ L) (B : Finset (Fin n)) (hB : B ∈ L)
          ⦃i j : Fin n⦄ (hne : i ≠ j) (hiA : i ∈ A) (hjA : j ∈ A)
          (hiB : i ∈ B) (hjB : j ∈ B) : A = B := by
        by_contra h
        exact hne (card_le_one.mp (hlin A hA B hB h) i (mem_inter.mpr ⟨hiA, hiB⟩)
          j (mem_inter.mpr ⟨hjA, hjB⟩))
      obtain ⟨K, hLK, hKsize, hpair, _, _⟩ := bounded_pair_completion L hR hsize hp
      by_contra hbad
      have hbadK : ¬ ∃ c, Proper K c := by
        rintro ⟨c, hc⟩
        exact hbad ⟨c, fun A hA B hB => hc A (hLK hA) B (hLK hB)⟩
      obtain ⟨T, hTK, hT, hbadT, hcritical⟩ := exists_critical_subfamily hbadK
      have hbound (A : Finset (Fin n)) (hA : A ∈ K) : A.card * A.card < n :=
        (Nat.mul_le_mul (hKsize A hA).2 (hKsize A hA).2).trans_lt hn
      have hthree : ∃ A ∈ T, 3 ≤ A.card := by
        by_contra! h
        apply hbadT (color_two_blocks ?_)
        intro A hA
        have h₂ := (hKsize A (hTK hA)).1
        have h₃ := h A hA
        omega
      obtain ⟨A, hA⟩ := hT
      exact hcrit K T (fun B hB => ⟨(hKsize B hB).1, (hbound B hB).le⟩)
        hpair hTK (fun B hB => (hKsize B (hTK hB)).2) hbadT hcritical
        (fun _ _ _ => all_colors_blocked hbadT)
        hthree ⟨A, hA, hbound A (hTK hA)⟩
        (fun B hB h₂ => critical_pair_neighbor_card hpair hTK
          (fun E hE => (hKsize E hE).1) hB h₂ (hcritical B hB).2)
    · refine ⟨fun _ => 0, fun A hA => ?_⟩
      have hh := hsize A hA
      omega
  · intro h R
    filter_upwards [h R] with n hn
    intro K L hsize hpair hLK hR hbad _ _ _ _ _
    apply hbad (hn L (fun A hA => ⟨(hsize A (hLK hA)).1, hR A hA⟩) ?_)
    intro A hA B hB hAB
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hne
    exact hAB (block_eq_of_pair hpair (hLK hA) (hLK hB) hne
      (mem_inter.mp hi).1 (mem_inter.mp hj).1 (mem_inter.mp hi).2 (mem_inter.mp hj).2)

/-- A uniform positive pair deficit gives enough degree slack to use an
    asymptotic bounded-rank colouring bound. -/
private theorem color_of_uniform_pair_deficit_of_approx {n R q D₀ : ℕ}
    (hq : 2 ≤ q) (hn : 2 * D₀ ≤ n)
    (happrox : ∀ D : ℕ, D₀ ≤ D → ∀ H : Finset (Finset (Fin n)),
      (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ R) →
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ x : Fin n, (H.filter (fun A => x ∈ A)).card ≤ D) →
      ∃ c : Finset (Fin n) → Fin (D + D / q), ProperOn H c)
    {K L : Finset (Finset (Fin n))}
    (hLK : L ⊆ K)
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R)
    (hdeficit : ∀ x : Fin n, 2 * (n / q) ≤ ((univ : Finset (Fin n)).filter
      (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card) :
    ∃ c, Proper L c := by
  let D := n - n / q
  have hhalf : n / q * 2 ≤ n :=
    (Nat.mul_le_mul_left (n / q) hq).trans (Nat.div_mul_le_self n q)
  have hD₀ : D₀ ≤ D := by dsimp [D]; omega
  have hD : ∀ x : Fin n, (L.filter (fun A => x ∈ A)).card ≤ D := by
    intro x
    have hb := total_degree_lt_from_pair_deficit hLK hpair (fun A hA => (hsize A hA).1) x
    have hd := hdeficit x
    dsimp [D]
    omega
  have hlinear : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).card ≤ 1 := by
    intro A hA B hB hAB
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hne
    exact hAB (block_eq_of_pair hpair (hLK hA) (hLK hB) hne
      (mem_inter.mp hi).1 (mem_inter.mp hj).1 (mem_inter.mp hi).2 (mem_inter.mp hj).2)
  obtain ⟨c, hc⟩ := happrox D hD₀ L hsize hlinear hD
  have hfit : D + D / q ≤ n := by
    have hd : D ≤ n := Nat.sub_le _ _
    have hdiv : D / q ≤ n / q := Nat.div_le_div_right hd
    dsimp [D] at *
    omega
  refine ⟨fun A => Fin.castLE hfit (c A), ?_⟩
  intro A hA B hB hAB hmeet he
  have heq := congrArg (fun i : Fin n => i.val) he
  exact hc A hA B hB hAB hmeet (Fin.ext heq)

theorem OMA.solution : OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1.H1 := by
  classical
  intro R
  filter_upwards [Filter.eventually_gt_atTop (R * R),
    Filter.eventually_ge_atTop (12 * (R + 2))] with n hn hn'
  intro K L hsize hpair hLK hR hbad hcritical hblocked hthree hstrict hpairs
  have hbudget := point_rank_budget hpair hLK (fun B hB => (hsize B (hLK hB)).1)
  have hdegrees (x y : Fin n) (hxy : x ≠ y) (hA : {x, y} ∈ L) :
      n + 2 ≤ (L.filter (fun B => x ∈ B)).card + (L.filter (fun B => y ∈ B)).card := by
    have hlinear (B : Finset (Fin n)) (hB : B ∈ L) (hxB : x ∈ B) (hyB : y ∈ B) :
        B = {x, y} :=
      block_eq_of_pair hpair (hLK hB) (hLK hA) hxy hxB hyB (by simp) (by simp)
    have hcount := pair_neighborhood_card hA hlinear
    have := (hcritical {x, y} hA).2
    omega
  have : NeZero n := ⟨by omega⟩
  have hlargeMeet : ∃ A ∈ L, ∃ B ∈ L, A ≠ B ∧
      3 ≤ A.card ∧ 3 ≤ B.card ∧ (A ∩ B).Nonempty := by
    by_contra h
    apply hbad (color_disjoint_large_blocks hLK hpair (fun A hA => (hsize A (hLK hA)).1) ?_)
    intro A hA B hB hAB hA₃ hB₃
    apply disjoint_left.mpr
    intro x hxA hxB
    exact h ⟨A, hA, B, hB, hAB, hA₃, hB₃, x, mem_inter.mpr ⟨hxA, hxB⟩⟩
  have hH : 2 ≤ (L.filter (fun A => 3 ≤ A.card)).card := by
    obtain ⟨A, hA, B, hB, hab, hA3, hB3, _⟩ := hlargeMeet
    exact one_lt_card.mpr ⟨A, mem_filter.mpr ⟨hA, hA3⟩,
      B, mem_filter.mpr ⟨hB, hB3⟩, hab⟩
  by_cases hDense : ∃ d : ℕ, 12 * (d + 6 * R * d + R + 2) ≤ n ∧
      ∀ x : Fin n, ((univ : Finset (Fin n)).filter
        (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card ≤ d
  · obtain ⟨d, hd, hdeg⟩ := hDense
    exact hbad (color_bounded_dense_pairs hd hLK hpair
      (fun A hA => ⟨(hsize A (hLK hA)).1, hR A hA⟩) hH hdeg)
  · by_cases hSparse : ∃ D : ℕ,
        12 * (D * (R - 1) + 6 * R * (D * (R - 1)) + R + 2) ≤ n ∧
        ∀ x : Fin n, ((L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)).card ≤ D
    · obtain ⟨D, hD, hdeg⟩ := hSparse
      exact hbad (color_of_sparse_large_blocks hD hLK hpair
        (fun A hA => ⟨(hsize A (hLK hA)).1, hR A hA⟩) hH hdeg)
    · let d := (n - 12 * (R + 2)) / (12 * (6 * R + 1))
      let D := (n - 12 * (R + 2)) / (12 * (6 * R + 1) * (R - 1))
      have hDfit : 12 * (D * (R - 1) + 6 * R * (D * (R - 1)) + R + 2) ≤ n := by
        have hle := Nat.div_mul_le_self (n - 12 * (R + 2)) (12 * (6 * R + 1) * (R - 1))
        change D * (12 * (6 * R + 1) * (R - 1)) ≤ _ at hle
        calc
          _ = D * (12 * (6 * R + 1) * (R - 1)) + 12 * (R + 2) := by ring
          _ ≤ (n - 12 * (R + 2)) + 12 * (R + 2) := Nat.add_le_add_right hle _
          _ = n := Nat.sub_add_cancel hn'
      have hCongestion : ∃ x : Fin n,
          D < ((L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)).card := by
        by_contra! h
        exact hSparse ⟨D, hDfit, h⟩
      have hdfit : 12 * (d + 6 * R * d + R + 2) ≤ n := by
        have hle := Nat.div_mul_le_self (n - 12 * (R + 2)) (12 * (6 * R + 1))
        change d * (12 * (6 * R + 1)) ≤ _ at hle
        calc
          _ = d * (12 * (6 * R + 1)) + 12 * (R + 2) := by ring
          _ ≤ (n - 12 * (R + 2)) + 12 * (R + 2) := Nat.add_le_add_right hle _
          _ = n := Nat.sub_add_cancel hn'
      have hPairDeficit : ∃ x : Fin n, d < ((univ : Finset (Fin n)).filter
          (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card := by
        by_contra! h
        exact hDense ⟨d, hdfit, h⟩
      sorry
