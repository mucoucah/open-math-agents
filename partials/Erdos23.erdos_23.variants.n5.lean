import FormalConjectures.ErdosProblems.«23»

-- Problem: Erdős Problem 23 — n5
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/23.lean:80 (declaration Erdos23.erdos_23.variants.n5)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Reduction of the n = 5 case of Erdős Problem 23.
* `OMA23.cutG G S` keeps the edges of `G` crossing the vertex set `S`; it is bipartite and its
  deleted edges are exactly the edges of `G` with both ends on the same side of `S`.
* `OMA23.exists_half_cut`: averaging over all `2 ^ n` subsets, some cut keeps half the edges
  (settles at most 51 edges).
* `OMA23.dense_case`: the neighbourhood cut of the best vertex plus Cauchy-Schwarz settles at
  least 124 edges.
* `OMA23.sparse_ext`: for an edge uv, fix N(u) and N(v) on opposite sides and average over the
  rest; with a well-chosen edge this settles 52 to 60 edges.
* `OMA23.highdeg_case`: a vertex of degree at least 14 leaves at most 10 vertices outside its
  closed neighbourhood, so by Mantel (`CliqueFree.card_edgeFinset_le`) its cut deletes at most 25.
* `OMA23.exists_maximal_tf` / `OMA23.filter_mono_graph`: adding edges never helps, so it suffices
  to treat maximal triangle-free graphs (the class McKay enumerates).
* `OMA23.common_nbr_of_max`: in a maximal triangle-free graph any two non-adjacent vertices have
  a common neighbour (diameter at most 2).
* `OMA23.exists_edge_cut_full`: the edge cut keeps every edge between N(u) and N(v), so some cut
  deletes at most (m - e(N(u), N(v))) / 2 edges.
* `OMA23.middle_case` (maximal triangle-free, diameter 2, 61 to 123 edges, all degrees at most 13,
  and every neighbourhood cut and every edge cut fails) is the remaining, genuinely hard range.
* `OMA23.main_cut_of_literature` (second attempt): the whole statement follows from three
  computer-assisted inputs (dense range and sparse core on 25 vertices, two facts on 23
  vertices) by deleting two vertices of small degree; see `OMA23.del_vertex`, `OMA23.transfer`,
  `OMA23.two_del`.
-/

open SimpleGraph Finset

namespace OMA23

section
variable {V : Type} [Fintype V] [DecidableEq V]

def cutG (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ (u ∈ S ↔ v ∈ S)
  symm := ⟨fun u v h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
  loopless := ⟨fun u h => h.2 Iff.rfl⟩

lemma cutG_adj (G : SimpleGraph V) (S : Finset V) (u v : V) :
    (cutG G S).Adj u v ↔ (G.Adj u v ∧ ¬ (u ∈ S ↔ v ∈ S)) := Iff.rfl

lemma cutG_le (G : SimpleGraph V) (S : Finset V) : cutG G S ≤ G := fun _ _ h => h.1

lemma cutG_bip (G : SimpleGraph V) (S : Finset V) : (cutG G S).IsBipartite := by
  refine ⟨Coloring.mk (fun v => if v ∈ S then (0 : Fin 2) else 1) ?_⟩
  intro u v h
  have h2 := ((cutG_adj G S u v).1 h).2
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all

def Same (S : Finset V) (e : Sym2 V) : Prop := ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)

lemma same_mk (S : Finset V) (u v : V) : Same S s(u, v) ↔ (u ∈ S ↔ v ∈ S) := by
  unfold Same
  simp only [Sym2.mem_iff]
  constructor
  · intro h; exact h u (Or.inl rfl) v (Or.inr rfl)
  · rintro h x (rfl | rfl) y (rfl | rfl) <;> tauto

open scoped Classical in
lemma uncut_card (G : SimpleGraph V) (S : Finset V) [Fintype G.edgeSet] [Fintype (cutG G S).edgeSet]
    [DecidableEq (Sym2 V)] :
    (G.edgeFinset \ (cutG G S).edgeFinset).card = (G.edgeFinset.filter (Same S)).card := by
  congr 1
  ext e
  induction e using Sym2.ind with
  | h x y =>
    simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, Finset.mem_filter, same_mk,
      cutG_adj]
    tauto


lemma count_same_pair (u v : V) (huv : u ≠ v) :
    2 * ((univ : Finset (Finset V)).filter (fun S => (u ∈ S ↔ v ∈ S))).card
      = 2 ^ Fintype.card V := by
  have hAB : ((univ : Finset (Finset V)).filter (fun S => (u ∈ S ↔ v ∈ S))).card
      = ((univ : Finset (Finset V)).filter (fun S => ¬ (u ∈ S ↔ v ∈ S))).card := by
    apply Finset.card_nbij' (fun S => symmDiff S {u}) (fun S => symmDiff S {u})
    · intro S hS
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, huv.symm, not_true_eq_false,
        and_false, or_false, and_true, false_and]
      tauto
    · intro S hS
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, huv.symm, not_true_eq_false,
        and_false, or_false, and_true, false_and]
      tauto
    · intro S _
      simp [symmDiff_symmDiff_cancel_right]
    · intro S _
      simp [symmDiff_symmDiff_cancel_right]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Finset V))) (fun S => (u ∈ S ↔ v ∈ S))
  rw [Finset.card_univ, Fintype.card_finset] at hsum
  omega

open scoped Classical in
lemma exists_half_cut (G : SimpleGraph V) [Fintype G.edgeSet] :
    ∃ S : Finset V, 2 * (G.edgeFinset.filter (Same S)).card ≤ G.edgeFinset.card := by
  have key : ∑ S : Finset V, 2 * (G.edgeFinset.filter (Same S)).card
      = ∑ S : Finset V, G.edgeFinset.card := by
    have h1 : ∀ e ∈ G.edgeFinset,
        2 * ((univ : Finset (Finset V)).filter (fun S => Same S e)).card
          = 2 ^ Fintype.card V := by
      intro e he
      induction e using Sym2.ind with
      | h x y =>
        have hxy : x ≠ y := by
          rw [mem_edgeFinset, mem_edgeSet] at he
          exact he.ne
        simp only [same_mk]
        exact count_same_pair x y hxy
    calc ∑ S : Finset V, 2 * (G.edgeFinset.filter (Same S)).card
        = ∑ S : Finset V, ∑ e ∈ G.edgeFinset, 2 * (if Same S e then 1 else 0) := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.card_filter, Finset.mul_sum]
      _ = ∑ e ∈ G.edgeFinset, ∑ S : Finset V, 2 * (if Same S e then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ e ∈ G.edgeFinset, 2 ^ Fintype.card V := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          rw [← Finset.mul_sum, ← Finset.card_filter]
          exact h1 e he
      _ = ∑ S : Finset V, G.edgeFinset.card := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_finset,
            smul_eq_mul, smul_eq_mul, mul_comm]
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty key.le
  exact ⟨S, hS⟩


open scoped Classical in
lemma cut_card_nbhd (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (v : V) :
    (G.edgeFinset.filter (Same (G.neighborFinset v))).card
      + ∑ u ∈ G.neighborFinset v, G.degree u = G.edgeFinset.card := by
  have hind : ∀ a ∈ G.neighborFinset v, ∀ b ∈ G.neighborFinset v, ¬ G.Adj a b := by
    intro a ha b hb hab
    rw [mem_neighborFinset] at ha hb
    exact hG {v, a, b} (is3Clique_triple_iff.2 ⟨ha, hb, hab⟩)
  have h1 : G.edgeFinset.filter (fun e => ¬ Same (G.neighborFinset v) e)
      = (G.neighborFinset v).biUnion (fun u => G.incidenceFinset u) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, same_mk, Finset.mem_biUnion,
        mem_incidenceFinset, mk'_mem_incidenceSet_iff]
      constructor
      · rintro ⟨hxy, hn⟩
        by_cases hx : x ∈ G.neighborFinset v
        · exact ⟨x, hx, hxy, Or.inl rfl⟩
        · have hy : y ∈ G.neighborFinset v := by tauto
          exact ⟨y, hy, hxy, Or.inr rfl⟩
      · rintro ⟨u, hu, hxy, rfl | rfl⟩
        · exact ⟨hxy, fun hiff => hind _ hu _ (hiff.1 hu) hxy⟩
        · exact ⟨hxy, fun hiff => hind _ (hiff.2 hu) _ hu hxy⟩
  have h2 : ((G.neighborFinset v).biUnion (fun u => G.incidenceFinset u)).card
      = ∑ u ∈ G.neighborFinset v, G.degree u := by
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl (fun u _ => card_incidenceFinset_eq_degree G u)
    · intro a ha b hb hab
      show Disjoint (G.incidenceFinset a) (G.incidenceFinset b)
      rw [Finset.disjoint_left]
      intro e hea heb
      rw [mem_incidenceFinset] at hea heb
      have hsub := G.incidenceSet_inter_incidenceSet_subset hab ⟨hea, heb⟩
      rw [Set.mem_singleton_iff] at hsub
      have hadj : G.Adj a b := by
        have := hea.1
        rw [hsub, mem_edgeSet] at this
        exact this
      exact hind a ha b hb hadj
  have h3 := Finset.card_filter_add_card_filter_not
    (s := G.edgeFinset) (fun e => Same (G.neighborFinset v) e)
  rw [h1, h2] at h3
  exact h3

lemma sum_nbhd_deg (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, ∑ u ∈ G.neighborFinset v, G.degree u = ∑ u, G.degree u ^ 2 := by
  simp_rw [neighborFinset_eq_filter (G := G), Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, sq]
  congr 1
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  congr 1
  ext w
  simp [adj_comm]

end

open scoped Classical in
lemma dense_case (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hm : 124 ≤ G.edgeFinset.card) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  by_contra hcon
  push Not at hcon
  have hv : ∀ v, 26 + ∑ u ∈ G.neighborFinset v, G.degree u ≤ G.edgeFinset.card := by
    intro v
    have h1 := cut_card_nbhd G hG v
    have h2 := hcon (G.neighborFinset v)
    omega
  have hsum : ∑ v : Fin 25, (26 + ∑ u ∈ G.neighborFinset v, G.degree u)
      ≤ ∑ v : Fin 25, G.edgeFinset.card := Finset.sum_le_sum (fun v _ => hv v)
  rw [Finset.sum_add_distrib, sum_nbhd_deg] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 25)))
    (f := fun v => G.degree v)
  rw [sum_degrees_eq_twice_card_edges] at hcs
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_id] at hcs
  set M := G.edgeFinset.card
  set D := ∑ u, G.degree u ^ 2
  have hM : (124 : ℤ) ≤ M := by exact_mod_cast hm
  have h1 : (650 : ℤ) + D ≤ 25 * M := by exact_mod_cast hsum
  have h2 : (2 * (M : ℤ)) ^ 2 ≤ 25 * D := by exact_mod_cast hcs
  nlinarith [sq_nonneg ((M : ℤ) - 124)]



section
variable {V : Type} [Fintype V] [DecidableEq V]

def eside (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (T : Finset V) : Finset V :=
  (T ∪ G.neighborFinset u) \ G.neighborFinset v

lemma mem_eside (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (T : Finset V) (x : V) :
    x ∈ eside G u v T ↔ ((x ∈ T ∨ x ∈ G.neighborFinset u) ∧ x ∉ G.neighborFinset v) := by
  simp [eside]

lemma toggle_count (P : Finset V → Prop) [DecidablePred P] (x : V)
    (hP : ∀ T, P (symmDiff T {x}) ↔ ¬ P T) :
    2 * ((univ : Finset (Finset V)).filter P).card = 2 ^ Fintype.card V := by
  have hAB : ((univ : Finset (Finset V)).filter P).card
      = ((univ : Finset (Finset V)).filter (fun T => ¬ P T)).card := by
    apply Finset.card_nbij' (fun S => symmDiff S {x}) (fun S => symmDiff S {x})
    · intro S hS
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      rw [hP]
      exact not_not.mpr hS
    · intro S hS
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      rw [hP]
      exact hS
    · intro S _
      simp [symmDiff_symmDiff_cancel_right]
    · intro S _
      simp [symmDiff_symmDiff_cancel_right]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Finset V))) P
  rw [Finset.card_univ, Fintype.card_finset] at hsum
  omega

lemma nbhd_disj (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) {u v : V}
    (huv : G.Adj u v) (x : V) (hxu : x ∈ G.neighborFinset u) : x ∉ G.neighborFinset v := by
  intro hxv
  rw [mem_neighborFinset] at hxu hxv
  exact hG {u, v, x} (is3Clique_triple_iff.2 ⟨huv, hxu, hxv⟩)

open scoped Classical in
lemma edge_count (G : SimpleGraph V) [DecidableRel G.Adj] (u v x y : V) (hxy : x ≠ y)
    (hx : x ∉ G.neighborFinset u) (hx' : x ∉ G.neighborFinset v) :
    2 * ((univ : Finset (Finset V)).filter (fun T => Same (eside G u v T) s(x, y))).card
      = 2 ^ Fintype.card V := by
  apply toggle_count _ x
  intro T
  have hyx : y ≠ x := hxy.symm
  simp only [same_mk, mem_eside, Finset.mem_symmDiff, Finset.mem_singleton, hyx, hx, hx',
    not_false_eq_true, and_true, or_false, true_and, false_and, and_false, false_or, not_true_eq_false]
  tauto

open scoped Classical in
lemma exists_edge_cut (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) {u v : V}
    (huv : G.Adj u v) :
    ∃ S : Finset V, 2 * (G.edgeFinset.filter (Same S)).card + G.degree u + G.degree v
      ≤ G.edgeFinset.card + 1 := by
  set N := G.neighborFinset u ∪ G.neighborFinset v with hN
  set E0 := G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ N) with hE0
  set ER := G.edgeFinset.filter (fun e => ¬ ∀ x ∈ e, x ∈ N) with hER
  have hsplit : E0.card + ER.card = G.edgeFinset.card :=
    Finset.card_filter_add_card_filter_not _
  have hu : u ∈ N := by
    rw [hN, Finset.mem_union, mem_neighborFinset, mem_neighborFinset]
    exact Or.inr huv.symm
  have hv : v ∈ N := by
    rw [hN, Finset.mem_union, mem_neighborFinset, mem_neighborFinset]
    exact Or.inl huv
  have hNu : ∀ z, G.Adj u z → z ∈ N := by
    intro z hz
    rw [hN, Finset.mem_union, mem_neighborFinset]
    exact Or.inl hz
  have hNv : ∀ z, G.Adj v z → z ∈ N := by
    intro z hz
    rw [hN, Finset.mem_union, mem_neighborFinset, mem_neighborFinset]
    exact Or.inr hz
  have hinc : G.incidenceFinset u ∪ G.incidenceFinset v ⊆ E0 := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_union, mem_incidenceFinset, mem_incidenceFinset,
        mk'_mem_incidenceSet_iff, mk'_mem_incidenceSet_iff] at he
      rw [hE0, Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
      rcases he with ⟨hxy, hux | huy⟩ | ⟨hxy, hvx | hvy⟩
      · subst hux
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hu
        · exact hNu _ hxy
      · subst huy
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hNu _ hxy.symm
        · exact hu
      · subst hvx
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hv
        · exact hNv _ hxy
      · subst hvy
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hNv _ hxy.symm
        · exact hv
  have hinter : G.incidenceFinset u ∩ G.incidenceFinset v = {s(u, v)} := by
    ext e
    rw [Finset.mem_inter, mem_incidenceFinset, mem_incidenceFinset, Finset.mem_singleton]
    have hset := G.incidenceSet_inter_incidenceSet_of_adj huv
    constructor
    · intro h
      have h' : e ∈ G.incidenceSet u ∩ G.incidenceSet v := h
      rw [hset] at h'
      exact h'
    · intro h
      have h' : e ∈ ({s(u, v)} : Set (Sym2 V)) := h
      rw [← hset] at h'
      exact h'
  have hcard : (G.incidenceFinset u ∪ G.incidenceFinset v).card + 1
      = G.degree u + G.degree v := by
    have := Finset.card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
    rw [hinter, Finset.card_singleton, card_incidenceFinset_eq_degree,
      card_incidenceFinset_eq_degree] at this
    exact this
  have hzero : ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∈ N) →
      ∀ T : Finset V, ¬ Same (eside G u v T) e := by
    intro e he hall T hs
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rw [same_mk, mem_eside, mem_eside] at hs
      have hx := hall x (Sym2.mem_mk_left x y)
      have hy := hall y (Sym2.mem_mk_right x y)
      rw [hN, Finset.mem_union] at hx hy
      rcases hx with hxu | hxv
      · have hxv := nbhd_disj G hG huv x hxu
        rcases hy with hyu | hyv
        · rw [mem_neighborFinset] at hxu hyu
          exact hG {u, x, y} (is3Clique_triple_iff.2 ⟨hxu, hyu, he⟩)
        · have : ¬ ((y ∈ T ∨ y ∈ G.neighborFinset u) ∧ y ∉ G.neighborFinset v) :=
            fun h => h.2 hyv
          exact this (hs.1 ⟨Or.inr hxu, hxv⟩)
      · rcases hy with hyu | hyv
        · have hyv := nbhd_disj G hG huv y hyu
          have : ¬ ((x ∈ T ∨ x ∈ G.neighborFinset u) ∧ x ∉ G.neighborFinset v) :=
            fun h => h.2 hxv
          exact this (hs.2 ⟨Or.inr hyu, hyv⟩)
        · rw [mem_neighborFinset] at hxv hyv
          exact hG {v, x, y} (is3Clique_triple_iff.2 ⟨hxv, hyv, he⟩)
  have hcount : ∀ e ∈ G.edgeFinset,
      2 * ((univ : Finset (Finset V)).filter (fun T => Same (eside G u v T) e)).card
        = if (∀ x ∈ e, x ∈ N) then 0 else 2 ^ Fintype.card V := by
    intro e he
    split_ifs with hall
    · rw [Finset.filter_false_of_mem (fun T _ => hzero e he hall T)]
      simp
    · push Not at hall
      obtain ⟨x, hxe, hxN⟩ := hall
      have hspec := Sym2.other_spec hxe
      rw [← hspec] at he ⊢
      have hne : x ≠ Sym2.Mem.other hxe := by
        rw [mem_edgeFinset, mem_edgeSet] at he
        exact he.ne
      rw [hN, Finset.mem_union, not_or] at hxN
      exact edge_count G u v x _ hne hxN.1 hxN.2
  have key : ∑ T : Finset V, 2 * (G.edgeFinset.filter (Same (eside G u v T))).card
      = ∑ T : Finset V, ER.card := by
    calc ∑ T : Finset V, 2 * (G.edgeFinset.filter (Same (eside G u v T))).card
        = ∑ T : Finset V, ∑ e ∈ G.edgeFinset, 2 * (if Same (eside G u v T) e then 1 else 0) := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [Finset.card_filter, Finset.mul_sum]
      _ = ∑ e ∈ G.edgeFinset, ∑ T : Finset V, 2 * (if Same (eside G u v T) e then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ e ∈ G.edgeFinset, (if (∀ x ∈ e, x ∈ N) then 0 else 2 ^ Fintype.card V) := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          rw [← Finset.mul_sum, ← Finset.card_filter]
          exact hcount e he
      _ = ∑ T : Finset V, ER.card := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.sum_const,
            Finset.card_univ, Fintype.card_finset, smul_eq_mul, smul_eq_mul, mul_comm]
  obtain ⟨T, -, hT⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty key.le
  refine ⟨eside G u v T, ?_⟩
  have := Finset.card_le_card hinc
  omega


open scoped Classical in
lemma exists_edge_cut_full (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    {u v : V} (huv : G.Adj u v) :
    ∃ S : Finset V, 2 * (G.edgeFinset.filter (Same S)).card
      + (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card
      ≤ G.edgeFinset.card := by
  set N := G.neighborFinset u ∪ G.neighborFinset v with hN
  set E0 := G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ N) with hE0
  set ER := G.edgeFinset.filter (fun e => ¬ ∀ x ∈ e, x ∈ N) with hER
  have hsplit : E0.card + ER.card = G.edgeFinset.card :=
    Finset.card_filter_add_card_filter_not _
  have hzero : ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∈ N) →
      ∀ T : Finset V, ¬ Same (eside G u v T) e := by
    intro e he hall T hs
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rw [same_mk, mem_eside, mem_eside] at hs
      have hx := hall x (Sym2.mem_mk_left x y)
      have hy := hall y (Sym2.mem_mk_right x y)
      rw [hN, Finset.mem_union] at hx hy
      rcases hx with hxu | hxv
      · have hxv := nbhd_disj G hG huv x hxu
        rcases hy with hyu | hyv
        · rw [mem_neighborFinset] at hxu hyu
          exact hG {u, x, y} (is3Clique_triple_iff.2 ⟨hxu, hyu, he⟩)
        · have : ¬ ((y ∈ T ∨ y ∈ G.neighborFinset u) ∧ y ∉ G.neighborFinset v) :=
            fun h => h.2 hyv
          exact this (hs.1 ⟨Or.inr hxu, hxv⟩)
      · rcases hy with hyu | hyv
        · have hyv := nbhd_disj G hG huv y hyu
          have : ¬ ((x ∈ T ∨ x ∈ G.neighborFinset u) ∧ x ∉ G.neighborFinset v) :=
            fun h => h.2 hxv
          exact this (hs.2 ⟨Or.inr hyu, hyv⟩)
        · rw [mem_neighborFinset] at hxv hyv
          exact hG {v, x, y} (is3Clique_triple_iff.2 ⟨hxv, hyv, he⟩)
  have hcount : ∀ e ∈ G.edgeFinset,
      2 * ((univ : Finset (Finset V)).filter (fun T => Same (eside G u v T) e)).card
        = if (∀ x ∈ e, x ∈ N) then 0 else 2 ^ Fintype.card V := by
    intro e he
    split_ifs with hall
    · rw [Finset.filter_false_of_mem (fun T _ => hzero e he hall T)]
      simp
    · push Not at hall
      obtain ⟨x, hxe, hxN⟩ := hall
      have hspec := Sym2.other_spec hxe
      rw [← hspec] at he ⊢
      have hne : x ≠ Sym2.Mem.other hxe := by
        rw [mem_edgeFinset, mem_edgeSet] at he
        exact he.ne
      rw [hN, Finset.mem_union, not_or] at hxN
      exact edge_count G u v x _ hne hxN.1 hxN.2
  have key : ∑ T : Finset V, 2 * (G.edgeFinset.filter (Same (eside G u v T))).card
      = ∑ T : Finset V, ER.card := by
    calc ∑ T : Finset V, 2 * (G.edgeFinset.filter (Same (eside G u v T))).card
        = ∑ T : Finset V, ∑ e ∈ G.edgeFinset, 2 * (if Same (eside G u v T) e then 1 else 0) := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [Finset.card_filter, Finset.mul_sum]
      _ = ∑ e ∈ G.edgeFinset, ∑ T : Finset V, 2 * (if Same (eside G u v T) e then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ e ∈ G.edgeFinset, (if (∀ x ∈ e, x ∈ N) then 0 else 2 ^ Fintype.card V) := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          rw [← Finset.mul_sum, ← Finset.card_filter]
          exact hcount e he
      _ = ∑ T : Finset V, ER.card := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.sum_const,
            Finset.card_univ, Fintype.card_finset, smul_eq_mul, smul_eq_mul, mul_comm]
  obtain ⟨T, -, hT⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty key.le
  exact ⟨eside G u v T, by omega⟩

end

lemma exists_good_edge (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hm : 1 ≤ G.edgeFinset.card) :
    ∃ u v, G.Adj u v ∧ 4 * G.edgeFinset.card ≤ 25 * (G.degree u + G.degree v) := by
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image univ
    (fun u => ∑ w ∈ G.neighborFinset u, G.degree w) univ_nonempty
  have hS : ∑ v, ∑ w ∈ G.neighborFinset v, G.degree w
      ≤ 25 * ∑ w ∈ G.neighborFinset u, G.degree w := by
    calc ∑ v, ∑ w ∈ G.neighborFinset v, G.degree w
        ≤ ∑ v : Fin 25, ∑ w ∈ G.neighborFinset u, G.degree w :=
          Finset.sum_le_sum (fun v _ => hu v (mem_univ v))
      _ = 25 * ∑ w ∈ G.neighborFinset u, G.degree w := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [sum_nbhd_deg] at hS
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 25)))
    (f := fun v => G.degree v)
  rw [sum_degrees_eq_twice_card_edges] at hcs
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_id] at hcs
  generalize hD : ∑ u, G.degree u ^ 2 = D at hS hcs
  generalize hM : G.edgeFinset.card = M at hm hcs ⊢
  by_cases hne : (G.neighborFinset u).Nonempty
  · obtain ⟨v, hv, hvmax⟩ :=
      Finset.exists_max_image (G.neighborFinset u) (fun w => G.degree w) hne
    have hSle : ∑ w ∈ G.neighborFinset u, G.degree w ≤ G.degree u * G.degree v := by
      calc ∑ w ∈ G.neighborFinset u, G.degree w
          ≤ ∑ w ∈ G.neighborFinset u, G.degree v := Finset.sum_le_sum (fun w hw => hvmax w hw)
        _ = G.degree u * G.degree v := by
            rw [Finset.sum_const, card_neighborFinset_eq_degree, smul_eq_mul]
    refine ⟨u, v, (mem_neighborFinset _ _ _).1 hv, ?_⟩
    generalize hSu : ∑ w ∈ G.neighborFinset u, G.degree w = Su at hS hSle
    generalize G.degree u = a at hSle ⊢
    generalize G.degree v = b at hSle ⊢
    have key : (4 * M) * (4 * M) ≤ (25 * (a + b)) * (25 * (a + b)) := by
      have h1 : (2 * (M : ℤ)) ^ 2 ≤ 25 * (D : ℤ) := by exact_mod_cast hcs
      have h2 : (D : ℤ) ≤ 25 * (Su : ℤ) := by exact_mod_cast hS
      have h3 : (Su : ℤ) ≤ (a : ℤ) * b := by exact_mod_cast hSle
      have : (4 * (M : ℤ)) * (4 * M) ≤ (25 * ((a : ℤ) + b)) * (25 * ((a : ℤ) + b)) := by
        nlinarith [sq_nonneg ((a : ℤ) - b)]
      exact_mod_cast this
    exact Nat.mul_self_le_mul_self_iff.1 key
  · exfalso
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hS
    have hD0 : D = 0 := by omega
    rw [hD0] at hcs
    simp at hcs
    omega

open scoped Classical in
lemma sparse_ext (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (h1 : 52 ≤ G.edgeFinset.card) (h2 : G.edgeFinset.card ≤ 60) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  obtain ⟨u, v, huv, hdeg⟩ := exists_good_edge G (by omega)
  obtain ⟨S, hS⟩ := exists_edge_cut G hG huv
  exact ⟨S, by omega⟩


open scoped Classical in
lemma highdeg_case (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (v : Fin 25) (hv : 14 ≤ G.degree v) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  refine ⟨G.neighborFinset v, ?_⟩
  set W := (insert v (G.neighborFinset v))ᶜ with hWdef
  have hsub : G.edgeFinset.filter (Same (G.neighborFinset v))
      ⊆ G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ W) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, same_mk] at he
      rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
      refine ⟨he.1, fun z hz => ?_⟩
      have hxN : x ∉ G.neighborFinset v := by
        intro hx
        have hy := he.2.1 hx
        rw [mem_neighborFinset] at hx hy
        exact hG {v, x, y} (is3Clique_triple_iff.2 ⟨hx, hy, he.1⟩)
      have hyN : y ∉ G.neighborFinset v := fun hy => hxN (he.2.2 hy)
      have hxv : x ≠ v := by
        intro hxv
        subst hxv
        exact hyN ((mem_neighborFinset _ _ _).2 he.1)
      have hyv : y ≠ v := by
        intro hyv
        subst hyv
        exact hxN ((mem_neighborFinset _ _ _).2 he.1.symm)
      rw [Sym2.mem_iff] at hz
      rw [hWdef, Finset.mem_compl, Finset.mem_insert, not_or]
      rcases hz with rfl | rfl
      · exact ⟨hxv, hxN⟩
      · exact ⟨hyv, hyN⟩
  have hWcard : W.card ≤ 10 := by
    rw [hWdef, Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem
      (by simp), card_neighborFinset_eq_degree]
    omega
  have hmap : G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ W)
      ⊆ (G.induce (W : Set (Fin 25))).edgeFinset.map
        ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩ := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet] at he
      have hx : x ∈ W := he.2 x (Sym2.mem_mk_left x y)
      have hy : y ∈ W := he.2 y (Sym2.mem_mk_right x y)
      rw [Finset.mem_map]
      refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, ?_⟩
      · rw [mem_edgeFinset, mem_edgeSet, comap_adj]
        exact he.1
      · simp
  have hcf : (G.induce (W : Set (Fin 25))).CliqueFree 3 := hG.comap (Embedding.induce _).isContained
  have hT := CliqueFree.card_edgeFinset_le (r := 2) hcf
  dsimp only at hT
  have hc : Fintype.card ↑(↑W : Set (Fin 25)) = W.card := by simp
  rw [hc] at hT
  have hbound : ∀ n : ℕ, n ≤ 10 →
      (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) + (n % 2).choose 2 ≤ 25 := by
    intro n hn
    interval_cases n <;> decide
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_card hmap
  rw [Finset.card_map] at h2
  have h3 := hbound _ hWcard
  omega

lemma exists_maximal_tf (G : SimpleGraph (Fin 25)) (hG : G.CliqueFree 3) :
    ∃ G' : SimpleGraph (Fin 25), G ≤ G' ∧ G'.CliqueFree 3 ∧
      ∀ H : SimpleGraph (Fin 25), G' ≤ H → H.CliqueFree 3 → H = G' := by
  obtain ⟨G', hle, hmax⟩ :=
    Finite.exists_le_maximal (p := fun H : SimpleGraph (Fin 25) => H.CliqueFree 3) hG
  exact ⟨G', hle, hmax.1, fun H hH hHcf => le_antisymm (hmax.2 hHcf hH) hH⟩

lemma common_nbr_of_max (G : SimpleGraph (Fin 25)) (hG : G.CliqueFree 3)
    (hmax : ∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G)
    (x y : Fin 25) (hxy : x ≠ y) (hn : ¬ G.Adj x y) : ∃ z, G.Adj x z ∧ G.Adj y z := by
  by_contra hno
  push Not at hno
  have hno' : ∀ z, G.Adj z x → G.Adj z y → False := fun z h1 h2 => hno z h1.symm h2.symm
  have hcf : (G ⊔ edge x y).CliqueFree 3 := by
    intro t ht
    rw [is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
    simp only [sup_adj, edge_adj] at hab hac hbc
    rcases hab with hab | ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, hab'⟩ <;>
    rcases hac with hac | ⟨⟨h3, h4⟩ | ⟨h3, h4⟩, hac'⟩ <;>
    rcases hbc with hbc | ⟨⟨h5, h6⟩ | ⟨h5, h6⟩, hbc'⟩ <;>
    subst_vars <;>
    first
      | exact hG {a, b, c} (is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)
      | exact absurd rfl hxy
      | exact absurd rfl hab'
      | exact absurd rfl hac'
      | exact absurd rfl hbc'
      | exact G.irrefl hab
      | exact G.irrefl hac
      | exact G.irrefl hbc
      | exact hno _ hab hac
      | exact hno _ hac hab
      | exact hno _ hab hac.symm
      | exact hno _ hac.symm hab
      | exact hno _ hab.symm hac
      | exact hno _ hac hab.symm
      | exact hno _ hab.symm hac.symm
      | exact hno _ hac.symm hab.symm
      | exact hno _ hab hbc
      | exact hno _ hbc hab
      | exact hno _ hab hbc.symm
      | exact hno _ hbc.symm hab
      | exact hno _ hab.symm hbc
      | exact hno _ hbc hab.symm
      | exact hno _ hab.symm hbc.symm
      | exact hno _ hbc.symm hab.symm
      | exact hno _ hac hbc
      | exact hno _ hbc hac
      | exact hno _ hac hbc.symm
      | exact hno _ hbc.symm hac
      | exact hno _ hac.symm hbc
      | exact hno _ hbc hac.symm
      | exact hno _ hac.symm hbc.symm
      | exact hno _ hbc.symm hac.symm
  have hle : G ≤ G ⊔ edge x y := le_sup_left
  have heq := hmax _ hle hcf
  apply hn
  have hadj : (G ⊔ edge x y).Adj x y := by
    rw [sup_adj, edge_adj]
    exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
  rw [heq] at hadj
  exact hadj

open scoped Classical in
lemma filter_mono_graph {G G' : SimpleGraph (Fin 25)} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G ≤ G') (S : Finset (Fin 25)) :
    (G.edgeFinset.filter (Same S)).card ≤ (G'.edgeFinset.filter (Same S)).card := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact edgeFinset_mono hle

lemma middle_sum_nbhd_weight (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (f : Fin 25 → ℕ) :
    ∑ v, ∑ u ∈ G.neighborFinset v, f u = ∑ u, G.degree u * f u := by
  simp_rw [neighborFinset_eq_filter (G := G), Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  congr 1
  ext w
  simp [adj_comm]

-- Each vertex requires a deficit below k in its neighbourhood when k times its degree
-- exceeds the bound on the sum of its neighbours' degrees.
lemma middle_deficit_bound (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (A k : ℕ)
    (hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ A) :
    (∑ v, (k * G.degree v - A)) ≤ ∑ v, G.degree v * (k - G.degree v) := by
  rw [← middle_sum_nbhd_weight]
  apply Finset.sum_le_sum
  intro v _
  have h : ∑ u ∈ G.neighborFinset v, k ≤
      ∑ u ∈ G.neighborFinset v, (G.degree u + (k - G.degree u)) :=
    Finset.sum_le_sum (fun u _ => by omega)
  rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree,
    Finset.sum_add_distrib, mul_comm] at h
  have := hA v
  omega

lemma middle_deficit_pair (d m : ℕ) (hd : d ≤ 13) (hm : m = 121 ∨ m = 122) :
    3 * (d * (9 - d) + d * (10 - d)) + (285 - 2 * m) * d ≤
      3 * ((9 * d - (m - 26)) + (10 * d - (m - 26))) + (2352 - 16 * m) := by
  rcases hm with rfl | rfl <;> interval_cases d <;> norm_num

lemma middle_deficit_square (d : ℕ) (hd : d ≤ 13) :
    d * (10 - d) + 31 * d ≤ (10 * d - 97) + d ^ 2 + 207 := by
  interval_cases d <;> norm_num

open scoped Classical in
lemma middle_upper_edges (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 13)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hmlo : 121 ≤ G.edgeFinset.card) (hmhi : G.edgeFinset.card ≤ 123) : False := by
  set m := G.edgeFinset.card
  have hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ m - 26 := by
    intro v
    have := cut_card_nbhd G hG v
    have := hnb v
    omega
  have hsum : ∑ v, G.degree v = 2 * m := G.sum_degrees_eq_twice_card_edges
  have h10 := middle_deficit_bound G (m - 26) 10 hA
  by_cases hm : m = 123
  · have hSq : ∑ v, G.degree v ^ 2 ≤ 25 * (m - 26) := by
      have h := Finset.sum_le_sum (s := (univ : Finset (Fin 25))) (fun v _ => hA v)
      rw [sum_nbhd_deg] at h
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
    rw [hm] at h10 hSq hsum
    norm_num at h10 hSq hsum
    have h := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
      (fun v _ => middle_deficit_square (G.degree v) (hdeg v))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    omega
  · have hm' : m = 121 ∨ m = 122 := by omega
    have h9 := middle_deficit_bound G (m - 26) 9 hA
    have h := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
      (fun v _ => middle_deficit_pair (G.degree v) m (hdeg v) hm')
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    rcases hm' with hm' | hm' <;> rw [hm'] at h h9 h10 <;> norm_num at h h9 h10 <;> omega

lemma middle_deficit_add (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (k : ℕ)
    (s : Finset (Fin 25)) (hs : ∀ v ∈ s, G.degree v ≤ k) :
    (∑ v ∈ s, G.degree v) + (∑ v ∈ s, (k - G.degree v)) = s.card * k := by
  rw [← Finset.sum_add_distrib, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_congr rfl (fun v hv => by have := hs v hv; omega)

lemma middle_no_degree_ten_edge (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hm : 26 ≤ G.edgeFinset.card)
    (hdeg : ∀ v, G.degree v ≤ 10)
    (hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ G.edgeFinset.card - 26)
    {u v : Fin 25} (hu : G.degree u = 10) (hv : G.degree v = 10) :
    ¬ G.Adj u v := by
  intro huv
  have hdis : Disjoint (G.neighborFinset u) (G.neighborFinset v) :=
    Finset.disjoint_left.2 (fun x hx hy => nbhd_disj G hG huv x hx hy)
  have hleft := middle_deficit_add G 10 (G.neighborFinset u) (fun x _ => hdeg x)
  have hright := middle_deficit_add G 10 (G.neighborFinset v) (fun x _ => hdeg x)
  rw [card_neighborFinset_eq_degree, hu] at hleft
  rw [card_neighborFinset_eq_degree, hv] at hright
  have htotal := middle_deficit_add G 10 univ (fun x _ => hdeg x)
  rw [G.sum_degrees_eq_twice_card_edges, Finset.card_univ, Fintype.card_fin] at htotal
  have hle : ∑ x ∈ G.neighborFinset u ∪ G.neighborFinset v, (10 - G.degree x)
      ≤ ∑ x : Fin 25, (10 - G.degree x) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_union hdis] at hle
  have := hA u
  have := hA v
  omega

open scoped Classical in
lemma middle_degree_ten_bound (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hm : 119 ≤ G.edgeFinset.card) (hm' : G.edgeFinset.card ≤ 123)
    (hdeg : ∀ v, G.degree v ≤ 10)
    (hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ G.edgeFinset.card - 26) :
    False := by
  let H := (univ : Finset (Fin 25)).filter (fun v => G.degree v = 10)
  have hH : ∀ v, v ∈ H ↔ G.degree v = 10 := fun v => by simp [H]
  have hc : H.card ≤ 25 := by simpa using Finset.card_le_card (Finset.subset_univ H)
  have htotal := middle_deficit_add G 10 univ (fun x _ => hdeg x)
  rw [G.sum_degrees_eq_twice_card_edges, Finset.card_univ, Fintype.card_fin] at htotal
  have hL : Hᶜ.card ≤ ∑ x : Fin 25, (10 - G.degree x) := by
    calc Hᶜ.card = ∑ x ∈ Hᶜ, (1 : ℕ) := by simp
      _ ≤ ∑ x ∈ Hᶜ, (10 - G.degree x) := by
        apply Finset.sum_le_sum
        intro x hx
        have hx' := Finset.mem_compl.1 hx
        rw [hH] at hx'
        have := hdeg x
        omega
      _ ≤ ∑ x : Fin 25, (10 - G.degree x) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.card_compl, Fintype.card_fin] at hL
  have hcard : 13 ≤ H.card := by omega
  have hinc : (H.biUnion (fun v => G.incidenceFinset v)).card = H.card * 10 := by
    rw [Finset.card_biUnion]
    · rw [← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_congr rfl (fun v hv => ?_)
      rw [card_incidenceFinset_eq_degree, (hH v).1 hv]
    · intro a ha b hb hab
      show Disjoint (G.incidenceFinset a) (G.incidenceFinset b)
      rw [Finset.disjoint_left]
      intro e hea heb
      rw [mem_incidenceFinset] at hea heb
      have hs := G.incidenceSet_inter_incidenceSet_subset hab ⟨hea, heb⟩
      rw [Set.mem_singleton_iff] at hs
      have he := hea.1
      rw [hs, mem_edgeSet] at he
      exact middle_no_degree_ten_edge G hG (by omega) hdeg hA ((hH a).1 ha) ((hH b).1 hb) he
  have hsub : (H.biUnion (fun v => G.incidenceFinset v)).card ≤ G.edgeFinset.card := by
    apply Finset.card_le_card
    intro e he
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.1 he
    exact G.incidenceFinset_subset v hv
  omega

lemma middle_tight_degree_table (d : ℕ) (hd : d ≤ 13) :
    d * (9 - d) + d * (10 - d) + 15 * d + (if 8 ≤ d ∧ d ≤ 11 then 0 else 1) ≤
      (9 * d - 94) + (10 * d - 94) + 144 := by
  interval_cases d <;> norm_num

lemma middle_deficit_eleven_table (d : ℕ) (hd₁ : 8 ≤ d) (hd₂ : d ≤ 11) :
    5 * (d * (11 - d)) + 2 * (9 * d - 94) + 95 * d + 50 * (9 - d) ≤
      5 * (11 * d - 94) + 2 * (d * (9 - d)) + 920 := by
  interval_cases d <;> norm_num

open scoped Classical in
lemma middle_edges_120 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 13)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hm : G.edgeFinset.card = 120) : False := by
  have hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ 94 := by
    intro v
    have := cut_card_nbhd G hG v
    have := hnb v
    omega
  have hsum : ∑ v, G.degree v = 240 := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have h9 := middle_deficit_bound G 94 9 hA
  have h10 := middle_deficit_bound G 94 10 hA
  have h11 := middle_deficit_bound G 94 11 hA
  have ht := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
    (fun v _ => middle_tight_degree_table (G.degree v) (hdeg v))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at ht
  have h9eq : (∑ v, G.degree v * (9 - G.degree v)) = ∑ v, (9 * G.degree v - 94) := by omega
  have hz : (∑ v : Fin 25, (if 8 ≤ G.degree v ∧ G.degree v ≤ 11 then 0 else 1 : ℕ)) = 0 := by omega
  have hr : ∀ v, 8 ≤ G.degree v ∧ G.degree v ≤ 11 := by
    intro v
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).1 hz v (mem_univ v)
    by_contra hc
    simp [hc] at h
  have ht' := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
    (fun v _ => middle_deficit_eleven_table (G.degree v) (hr v).1 (hr v).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, h9eq] at ht'
  have hdef : (∑ v : Fin 25, (9 - G.degree v)) ≤ 4 := by omega
  have hd : ∀ v, G.degree v ≤ 10 := by
    intro v
    by_contra! hv
    have hv' : G.degree v = 11 := by have := (hr v).2; omega
    have hc : ∑ x ∈ G.neighborFinset v, 9 ≤
        ∑ x ∈ G.neighborFinset v, (G.degree x + (9 - G.degree x)) :=
      Finset.sum_le_sum (fun _ _ => by omega)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, hv',
      Finset.sum_add_distrib] at hc
    have hl : ∑ x ∈ G.neighborFinset v, (9 - G.degree x) ≤ ∑ x : Fin 25, (9 - G.degree x) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hA v
    omega
  exact middle_degree_ten_bound G hG (by omega) (by omega) hd (by simpa [hm] using hA)

lemma middle_deficit_119_low_table (d : ℕ) (hd : d ≤ 11) :
    d * (10 - d) + 3 * (d * (11 - d)) + 73 * d + 30 * (9 - d) ≤
      (10 * d - 93) + 3 * (11 * d - 93) + 702 := by
  interval_cases d <;> norm_num

lemma middle_deficit_119_high_table (d D : ℕ) (hd : d ≤ D) (hD : D = 12 ∨ D = 13) :
    d * (10 - d) + 12 * d + 5 * (9 - d) ≤ (10 * d - 93) + (93 + 2 * D) := by
  rcases hD with rfl | rfl <;> interval_cases d <;> norm_num

open scoped Classical in
lemma middle_edges_119 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 13)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hm : G.edgeFinset.card = 119) : False := by
  have hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ 93 := by
    intro v
    have := cut_card_nbhd G hG v
    have := hnb v
    omega
  have hsum : ∑ v, G.degree v = 238 := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have h10 := middle_deficit_bound G 93 10 hA
  obtain ⟨u, _, hu⟩ := Finset.exists_max_image univ (fun v => G.degree v) univ_nonempty
  let D := G.degree u
  have hD : ∀ v, G.degree v ≤ D := fun v => hu v (mem_univ v)
  have hdegU := hdeg u
  change D ≤ 13 at hdegU
  have hlocal : 9 * D ≤ 93 + ∑ v : Fin 25, (9 - G.degree v) := by
    have hs : ∑ x ∈ G.neighborFinset u, 9 ≤
        ∑ x ∈ G.neighborFinset u, (G.degree x + (9 - G.degree x)) :=
      Finset.sum_le_sum (fun _ _ => by omega)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree,
      Finset.sum_add_distrib] at hs
    have hl : ∑ x ∈ G.neighborFinset u, (9 - G.degree x) ≤ ∑ x : Fin 25, (9 - G.degree x) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    change D * 9 ≤ _ at hs
    have := hA u
    omega
  have hD10 : D ≤ 10 := by
    by_cases hD11 : D ≤ 11
    · have h11 := middle_deficit_bound G 93 11 hA
      have ht := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
        (fun v _ => middle_deficit_119_low_table (G.degree v) ((hD v).trans hD11))
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul] at ht
      omega
    · have hD' : D = 12 ∨ D = 13 := by omega
      have ht := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
        (fun v _ => middle_deficit_119_high_table (G.degree v) D (hD v) hD')
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul] at ht
      rcases hD' with hD' | hD' <;> rw [hD'] at hlocal ht <;> omega
  exact middle_degree_ten_bound G hG (by omega) (by omega) (fun v => (hD v).trans hD10)
    (by simpa [hm] using hA)

lemma middle_diameter_weight (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    (v : Fin 25) : 24 ≤ ∑ u ∈ G.neighborFinset v, G.degree u := by
  let B := fun u => insert u ((G.neighborFinset u).erase v)
  have hs : univ.erase v ⊆ (G.neighborFinset v).biUnion B := by
    intro x hx
    have hxv := Finset.ne_of_mem_erase hx
    rw [Finset.mem_biUnion]
    by_cases hadj : G.Adj v x
    · exact ⟨x, (mem_neighborFinset _ _ _).2 hadj, Finset.mem_insert_self _ _⟩
    · obtain ⟨u, hvu, hxu⟩ := hdiam v x hxv.symm hadj
      exact ⟨u, (mem_neighborFinset _ _ _).2 hvu, Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨hxv, (mem_neighborFinset _ _ _).2 hxu.symm⟩)⟩
  have hcard : ∀ u ∈ G.neighborFinset v, (B u).card = G.degree u := by
    intro u hu
    have hvu : v ∈ G.neighborFinset u :=
      (mem_neighborFinset _ _ _).2 ((mem_neighborFinset _ _ _).1 hu).symm
    have hnu : u ∉ (G.neighborFinset u).erase v := by simp
    dsimp [B]
    rw [Finset.card_insert_of_notMem hnu, Finset.card_erase_of_mem hvu,
      card_neighborFinset_eq_degree]
    have hp := Finset.card_pos.2 ⟨v, hvu⟩
    rw [card_neighborFinset_eq_degree] at hp
    omega
  calc 24 = (univ.erase v).card := by simp
    _ ≤ ((G.neighborFinset v).biUnion B).card := Finset.card_le_card hs
    _ ≤ ∑ u ∈ G.neighborFinset v, (B u).card := Finset.card_biUnion_le
    _ = _ := Finset.sum_congr rfl hcard

open scoped Classical in
lemma middle_edges_61 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    (hm : G.edgeFinset.card = 61) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  by_contra! hcut
  have he : ∀ u v, G.Adj u v → G.degree u + G.degree v ≤ 10 := by
    intro u v huv
    obtain ⟨S, hS⟩ := exists_edge_cut G hG huv
    have := hcut S
    omega
  have hWeight := middle_diameter_weight G hdiam
  have hdegU : ∀ u, G.degree u ≤ 6 := by
    intro u
    have hz : 24 ≤ G.degree u * (10 - G.degree u) := by
      refine (hWeight u).trans ?_
      calc ∑ v ∈ G.neighborFinset u, G.degree v
          ≤ ∑ v ∈ G.neighborFinset u, (10 - G.degree u) :=
            Finset.sum_le_sum (fun v hv => by
              have := he u v ((mem_neighborFinset _ _ _).1 hv)
              omega)
        _ = _ := by rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree]
    by_contra! hn
    have h10 : G.degree u ≤ 10 := by
      by_contra! h10
      have hzero : 10 - G.degree u = 0 := by omega
      rw [hzero, mul_zero] at hz
      omega
    generalize G.degree u = d at hn h10 hz
    interval_cases d <;> norm_num at hz
  have hdegL : ∀ u, 4 ≤ G.degree u := by
    intro u
    have h := Finset.sum_le_sum (s := G.neighborFinset u) (fun v _ => hdegU v)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree] at h
    have := hWeight u
    omega
  have h46 : ∀ u v, G.degree u = 4 → G.Adj u v → G.degree v = 6 := by
    intro u v hu huv
    by_contra hnv
    have h := Finset.sum_lt_sum (s := G.neighborFinset u) (fun w _ => hdegU w)
      ⟨v, (mem_neighborFinset _ _ _).2 huv, by have := hdegU v; omega⟩
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, hu] at h
    have := hWeight u
    omega
  have h64 : ∀ u v, G.degree u = 6 → G.Adj u v → G.degree v = 4 := by
    intro u v hu huv
    have := he u v huv
    have := hdegL v
    omega
  by_cases hex : ∃ u, G.degree u = 6
  · obtain ⟨u, hu⟩ := hex
    have hnot5 : ∀ v, G.degree v ≠ 5 := by
      intro v hv
      have hne : u ≠ v := fun heq => by rw [heq, hv] at hu; omega
      have hn : ¬ G.Adj u v := fun ha => by have := h64 u v hu ha; omega
      obtain ⟨w, huw, hvw⟩ := hdiam u v hne hn
      have := h46 w v (h64 u w hu huw) hvw.symm
      omega
    let S := (univ : Finset (Fin 25)).filter (fun v => G.degree v = 6)
    have hs : (G.edgeFinset.filter (Same S)).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.2
      intro e he'
      induction e using Sym2.ind with
      | h a b =>
        rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, same_mk] at he'
        have hside : G.degree a = 6 ↔ G.degree b = 6 := by
          simpa [S] using he'.2
        have ha := hdegL a
        have hb := hdegU a
        have hn := hnot5 a
        by_cases h6 : G.degree a = 6
        · have := h64 a b h6 he'.1
          have := hside.1 h6
          omega
        · have := h46 a b (by omega) he'.1
          exact h6 (hside.2 this)
    exact (hcut S).not_ge (by omega)
  · have hconst : ∀ v, G.degree v = 5 := by
      intro v
      have hn6 : ∀ w, G.degree w ≠ 6 := fun w hw => hex ⟨w, hw⟩
      have hh := Finset.sum_le_sum (s := G.neighborFinset v) (f := fun w => G.degree w) (g := fun _ => 5)
        (fun w _ => by have := hdegU w; have := hn6 w; omega)
      rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree] at hh
      have := hWeight v
      have := hdegU v
      have := hn6 v
      omega
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hm] at hsum
    omega

open scoped Classical in
-- The incident edges at u and v already use degree u + degree v - 1 slots in the core.
lemma middle_edge_core_budget (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    {u v : Fin 25} (huv : G.Adj u v) (T : Finset (Sym2 (Fin 25)))
    (hT : ∀ e ∈ T, e ∈ G.edgeFinset ∧
      (∀ z ∈ e, z ∈ G.neighborFinset u ∪ G.neighborFinset v) ∧ u ∉ e ∧ v ∉ e) :
    G.degree u + G.degree v + T.card ≤ (G.edgeFinset.filter
      (fun e => ∀ z ∈ e, z ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 1 := by
  set N := G.neighborFinset u ∪ G.neighborFinset v with hN
  set E0 := G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ N) with hE0
  have hu : u ∈ N := by
    rw [hN, Finset.mem_union, mem_neighborFinset, mem_neighborFinset]
    exact Or.inr huv.symm
  have hv : v ∈ N := by
    rw [hN, Finset.mem_union, mem_neighborFinset, mem_neighborFinset]
    exact Or.inl huv
  have hNu : ∀ z, G.Adj u z → z ∈ N := by
    intro z hz
    rw [hN, Finset.mem_union, mem_neighborFinset]
    exact Or.inl hz
  have hNv : ∀ z, G.Adj v z → z ∈ N := by
    intro z hz
    rw [hN, Finset.mem_union, mem_neighborFinset, mem_neighborFinset]
    exact Or.inr hz
  have hinc : G.incidenceFinset u ∪ G.incidenceFinset v ⊆ E0 := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_union, mem_incidenceFinset, mem_incidenceFinset,
        mk'_mem_incidenceSet_iff, mk'_mem_incidenceSet_iff] at he
      rw [hE0, Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
      rcases he with ⟨hxy, hux | huy⟩ | ⟨hxy, hvx | hvy⟩
      · subst hux
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hu
        · exact hNu _ hxy
      · subst huy
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hNu _ hxy.symm
        · exact hu
      · subst hvx
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hv
        · exact hNv _ hxy
      · subst hvy
        refine ⟨hxy, fun z hz => ?_⟩
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hNv _ hxy.symm
        · exact hv
  have hinter : G.incidenceFinset u ∩ G.incidenceFinset v = {s(u, v)} := by
    ext e
    rw [Finset.mem_inter, mem_incidenceFinset, mem_incidenceFinset, Finset.mem_singleton]
    have hset := G.incidenceSet_inter_incidenceSet_of_adj huv
    constructor
    · intro h
      have h' : e ∈ G.incidenceSet u ∩ G.incidenceSet v := h
      rw [hset] at h'
      exact h'
    · intro h
      have h' : e ∈ ({s(u, v)} : Set (Sym2 (Fin 25))) := h
      rw [← hset] at h'
      exact h'
  have hcard : (G.incidenceFinset u ∪ G.incidenceFinset v).card + 1
      = G.degree u + G.degree v := by
    have := Finset.card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
    rw [hinter, Finset.card_singleton, card_incidenceFinset_eq_degree,
      card_incidenceFinset_eq_degree] at this
    exact this
  have hdis : Disjoint (G.incidenceFinset u ∪ G.incidenceFinset v) T := by
    rw [Finset.disjoint_left]
    intro e he ht
    rcases Finset.mem_union.1 he with hu | hv
    · exact (hT e ht).2.2.1 (((mem_incidenceFinset _ _ _).1 hu).2)
    · exact (hT e ht).2.2.2 (((mem_incidenceFinset _ _ _).1 hv).2)
  have hsub : (G.incidenceFinset u ∪ G.incidenceFinset v) ∪ T ⊆ E0 :=
    Finset.union_subset hinc (fun e he => Finset.mem_filter.2 ⟨(hT e he).1, (hT e he).2.1⟩)
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at h
  omega

open scoped Classical in
lemma middle_edge_core_extra (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    {u v x y : Fin 25} (huv : G.Adj u v) (hux : G.Adj u x) (hvy : G.Adj v y)
    (hxy : G.Adj x y) (hxv : x ≠ v) (hyu : y ≠ u) :
    G.degree u + G.degree v ≤ (G.edgeFinset.filter
      (fun e => ∀ z ∈ e, z ∈ G.neighborFinset u ∪ G.neighborFinset v)).card := by
  have h := middle_edge_core_budget G huv {s(x,y)} (fun e he => by
    obtain rfl := Finset.mem_singleton.1 he
    refine ⟨by rwa [mem_edgeFinset, mem_edgeSet], ?_, ?_, ?_⟩
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_union.2 (Or.inl ((mem_neighborFinset _ _ _).2 hux))
      · exact Finset.mem_union.2 (Or.inr ((mem_neighborFinset _ _ _).2 hvy))
    · rw [Sym2.mem_iff, not_or]
      exact ⟨hux.ne, hyu.symm⟩
    · rw [Sym2.mem_iff, not_or]
      exact ⟨hxv.symm, hvy.ne⟩)
  rw [Finset.card_singleton] at h
  omega

lemma middle_diameter_tight (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    (v : Fin 25) :
    (∑ u ∈ G.neighborFinset v, G.degree u) = 24 ↔
      ∀ a b x, G.Adj v a → G.Adj v b → G.Adj a x → G.Adj b x → x ≠ v → a = b := by
  let B := fun u => insert u ((G.neighborFinset u).erase v)
  let C : Finset (Σ _ : Fin 25, Fin 25) := (G.neighborFinset v).sigma B
  let p : (Σ _ : Fin 25, Fin 25) → Fin 25 := fun x => x.2
  have hcard : ∀ u ∈ G.neighborFinset v, (B u).card = G.degree u := by
    intro u hu
    have hvu : v ∈ G.neighborFinset u :=
      (mem_neighborFinset _ _ _).2 ((mem_neighborFinset _ _ _).1 hu).symm
    have hnu : u ∉ (G.neighborFinset u).erase v := by simp
    dsimp [B]
    rw [Finset.card_insert_of_notMem hnu, Finset.card_erase_of_mem hvu,
      card_neighborFinset_eq_degree]
    have hp := Finset.card_pos.2 ⟨v, hvu⟩
    rw [card_neighborFinset_eq_degree] at hp
    omega
  have hC : C.card = ∑ u ∈ G.neighborFinset v, G.degree u := by
    change ((G.neighborFinset v).sigma B).card = _
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl hcard
  have hcover : C.image p = univ.erase v := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨⟨u,w⟩, hu, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨hu, hw⟩ := Finset.mem_sigma.1 hu
      rw [Finset.mem_erase]
      refine ⟨?_, mem_univ _⟩
      rcases Finset.mem_insert.1 hw with h | h
      · exact h.trans_ne ((mem_neighborFinset _ _ _).1 hu).ne.symm
      · exact Finset.ne_of_mem_erase h
    · intro x hx
      have hxv := Finset.ne_of_mem_erase hx
      by_cases hadj : G.Adj v x
      · exact Finset.mem_image.2 ⟨⟨x,x⟩, Finset.mem_sigma.2
          ⟨(mem_neighborFinset _ _ _).2 hadj, Finset.mem_insert_self _ _⟩, rfl⟩
      · obtain ⟨u, hvu, hxu⟩ := hdiam v x hxv.symm hadj
        exact Finset.mem_image.2 ⟨⟨u,x⟩, Finset.mem_sigma.2
          ⟨(mem_neighborFinset _ _ _).2 hvu, Finset.mem_insert_of_mem
            (Finset.mem_erase.2 ⟨hxv, (mem_neighborFinset _ _ _).2 hxu.symm⟩)⟩, rfl⟩
  have hn : (C.image p).card = 24 := by rw [hcover]; simp
  have hi : (∑ u ∈ G.neighborFinset v, G.degree u) = 24 ↔ Set.InjOn p C := by
    rw [← hC, ← Finset.card_image_iff, hn, eq_comm]
  rw [hi]
  constructor
  · intro hij a b x hva hvb hax hbx hxv
    have ha : (⟨a,x⟩ : Σ _ : Fin 25, Fin 25) ∈ C := Finset.mem_sigma.2
      ⟨(mem_neighborFinset _ _ _).2 hva, Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨hxv, (mem_neighborFinset _ _ _).2 hax⟩)⟩
    have hb : (⟨b,x⟩ : Σ _ : Fin 25, Fin 25) ∈ C := Finset.mem_sigma.2
      ⟨(mem_neighborFinset _ _ _).2 hvb, Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨hxv, (mem_neighborFinset _ _ _).2 hbx⟩)⟩
    exact congrArg Sigma.fst (hij ha hb rfl)
  · intro hu x hx y hy he
    obtain ⟨a,c⟩ := x
    obtain ⟨b,d⟩ := y
    change c = d at he
    subst d
    have ha : a ∈ G.neighborFinset v := (Finset.mem_sigma.1 hx).1
    have hb : b ∈ G.neighborFinset v := (Finset.mem_sigma.1 hy).1
    have hc : c ∈ B a := (Finset.mem_sigma.1 hx).2
    have hd : c ∈ B b := (Finset.mem_sigma.1 hy).2
    have hva := (mem_neighborFinset _ _ _).1 ha
    have hvb := (mem_neighborFinset _ _ _).1 hb
    rcases Finset.mem_insert.1 hc with hca | hc <;>
      rcases Finset.mem_insert.1 hd with he | hd
    · subst c
      subst b
      rfl
    · subst c
      exact (hG {v, b, a} (is3Clique_triple_iff.2
        ⟨hvb, hva, (mem_neighborFinset _ _ _).1 (Finset.mem_erase.1 hd).2⟩)).elim
    · subst c
      exact (hG {v, a, b} (is3Clique_triple_iff.2
        ⟨hva, hvb, (mem_neighborFinset _ _ _).1 (Finset.mem_erase.1 hc).2⟩)).elim
    · have hab := hu a b c hva hvb
        ((mem_neighborFinset _ _ _).1 (Finset.mem_erase.1 hc).2)
        ((mem_neighborFinset _ _ _).1 (Finset.mem_erase.1 hd).2)
        (Finset.ne_of_mem_erase hc)
      subst b
      rfl

lemma middle_neighbors_of_tight_bound (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    {v : Fin 25} {k : ℕ} (hW : 24 ≤ ∑ u ∈ G.neighborFinset v, G.degree u)
    (hcap : G.degree v * k = 24) (hk : ∀ u, G.Adj v u → G.degree u ≤ k) :
    ∀ u, G.Adj v u → G.degree u = k := by
  intro u hu
  by_contra h
  have hsum := Finset.sum_lt_sum (s := G.neighborFinset v)
    (fun w hw => hk w ((mem_neighborFinset _ _ _).1 hw))
    ⟨u, (mem_neighborFinset _ _ _).2 hu, lt_of_le_of_ne (hk u hu) h⟩
  rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, hcap] at hsum
  omega

open scoped Classical in
lemma middle_two_degree_cut (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    {p q : ℕ} (hpq : p ≠ q) {w : Fin 25} (hw : G.degree w = p)
    (hp : ∀ a b, G.degree a = p → G.Adj a b → G.degree b = q)
    (hq : ∀ a b, G.degree a = q → G.Adj a b → G.degree b = p) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  have htype : ∀ a, G.degree a = p ∨ G.degree a = q := by
    intro a
    by_cases h : a = w
    · exact Or.inl (h.symm ▸ hw)
    by_cases ha : G.Adj w a
    · exact Or.inr (hp w a hw ha)
    obtain ⟨b, hwb, hab⟩ := hdiam w a (Ne.symm h) ha
    exact Or.inl (hq b a (hp w b hw hwb) hab.symm)
  let S := (univ : Finset (Fin 25)).filter (fun v => G.degree v = p)
  refine ⟨S, ?_⟩
  have hS : G.edgeFinset.filter (Same S) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, same_mk] at he
      have hs : G.degree a = p ↔ G.degree b = p := by simpa [S] using he.2
      rcases htype a with ha | ha
      · exact hpq ((hs.1 ha).symm.trans (hp a b ha he.1))
      · exact hpq ((hs.2 (hq a b ha he.1)).symm.trans ha)
  simp [hS]

open scoped Classical in
lemma middle_edges_62 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    (hdeg : ∀ v, G.degree v ≤ 13)
    (hed : ∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card)
    (hm : G.edgeFinset.card = 62) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  by_contra! hlo
  have he : ∀ u v, G.Adj u v → G.degree u + G.degree v ≤ 11 := by
    intro u v huv
    obtain ⟨S, hS⟩ := exists_edge_cut G hG huv
    have := hlo S
    omega
  have hnSquare : ∀ u v x y, G.Adj u v → G.Adj u x → G.Adj v y → G.Adj x y →
      G.degree u + G.degree v = 11 → x ≠ v → y ≠ u → False := by
    intro u v x y huv hux hvy hxy hs hx hy
    have := middle_edge_core_extra G huv hux hvy hxy hx hy
    have := hed u v huv
    omega
  have hw := middle_diameter_weight G hdiam
  have hT := middle_diameter_tight G hG hdiam
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image univ (fun u => G.degree u) univ_nonempty
  set D := G.degree v with hD
  have hU : ∀ u, G.degree u ≤ D := fun u => hv u (mem_univ u)
  have hdUpper : D ≤ 8 := by
    have h := Finset.sum_le_sum (s := G.neighborFinset v) (g := fun _ => 11 - D)
      (f := fun u => G.degree u)
      (fun u hu => by have := he v u ((mem_neighborFinset _ _ _).1 hu); omega)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, ← hD] at h
    have hc := (hw v).trans h
    have hmax : D ≤ 13 := hdeg v
    by_contra! hbad
    interval_cases D <;> norm_num at hc
  have hLower (k : ℕ) (hk : D ≤ k) (u : Fin 25) : 24 ≤ G.degree u * k := by
    have h := Finset.sum_le_sum (s := G.neighborFinset u) (fun a _ => (hU a).trans hk)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree] at h
    exact (hw u).trans h
  have hsum : ∑ u, G.degree u = 124 := by rw [G.sum_degrees_eq_twice_card_edges, hm]
  have h5 : 5 ≤ D := by
    have h := Finset.sum_le_sum (s := (univ : Finset (Fin 25))) (fun u _ => hU u)
    simp only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    omega
  have hSat : ∀ u : Fin 25, (∀ a, G.Adj u a → G.degree u + G.degree a = 11) →
      ∑ a ∈ G.neighborFinset u, G.degree a = 24 := by
    intro u ha
    apply (hT u).2
    intro a b x hua hub hax hbx hx
    by_contra hab
    exact hnSquare u a b x hua hub hax hbx (ha a hua) (Ne.symm hab) hx
  have hContr : (∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25) → False := by
    rintro ⟨S, hS⟩
    exact (hlo S).not_ge hS
  by_cases h8 : D = 8
  · have h83 : ∀ a b, G.degree a = 8 → G.Adj a b → G.degree b = 3 := by
      intro a b ha hab
      have := he a b hab
      have := hLower 8 hdUpper b
      omega
    have h38 : ∀ a b, G.degree a = 3 → G.Adj a b → G.degree b = 8 := by
      intro a b ha
      exact middle_neighbors_of_tight_bound G (hw a) (by rw [ha]) (fun u _ => (hU u).trans hdUpper) b
    exact hContr (middle_two_degree_cut G hdiam (by decide) (hD ▸ h8) h83 h38)
  by_cases h7 : D = 7
  · have hdv : G.degree v = 7 := hD ▸ h7
    have hn : ∀ a, G.Adj v a → G.degree a = 4 := by
      intro a ha
      have := he v a ha
      have := hLower 7 (by omega) a
      omega
    have h24 := hSat v (fun a ha => by rw [hdv, hn a ha])
    have h28 : ∑ a ∈ G.neighborFinset v, G.degree a = 28 := by
      calc ∑ a ∈ G.neighborFinset v, G.degree a = ∑ a ∈ G.neighborFinset v, 4 :=
            Finset.sum_congr rfl (fun a ha => hn a ((mem_neighborFinset _ _ _).1 ha))
         _ = 28 := by rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, hdv]
    omega
  by_cases h6 : D = 6
  · have h4 : ∀ u, 4 ≤ G.degree u := fun u => by have := hLower 6 (by omega) u; omega
    have hd6 : ∀ u, G.degree u ≤ 6 := fun u => (hU u).trans (by omega)
    have h46 : ∀ a b, G.degree a = 4 → G.Adj a b → G.degree b = 6 := by
      intro a b ha
      exact middle_neighbors_of_tight_bound G (hw a) (by rw [ha]) (fun u _ => hd6 u) b
    have h44 : ∀ a, G.degree a = 4 → ∑ b ∈ G.neighborFinset a, G.degree b = 24 := by
      intro a ha
      calc ∑ b ∈ G.neighborFinset a, G.degree b = ∑ b ∈ G.neighborFinset a, 6 :=
            Finset.sum_congr rfl
              (fun b hb => h46 a b ha ((mem_neighborFinset _ _ _).1 hb))
        _ = 24 := by rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, ha]
    have h64 : ∀ a b, G.degree a = 6 → G.Adj a b → G.degree b = 4 := by
      intro a b ha hab
      have hza : ∑ c ∈ G.neighborFinset a, G.degree c = 24 := by
        apply (hT a).2
        intro x y z hax hay hxz hyz hza
        by_contra hxy
        have hbd := he a x hax
        have hl := h4 x
        by_cases hx : G.degree x = 4
        · have := (hT x).1 (h44 x hx) a z y hax.symm hxz hay hyz.symm (Ne.symm hxy)
          exact hza this.symm
        · exact hnSquare a x y z hax hay hxz hyz (by omega) (Ne.symm hxy) hza
      by_contra hb
      have hs := Finset.sum_lt_sum (s := G.neighborFinset a) (f := fun _ => 4)
        (fun u _ => h4 u) ⟨b, (mem_neighborFinset _ _ _).2 hab, by have := h4 b; omega⟩
      rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, ha, hza] at hs
      omega
    exact hContr (middle_two_degree_cut G hdiam (by decide) (hD ▸ h6) h64 h46)
  have hD5 : D = 5 := by omega
  have hconst : ∀ u, G.degree u = 5 := by
    intro u
    have := hLower 5 (by omega) u
    have := hU u
    omega
  simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

-- A fibre of size two contributes two points to the repeated part.
open scoped Classical in
lemma middle_repeated_fibers {X Y : Type} [DecidableEq Y] (C : Finset X) (p : X → Y)
    (huniq : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C,
      p a = p b → p a = p c → a ≠ b → a ≠ c → b = c) :
    2 * C.card ≤ 2 * (C.image p).card +
      (C.filter (fun a => 1 < (C.filter (fun b => p b = p a)).card)).card := by
  let Q := C.filter (fun a => 1 < (C.filter (fun b => p b = p a)).card)
  change 2 * C.card ≤ 2 * (C.image p).card + Q.card
  have hQ : (Q : Set X).MapsTo p (C.image p) :=
    fun a ha => Finset.mem_image_of_mem _ (Finset.mem_filter.1 ha).1
  rw [Finset.card_eq_sum_card_image p C, Finset.card_eq_sum_card_fiberwise hQ]
  rw [Finset.mul_sum]
  conv_rhs => rw [Finset.card_eq_sum_ones (C.image p), Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  let F := C.filter (fun a => p a = b)
  change 2 * F.card ≤ 2 * 1 + (Q.filter (fun a => p a = b)).card
  by_cases hb : 1 < F.card
  · obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.1 hb
    have hsub : F ⊆ {a, c} := by
      intro d hd
      by_cases had : a = d
      · exact Finset.mem_insert.2 (Or.inl had.symm)
      · have ha' := Finset.mem_filter.1 ha
        have hc' := Finset.mem_filter.1 hc
        have hd' := Finset.mem_filter.1 hd
        have heq := huniq a ha'.1 c hc'.1 d hd'.1 (ha'.2.trans hc'.2.symm)
          (ha'.2.trans hd'.2.symm) hac had
        exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 heq.symm))
    have htwo : F.card ≤ 2 := (Finset.card_le_card hsub).trans Finset.card_le_two
    have heq : Q.filter (fun a => p a = b) = F := by
      ext a
      simp only [Q, F, Finset.mem_filter]
      constructor
      · rintro ⟨⟨ha, _⟩, he⟩
        exact ⟨ha, he⟩
      · rintro ⟨ha, he⟩
        exact ⟨⟨ha, by rw [he]; exact hb⟩, he⟩
    rw [heq]
    omega
  · omega

open scoped Classical in
lemma middle_unique_square (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) {v a b x c y : Fin 25}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hax : G.Adj a x) (hbx : G.Adj b x) (hay : G.Adj a y) (hcy : G.Adj c y)
    (hx : x ≠ v) (hy : y ≠ v) (hab : a ≠ b) (hac : a ≠ c)
    (hE : (G.edgeFinset.filter
      (fun e => ∀ z ∈ e, z ∈ G.neighborFinset v ∪ G.neighborFinset a)).card
      ≤ G.degree v + G.degree a) :
    b = c ∧ x = y := by
  by_contra hne
  have hneq : s(b, x) ≠ s(c, y) := by
    intro h
    rcases Sym2.eq_iff.1 h with h | ⟨h, _⟩
    · exact hne h
    · have hx' : G.Adj v y := h ▸ hvb
      exact hG {v, a, y} (is3Clique_triple_iff.2 ⟨hva, hx', hay⟩)
  have hsingle : ∀ (b x : Fin 25), G.Adj v b → G.Adj a x → G.Adj b x →
      x ≠ v → a ≠ b → s(b,x) ∈ G.edgeFinset ∧
        (∀ z ∈ s(b,x), z ∈ G.neighborFinset v ∪ G.neighborFinset a) ∧
        v ∉ s(b,x) ∧ a ∉ s(b,x) := by
    intro b x hvb hax hbx hx hab
    refine ⟨by rwa [mem_edgeFinset, mem_edgeSet], ?_, ?_, ?_⟩
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_union.2 (Or.inl ((mem_neighborFinset _ _ _).2 hvb))
      · exact Finset.mem_union.2 (Or.inr ((mem_neighborFinset _ _ _).2 hax))
    · rw [Sym2.mem_iff, not_or]
      exact ⟨hvb.ne, hx.symm⟩
    · rw [Sym2.mem_iff, not_or]
      exact ⟨hab, hax.ne⟩
  have hb := hsingle b x hvb hax hbx hx hab
  have hc := hsingle c y hvc hay hcy hy hac
  have h := middle_edge_core_budget G hva {s(b,x), s(c,y)} (fun e he => by
    rw [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hb
    · exact hc)
  rw [Finset.card_pair hneq] at h
  omega

open scoped Classical in
lemma middle_diameter_duplicate_bound (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    (v : Fin 25) (R : Finset (Fin 25))
    (hrep : ∀ a b x, G.Adj v a → G.Adj v b → G.Adj a x → G.Adj b x →
      x ≠ v → a ≠ b → a ∈ R)
    (huniq : ∀ a b x c y, G.Adj v a → G.Adj v b → G.Adj v c →
      G.Adj a x → G.Adj b x → G.Adj a y → G.Adj c y →
      x ≠ v → y ≠ v → a ≠ b → a ≠ c → b = c ∧ x = y) :
    2 * (∑ u ∈ G.neighborFinset v, G.degree u) ≤ 48 + R.card := by
  let B := fun u => insert u ((G.neighborFinset u).erase v)
  let C : Finset (Σ _ : Fin 25, Fin 25) := (G.neighborFinset v).sigma B
  let p : (Σ _ : Fin 25, Fin 25) → Fin 25 := fun x => x.2
  have hcard : ∀ u ∈ G.neighborFinset v, (B u).card = G.degree u := by
    intro u hu
    have hvu : v ∈ G.neighborFinset u :=
      (mem_neighborFinset _ _ _).2 ((mem_neighborFinset _ _ _).1 hu).symm
    have hnu : u ∉ (G.neighborFinset u).erase v := by simp
    dsimp [B]
    rw [Finset.card_insert_of_notMem hnu, Finset.card_erase_of_mem hvu,
      card_neighborFinset_eq_degree]
    have hp := Finset.card_pos.2 ⟨v, hvu⟩
    rw [card_neighborFinset_eq_degree] at hp
    omega
  have hC : C.card = ∑ u ∈ G.neighborFinset v, G.degree u := by
    change ((G.neighborFinset v).sigma B).card = _
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl hcard
  have hcover : C.image p = univ.erase v := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨⟨u,w⟩, hu, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨hu, hw⟩ := Finset.mem_sigma.1 hu
      rw [Finset.mem_erase]
      refine ⟨?_, mem_univ _⟩
      rcases Finset.mem_insert.1 hw with h | h
      · exact h.trans_ne ((mem_neighborFinset _ _ _).1 hu).ne.symm
      · exact Finset.ne_of_mem_erase h
    · intro x hx
      have hxv := Finset.ne_of_mem_erase hx
      by_cases hadj : G.Adj v x
      · exact Finset.mem_image.2 ⟨⟨x,x⟩, Finset.mem_sigma.2
          ⟨(mem_neighborFinset _ _ _).2 hadj, Finset.mem_insert_self _ _⟩, rfl⟩
      · obtain ⟨u, hvu, hxu⟩ := hdiam v x hxv.symm hadj
        exact Finset.mem_image.2 ⟨⟨u,x⟩, Finset.mem_sigma.2
          ⟨(mem_neighborFinset _ _ _).2 hvu, Finset.mem_insert_of_mem
            (Finset.mem_erase.2 ⟨hxv, (mem_neighborFinset _ _ _).2 hxu.symm⟩)⟩, rfl⟩
  have hn : (C.image p).card = 24 := by rw [hcover]; simp
  have hpair : ∀ a b : (Σ _ : Fin 25, Fin 25), a ∈ C → b ∈ C → p a = p b → a ≠ b →
      G.Adj v a.1 ∧ G.Adj v b.1 ∧ G.Adj a.1 a.2 ∧ G.Adj b.1 a.2 ∧ a.2 ≠ v ∧ a.1 ≠ b.1 := by
    rintro ⟨a,x⟩ ⟨b,y⟩ ha hb hxy hab
    change x = y at hxy
    subst y
    have ha' : a ∈ G.neighborFinset v := (Finset.mem_sigma.1 ha).1
    have hb' : b ∈ G.neighborFinset v := (Finset.mem_sigma.1 hb).1
    have hx : x ∈ B a := (Finset.mem_sigma.1 ha).2
    have hy : x ∈ B b := (Finset.mem_sigma.1 hb).2
    have hva := (mem_neighborFinset _ _ _).1 ha'
    have hvb := (mem_neighborFinset _ _ _).1 hb'
    have hab' : a ≠ b := fun he => hab (by subst b; rfl)
    rcases Finset.mem_insert.1 hx with hxa | hx <;>
      rcases Finset.mem_insert.1 hy with hxb | hy
    · exact (hab' (hxa.symm.trans hxb)).elim
    · subst x
      exact (hG {v,b,a} (is3Clique_triple_iff.2
        ⟨hvb, hva, (mem_neighborFinset _ _ _).1 (Finset.mem_erase.1 hy).2⟩)).elim
    · subst x
      exact (hG {v,a,b} (is3Clique_triple_iff.2
        ⟨hva, hvb, (mem_neighborFinset _ _ _).1 (Finset.mem_erase.1 hx).2⟩)).elim
    · exact ⟨hva, hvb, (mem_neighborFinset _ _ _).1 (Finset.mem_erase.1 hx).2,
        (mem_neighborFinset _ _ _).1 (Finset.mem_erase.1 hy).2, Finset.ne_of_mem_erase hx, hab'⟩
  have hsame : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, p a = p b → p a = p c → a ≠ b → a ≠ c → b = c := by
    rintro ⟨a,w⟩ ha ⟨b,x⟩ hb ⟨c,y⟩ hc hx hy hab hac
    change w = x at hx
    change w = y at hy
    subst x
    subst y
    obtain ⟨hva, hvb, haw, hbw, hwv, hab'⟩ := hpair _ _ ha hb rfl hab
    obtain ⟨_, hvc, _, hcw, _, hac'⟩ := hpair _ _ ha hc rfl hac
    obtain ⟨he, _⟩ := huniq a b w c w hva hvb hvc haw hbw haw hcw hwv hwv hab' hac'
    subst c
    rfl
  let Q := C.filter (fun a => 1 < (C.filter (fun b => p b = p a)).card)
  have hmate : ∀ a ∈ Q, ∃ b ∈ C, p a = p b ∧ a ≠ b := by
    intro a ha
    obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.1 (Finset.mem_filter.1 ha).2
    by_cases hab : a = b
    · have hc' := Finset.mem_filter.1 hc
      exact ⟨c, hc'.1, hc'.2.symm, hab ▸ hbc⟩
    · have hb' := Finset.mem_filter.1 hb
      exact ⟨b, hb'.1, hb'.2.symm, hab⟩
  have hQ : Q.card ≤ R.card := by
    apply Finset.card_le_card_of_injOn Sigma.fst
    · intro a ha
      obtain ⟨b, hb, hp, hne⟩ := hmate a ha
      obtain ⟨hva, hvb, hax, hbx, hx, hab⟩ :=
        hpair a b (Finset.mem_filter.1 ha).1 hb hp hne
      exact hrep _ _ _ hva hvb hax hbx hx hab
    · rintro ⟨a,x⟩ ha ⟨b,y⟩ hq h
      change a = b at h
      subst b
      obtain ⟨b, hb, hb', hn⟩ := hmate _ ha
      obtain ⟨c, hc, hc', hn'⟩ := hmate _ hq
      obtain ⟨hva, hvb, hax, hbx, hx, hab⟩ :=
        hpair _ b (Finset.mem_filter.1 ha).1 hb hb' hn
      obtain ⟨_, hvc, hay, hcy, hy, hac⟩ :=
        hpair _ c (Finset.mem_filter.1 hq).1 hc hc' hn'
      obtain ⟨_, he⟩ := huniq a b.1 x c.1 y hva hvb hvc hax hbx hay hcy hx hy hab hac
      subst y
      rfl
  have h := middle_repeated_fibers C p hsame
  change 2 * C.card ≤ 2 * (C.image p).card + Q.card at h
  rw [hC, hn] at h
  omega

open scoped Classical in
lemma middle_edges_63 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    (hdeg : ∀ v, G.degree v ≤ 13)
    (hed : ∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card)
    (hm : G.edgeFinset.card = 63) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  by_contra! hlo
  have he : ∀ u v, G.Adj u v → G.degree u + G.degree v ≤ 12 := by
    intro u v huv
    obtain ⟨S, hS⟩ := exists_edge_cut G hG huv
    have := hlo S
    omega
  have hnSquare : ∀ u v x y, G.Adj u v → G.Adj u x → G.Adj v y → G.Adj x y →
      G.degree u + G.degree v = 12 → x ≠ v → y ≠ u → False := by
    intro u v x y huv hux hvy hxy hs hx hy
    have := middle_edge_core_extra G huv hux hvy hxy hx hy
    have := hed u v huv
    omega
  have hw := middle_diameter_weight G hdiam
  have hT := middle_diameter_tight G hG hdiam
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image univ (fun u => G.degree u) univ_nonempty
  set D := G.degree v with hD
  have hU : ∀ u, G.degree u ≤ D := fun u => hv u (mem_univ u)
  have hdUpper : D ≤ 9 := by
    have h := Finset.sum_le_sum (s := G.neighborFinset v) (g := fun _ => 12 - D)
      (f := fun u => G.degree u)
      (fun u hu => by have := he v u ((mem_neighborFinset _ _ _).1 hu); omega)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, ← hD] at h
    have hc := (hw v).trans h
    have hmax : D ≤ 13 := hdeg v
    by_contra! hbad
    interval_cases D <;> norm_num at hc
  have hLower (k : ℕ) (hk : D ≤ k) (u : Fin 25) : 24 ≤ G.degree u * k := by
    have h := Finset.sum_le_sum (s := G.neighborFinset u) (fun a _ => (hU a).trans hk)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree] at h
    exact (hw u).trans h
  have hsum : ∑ u, G.degree u = 126 := by rw [G.sum_degrees_eq_twice_card_edges, hm]
  have h5 : 5 ≤ D := by
    have h := Finset.sum_le_sum (s := (univ : Finset (Fin 25))) (fun u _ => hU u)
    simp only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    omega
  have hSat : ∀ u : Fin 25, (∀ a, G.Adj u a → G.degree u + G.degree a = 12) →
      ∑ a ∈ G.neighborFinset u, G.degree a = 24 := by
    intro u ha
    apply (hT u).2
    intro a b x hua hub hax hbx hx
    by_contra hab
    exact hnSquare u a b x hua hub hax hbx (ha a hua) (Ne.symm hab) hx
  have hContr : (∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25) → False := by
    rintro ⟨S, hS⟩
    exact (hlo S).not_ge hS
  have hApprox (u : Fin 25) (R : Finset (Fin 25))
      (hR : ∀ a b x, G.Adj u a → G.Adj u b → G.Adj a x → G.Adj b x →
        x ≠ u → a ≠ b → a ∈ R ∧ 11 ≤ G.degree u + G.degree a) :
      2 * (∑ a ∈ G.neighborFinset u, G.degree a) ≤ 48 + R.card := by
    apply middle_diameter_duplicate_bound G hG hdiam u R
    · intro a b x hua hub hax hbx hxu hab
      exact (hR a b x hua hub hax hbx hxu hab).1
    · intro a b x c y hua hub huc hax hbx hay hcy hxu hyu hab hac
      apply middle_unique_square G hG hua hub huc hax hbx hay hcy hxu hyu hab hac
      have := (hR a b x hua hub hax hbx hxu hab).2
      have := hed u a hua
      omega
  have hLowerBound (u : Fin 25) (k : ℕ) (hk : ∀ a, G.Adj u a → k ≤ G.degree a) :
      G.degree u * k ≤ ∑ a ∈ G.neighborFinset u, G.degree a := by
    have h := Finset.sum_le_sum (s := G.neighborFinset u) (f := fun _ => k)
      (fun a ha => hk a ((mem_neighborFinset _ _ _).1 ha))
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree] at h
    exact h
  have hTight (u : Fin 25) (k : ℕ) (hk : ∀ a, G.Adj u a → k ≤ G.degree a)
      (heq : G.degree u * k = ∑ a ∈ G.neighborFinset u, G.degree a) :
      ∀ a, G.Adj u a → G.degree a = k := by
    intro a ha
    by_contra hn
    have h := Finset.sum_lt_sum (s := G.neighborFinset u) (f := fun _ => k)
      (fun b hb => hk b ((mem_neighborFinset _ _ _).1 hb))
      ⟨a, (mem_neighborFinset _ _ _).2 ha, lt_of_le_of_ne (hk a ha) (Ne.symm hn)⟩
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, heq] at h
    omega
  by_cases h9 : D = 9
  · have hdv : G.degree v = 9 := hD ▸ h9
    have hn : ∀ a, G.Adj v a → G.degree a = 3 := by
      intro a ha
      have := he v a ha
      have := hLower 9 (by omega) a
      omega
    have h24 := hSat v (fun a ha => by rw [hdv, hn a ha])
    have hl := hLowerBound v 3 (fun a ha => (hn a ha).ge)
    omega
  by_cases h8 : D = 8
  · have h3 : ∀ a, 3 ≤ G.degree a := fun a => by have := hLower 8 (by omega) a; omega
    have hd8 : ∀ a, G.degree a ≤ 8 := fun a => (hU a).trans (by omega)
    have h38 : ∀ a b, G.degree a = 3 → G.Adj a b → G.degree b = 8 := by
      intro a b ha
      exact middle_neighbors_of_tight_bound G (hw a) (by rw [ha]) (fun u _ => hd8 u) b
    have h33 : ∀ a, G.degree a = 3 → ∑ b ∈ G.neighborFinset a, G.degree b = 24 := by
      intro a ha
      calc ∑ b ∈ G.neighborFinset a, G.degree b = ∑ b ∈ G.neighborFinset a, 8 :=
            Finset.sum_congr rfl (fun b hb => h38 a b ha ((mem_neighborFinset _ _ _).1 hb))
        _ = 24 := by rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, ha]
    have h83 : ∀ a b, G.degree a = 8 → G.Adj a b → G.degree b = 3 := by
      intro a b ha hab
      have hw' : ∑ x ∈ G.neighborFinset a, G.degree x = 24 := by
        apply (hT a).2
        intro x y z hax hay hxz hyz hza
        by_contra hxy
        by_cases hx : G.degree x = 3
        · have heq := (hT x).1 (h33 x hx) a z y hax.symm hxz hay hyz.symm (Ne.symm hxy)
          exact hza heq.symm
        · have := he a x hax
          have := h3 x
          exact hnSquare a x y z hax hay hxz hyz (by omega) (Ne.symm hxy) hza
      exact hTight a 3 (fun u _ => h3 u) (by rw [ha, hw']) b hab
    exact hContr (middle_two_degree_cut G hdiam (by decide) (hD ▸ h8) h83 h38)
  by_cases h7 : D = 7
  · have hdv : G.degree v = 7 := hD ▸ h7
    have h4 : ∀ a, 4 ≤ G.degree a := fun a => by have := hLower 7 (by omega) a; omega
    have h := hApprox v (G.neighborFinset v) (fun a _ _ hva _ _ _ _ _ =>
      ⟨(mem_neighborFinset _ _ _).2 hva, by have := h4 a; omega⟩)
    rw [card_neighborFinset_eq_degree] at h
    have hl := hLowerBound v 4 (fun u _ => h4 u)
    omega
  by_cases h6 : D = 6
  · have h4 : ∀ u, 4 ≤ G.degree u := fun u => by have := hLower 6 (by omega) u; omega
    have hd6 : ∀ u, G.degree u ≤ 6 := fun u => (hU u).trans (by omega)
    have h46 : ∀ a b, G.degree a = 4 → G.Adj a b → G.degree b = 6 := by
      intro a b ha
      exact middle_neighbors_of_tight_bound G (hw a) (by rw [ha]) (fun u _ => hd6 u) b
    have h44 : ∀ a, G.degree a = 4 → ∑ b ∈ G.neighborFinset a, G.degree b = 24 := by
      intro a ha
      calc ∑ b ∈ G.neighborFinset a, G.degree b = ∑ b ∈ G.neighborFinset a, 6 :=
            Finset.sum_congr rfl
              (fun b hb => h46 a b ha ((mem_neighborFinset _ _ _).1 hb))
        _ = 24 := by rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree, ha]
    have h64 : ∀ a b, G.degree a = 6 → G.Adj a b → G.degree b = 4 := by
      intro a b ha hab
      let R := (G.neighborFinset a).filter (fun x => G.degree x = 5)
      have h := hApprox a R (by
        intro x y z hax hay hxz hyz hza hxy
        have hx : G.degree x = 5 := by
          have := h4 x
          have := hd6 x
          by_contra hn
          by_cases hx4 : G.degree x = 4
          · have heq := (hT x).1 (h44 x hx4) a z y hax.symm hxz hay hyz.symm (Ne.symm hxy)
            exact hza heq.symm
          · exact hnSquare a x y z hax hay hxz hyz (by omega) (Ne.symm hxy) hza
        exact ⟨Finset.mem_filter.2 ⟨(mem_neighborFinset _ _ _).2 hax, hx⟩, by omega⟩)
      have hl : 24 + R.card ≤ ∑ x ∈ G.neighborFinset a, G.degree x := by
        have hs := Finset.sum_le_sum (s := G.neighborFinset a)
          (f := fun x => 4 + (if G.degree x = 5 then 1 else 0))
          (g := fun x => G.degree x)
          (fun x _ => by have := h4 x; split <;> omega)
        simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
          card_neighborFinset_eq_degree, ha, ← Finset.card_filter] at hs
        exact hs
      exact hTight a 4 (fun u _ => h4 u) (by rw [ha]; omega) b hab
    exact hContr (middle_two_degree_cut G hdiam (by decide) (hD ▸ h6) h64 h46)
  have hD5 : D = 5 := by omega
  have hconst : ∀ u, G.degree u = 5 := by
    intro u
    have := hLower 5 (by omega) u
    have := hU u
    omega
  simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

open scoped Classical in
lemma middle_cut_independent (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (S : Finset (Fin 25)) (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) :
    (G.edgeFinset.filter (Same S)).card + ∑ u ∈ S, G.degree u = G.edgeFinset.card := by
  have h1 : G.edgeFinset.filter (fun e => ¬ Same S e)
      = S.biUnion (fun u => G.incidenceFinset u) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, same_mk, Finset.mem_biUnion,
        mem_incidenceFinset, mk'_mem_incidenceSet_iff]
      constructor
      · rintro ⟨hxy, hn⟩
        by_cases hx : x ∈ S
        · exact ⟨x, hx, hxy, Or.inl rfl⟩
        · have hy : y ∈ S := by tauto
          exact ⟨y, hy, hxy, Or.inr rfl⟩
      · rintro ⟨u, hu, hxy, rfl | rfl⟩
        · exact ⟨hxy, fun hiff => hind _ hu _ (hiff.1 hu) hxy⟩
        · exact ⟨hxy, fun hiff => hind _ (hiff.2 hu) _ hu hxy⟩
  have h2 : (S.biUnion (fun u => G.incidenceFinset u)).card
      = ∑ u ∈ S, G.degree u := by
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl (fun u _ => card_incidenceFinset_eq_degree G u)
    · intro a ha b hb hab
      show Disjoint (G.incidenceFinset a) (G.incidenceFinset b)
      rw [Finset.disjoint_left]
      intro e hea heb
      rw [mem_incidenceFinset] at hea heb
      have hsub := G.incidenceSet_inter_incidenceSet_subset hab ⟨hea, heb⟩
      rw [Set.mem_singleton_iff] at hsub
      have hadj : G.Adj a b := by
        have := hea.1
        rw [hsub, mem_edgeSet] at this
        exact this
      exact hind a ha b hb hadj
  have h3 := Finset.card_filter_add_card_filter_not
    (s := G.edgeFinset) (fun e => Same S e)
  rw [h1, h2] at h3
  exact h3
lemma middle_outside_edge (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hm : 26 ≤ G.edgeFinset.card)
    (hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ G.edgeFinset.card - 26)
    {u v : Fin 25} (huv : G.Adj u v) :
    ((G.neighborFinset u ∪ G.neighborFinset v)ᶜ).card = 25 - (G.degree u + G.degree v) ∧
    52 ≤ ∑ x ∈ (G.neighborFinset u ∪ G.neighborFinset v)ᶜ, G.degree x := by
  have hdis : Disjoint (G.neighborFinset u) (G.neighborFinset v) :=
    Finset.disjoint_left.2 (fun x hx hy => nbhd_disj G hG huv x hx hy)
  constructor
  · rw [Finset.card_compl, Finset.card_union_of_disjoint hdis,
      card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, Fintype.card_fin]
  · have hs := Finset.sum_add_sum_compl (G.neighborFinset u ∪ G.neighborFinset v)
      (fun x => G.degree x)
    rw [Finset.sum_union hdis, G.sum_degrees_eq_twice_card_edges] at hs
    have := hA u
    have := hA v
    omega

lemma middle_deficit_118_twelve_table (d : ℕ) (hd : d ≤ 12) :
    d * (8 - d) + d * (11 - d) + 18 * d + 5 * (9 - d) ≤
      (8 * d - 92) + (11 * d - 92) + 173 := by
  interval_cases d <;> norm_num

lemma middle_deficit_118_thirteen_table (d : ℕ) (hd : d ≤ 13) :
    d * (10 - d) + 12 * d + 5 * (9 - d) ≤ (10 * d - 92) + 118 := by
  interval_cases d <;> norm_num

lemma middle_deficit_118_eleven (d : ℕ) (hd : d ≤ 11) :
    d + (9 - d) = 9 + (if d = 10 then 1 else 0) + (if d = 11 then 2 else 0) := by
  interval_cases d <;> norm_num

set_option maxHeartbeats 400000 in
open scoped Classical in
lemma middle_edges_118 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 13)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hm : G.edgeFinset.card = 118) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  have hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ 92 := by
    intro v
    have := cut_card_nbhd G hG v
    have := hnb v
    omega
  have hsum : ∑ v, G.degree v = 236 := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  set z := ∑ v : Fin 25, (9 - G.degree v) with hzdef
  have hlocal : ∀ v, 9 * G.degree v ≤ 92 + z := by
    intro v
    have hs : ∑ x ∈ G.neighborFinset v, 9 ≤
        ∑ x ∈ G.neighborFinset v, (G.degree x + (9 - G.degree x)) :=
      Finset.sum_le_sum (fun _ _ => by omega)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree,
      Finset.sum_add_distrib] at hs
    have hl : ∑ x ∈ G.neighborFinset v, (9 - G.degree x) ≤ z :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hA v
    omega
  have h10 := middle_deficit_bound G 92 10 hA
  have hD : ∀ v, G.degree v ≤ 11 := by
    have ht := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
      (fun v _ => middle_deficit_118_thirteen_table (G.degree v) (hdeg v))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hzdef] at ht
    have h12 : ∀ v, G.degree v ≤ 12 := by
      intro v
      have := hdeg v
      have := hlocal v
      omega
    have ht' := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
      (fun v _ => middle_deficit_118_twelve_table (G.degree v) (h12 v))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hzdef] at ht'
    have h8 := middle_deficit_bound G 92 8 hA
    have h11 := middle_deficit_bound G 92 11 hA
    intro v
    have := hlocal v
    omega
  let P := (univ : Finset (Fin 25)).filter (fun v => G.degree v = 11)
  let N := (univ : Finset (Fin 25)).filter (fun v => G.degree v = 10)
  have hP : ∀ v, v ∈ P ↔ G.degree v = 11 := fun v => by simp [P]
  have hN : ∀ v, v ∈ N ↔ G.degree v = 10 := fun v => by simp [N]
  have hc : N.card + 2 * P.card = 11 + z := by
    have h := Finset.sum_congr (rfl : (univ : Finset (Fin 25)) = univ)
      (fun v _ => middle_deficit_118_eleven (G.degree v) (hD v))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hsum, ← hzdef, Finset.sum_ite, Finset.sum_const_zero, add_zero, mul_one] at h
    change 236 + z = 225 + N.card + P.card * 2 at h
    omega
  have hf : ∀ d : ℕ, d ≤ 11 → d * (10 - d) +
      (if d = 10 then 17 else 0) + (if d = 11 then 27 else 0) ≤
      (10 * d - 92) + 9 + 7 * (9 - d) := by
    intro d hd
    interval_cases d <;> norm_num
  have hnum : 10 * z ≤ 38 + 7 * P.card := by
    have ht := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
      (fun v _ => hf (G.degree v) (hD v))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hzdef, Finset.sum_ite,
      Nat.mul_zero, add_zero] at ht
    change (∑ v, G.degree v * (10 - G.degree v)) + N.card * 17 + P.card * 27 ≤
      (∑ v, (10 * G.degree v - 92)) + 225 + 7 * z at ht
    omega
  have hroom : ∀ u v, G.Adj u v → G.degree u + G.degree v ≤ 20 := by
    intro u v huv
    obtain ⟨hc', hs⟩ := middle_outside_edge G hG (by omega) (by simpa [hm] using hA) huv
    have h := Finset.sum_le_sum (s := (G.neighborFinset u ∪ G.neighborFinset v)ᶜ)
      (fun w _ => hD w)
    rw [Finset.sum_const, smul_eq_mul, hc'] at h
    omega
  have hcut : ∀ T : Finset (Fin 25), T ⊆ N →
      (∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b) →
      93 ≤ 10 * T.card + 11 * P.card →
      ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
    intro T hTN hi ht
    have hdis : Disjoint T P := Finset.disjoint_left.2 (fun v hv hv' => by
      have := (hN v).1 (hTN hv)
      have := (hP v).1 hv'
      omega)
    have hInd : ∀ a ∈ T ∪ P, ∀ b ∈ T ∪ P, ¬ G.Adj a b := by
      intro a ha b hb hab
      have hr := hroom a b hab
      rcases Finset.mem_union.1 ha with ha | ha <;>
        rcases Finset.mem_union.1 hb with hb | hb
      · exact hi a ha b hb hab
      · have := (hN a).1 (hTN ha)
        have := (hP b).1 hb
        omega
      · have := (hP a).1 ha
        have := (hN b).1 (hTN hb)
        omega
      · have := (hP a).1 ha
        have := (hP b).1 hb
        omega
    have hTsum : ∑ v ∈ T, G.degree v = 10 * T.card := by
      rw [mul_comm 10, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl (fun v hv => (hN v).1 (hTN hv))
    have hPsum : ∑ v ∈ P, G.degree v = 11 * P.card := by
      rw [mul_comm 11, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl (fun v hv => (hP v).1 hv)
    have h := middle_cut_independent G (T ∪ P) hInd
    rw [Finset.sum_union hdis, hTsum, hPsum, hm] at h
    exact ⟨T ∪ P, by omega⟩
  by_cases hPempty : P = ∅
  · have hmax : ∀ v, G.degree v ≤ 10 := by
      intro v
      have h := hD v
      by_contra! hn
      have hv := (hP v).2 (by omega)
      simpa [hPempty] using hv
    have hp : P.card = 0 := by simp [hPempty]
    refine hcut N Finset.Subset.rfl ?_ (by omega)
    intro u hu v hv
    exact middle_no_degree_ten_edge G hG (by omega) hmax (by simpa [hm] using hA)
      ((hN u).1 hu) ((hN v).1 hv)
  have hz : 7 ≤ z := by
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hPempty
    have h := hlocal v
    rw [(hP v).1 hv] at h
    omega
  by_cases hi : ∀ a ∈ N, ∀ b ∈ N, ¬ G.Adj a b
  · exact hcut N Finset.Subset.rfl hi (by omega)
  push Not at hi
  obtain ⟨u, hu, v, hv, huv⟩ := hi
  have hr := (middle_outside_edge G hG (by omega) (by simpa [hm] using hA) huv).1
  rw [(hN u).1 hu, (hN v).1 hv] at hr
  have hsub : P ⊆ (G.neighborFinset u ∪ G.neighborFinset v)ᶜ := by
    intro x hx
    rw [Finset.mem_compl, Finset.mem_union]
    rintro (hx' | hx')
    · have := hroom u x ((mem_neighborFinset _ _ _).1 hx')
      have := (hN u).1 hu
      have := (hP x).1 hx
      omega
    · have := hroom v x ((mem_neighborFinset _ _ _).1 hx')
      have := (hN v).1 hv
      have := (hP x).1 hx
      omega
  have hpc := Finset.card_le_card hsub
  have hp : P.card = 5 := by omega
  have hn : 8 ≤ N.card := by omega
  have heq : P = (G.neighborFinset u ∪ G.neighborFinset v)ᶜ :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  let L := N ∩ G.neighborFinset u
  let R := N ∩ G.neighborFinset v
  have hLR : L ∪ R = N := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · exact (Finset.mem_inter.1 h).1
      · exact (Finset.mem_inter.1 h).1
    · intro x hx
      have hnP : x ∉ P := by
        intro hxp
        exact (by decide : (10 : ℕ) ≠ 11) (((hN x).1 hx).symm.trans ((hP x).1 hxp))
      have hmem : x ∈ G.neighborFinset u ∪ G.neighborFinset v := by
        by_contra hnm
        have hxc : x ∈ (G.neighborFinset u ∪ G.neighborFinset v)ᶜ :=
          Finset.mem_compl.2 hnm
        exact hnP (heq.symm ▸ hxc)
      apply Finset.mem_union.2
      exact (Finset.mem_union.1 hmem).imp
        (fun h => Finset.mem_inter.2 ⟨hx, h⟩) (fun h => Finset.mem_inter.2 ⟨hx, h⟩)
  have hlarge : 4 ≤ L.card ∨ 4 ≤ R.card := by
    have h := Finset.card_union_le (s := L) (t := R)
    rw [hLR] at h
    omega
  have hside : ∀ w : Fin 25, 4 ≤ (N ∩ G.neighborFinset w).card →
      ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
    intro w hc'
    refine hcut (N ∩ G.neighborFinset w) Finset.inter_subset_left ?_ (by omega)
    intro a ha b hb hab
    exact hG {w, a, b} (is3Clique_triple_iff.2
      ⟨(mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 ha).2,
        (mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 hb).2, hab⟩)
  exact hlarge.elim (hside u) (hside v)

lemma middle_deficit_117_thirteen_table (d : ℕ) (hd : d ≤ 13) :
    4 * (9 - d) + 20 * d ≤ d ^ 2 + 100 := by
  interval_cases d <;> norm_num

lemma middle_deficit_117_twelve_table (d : ℕ) (hd : d ≤ 12) :
    2 * (d * (8 - d)) + d * (11 - d) + 20 * d + 2 * (9 - d) +
      (if d ≤ 8 then 5 else 0) + (if d = 12 then 2 else 0) ≤
      2 * (8 * d - 91) + (11 * d - 91) + 191 := by
  interval_cases d <;> norm_num

open scoped Classical in
lemma middle_degree_cap_117 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 13)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hm : G.edgeFinset.card = 117) :
    ∀ v, G.degree v ≤ 11 := by
  have hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ 91 := by
    intro v
    have := cut_card_nbhd G hG v
    have := hnb v
    omega
  have hsum : ∑ v, G.degree v = 234 := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  set z := ∑ v : Fin 25, (9 - G.degree v) with hz
  have hlocal : ∀ v, 9 * G.degree v ≤ 91 + z := by
    intro v
    have hs : ∑ x ∈ G.neighborFinset v, 9 ≤
        ∑ x ∈ G.neighborFinset v, (G.degree x + (9 - G.degree x)) :=
      Finset.sum_le_sum (fun _ _ => by omega)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree,
      Finset.sum_add_distrib] at hs
    have hl : ∑ x ∈ G.neighborFinset v, (9 - G.degree x) ≤ z :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hA v
    omega
  have hd12 : ∀ v, G.degree v ≤ 12 := by
    have hsq := Finset.sum_le_sum (s := (univ : Finset (Fin 25))) (fun v _ => hA v)
    rw [sum_nbhd_deg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsq
    have h := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
      (fun v _ => middle_deficit_117_thirteen_table (G.degree v) (hdeg v))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hz] at h
    intro v
    have := hlocal v
    omega
  intro v
  by_contra! hn
  have hv : G.degree v = 12 := by have := hd12 v; omega
  let L := (univ : Finset (Fin 25)).filter (fun x => G.degree x ≤ 8)
  let H := (univ : Finset (Fin 25)).filter (fun x => G.degree x = 12)
  have hl : 12 ≤ L.card := by
    have hs : G.neighborFinset v ⊆ L := by
      intro u hu
      have hadj := (mem_neighborFinset _ _ _).1 hu
      obtain ⟨hc, hs⟩ := middle_outside_edge G hG (by omega) (by simpa [hm] using hA) hadj
      have h := Finset.sum_le_sum (s := (G.neighborFinset v ∪ G.neighborFinset u)ᶜ)
        (fun x _ => hd12 x)
      rw [Finset.sum_const, smul_eq_mul, hc, hv] at h
      exact Finset.mem_filter.2 ⟨mem_univ _, by omega⟩
    have h := Finset.card_le_card hs
    rwa [card_neighborFinset_eq_degree, hv] at h
  have hh : 1 ≤ H.card := Finset.card_pos.2 ⟨v, Finset.mem_filter.2 ⟨mem_univ _, hv⟩⟩
  have h8 := middle_deficit_bound G 91 8 hA
  have h11 := middle_deficit_bound G 91 11 hA
  have ht := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
    (fun v _ => middle_deficit_117_twelve_table (G.degree v) (hd12 v))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hz, Finset.sum_ite,
    Nat.mul_zero, add_zero] at ht
  change 2 * (∑ v, G.degree v * (8 - G.degree v)) +
      (∑ v, G.degree v * (11 - G.degree v)) + 20 * 234 + 2 * z + L.card * 5 + H.card * 2 ≤
      2 * (∑ v, (8 * G.degree v - 91)) + (∑ v, (11 * G.degree v - 91)) + 25 * 191 at ht
  have := hlocal v
  omega

open scoped Classical in
lemma middle_flip_outside (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (S : Finset (Fin 25)) {v : Fin 25} (hv : v ∉ S) :
    (G.edgeFinset.filter (Same (insert v S))).card + G.degree v =
      (G.edgeFinset.filter (Same S)).card + 2 * (G.neighborFinset v ∩ S).card := by
  let I := G.incidenceFinset v
  let R := G.edgeFinset \ I
  have hsplit (T : Finset (Fin 25)) :
      (G.edgeFinset.filter (Same T)).card = (R.filter (Same T)).card + (I.filter (Same T)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext e
      simp only [R, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      have hs : e ∈ I → e ∈ G.edgeFinset := fun h => G.incidenceFinset_subset v h
      tauto
    · exact Finset.disjoint_left.2 fun e he he' =>
        (Finset.mem_sdiff.1 (Finset.mem_filter.1 he).1).2 (Finset.mem_filter.1 he').1
  have hrest : R.filter (Same (insert v S)) = R.filter (Same S) := by
    apply Finset.filter_congr
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have he' := Finset.mem_sdiff.1 he
      rw [mem_edgeFinset, mem_edgeSet] at he'
      have hn : ¬ (v = x ∨ v = y) := by
        intro h
        apply he'.2
        exact (mem_incidenceFinset _ _ _).2 ((mk'_mem_incidenceSet_iff G).2 ⟨he'.1, h⟩)
      have hxv : x ≠ v := fun h => hn (Or.inl h.symm)
      have hyv : y ≠ v := fun h => hn (Or.inr h.symm)
      simp [same_mk, hxv, hyv]
  have hflip : I.filter (Same (insert v S)) = I.filter (fun e => ¬ Same S e) := by
    apply Finset.filter_congr
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have he' := (mk'_mem_incidenceSet_iff G).1 ((mem_incidenceFinset _ _ _).1 he)
      rcases he'.2 with rfl | rfl
      · simp [same_mk, hv, he'.1.ne.symm]
      · simp [same_mk, hv, he'.1.ne]
  let emb : Fin 25 ↪ Sym2 (Fin 25) :=
    ⟨fun x => s(v,x), fun a b he => (Sym2.eq_iff.1 he).elim And.right
      (fun he => he.2.trans he.1)⟩
  have hx : I.filter (fun e => ¬ Same S e) = (G.neighborFinset v ∩ S).map emb := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_filter, Finset.mem_map]
      constructor
      · rintro ⟨he, hs⟩
        have he' := (mk'_mem_incidenceSet_iff G).1 ((mem_incidenceFinset _ _ _).1 he)
        rw [same_mk] at hs
        rcases he'.2 with rfl | rfl
        · exact ⟨y, Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 he'.1,
            by simpa [hv] using hs⟩, rfl⟩
        · exact ⟨x, Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 he'.1.symm,
            by simpa [hv] using hs⟩, by exact Sym2.eq_swap⟩
      · rintro ⟨w, hw, he⟩
        change s(v,w) = s(x,y) at he
        rw [← he]
        have hw' := Finset.mem_inter.1 hw
        exact ⟨(mem_incidenceFinset _ _ _).2 ((mk'_mem_incidenceSet_iff G).2
          ⟨(mem_neighborFinset _ _ _).1 hw'.1, Or.inl rfl⟩), by simp [same_mk, hv, hw'.2]⟩
  have hc := Finset.card_filter_add_card_filter_not (s := I) (Same S)
  have hd : I.card = G.degree v := card_incidenceFinset_eq_degree G v
  have h₁ := hsplit S
  have h₂ := hsplit (insert v S)
  rw [hrest, hflip] at h₂
  rw [hx, Finset.card_map] at hc h₂
  omega

open scoped Classical in
lemma middle_edges_117_low_degree (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 10)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hm : G.edgeFinset.card = 117) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  let H := (univ : Finset (Fin 25)).filter (fun v => G.degree v = 10)
  have hH : ∀ v, v ∈ H ↔ G.degree v = 10 := fun v => by simp [H]
  have hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ G.edgeFinset.card - 26 := by
    intro v
    have := cut_card_nbhd G hG v
    have := hnb v
    omega
  have hI : ∀ a ∈ H, ∀ b ∈ H, ¬ G.Adj a b := fun a ha b hb =>
    middle_no_degree_ten_edge G hG (by omega) hdeg hA ((hH a).1 ha) ((hH b).1 hb)
  have hcut := middle_cut_independent G H hI
  have hHsum : ∑ v ∈ H, G.degree v = H.card * 10 := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl (fun v hv => (hH v).1 hv)
  rw [hHsum, hm] at hcut
  by_cases hbig : 10 ≤ H.card
  · exact ⟨H, by omega⟩
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hpart := Finset.sum_add_sum_compl H (fun v => G.degree v)
  rw [hsum, hm, hHsum] at hpart
  have hL : ∀ v ∈ Hᶜ, G.degree v ≤ 9 := by
    intro v hv
    have hh := Finset.mem_compl.1 hv
    rw [hH] at hh
    have := hdeg v
    omega
  have hLsum : ∑ v ∈ Hᶜ, G.degree v ≤ 9 * (25 - H.card) := by
    have h := Finset.sum_le_sum (s := Hᶜ) hL
    rw [Finset.sum_const, smul_eq_mul, Finset.card_compl, Fintype.card_fin, mul_comm] at h
    exact h
  have hHcard : H.card = 9 := by omega
  have hLdeg : ∀ v ∈ Hᶜ, G.degree v = 9 := by
    intro v hv
    by_contra hn
    have h := Finset.sum_lt_sum (s := Hᶜ) hL
      ⟨v, hv, lt_of_le_of_ne (hL v hv) hn⟩
    rw [Finset.sum_const, smul_eq_mul, Finset.card_compl, Fintype.card_fin, hHcard] at h
    omega
  let B := Hᶜ.filter (fun v => (G.neighborFinset v ∩ H).card ≤ 4)
  have hcover : G.edgeFinset.filter (Same H) ⊆ B.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, same_mk] at he
      have hx : x ∉ H := fun hx => hI x hx y (he.2.1 hx) he.1
      have hy : y ∉ H := fun hy => hx (he.2.2 hy)
      have hd : Disjoint (G.neighborFinset x ∩ H) (G.neighborFinset y ∩ H) :=
        Finset.disjoint_left.2 fun z hx hy => nbhd_disj G hG he.1 z
          (Finset.mem_inter.1 hx).1 (Finset.mem_inter.1 hy).1
      have hu := Finset.card_le_card
        (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right :
          (G.neighborFinset x ∩ H) ∪ (G.neighborFinset y ∩ H) ⊆ H)
      rw [Finset.card_union_of_disjoint hd, hHcard] at hu
      have ha : (G.neighborFinset x ∩ H).card ≤ 4 ∨ (G.neighborFinset y ∩ H).card ≤ 4 := by omega
      apply Finset.mem_biUnion.2
      rcases ha with ha | ha
      · exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_compl.2 hx, ha⟩,
          (mem_incidenceFinset _ _ _).2 ((mk'_mem_incidenceSet_iff G).2 ⟨he.1, Or.inl rfl⟩)⟩
      · exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_compl.2 hy, ha⟩,
          (mem_incidenceFinset _ _ _).2 ((mk'_mem_incidenceSet_iff G).2 ⟨he.1, Or.inr rfl⟩)⟩
  have hBsum : ∑ v ∈ B, (G.incidenceFinset v).card = B.card * 9 := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl (fun v hv => (card_incidenceFinset_eq_degree G v).trans
      (hLdeg v (Finset.mem_filter.1 hv).1))
  have hcard := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  rw [hBsum] at hcard
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (by omega : 2 < B.card)
  have hpair : ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ ¬ G.Adj a b := by
    by_cases hab' : G.Adj a b
    · by_cases hac' : G.Adj a c
      · exact ⟨b, hb, c, hc, hbc, fun hbc' =>
          hG {a,b,c} (is3Clique_triple_iff.2 ⟨hab', hac', hbc'⟩)⟩
      · exact ⟨a, ha, c, hc, hac, hac'⟩
    · exact ⟨a, ha, b, hb, hab, hab'⟩
  obtain ⟨a, ha, b, hb, hab, hn⟩ := hpair
  have ha' := Finset.mem_filter.1 ha
  have hb' := Finset.mem_filter.1 hb
  have hflip₁ := middle_flip_outside G H (Finset.mem_compl.1 ha'.1)
  have hflip₂ := middle_flip_outside G (insert a H)
    (show b ∉ insert a H from fun h => (Finset.mem_insert.1 h).elim
      (Ne.symm hab) (Finset.mem_compl.1 hb'.1))
  have he : G.neighborFinset b ∩ insert a H = G.neighborFinset b ∩ H := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, rfl | hh⟩
      · exact (hn ((mem_neighborFinset _ _ _).1 hx).symm).elim
      · exact ⟨hx, hh⟩
    · exact fun ⟨hx, hh⟩ => ⟨hx, Or.inr hh⟩
  rw [he, hLdeg b hb'.1] at hflip₂
  rw [hLdeg a ha'.1] at hflip₁
  exact ⟨insert b (insert a H), by omega⟩

lemma middle_deficit_117_eleven_table (d : ℕ) (hd : d ≤ 11) :
    d * (10 - d) + (if d = 10 then 18 else 0) + (if d = 11 then 28 else 0) ≤
      (10 * d - 91) + 9 + 7 * (9 - d) := by
  interval_cases d <;> norm_num

-- 117 edges with a vertex of degree 11: the degree-11 class P together with an independent
-- set of degree-10 vertices gives a cut crossing at least 92 edges.
set_option maxHeartbeats 400000 in
open scoped Classical in
lemma middle_edges_117_high_degree (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hD : ∀ v, G.degree v ≤ 11) (hex : ∃ v, G.degree v = 11)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hm : G.edgeFinset.card = 117) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  have hA : ∀ v, ∑ u ∈ G.neighborFinset v, G.degree u ≤ 91 := by
    intro v
    have := cut_card_nbhd G hG v
    have := hnb v
    omega
  have hsum : ∑ v, G.degree v = 234 := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  set z := ∑ v : Fin 25, (9 - G.degree v) with hzdef
  have hlocal : ∀ v, 9 * G.degree v ≤ 91 + z := by
    intro v
    have hs : ∑ x ∈ G.neighborFinset v, 9 ≤
        ∑ x ∈ G.neighborFinset v, (G.degree x + (9 - G.degree x)) :=
      Finset.sum_le_sum (fun _ _ => by omega)
    rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree,
      Finset.sum_add_distrib] at hs
    have hl : ∑ x ∈ G.neighborFinset v, (9 - G.degree x) ≤ z :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hA v
    omega
  have h10 := middle_deficit_bound G 91 10 hA
  let P := (univ : Finset (Fin 25)).filter (fun v => G.degree v = 11)
  let N := (univ : Finset (Fin 25)).filter (fun v => G.degree v = 10)
  have hP : ∀ v, v ∈ P ↔ G.degree v = 11 := fun v => by simp [P]
  have hN : ∀ v, v ∈ N ↔ G.degree v = 10 := fun v => by simp [N]
  have hc : N.card + 2 * P.card = 9 + z := by
    have h := Finset.sum_congr (rfl : (univ : Finset (Fin 25)) = univ)
      (fun v _ => middle_deficit_118_eleven (G.degree v) (hD v))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hsum, ← hzdef, Finset.sum_ite, Finset.sum_const_zero, add_zero, mul_one] at h
    change 234 + z = 225 + N.card + P.card * 2 at h
    omega
  have hnum : 11 * z ≤ 63 + 8 * P.card := by
    have ht := Finset.sum_le_sum (s := (univ : Finset (Fin 25)))
      (fun v _ => middle_deficit_117_eleven_table (G.degree v) (hD v))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hzdef, Finset.sum_ite,
      Nat.mul_zero, add_zero] at ht
    change (∑ v, G.degree v * (10 - G.degree v)) + N.card * 18 + P.card * 28 ≤
      (∑ v, (10 * G.degree v - 91)) + 225 + 7 * z at ht
    omega
  have hroom : ∀ u v, G.Adj u v → G.degree u + G.degree v ≤ 20 := by
    intro u v huv
    obtain ⟨hc', hs⟩ := middle_outside_edge G hG (by omega) (by simpa [hm] using hA) huv
    have h := Finset.sum_le_sum (s := (G.neighborFinset u ∪ G.neighborFinset v)ᶜ)
      (fun w _ => hD w)
    rw [Finset.sum_const, smul_eq_mul, hc'] at h
    omega
  have hcut : ∀ T : Finset (Fin 25), T ⊆ N →
      (∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b) →
      92 ≤ 10 * T.card + 11 * P.card →
      ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
    intro T hTN hi ht
    have hdis : Disjoint T P := Finset.disjoint_left.2 (fun v hv hv' => by
      have := (hN v).1 (hTN hv)
      have := (hP v).1 hv'
      omega)
    have hInd : ∀ a ∈ T ∪ P, ∀ b ∈ T ∪ P, ¬ G.Adj a b := by
      intro a ha b hb hab
      have hr := hroom a b hab
      rcases Finset.mem_union.1 ha with ha | ha <;>
        rcases Finset.mem_union.1 hb with hb | hb
      · exact hi a ha b hb hab
      · have := (hN a).1 (hTN ha)
        have := (hP b).1 hb
        omega
      · have := (hP a).1 ha
        have := (hN b).1 (hTN hb)
        omega
      · have := (hP a).1 ha
        have := (hP b).1 hb
        omega
    have hTsum : ∑ v ∈ T, G.degree v = 10 * T.card := by
      rw [mul_comm 10, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl (fun v hv => (hN v).1 (hTN hv))
    have hPsum : ∑ v ∈ P, G.degree v = 11 * P.card := by
      rw [mul_comm 11, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl (fun v hv => (hP v).1 hv)
    have h := middle_cut_independent G (T ∪ P) hInd
    rw [Finset.sum_union hdis, hTsum, hPsum, hm] at h
    exact ⟨T ∪ P, by omega⟩
  obtain ⟨v0, hv0⟩ := hex
  have hz : 8 ≤ z := by
    have h := hlocal v0
    rw [hv0] at h
    omega
  have hside : ∀ w : Fin 25, 92 ≤ 10 * (N ∩ G.neighborFinset w).card + 11 * P.card →
      ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
    intro w hc'
    refine hcut (N ∩ G.neighborFinset w) Finset.inter_subset_left ?_ hc'
    intro a ha b hb hab
    exact hG {w, a, b} (is3Clique_triple_iff.2
      ⟨(mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 ha).2,
        (mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 hb).2, hab⟩)
  by_cases hi : ∀ a ∈ N, ∀ b ∈ N, ¬ G.Adj a b
  · exact hcut N Finset.Subset.rfl hi (by omega)
  push Not at hi
  obtain ⟨u, hu, v, hv, huv⟩ := hi
  have hPout : ∀ a ∈ N, ∀ b ∈ N, P ⊆ (G.neighborFinset a ∪ G.neighborFinset b)ᶜ := by
    intro a ha b hb x hx
    rw [Finset.mem_compl, Finset.mem_union]
    rintro (hx' | hx')
    · have := hroom a x ((mem_neighborFinset _ _ _).1 hx')
      have := (hN a).1 ha
      have := (hP x).1 hx
      omega
    · have := hroom b x ((mem_neighborFinset _ _ _).1 hx')
      have := (hN b).1 hb
      have := (hP x).1 hx
      omega
  have hout : ∀ a ∈ N, ∀ b ∈ N, G.Adj a b →
      ((G.neighborFinset a ∪ G.neighborFinset b)ᶜ).card = 5 := by
    intro a ha b hb hab
    have hr := (middle_outside_edge G hG (by omega) (by simpa [hm] using hA) hab).1
    rw [(hN a).1 ha, (hN b).1 hb] at hr
    exact hr
  have hpc := Finset.card_le_card (hPout u hu v hv)
  rw [hout u hu v hv huv] at hpc
  by_cases hp : P.card = 5
  · have heq : P = (G.neighborFinset u ∪ G.neighborFinset v)ᶜ :=
      Finset.eq_of_subset_of_card_le (hPout u hu v hv) (by rw [hout u hu v hv huv]; omega)
    have hLR : N ⊆ (N ∩ G.neighborFinset u) ∪ (N ∩ G.neighborFinset v) := by
      intro x hx
      have hnP : x ∉ P := by
        intro hxp
        have := (hN x).1 hx
        have := (hP x).1 hxp
        omega
      have hmem : x ∈ G.neighborFinset u ∪ G.neighborFinset v := by
        by_contra hnm
        have hxc : x ∈ (G.neighborFinset u ∪ G.neighborFinset v)ᶜ :=
          Finset.mem_compl.2 hnm
        exact hnP (heq.symm ▸ hxc)
      exact Finset.mem_union.2 ((Finset.mem_union.1 hmem).imp
        (fun h => Finset.mem_inter.2 ⟨hx, h⟩) (fun h => Finset.mem_inter.2 ⟨hx, h⟩))
    have h := (Finset.card_le_card hLR).trans (Finset.card_union_le _ _)
    by_cases h4 : 4 ≤ (N ∩ G.neighborFinset u).card
    · exact hside u (by omega)
    · exact hside v (by omega)
  have hp4 : P.card = 4 := by omega
  have hNc : N.card = 9 := by omega
  have hpair : ∀ a ∈ N, ∀ b ∈ N, G.Adj a b →
      8 ≤ (N ∩ G.neighborFinset a).card + (N ∩ G.neighborFinset b).card := by
    intro a ha b hb hab
    have hsub := hPout a ha b hb
    have hcov : N ⊆ ((N ∩ G.neighborFinset a) ∪ (N ∩ G.neighborFinset b)) ∪
        ((G.neighborFinset a ∪ G.neighborFinset b)ᶜ \ P) := by
      intro x hx
      by_cases hxa : x ∈ G.neighborFinset a
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hx, hxa⟩))
      · by_cases hxb : x ∈ G.neighborFinset b
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hx, hxb⟩))
        · refine Finset.mem_union_right _
            (Finset.mem_sdiff.2 ⟨Finset.mem_compl.2 (fun h => ?_), ?_⟩)
          · exact (Finset.mem_union.1 h).elim hxa hxb
          · intro hxp
            have := (hN x).1 hx
            have := (hP x).1 hxp
            omega
    have h1 := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
    have h3 := Finset.card_union_le (N ∩ G.neighborFinset a) (N ∩ G.neighborFinset b)
    have h4 := Finset.card_sdiff_add_card_eq_card hsub
    rw [hout a ha b hb hab] at h4
    omega
  by_cases hbig : ∃ w, 5 ≤ (N ∩ G.neighborFinset w).card
  · obtain ⟨w, hw⟩ := hbig
    exact hside w (by omega)
  push Not at hbig
  have hfour : ∀ a ∈ N, ∀ b ∈ N, G.Adj a b → (N ∩ G.neighborFinset a).card = 4 := by
    intro a ha b hb hab
    have := hpair a ha b hb hab
    have := hbig a
    have := hbig b
    omega
  have hL4 := hfour u hu v hv huv
  have hR4 := hfour v hv u hu huv.symm
  have hdLR : Disjoint (N ∩ G.neighborFinset u) (N ∩ G.neighborFinset v) :=
    Finset.disjoint_left.2 fun y hy hy' =>
      nbhd_disj G hG huv y (Finset.mem_inter.1 hy).2 (Finset.mem_inter.1 hy').2
  have hsubLR : (N ∩ G.neighborFinset u) ∪ (N ∩ G.neighborFinset v) ⊆ N :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hrest := Finset.card_sdiff_add_card_eq_card hsubLR
  rw [Finset.card_union_of_disjoint hdLR] at hrest
  obtain ⟨x, hx⟩ := Finset.card_eq_one.1
    (show (N \ ((N ∩ G.neighborFinset u) ∪ (N ∩ G.neighborFinset v))).card = 1 by omega)
  have hxmem : x ∈ N \ ((N ∩ G.neighborFinset u) ∪ (N ∩ G.neighborFinset v)) := by
    rw [hx]
    exact Finset.mem_singleton_self x
  have hxN : x ∈ N := (Finset.mem_sdiff.1 hxmem).1
  have hxLR := (Finset.mem_sdiff.1 hxmem).2
  have hxL : x ∉ N ∩ G.neighborFinset u := fun h => hxLR (Finset.mem_union_left _ h)
  have hxR : x ∉ N ∩ G.neighborFinset v := fun h => hxLR (Finset.mem_union_right _ h)
  have hcov : ∀ y ∈ N, y ∈ N ∩ G.neighborFinset u ∨ y ∈ N ∩ G.neighborFinset v ∨ y = x := by
    intro y hy
    by_cases h : y ∈ (N ∩ G.neighborFinset u) ∪ (N ∩ G.neighborFinset v)
    · rcases Finset.mem_union.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have h' : y ∈ N \ ((N ∩ G.neighborFinset u) ∪ (N ∩ G.neighborFinset v)) :=
        Finset.mem_sdiff.2 ⟨hy, h⟩
      rw [hx, Finset.mem_singleton] at h'
      exact Or.inr (Or.inr h')
  have hins : ∀ w : Fin 25, (N ∩ G.neighborFinset w).card = 4 →
      x ∉ N ∩ G.neighborFinset w →
      (∀ a ∈ N ∩ G.neighborFinset w, ¬ G.Adj x a) →
      ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
    intro w hw4 hxw hxa
    refine hcut (insert x (N ∩ G.neighborFinset w))
      (Finset.insert_subset hxN Finset.inter_subset_left) ?_ ?_
    · intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with ha' | ha' <;>
        rcases Finset.mem_insert.1 hb with hb' | hb'
      · rw [ha', hb'] at hab
        exact hab.ne rfl
      · rw [ha'] at hab
        exact hxa b hb' hab
      · rw [hb'] at hab
        exact hxa a ha' hab.symm
      · exact hG {w, a, b} (is3Clique_triple_iff.2
          ⟨(mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 ha').2,
            (mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 hb').2, hab⟩)
    · rw [Finset.card_insert_eq_ite, if_neg hxw]
      omega
  by_cases hxl : ∀ a ∈ N ∩ G.neighborFinset u, ¬ G.Adj x a
  · exact hins u hL4 hxL hxl
  by_cases hxr : ∀ b ∈ N ∩ G.neighborFinset v, ¬ G.Adj x b
  · exact hins v hR4 hxR hxr
  push Not at hxl hxr
  obtain ⟨a', ha', hxa'⟩ := hxl
  obtain ⟨b', hb', hxb'⟩ := hxr
  have hkey : ∀ (w : Fin 25) (B : Finset (Fin 25)), B.card = 4 →
      (∀ y ∈ N, y ∈ N ∩ G.neighborFinset w ∨ y ∈ B ∨ y = x) →
      ∀ c ∈ N ∩ G.neighborFinset w, G.Adj x c → (B ∩ G.neighborFinset x).card ≤ 1 := by
    intro w B hB hcv c hc' hxc
    have hcN : c ∈ N := (Finset.mem_inter.1 hc').1
    have hwc : G.Adj w c := (mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 hc').2
    have h4c : (N ∩ G.neighborFinset c).card = 4 := hfour c hcN x hxN hxc.symm
    have hsub : N ∩ G.neighborFinset c ⊆ insert x (B \ G.neighborFinset x) := by
      intro y hy
      have hyN := (Finset.mem_inter.1 hy).1
      have hcy : G.Adj c y := (mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 hy).2
      rcases hcv y hyN with h | h | h
      · exact (hG {w, c, y} (is3Clique_triple_iff.2
          ⟨hwc, (mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 h).2, hcy⟩)).elim
      · refine Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨h, fun hyx => ?_⟩)
        exact hG {x, c, y} (is3Clique_triple_iff.2
          ⟨hxc, (mem_neighborFinset _ _ _).1 hyx, hcy⟩)
      · rw [h]
        exact Finset.mem_insert_self _ _
    have hc1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hc3 := Finset.card_sdiff_add_card_inter B (G.neighborFinset x)
    omega
  have hR1 := hkey u (N ∩ G.neighborFinset v) hR4 hcov a' ha' hxa'
  have hL1 := hkey v (N ∩ G.neighborFinset u) hL4
    (fun y hy => (hcov y hy).elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h)))) b' hb' hxb'
  have h4x : (N ∩ G.neighborFinset x).card = 4 :=
    hfour x hxN a' (Finset.mem_inter.1 ha').1 hxa'
  have hsubx : N ∩ G.neighborFinset x ⊆
      ((N ∩ G.neighborFinset u) ∩ G.neighborFinset x) ∪
        ((N ∩ G.neighborFinset v) ∩ G.neighborFinset x) := by
    intro y hy
    have hyN := (Finset.mem_inter.1 hy).1
    have hyx := (Finset.mem_inter.1 hy).2
    rcases hcov y hyN with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨h, hyx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h, hyx⟩)
    · rw [h] at hyx
      exact (((mem_neighborFinset _ _ _).1 hyx).ne rfl).elim
  have hfin := (Finset.card_le_card hsubx).trans (Finset.card_union_le _ _)
  exfalso
  omega

-- Inserting an independent set T (disjoint from S) into a cut S: exact change of the number
-- of same-side edges.  Building block for the degree-13 plan in notes_opus.md.
open scoped Classical in
lemma middle_insert_indep (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (S T : Finset (Fin 25)) (hdisj : Disjoint S T)
    (hind : ∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b) :
    (G.edgeFinset.filter (Same (S ∪ T))).card + ∑ u ∈ T, G.degree u =
      (G.edgeFinset.filter (Same S)).card + 2 * ∑ u ∈ T, (G.neighborFinset u ∩ S).card := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have hdisj' : Disjoint S T := Finset.disjoint_of_subset_right (Finset.subset_insert a T) hdisj
    have hind' : ∀ x ∈ T, ∀ y ∈ T, ¬ G.Adj x y := fun x hx y hy =>
      hind x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
    have haS : a ∉ S := fun h => Finset.disjoint_left.1 hdisj h (Finset.mem_insert_self a T)
    have hnot : a ∉ S ∪ T := by
      rw [Finset.mem_union]
      tauto
    have hfl := middle_flip_outside G (S ∪ T) hnot
    have hint : G.neighborFinset a ∩ (S ∪ T) = G.neighborFinset a ∩ S := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, mem_neighborFinset]
      constructor
      · rintro ⟨hax, hx | hx⟩
        · exact ⟨hax, hx⟩
        · exact (hind a (Finset.mem_insert_self a T) x (Finset.mem_insert_of_mem hx) hax).elim
      · rintro ⟨hax, hx⟩
        exact ⟨hax, Or.inl hx⟩
    rw [hint] at hfl
    have hU : S ∪ insert a T = insert a (S ∪ T) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [hU, Finset.sum_insert haT, Finset.sum_insert haT]
    have := ih hdisj' hind'
    omega

-- Building block for the degree-13 sub-case (paper proof in the notes): outside the closed
-- neighbourhood of a degree-13 vertex there are 11 vertices spanning at least 26 edges.
open scoped Classical in
lemma middle_deg13_outside (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (v : Fin 25) (hv : G.degree v = 13)
    (hnbv : 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card) :
    ((insert v (G.neighborFinset v))ᶜ).card = 11 ∧
    26 ≤ (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ (insert v (G.neighborFinset v))ᶜ)).card := by
  constructor
  · rw [Finset.card_compl, Finset.card_insert_of_notMem (by simp),
      card_neighborFinset_eq_degree, hv, Fintype.card_fin]
  · refine lt_of_lt_of_le hnbv (Finset.card_le_card ?_)
    intro e he
    rw [Finset.mem_filter] at he ⊢
    refine ⟨he.1, ?_⟩
    obtain ⟨he1, he2⟩ := he
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he1
      rw [same_mk] at he2
      have hx : x ∉ G.neighborFinset v := by
        intro hx
        exact nbhd_disj G hG ((mem_neighborFinset _ _ _).1 hx) y (he2.1 hx)
          ((mem_neighborFinset _ _ _).2 he1)
      have hy : y ∉ G.neighborFinset v := by
        intro hy
        exact nbhd_disj G hG ((mem_neighborFinset _ _ _).1 hy) x (he2.2 hy)
          ((mem_neighborFinset _ _ _).2 he1.symm)
      have hxv : x ≠ v := by
        rintro rfl
        exact hy ((mem_neighborFinset _ _ _).2 he1)
      have hyv : y ≠ v := by
        rintro rfl
        exact hx ((mem_neighborFinset _ _ _).2 he1.symm)
      intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · simp [hx, hxv]
      · simp [hy, hyv]

-- Building block for the degree-13 sub-case: an 11-vertex set spanning at least 26 edges
-- contains an edge pq whose two neighbourhoods inside the set cover at least 10 vertices.
open scoped Classical in
lemma middle_good_edge_in (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (T : Finset (Fin 25))
    (hT : T.card = 11)
    (he : 26 ≤ (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ T)).card) :
    ∃ p ∈ T, ∃ q ∈ T, G.Adj p q ∧
      10 ≤ (G.neighborFinset p ∩ T).card + (G.neighborFinset q ∩ T).card := by
  let H : SimpleGraph (Fin 25) :=
    { Adj := fun x y => G.Adj x y ∧ x ∈ T ∧ y ∈ T
      symm := ⟨fun x y h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun x h => h.1.ne rfl⟩ }
  have hHe : H.edgeFinset = G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ T) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_filter, Sym2.mem_iff]
      constructor
      · rintro ⟨h, hx, hy⟩
        exact ⟨h, by rintro z (rfl | rfl) <;> assumption⟩
      · rintro ⟨h, hz⟩
        exact ⟨h, hz x (Or.inl rfl), hz y (Or.inr rfl)⟩
  have hHn : ∀ x ∈ T, H.neighborFinset x = G.neighborFinset x ∩ T := by
    intro x hx
    ext y
    simp only [mem_neighborFinset, Finset.mem_inter]
    show (G.Adj x y ∧ x ∈ T ∧ y ∈ T) ↔ _
    tauto
  have hHn0 : ∀ x ∉ T, H.neighborFinset x = ∅ := by
    intro x hx
    ext y
    simp only [mem_neighborFinset, Finset.notMem_empty, iff_false]
    exact fun h => hx h.2.1
  have hHd0 : ∀ x ∉ T, H.degree x = 0 := by
    intro x hx
    rw [← card_neighborFinset_eq_degree, hHn0 x hx, Finset.card_empty]
  have hE : 26 ≤ H.edgeFinset.card := by rw [hHe]; exact he
  have hsumdeg : ∑ x ∈ T, H.degree x = 2 * H.edgeFinset.card := by
    rw [← sum_degrees_eq_twice_card_edges]
    apply Finset.sum_subset (Finset.subset_univ T)
    intro x _ hx
    exact hHd0 x hx
  have hsq : ∑ x ∈ T, H.degree x ^ 2 = ∑ x, H.degree x ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ T)
    intro x _ hx
    rw [hHd0 x hx]
    rfl
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image univ
    (fun u => ∑ w ∈ H.neighborFinset u, H.degree w) univ_nonempty
  have hW : ∑ v, ∑ w ∈ H.neighborFinset v, H.degree w
      ≤ 11 * ∑ w ∈ H.neighborFinset u, H.degree w := by
    rw [← Finset.sum_subset (Finset.subset_univ T)
      (fun x _ hx => by rw [hHn0 x hx, Finset.sum_empty])]
    calc ∑ v ∈ T, ∑ w ∈ H.neighborFinset v, H.degree w
        ≤ ∑ v ∈ T, ∑ w ∈ H.neighborFinset u, H.degree w :=
          Finset.sum_le_sum (fun v _ => hu v (mem_univ v))
      _ = 11 * ∑ w ∈ H.neighborFinset u, H.degree w := by
          rw [Finset.sum_const, hT, smul_eq_mul]
  rw [sum_nbhd_deg] at hW
  have hcs := sq_sum_le_card_mul_sum_sq (s := T) (f := fun v => H.degree v)
  simp only [Nat.cast_id] at hcs
  rw [hsumdeg, hT, hsq] at hcs
  generalize hD : ∑ x, H.degree x ^ 2 = D at hW hcs
  generalize hM : H.edgeFinset.card = M at hE hcs
  by_cases hne : (H.neighborFinset u).Nonempty
  · obtain ⟨v, hv, hvmax⟩ :=
      Finset.exists_max_image (H.neighborFinset u) (fun w => H.degree w) hne
    have huv : H.Adj u v := (mem_neighborFinset _ _ _).1 hv
    have huT : u ∈ T := huv.2.1
    have hvT : v ∈ T := huv.2.2
    have hSle : ∑ w ∈ H.neighborFinset u, H.degree w ≤ H.degree u * H.degree v := by
      calc ∑ w ∈ H.neighborFinset u, H.degree w
          ≤ ∑ w ∈ H.neighborFinset u, H.degree v := Finset.sum_le_sum (fun w hw => hvmax w hw)
        _ = H.degree u * H.degree v := by
            rw [Finset.sum_const, card_neighborFinset_eq_degree, smul_eq_mul]
    have hdu : H.degree u = (G.neighborFinset u ∩ T).card := by
      rw [← card_neighborFinset_eq_degree, hHn u huT]
    have hdv : H.degree v = (G.neighborFinset v ∩ T).card := by
      rw [← card_neighborFinset_eq_degree, hHn v hvT]
    refine ⟨u, huT, v, hvT, huv.1, ?_⟩
    rw [← hdu, ← hdv]
    generalize hSu : ∑ w ∈ H.neighborFinset u, H.degree w = Su at hW hSle
    generalize H.degree u = a at hSle ⊢
    generalize H.degree v = b at hSle ⊢
    have key : (4 * M) * (4 * M) ≤ (11 * (a + b)) * (11 * (a + b)) := by
      have h1 : (2 * (M : ℤ)) ^ 2 ≤ 11 * (D : ℤ) := by exact_mod_cast hcs
      have h2 : (D : ℤ) ≤ 11 * (Su : ℤ) := by exact_mod_cast hW
      have h3 : (Su : ℤ) ≤ (a : ℤ) * b := by exact_mod_cast hSle
      have : (4 * (M : ℤ)) * (4 * M) ≤ (11 * ((a : ℤ) + b)) * (11 * ((a : ℤ) + b)) := by
        nlinarith [sq_nonneg ((a : ℤ) - b)]
      exact_mod_cast this
    have := Nat.mul_self_le_mul_self_iff.1 key
    omega
  · exfalso
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hW
    have hD0 : D = 0 := by omega
    rw [hD0] at hcs
    have : (2 * M) ^ 2 = 0 := by omega
    have : M = 0 := by
      rcases Nat.eq_zero_of_le_zero (le_of_eq this) with h
      simp at this
      omega
    omega

-- Handshake inside a vertex set T.
open scoped Classical in
lemma middle_sum_deg_in (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (T : Finset (Fin 25)) :
    ∑ y ∈ T, (G.neighborFinset y ∩ T).card =
      2 * (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ T)).card := by
  let H : SimpleGraph (Fin 25) :=
    { Adj := fun x y => G.Adj x y ∧ x ∈ T ∧ y ∈ T
      symm := ⟨fun x y h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun x h => h.1.ne rfl⟩ }
  have hHe : H.edgeFinset = G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ T) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_filter, Sym2.mem_iff]
      constructor
      · rintro ⟨h, hx, hy⟩
        exact ⟨h, by rintro z (rfl | rfl) <;> assumption⟩
      · rintro ⟨h, hz⟩
        exact ⟨h, hz x (Or.inl rfl), hz y (Or.inr rfl)⟩
  have hHn : ∀ x ∈ T, H.neighborFinset x = G.neighborFinset x ∩ T := by
    intro x hx
    ext y
    simp only [mem_neighborFinset, Finset.mem_inter]
    show (G.Adj x y ∧ x ∈ T ∧ y ∈ T) ↔ _
    tauto
  have hHd0 : ∀ x ∉ T, H.degree x = 0 := by
    intro x hx
    rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero]
    ext y
    simp only [mem_neighborFinset, Finset.notMem_empty, iff_false]
    exact fun h => hx h.2.1
  rw [← hHe, ← sum_degrees_eq_twice_card_edges,
    ← Finset.sum_subset (Finset.subset_univ T) (fun x _ hx => hHd0 x hx)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← card_neighborFinset_eq_degree, hHn x hx]

-- Building block for the degree-13 sub-case: an 11-vertex triangle-free set spanning at least
-- 26 edges has a bipartition with at most one edge inside its parts.
open scoped Classical in
lemma middle_bip_in (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (T : Finset (Fin 25)) (hT : T.card = 11)
    (he : 26 ≤ (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ T)).card) :
    ∃ X ⊆ T, (G.edgeFinset.filter (fun e => (∀ w ∈ e, w ∈ T) ∧ Same X e)).card ≤ 1 := by
  obtain ⟨p, hp, q, hq, hpq, h10⟩ := middle_good_edge_in G T hT he
  set A := G.neighborFinset p ∩ T with hA
  set B := G.neighborFinset q ∩ T with hB
  have hAind : ∀ y ∈ A, ∀ z ∈ A, ¬ G.Adj y z := by
    intro y hy z hz hyz
    rw [hA, Finset.mem_inter, mem_neighborFinset] at hy hz
    exact hG {p, y, z} (is3Clique_triple_iff.2 ⟨hy.1, hz.1, hyz⟩)
  have hBind : ∀ y ∈ B, ∀ z ∈ B, ¬ G.Adj y z := by
    intro y hy z hz hyz
    rw [hB, Finset.mem_inter, mem_neighborFinset] at hy hz
    exact hG {q, y, z} (is3Clique_triple_iff.2 ⟨hy.1, hz.1, hyz⟩)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    rw [hA, Finset.mem_inter] at hy
    rw [hB, Finset.mem_inter] at hy'
    exact nbhd_disj G hG hpq y hy.1 hy'.1
  have hAT : A ⊆ T := Finset.inter_subset_right
  have hBT : B ⊆ T := Finset.inter_subset_right
  have hABT : A ∪ B ⊆ T := Finset.union_subset hAT hBT
  have hcardU : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
  have hrest : (T \ (A ∪ B)).card + (A.card + B.card) = 11 := by
    rw [← hcardU, Finset.card_sdiff_add_card_eq_card hABT, hT]
  have himg : ∀ (X : Finset (Fin 25)) (x : Fin 25) (W : Finset (Fin 25)),
      (∀ y z, G.Adj y z → y ∈ T → z ∈ T → (y ∈ X ↔ z ∈ X) →
        (y = x ∧ z ∈ W) ∨ (z = x ∧ y ∈ W)) →
      (G.edgeFinset.filter (fun e => (∀ w ∈ e, w ∈ T) ∧ Same X e)).card ≤ W.card := by
    intro X x W hc
    calc _ ≤ (W.image (fun y => s(x, y))).card := by
          apply Finset.card_le_card
          intro e he
          induction e using Sym2.ind with
          | h y z =>
            rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, same_mk] at he
            rw [Finset.mem_image]
            rcases hc y z he.1 (he.2.1 y (Sym2.mem_mk_left y z))
              (he.2.1 z (Sym2.mem_mk_right y z)) he.2.2 with ⟨rfl, hz⟩ | ⟨rfl, hy⟩
            · exact ⟨z, hz, rfl⟩
            · exact ⟨y, hy, Sym2.eq_swap⟩
      _ ≤ W.card := Finset.card_image_le
  have hcases : (T \ (A ∪ B)).card = 0 ∨ (T \ (A ∪ B)).card = 1 := by omega
  rcases hcases with h0 | h1
  · -- T is covered by A and B
    have hcov : ∀ y ∈ T, y ∈ A ∨ y ∈ B := by
      intro y hy
      by_contra hn
      have : y ∈ T \ (A ∪ B) := by
        rw [Finset.mem_sdiff, Finset.mem_union]
        exact ⟨hy, hn⟩
      rw [Finset.card_eq_zero] at h0
      rw [h0] at this
      exact Finset.notMem_empty y this
    refine ⟨A, hAT, le_trans (himg A p ∅ ?_) (by simp)⟩
    intro y z hyz hy hz hiff
    exfalso
    by_cases hyA : y ∈ A
    · exact hAind y hyA z (hiff.1 hyA) hyz
    · have hzA : z ∉ A := fun h => hyA (hiff.2 h)
      have hyB := (hcov y hy).resolve_left hyA
      have hzB := (hcov z hz).resolve_left hzA
      exact hBind y hyB z hzB hyz
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
    have hxm : x ∈ T \ (A ∪ B) := by rw [hx]; exact Finset.mem_singleton_self x
    rw [Finset.mem_sdiff, Finset.mem_union] at hxm
    have hxT : x ∈ T := hxm.1
    have hxA : x ∉ A := fun h => hxm.2 (Or.inl h)
    have hxB : x ∉ B := fun h => hxm.2 (Or.inr h)
    have hcov : ∀ y ∈ T, y ∈ A ∨ y ∈ B ∨ y = x := by
      intro y hy
      by_contra hn
      push Not at hn
      have : y ∈ T \ (A ∪ B) := by
        rw [Finset.mem_sdiff, Finset.mem_union]
        exact ⟨hy, fun h => h.elim hn.1 hn.2.1⟩
      rw [hx, Finset.mem_singleton] at this
      exact hn.2.2 this
    by_cases ha : (G.neighborFinset x ∩ A).card ≤ 1
    · refine ⟨insert x A, Finset.insert_subset hxT hAT,
        le_trans (himg (insert x A) x (G.neighborFinset x ∩ A) ?_) ha⟩
      intro y z hyz hy hz hiff
      simp only [Finset.mem_insert] at hiff
      by_cases hyX : y = x ∨ y ∈ A
      · have hzX := hiff.1 hyX
        rcases hyX with rfl | hyA
        · rcases hzX with rfl | hzA
          · exact (hyz.ne rfl).elim
          · exact Or.inl ⟨rfl, Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hyz, hzA⟩⟩
        · rcases hzX with rfl | hzA
          · exact Or.inr ⟨rfl, Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hyz.symm, hyA⟩⟩
          · exact (hAind y hyA z hzA hyz).elim
      · have hzX : ¬ (z = x ∨ z ∈ A) := fun h => hyX (hiff.2 h)
        push Not at hyX hzX
        have hyB := ((hcov y hy).resolve_left hyX.2).resolve_right hyX.1
        have hzB := ((hcov z hz).resolve_left hzX.2).resolve_right hzX.1
        exact (hBind y hyB z hzB hyz).elim
    · by_cases hb : (G.neighborFinset x ∩ B).card ≤ 1
      · refine ⟨A, hAT, le_trans (himg A x (G.neighborFinset x ∩ B) ?_) hb⟩
        intro y z hyz hy hz hiff
        by_cases hyA : y ∈ A
        · exact (hAind y hyA z (hiff.1 hyA) hyz).elim
        · have hzA : z ∉ A := fun h => hyA (hiff.2 h)
          rcases (hcov y hy).resolve_left hyA with hyB | rfl
          · rcases (hcov z hz).resolve_left hzA with hzB | rfl
            · exact (hBind y hyB z hzB hyz).elim
            · exact Or.inr ⟨rfl, Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hyz.symm, hyB⟩⟩
          · rcases (hcov z hz).resolve_left hzA with hzB | rfl
            · exact Or.inl ⟨rfl, Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hyz, hzB⟩⟩
            · exact (hyz.ne rfl).elim
      · exfalso
        push Not at ha hb
        set a := (G.neighborFinset x ∩ A).card with hadef
        set b := (G.neighborFinset x ∩ B).card with hbdef
        have hsum := middle_sum_deg_in G T
        have hTeq : T = insert x (A ∪ B) := by
          ext y
          simp only [Finset.mem_insert, Finset.mem_union]
          constructor
          · intro hy
            rcases hcov y hy with h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact Or.inl h
          · rintro (rfl | h | h)
            · exact hxT
            · exact hAT h
            · exact hBT h
        have hxU : x ∉ A ∪ B := fun h => (Finset.mem_union.1 h).elim hxA hxB
        have hsplit : ∑ y ∈ T, (G.neighborFinset y ∩ T).card =
            (G.neighborFinset x ∩ T).card + (∑ y ∈ A, (G.neighborFinset y ∩ T).card +
              ∑ y ∈ B, (G.neighborFinset y ∩ T).card) := by
          conv_lhs => rw [hTeq]
          rw [Finset.sum_insert hxU, Finset.sum_union hdisj, ← hTeq]
        -- degree of x inside T
        have hdx : (G.neighborFinset x ∩ T).card ≤ a + b := by
          calc (G.neighborFinset x ∩ T).card
              ≤ ((G.neighborFinset x ∩ A) ∪ (G.neighborFinset x ∩ B)).card := by
                apply Finset.card_le_card
                intro y hy
                rw [Finset.mem_inter] at hy
                rcases hcov y hy.2 with h | h | rfl
                · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2 ⟨hy.1, h⟩))
                · exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨hy.1, h⟩))
                · exact (((mem_neighborFinset _ _ _).1 hy.1).ne rfl).elim
            _ ≤ a + b := Finset.card_union_le _ _
        -- per-vertex bound on A
        have hvA : ∀ y ∈ A, (G.neighborFinset y ∩ T).card + b * (if G.Adj y x then 1 else 0)
            ≤ B.card + (if G.Adj y x then 1 else 0) := by
          intro y hy
          split_ifs with hyx
          · have hsub : G.neighborFinset y ∩ T ⊆ insert x (B \ (G.neighborFinset x ∩ B)) := by
              intro z hz
              rw [Finset.mem_inter, mem_neighborFinset] at hz
              rcases hcov z hz.2 with hzA | hzB | rfl
              · exact (hAind y hy z hzA hz.1).elim
              · refine Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨hzB, fun h => ?_⟩)
                exact hG {x, y, z} (is3Clique_triple_iff.2
                  ⟨hyx.symm, (mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 h).1, hz.1⟩)
              · exact Finset.mem_insert_self _ _
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_insert_le x (B \ (G.neighborFinset x ∩ B))
            have h3 := Finset.card_sdiff_add_card_eq_card
              (Finset.inter_subset_right : G.neighborFinset x ∩ B ⊆ B)
            omega
          · have hsub : G.neighborFinset y ∩ T ⊆ B := by
              intro z hz
              rw [Finset.mem_inter, mem_neighborFinset] at hz
              rcases hcov z hz.2 with hzA | hzB | rfl
              · exact (hAind y hy z hzA hz.1).elim
              · exact hzB
              · exact (hyx hz.1).elim
            have := Finset.card_le_card hsub
            omega
        have hvB : ∀ y ∈ B, (G.neighborFinset y ∩ T).card + a * (if G.Adj y x then 1 else 0)
            ≤ A.card + (if G.Adj y x then 1 else 0) := by
          intro y hy
          split_ifs with hyx
          · have hsub : G.neighborFinset y ∩ T ⊆ insert x (A \ (G.neighborFinset x ∩ A)) := by
              intro z hz
              rw [Finset.mem_inter, mem_neighborFinset] at hz
              rcases hcov z hz.2 with hzA | hzB | rfl
              · refine Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨hzA, fun h => ?_⟩)
                exact hG {x, y, z} (is3Clique_triple_iff.2
                  ⟨hyx.symm, (mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 h).1, hz.1⟩)
              · exact (hBind y hy z hzB hz.1).elim
              · exact Finset.mem_insert_self _ _
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_insert_le x (A \ (G.neighborFinset x ∩ A))
            have h3 := Finset.card_sdiff_add_card_eq_card
              (Finset.inter_subset_right : G.neighborFinset x ∩ A ⊆ A)
            omega
          · have hsub : G.neighborFinset y ∩ T ⊆ A := by
              intro z hz
              rw [Finset.mem_inter, mem_neighborFinset] at hz
              rcases hcov z hz.2 with hzA | hzB | rfl
              · exact hzA
              · exact (hBind y hy z hzB hz.1).elim
              · exact (hyx hz.1).elim
            have := Finset.card_le_card hsub
            omega
        have hcntA : ∑ y ∈ A, (if G.Adj y x then 1 else 0) = a := by
          rw [Finset.sum_boole, hadef]
          simp only [Nat.cast_id]
          congr 1
          ext y
          simp only [Finset.mem_filter, Finset.mem_inter, mem_neighborFinset]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h2.symm, h1⟩
          · rintro ⟨h1, h2⟩; exact ⟨h2, h1.symm⟩
        have hcntB : ∑ y ∈ B, (if G.Adj y x then 1 else 0) = b := by
          rw [Finset.sum_boole, hbdef]
          simp only [Nat.cast_id]
          congr 1
          ext y
          simp only [Finset.mem_filter, Finset.mem_inter, mem_neighborFinset]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h2.symm, h1⟩
          · rintro ⟨h1, h2⟩; exact ⟨h2, h1.symm⟩
        have hSA := Finset.sum_le_sum hvA
        have hSB := Finset.sum_le_sum hvB
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcntA,
          Finset.sum_const, smul_eq_mul] at hSA
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcntB,
          Finset.sum_const, smul_eq_mul] at hSB
        have hAB10 : A.card + B.card = 10 := by
          have := Finset.card_le_card hABT
          omega
        have hprod : A.card * B.card ≤ 25 := by
          obtain ⟨s, hs⟩ : ∃ s, A.card = s := ⟨_, rfl⟩
          obtain ⟨t, ht⟩ : ∃ t, B.card = t := ⟨_, rfl⟩
          rw [hs, ht] at hAB10 ⊢
          have : s ≤ 10 := by omega
          interval_cases s <;> omega
        have hab : a + b ≤ a * b := by nlinarith
        have hSA' : ∑ y ∈ A, (G.neighborFinset y ∩ T).card + a * b ≤ A.card * B.card + a := by
          rw [Nat.mul_comm a b]; exact hSA
        have hSB' : ∑ y ∈ B, (G.neighborFinset y ∩ T).card + a * b ≤ A.card * B.card + b := by
          rw [Nat.mul_comm A.card B.card]; exact hSB
        generalize A.card * B.card = P at hSA' hSB' hprod
        generalize a * b = Q at hSA' hSB' hab
        omega

private lemma middle_transversal_pair {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    (u v : V) (hne : u ≠ v) (f : W → W → ℕ) :
    (∑ s : V → W, f (s u) (s v)) =
      Fintype.card W ^ (Fintype.card V - 2) * ∑ i : W, ∑ j : W, f i j := by
  classical
  let v' : {x : V // x ≠ u} := ⟨v, hne.symm⟩
  have card_compl {X : Type} [Fintype X] [DecidableEq X] (x : X) :
      Fintype.card {y : X // y ≠ x} = Fintype.card X - 1 := by
    rw [Fintype.card_subtype_compl (· = x)]
    simp
  calc
    _ = ∑ p : W × ({x : V // x ≠ u} → W), f p.1 (p.2 v') :=
      Fintype.sum_equiv (Equiv.funSplitAt u W) _ _ (fun _ => rfl)
    _ = ∑ i : W, ∑ s : {x : V // x ≠ u} → W, f i (s v') :=
      Fintype.sum_prod_type _
    _ = ∑ i : W, ∑ p : W × ({x : {y : V // y ≠ u} // x ≠ v'} → W), f i p.1 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Fintype.sum_equiv (Equiv.funSplitAt v' W) _ _ (fun _ => rfl)
    _ = _ := by
      simp_rw [Fintype.sum_prod_type, Finset.sum_const, smul_eq_mul, Finset.card_univ,
        Fintype.card_fun, card_compl, ← Nat.sub_add_eq, ← Finset.mul_sum]

private lemma middle_blowup_edge_sum (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (t : ℕ)
    (w : Sym2 (Fin 25 × Fin t) → ℕ) :
    (∑ s : Fin 25 → Fin t, ∑ e ∈ G.edgeFinset, w (e.map fun v => (v, s v))) =
      t ^ 23 * ∑ e ∈ (G.comap (Prod.fst : Fin 25 × Fin t → Fin 25)).edgeFinset, w e := by
  classical
  let H := G.comap (Prod.fst : Fin 25 × Fin t → Fin 25)
  have hproj : ∀ e ∈ H.edgeFinset, e.map Prod.fst ∈ G.edgeFinset := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simpa only [mem_edgeFinset, mem_edgeSet, Sym2.map_mk] using
        (show s(a, b) ∈ H.edgeFinset → G.Adj a.1 b.1 from
          fun he => mem_edgeFinset.1 he)
  have hfiber (e : Sym2 (Fin 25)) (he : e ∈ G.edgeFinset) :
      (∑ s : Fin 25 → Fin t, w (e.map fun v => (v, s v))) =
        t ^ 23 * ∑ d ∈ H.edgeFinset.filter (fun d => d.map Prod.fst = e), w d := by
    induction e using Sym2.ind with
    | h u v =>
      have huv : G.Adj u v := mem_edgeFinset.1 he
      simp only [Sym2.map_mk]
      rw [middle_transversal_pair u v huv.ne (fun i j => w s((u, i), (v, j)))]
      simp only [Fintype.card_fin]
      congr 1
      rw [← Fintype.sum_prod_type (fun p : Fin t × Fin t => w s((u, p.1), (v, p.2)))]
      refine Finset.sum_bij (fun p _ => s((u, p.1), (v, p.2))) ?_ ?_ ?_ ?_
      · intro p _
        exact Finset.mem_filter.2 ⟨mem_edgeFinset.2 (show H.Adj (u, p.1) (v, p.2) from huv), rfl⟩
      · intro p _ q _ hpq
        rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, _⟩
        · have hi : p.1 = q.1 := congrArg (fun x : Fin 25 × Fin t => x.2) h1
          have hj : p.2 = q.2 := congrArg (fun x : Fin 25 × Fin t => x.2) h2
          exact Prod.ext hi hj
        · exact (huv.ne (congrArg Prod.fst h1)).elim
      · intro d hd
        induction d using Sym2.ind with
        | h a b =>
          rcases Sym2.eq_iff.1 (Finset.mem_filter.1 hd).2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · refine ⟨(a.2, b.2), Finset.mem_univ _, ?_⟩
            exact Sym2.eq_iff.2 (Or.inl ⟨Prod.ext ha.symm rfl, Prod.ext hb.symm rfl⟩)
          · refine ⟨(b.2, a.2), Finset.mem_univ _, ?_⟩
            exact Sym2.eq_iff.2 (Or.inr ⟨Prod.ext hb.symm rfl, Prod.ext ha.symm rfl⟩)
      · intro p _
        rfl
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl hfiber, ← Finset.mul_sum]
  congr 1
  exact Finset.sum_fiberwise_of_maps_to hproj w

private lemma middle_blowup_edges (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (t : ℕ) (ht : 0 < t) :
    (G.comap (Prod.fst : Fin 25 × Fin t → Fin 25)).edgeFinset.card =
      t ^ 2 * G.edgeFinset.card := by
  classical
  have h := middle_blowup_edge_sum G t (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin] at h
  have hpow : t ^ 25 = t ^ 23 * t ^ 2 := pow_add t 23 2
  rw [hpow, mul_assoc] at h
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos ht 23) h).symm

open scoped Classical in
private lemma middle_blowup_round (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (t : ℕ) (ht : 0 < t) (T : Finset (Fin 25 × Fin t)) (k : ℕ)
    (hT : ((G.comap (Prod.fst : Fin 25 × Fin t → Fin 25)).edgeFinset.filter (Same T)).card
      < (k + 1) * t ^ 2) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ k := by
  classical
  let S (f : Fin 25 → Fin t) := (univ : Finset (Fin 25)).filter (fun v => (v, f v) ∈ T)
  have hpull (f : Fin 25 → Fin t) (e : Sym2 (Fin 25)) :
      Same (S f) e ↔ Same T (e.map fun v => (v, f v)) := by
    induction e using Sym2.ind with
    | h u v => simp [S, Sym2.map_mk, same_mk]
  have havg : (∑ f : Fin 25 → Fin t, (G.edgeFinset.filter (Same (S f))).card) =
      t ^ 23 * ((G.comap (Prod.fst : Fin 25 × Fin t → Fin 25)).edgeFinset.filter (Same T)).card := by
    simp_rw [Finset.card_filter, hpull]
    exact middle_blowup_edge_sum G t (fun e => if Same T e then 1 else 0)
  by_contra! h
  have hpoint (f : Fin 25 → Fin t) (_ : f ∈ (univ : Finset (Fin 25 → Fin t))) :
      k + 1 ≤ (G.edgeFinset.filter (Same (S f))).card := h (S f)
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, havg] at hsum
  have hpow : t ^ 25 = t ^ 23 * t ^ 2 := pow_add t 23 2
  rw [hpow, mul_assoc, mul_comm (t ^ 2) (k + 1)] at hsum
  exact (not_le_of_gt hT) (Nat.le_of_mul_le_mul_left hsum (pow_pos ht 23))

open scoped Classical in
/-- Transfer the asymptotic BCL density bounds to cuts on 25 vertices. -/
lemma middle_cut_of_bcl
    (hBCL : ∃ N : ℕ, ∀ t : ℕ, N ≤ 25 * t →
      ∀ (H : SimpleGraph (Fin 25 × Fin t)) [DecidableRel H.Adj], H.CliqueFree 3 →
        (10000 * H.edgeFinset.card ≤ 1243 * (25 * t) ^ 2 ∨
          3197 * (25 * t) ^ 2 < 20000 * H.edgeFinset.card) →
        ∃ T : Finset (Fin 25 × Fin t),
          1250 * (H.edgeFinset.filter (Same T)).card ≤ 51 * (25 * t) ^ 2)
    (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hm : G.edgeFinset.card ≤ 77 ∨ 100 ≤ G.edgeFinset.card) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  classical
  obtain ⟨N, hN⟩ := hBCL
  let t := N + 1
  have ht : 0 < t := Nat.succ_pos _
  let H := G.comap (Prod.fst : Fin 25 × Fin t → Fin 25)
  have hH : H.CliqueFree 3 := by
    intro C hC
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := is3Clique_iff.1 hC
    exact hG {a.1, b.1, c.1} (is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)
  have hedges : H.edgeFinset.card = t ^ 2 * G.edgeFinset.card :=
    middle_blowup_edges G t ht
  have hv : (25 * t) ^ 2 = 625 * t ^ 2 := by ring
  have hd : 10000 * H.edgeFinset.card ≤ 1243 * (25 * t) ^ 2 ∨
      3197 * (25 * t) ^ 2 < 20000 * H.edgeFinset.card := by
    rw [hedges, hv]
    rcases hm with hlo | hhi
    · left
      calc
        _ = t ^ 2 * (10000 * G.edgeFinset.card) := by ring
        _ ≤ t ^ 2 * (1243 * 625) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    · right
      calc
        _ = t ^ 2 * (3197 * 625) := by ring
        _ < t ^ 2 * (20000 * G.edgeFinset.card) :=
          Nat.mul_lt_mul_of_pos_left (by omega) (pow_pos ht 2)
        _ = _ := by ring
  obtain ⟨T, hT⟩ := hN t (show N ≤ 25 * t by dsimp [t]; omega) H hH hd
  apply middle_blowup_round G t ht T 25
  change (H.edgeFinset.filter (Same T)).card < 26 * t ^ 2
  have hpos : 0 < t ^ 2 := pow_pos ht _
  rw [mul_pow] at hT
  norm_num at hT
  omega

-- Generic cover bound for the degree-13 sub-case: if every edge with an endpoint outside R has
-- an endpoint in N, then the same-side edges of S are those inside R plus, for each u in N,
-- the neighbours of u lying on the side of u.
open scoped Classical in
lemma middle_cover_count (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (N R S : Finset (Fin 25))
    (hcov : ∀ x y, G.Adj x y → x ∉ R → x ∈ N ∨ y ∈ N) :
    (G.edgeFinset.filter (Same S)).card ≤
      (G.edgeFinset.filter (fun e => (∀ w ∈ e, w ∈ R) ∧ Same S e)).card +
      ∑ u ∈ N, ((G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S))).card := by
  have hsub : G.edgeFinset.filter (Same S) ⊆
      G.edgeFinset.filter (fun e => (∀ w ∈ e, w ∈ R) ∧ Same S e) ∪
      N.biUnion (fun u => ((G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S))).image
        (fun x => s(u, x))) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨he1, he2⟩ := he
    induction e using Sym2.ind with
    | h x y =>
      have hadj : G.Adj x y := by
        rw [mem_edgeFinset, mem_edgeSet] at he1
        exact he1
      have hs : x ∈ S ↔ y ∈ S := (same_mk S x y).1 he2
      rw [Finset.mem_union]
      by_cases hx : x ∈ R
      · by_cases hy : y ∈ R
        · left
          rw [Finset.mem_filter]
          refine ⟨he1, ?_, he2⟩
          intro w hw
          rw [Sym2.mem_iff] at hw
          rcases hw with rfl | rfl
          · exact hx
          · exact hy
        · right
          rw [Finset.mem_biUnion]
          rcases hcov y x hadj.symm hy with h | h
          · exact ⟨y, h, Finset.mem_image.2 ⟨x, Finset.mem_filter.2
              ⟨(mem_neighborFinset _ _ _).2 hadj.symm, hs.symm⟩, Sym2.eq_swap⟩⟩
          · exact ⟨x, h, Finset.mem_image.2 ⟨y, Finset.mem_filter.2
              ⟨(mem_neighborFinset _ _ _).2 hadj, hs⟩, rfl⟩⟩
      · right
        rw [Finset.mem_biUnion]
        rcases hcov x y hadj hx with h | h
        · exact ⟨x, h, Finset.mem_image.2 ⟨y, Finset.mem_filter.2
            ⟨(mem_neighborFinset _ _ _).2 hadj, hs⟩, rfl⟩⟩
        · exact ⟨y, h, Finset.mem_image.2 ⟨x, Finset.mem_filter.2
            ⟨(mem_neighborFinset _ _ _).2 hadj.symm, hs.symm⟩, Sym2.eq_swap⟩⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  refine Nat.add_le_add_left ?_ _
  exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun u _ => Finset.card_image_le)

-- Degree-13 sub-case, per-vertex cost: for a neighbour u of v and a cut S that agrees with X
-- outside the closed neighbourhood of v, the neighbours of u on the side of u are counted by
-- the trace of N(u) on X (resp. on the rest), plus possibly v itself.
open scoped Classical in
lemma middle_deg13_side (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (v u : Fin 25) (hvu : G.Adj v u) (X S : Finset (Fin 25))
    (hS : ∀ x, x ∈ (insert v (G.neighborFinset v))ᶜ → (x ∈ S ↔ x ∈ X)) :
    (u ∈ S → ((G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S))).card ≤
        (G.neighborFinset u ∩ X).card + (if v ∈ S then 1 else 0)) ∧
    (u ∉ S → ((G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S))).card ≤
        (G.neighborFinset u ∩ ((insert v (G.neighborFinset v))ᶜ \ X)).card +
          (if v ∈ S then 0 else 1)) := by
  have hR : ∀ x, G.Adj u x → x = v ∨ x ∈ (insert v (G.neighborFinset v))ᶜ := by
    intro x hux
    by_cases hxv : x = v
    · exact Or.inl hxv
    · right
      rw [Finset.mem_compl, Finset.mem_insert, mem_neighborFinset]
      rintro (h | h)
      · exact hxv h
      · exact hG {v, u, x} (is3Clique_triple_iff.2 ⟨hvu, h, hux⟩)
  constructor
  · intro huS
    by_cases hvS : v ∈ S
    · rw [if_pos hvS]
      have hsub : (G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S)) ⊆
          insert v (G.neighborFinset u ∩ X) := by
        intro x hx
        rw [Finset.mem_filter, mem_neighborFinset] at hx
        rw [Finset.mem_insert]
        rcases hR x hx.1 with h | h
        · exact Or.inl h
        · right
          exact Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hx.1, (hS x h).1 (hx.2.1 huS)⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    · rw [if_neg hvS]
      have hsub : (G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S)) ⊆
          G.neighborFinset u ∩ X := by
        intro x hx
        rw [Finset.mem_filter, mem_neighborFinset] at hx
        rcases hR x hx.1 with h | h
        · exact (hvS (by rw [← h]; exact hx.2.1 huS)).elim
        · exact Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hx.1, (hS x h).1 (hx.2.1 huS)⟩
      exact Finset.card_le_card hsub
  · intro huS
    by_cases hvS : v ∈ S
    · rw [if_pos hvS]
      have hsub : (G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S)) ⊆
          G.neighborFinset u ∩ ((insert v (G.neighborFinset v))ᶜ \ X) := by
        intro x hx
        rw [Finset.mem_filter, mem_neighborFinset] at hx
        have hxS : x ∉ S := fun h => huS (hx.2.2 h)
        rcases hR x hx.1 with h | h
        · exact (hxS (by rw [h]; exact hvS)).elim
        · exact Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hx.1,
            Finset.mem_sdiff.2 ⟨h, fun hX => hxS ((hS x h).2 hX)⟩⟩
      exact Finset.card_le_card hsub
    · rw [if_neg hvS]
      have hsub : (G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S)) ⊆
          insert v (G.neighborFinset u ∩ ((insert v (G.neighborFinset v))ᶜ \ X)) := by
        intro x hx
        rw [Finset.mem_filter, mem_neighborFinset] at hx
        have hxS : x ∉ S := fun h => huS (hx.2.2 h)
        rw [Finset.mem_insert]
        rcases hR x hx.1 with h | h
        · exact Or.inl h
        · right
          exact Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hx.1,
            Finset.mem_sdiff.2 ⟨h, fun hX => hxS ((hS x h).2 hX)⟩⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

-- Degree-13 sub-case: an 11-vertex set R spanning at least 26 edges, cut by X with at most one
-- edge of R on the same side, has at most 5 non-adjacent pairs between X and the rest of R.
open scoped Classical in
lemma middle_deg13_missing (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (R X : Finset (Fin 25)) (hXR : X ⊆ R) (hR : R.card = 11)
    (heR : 26 ≤ (G.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ R)).card)
    (ht : (G.edgeFinset.filter (fun e => (∀ w ∈ e, w ∈ R) ∧ Same X e)).card ≤ 1) :
    ((X ×ˢ (R \ X)).filter (fun p => ¬ G.Adj p.1 p.2)).card ≤ 5 := by
  have hsub : G.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ R) ⊆
      G.edgeFinset.filter (fun e => (∀ w ∈ e, w ∈ R) ∧ Same X e) ∪
      ((X ×ˢ (R \ X)).filter (fun p => G.Adj p.1 p.2)).image (fun p => s(p.1, p.2)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨he1, he2⟩ := he
    induction e using Sym2.ind with
    | h x y =>
      have hadj : G.Adj x y := by
        rw [mem_edgeFinset, mem_edgeSet] at he1
        exact he1
      have hx : x ∈ R := he2 x (Sym2.mem_mk_left x y)
      have hy : y ∈ R := he2 y (Sym2.mem_mk_right x y)
      rw [Finset.mem_union]
      by_cases hs : (x ∈ X ↔ y ∈ X)
      · left
        exact Finset.mem_filter.2 ⟨he1, he2, (same_mk X x y).2 hs⟩
      · right
        rw [Finset.mem_image]
        by_cases hxX : x ∈ X
        · have hyX : y ∉ X := fun h => hs ⟨fun _ => h, fun _ => hxX⟩
          exact ⟨(x, y), Finset.mem_filter.2 ⟨Finset.mem_product.2
            ⟨hxX, Finset.mem_sdiff.2 ⟨hy, hyX⟩⟩, hadj⟩, rfl⟩
        · have hyX : y ∈ X := by
            by_contra h
            exact hs ⟨fun h' => (hxX h').elim, fun h' => (h h').elim⟩
          exact ⟨(y, x), Finset.mem_filter.2 ⟨Finset.mem_product.2
            ⟨hyX, Finset.mem_sdiff.2 ⟨hx, hxX⟩⟩, hadj.symm⟩, Sym2.eq_swap⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 : (((X ×ˢ (R \ X)).filter (fun p => G.Adj p.1 p.2)).image
      (fun p => s(p.1, p.2))).card ≤ ((X ×ˢ (R \ X)).filter (fun p => G.Adj p.1 p.2)).card :=
    Finset.card_image_le
  have h3 := Finset.card_filter_add_card_filter_not (s := X ×ˢ (R \ X))
    (fun p => G.Adj p.1 p.2)
  rw [Finset.card_product] at h3
  have h4 := Finset.card_sdiff_add_card_eq_card hXR
  have h6 : ∀ a b : ℕ, b + a = 11 → a * b ≤ 30 := by
    intro a b hab
    have ha : a ≤ 11 := by omega
    have hb : b = 11 - a := by omega
    subst hb
    interval_cases a <;> norm_num
  have h7 := h6 X.card (R \ X).card (by omega)
  have h8 : ((X ×ˢ (R \ X)).filter (fun p => G.Adj p.1 p.2)).card +
      ((X ×ˢ (R \ X)).filter (fun p => ¬ G.Adj p.1 p.2)).card ≤ 30 := by
    rw [h3]
    exact h7
  omega

-- Degree-13 sub-case: inside R the cut S and the cut X see the same edges.
open scoped Classical in
lemma middle_deg13_inside (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (R X S : Finset (Fin 25)) (hS : ∀ x, x ∈ R → (x ∈ S ↔ x ∈ X)) :
    (G.edgeFinset.filter (fun e => (∀ w ∈ e, w ∈ R) ∧ Same S e)).card ≤
      (G.edgeFinset.filter (fun e => (∀ w ∈ e, w ∈ R) ∧ Same X e)).card := by
  refine Finset.card_le_card ?_
  intro e he
  rw [Finset.mem_filter] at he ⊢
  obtain ⟨he1, he2, he3⟩ := he
  refine ⟨he1, he2, ?_⟩
  induction e using Sym2.ind with
  | h x y =>
    have hx : x ∈ R := he2 x (Sym2.mem_mk_left x y)
    have hy : y ∈ R := he2 y (Sym2.mem_mk_right x y)
    rw [same_mk] at he3 ⊢
    exact ⟨fun h => (hS y hy).1 (he3.1 ((hS x hx).2 h)),
      fun h => (hS x hx).1 (he3.2 ((hS y hy).2 h))⟩

-- Degree-13 sub-case, arithmetic of the two side choices for one neighbour of v.
lemma middle_deg13_arith (a b cA cB : ℕ) (hab : a * b ≤ 5)
    (hA : cA ≤ if a ≤ b then a else b + 1) (hB : cB ≤ if a < b then a + 1 else b) :
    cA + cB ≤ 3 + (if a = 2 ∧ b = 2 then 1 else 0) := by
  have hmin : a ≤ 1 ∨ b ≤ 1 ∨ (a = 2 ∧ b = 2) := by
    by_cases h1 : a ≤ 1
    · exact Or.inl h1
    · by_cases h2 : b ≤ 1
      · exact Or.inr (Or.inl h2)
      · right; right
        have h4 : 2 ≤ a := by omega
        have h5 : 2 ≤ b := by omega
        have h6 : 2 * b ≤ a * b := Nat.mul_le_mul_right b h4
        have h7 : a * 2 ≤ a * b := Nat.mul_le_mul_left a h5
        constructor <;> omega
  split_ifs at hA hB ⊢ <;> omega

lemma middle_two_two (p q U : ℕ) (hp : p ≤ 2) (hq : q ≤ 2) (hU : U ≤ 5) (h : U + p * q = 8) :
    p = 2 ∧ q = 2 := by
  interval_cases p <;> interval_cases q <;> omega

-- Degree-13 sub-case: at most 10 vertices outside R can have exactly two neighbours on each
-- side of the cut X of R (they would all share one 2x2 block of missing pairs).
open scoped Classical in
lemma middle_deg13_few22 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hdeg : ∀ x, G.degree x ≤ 13) (K R X : Finset (Fin 25)) (hXR : X ⊆ R) (hR : R.card = 11)
    (hKR : ∀ u ∈ K, u ∉ R)
    (hK : ∀ u ∈ K, (G.neighborFinset u ∩ X).card = 2 ∧ (G.neighborFinset u ∩ (R \ X)).card = 2)
    (hM : ((X ×ˢ (R \ X)).filter (fun p => ¬ G.Adj p.1 p.2)).card ≤ 5) :
    K.card ≤ 10 := by
  by_contra hcon
  have hK11 : 11 ≤ K.card := by omega
  have hprod : ∀ u, (G.neighborFinset u ∩ X) ×ˢ (G.neighborFinset u ∩ (R \ X)) ⊆
      (X ×ˢ (R \ X)).filter (fun p => ¬ G.Adj p.1 p.2) := by
    intro u p hp
    rw [Finset.mem_product, Finset.mem_inter, Finset.mem_inter, mem_neighborFinset,
      mem_neighborFinset] at hp
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hp.1.2, hp.2.2⟩, fun hadj =>
      hG {u, p.1, p.2} (is3Clique_triple_iff.2 ⟨hp.1.1, hp.2.1, hadj⟩)⟩
  obtain ⟨u0, hu0⟩ : K.Nonempty := Finset.card_pos.1 (by omega)
  have hu0' := hK u0 hu0
  have hsame : ∀ u ∈ K, G.neighborFinset u ∩ X = G.neighborFinset u0 ∩ X ∧
      G.neighborFinset u ∩ (R \ X) = G.neighborFinset u0 ∩ (R \ X) := by
    intro u hu
    have hu' := hK u hu
    have h1 := (Finset.card_le_card (Finset.union_subset (hprod u) (hprod u0))).trans hM
    have h2 := Finset.card_union_add_card_inter
      ((G.neighborFinset u ∩ X) ×ˢ (G.neighborFinset u ∩ (R \ X)))
      ((G.neighborFinset u0 ∩ X) ×ˢ (G.neighborFinset u0 ∩ (R \ X)))
    rw [Finset.product_inter_product, Finset.card_product, Finset.card_product,
      Finset.card_product, hu'.1, hu'.2, hu0'.1, hu0'.2] at h2
    have h3 : ((G.neighborFinset u ∩ X) ∩ (G.neighborFinset u0 ∩ X)).card ≤ 2 := by
      rw [← hu'.1]
      exact Finset.card_le_card Finset.inter_subset_left
    have h4 : ((G.neighborFinset u ∩ (R \ X)) ∩ (G.neighborFinset u0 ∩ (R \ X))).card ≤ 2 := by
      rw [← hu'.2]
      exact Finset.card_le_card Finset.inter_subset_left
    have h5 := middle_two_two _ _ _ h3 h4 h1 (by omega)
    constructor
    · have e1 : (G.neighborFinset u ∩ X) ∩ (G.neighborFinset u0 ∩ X) = G.neighborFinset u ∩ X :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h5.1, hu'.1])
      have e2 : (G.neighborFinset u ∩ X) ∩ (G.neighborFinset u0 ∩ X) = G.neighborFinset u0 ∩ X :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h5.1, hu0'.1])
      exact e1.symm.trans e2
    · have e1 : (G.neighborFinset u ∩ (R \ X)) ∩ (G.neighborFinset u0 ∩ (R \ X)) =
          G.neighborFinset u ∩ (R \ X) :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h5.2, hu'.2])
      have e2 : (G.neighborFinset u ∩ (R \ X)) ∩ (G.neighborFinset u0 ∩ (R \ X)) =
          G.neighborFinset u0 ∩ (R \ X) :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h5.2, hu0'.2])
      exact e1.symm.trans e2
  obtain ⟨x1, hx1⟩ : (G.neighborFinset u0 ∩ X).Nonempty :=
    Finset.card_pos.1 (by rw [hu0'.1]; norm_num)
  obtain ⟨y1, hy1⟩ : (G.neighborFinset u0 ∩ (R \ X)).Nonempty :=
    Finset.card_pos.1 (by rw [hu0'.2]; norm_num)
  have hx1X : x1 ∈ X := (Finset.mem_inter.1 hx1).2
  have hy1Y : y1 ∈ R \ X := (Finset.mem_inter.1 hy1).2
  have hKx : ∀ u ∈ K, G.Adj x1 u := by
    intro u hu
    have h : x1 ∈ G.neighborFinset u ∩ X := by
      rw [(hsame u hu).1]
      exact hx1
    exact ((mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 h).1).symm
  have hKy : ∀ u ∈ K, G.Adj y1 u := by
    intro u hu
    have h : y1 ∈ G.neighborFinset u ∩ (R \ X) := by
      rw [(hsame u hu).2]
      exact hy1
    exact ((mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 h).1).symm
  have hdx : K.card + (G.neighborFinset x1 ∩ (R \ X)).card ≤ 13 := by
    have hsub : K ∪ (G.neighborFinset x1 ∩ (R \ X)) ⊆ G.neighborFinset x1 := by
      intro z hz
      rcases Finset.mem_union.1 hz with h | h
      · exact (mem_neighborFinset _ _ _).2 (hKx z h)
      · exact (Finset.mem_inter.1 h).1
    have hdj : Disjoint K (G.neighborFinset x1 ∩ (R \ X)) := by
      rw [Finset.disjoint_left]
      intro z hzK hz
      exact hKR z hzK (Finset.mem_sdiff.1 (Finset.mem_inter.1 hz).2).1
    have h := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdj, card_neighborFinset_eq_degree] at h
    exact h.trans (hdeg x1)
  have hdy : K.card + (G.neighborFinset y1 ∩ X).card ≤ 13 := by
    have hsub : K ∪ (G.neighborFinset y1 ∩ X) ⊆ G.neighborFinset y1 := by
      intro z hz
      rcases Finset.mem_union.1 hz with h | h
      · exact (mem_neighborFinset _ _ _).2 (hKy z h)
      · exact (Finset.mem_inter.1 h).1
    have hdj : Disjoint K (G.neighborFinset y1 ∩ X) := by
      rw [Finset.disjoint_left]
      intro z hzK hz
      exact hKR z hzK (hXR (Finset.mem_inter.1 hz).2)
    have h := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdj, card_neighborFinset_eq_degree] at h
    exact h.trans (hdeg y1)
  have hY1 : (R \ X).card ≤ ((R \ X) \ G.neighborFinset x1).card +
      (G.neighborFinset x1 ∩ (R \ X)).card := by
    have hsub : R \ X ⊆ ((R \ X) \ G.neighborFinset x1) ∪ (G.neighborFinset x1 ∩ (R \ X)) := by
      intro z hz
      by_cases h : z ∈ G.neighborFinset x1
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h, hz⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hz, h⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hX1 : X.card ≤ (X \ insert x1 (G.neighborFinset y1)).card +
      ((G.neighborFinset y1 ∩ X).card + 1) := by
    have hsub : X ⊆ (X \ insert x1 (G.neighborFinset y1)) ∪
        insert x1 (G.neighborFinset y1 ∩ X) := by
      intro z hz
      by_cases h : z ∈ insert x1 (G.neighborFinset y1)
      · refine Finset.mem_union_right _ ?_
        rcases Finset.mem_insert.1 h with h | h
        · exact Finset.mem_insert.2 (Or.inl h)
        · exact Finset.mem_insert.2 (Or.inr (Finset.mem_inter.2 ⟨h, hz⟩))
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hz, h⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_insert_le _ _) _))
  have hsubM : (((R \ X) \ G.neighborFinset x1).image (fun y => (x1, y))) ∪
      ((X \ insert x1 (G.neighborFinset y1)).image (fun x => (x, y1))) ⊆
      (X ×ˢ (R \ X)).filter (fun p => ¬ G.Adj p.1 p.2) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product]
    rcases Finset.mem_union.1 hp with h | h
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      rw [Finset.mem_sdiff, mem_neighborFinset] at hy
      exact ⟨⟨hx1X, hy.1⟩, hy.2⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      rw [Finset.mem_sdiff, Finset.mem_insert, mem_neighborFinset] at hx
      exact ⟨⟨hx.1, hy1Y⟩, fun hadj => hx.2 (Or.inr hadj.symm)⟩
  have hdjM : Disjoint (((R \ X) \ G.neighborFinset x1).image (fun y => (x1, y)))
      ((X \ insert x1 (G.neighborFinset y1)).image (fun x => (x, y1))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hp1
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 hp2
    rw [Finset.mem_sdiff, Finset.mem_insert] at hx
    have hxx : x = x1 := congrArg Prod.fst hxe
    exact hx.2 (Or.inl hxx)
  have hinj1 : Function.Injective (fun y : Fin 25 => (x1, y)) :=
    fun a b h => congrArg Prod.snd h
  have hinj2 : Function.Injective (fun x : Fin 25 => (x, y1)) :=
    fun a b h => congrArg Prod.fst h
  have hcardM := Finset.card_le_card hsubM
  rw [Finset.card_union_of_disjoint hdjM, Finset.card_image_of_injective _ hinj1,
    Finset.card_image_of_injective _ hinj2] at hcardM
  have hXY := Finset.card_sdiff_add_card_eq_card hXR
  omega

-- Degree-13 sub-case, complete: a vertex of degree 13 whose neighbourhood cut fails still
-- yields a cut with at most 25 same-side edges (maximum degree at most 13).
open scoped Classical in
lemma middle_deg13_case (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hdeg : ∀ x, G.degree x ≤ 13) (v : Fin 25) (hv : G.degree v = 13)
    (hnbv : 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  obtain ⟨hRc, heR⟩ := middle_deg13_outside G hG v hv hnbv
  have hvR : v ∉ (insert v (G.neighborFinset v))ᶜ := by simp
  have hNR : ∀ u ∈ G.neighborFinset v, u ∉ (insert v (G.neighborFinset v))ᶜ := by
    intro u hu
    simp [hu]
  have hcov : ∀ x y, G.Adj x y → x ∉ (insert v (G.neighborFinset v))ᶜ →
      x ∈ G.neighborFinset v ∨ y ∈ G.neighborFinset v := by
    intro x y hxy hx
    rw [Finset.mem_compl, not_not, Finset.mem_insert] at hx
    rcases hx with hx | hx
    · rw [hx] at hxy
      exact Or.inr ((mem_neighborFinset _ _ _).2 hxy)
    · exact Or.inl hx
  have hside : ∀ (u : Fin 25), G.Adj v u → ∀ (X S : Finset (Fin 25)),
      (∀ x, x ∈ (insert v (G.neighborFinset v))ᶜ → (x ∈ S ↔ x ∈ X)) →
      (u ∈ S → ((G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S))).card ≤
        (G.neighborFinset u ∩ X).card + (if v ∈ S then 1 else 0)) ∧
      (u ∉ S → ((G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S))).card ≤
        (G.neighborFinset u ∩ ((insert v (G.neighborFinset v))ᶜ \ X)).card +
          (if v ∈ S then 0 else 1)) :=
    fun u hvu X S hS => middle_deg13_side G hG v u hvu X S hS
  generalize (insert v (G.neighborFinset v))ᶜ = R at hRc heR hvR hNR hcov hside
  obtain ⟨X, hXR, ht⟩ := middle_bip_in G hG R hRc heR
  have hM := middle_deg13_missing G R X hXR hRc heR ht
  have hvX : v ∉ X := fun h => hvR (hXR h)
  have hNX : ∀ u ∈ G.neighborFinset v, u ∉ X := fun u hu h => hNR u hu (hXR h)
  have hvN : v ∉ G.neighborFinset v := by simp
  have hab : ∀ u, (G.neighborFinset u ∩ X).card * (G.neighborFinset u ∩ (R \ X)).card ≤ 5 := by
    intro u
    have hsub : (G.neighborFinset u ∩ X) ×ˢ (G.neighborFinset u ∩ (R \ X)) ⊆
        (X ×ˢ (R \ X)).filter (fun p => ¬ G.Adj p.1 p.2) := by
      intro p hp
      rw [Finset.mem_product, Finset.mem_inter, Finset.mem_inter, mem_neighborFinset,
        mem_neighborFinset] at hp
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp.1.2, hp.2.2⟩, fun hadj =>
        hG {u, p.1, p.2} (is3Clique_triple_iff.2 ⟨hp.1.1, hp.2.1, hadj⟩)⟩
    have h := Finset.card_le_card hsub
    rw [Finset.card_product] at h
    exact h.trans hM
  have key : ∀ S : Finset (Fin 25), (∀ x, x ∈ R → (x ∈ S ↔ x ∈ X)) →
      (G.edgeFinset.filter (Same S)).card ≤ 1 + ∑ u ∈ G.neighborFinset v,
        ((G.neighborFinset u).filter (fun x => (u ∈ S ↔ x ∈ S))).card := by
    intro S hS
    have h1 := middle_cover_count G (G.neighborFinset v) R S hcov
    have h2 := middle_deg13_inside G R X S hS
    omega
  obtain ⟨SA, hSAdef⟩ : ∃ SA : Finset (Fin 25), SA = X ∪ (G.neighborFinset v).filter
      (fun u => (G.neighborFinset u ∩ X).card ≤ (G.neighborFinset u ∩ (R \ X)).card) := ⟨_, rfl⟩
  obtain ⟨SB, hSBdef⟩ : ∃ SB : Finset (Fin 25), SB = insert v (X ∪ (G.neighborFinset v).filter
      (fun u => (G.neighborFinset u ∩ X).card < (G.neighborFinset u ∩ (R \ X)).card)) :=
    ⟨_, rfl⟩
  have hSA : ∀ x, x ∈ R → (x ∈ SA ↔ x ∈ X) := by
    intro x hx
    rw [hSAdef, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact h
      · exact (hNR x h hx).elim
    · exact fun h => Or.inl h
  have hSB : ∀ x, x ∈ R → (x ∈ SB ↔ x ∈ X) := by
    intro x hx
    rw [hSBdef, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h | ⟨h, _⟩)
      · exact (hvR (by rw [h] at hx; exact hx)).elim
      · exact h
      · exact (hNR x h hx).elim
    · exact fun h => Or.inr (Or.inl h)
  have hvSA : v ∉ SA := by
    rw [hSAdef, Finset.mem_union, Finset.mem_filter]
    rintro (h | ⟨h, _⟩)
    · exact hvX h
    · exact hvN h
  have hvSB : v ∈ SB := by
    rw [hSBdef]
    exact Finset.mem_insert_self _ _
  have huSA : ∀ u ∈ G.neighborFinset v, (u ∈ SA ↔
      (G.neighborFinset u ∩ X).card ≤ (G.neighborFinset u ∩ (R \ X)).card) := by
    intro u hu
    rw [hSAdef, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact (hNX u hu h).elim
      · exact h
    · exact fun h => Or.inr ⟨hu, h⟩
  have huSB : ∀ u ∈ G.neighborFinset v, (u ∈ SB ↔
      (G.neighborFinset u ∩ X).card < (G.neighborFinset u ∩ (R \ X)).card) := by
    intro u hu
    rw [hSBdef, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h | ⟨_, h⟩)
      · exact (hvN (by rw [h] at hu; exact hu)).elim
      · exact (hNX u hu h).elim
      · exact h
    · exact fun h => Or.inr (Or.inr ⟨hu, h⟩)
  have hper : ∀ u ∈ G.neighborFinset v,
      ((G.neighborFinset u).filter (fun x => (u ∈ SA ↔ x ∈ SA))).card +
      ((G.neighborFinset u).filter (fun x => (u ∈ SB ↔ x ∈ SB))).card ≤
      3 + (if (G.neighborFinset u ∩ X).card = 2 ∧ (G.neighborFinset u ∩ (R \ X)).card = 2
        then 1 else 0) := by
    intro u hu
    have hvu : G.Adj v u := (mem_neighborFinset _ _ _).1 hu
    obtain ⟨hA1, hA2⟩ := hside u hvu X SA hSA
    obtain ⟨hB1, hB2⟩ := hside u hvu X SB hSB
    rw [if_neg hvSA] at hA1 hA2
    rw [if_pos hvSB] at hB1 hB2
    refine middle_deg13_arith _ _ _ _ (hab u) ?_ ?_
    · by_cases h : (G.neighborFinset u ∩ X).card ≤ (G.neighborFinset u ∩ (R \ X)).card
      · rw [if_pos h]
        exact hA1 ((huSA u hu).2 h)
      · rw [if_neg h]
        exact hA2 (fun hc => h ((huSA u hu).1 hc))
    · by_cases h : (G.neighborFinset u ∩ X).card < (G.neighborFinset u ∩ (R \ X)).card
      · rw [if_pos h]
        exact hB1 ((huSB u hu).2 h)
      · rw [if_neg h]
        exact hB2 (fun hc => h ((huSB u hu).1 hc))
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    card_neighborFinset_eq_degree, hv, ← Finset.card_filter] at hsum
  have hK := middle_deg13_few22 G hG hdeg
    ((G.neighborFinset v).filter (fun u => (G.neighborFinset u ∩ X).card = 2 ∧
      (G.neighborFinset u ∩ (R \ X)).card = 2)) R X hXR hRc
    (fun u hu => hNR u (Finset.mem_filter.1 hu).1)
    (fun u hu => (Finset.mem_filter.1 hu).2) hM
  have hA := key SA hSA
  have hB := key SB hSB
  by_cases h : (G.edgeFinset.filter (Same SA)).card ≤ 25
  · exact ⟨SA, h⟩
  · exact ⟨SB, by omega⟩

-- The only remaining open core: 64 to 116 edges and maximum degree at most 12
-- (61, 62, 63 and 117 to 123 edges are proved above; a vertex of degree 13 is handled by
-- middle_deg13_case).
open scoped Classical in
lemma middle_core_64_116_deg12 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3)
    (hmax : ∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G)
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    (h1 : 64 ≤ G.edgeFinset.card) (h2 : G.edgeFinset.card ≤ 116)
    (hdeg : ∀ v, G.degree v ≤ 12)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hed : ∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  sorry

-- 64 to 116 edges: a vertex of degree 13 is settled by middle_deg13_case, the rest is the
-- open core above.
open scoped Classical in
lemma middle_core_64_116 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hmax : ∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G)
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    (h1 : 64 ≤ G.edgeFinset.card) (h2 : G.edgeFinset.card ≤ 116)
    (hdeg : ∀ v, G.degree v ≤ 13)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hed : ∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  by_cases h13 : ∃ v, G.degree v = 13
  · obtain ⟨v, hv⟩ := h13
    exact middle_deg13_case G hG hdeg v hv (hnb v)
  · refine middle_core_64_116_deg12 G hG hmax hdiam h1 h2 (fun v => ?_) hnb hed
    have h := hdeg v
    by_contra hc
    exact h13 ⟨v, by omega⟩

open scoped Classical in
lemma middle_case (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hmax : ∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G)
    (hdiam : ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z)
    (h1 : 61 ≤ G.edgeFinset.card) (h2 : G.edgeFinset.card ≤ 123)
    (hdeg : ∀ v, G.degree v ≤ 13)
    (hnb : ∀ v, 25 < (G.edgeFinset.filter (Same (G.neighborFinset v))).card)
    (hed : ∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  by_cases hm : 121 ≤ G.edgeFinset.card
  · exact (middle_upper_edges G hG hdeg hnb hm h2).elim
  · by_cases hm120 : G.edgeFinset.card = 120
    · exact (middle_edges_120 G hG hdeg hnb hm120).elim
    · by_cases hm119 : G.edgeFinset.card = 119
      · exact (middle_edges_119 G hG hdeg hnb hm119).elim
      · by_cases hm61 : G.edgeFinset.card = 61
        · exact middle_edges_61 G hG hdiam hm61
        · by_cases hm118 : G.edgeFinset.card = 118
          · exact middle_edges_118 G hG hdeg hnb hm118
          · by_cases hm62 : G.edgeFinset.card = 62
            · exact middle_edges_62 G hG hdiam hdeg hed hm62
            · by_cases hm63 : G.edgeFinset.card = 63
              · exact middle_edges_63 G hG hdiam hdeg hed hm63
              · by_cases h117low : G.edgeFinset.card = 117 ∧ ∀ v, G.degree v ≤ 10
                · exact middle_edges_117_low_degree G hG h117low.2 hnb h117low.1
                · have h117 : G.edgeFinset.card = 117 → ∀ v, G.degree v ≤ 11 :=
                    middle_degree_cap_117 G hG hdeg hnb
                  by_cases hm117 : G.edgeFinset.card = 117
                  · have hD11 := h117 hm117
                    have hex : ∃ v, G.degree v = 11 := by
                      by_contra hne
                      push Not at hne
                      exact h117low ⟨hm117, fun v => by
                        have := hD11 v
                        have := hne v
                        omega⟩
                    exact middle_edges_117_high_degree G hG hD11 hex hnb hm117
                  · exact middle_core_64_116 G hG hmax hdiam (by omega) (by omega) hdeg hnb hed

open scoped Classical in
lemma main_cut_max (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hmax : ∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  by_cases hd : ∃ v, 14 ≤ G.degree v
  · obtain ⟨v, hv⟩ := hd
    exact highdeg_case G hG v hv
  push Not at hd
  by_cases h1 : G.edgeFinset.card ≤ 51
  · obtain ⟨S, hS⟩ := exists_half_cut G
    exact ⟨S, by omega⟩
  by_cases h3 : G.edgeFinset.card ≤ 60
  · exact sparse_ext G hG (by omega) h3
  by_cases h2 : 124 ≤ G.edgeFinset.card
  · exact dense_case G hG h2
  · by_cases hN : ∃ v, (G.edgeFinset.filter (Same (G.neighborFinset v))).card ≤ 25
    · obtain ⟨v, hv⟩ := hN
      exact ⟨_, hv⟩
    push Not at hN
    by_cases hE : ∃ u v, G.Adj u v ∧ G.edgeFinset.card ≤ (G.edgeFinset.filter
        (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
    · obtain ⟨u, v, huv, hle⟩ := hE
      obtain ⟨S, hS⟩ := exists_edge_cut_full G hG huv
      refine ⟨S, ?_⟩
      have hS' : 2 * (G.edgeFinset.filter (Same S)).card
          + (G.edgeFinset.filter
            (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card
          ≤ G.edgeFinset.card := by convert hS
      omega
    push Not at hE
    exact middle_case G hG hmax (common_nbr_of_max G hG hmax) (by omega) (by omega)
      (fun v => by have := hd v; omega) hN hE

open scoped Classical in
lemma main_cut (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  obtain ⟨G', hle, hG', hmax⟩ := exists_maximal_tf G hG
  obtain ⟨S, hS⟩ := main_cut_max G' hG' hmax
  exact ⟨S, le_trans (filter_mono_graph hle S) hS⟩

/-!
The route cited in the literature (added in the second attempt).  Deleting a vertex `v` costs at
most half of its degree (`del_vertex`), a graph on 25 vertices with two isolated vertices is a
graph on 23 vertices (`transfer`), and a graph with at most 99 edges has a vertex of degree at
most 7.  So the case of at most 99 edges with a vertex of degree at most 5 follows from two
statements about triangle-free graphs on 23 vertices (`two_del`), and the whole theorem follows
from those two statements, the sparse core (at most 99 edges, all degrees at least 6) and the
dense range 100 to 123 edges (`main_cut_of_literature`).  These inputs are the computer-assisted
results of Balogh-Clemen-Lidicky and McKay; they are hypotheses below, not proved here.
-/

section
variable {V : Type} [Fintype V] [DecidableEq V]

open scoped Classical in
/-- Vertex deletion: a cut of `G` minus the edges at `v` extends to a cut of `G` that leaves at
most half of the edges at `v` uncut. -/
lemma del_vertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) :
    ∃ S' : Finset V, 2 * (G.edgeFinset.filter (Same S')).card
      ≤ 2 * ((G.deleteIncidenceSet v).edgeFinset.filter (Same S)).card + G.degree v := by
  have hE' : ∀ e, e ∈ (G.deleteIncidenceSet v).edgeFinset ↔
      (e ∈ G.edgeFinset ∧ e ∉ G.incidenceFinset v) := by
    intro e
    rw [mem_edgeFinset, edgeSet_deleteIncidenceSet, Set.mem_sdiff, mem_edgeFinset,
      mem_incidenceFinset]
  have hsplit : ∀ T : Finset V, (G.edgeFinset.filter (Same T)).card
      = ((G.deleteIncidenceSet v).edgeFinset.filter (Same T)).card
        + ((G.incidenceFinset v).filter (Same T)).card := by
    intro T
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_union, hE']
      have hsub : e ∈ G.incidenceFinset v → e ∈ G.edgeFinset := fun h =>
        G.incidenceFinset_subset v h
      tauto
    · rw [Finset.disjoint_left]
      intro e he1 he2
      rw [Finset.mem_filter, hE'] at he1
      rw [Finset.mem_filter] at he2
      exact he1.1.2 he2.1
  have hsame : ∀ T : Finset V, (∀ x, x ≠ v → (x ∈ T ↔ x ∈ S)) →
      (G.deleteIncidenceSet v).edgeFinset.filter (Same T)
        = (G.deleteIncidenceSet v).edgeFinset.filter (Same S) := by
    intro T hT
    apply Finset.filter_congr
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet, deleteIncidenceSet_adj] at he
      rw [same_mk, same_mk, hT x he.2.1, hT y he.2.2]
  have hcompl : (G.incidenceFinset v).filter (Same (S.erase v))
      = (G.incidenceFinset v).filter (fun e => ¬ Same (insert v S) e) := by
    apply Finset.filter_congr
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_incidenceFinset, mk'_mem_incidenceSet_iff] at he
      rw [same_mk, same_mk]
      rcases he with ⟨hxy, hvx | hvy⟩
      · have hyv : y ≠ v := by rw [hvx]; exact hxy.ne'
        rw [← hvx]
        simp [hyv]
      · have hxv : x ≠ v := by rw [hvy]; exact hxy.ne
        rw [← hvy]
        simp [hxv]
  have hI := Finset.card_filter_add_card_filter_not (s := G.incidenceFinset v)
    (Same (insert v S))
  rw [← hcompl, card_incidenceFinset_eq_degree] at hI
  have h1 := hsplit (insert v S)
  have h2 := hsplit (S.erase v)
  rw [hsame (insert v S) (fun x hx => by simp [hx])] at h1
  rw [hsame (S.erase v) (fun x hx => by simp [hx])] at h2
  by_cases hc : ((G.incidenceFinset v).filter (Same (insert v S))).card
      ≤ ((G.incidenceFinset v).filter (Same (S.erase v))).card
  · exact ⟨insert v S, by omega⟩
  · exact ⟨S.erase v, by omega⟩

lemma deg_zero_of_isolated (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (h : ∀ w, ¬ G.Adj v w) : G.degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero]
  ext w
  simp [h w]

end

lemma exists_low_deg (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] :
    ∃ v, 25 * G.degree v ≤ 2 * G.edgeFinset.card := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  by_contra hcon
  push Not at hcon
  have h1 : ∑ _v : Fin 25, (2 * G.edgeFinset.card + 1) ≤ ∑ v : Fin 25, 25 * G.degree v :=
    Finset.sum_le_sum (fun v _ => hcon v)
  rw [← Finset.mul_sum, hsum] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  omega

lemma exists_low_deg' (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (v : Fin 25)
    (hv : G.degree v = 0) :
    ∃ u, u ≠ v ∧ 24 * G.degree u ≤ 2 * G.edgeFinset.card := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  by_contra hcon
  push Not at hcon
  have h1 : ∑ _u ∈ (univ.erase v : Finset (Fin 25)), (2 * G.edgeFinset.card + 1)
      ≤ ∑ u ∈ (univ.erase v : Finset (Fin 25)), 24 * G.degree u :=
    Finset.sum_le_sum (fun u hu => hcon u (Finset.ne_of_mem_erase hu))
  have h2 : ∑ u ∈ (univ.erase v : Finset (Fin 25)), G.degree u = 2 * G.edgeFinset.card := by
    rw [← hsum, ← Finset.add_sum_erase univ _ (mem_univ v), hv, zero_add]
  rw [← Finset.mul_sum, h2] at h1
  simp only [Finset.sum_const, Finset.card_erase_of_mem (mem_univ v), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h1
  omega

open scoped Classical in
/-- A graph on 25 vertices with two isolated vertices is a graph on 23 vertices. -/
lemma transfer (k M : ℕ)
    (hyp : ∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
      G.edgeFinset.card ≤ M →
      ∃ S : Finset (Fin 23),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ k)
    (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (u v : Fin 25) (huv : u ≠ v) (hu : ∀ w, ¬ G.Adj u w) (hv : ∀ w, ¬ G.Adj v w)
    (hm : G.edgeFinset.card ≤ M) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ k := by
  have hcard : (({u, v} : Finset (Fin 25))ᶜ).card = 23 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair huv]
  obtain ⟨f, hf⟩ : ∃ f : Fin 23 ↪ Fin 25, ∀ x, x ≠ u → x ≠ v → ∃ a, f a = x := by
    refine ⟨(Finset.orderEmbOfFin _ hcard).toEmbedding, fun x hxu hxv => ?_⟩
    have hx : x ∈ (({u, v} : Finset (Fin 25))ᶜ) := by
      rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin _ hcard] at hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, ha⟩
  have hcf : (G.comap f).CliqueFree 3 := hG.comap (Embedding.comap f G).isContained
  have hle : (G.comap f).edgeFinset.card ≤ G.edgeFinset.card := by
    apply Finset.card_le_card_of_injOn (Sym2.map f)
    · intro e he
      induction e using Sym2.ind with
      | h a b =>
        rw [Finset.mem_coe, mem_edgeFinset, mem_edgeSet, comap_adj] at he
        rw [Sym2.map_mk, Finset.mem_coe, mem_edgeFinset, mem_edgeSet]
        exact he
    · exact (Sym2.map.injective f.injective).injOn
  obtain ⟨S3, hS3⟩ := hyp (G.comap f) hcf (le_trans hle hm)
  refine ⟨S3.map f, le_trans ?_ hS3⟩
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := Sym2.map f))
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, same_mk] at he
    obtain ⟨hxy, hside⟩ := he
    have hxu : x ≠ u := fun h => hu y (h ▸ hxy)
    have hxv : x ≠ v := fun h => hv y (h ▸ hxy)
    have hyu : y ≠ u := fun h => hu x (h ▸ hxy.symm)
    have hyv : y ≠ v := fun h => hv x (h ▸ hxy.symm)
    obtain ⟨a, rfl⟩ := hf x hxu hxv
    obtain ⟨b, rfl⟩ := hf y hyu hyv
    rw [Finset.mem_image]
    refine ⟨s(a, b), ?_, rfl⟩
    rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, comap_adj]
    refine ⟨hxy, (same_mk S3 a b).2 ?_⟩
    rw [Finset.mem_map', Finset.mem_map'] at hside
    exact hside

open scoped Classical in
/-- Two vertex deletions.  The vertex `v` has degree at most 7; the sharper input `hC` is only
used when the degree of `v` is at least 6. -/
lemma two_del (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hm : G.edgeFinset.card ≤ 99) (v : Fin 25) (hv : G.degree v ≤ 7)
    (hA : (∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
      ∃ S : Finset (Fin 23),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 21))
    (hB : (∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
      G.edgeFinset.card ≤ 89 →
      ∃ S : Finset (Fin 23),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 20))
    (hC : 6 ≤ G.degree v → (∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
      G.edgeFinset.card ≤ 87 →
      ∃ S : Finset (Fin 23),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 19)) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  have hm1 : (G.deleteIncidenceSet v).edgeFinset.card = G.edgeFinset.card - G.degree v :=
    card_edgeFinset_deleteIncidenceSet G v
  have hiso1 : ∀ w, ¬ (G.deleteIncidenceSet v).Adj v w := by
    intro w hw
    rw [deleteIncidenceSet_adj] at hw
    exact hw.2.1 rfl
  obtain ⟨u, huv, hu⟩ := exists_low_deg' (G.deleteIncidenceSet v) v
    (deg_zero_of_isolated _ v hiso1)
  have hm2 : ((G.deleteIncidenceSet v).deleteIncidenceSet u).edgeFinset.card
      = (G.deleteIncidenceSet v).edgeFinset.card - (G.deleteIncidenceSet v).degree u :=
    card_edgeFinset_deleteIncidenceSet (G.deleteIncidenceSet v) u
  have hiso2u : ∀ w, ¬ ((G.deleteIncidenceSet v).deleteIncidenceSet u).Adj u w := by
    intro w hw
    rw [deleteIncidenceSet_adj] at hw
    exact hw.2.1 rfl
  have hiso2v : ∀ w, ¬ ((G.deleteIncidenceSet v).deleteIncidenceSet u).Adj v w := by
    intro w hw
    rw [deleteIncidenceSet_adj] at hw
    exact hiso1 w hw.1
  have hcf2 : ((G.deleteIncidenceSet v).deleteIncidenceSet u).CliqueFree 3 :=
    (hG.anti (deleteIncidenceSet_le G v)).anti (deleteIncidenceSet_le _ u)
  by_cases hbad : 6 ≤ G.degree v ∧ 6 ≤ (G.deleteIncidenceSet v).degree u
  · obtain ⟨S, hS⟩ := transfer 19 87 (hC hbad.1) _ hcf2 u v huv hiso2u hiso2v (by omega)
    obtain ⟨Sa, hSa⟩ := del_vertex (G.deleteIncidenceSet v) u S
    obtain ⟨Sb, hSb⟩ := del_vertex G v Sa
    exact ⟨Sb, by omega⟩
  · by_cases h5 : 5 ≤ G.degree v / 2 + (G.deleteIncidenceSet v).degree u / 2
    · obtain ⟨S, hS⟩ := transfer 20 89 hB _ hcf2 u v huv hiso2u hiso2v (by omega)
      obtain ⟨Sa, hSa⟩ := del_vertex (G.deleteIncidenceSet v) u S
      obtain ⟨Sb, hSb⟩ := del_vertex G v Sa
      exact ⟨Sb, by omega⟩
    · obtain ⟨S, hS⟩ := transfer 21 99 (fun G23 _ hcf _ => hA G23 hcf) _ hcf2 u v huv
        hiso2u hiso2v (by omega)
      obtain ⟨Sa, hSa⟩ := del_vertex (G.deleteIncidenceSet v) u S
      obtain ⟨Sb, hSb⟩ := del_vertex G v Sa
      exact ⟨Sb, by omega⟩

open scoped Classical in
/-- The theorem, conditional on four inputs: the dense range on 25 vertices (`h1`), the sparse
core on 25 vertices (`h2`), and two statements on 23 vertices (`h3`, `h4`).  The first two are
special cases of the theorem; the last two are of the kind settled by McKay's computations. -/
lemma main_cut_of_literature
    (h1 : ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
      100 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 123 → (∀ v, G.degree v ≤ 13) →
      ∃ S : Finset (Fin 25),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25)
    (h2 : ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
      G.edgeFinset.card ≤ 99 → (∀ v, 6 ≤ G.degree v) → (∀ v, G.degree v ≤ 13) →
      ∃ S : Finset (Fin 25),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25)
    (h3 : (∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
      ∃ S : Finset (Fin 23),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 21))
    (h4 : (∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
      G.edgeFinset.card ≤ 89 →
      ∃ S : Finset (Fin 23),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 20))
    (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  have hfeq : ∀ S : Finset (Fin 25), G.edgeFinset.filter (Same S)
      = G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) := by
    intro S
    ext e
    simp only [Finset.mem_filter, Same]
  by_cases hd : ∃ v, 14 ≤ G.degree v
  · obtain ⟨v, hv⟩ := hd
    exact highdeg_case G hG v hv
  push Not at hd
  have hdeg : ∀ v, G.degree v ≤ 13 := fun v => by have := hd v; omega
  by_cases hm : G.edgeFinset.card ≤ 99
  · obtain ⟨v, -, hvmin⟩ := Finset.exists_min_image univ (fun w => G.degree w) univ_nonempty
    by_cases h6 : 6 ≤ G.degree v
    · obtain ⟨S, hS⟩ := h2 G hG hm (fun w => le_trans h6 (hvmin w (mem_univ w))) hdeg
      exact ⟨S, by rw [hfeq]; exact hS⟩
    · exact two_del G hG hm v (by omega) h3 h4 (fun h => absurd h h6)
  by_cases hbig : 124 ≤ G.edgeFinset.card
  · exact dense_case G hG hbig
  obtain ⟨S, hS⟩ := h1 G hG (by omega) (by omega) hdeg
  exact ⟨S, by rw [hfeq]; exact hS⟩

open scoped Classical in
/-- The sparse core (at most 99 edges, all degrees at least 6) follows from three statements on
23 vertices; the sharpest one (at most 87 edges, at most 19 deletions) is unconfirmed. -/
lemma sparse_core_of_23 (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hm : G.edgeFinset.card ≤ 99)
    (h3 : (∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
      ∃ S : Finset (Fin 23),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 21))
    (h4 : (∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
      G.edgeFinset.card ≤ 89 →
      ∃ S : Finset (Fin 23),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 20))
    (hs : (∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
      G.edgeFinset.card ≤ 87 →
      ∃ S : Finset (Fin 23),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 19)) :
    ∃ S : Finset (Fin 25), (G.edgeFinset.filter (Same S)).card ≤ 25 := by
  obtain ⟨v, hv⟩ := exists_low_deg G
  exact two_del G hG hm v (by omega) h3 h4 (fun _ => hs)

end OMA23

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n5 := by
  classical
  intro G hG
  obtain ⟨S, hS⟩ := OMA23.main_cut G hG
  refine ⟨OMA23.cutG G S, OMA23.cutG_le G S, OMA23.cutG_bip G S, ?_⟩
  rw [OMA23.uncut_card]
  convert hS
