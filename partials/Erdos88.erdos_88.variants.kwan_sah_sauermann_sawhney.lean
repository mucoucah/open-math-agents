import FormalConjectures.ErdosProblems.«88»

/-!
# Erdős Problem 88, Kwan–Sah–Sauermann–Sawhney variant

A neighborhood recursion treats the small Ramsey constants. For the other constants,
threshold graphs give the smallest counts, and restriction to an induced subgraph
reduces intermediate counts to a constant fraction of the host edge count.
-/

open Filter

namespace OMA.E88

/-- The empty vertex set induces a graph with no edges. -/
lemma induce_empty_ncard {n : ℕ} (G : SimpleGraph (Fin n)) :
    (G.induce ((∅ : Finset (Fin n)) : Set (Fin n))).edgeSet.ncard = 0 := by
  rw [Set.ncard_eq_zero]
  ext e
  refine Sym2.ind (fun a b => ?_) e
  simp only [SimpleGraph.mem_edgeSet, Set.mem_empty_iff_false, iff_false]
  exact absurd a.2 (by simp)

/-- Trivial regime: if eta is at least one then only m = 0 is allowed. -/
lemma large_eta (C η : ℝ) (hη : 1 ≤ η) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.logb 2 n → (G.indepNum : ℝ) < C * Real.logb 2 n →
        ∀ m : ℕ, (m : ℝ) ≤ (1 - η) * G.edgeSet.ncard →
          ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m := by
  refine Eventually.of_forall (fun n G _ _ m hm => ⟨∅, ?_⟩)
  have h1 : (1 - η) * (G.edgeSet.ncard : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
  have hm0 : m = 0 := by exact_mod_cast le_antisymm (hm.trans h1) (Nat.cast_nonneg m)
  rw [hm0]
  exact induce_empty_ncard G

/-- The neighborhood recursion bounds the size of a set with two homogeneous-set bounds. -/
lemma card_add_one_le_two_pow {α : Type*} (G : SimpleGraph α) (a b : ℕ)
    (s : Finset α) (hc : ∀ t ⊆ s, G.IsClique (t : Set α) → t.card ≤ a)
    (hi : ∀ t ⊆ s, G.IsIndepSet (t : Set α) → t.card ≤ b) :
    s.card + 1 ≤ 2 ^ (a + b) := by
  classical
  have hpow (k : ℕ) : 1 ≤ (2 : ℕ) ^ k := Nat.succ_le_of_lt (by positivity)
  induction a generalizing b s with
  | zero =>
    suffices h : s = ∅ by simp [h, hpow]
    by_contra hs
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have h := hc {v} (Finset.singleton_subset_iff.mpr hv) (by simp)
    simp at h
  | succ a iha =>
    induction b generalizing s with
    | zero =>
      suffices h : s = ∅ by simp [h, hpow]
      by_contra hs
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have h := hi {v} (Finset.singleton_subset_iff.mpr hv) (by simp)
      simp at h
    | succ b ihb =>
      by_cases hs : s = ∅
      · simp [hs, hpow]
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      let A := (s.erase v).filter (G.Adj v)
      let B := (s.erase v).filter (fun w => ¬ G.Adj v w)
      have hA : A ⊆ s := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hB : B ⊆ s := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hAv : v ∉ A := by simp [A]
      have hBv : v ∉ B := by simp [B]
      have ha : A.card + 1 ≤ 2 ^ (a + (b + 1)) := by
        refine iha (b + 1) A ?_ (fun t ht => hi t (ht.trans hA))
        intro t ht hcl
        have hv' : v ∉ t := fun h => hAv (ht h)
        have hcl' : G.IsClique (↑(insert v t) : Set α) := by
          rw [Finset.coe_insert]
          exact hcl.insert (fun w hw _ => (Finset.mem_filter.mp (ht hw)).2)
        have h := hc (insert v t) (Finset.insert_subset hv (ht.trans hA)) hcl'
        rw [Finset.card_insert_of_notMem hv'] at h
        omega
      have hb : B.card + 1 ≤ 2 ^ ((a + 1) + b) := by
        refine ihb B (fun t ht => hc t (ht.trans hB)) ?_
        intro t ht hin
        have hv' : v ∉ t := fun h => hBv (ht h)
        have hin' : G.IsIndepSet (↑(insert v t) : Set α) := by
          rw [← SimpleGraph.isClique_compl] at hin ⊢
          rw [Finset.coe_insert]
          exact hin.insert (fun w hw hne => by
            rw [SimpleGraph.compl_adj]
            exact ⟨hne, (Finset.mem_filter.mp (ht hw)).2⟩)
        have h := hi (insert v t) (Finset.insert_subset hv (ht.trans hB)) hin'
        rw [Finset.card_insert_of_notMem hv'] at h
        omega
      have hsplit : A.card + B.card = (s.erase v).card :=
        Finset.card_filter_add_card_filter_not _
      have herase := Finset.card_erase_add_one hv
      rw [show a + 1 + (b + 1) = (a + (b + 1)) + 1 by omega, pow_succ]
      rw [show a + 1 + b = a + (b + 1) by omega] at hb
      omega

/-- The strict logarithmic bounds are inconsistent when the Ramsey constant is at most one half. -/
lemma small_C {n : ℕ} (G : SimpleGraph (Fin n)) (C : ℝ) (hC : C ≤ 1 / 2)
    (hc : (G.cliqueNum : ℝ) < C * Real.logb 2 n)
    (hi : (G.indepNum : ℝ) < C * Real.logb 2 n) : False := by
  have hn : 0 < n := by
    by_contra! h
    have heq : n = 0 := by omega
    simp [heq, not_lt.mpr (Nat.cast_nonneg _)] at hc
  have hcard : n + 1 ≤ 2 ^ (G.cliqueNum + G.indepNum) := by
    simpa using card_add_one_le_two_pow G G.cliqueNum G.indepNum Finset.univ
      (fun _ _ h => h.card_le_cliqueNum) (fun _ _ h => h.card_le_indepNum)
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ ((G.cliqueNum : ℝ) + G.indepNum) := by
    rw [← Nat.cast_add, Real.rpow_natCast]
    exact_mod_cast (Nat.le_succ n).trans hcard
  have hlog : Real.logb 2 n ≤ (G.cliqueNum : ℝ) + G.indepNum :=
    (Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hn)).mpr hpow
  have hlog0 : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
  have hhalf := mul_le_mul_of_nonneg_right hC hlog0
  linarith

section InducedSubgraphs

variable {α β : Type*} {H : SimpleGraph α} {G : SimpleGraph β}

/-- A graph embedding carries any induced edge count into the ambient graph. -/
lemma edge_ncard_induce_map (f : H ↪g G) (T : Finset α) :
    (H.induce (T : Set α)).edgeSet.ncard =
      (G.induce (T.map f.toEmbedding : Set β)).edgeSet.ncard := by
  let g := f.comp (SimpleGraph.Embedding.induce (G := H) (T : Set α))
  have hrange : Set.range g = (T.map f.toEmbedding : Set β) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe, Finset.mem_map]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.prop, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have he : (H.induce (T : Set α)).edgeSet.ncard =
      (G.induce (Set.range g)).edgeSet.ncard := Set.ncard_congr' g.isoInduceRange.mapEdgeSet
  rwa [hrange] at he

lemma cliqueNum_le_of_embedding [Finite β] (f : H ↪g G) : H.cliqueNum ≤ G.cliqueNum := by
  obtain ⟨T, hT⟩ := H.exists_isNClique_cliqueNum
  have hmap : G.IsClique (T.map f.toEmbedding : Set β) := by
    intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    exact f.map_rel_iff.mpr (hT.isClique hv hw (fun h => hxy (congrArg f h)))
  simpa only [Finset.card_map, hT.card_eq] using hmap.card_le_cliqueNum

lemma indepNum_le_of_embedding [Finite β] (f : H ↪g G) : H.indepNum ≤ G.indepNum := by
  simpa only [SimpleGraph.cliqueNum_compl] using
    cliqueNum_le_of_embedding (SimpleGraph.Embedding.complEquiv f)

lemma edge_ncard_le_square [Fintype β] (G : SimpleGraph β) :
    G.edgeSet.ncard ≤ Fintype.card β ^ 2 := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  exact G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)

/-- Deleting a vertex from an induced subgraph removes exactly its incident edges. -/
lemma edge_ncard_erase [Fintype β] [DecidableEq β] (G : SimpleGraph β) (T : Finset β)
    (v : (T : Set β)) :
    letI := Classical.decRel (G.induce (T : Set β)).Adj
    (G.induce ((T.erase v.val : Finset β) : Set β)).edgeSet.ncard =
      (G.induce (T : Set β)).edgeSet.ncard - (G.induce (T : Set β)).degree v := by
  classical
  let H := G.induce (T : Set β)
  let U : Finset (T : Set β) := Finset.univ.erase v
  have hU : U.map (SimpleGraph.Embedding.induce (G := G) (T : Set β)).toEmbedding =
      T.erase v.val := by
    ext x
    simp only [U, Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun ⟨y, hy, hyx⟩ => ⟨fun h => hy (Subtype.ext (hyx.trans h)), hyx ▸ y.prop⟩,
      fun ⟨hne, hx⟩ => ⟨⟨x, hx⟩, fun h => hne (congrArg Subtype.val h), rfl⟩⟩
  have hcompl : (U : Set (T : Set β)) = {v}ᶜ := by ext x; simp [U]
  rw [← hU, ← edge_ncard_induce_map (SimpleGraph.Embedding.induce (G := G) (T : Set β)),
    hcompl, Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  exact (H.card_edgeFinset_induce_compl_singleton v).trans (H.card_edgeFinset_deleteIncidenceSet v)

/-- A subgraph minimal at the threshold of twice the target has at most three times the target. -/
lemma exists_induced_edge_ncard_between [Fintype β] (G : SimpleGraph β) (m : ℕ)
    (hm : 3 ≤ m) (hG : 2 * m ≤ G.edgeSet.ncard) :
    ∃ T : Finset β, 2 * m ≤ (G.induce (T : Set β)).edgeSet.ncard ∧
      (G.induce (T : Set β)).edgeSet.ncard ≤ 3 * m := by
  classical
  let candidates : Finset (Finset β) := Finset.univ.filter fun T =>
    2 * m ≤ (G.induce (T : Set β)).edgeSet.ncard
  have htop : (Finset.univ : Finset β) ∈ candidates := by
    have he : (G.induce Set.univ).edgeSet.ncard = G.edgeSet.ncard :=
      Set.ncard_congr' G.induceUnivIso.mapEdgeSet
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Finset.coe_univ, he]⟩
  obtain ⟨T, hT, hmin⟩ := candidates.exists_min_image Finset.card ⟨_, htop⟩
  have hTE := (Finset.mem_filter.mp hT).2
  let H := G.induce (T : Set β)
  have hTne : Nonempty (T : Set β) := by
    by_contra! h
    have hE : H.edgeSet.ncard = 0 := by
      rw [Set.ncard_eq_zero]
      exact Set.eq_empty_of_isEmpty _
    change 2 * m ≤ H.edgeSet.ncard at hTE
    omega
  obtain ⟨v, hv⟩ := H.exists_minimal_degree_vertex
  have hdel : (G.induce ((T.erase v.val : Finset β) : Set β)).edgeSet.ncard < 2 * m := by
    by_contra! h
    have hc : T.erase v.val ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    exact (not_lt_of_ge (hmin _ hc)) (Finset.card_erase_lt_of_mem v.prop)
  rw [edge_ncard_erase G T v] at hdel
  change H.edgeSet.ncard - H.degree v < 2 * m at hdel
  rw [← hv] at hdel
  have hsum : Fintype.card (T : Set β) * H.minDegree ≤ 2 * H.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    change _ ≤ 2 * H.edgeFinset.card
    rw [← H.sum_degrees_eq_twice_card_edges]
    calc
      _ = ∑ _w : (T : Set β), H.minDegree := by simp
      _ ≤ _ := Finset.sum_le_sum fun w _ => H.minDegree_le_degree w
  have hd : H.minDegree ≤ m := by
    by_contra! h
    have hverts := H.minDegree_lt_card
    have hmul := Nat.mul_le_mul (Nat.succ_le_of_lt hverts) (le_refl H.minDegree)
    have h4 : 4 ≤ H.minDegree := by omega
    have hprod := Nat.mul_le_mul h4 (show m ≤ H.minDegree - 1 by omega)
    have hsplit : H.minDegree - 1 + 1 = H.minDegree := by omega
    have hdiff : 2 * H.edgeSet.ncard < 4 * m + 2 * H.minDegree := by omega
    nlinarith [congrArg (H.minDegree * ·) hsplit]
  exact ⟨T, hTE, by change H.edgeSet.ncard ≤ 3 * m; omega⟩

end InducedSubgraphs

/-- Inserting one vertex adds its edges to the existing vertices. -/
lemma edge_ncard_insert {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) (v : α) (hv : v ∉ S) :
    (G.induce (↑(insert v S) : Set α)).edgeSet.ncard =
      (G.induce (S : Set α)).edgeSet.ncard + (S.filter (G.Adj v)).card := by
  classical
  let T := insert v S
  let w : (T : Set α) := ⟨v, Finset.mem_insert_self _ _⟩
  let H := G.induce (T : Set α)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have h := edge_ncard_erase G T w
  change (G.induce (↑(T.erase v) : Set α)).edgeSet.ncard = H.edgeSet.ncard - H.degree w at h
  rw [show T.erase v = S by simp [T, hv]] at h
  have hdegree : H.degree w = (S.filter (G.Adj v)).card := by
    let emb : (T : Set α) ↪ α := Function.Embedding.subtype _
    rw [← H.card_neighborFinset_eq_degree, ← Finset.card_map (f := emb)]
    congr 1
    ext x
    simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change G.Adj v y.val at hy
      exact ⟨(Finset.mem_insert.mp y.prop).resolve_left hy.ne.symm, hy⟩
    · rintro ⟨hx, ha⟩
      exact ⟨⟨x, Finset.mem_insert_of_mem hx⟩, ha, rfl⟩
  have hle : H.degree w ≤ H.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card', ← H.card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (H.incidenceFinset_subset w)
  change H.edgeSet.ncard = _
  omega

/-- A potential budget for realizing an edge count by successive universal or isolated vertices. -/
lemma exists_edges_of_peeling {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℝ) (hq : 1 < q)
    (s : Finset (Fin n)) (l a b m : ℕ)
    (hc : ∀ t ⊆ s, G.IsClique (t : Set (Fin n)) → t.card ≤ a)
    (hi : ∀ t ⊆ s, G.IsIndepSet (t : Set (Fin n)) → t.card ≤ b)
    (hs : q ^ l * (q / (q - 1)) ^ (a + b) < (s.card : ℝ) + 1)
    (hm : m ≤ l.choose 2) :
    ∃ T ⊆ s, T.card = l ∧ (G.induce (T : Set (Fin n))).edgeSet.ncard = m := by
  classical
  let r := q / (q - 1)
  have hq0 : 0 < q := by linarith
  have hqsub : 0 < q - 1 := by linarith
  have hr : 1 ≤ r := (le_div_iff₀ hqsub).mpr (by linarith)
  have hsz : s.Nonempty := by
    by_contra! h
    rw [h] at hs
    have hcost : 1 * 1 ≤ q ^ l * r ^ (a + b) :=
      mul_le_mul (one_le_pow₀ hq.le) (one_le_pow₀ hr) (by norm_num) (by positivity)
    simp only [Finset.card_empty, Nat.cast_zero, zero_add] at hs
    exact (not_lt_of_ge (by simpa only [one_mul] using hcost)) hs
  obtain ⟨v, hv⟩ := hsz
  cases l with
  | zero =>
    have hm0 : m = 0 := by simpa using hm
    exact ⟨∅, Finset.empty_subset _, rfl, (induce_empty_ncard G).trans hm0.symm⟩
  | succ l =>
    cases a with
    | zero =>
      have h := hc {v} (Finset.singleton_subset_iff.mpr hv) (by simp)
      simp at h
    | succ a =>
      cases b with
      | zero =>
        have h := hi {v} (Finset.singleton_subset_iff.mpr hv) (by simp)
        simp at h
      | succ b =>
        change q ^ (l + 1) * r ^ (a + 1 + (b + 1)) < (s.card : ℝ) + 1 at hs
        let A := (s.erase v).filter (G.Adj v)
        let B := (s.erase v).filter (fun w => ¬ G.Adj v w)
        have hA : A ⊆ s := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
        have hB : B ⊆ s := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
        have hvA : v ∉ A := by simp [A]
        have hvB : v ∉ B := by simp [B]
        have hcliqueA (T : Finset (Fin n)) (hT : T ⊆ A) (hcl : G.IsClique (T : Set (Fin n))) :
            T.card ≤ a := by
          have hin : G.IsClique (↑(insert v T) : Set (Fin n)) := by
            rw [Finset.coe_insert]
            exact hcl.insert (fun w hw _ => (Finset.mem_filter.mp (hT hw)).2)
          have h := hc (insert v T) (Finset.insert_subset hv (hT.trans hA)) hin
          rw [Finset.card_insert_of_notMem (fun h => hvA (hT h))] at h
          omega
        have hindepB (T : Finset (Fin n)) (hT : T ⊆ B) (hin : G.IsIndepSet (T : Set (Fin n))) :
            T.card ≤ b := by
          have hin' : G.IsIndepSet (↑(insert v T) : Set (Fin n)) := by
            rw [← SimpleGraph.isClique_compl] at hin ⊢
            rw [Finset.coe_insert]
            exact hin.insert (fun w hw hne => by
              rw [SimpleGraph.compl_adj]
              exact ⟨hne, (Finset.mem_filter.mp (hT hw)).2⟩)
          have h := hi (insert v T) (Finset.insert_subset hv (hT.trans hB)) hin'
          rw [Finset.card_insert_of_notMem (fun h => hvB (hT h))] at h
          omega
        have hsplit : (A.card : ℝ) + 1 + ((B.card : ℝ) + 1) = (s.card : ℝ) + 1 := by
          have h := Finset.card_filter_add_card_filter_not (s := s.erase v) (G.Adj v)
          have h' : A.card + B.card + 1 = s.card := by
            exact (congrArg (· + 1) h).trans (Finset.card_erase_add_one hv)
          have h'' : (A.card : ℝ) + B.card + 1 = s.card := by exact_mod_cast h'
          linarith
        have hstep (X Y : ℝ) (hXY : X + Y = (s.card : ℝ) + 1) :
            q ^ l * r ^ (a + 1 + (b + 1)) < X ∨ q ^ (l + 1) * r ^ (a + b + 1) < Y := by
          by_cases hlarge : (s.card : ℝ) + 1 ≤ q * X
          · left
            apply (mul_lt_mul_iff_of_pos_left hq0).mp
            calc
              _ = q ^ (l + 1) * r ^ (a + 1 + (b + 1)) := by rw [pow_succ q]; ring
              _ < (s.card : ℝ) + 1 := hs
              _ ≤ _ := hlarge
          · right
            have hr0 : 0 < r := by linarith
            apply (mul_lt_mul_iff_of_pos_right hr0).mp
            calc
              _ = q ^ (l + 1) * r ^ (a + 1 + (b + 1)) := by
                rw [mul_assoc, ← pow_succ, show a + b + 1 + 1 = a + 1 + (b + 1) by omega]
              _ < (s.card : ℝ) + 1 := hs
              _ ≤ Y * r := by
                dsimp [r]
                rw [← mul_div_assoc]
                apply (le_div_iff₀ hqsub).mpr
                nlinarith [not_le.mp hlarge]
        have hchoose : (l + 1).choose 2 = l + l.choose 2 := by rw [Nat.choose_succ_succ', Nat.choose_one_right]
        by_cases hml : l ≤ m
        · rcases hstep (A.card + 1) (B.card + 1) hsplit with hgood | hbad
          · have hrest : m - l ≤ l.choose 2 := by omega
            obtain ⟨T, hT, hTc, hTe⟩ := exists_edges_of_peeling G q hq A l (a+1) (b+1) (m-l)
              (fun t ht => hc t (ht.trans hA)) (fun t ht => hi t (ht.trans hA)) hgood hrest
            have hvT : v ∉ T := fun h => hvA (hT h)
            refine ⟨insert v T, Finset.insert_subset hv (hT.trans hA),
              Finset.card_insert_of_notMem hvT |>.trans (congrArg (· + 1) hTc), ?_⟩
            rw [edge_ncard_insert G T v hvT, hTe, Finset.filter_true_of_mem
              (fun w hw => (Finset.mem_filter.mp (hT hw)).2), hTc]
            omega
          · have hbad' : q ^ (l + 1) * r ^ (a + 1 + b) < (B.card : ℝ) + 1 := by
              simpa only [show a + 1 + b = a + b + 1 by omega] using hbad
            obtain ⟨T, hT, hTc, hTe⟩ := exists_edges_of_peeling G q hq B (l+1) (a+1) b m
              (fun t ht => hc t (ht.trans hB)) hindepB hbad' hm
            exact ⟨T, hT.trans hB, hTc, hTe⟩
        · rcases hstep (B.card + 1) (A.card + 1) (by linarith) with hgood | hbad
          · have hrest : m ≤ l.choose 2 := by
              cases l with
              | zero => omega
              | succ d =>
                rw [Nat.choose_succ_succ', Nat.choose_one_right]
                omega
            obtain ⟨T, hT, hTc, hTe⟩ := exists_edges_of_peeling G q hq B l (a+1) (b+1) m
              (fun t ht => hc t (ht.trans hB)) (fun t ht => hi t (ht.trans hB)) hgood hrest
            have hvT : v ∉ T := fun h => hvB (hT h)
            refine ⟨insert v T, Finset.insert_subset hv (hT.trans hB),
              Finset.card_insert_of_notMem hvT |>.trans (congrArg (· + 1) hTc), ?_⟩
            have hfilter : T.filter (G.Adj v) = ∅ :=
              Finset.filter_eq_empty_iff.mpr (fun w hw => (Finset.mem_filter.mp (hT hw)).2)
            rw [edge_ncard_insert G T v hvT, hTe, hfilter, Finset.card_empty, Nat.add_zero]
          · have hbad' : q ^ (l + 1) * r ^ (a + (b + 1)) < (A.card : ℝ) + 1 := by
              simpa only [Nat.add_assoc] using hbad
            obtain ⟨T, hT, hTc, hTe⟩ := exists_edges_of_peeling G q hq A (l+1) a (b+1) m
              hcliqueA (fun t ht => hi t (ht.trans hA)) hbad' hm
            exact ⟨T, hT.trans hA, hTc, hTe⟩
termination_by l + a + b
decreasing_by all_goals omega

/-- The order up to which the peeling argument can realize threshold graphs. -/
noncomputable def thresholdOrder (C : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.log n / (2 * Real.log (1 + 4 * C / Real.log 2))⌋₊

lemma exists_edges_le_threshold {n : ℕ} (G : SimpleGraph (Fin n))
    (C : ℝ) (hC : 0 < C) (hc : (G.cliqueNum : ℝ) < C * Real.logb 2 n)
    (hi : (G.indepNum : ℝ) < C * Real.logb 2 n) (m : ℕ)
    (hm : m ≤ (thresholdOrder C n).choose 2) :
    ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m := by
  classical
  by_cases hn : n = 0
  · have hm0 : m = 0 := by simpa [hn, thresholdOrder] using hm
    exact ⟨∅, (induce_empty_ncard G).trans hm0.symm⟩
  let q := 1 + 4 * C / Real.log 2
  let r := q / (q - 1)
  let l := thresholdOrder C n
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 1 < q := by
    dsimp [q]
    linarith [div_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hC) hlog2]
  have hq0 : 0 < q := by linarith
  have hqsub : 0 < q - 1 := by linarith
  have hr : 0 < r := div_pos hq0 hqsub
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have h₁ : (l : ℝ) * Real.log q ≤ Real.log n / 2 := by
    have hfloor : (l : ℝ) ≤ Real.log n / (2 * Real.log q) :=
      Nat.floor_le (div_nonneg hlogn (by positivity))
    have h := (le_div_iff₀ (show 0 < 2 * Real.log q by positivity)).mp hfloor
    nlinarith
  have hsum : ((G.cliqueNum + G.indepNum : ℕ) : ℝ) ≤ (2 * C / Real.log 2) * Real.log n := by
    rw [Real.logb] at hc hi
    rw [Nat.cast_add, show (2 * C / Real.log 2) * Real.log n =
      2 * (C * (Real.log n / Real.log 2)) by ring]
    linarith
  have hlogr : Real.log r ≤ 1 / (q - 1) := by
    refine (Real.log_le_sub_one_of_pos hr).trans_eq ?_
    dsimp [r]
    field_simp [ne_of_gt hqsub]
    ring
  have h₂ : ((G.cliqueNum + G.indepNum : ℕ) : ℝ) * Real.log r ≤ Real.log n / 2 := by
    calc
      _ ≤ ((G.cliqueNum + G.indepNum : ℕ) : ℝ) * (1 / (q - 1)) :=
        mul_le_mul_of_nonneg_left hlogr (Nat.cast_nonneg _)
      _ ≤ (2 * C / Real.log 2) * Real.log n * (1 / (q - 1)) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = _ := by
        dsimp [q]
        field_simp [ne_of_gt hlog2, ne_of_gt hC]
        ring
  have hbudget : q ^ l * r ^ (G.cliqueNum + G.indepNum) ≤ (n : ℝ) := by
    apply (Real.log_le_log_iff (by positivity) hn0).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    linarith
  have hb : q ^ l * (q / (q - 1)) ^ (G.cliqueNum + G.indepNum) <
      ((Finset.univ : Finset (Fin n)).card : ℝ) + 1 := by
    simpa using hbudget.trans_lt (show (n : ℝ) < (n : ℝ) + 1 by linarith)
  obtain ⟨S, _, _, hS⟩ := exists_edges_of_peeling G q hq Finset.univ l G.cliqueNum G.indepNum m
    (fun _ _ h => h.card_le_cliqueNum) (fun _ _ h => h.card_le_indepNum) hb hm
  exact ⟨S, hS⟩

/-- Above the threshold-graph cutoff, the exact-count input is needed for targets below a fixed
power of the order and for targets comparable to the edge count. -/
lemma ksss_core_above_threshold (C : ℝ) (hC : 1 / 2 < C) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ k : ℕ, 0 < k ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.logb 2 n → (G.indepNum : ℝ) < C * Real.logb 2 n →
        ∀ m : ℕ, (m : ℝ) ≤ (1 - η) * G.edgeSet.ncard →
          (thresholdOrder C n).choose 2 < m →
          (m ^ k < n ∨ G.edgeSet.ncard ≤ 3 * m) →
          ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m := by
  sorry

lemma ksss_core (C : ℝ) (hC : 1 / 2 < C) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ k : ℕ, 0 < k ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.logb 2 n → (G.indepNum : ℝ) < C * Real.logb 2 n →
        ∀ m : ℕ, (m : ℝ) ≤ (1 - η) * G.edgeSet.ncard →
          (m ^ k < n ∨ G.edgeSet.ncard ≤ 3 * m) →
          ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m := by
  obtain ⟨k, hk, hcore⟩ := ksss_core_above_threshold C hC η hη hη1
  refine ⟨k, hk, hcore.mono fun n hn G hc hi m hm hregime => ?_⟩
  rcases le_or_gt m ((thresholdOrder C n).choose 2) with h | h
  · exact exists_edges_le_threshold G C (by linarith) hc hi m h
  · exact hn G hc hi m hm h hregime

/-- For the intervening targets, shrink the graph to put the target at constant relative size. -/
lemma ksss_main (C : ℝ) (hC : 1 / 2 < C) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.logb 2 n → (G.indepNum : ℝ) < C * Real.logb 2 n →
        ∀ m : ℕ, (m : ℝ) ≤ (1 - η) * G.edgeSet.ncard →
          ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m := by
  classical
  obtain ⟨k, hk, hcore⟩ := ksss_core C hC η hη hη1
  let C' : ℝ := (2 * k) * C
  let η' : ℝ := min η (1 / 2)
  have hC' : 1 / 2 < C' := by
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [C']
    nlinarith
  have hη' : 0 < η' := lt_min hη (by norm_num)
  have hη'half : η' ≤ 1 / 2 := min_le_right _ _
  have hη'1 : η' < 1 := hη'half.trans_lt (by norm_num)
  obtain ⟨_, _, hscaled⟩ := ksss_core C' hC' η' hη' hη'1
  obtain ⟨N, hN⟩ := eventually_atTop.mp hscaled
  filter_upwards [hcore, eventually_ge_atTop (max (2 ^ k + 1) (N ^ (2 * k)))] with n hncore hn
  intro G hc hi m hm
  by_cases hsmall : m ^ k < n
  · exact hncore G hc hi m hm (Or.inl hsmall)
  by_cases hratio : G.edgeSet.ncard ≤ 3 * m
  · exact hncore G hc hi m hm (Or.inr hratio)
  have hnlarge : 2 ^ k + 1 ≤ n := (le_max_left _ _).trans hn
  have hm3 : 3 ≤ m := by
    by_contra! h
    have hp := Nat.pow_le_pow_left (show m ≤ 2 by omega) k
    omega
  obtain ⟨T, hTlower, hTupper⟩ := exists_induced_edge_ncard_between G m hm3 (by omega)
  let H₀ := G.induce (T : Set (Fin n))
  let H := H₀.comap T.equivFin.symm
  let i : H ≃g H₀ := SimpleGraph.Iso.comap T.equivFin.symm H₀
  let f : H ↪g G := (SimpleGraph.Embedding.induce (G := G) (T : Set (Fin n))).comp i.toEmbedding
  have hE : H.edgeSet.ncard = H₀.edgeSet.ncard := Set.ncard_congr' i.mapEdgeSet
  have hTpow : n ≤ T.card ^ (2 * k) := by
    have hsq : H₀.edgeSet.ncard ≤ T.card ^ 2 := by
      have hcard : Fintype.card (T : Set (Fin n)) = T.card := Fintype.card_coe T
      rw [← hcard]
      exact edge_ncard_le_square H₀
    have hmT : m ≤ T.card ^ 2 := by change 2 * m ≤ H₀.edgeSet.ncard at hTlower; omega
    rw [pow_mul]
    exact (le_of_not_gt hsmall).trans (Nat.pow_le_pow_left hmT k)
  have hNT : N ≤ T.card := by
    by_contra! h
    have hlt := Nat.pow_lt_pow_left h (show 2 * k ≠ 0 by omega)
    exact (not_lt_of_ge (((le_max_right _ _).trans hn).trans hTpow)) hlt
  have hlog : Real.logb 2 n ≤ (2 * (k : ℝ)) * Real.logb 2 T.card := by
    calc
      _ ≤ Real.logb 2 ((T.card : ℝ) ^ (2 * k)) :=
        Real.logb_le_logb_of_le (by norm_num)
          (by exact_mod_cast (Nat.succ_pos (2 ^ k)).trans_le hnlarge)
          (by exact_mod_cast hTpow)
      _ = _ := by
        rw [Real.logb_pow, Nat.cast_mul]
        norm_num
  have hlogC : C * Real.logb 2 n ≤ C' * Real.logb 2 T.card := by
    dsimp [C']
    rw [mul_comm (2 * (k : ℝ)) C, mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog (by linarith)
  have hcH : (H.cliqueNum : ℝ) < C' * Real.logb 2 T.card :=
    (Nat.cast_le.mpr (cliqueNum_le_of_embedding f)).trans_lt (hc.trans_le hlogC)
  have hiH : (H.indepNum : ℝ) < C' * Real.logb 2 T.card :=
    (Nat.cast_le.mpr (indepNum_le_of_embedding f)).trans_lt (hi.trans_le hlogC)
  have hratioH : H.edgeSet.ncard ≤ 3 * m := hE.trans_le hTupper
  have hmH : (m : ℝ) ≤ (1 - η') * H.edgeSet.ncard := by
    have hl : (2 : ℝ) * m ≤ H.edgeSet.ncard := by exact_mod_cast hE.symm ▸ hTlower
    exact (show (m : ℝ) ≤ 1 / 2 * H.edgeSet.ncard by linarith).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  obtain ⟨S, hS⟩ := hN T.card hNT H hcH hiH m hmH (Or.inr hratioH)
  exact ⟨S.map f.toEmbedding, (edge_ncard_induce_map f S).symm.trans hS⟩

end OMA.E88

theorem OMA.solution : type_of% @Erdos88.erdos_88.variants.kwan_sah_sauermann_sawhney := by
  intro C hC η hη
  rcases lt_or_ge η 1 with h | h
  · rcases le_or_gt C (1 / 2) with hC' | hC'
    · exact Eventually.of_forall fun n G hc hi => (OMA.E88.small_C G C hC' hc hi).elim
    · exact OMA.E88.ksss_main C hC' η hη h
  · exact OMA.E88.large_eta C η h
