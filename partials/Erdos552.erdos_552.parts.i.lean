import FormalConjectures.ErdosProblems.«552»
import Mathlib

-- Problem: Erdős Problem 552 — i (it asks for a value)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/552.lean:48 (declaration Erdos552.erdos_552.parts.i; placeholder Erdos552.erdos_552.parts.i.answer := sorry)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Give the value explicitly as OMA.answer (same type as the placeholder; not built from Erdos552.…,
-- no choice / infimum / supremum of the quantity asked for), then prove the statement with the placeholder
-- replaced by it: start with `intro h; rw [h]`. No sorry, no axiom, no native_decide. A person checks the answer.

namespace OMA.CycleStar
open SimpleGraph Finset
open scoped Classical

private theorem cycle_adj_cases {i j : Fin 4} (h : (cycleGraph 4).Adj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3) := by
  revert h i j
  decide

/-- Two length-two walks between distinct vertices with different middle vertices give a cycle. -/
private theorem cycle_of_walks {V : Type*} (G : SimpleGraph V) {a b x y : V}
    (hab : a ≠ b) (hxy : x ≠ y) (hax : G.Adj a x) (hxb : G.Adj x b)
    (hay : G.Adj a y) (hyb : G.Adj y b) :
    (cycleGraph 4).IsContained G := by
  let f : Fin 4 → V := ![a, x, b, y]
  have hinj : Function.Injective f := by
    have hax' := G.ne_of_adj hax
    have hay' := G.ne_of_adj hay
    have hxb' := G.ne_of_adj hxb
    have hyb' := G.ne_of_adj hyb
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;> aesop
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  rintro i j hij
  rcases cycle_adj_cases hij with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | exact hax
    | exact hax.symm
    | exact hxb
    | exact hxb.symm
    | exact hay
    | exact hay.symm
    | exact hyb
    | exact hyb.symm

private theorem copy_star_of_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} (v : V) (hn : n ≤ G.degree v) :
    (completeBipartiteGraph (Fin 1) (Fin n)).IsContained G := by
  classical
  let s := G.neighborFinset v
  have hcard : n ≤ Fintype.card s := by
    rw [Fintype.card_coe, card_neighborFinset_eq_degree]
    exact hn
  let e : Fin n ↪ s := (Fin.castLEEmb hcard).trans (Fintype.equivFin s).symm.toEmbedding
  let f : Fin 1 ⊕ Fin n → V := Sum.elim (fun _ => v) (fun j => (e j).val)
  have hedge (j : Fin n) : G.Adj v (e j).val :=
    (G.mem_neighborFinset _ _).mp (e j).property
  have hinj : Function.Injective f := by
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subsingleton.elim i j)
      | inr j => exact ((G.ne_of_adj (hedge j)) h).elim
    | inr i =>
      cases j with
      | inl j => exact ((G.ne_of_adj (hedge i)) h.symm).elim
      | inr j => exact congrArg Sum.inr (e.injective (Subtype.ext h))
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro i j hij
  cases i <;> cases j <;> simp_all [completeBipartiteGraph, f, G.adj_comm]

private def twoStepEndpoints {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (G.neighborFinset v).biUnion fun w => (G.neighborFinset w).erase v

private theorem mem_twoStepEndpoints {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v w : V} :
    w ∈ twoStepEndpoints G v ↔ w ≠ v ∧ ∃ u, G.Adj v u ∧ G.Adj w u := by
  simp only [twoStepEndpoints, mem_biUnion, mem_erase, mem_neighborFinset]
  exact ⟨fun ⟨u, hvu, hwv, huw⟩ => ⟨hwv, u, hvu, huw.symm⟩,
    fun ⟨hwv, u, hvu, hwu⟩ => ⟨u, hvu, hwv, hwu.symm⟩⟩

private theorem twoStepEndpoints_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    twoStepEndpoints G v ⊆ univ.erase v :=
  fun w hw => mem_erase.mpr ⟨((mem_twoStepEndpoints G).mp hw).1, mem_univ w⟩

private theorem card_twoStepEndpoints {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ¬ (cycleGraph 4).IsContained G) (v : V) :
    (twoStepEndpoints G v).card = ∑ w ∈ G.neighborFinset v, (G.degree w - 1) := by
  let s := G.neighborFinset v
  let t (w : V) := (G.neighborFinset w).erase v
  have hdisj : (s : Set V).PairwiseDisjoint t := by
    intro x hx y hy hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro b hbx hby
    obtain ⟨hbv, hxb⟩ := mem_erase.mp hbx
    have hvar (w : V) (hw : w ∈ s) : G.Adj v w := (G.mem_neighborFinset _ _).mp hw
    exact hG (cycle_of_walks G hbv.symm hxy (hvar x hx) ((G.mem_neighborFinset _ _).mp hxb)
      (hvar y hy) ((G.mem_neighborFinset _ _).mp (mem_erase.mp hby).2))
  change (s.biUnion t).card = _
  rw [card_biUnion hdisj]
  refine sum_congr rfl fun w hw => ?_
  have hvw : G.Adj v w := (G.mem_neighborFinset _ _).mp hw
  change ((G.neighborFinset w).erase v).card = _
  rw [card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hvw.symm), card_neighborFinset_eq_degree]

/-- In a C4-free graph the number of non-returning two-step walks is bounded
    by the number of possible endpoints. -/
theorem vertex_degree_mul_pred_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ¬ (cycleGraph 4).IsContained G)
    {d : ℕ} (hd : ∀ v, d ≤ G.degree v) (v : V) :
    G.degree v * (d - 1) ≤ Fintype.card V - 1 := by
  classical
  calc
    G.degree v * (d - 1) = ∑ _w ∈ G.neighborFinset v, (d - 1) := by simp
    _ ≤ ∑ w ∈ G.neighborFinset v, (G.degree w - 1) :=
      sum_le_sum fun w _ => Nat.sub_le_sub_right (hd w) 1
    _ = (twoStepEndpoints G v).card := (card_twoStepEndpoints G hG v).symm
    _ ≤ (univ.erase v).card := card_le_card (twoStepEndpoints_subset G v)
    _ = Fintype.card V - 1 := by simp

/-- A uniform lower bound on degrees yields a uniform bound on two-step walks. -/
theorem degree_mul_pred_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ¬ (cycleGraph 4).IsContained G)
    {d : ℕ} (hd : ∀ v, d ≤ G.degree v) (v : V) :
    d * (d - 1) ≤ Fintype.card V - 1 :=
  (Nat.mul_le_mul_right (d - 1) (hd v)).trans (vertex_degree_mul_pred_le G hG hd v)

private theorem exists_degree_of_copy_star {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ}
    (h : (completeBipartiteGraph (Fin 1) (Fin n)).IsContained G) :
    ∃ v, n ≤ G.degree v := by
  obtain ⟨f⟩ := h
  let v := f (Sum.inl 0)
  let e (i : Fin n) : G.neighborFinset v :=
    ⟨f (Sum.inr i), (G.mem_neighborFinset _ _).mpr
      (f.toHom.map_adj (by simp [completeBipartiteGraph]))⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Sum.inr_injective (f.injective (congrArg Subtype.val hij))
  exact ⟨v, by simpa only [Fintype.card_fin, Fintype.card_coe, card_neighborFinset_eq_degree]
    using Fintype.card_le_of_injective e he⟩

private theorem not_copy_star_compl_iff {m n : ℕ} (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] :
    ¬ (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Gᶜ ↔
      ∀ v, m - n ≤ G.degree v := by
  classical
  constructor
  · intro h v
    have hdeg : Gᶜ.degree v < n := lt_of_not_ge (fun hv => h (copy_star_of_degree Gᶜ v hv))
    rw [G.degree_compl] at hdeg
    have hcard := G.degree_lt_card_verts v
    simp only [Fintype.card_fin] at hdeg hcard
    change m - n ≤ G.degree v
    omega
  · intro h hstar
    obtain ⟨v, hv⟩ := exists_degree_of_copy_star Gᶜ hstar
    rw [G.degree_compl] at hv
    have hcard := G.degree_lt_card_verts v
    simp only [Fintype.card_fin] at hv hcard
    have hdeg : m - n ≤ G.degree v := h v
    omega

private theorem cycle_or_star_at_bound (n : ℕ) :
    ∀ G : SimpleGraph (Fin (n + Nat.sqrt n + 2)), (cycleGraph 4).IsContained G ∨
      (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Gᶜ := by
  classical
  let s := Nat.sqrt n
  let m := n + s + 2
  change ∀ G : SimpleGraph (Fin m), (cycleGraph 4).IsContained G ∨
    (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Gᶜ
  intro G
  by_contra h
  rw [not_or] at h
  have hd (v : Fin m) : s + 2 ≤ G.degree v := by
    have hmin := (not_copy_star_compl_iff G).mp h.2 v
    dsimp [m] at hmin
    omega
  let v : Fin m := ⟨0, by dsimp [m]; omega⟩
  have hcount := degree_mul_pred_le G h.1 hd v
  have hs : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  simp only [Fintype.card_fin] at hcount
  change (s + 2) * (s + 1) ≤ n + s + 1 at hcount
  nlinarith

/-- The four-cycle versus star Ramsey number is bounded by the length-two walk count. -/
theorem ramsey_le_add_sqrt_add_two (n : ℕ) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) ≤
      n + Nat.sqrt n + 2 := by
  apply Nat.sInf_le
  exact cycle_or_star_at_bound n

private theorem ramsey_le_iff_cycle_or_star (m n : ℕ) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) ≤ m ↔
      ∀ G : SimpleGraph (Fin m), (cycleGraph 4).IsContained G ∨
        (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Gᶜ := by
  let P : Set ℕ := {k | ∀ G : SimpleGraph (Fin k), (cycleGraph 4).IsContained G ∨
      (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Gᶜ}
  change sInf P ≤ m ↔ m ∈ P
  refine ⟨?_, Nat.sInf_le⟩
  intro hm G
  have hP : P.Nonempty := ⟨_, cycle_or_star_at_bound n⟩
  let e := Fin.castLEEmb hm
  let f := SimpleGraph.Embedding.comap e G
  rcases Nat.sInf_mem hP (G.comap e) with hCycle | hStar
  · exact Or.inl (hCycle.trans f.isContained)
  · exact Or.inr (hStar.trans (SimpleGraph.Embedding.complEquiv f).isContained)

/-- An order lies below the Ramsey number precisely when a C4-free graph
    of that order has minimum degree at least the order minus the number of leaves. -/
theorem lt_ramsey_iff_exists_min_degree (m n : ℕ) :
    m < graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) ↔
      ∃ G : SimpleGraph (Fin m), ¬ (cycleGraph 4).IsContained G ∧
        ∀ v, m - n ≤ G.degree v := by
  classical
  rw [← not_le, ramsey_le_iff_cycle_or_star, Classical.not_forall]
  refine exists_congr fun G => ?_
  rw [not_or]
  refine and_congr_right fun _ => ?_
  exact not_copy_star_compl_iff G

/-- Below the threshold for a vertex of degree at least d+1, minimum degree d
    in a C4-free graph forces every vertex to have degree d. -/
theorem regular_of_small_order {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ¬ (cycleGraph 4).IsContained G)
    {d : ℕ} (hd : ∀ v, d ≤ G.degree v)
    (horder : Fintype.card V - 1 < (d + 1) * (d - 1)) (v : V) :
    G.degree v = d := by
  apply le_antisymm _ (hd v)
  by_contra! h
  have hmul := Nat.mul_le_mul_right (d - 1) (Nat.succ_le_of_lt h)
  exact (not_le_of_gt horder) (hmul.trans (vertex_degree_mul_pred_le G hG hd v))

/-- When both the order and required degree are odd, the degree-sum formula
    excludes a regular counterexample at the specified order. -/
theorem ramsey_le_of_odd_order_and_degree {n d : ℕ}
    (horder : n + d - 1 < (d + 1) * (d - 1))
    (hm : Odd (n + d)) (hd : Odd d) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) ≤ n + d := by
  classical
  by_contra! h
  obtain ⟨G, hG, hdeg⟩ := (lt_ramsey_iff_exists_min_degree (n + d) n).mp h
  have hreg (v : Fin (n + d)) : G.degree v = d :=
    regular_of_small_order G hG (fun w => by simpa using hdeg w) (by simpa using horder) v
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hreg, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact (Nat.not_even_iff_odd.mpr (hm.mul hd)) ⟨G.edgeFinset.card, by omega⟩

/-- For odd k and even excess t in the indicated range, the general upper
    bound improves by one. -/
theorem ramsey_le_add_of_even_excess {k t : ℕ} (hk : Odd k) (ht : Even t)
    (htlo : 0 < t) (hthi : t + 2 ≤ k) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin ((k - 1)^2 + t))) ≤
      (k - 1)^2 + t + k := by
  have hk1 : k - 1 + 1 = k := by omega
  apply ramsey_le_of_odd_order_and_degree _ _ hk
  · have hm : (k + 1) * (k - 1) = (k - 1)^2 + 2 * (k - 1) := by nlinarith
    rw [hm]
    omega
  · have he : Even (k - 1) := by
      obtain ⟨a, ha⟩ := hk
      exact ⟨a, by omega⟩
    have he2 : Even ((k - 1)^2) := he.pow_of_ne_zero (by decide)
    exact (he2.add ht).add_odd hk

/-- Join distinct vertices when they have no common neighbor in G. -/
private def missingCommonGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ¬ ∃ u, G.Adj v u ∧ G.Adj w u
  symm := ⟨fun _ _ ⟨hvw, h⟩ => ⟨hvw.symm, fun ⟨u, hwu, hvu⟩ => h ⟨u, hvu, hwu⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- For a regular C4-free graph, the missing common neighbor graph is regular
    with degree equal to the excess over d(d-1)+1 vertices. -/
private theorem degree_missingCommonGraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel (missingCommonGraph G).Adj]
    (hG : ¬ (cycleGraph 4).IsContained G) {d : ℕ} (hd : G.IsRegularOfDegree d) (v : V) :
    (missingCommonGraph G).degree v = Fintype.card V - 1 - d * (d - 1) := by
  classical
  have hs : (missingCommonGraph G).neighborFinset v = univ.erase v \ twoStepEndpoints G v := by
    ext w
    simp only [mem_neighborFinset, mem_sdiff, mem_erase, mem_univ, and_true, mem_twoStepEndpoints]
    change (v ≠ w ∧ ¬ ∃ u, G.Adj v u ∧ G.Adj w u) ↔ _
    rw [ne_comm (a := v)]
    exact ⟨fun ⟨hne, hn⟩ => ⟨hne, fun hh => hn hh.2⟩,
      fun ⟨hne, hn⟩ => ⟨hne, fun hh => hn ⟨hne, hh⟩⟩⟩
  rw [← card_neighborFinset_eq_degree, hs, card_sdiff_of_subset (twoStepEndpoints_subset G v),
    card_twoStepEndpoints G hG]
  change (∀ w, G.degree w = d) at hd
  simp [hd]

private theorem common_neighbor_unique {V : Type*} (G : SimpleGraph V)
    (hG : ¬ (cycleGraph 4).IsContained G) {u v x y : V} (huv : u ≠ v)
    (hux : G.Adj u x) (hvx : G.Adj v x) (huy : G.Adj u y) (hvy : G.Adj v y) : x = y := by
  by_contra hxy
  exact hG (cycle_of_walks G huv hxy hux hvx.symm huy hvy.symm)

private theorem missingCommonGraph_commute {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel (missingCommonGraph G).Adj]
    (hG : ¬ (cycleGraph 4).IsContained G) {d : ℕ} (hd : G.IsRegularOfDegree d) :
    G.adjMatrix ℤ * (missingCommonGraph G).adjMatrix ℤ =
      (missingCommonGraph G).adjMatrix ℤ * G.adjMatrix ℤ := by
  classical
  change (∀ v, G.degree v = d) at hd
  let A := G.adjMatrix ℤ
  let B := (missingCommonGraph G).adjMatrix ℤ
  let D := Matrix.diagonal fun _ : V => (d : ℤ) - 1
  let J : Matrix V V ℤ := Matrix.of fun _ _ => 1
  change A * B = B * A
  have hB : B = D + J - A * A := by
    ext v w
    change B v w = D v w + 1 - (A * A) v w
    by_cases hvw : v = w
    · subst w
      change B v v = D v v + 1 - (G.adjMatrix ℤ * G.adjMatrix ℤ) v v
      rw [adjMatrix_mul_self_apply_self]
      simp [B, D, adjMatrix_apply, hd]
    · have hcommon : (A * A) v w =
          ((G.neighborFinset v).filter fun u => G.Adj w u).card := by
        change (G.adjMatrix ℤ * G.adjMatrix ℤ) v w = _
        rw [adjMatrix_mul_apply]
        simp only [adjMatrix_apply, G.adj_comm (v := w)]
        rw [← sum_filter]
        simp
      have hD : D v w = 0 := Matrix.diagonal_apply_ne _ hvw
      rw [hcommon, hD]
      by_cases h : ∃ u, G.Adj v u ∧ G.Adj w u
      · obtain ⟨u, hvu, hwu⟩ := h
        have hf : ((G.neighborFinset v).filter fun z => G.Adj w z) = {u} := by
          ext z
          simp only [mem_filter, mem_neighborFinset, mem_singleton]
          exact ⟨fun hz => common_neighbor_unique G hG hvw hz.1 hz.2 hvu hwu,
            fun hz => hz.symm ▸ ⟨hvu, hwu⟩⟩
        have hm : ¬ (missingCommonGraph G).Adj v w := fun hh => hh.2 ⟨u, hvu, hwu⟩
        simp [B, adjMatrix_apply, hm, hf]
      · have hf : ((G.neighborFinset v).filter fun z => G.Adj w z) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro z hz
          simp only [mem_filter, mem_neighborFinset] at hz
          exact h ⟨z, hz.1, hz.2⟩
        have hm : (missingCommonGraph G).Adj v w := ⟨hvw, h⟩
        simp [B, adjMatrix_apply, hm, hf]
  have hD : A * D = D * A := by
    ext v w
    simp [D, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  have hJ : A * J = J * A := by
    ext v w
    simp [A, J, adjMatrix_mul_apply, mul_adjMatrix_apply, hd]
  rw [hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, hD, hJ, Matrix.mul_assoc]

/-- If the degree is odd and there is exactly one other vertex with no common
    neighbor, that vertex is adjacent. -/
private theorem adjacent_to_unique_missing {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ¬ (cycleGraph 4).IsContained G)
    {v p : V} (hodd : Odd (G.degree v)) (hp : ∀ w, (missingCommonGraph G).Adj v w ↔ w = p) :
    G.Adj v p := by
  classical
  by_contra hvp
  let T := G.comap (Subtype.val : G.neighborFinset v → V)
  have hreg (x : G.neighborFinset v) : T.degree x = 1 := by
    have hvx : G.Adj v x.val := (G.mem_neighborFinset _ _).mp x.property
    have hdiff : v ≠ x.val := hvx.ne
    have hn : ¬ (missingCommonGraph G).Adj v x.val := by
      rw [hp]
      exact fun hx => hvp (hx ▸ hvx)
    have hh : ∃ u, G.Adj v u ∧ G.Adj x.val u := by
      by_contra hh
      exact hn ⟨hdiff, hh⟩
    obtain ⟨u, hvu, hxu⟩ := hh
    let y : G.neighborFinset v := ⟨u, (G.mem_neighborFinset _ _).mpr hvu⟩
    rw [← card_neighborFinset_eq_degree, card_eq_one]
    refine ⟨y, ?_⟩
    ext z
    simp only [mem_neighborFinset, mem_singleton]
    change G.Adj x.val z.val ↔ z = y
    refine ⟨fun hxz => Subtype.ext ?_, fun hzy => hzy.symm ▸ hxu⟩
    exact common_neighbor_unique G hG hdiff ((G.mem_neighborFinset _ _).mp z.property) hxz hvu hxu
  have hsum := T.sum_degrees_eq_twice_card_edges
  simp only [hreg, sum_const, card_univ, smul_eq_mul, mul_one,
    Fintype.card_coe, card_neighborFinset_eq_degree] at hsum
  exact (Nat.not_even_iff_odd.mpr hodd) ⟨T.edgeFinset.card, by omega⟩

/-- In a regular C4-free graph of order d(d-1)+2, odd degree forces d ≤ 1. -/
theorem odd_degree_le_one_of_excess_one {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ¬ (cycleGraph 4).IsContained G)
    {d : ℕ} (hd : G.IsRegularOfDegree d) (hodd : Odd d)
    (hm : Fintype.card V = d * (d - 1) + 2) : d ≤ 1 := by
  classical
  let H := missingCommonGraph G
  have hsingle (v : V) : ∃ p, H.neighborFinset v = {p} := by
    refine card_eq_one.mp ?_
    rw [card_neighborFinset_eq_degree, degree_missingCommonGraph G hG hd, hm]
    omega
  choose p hp using hsingle
  have hAdj (v w : V) : H.Adj v w ↔ w = p v := by
    rw [← mem_neighborFinset, hp, mem_singleton]
  have hpartner (v : V) : H.Adj v (p v) := (hAdj ..).mpr rfl
  have hinv (v : V) : p (p v) = v := ((hAdj ..).mp (hpartner v).symm).symm
  have hedge (v : V) : G.Adj v (p v) := adjacent_to_unique_missing G hG (by rw [hd v]; exact hodd) (hAdj v)
  have hauto (v w : V) (hvw : G.Adj v w) : G.Adj (p v) (p w) := by
    have hc := congrArg (fun M : Matrix V V ℤ => M v (p w)) (missingCommonGraph_commute G hG hd)
    change (G.adjMatrix ℤ * H.adjMatrix ℤ) v (p w) = (H.adjMatrix ℤ * G.adjMatrix ℤ) v (p w) at hc
    rw [mul_adjMatrix_apply, adjMatrix_mul_apply, hp, hp, sum_singleton, sum_singleton, hinv] at hc
    simpa [adjMatrix_apply, hvw] using hc.symm
  obtain ⟨v⟩ := ‹Nonempty V›
  have hv (w : V) : G.Adj v w → w = p v := by
    intro hvw
    by_contra hwp
    have hmid : w ≠ p v := hwp
    have hend : v ≠ p w := fun h => hwp (by rw [h, hinv])
    exact hG (cycle_of_walks G hend hmid hvw (hedge w) (hedge v) (hauto v w hvw))
  have hf : G.neighborFinset v = {p v} := by
    ext w
    simp only [mem_neighborFinset, mem_singleton]
    exact ⟨hv w, fun h => h.symm ▸ hedge v⟩
  have hdeg : G.degree v = 1 := by rw [← card_neighborFinset_eq_degree, hf, card_singleton]
  rw [hd v] at hdeg
  omega

/-- At excess one, the perfect matching of vertex pairs with no common neighbor
    rules out an odd-regular counterexample. -/
theorem ramsey_le_add_of_excess_one {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin ((k - 1)^2 + 1))) ≤
      (k - 1)^2 + 1 + k := by
  classical
  by_contra! h
  let n := (k - 1)^2 + 1
  change n + k < graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) at h
  obtain ⟨G, hG, hdeg⟩ := (lt_ramsey_iff_exists_min_degree (n + k) n).mp h
  have hk1 : k - 1 + 1 = k := by omega
  have horder : (n + k) - 1 < (k + 1) * (k - 1) := by
    have hm : (k + 1) * (k - 1) = (k - 1)^2 + 2 * (k - 1) := by nlinarith
    dsimp [n]
    rw [hm]
    omega
  have hreg : G.IsRegularOfDegree k :=
    regular_of_small_order G hG (fun w => by simpa using hdeg w) (by simpa using horder)
  have hm : Fintype.card (Fin (n + k)) = k * (k - 1) + 2 := by
    simp only [Fintype.card_fin, n]
    nlinarith
  have : Nonempty (Fin (n + k)) := ⟨⟨0, by omega⟩⟩
  have := odd_degree_le_one_of_excess_one G hG hreg hk hm
  omega

end OMA.CycleStar

noncomputable def OMA.answer : ℕ → ℕ := sorry

theorem OMA.solution : Erdos552.erdos_552.parts.i.answer = OMA.answer → type_of% @Erdos552.erdos_552.parts.i := by
  intro h
  rw [h]
  sorry

