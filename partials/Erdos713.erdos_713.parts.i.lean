import FormalConjectures.ErdosProblems.«713»
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Analysis.Subadditive
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Combinatorics.Hall.Finite

-- Problem: Erdős Problem 713 — i
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/713.lean:49 (declaration Erdos713.erdos_713.parts.i)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Bounds on the extremal function and its possible power exponents. -/

open Filter SimpleGraph Finset
open scoped Classical Topology Sym2

private lemma contained_in_balanced_bipartite {q : ℕ} (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) : G ⊑ completeBipartiteGraph (Fin q) (Fin q) := by
  obtain ⟨c⟩ := bip
  let f : Fin q → Fin q ⊕ Fin q := fun v => if c v = 0 then .inl v else .inr v
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro v w h
    have hc := c.valid h
    by_cases hv : c v = 0 <;> by_cases hw : c w = 0
    · exact (hc (hv.trans hw.symm)).elim
    · simp [f, hv, hw]
    · simp [f, hv, hw]
    · have hv' : c v = 1 := by exact Fin.eq_one_of_ne_zero _ hv
      have hw' : c w = 1 := by exact Fin.eq_one_of_ne_zero _ hw
      exact (hc (hv'.trans hw'.symm)).elim
  · intro v w h
    change f v = f w at h
    have hf (u) : Sum.elim id id (f u) = u := by
      by_cases hu : c u = 0 <;> simp [f, hu]
    simpa only [hf] using congrArg (Sum.elim id id) h

-- Count pairs of a vertex and an ordered tuple of distinct neighbors.
private lemma rectangular_degree_count {s t n : ℕ} (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin s) (Fin t)).Free X) :
    (∑ v : Fin n, (X.degree v).descFactorial s) ≤ n ^ s * (t - 1) := by
  let R (v : Fin n) (f : Fin s ↪ Fin n) : Prop := ∀ i, X.Adj v (f i)
  have hrow (v : Fin n) :
      (univ.bipartiteAbove R v).card = (X.degree v).descFactorial s := by
    let e : (univ.bipartiteAbove R v) ≃ (Fin s ↪ X.neighborFinset v) :=
      { toFun := fun f =>
          ⟨fun i => ⟨f.val i, (mem_neighborFinset X v _).mpr (((mem_bipartiteAbove R).mp f.property).2 i)⟩,
            fun _ _ h => f.val.injective (congrArg Subtype.val h)⟩
        invFun := fun f =>
          ⟨f.trans (Function.Embedding.subtype _),
            (mem_bipartiteAbove R).mpr ⟨mem_univ _, fun i => (mem_neighborFinset X v _).mp (f i).property⟩⟩
        left_inv := fun f => Subtype.ext (Function.Embedding.ext fun _ => rfl)
        right_inv := fun f => Function.Embedding.ext fun _ => rfl }
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_fin]
    rw [Fintype.card_coe, card_neighborFinset_eq_degree]
  have hcol (f : Fin s ↪ Fin n) : (univ.bipartiteBelow R f).card ≤ t - 1 := by
    have hlt : (univ.bipartiteBelow R f).card < t := by
      by_contra! hlarge
      obtain ⟨U, hU, hcard⟩ := exists_subset_card_eq hlarge
      apply free
      apply completeBipartiteGraph_isContained_iff.mpr
      refine ⟨univ.map f, U, by simp, by simpa using hcard, ?_⟩
      intro a ha b hb
      obtain ⟨i, -, rfl⟩ := mem_map.mp (mem_coe.mp ha)
      exact (((mem_bipartiteBelow R).mp (hU (mem_coe.mp hb))).2 i).symm
    omega
  calc
    _ = ∑ v : Fin n, (univ.bipartiteAbove R v).card := by simp only [hrow]
    _ = ∑ f : Fin s ↪ Fin n, (univ.bipartiteBelow R f).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ ≤ ∑ _ : Fin s ↪ Fin n, (t - 1) := sum_le_sum (fun f _ => hcol f)
    _ = n.descFactorial s * (t - 1) := by
      simp [Fintype.card_embedding_eq]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow n s)

private lemma balanced_degree_count {q n : ℕ} (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin q) (Fin q)).Free X) :
    (∑ v : Fin n, (X.degree v).descFactorial q) ≤ n ^ q * (q - 1) :=
  rectangular_degree_count X free

private lemma rectangular_edge_bound {s t n : ℕ} (hs : 0 < s) (hn : 0 < n)
    (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin s) (Fin t)).Free X) {C : ℝ}
    (hC : 0 ≤ C) (ht : ((t - 1 : ℕ) : ℝ) ≤ C ^ s) :
    2 * (X.edgeFinset.card : ℝ) ≤
      C * (n : ℝ) ^ (2 - 1 / (s : ℝ)) + (s - 1 : ℕ) * (n : ℝ) := by
  have npos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let d (v : Fin n) := X.degree v + 1 - s
  have hcount : (∑ v : Fin n, (d v : ℝ) ^ s) ≤ (n : ℝ) ^ s * (t - 1 : ℕ) := by
    exact_mod_cast (sum_le_sum (fun v _ => Nat.pow_sub_le_descFactorial (X.degree v) s)).trans
      (rectangular_degree_count X free)
  let m : ℝ := (∑ v : Fin n, (d v : ℝ)) / n
  have hjensen : m ^ s ≤ (∑ v : Fin n, (d v : ℝ) ^ s) / n := by
    have hw : (∑ _ : Fin n, (1 / (n : ℝ))) = 1 := by simp [npos.ne']
    simp only [m, div_eq_inv_mul]
    simpa only [one_div, ← Finset.mul_sum] using
      Real.pow_arith_mean_le_arith_mean_pow univ (fun _ : Fin n => 1 / (n : ℝ))
        (fun v => (d v : ℝ)) (fun _ _ => by positivity) hw (fun _ _ => by positivity) s
  let β : ℝ := 1 - 1 / (s : ℝ)
  have hpowers : ((n : ℝ) ^ β) ^ s = (n : ℝ) ^ s / n := by
    have cs : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
    rw [← Real.rpow_natCast ((n : ℝ) ^ β) s, ← Real.rpow_mul npos.le]
    dsimp only [β]
    rw [sub_mul, one_mul, div_mul_cancel₀ _ cs, Real.rpow_sub npos, Real.rpow_natCast,
      Real.rpow_one]
  have havg : m ≤ C * (n : ℝ) ^ β := by
    apply le_of_pow_le_pow_left₀ hs.ne' (by positivity)
    calc
      m ^ s ≤ ((n : ℝ) ^ s * (t - 1 : ℕ)) / n :=
        hjensen.trans (div_le_div_of_nonneg_right hcount npos.le)
      _ = (t - 1 : ℕ) * ((n : ℝ) ^ s / n) := by ring
      _ ≤ (C * (n : ℝ) ^ β) ^ s := by
        rw [mul_pow, hpowers]
        exact mul_le_mul_of_nonneg_right ht (by positivity)
  have hdeg : (∑ v : Fin n, (X.degree v : ℝ)) ≤ n * m + (s - 1 : ℕ) * (n : ℝ) := by
    calc
      _ ≤ ∑ v : Fin n, ((d v : ℝ) + (s - 1 : ℕ)) := by
        apply sum_le_sum
        intro v _
        exact_mod_cast (show X.degree v ≤ d v + (s - 1) by dsimp [d]; omega)
      _ = _ := by
        simp only [m, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hhand : (∑ v : Fin n, (X.degree v : ℝ)) = 2 * X.edgeFinset.card := by
    exact_mod_cast X.sum_degrees_eq_twice_card_edges
  have hpow : (n : ℝ) * (C * (n : ℝ) ^ β) = C * (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
    rw [show (2 : ℝ) - 1 / s = 1 + β by dsimp [β]; ring, Real.rpow_add npos, Real.rpow_one]
    ring
  rw [← hhand, ← hpow]
  exact hdeg.trans (add_le_add (mul_le_mul_of_nonneg_left havg npos.le) le_rfl)

private lemma balanced_edge_bound {q n : ℕ} (hq : 0 < q) (hn : 0 < n)
    (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin q) (Fin q)).Free X) :
    (X.edgeFinset.card : ℝ) ≤ q * (n : ℝ) ^ (2 - 1 / (q : ℝ)) := by
  have npos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have qpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpow : (((q - 1 : ℕ) : ℝ)) ≤ (q : ℝ) ^ q :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (le_self_pow₀ hq1 hq.ne')
  have hbound := rectangular_edge_bound hq hn X free qpos.le hqpow
  let β : ℝ := 1 - 1 / (q : ℝ)
  have hβ : 0 ≤ β := sub_nonneg.mpr ((div_le_one qpos).mpr hq1)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase := Real.one_le_rpow hn1 hβ
  have hsingle : ((q - 1 : ℕ) : ℝ) * n ≤ (q : ℝ) * (n : ℝ) ^ (2 - 1 / (q : ℝ)) := by
    rw [show (2 : ℝ) - 1 / q = 1 + β by dsimp [β]; ring, Real.rpow_add npos, Real.rpow_one,
      ← mul_assoc]
    calc
      _ ≤ (q : ℝ) * n := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ _)) (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hbase
  linarith

private lemma bipartite_extremal_upper {q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) {n : ℕ} (hn : 0 < n) :
    (extremalNumber n G : ℝ) ≤ (q : ℝ) * (n : ℝ) ^ (2 - 1 / (q : ℝ)) := by
  have hcard := contained_in_balanced_bipartite G bip
  have hmono : extremalNumber n G ≤ extremalNumber n (completeBipartiteGraph (Fin q) (Fin q)) :=
    hcard.extremalNumber_le
  apply (Nat.cast_le.mpr hmono).trans
  rw [← Fintype.card_fin n, extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro X _ hfree
  rw [Fintype.card_fin]
  exact balanced_edge_bound hq hn X hfree

private lemma exponent_le_bipartite_bound {q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) {α c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α)
      atTop (𝓝 c)) :
    α ≤ 2 - 1 / (q : ℝ) := by
  by_contra! hα
  let β : ℝ := 2 - 1 / (q : ℝ)
  have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - α)) atTop (𝓝 0) := by
    rw [← neg_sub]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => (q : ℝ) * (n : ℝ) ^ (β - α)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpower.const_mul (q : ℝ)
  have hle : c ≤ 0 := le_of_tendsto_of_tendsto hlim hzero (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [Real.rpow_sub hnpos, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (bipartite_extremal_upper hq G bip (by omega)) (by positivity))
  exact hc.not_ge hle

private def consecutive_matching (n : ℕ) : SimpleGraph (Fin n) where
  Adj v w := v.val / 2 = w.val / 2 ∧ v ≠ w
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.2 rfl

private lemma consecutive_matching_degree (n : ℕ) (v : Fin n) :
    (consecutive_matching n).degree v ≤ 1 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_le_one]
  intro a ha b hb
  have ha' : v.val / 2 = a.val / 2 ∧ v ≠ a := (mem_neighborFinset _ _ _).mp ha
  have hb' : v.val / 2 = b.val / 2 ∧ v ≠ b := (mem_neighborFinset _ _ _).mp hb
  have hna : v.val ≠ a.val := fun h => ha'.2 (Fin.ext h)
  have hnb : v.val ≠ b.val := fun h => hb'.2 (Fin.ext h)
  apply Fin.ext
  omega

private lemma consecutive_matching_edges (n : ℕ) :
    n / 2 ≤ (consecutive_matching n).edgeFinset.card := by
  let a (i : Fin (n / 2)) : Fin n := ⟨2 * i.val, by have hi := i.isLt; omega⟩
  let b (i : Fin (n / 2)) : Fin n := ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩
  have h (i) : s(a i, b i) ∈ (consecutive_matching n).edgeFinset := by
    rw [mem_edgeFinset, mem_edgeSet]
    change (2 * i.val) / 2 = (2 * i.val + 1) / 2 ∧ a i ≠ b i
    refine ⟨by omega, ?_⟩
    intro heq
    have eq := congrArg Fin.val heq
    change 2 * i.val = 2 * i.val + 1 at eq
    omega
  let f (i : Fin (n / 2)) : (consecutive_matching n).edgeFinset := ⟨_, h i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have eq : s(a i, b i) = s(a j, b j) := congrArg Subtype.val hij
    rcases Sym2.eq_iff.mp eq with ⟨heq, _⟩ | ⟨heq, _⟩
    · have hval := congrArg Fin.val heq
      change 2 * i.val = 2 * j.val at hval
      exact Fin.ext (by omega)
    · have hval := congrArg Fin.val heq
      change 2 * i.val = 2 * j.val + 1 at hval
      omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

private lemma star_free_of_degree_le_one {q n : ℕ} (G : SimpleGraph (Fin q))
    (edges : 2 ≤ G.edgeFinset.card) (degree : ∀ v, G.degree v ≤ 1) (r : Fin n) :
    G.Free (starGraph r) := by
  rintro ⟨f⟩
  have hcenter (v w : Fin q) (h : G.Adj v w) : f v = r ∨ f w = r :=
    (starGraph_adj.mp (f.toHom.map_adj h)).2
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < G.edgeFinset.card)
  obtain ⟨u, hu⟩ : ∃ u, f u = r := by
    induction e using Sym2.inductionOn with
    | _ v w =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      exact (hcenter v w he).elim (fun h => ⟨v, h⟩) (fun h => ⟨w, h⟩)
  have hsub : G.edgeFinset ⊆ G.incidenceFinset u := by
    intro e he
    rw [incidenceFinset_eq_filter, mem_filter]
    refine ⟨he, ?_⟩
    induction e using Sym2.inductionOn with
    | _ v w =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rcases hcenter v w he with hv | hw
      · have hv' : v = u := f.injective (hv.trans hu.symm)
        simp [hv']
      · have hw' : w = u := f.injective (hw.trans hu.symm)
        simp [hw']
  have hle := Finset.card_le_card hsub
  rw [card_incidenceFinset_eq_degree] at hle
  have hdegree := degree u
  omega

private lemma extremal_linear_lower {q n : ℕ} (G : SimpleGraph (Fin q))
    (edges : 2 ≤ G.edgeFinset.card) (hn : 0 < n) : n / 2 ≤ extremalNumber n G := by
  by_cases h : ∀ v, G.degree v ≤ 1
  · let r : Fin n := ⟨0, hn⟩
    have hfree := star_free_of_degree_le_one G edges h r
    have hdegree := (starGraph r).card_incidenceFinset_eq_degree r
    have hcard : n - 1 ≤ (starGraph r).edgeFinset.card := by
      rw [degree_starGraph_center, Fintype.card_fin] at hdegree
      rw [← hdegree]
      exact Finset.card_le_card (by
        rw [incidenceFinset_eq_filter]
        exact filter_subset _ _)
    have hex := card_edgeFinset_le_extremalNumber hfree
    rw [Fintype.card_fin] at hex
    exact (by omega : n / 2 ≤ n - 1).trans (hcard.trans hex)
  · obtain ⟨v, hv⟩ := not_forall.mp h
    have hfree : G.Free (consecutive_matching n) := by
      rintro ⟨f⟩
      exact hv ((f.degree_le v).trans (consecutive_matching_degree n (f v)))
    have hex := card_edgeFinset_le_extremalNumber hfree
    rw [Fintype.card_fin] at hex
    exact (consecutive_matching_edges n).trans hex

private lemma exponent_ge_one {q : ℕ} (G : SimpleGraph (Fin q))
    (edges : 2 ≤ G.edgeFinset.card) {α c : ℝ}
    (hlim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α)
      atTop (𝓝 c)) : 1 ≤ α := by
  by_contra! hα
  have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    rw [← neg_sub]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop (𝓝 0) := by
    have hmul := hlim.mul hpower
    rw [mul_zero] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [Real.rpow_sub hnpos, Real.rpow_one, div_mul_div_comm,
      div_eq_div_iff (by positivity) hnpos.ne']
    ring
  have hle : (1 / 3 : ℝ) ≤ 0 := ge_of_tendsto hzero (by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [le_div_iff₀ hnpos]
    have hnat : n ≤ 3 * extremalNumber n G :=
      (show n ≤ 3 * (n / 2) by omega).trans
        (Nat.mul_le_mul_left 3 (extremal_linear_lower G edges (by omega)))
    have hreal : (n : ℝ) ≤ 3 * (extremalNumber n G : ℝ) := by exact_mod_cast hnat
    linarith)
  norm_num at hle

private lemma connected_copy_from_left {V W Z : Type*} {G : SimpleGraph V}
    {A : SimpleGraph W} {B : SimpleGraph Z} (conn : G.Connected)
    (f : Copy G (A ⊕g B)) {u : V} {a : W} (hu : f u = Sum.inl a) : G ⊑ A := by
  let g (v : V) : W := Sum.elim id (fun _ => a) (f v)
  have hg (v : V) : f v = Sum.inl (g v) := by
    cases hv : f v with
    | inl w => simp [g, hv]
    | inr z =>
      have hpath := (conn u v).map f.toHom
      change (A ⊕g B).Reachable (f u) (f v) at hpath
      rw [hu, hv] at hpath
      exact (not_reachable_sum_inl_inr a z hpath).elim
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro v w adj
    have h := f.toHom.map_adj adj
    change (A ⊕g B).Adj (f v) (f w) at h
    rw [hg v, hg w] at h
    exact sum_adj_inl.mp h
  · intro v w eq
    change g v = g w at eq
    apply f.injective
    change f v = f w
    rw [hg v, hg w, eq]

private lemma connected_free_sum {V W Z : Type*} {G : SimpleGraph V}
    {A : SimpleGraph W} {B : SimpleGraph Z} (conn : G.Connected)
    (freeA : G.Free A) (freeB : G.Free B) : G.Free (A ⊕g B) := by
  rintro ⟨f⟩
  obtain ⟨u⟩ := conn.nonempty
  cases hu : f u with
  | inl a => exact freeA (connected_copy_from_left conn f hu)
  | inr b =>
    apply freeB (connected_copy_from_left conn (Iso.sumComm.toCopy.comp f) (u := u) (a := b) ?_)
    change Sum.swap (f u) = Sum.inl b
    rw [hu]
    rfl

private lemma connected_extremal_superadditive {q : ℕ} (G : SimpleGraph (Fin q))
    (conn : G.Connected) (edges : 2 ≤ G.edgeFinset.card) (m n : ℕ) :
    extremalNumber m G + extremalNumber n G ≤ extremalNumber (m + n) G := by
  have hG : G ≠ ⊥ := by
    intro heq
    rw [edgeFinset_eq_empty.mpr heq] at edges
    simp at edges
  obtain ⟨A, hAd, hA⟩ := exists_isExtremal_free (V := Fin m) hG
  obtain ⟨B, hBd, hB⟩ := exists_isExtremal_free (V := Fin n) hG
  let _ := hAd
  let _ := hBd
  calc
    extremalNumber m G + extremalNumber n G = A.edgeFinset.card + B.edgeFinset.card := by
      rw [card_edgeFinset_of_isExtremal_free hA, card_edgeFinset_of_isExtremal_free hB,
        Fintype.card_fin, Fintype.card_fin]
    _ = (A ⊕g B).edgeFinset.card := by
      rw [edgeFinset_card, edgeFinset_card, edgeFinset_card,
        Fintype.card_congr (edgeSetSumEquiv (G := A) (H := B)), Fintype.card_sum]
    _ ≤ _ := by
      simpa only [Fintype.card_sum, Fintype.card_fin] using
        card_edgeFinset_le_extremalNumber (connected_free_sum conn hA.prop hB.prop)

private lemma connected_density_alternative {q : ℕ} (G : SimpleGraph (Fin q))
    (conn : G.Connected) (edges : 2 ≤ G.edgeFinset.card) :
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop (𝓝 c)) ∨
      Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop atTop := by
  let u (n : ℕ) : ℝ := -(extremalNumber n G : ℝ)
  have hadd : Subadditive u := by
    intro m n
    have h : (extremalNumber m G : ℝ) + extremalNumber n G ≤ extremalNumber (m + n) G :=
      by exact_mod_cast connected_extremal_superadditive G conn edges m n
    dsimp [u]
    linarith
  by_cases hb : BddBelow (Set.range fun n : ℕ => u n / n)
  · left
    have h2 := hadd.lim_le_div hb (by decide : (2 : ℕ) ≠ 0)
    have hlo := extremal_linear_lower G edges (by decide : 0 < (2 : ℕ))
    have hlo' : (1 : ℝ) ≤ extremalNumber 2 G := by exact_mod_cast hlo
    norm_num [u] at h2
    refine ⟨-hadd.lim, by linarith, ?_⟩
    simpa only [u, neg_div, neg_neg] using (hadd.tendsto_lim hb).neg
  · right
    apply tendsto_atTop.mpr
    intro M
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := not_bddBelow_iff.mp hb (min 0 (-M) - 1)
    have ht : min 0 (-M) - 1 < 0 := by linarith [min_le_left (0 : ℝ) (-M)]
    have hne : k ≠ 0 := by
      rintro rfl
      simp only [Nat.cast_zero, div_zero] at hk
      linarith
    filter_upwards [hadd.eventually_div_lt_of_div_lt hne hk] with n hn
    simp only [u, neg_div] at hn
    linarith [min_le_right (0 : ℝ) (-M)]

private lemma tree_copies_into_high_degree {V W : Type} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (tree : T.IsTree) (X : SimpleGraph W) [DecidableRel X.Adj]
    (w : W) (degree : ∀ x, Fintype.card V ≤ X.degree x) : T ⊑ X := by
  have aux (k : ℕ) : ∀ (U : Type) [Fintype U], Fintype.card U = k →
      ∀ (S : SimpleGraph U), S.IsTree → (∀ x, k ≤ X.degree x) → S ⊑ X := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro U _ hU S hS hdeg
      rcases subsingleton_or_nontrivial U with hs | hs
      · exact ⟨⟨⟨fun _ => w, fun h => (h.ne (Subsingleton.elim _ _)).elim⟩,
          fun _ _ _ => Subsingleton.elim _ _⟩⟩
      let _ := hs
      obtain ⟨leaf, hleaf⟩ := hS.exists_vert_degree_one_of_nontrivial
      obtain ⟨parent, hparent, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hleaf
      let V' := ({leaf}ᶜ : Set U)
      let S' := S.induce V'
      have htree' : S'.IsTree := ⟨hS.connected.induce_compl_singleton_of_degree_eq_one hleaf,
        hS.isAcyclic.induce V'⟩
      have hcard : Fintype.card V' < k := by
        rw [← hU]
        exact Fintype.card_lt_of_injective_of_notMem (f := fun x : V' => x.val)
          Subtype.val_injective (b := leaf) (by simp [V'])
      obtain ⟨f⟩ := ih (Fintype.card V') hcard V' rfl S' htree'
        (fun x => hcard.le.trans (hdeg x))
      let p : V' := ⟨parent, hparent.ne.symm⟩
      let used := (univ : Finset V').map f.toEmbedding
      have hfresh : ∃ y ∈ X.neighborFinset (f p), y ∉ used := by
        by_contra! h
        have hc := Finset.card_le_card (show X.neighborFinset (f p) ⊆ used from h)
        rw [card_neighborFinset_eq_degree] at hc
        have hused : used.card = Fintype.card V' := by simp [used]
        exact hcard.not_ge ((hdeg (f p)).trans (hc.trans_eq hused))
      obtain ⟨y, hy, hynew⟩ := hfresh
      have hy' := (mem_neighborFinset X (f p) y).mp hy
      let g (v : U) : W := if h : v = leaf then y else f ⟨v, h⟩
      have g_eq (v : U) (hv : v ≠ leaf) : g v = f ⟨v, hv⟩ := by
        simp [g, hv]
      have g_leaf : g leaf = y := by simp [g]
      have g_used (v : U) (hv : v ≠ leaf) : g v ∈ used := by
        rw [g_eq v hv]
        exact mem_map.mpr ⟨⟨v, hv⟩, mem_univ _, rfl⟩
      have hleaf_adj (v : U) (hv : S.Adj leaf v) : X.Adj (g leaf) (g v) := by
        have hv' : v = parent := hu v hv
        subst v
        rw [g_leaf, g_eq parent hparent.ne.symm]
        exact hy'.symm
      refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
      · intro v u adj
        rcases eq_or_ne v leaf with rfl | hv
        · exact hleaf_adj u adj
        rcases eq_or_ne u leaf with rfl | hu'
        · exact (hleaf_adj v adj.symm).symm
        rw [g_eq v hv, g_eq u hu']
        exact f.toHom.map_adj (show S'.Adj ⟨v, hv⟩ ⟨u, hu'⟩ from adj)
      · intro v u eq
        change g v = g u at eq
        rcases eq_or_ne v leaf with rfl | hv
        · by_contra hu'
          rw [g_leaf] at eq
          exact hynew (eq ▸ g_used u (fun h => hu' h.symm))
        rcases eq_or_ne u leaf with rfl | hu'
        · rw [g_leaf] at eq
          exact (hynew (eq ▸ g_used v hv)).elim
        rw [g_eq v hv, g_eq u hu'] at eq
        exact congrArg Subtype.val (f.injective eq)
  exact aux (Fintype.card V) V rfl T tree degree

private lemma forest_extremal_upper {q : ℕ} (G : SimpleGraph (Fin q))
    (forest : G.IsAcyclic) (n : ℕ) : extremalNumber n G ≤ q * n := by
  induction n with
  | zero =>
    rw [← Fintype.card_fin 0, extremalNumber_le_iff (V := Fin 0)]
    intro X _ _
    have bound := X.card_edgeFinset_le_card_choose_two
    simpa using bound
  | succ n ih =>
    rw [← Fintype.card_fin (n+1), extremalNumber_le_iff (V := Fin (n+1))]
    intro X _ free
    by_cases h : ∃ x, X.degree x < q
    · obtain ⟨x, hx⟩ := h
      have hdel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber free x
      rw [card_edgeFinset_deleteIncidenceSet, Fintype.card_fin, Nat.add_sub_cancel] at hdel
      rw [Fintype.card_fin, Nat.mul_succ]
      omega
    · have hdeg (x) : q ≤ X.degree x := Nat.le_of_not_gt (fun hx => h ⟨x, hx⟩)
      have nonempty : Nonempty (Fin q) := by
        by_contra! hempty
        have hbot : G = ⊥ := by ext v; exact (hempty.false v).elim
        exact free (by rw [hbot, bot_isContained_iff_card_le]; simp)
      obtain ⟨T, hGT, _, ht⟩ := (connected_top (V := Fin q)).exists_isTree_le_of_le_of_isAcyclic
        (show G ≤ ⊤ from le_top) forest
      have hc := tree_copies_into_high_degree T ht X (0 : Fin (n+1)) (by simpa using hdeg)
      exact (free ((IsContained.of_le hGT).trans hc)).elim

private lemma contained_iff_contained_support {q n : ℕ} (G : SimpleGraph (Fin q))
    (X : SimpleGraph (Fin n)) (hn : q ≤ n) :
    G ⊑ X ↔ (G.induce G.support) ⊑ X := by
  constructor
  · exact fun h => (Copy.induce G G.support).isContained.trans h
  · rintro ⟨f⟩
    let image : Set (Fin n) := Set.range f.toEmbedding
    have himage : Fintype.card image = Fintype.card G.support :=
      Fintype.card_range f.toEmbedding
    have hcard : Fintype.card (↑G.supportᶜ : Type) ≤ Fintype.card (↑imageᶜ : Type) := by
      simpa only [Fintype.card_compl_set, Fintype.card_fin, himage] using
        Nat.sub_le_sub_right hn (Fintype.card G.support)
    let e : (↑G.supportᶜ : Type) ↪ (↑imageᶜ : Type) :=
      (Function.Embedding.nonempty_of_card_le hcard).some
    let g (v : Fin q) : Fin n :=
      if h : v ∈ G.support then f ⟨v, h⟩ else (e ⟨v, h⟩).val
    have hg (v) (hv : v ∈ G.support) : g v = f ⟨v, hv⟩ := dif_pos hv
    have hn' (v) (hv : v ∉ G.support) : g v = (e ⟨v, hv⟩).val := dif_neg hv
    refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
    · intro v w h
      rw [hg v h.mem_support_left, hg w h.mem_support_right]
      exact f.toHom.map_adj (show (G.induce G.support).Adj
        ⟨v, h.mem_support_left⟩ ⟨w, h.mem_support_right⟩ from h)
    · intro v w heq
      change g v = g w at heq
      by_cases hv : v ∈ G.support <;> by_cases hw : w ∈ G.support
      · rw [hg v hv, hg w hw] at heq
        exact congrArg Subtype.val (f.injective heq)
      · rw [hg v hv, hn' w hw] at heq
        exact ((e ⟨w, hw⟩).property ⟨⟨v, hv⟩, heq⟩).elim
      · rw [hn' v hv, hg w hw] at heq
        exact ((e ⟨v, hv⟩).property ⟨⟨w, hw⟩, heq.symm⟩).elim
      · rw [hn' v hv, hn' w hw] at heq
        exact congrArg Subtype.val (e.injective (Subtype.ext heq))

private lemma extremal_eq_on_support {q n : ℕ} (G : SimpleGraph (Fin q)) (hn : q ≤ n) :
    extremalNumber n G = extremalNumber n (G.induce G.support) := by
  have hfree (X : SimpleGraph (Fin n)) : G.Free X ↔ (G.induce G.support).Free X :=
    not_congr (contained_iff_contained_support G X hn)
  have hx : (univ : Finset (SimpleGraph (Fin n))).filter (fun X => G.Free X) =
      univ.filter (fun X => (G.induce G.support).Free X) := by
    ext X
    simpa only [mem_filter, mem_univ, true_and] using hfree X
  unfold extremalNumber
  rw [hx]

private lemma remove_isolated_vertices {q : ℕ} (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) :
    ∃ (k : ℕ) (H : SimpleGraph (Fin k)), H.IsBipartite ∧
      H.edgeFinset.card = G.edgeFinset.card ∧ (∀ v, ¬ H.IsIsolated v) ∧
      ∀ n ≥ q, extremalNumber n G = extremalNumber n H := by
  let k := Fintype.card G.support
  let e : G.support ≃ Fin k := Fintype.equivFin _
  let H := (G.induce G.support).comap e.symm
  let iso : H ≃g G.induce G.support := ⟨e.symm, Iff.rfl⟩
  have hBip : H.IsBipartite :=
    bip.of_hom ((Embedding.induce G.support).toHom.comp iso.toHom)
  refine ⟨k, H, hBip, iso.card_edgeFinset_eq.trans card_edgeFinset_induce_support, ?_, ?_⟩
  · intro v
    rw [← mem_support_iff_not_isIsolated]
    let u := e.symm v
    obtain ⟨w, hw⟩ := (show ∃ w, G.Adj u.val w from u.property)
    let w' : G.support := ⟨w, hw.mem_support_right⟩
    change ∃ w, H.Adj v w
    refine ⟨e w', ?_⟩
    change (G.induce G.support).Adj (e.symm v) (e.symm (e w'))
    rw [e.symm_apply_apply]
    exact hw
  · intro n hn
    rw [extremal_eq_on_support G hn, extremalNumber_congr_right iso]

private def eraseVertices {W : Type*} (X : SimpleGraph W) (S : Set W) : SimpleGraph W where
  Adj x y := X.Adj x y ∧ x ∉ S ∧ y ∉ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => X.irrefl h.1⟩

private lemma card_edges_eraseVertices_le_degree_sum {W : Type*} [Fintype W]
    (X : SimpleGraph W) (T : Finset W) :
    X.edgeFinset.card ≤ (eraseVertices X (↑T : Set W)).edgeFinset.card +
      ∑ v ∈ T, X.degree v := by
  induction T using Finset.induction_on with
  | empty =>
    have heq : eraseVertices X (↑(∅ : Finset W) : Set W) = X := by
      ext a b
      simp [eraseVertices]
    rw [heq, Finset.sum_empty, Nat.add_zero]
  | @insert v T hv ih =>
    let Y := eraseVertices X (↑T : Set W)
    have heq : eraseVertices X (↑(insert v T) : Set W) = Y.deleteIncidenceSet v := by
      ext a b
      simp only [Y, eraseVertices, coe_insert, Set.mem_insert_iff, not_or, deleteIncidenceSet_adj]
      tauto
    have hdel : (Y.deleteIncidenceSet v).edgeFinset.card = Y.edgeFinset.card - Y.degree v := by
      convert! card_edgeFinset_deleteIncidenceSet Y v
    have hd : Y.degree v ≤ X.degree v := Y.degree_le_of_le (fun _ _ h => h.1)
    have hi : X.edgeFinset.card ≤ Y.edgeFinset.card + ∑ w ∈ T, X.degree w := ih
    rw [heq, Finset.sum_insert hv]
    have hf : X.edgeFinset.card ≤ (Y.deleteIncidenceSet v).edgeFinset.card +
        (X.degree v + ∑ w ∈ T, X.degree w) := by
      rw [hdel]
      omega
    convert! hf

private lemma card_edgeFinset_eraseVertices {W : Type*} [Fintype W]
    (X : SimpleGraph W) [DecidableRel X.Adj] (S : Finset W) :
    X.edgeFinset.card ≤ (eraseVertices X (↑S : Set W)).edgeFinset.card +
      S.card * Fintype.card W := by
  have hweight : (∑ v ∈ S, X.degree v) ≤ S.card * Fintype.card W := by
    calc
      _ ≤ ∑ _v ∈ S, Fintype.card W :=
        Finset.sum_le_sum (fun v _ => (X.degree_lt_card_verts v).le)
      _ = _ := by simp
  have h : X.edgeFinset.card ≤ (eraseVertices X (↑S : Set W)).edgeFinset.card +
      ∑ v ∈ S, X.degree v := by
    convert! card_edges_eraseVertices_le_degree_sum X S
  exact h.trans (Nat.add_le_add_left hweight _)

private lemma contained_of_component_bounds {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (X : SimpleGraph W) [DecidableRel X.Adj]
    (active : ∀ v, ∃ w, H.Adj v w)
    (rich : ∀ C : H.ConnectedComponent, extremalNumber (Fintype.card W) C.toSimpleGraph +
        Fintype.card V * Fintype.card W < X.edgeFinset.card) : H ⊑ X := by
  let p := H.connectedComponentMk
  let P (s : Finset H.ConnectedComponent) : Set V := {v | p v ∈ s}
  have partialCopy (s : Finset H.ConnectedComponent) : (H.induce (P s)) ⊑ X := by
    induction s using Finset.induction_on with
    | empty =>
      have empty (v : P ∅) : False := Finset.notMem_empty _ v.property
      exact ⟨⟨⟨fun v => (empty v).elim, fun {v} _ _ => (empty v).elim⟩,
        fun v _ _ => (empty v).elim⟩⟩
    | @insert C s hC ih =>
      obtain ⟨f⟩ := ih
      let used := (univ : Finset (P s)).map f.toEmbedding
      have hused : used.card ≤ Fintype.card V := by
        simpa [used] using Fintype.card_le_of_injective (fun v : P s => v.val)
          Subtype.val_injective
      have hn := card_edgeFinset_eraseVertices X used
      have hm := Nat.mul_le_mul_right (Fintype.card W) hused
      obtain ⟨g⟩ := IsContained.of_extremalNumber_lt_card_edgeFinset
        (G := eraseVertices X (↑used : Set W)) (H := C.toSimpleGraph) (by
          have h := rich C
          omega)
      have g_new (v : C.supp) : g v ∉ used := by
        obtain ⟨w, hw⟩ := active v.val
        have hcw := C.mem_supp_of_adj_mem_supp v.property hw
        have h := g.toHom.map_adj (show C.toSimpleGraph.Adj v ⟨w, hcw⟩ from hw)
        exact h.2.1
      have g_adj {v w : C.supp} (h : H.Adj v.val w.val) : X.Adj (g v) (g w) :=
        (g.toHom.map_adj (show C.toSimpleGraph.Adj v w from h)).1
      have memC (v : P (insert C s)) (hv : p v.val ∉ s) : v.val ∈ C.supp := by
        exact (mem_insert.mp v.property).resolve_right hv
      let k (v : P (insert C s)) : W :=
        if hv : p v.val ∈ s then f ⟨v.val, hv⟩ else g ⟨v.val, memC v hv⟩
      have k_old (v : P (insert C s)) (hv : p v.val ∈ s) : k v = f ⟨v.val, hv⟩ :=
        dif_pos hv
      have k_new (v : P (insert C s)) (hv : p v.val ∉ s) :
          k v = g ⟨v.val, memC v hv⟩ := dif_neg hv
      have k_used (v : P (insert C s)) (hv : p v.val ∈ s) : k v ∈ used := by
        rw [k_old v hv]
        exact mem_map.mpr ⟨⟨v.val, hv⟩, mem_univ _, rfl⟩
      refine ⟨⟨⟨k, ?_⟩, ?_⟩⟩
      · intro v w h
        change H.Adj v.val w.val at h
        have hp : p v.val = p w.val := ConnectedComponent.connectedComponentMk_eq_of_adj h
        by_cases hv : p v.val ∈ s
        · have hw : p w.val ∈ s := hp ▸ hv
          rw [k_old v hv, k_old w hw]
          exact f.toHom.map_adj (show (H.induce (P s)).Adj ⟨v.val, hv⟩
            ⟨w.val, hw⟩ from h)
        · have hw : p w.val ∉ s := hp ▸ hv
          rw [k_new v hv, k_new w hw]
          exact g_adj h
      · intro v w eq
        change k v = k w at eq
        by_cases hv : p v.val ∈ s <;> by_cases hw : p w.val ∈ s
        · rw [k_old v hv, k_old w hw] at eq
          exact Subtype.ext (congrArg (fun x : P s => x.val) (f.injective eq))
        · have hm := k_used v hv
          rw [eq, k_new w hw] at hm
          exact (g_new _ hm).elim
        · have hm := k_used w hw
          rw [← eq, k_new v hv] at hm
          exact (g_new _ hm).elim
        · rw [k_new v hv, k_new w hw] at eq
          exact Subtype.ext (congrArg (fun x : C.supp => x.val) (g.injective eq))
  let : Fintype H.ConnectedComponent :=
    Fintype.ofSurjective p (fun C => ⟨C.out, C.out_eq⟩)
  obtain ⟨f⟩ := partialCopy univ
  let incl (v : V) : P univ := ⟨v, mem_univ _⟩
  exact ⟨⟨⟨fun v => f (incl v), fun h => f.toHom.map_adj
    (show (H.induce (P univ)).Adj (incl _) (incl _) from h)⟩,
    fun _ _ h => congrArg Subtype.val (f.injective h)⟩⟩

private lemma extremal_le_component_bound {V : Type*} [Fintype V]
    (H : SimpleGraph V) (active : ∀ v, ∃ w, H.Adj v w) (n M : ℕ)
    (bound : ∀ C : H.ConnectedComponent, extremalNumber n C.toSimpleGraph ≤ M) :
    extremalNumber n H ≤ M + Fintype.card V * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff (V := Fin n)]
  intro X _ hfree
  by_contra! h
  apply hfree (contained_of_component_bounds H X active ?_)
  intro C
  rw [Fintype.card_fin]
  rw [Fintype.card_fin] at h
  exact lt_of_le_of_lt (Nat.add_le_add_right (bound C) _) h

/-- A trail using the new edge splits at that edge into two walks in the old graph. -/
private lemma trail_split_at_added_edge {V : Type*} (X : SimpleGraph V) {u v : V} :
    ∀ {a b : V} (p : (X ⊔ edge u v).Walk a b), p.IsTrail → s(u, v) ∈ p.edges →
      ∃ (x y : V) (q : X.Walk a x) (r : X.Walk y b),
        s(x, y) = s(u, v) ∧ q.length + r.length < p.length := by
  intro a b p
  induction p with
  | nil => simp
  | @cons a w b hadj p ih =>
    intro ht hm
    have hn := (Walk.isTrail_cons _ _).mp ht
    simp only [Walk.edges_cons, List.mem_cons] at hm
    rcases hm with he | he
    · have hsub : ∀ e ∈ p.edges, e ∈ X.edgeSet := by
        intro e hm
        have hmem := p.edges_subset_edgeSet hm
        rw [edgeSet_sup, Set.mem_union] at hmem
        rcases hmem with h | h
        · exact h
        · have he' := edgeSet_edge_subset h
          have heq : e = s(a, w) := (Set.mem_singleton_iff.mp he').trans he
          exact (hn.2 (heq ▸ hm)).elim
      refine ⟨a, w, Walk.nil, p.transfer X hsub, he.symm, ?_⟩
      simp
    · obtain ⟨x, y, q, r, hxy, hlen⟩ := ih hn.1 he
      have old : X.Adj a w := by
        rcases (show X.Adj a w ∨ (edge u v).Adj a w from hadj) with old | new
        · exact old
        · exact (hn.2 ((adj_edge (s := u) (t := v)).mp new |>.1 ▸ he)).elim
      exact ⟨x, y, Walk.cons old q, r, hxy, by simp only [Walk.length_cons]; omega⟩

private lemma short_cycles_sup_edge {V : Type*} (X : SimpleGraph V) {k : ℕ}
    (hcycles : ∀ ⦃w⦄ (p : X.Walk w w), p.IsCycle → k < p.length)
    {u v : V} (hfar : ∀ p : X.Walk u v, k ≤ p.length) :
    ∀ ⦃w⦄ (p : (X ⊔ edge u v).Walk w w), p.IsCycle → k < p.length := by
  intro w p hp
  by_cases he : s(u, v) ∈ p.edges
  · obtain ⟨a, b, q, r, hab, hlt⟩ := trail_split_at_added_edge X p hp.isTrail he
    rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h := hfar ((r.append q).reverse)
      rw [Walk.length_reverse, Walk.length_append, Nat.add_comm] at h
      exact h.trans_lt hlt
    · have h := hfar (r.append q)
      rw [Walk.length_append, Nat.add_comm] at h
      exact h.trans_lt hlt
  · have hsub : ∀ e ∈ p.edges, e ∈ X.edgeSet := by
      intro e hm
      have he' := p.edges_subset_edgeSet hm
      rw [edgeSet_sup, Set.mem_union] at he'
      rcases he' with he' | he'
      · exact he'
      · exact (he (Set.mem_singleton_iff.mp (edgeSet_edge_subset he') ▸ hm)).elim
    simpa only [Walk.length_transfer] using hcycles (p.transfer X hsub) (hp.transfer hsub)

private noncomputable def walkBall {V : Type*} [Fintype V] (X : SimpleGraph V)
    (u : V) : ℕ → Finset V
  | 0 => {u}
  | j + 1 => (insert u (X.neighborFinset u)).biUnion (fun v => walkBall X v j)

private lemma mem_walkBall_of_length_le {V : Type*} [Fintype V] (X : SimpleGraph V) :
    ∀ (j : ℕ) {u v : V} (p : X.Walk u v), p.length ≤ j → v ∈ walkBall X u j := by
  intro j
  induction j with
  | zero =>
    intro u v p hp
    cases p with
    | nil => simp [walkBall]
    | cons => simp at hp
  | succ j ih =>
    intro u v p hp
    cases p with
    | nil =>
      exact Finset.mem_biUnion.mpr ⟨u, mem_insert_self _ _, ih Walk.nil (by simp)⟩
    | @cons _ w _ adj p =>
      exact Finset.mem_biUnion.mpr ⟨w, mem_insert_of_mem
        ((mem_neighborFinset _ _ _).mpr adj), ih p (by simpa using hp)⟩

private lemma card_walkBall_le {V : Type*} [Fintype V] (X : SimpleGraph V)
    {D : ℕ} (hdeg : ∀ w, X.degree w ≤ D) (j : ℕ) (u : V) :
    (walkBall X u j).card ≤ (D + 1) ^ j := by
  induction j generalizing u with
  | zero => simp [walkBall]
  | succ j ih =>
    calc
      _ ≤ ∑ w ∈ insert u (X.neighborFinset u), (walkBall X w j).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ insert u (X.neighborFinset u), (D + 1) ^ j :=
        Finset.sum_le_sum fun w _ => ih w
      _ = (insert u (X.neighborFinset u)).card * (D + 1) ^ j := by simp
      _ ≤ (D + 1) ^ (j + 1) := by
        rw [pow_succ']
        apply Nat.mul_le_mul_right
        rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
        exact Nat.succ_le_succ (hdeg u)

private lemma degree_sup_edge_le {V : Type*} [Fintype V] (X : SimpleGraph V)
    {u v : V} (D : ℕ) (hdeg : ∀ w, X.degree w ≤ D)
    (hu : X.degree u < D) (hv : X.degree v < D) :
    ∀ w, (X ⊔ edge u v).degree w ≤ D := by
  intro w
  by_cases hw : w = u ∨ w = v
  · let t := if w = u then v else u
    have hs : (X ⊔ edge u v).neighborFinset w ⊆ insert t (X.neighborFinset w) := by
      intro z hz
      rw [mem_neighborFinset, sup_adj] at hz
      rcases hz with hz | hz
      · exact mem_insert_of_mem ((mem_neighborFinset _ _ _).mpr hz)
      · have h := (edge_adj u v w z).mp hz
        rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [t]
        · simp [t, hz.ne]
    have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hc
    rcases hw with rfl | rfl <;> omega
  · have hs : (X ⊔ edge u v).neighborFinset w ⊆ X.neighborFinset w := by
      intro z hz
      rw [mem_neighborFinset, sup_adj] at hz
      exact (mem_neighborFinset _ _ _).mpr (hz.resolve_right fun h =>
        hw (((edge_adj u v w z).mp h).1.imp And.left And.left))
    have hc := Finset.card_le_card hs
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hc
    exact hc.trans (hdeg w)

private lemma cycle_length_le_vertices {V : Type*} [Fintype V] {X : SimpleGraph V}
    {v : V} {p : X.Walk v v} (hp : p.IsCycle) : p.length ≤ Fintype.card V := by
  have ht := hp.isPath_tail.length_lt
  rw [Walk.length_tail] at ht
  omega

private lemma cyclic_extremal_degree_bound {V : Type*} [Fintype V] {H : SimpleGraph V}
    (cyclic : ¬ H.IsAcyclic) (n D : ℕ) :
    D * (n - (D + 1) ^ (Fintype.card V - 1)) ≤ 2 * extremalNumber n H := by
  let k := Fintype.card V
  let Good (X : SimpleGraph (Fin n)) : Prop :=
    (∀ w, X.degree w ≤ D) ∧ ∀ ⦃w⦄ (p : X.Walk w w), p.IsCycle → k < p.length
  have hbot : Good ⊥ := ⟨by simp, fun _ _ hc => (isAcyclic_bot _ hc).elim⟩
  obtain ⟨X, inst, hX⟩ := (exists_isExtremal_iff_exists Good).mpr ⟨⊥, hbot⟩
  obtain ⟨a, p, hp⟩ : ∃ (a : V) (p : H.Walk a a), p.IsCycle := by
    by_contra! h
    exact cyclic h
  have hlen := cycle_length_le_vertices hp
  have hk : 1 < k := by have := hp.three_le_length; omega
  have free : H.Free X := by
    rintro ⟨f⟩
    have h := hX.prop.2 (p.map f.toHom) (hp.map f.injective)
    rw [Walk.length_map] at h
    exact (not_lt_of_ge hlen) h
  have nearby (u v : Fin n) (hu : X.degree u < D) (hv : X.degree v < D) :
      ∃ q : X.Walk u v, q.length < k := by
    by_contra! hfar
    have hne : u ≠ v := by
      rintro rfl
      have hh := hfar Walk.nil
      simp at hh
      omega
    have hnadj : ¬ X.Adj u v := by
      intro h
      have hh := hfar (Walk.cons h Walk.nil)
      simp at hh
      omega
    have hy : Good (X ⊔ edge u v) := by
      refine ⟨?_, short_cycles_sup_edge X hX.prop.2 hfar⟩
      intro w
      convert! degree_sup_edge_le X (u := u) (v := v) D hX.prop.1 (by convert! hu) (by convert! hv) w
    exact (lt_sup_edge X u v hne hnadj).ne ((hX.le_iff_eq hy).mp le_sup_left)
  let low := univ.filter fun u : Fin n => X.degree u < D
  have hlow : low.card ≤ (D + 1) ^ (k - 1) := by
    by_cases h : low.Nonempty
    · obtain ⟨u, hu⟩ := h
      have hsub : low ⊆ walkBall X u (k - 1) := by
        intro v hv
        obtain ⟨q, hq⟩ := nearby u v (mem_filter.mp hu).2 (mem_filter.mp hv).2
        exact mem_walkBall_of_length_le X _ q (by omega)
      exact (Finset.card_le_card hsub).trans (card_walkBall_le X hX.prop.1 _ _)
    · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty]
      exact Nat.zero_le _
  let high := univ \ low
  have hhigh : high.card = n - low.card := by simp [high, Finset.card_sdiff_of_subset]
  have hsum : D * (n - (D + 1) ^ (k - 1)) ≤ ∑ v, X.degree v := by
    calc
      _ ≤ D * high.card := by rw [hhigh]; exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hlow _)
      _ = ∑ _v ∈ high, D := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ high, X.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact Nat.le_of_not_gt fun h =>
          (Finset.mem_sdiff.mp hv).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
      _ ≤ ∑ v, X.degree v := Finset.sum_le_sum_of_subset (subset_univ _)
  rw [sum_degrees_eq_twice_card_edges] at hsum
  exact hsum.trans (Nat.mul_le_mul_left 2 (by simpa using card_edgeFinset_le_extremalNumber free))

private lemma cyclic_density_diverges {V : Type*} [Fintype V] {H : SimpleGraph V}
    (cyclic : ¬ H.IsAcyclic) :
    Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  obtain ⟨D, hD⟩ := exists_nat_ge (4 * M)
  let K := (D + 1) ^ (Fintype.card V - 1)
  filter_upwards [eventually_ge_atTop (max 1 (2 * K))] with n hn
  have hlarge : 2 * K ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr ((le_max_left _ _).trans hn)
  have hb := cyclic_extremal_degree_bound cyclic n D
  change D * (n - K) ≤ _ at hb
  have hb' : D * n ≤ 4 * extremalNumber n H := calc
    _ ≤ D * (2 * (n - K)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (D * (n - K)) := by ring
    _ ≤ _ := by omega
  have hbR : (D : ℝ) * n ≤ 4 * (extremalNumber n H : ℝ) := by exact_mod_cast hb'
  apply (le_div_iff₀ hnpos).mpr
  nlinarith only [hbR, mul_le_mul_of_nonneg_right hD hnpos.le]

private def HasExtremalLimit {V : Type*} (H : SimpleGraph V) (a c : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ a) atTop (𝓝 c)

private lemma extremal_limit_at_higher_power {V : Type*} {H : SimpleGraph V} {a b c : ℝ}
    (hab : a < b) (fit : HasExtremalLimit H a c) : HasExtremalLimit H b 0 := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop (𝓝 0) := by
    rw [← neg_sub]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  unfold HasExtremalLimit at *
  have hmul := fit.mul hpow
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Real.rpow_sub hnpos, div_mul_div_comm, mul_comm, mul_div_mul_left _ _ (by positivity)]

private lemma linear_term_at_higher_power {a : ℝ} (ha : 1 < a) (K : ℝ) :
    Tendsto (fun n : ℕ => K * n / (n : ℝ) ^ a) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp
    (tendsto_natCast_atTop_atTop : Tendsto ((↑) : ℕ → ℝ) atTop atTop)
  have hmul := hpow.const_mul K
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  change K * (n : ℝ) ^ (-(a - 1)) = _
  rw [neg_sub, Real.rpow_sub hnpos, Real.rpow_one, mul_div_assoc]

private lemma forest_limit_at_higher_power {V : Type*} [Fintype V] {H : SimpleGraph V}
    (forest : H.IsAcyclic) {a : ℝ} (ha : 1 < a) : HasExtremalLimit H a 0 := by
  let e := Fintype.equivFin V
  let J := H.comap e.symm
  let iso : J ≃g H := ⟨e.symm, Iff.rfl⟩
  unfold HasExtremalLimit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (linear_term_at_higher_power ha (Fintype.card V : ℝ))
  · intro n
    positivity
  · intro n
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← extremalNumber_congr_right iso]
    have h := forest_extremal_upper J (iso.isAcyclic_iff.mpr forest) n
    push_cast
    exact_mod_cast h

private lemma exists_cyclic_component {V : Type*} {H : SimpleGraph V} (h : ¬ H.IsAcyclic) :
    ∃ C : H.ConnectedComponent, ¬ C.toSimpleGraph.IsAcyclic := by
  classical
  obtain ⟨u, p, hp⟩ : ∃ (u : V) (p : H.Walk u u), p.IsCycle := by
    by_contra! hn
    exact h hn
  let C := H.connectedComponentMk u
  have hsub : ∀ v ∈ p.support, v ∈ C.supp := by
    intro v hv
    exact ConnectedComponent.sound (p.takeUntil v hv).reachable.symm
  let q := p.induce C.supp hsub
  have hq : q.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce C.supp).toHom)
    simpa [q] using hp
  exact ⟨C, fun forest => forest q hq⟩

private lemma limit_of_component_limits {V : Type*} [Fintype V] (H : SimpleGraph V)
    (active : ∀ v, ∃ w, H.Adj v w) (cyclic : ¬ H.IsAcyclic)
    (components : ∀ C : H.ConnectedComponent, ¬ C.toSimpleGraph.IsAcyclic →
      ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ HasExtremalLimit C.toSimpleGraph a c) :
    ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ HasExtremalLimit H a c := by
  obtain ⟨C₀, hC₀⟩ := exists_cyclic_component cyclic
  let : Fintype H.ConnectedComponent :=
    Fintype.ofSurjective H.connectedComponentMk (fun C => ⟨C.out, C.out_eq⟩)
  let I : Finset H.ConnectedComponent := univ
  have hI : I.Nonempty := ⟨C₀, mem_univ _⟩
  have choices (C : H.ConnectedComponent) : ∃ a c : ℝ,
      (a = 1 ∧ C.toSimpleGraph.IsAcyclic) ∨
        (1 < a ∧ 0 < c ∧ HasExtremalLimit C.toSimpleGraph a c) := by
    by_cases forest : C.toSimpleGraph.IsAcyclic
    · exact ⟨1, 0, Or.inl ⟨rfl, forest⟩⟩
    · obtain ⟨a, c, hc⟩ := components C forest
      exact ⟨a, c, Or.inr hc⟩
  choose a c h using choices
  let A := I.sup' hI a
  have ha (C : H.ConnectedComponent) : a C ≤ A := Finset.le_sup' a (mem_univ C)
  have hA : 1 < A := by
    rcases h C₀ with h₀ | h₀
    · exact (hC₀ h₀.2).elim
    · exact h₀.1.trans_le (ha _)
  let d (C : H.ConnectedComponent) : ℝ := if a C = A then c C else 0
  have limits (C : H.ConnectedComponent) : HasExtremalLimit C.toSimpleGraph A (d C) := by
    rcases h C with ⟨hc, forest⟩ | ⟨_, _, fit⟩
    · simpa [d, hc, hA.ne] using (forest_limit_at_higher_power forest hA)
    · rcases (ha C).lt_or_eq with hlt | heq
      · simpa [d, hlt.ne] using (extremal_limit_at_higher_power hlt fit)
      · simpa [d, heq] using fit
  let best := I.sup' hI d
  have hbest : 0 < best := by
    obtain ⟨C, hC, heq⟩ := I.exists_mem_eq_sup' hI a
    rcases h C with ⟨hc, _⟩ | ⟨_, hpos, _⟩
    · exact (hA.ne' (heq.trans hc)).elim
    · have hd : d C = c C := if_pos heq.symm
      exact (hd ▸ hpos).trans_le (Finset.le_sup' d hC)
  let μ (n : ℕ) := I.sup' hI (fun C => extremalNumber n C.toSimpleGraph)
  have hm (n : ℕ) : μ n ≤ extremalNumber n H := by
    apply Finset.sup'_le
    intro C _
    exact (Copy.induce H C.supp).isContained.extremalNumber_le
  have hu (n : ℕ) : extremalNumber n H ≤ μ n + Fintype.card V * n :=
    extremal_le_component_bound H active n (μ n) (fun C => Finset.le_sup' (fun C => extremalNumber n C.toSimpleGraph) (mem_univ C))
  have hsup := Tendsto.finset_sup'_nhds_apply hI (fun C _ => limits C)
  have hμ : Tendsto (fun n : ℕ => (μ n : ℝ) / (n : ℝ) ^ A) atTop (𝓝 best) := by
    apply hsup.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hpow : 0 < (n : ℝ) ^ A := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
    symm
    apply Finset.apply_sup'_eq_sup'_comp hI (fun m : ℕ => (m : ℝ) / (n : ℝ) ^ A)
    intro x y
    exact Monotone.map_sup (fun _ _ hxy => div_le_div_of_nonneg_right (by exact_mod_cast hxy)
      hpow.le) x y
  refine ⟨A, best, hA, hbest, ?_⟩
  unfold HasExtremalLimit
  have hsum := hμ.add (linear_term_at_higher_power hA (Fintype.card V : ℝ))
  rw [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hμ hsum
  · intro n
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hm n)) (by positivity)
  · intro n
    dsimp
    rw [← add_div]
    have hab : (extremalNumber n H : ℝ) ≤ (μ n : ℝ) + (Fintype.card V : ℝ) * n := by
      exact_mod_cast hu n
    exact div_le_div_of_nonneg_right hab (by positivity)

/-- The true labels mark vertices to place. The left labels fix boundary vertices. -/
private def PatternFits {V W : Type*} (H : SimpleGraph V) (X : SimpleGraph W)
    (S : Finset W) (tag : V → S ⊕ Bool) (U : Finset W) : Prop :=
  ∃ f : V → W,
    (∀ v, tag v = .inr true → f v ∉ S ∧ f v ∉ U) ∧
    Set.InjOn f {v | tag v = .inr true} ∧
    (∀ ⦃v w⦄, H.Adj v w → tag v = .inr true → tag w = .inr true → X.Adj (f v) (f w)) ∧
    (∀ ⦃v w⦄ (s : S), H.Adj v w → tag v = .inr true → tag w = .inl s → X.Adj (f v) s.val)

private def BoundaryRegular {V W : Type*} [Fintype V] (H : SimpleGraph V)
    (X : SimpleGraph W) (S T : Finset W) : Prop :=
  ∀ tag : V → S ⊕ Bool, PatternFits H X S tag T →
    ∀ U : Finset W, U.card ≤ Fintype.card V → PatternFits H X S tag U

private lemma exists_boundary_regularizer {V W : Type*} [Fintype V] (H : SimpleGraph V)
    (X : SimpleGraph W) (S : Finset W) :
    ∃ T : Finset W, Disjoint S T ∧ T.card ≤ (S.card + 2) ^ Fintype.card V * Fintype.card V ∧
      BoundaryRegular H X S T := by
  let bad (tag : V → S ⊕ Bool) := ∃ U : Finset W,
    U.card ≤ Fintype.card V ∧ ¬ PatternFits H X S tag U
  let witness (tag : V → S ⊕ Bool) : Finset W :=
    if h : bad tag then h.choose \ S else ∅
  let T := univ.biUnion witness
  have hw (tag) : witness tag ⊆ T := subset_biUnion_of_mem witness (mem_univ tag)
  have hsize (tag) : (witness tag).card ≤ Fintype.card V := by
    by_cases h : bad tag
    · exact (by simpa only [witness, dif_pos h] using
        (Finset.card_le_card (Finset.sdiff_subset (s := h.choose) (t := S))).trans h.choose_spec.1)
    · simp [witness, h]
  refine ⟨T, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro w hS hT
    obtain ⟨tag, _, hw⟩ := mem_biUnion.mp hT
    by_cases h : bad tag
    · exact (mem_sdiff.mp (by simpa only [witness, dif_pos h] using hw)).2 hS
    · simp [witness, h] at hw
  · calc
      _ ≤ ∑ tag, (witness tag).card := Finset.card_biUnion_le
      _ ≤ ∑ _tag : V → S ⊕ Bool, Fintype.card V := Finset.sum_le_sum fun tag _ => hsize tag
      _ = _ := by simp
  · intro tag fit U hU
    by_contra hnot
    have h : bad tag := ⟨U, hU, hnot⟩
    obtain ⟨f, hf, hInj, hin, hout⟩ := fit
    apply h.choose_spec.2
    refine ⟨f, fun v hv => ⟨(hf v hv).1, ?_⟩, hInj, hin, hout⟩
    intro hm
    apply (hf v hv).2 (hw tag ?_)
    dsimp only [witness]
    rw [dif_pos h]
    exact mem_sdiff.mpr ⟨hm, (hf v hv).1⟩

/-- Separate one layer from the other non-boundary vertices of a proposed copy. -/
private noncomputable def layerPattern {V W I : Type*} (S : Finset W)
    (tag : V → S ⊕ I) (i : I) (v : V) : S ⊕ Bool :=
  match tag v with
  | .inl s => .inl s
  | .inr j => .inr (Classical.decEq I j i |>.decide)

@[simp] private lemma layerPattern_eq_true {V W I : Type*} {S : Finset W}
    (tag : V → S ⊕ I) (i : I) (v : V) :
    layerPattern S tag i v = .inr true ↔ tag v = .inr i := by
  cases h : tag v <;> simp [layerPattern, h]

@[simp] private lemma layerPattern_eq_left {V W I : Type*} {S : Finset W}
    (tag : V → S ⊕ I) (i : I) (v : V) (s : S) :
    layerPattern S tag i v = .inl s ↔ tag v = .inl s := by
  cases h : tag v <;> simp [layerPattern, h]

private lemma contained_of_regular_boundary {V W I : Type*} [Fintype V] [Fintype I]
    (H : SimpleGraph V) (X : SimpleGraph W) {S T : Finset W}
    (regular : BoundaryRegular H X S T) (tag : V → S ⊕ I) (g : V → W)
    (root : ∀ v s, tag v = .inl s → g v = s.val)
    (rootInj : ∀ ⦃v w⦄ (s : S), tag v = .inl s → tag w = .inl s → v = w)
    (tagAdj : ∀ ⦃v w i j⦄, H.Adj v w → tag v = .inr i → tag w = .inr j → i = j)
    (adj : ∀ ⦃v w⦄, H.Adj v w → X.Adj (g v) (g w))
    (patterns : ∀ i, PatternFits H X S (layerPattern S tag i) T) : H ⊑ X := by
  let assigned (s : Finset I) : Set V :=
    {v | match tag v with | .inl _ => True | .inr i => i ∈ s}
  have hfit (s : Finset I) : ∃ f : V → W,
      (∀ v r, tag v = .inl r → f v = r.val) ∧
      (∀ ⦃v w⦄, H.Adj v w → X.Adj (f v) (f w)) ∧ Set.InjOn f (assigned s) := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨g, root, adj, ?_⟩
      intro v hv w hw heq
      cases ev : tag v with
      | inr i => simp [assigned, ev] at hv
      | inl r =>
        cases ew : tag w with
        | inr i => simp [assigned, ew] at hw
        | inl t =>
          have hrs : r = t := Subtype.ext ((root v r ev).symm.trans (heq.trans (root w t ew)))
          subst t
          exact rootInj r ev ew
    | @insert i s hi ih =>
      obtain ⟨f, hroot, hadj, hinj⟩ := ih
      let used := univ.image f
      have hu : used.card ≤ Fintype.card V := by
        simpa [used] using (Finset.card_image_le (s := (univ : Finset V)) (f := f))
      obtain ⟨z, hz, hzinj, hzin, hzout⟩ := regular _ (patterns i) used hu
      let p (v : V) := if tag v = .inr i then z v else f v
      have pnew {v} (hv : tag v = .inr i) : p v = z v := if_pos hv
      have pold {v} (hv : tag v ≠ .inr i) : p v = f v := if_neg hv
      have hnew {v} (hv : tag v = .inr i) : z v ∉ used := (hz v (by simpa using hv)).2
      have hold (v) : f v ∈ used := Finset.mem_image_of_mem f (mem_univ v)
      have mainAdj ⦃v w⦄ (h : H.Adj v w) (hv : tag v = .inr i) :
          X.Adj (p v) (p w) := by
        rw [pnew hv]
        cases hw : tag w with
        | inl r =>
          rw [pold (by simp [hw]), hroot w r hw]
          exact hzout r h (by simpa using hv) (by simpa using hw)
        | inr j =>
          have hij := tagAdj h hv hw
          subst j
          rw [pnew hw]
          exact hzin h (by simpa using hv) (by simpa using hw)
      have oldAssigned {v} (hv : v ∈ assigned (insert i s)) (h : tag v ≠ .inr i) :
          v ∈ assigned s := by
        cases e : tag v <;> simp_all [assigned]
      refine ⟨p, fun v r hv => (pold (by simp [hv])).trans (hroot v r hv), ?_, ?_⟩
      · intro v w h
        by_cases hv : tag v = .inr i
        · exact mainAdj h hv
        by_cases hw : tag w = .inr i
        · exact (mainAdj h.symm hw).symm
        rw [pold hv, pold hw]
        exact hadj h
      · intro v hv w hw heq
        by_cases ev : tag v = .inr i <;> by_cases ew : tag w = .inr i
        · rw [pnew ev, pnew ew] at heq
          exact hzinj (by simpa using ev) (by simpa using ew) heq
        · rw [pnew ev, pold ew] at heq
          exact (hnew ev (heq.symm ▸ hold w)).elim
        · rw [pold ev, pnew ew] at heq
          exact (hnew ew (heq ▸ hold v)).elim
        · rw [pold ev, pold ew] at heq
          exact hinj (oldAssigned hv ev) (oldAssigned hw ew) heq
  obtain ⟨f, _, hf, hinj⟩ := hfit univ
  have hall (v : V) : v ∈ assigned univ := by cases h : tag v <;> simp [assigned, h]
  exact ⟨⟨⟨f, fun h => hf h⟩, fun v w h => hinj (hall v) (hall w) h⟩⟩

private abbrev GluedVertex {W : Type*} (S : Finset W) (I : Type*) := S ⊕ (W × I)

private def vertexBase {W I : Type*} {S : Finset W} : GluedVertex S I → W :=
  Sum.elim Subtype.val Prod.fst

private def vertexLabel {W I : Type*} {S : Finset W} : GluedVertex S I → S ⊕ I :=
  Sum.map id Prod.snd

private def validVertex {W I : Type*} {S : Finset W} (T : Finset W) :
    GluedVertex S I → Prop :=
  Sum.elim (fun _ => True) (fun p => p.1 ∉ S ∧ p.1 ∉ T)

private lemma gluedVertex_eq {W I : Type*} {S : Finset W} {x y : GluedVertex S I}
    (h₁ : vertexBase x = vertexBase y) (h₂ : vertexLabel x = vertexLabel y) : x = y := by
  cases x <;> cases y <;> simp_all [vertexBase, vertexLabel, Prod.ext_iff]

private def gluedGraph {W : Type*} (X : SimpleGraph W) (S T : Finset W) (I : Type*) :
    SimpleGraph (GluedVertex S I) where
  Adj x y := X.Adj (vertexBase x) (vertexBase y) ∧ validVertex T x ∧ validVertex T y ∧
    ∀ ⦃i j⦄, vertexLabel x = .inr i → vertexLabel y = .inr j → i = j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, fun {_ _} hx hy => (h.2.2.2 hy hx).symm⟩⟩
  loopless := ⟨fun _ h => X.irrefl h.1⟩

private lemma gluedGraph_free {V W I : Type*} [Fintype V] [Fintype I]
    {H : SimpleGraph V} {X : SimpleGraph W} {S T : Finset W}
    (active : ∀ v, ∃ w, H.Adj v w) (free : H.Free X)
    (regular : BoundaryRegular H X S T) : H.Free (gluedGraph X S T I) := by
  rintro ⟨f⟩
  let tag (v : V) := vertexLabel (f v)
  let g (v : V) := vertexBase (f v)
  have labelRoot {v : V} {s : S} (h : tag v = .inl s) : f v = .inl s := by
    cases he : f v <;> simp_all [tag, vertexLabel]
  have hvalid (v : V) : validVertex T (f v) := by
    obtain ⟨w, hvw⟩ := active v
    exact (f.toHom.map_adj hvw).2.1
  apply free (contained_of_regular_boundary H X regular tag g ?_ ?_ ?_ ?_ ?_)
  · intro v s h
    change vertexBase (f v) = s.val
    rw [labelRoot h]
    rfl
  · intro v w s hv hw
    exact f.injective ((labelRoot hv).trans (labelRoot hw).symm)
  · intro v w i j hvw hi hj
    exact (f.toHom.map_adj hvw).2.2.2 hi hj
  · intro v w h
    exact (f.toHom.map_adj h).1
  · intro i
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [layerPattern_eq_true] at hv
      have hu := hvalid v
      cases he : f v <;> simp_all [tag, g, vertexLabel, vertexBase, validVertex]
    · intro v hv w hw heq
      have h₁ : tag v = .inr i := (layerPattern_eq_true _ _ _).mp hv
      have h₂ : tag w = .inr i := (layerPattern_eq_true _ _ _).mp hw
      exact f.injective (gluedVertex_eq heq (h₁.trans h₂.symm))
    · intro v w h _ _
      exact (f.toHom.map_adj h).1
    · intro v w s h _ hs
      have he := labelRoot ((layerPattern_eq_left _ _ _ _).mp hs)
      have ha : X.Adj (g v) (g w) := (f.toHom.map_adj h).1
      simpa [g, he, vertexBase] using ha

private def offBoundary {W : Type*} (X : SimpleGraph W) (S T : Finset W) : SimpleGraph W where
  Adj x y := X.Adj x y ∧ x ∉ T ∧ y ∉ T ∧ (x ∉ S ∨ y ∉ S)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩⟩
  loopless := ⟨fun _ h => X.irrefl h.1⟩

private lemma offBoundary_edge_bound {W : Type*} [Fintype W] (X : SimpleGraph W)
    (S T : Finset W) :
    X.edgeFinset.card ≤ (offBoundary X S T).edgeFinset.card +
      (∑ w ∈ T, X.degree w) + S.card ^ 2 := by
  let Y := eraseVertices X (↑T : Set W)
  let Z := offBoundary X S T
  let inc : S ↪ W := ⟨Subtype.val, Subtype.val_injective⟩
  let B := (⊤ : SimpleGraph S).map inc
  have hc : Y ≤ Z ⊔ B := by
    intro u v huv
    by_cases hs : u ∉ S ∨ v ∉ S
    · exact Or.inl ⟨huv.1, huv.2.1, huv.2.2, hs⟩
    · have hu : u ∈ S := not_not.mp (fun h => hs (Or.inl h))
      have hv : v ∈ S := not_not.mp (fun h => hs (Or.inr h))
      apply Or.inr
      exact (map_adj inc ⊤ u v).mpr ⟨⟨u, hu⟩, ⟨v, hv⟩,
        fun h => huv.1.ne (congrArg Subtype.val h), rfl, rfl⟩
  have hB : B.edgeFinset.card ≤ S.card ^ 2 := by
    have he : B.edgeFinset.card = (⊤ : SimpleGraph S).edgeFinset.card := by
      convert! card_edgeFinset_map inc (⊤ : SimpleGraph S)
    rw [he, card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe]
    exact Nat.choose_le_pow _ _
  have hsup : (Z ⊔ B).edgeFinset.card ≤ Z.edgeFinset.card + B.edgeFinset.card := by
    have he : (Z ⊔ B).edgeFinset = Z.edgeFinset ∪ B.edgeFinset := by
      convert! (edgeFinset_sup (G₁ := Z) (G₂ := B))
    rw [he]
    exact Finset.card_union_le _ _
  have hy := Finset.card_le_card (edgeFinset_mono hc)
  have ht : X.edgeFinset.card ≤ Y.edgeFinset.card + ∑ w ∈ T, X.degree w :=
    card_edges_eraseVertices_le_degree_sum X T
  change X.edgeFinset.card ≤ Z.edgeFinset.card + _ + _
  omega

private noncomputable def stamp {W I : Type*} (S : Finset W) (i : I) (w : W) : GluedVertex S I :=
  if h : w ∈ S then .inl ⟨w, h⟩ else .inr (w, i)

private lemma stamp_base {W I : Type*} (S : Finset W) (i : I) (w : W) :
    vertexBase (stamp S i w) = w := by
  by_cases h : w ∈ S <;> simp [stamp, h, vertexBase]

private lemma stamp_labels {W I : Type*} (S : Finset W) (i : I) (w : W) {j : I} :
    vertexLabel (stamp S i w) = .inr j → i = j := by
  by_cases h : w ∈ S <;> simp [stamp, h, vertexLabel]

private lemma stamp_adj {W I : Type*} (X : SimpleGraph W) (S T : Finset W)
    {u v : W} (h : (offBoundary X S T).Adj u v) (i : I) :
    (gluedGraph X S T I).Adj (stamp S i u) (stamp S i v) := by
  have valid (w : W) (hw : w ∉ T) : validVertex T (stamp S i w) := by
    by_cases hm : w ∈ S <;> simp [stamp, hm, hw, validVertex]
  refine ⟨?_, valid u h.2.1, valid v h.2.2.1, fun {_ _} h₁ h₂ =>
    (stamp_labels S i u h₁).symm.trans (stamp_labels S i v h₂)⟩
  simpa only [stamp_base] using h.1

private lemma gluedGraph_edge_lower {W I : Type*} [Fintype W] [Fintype I] (X : SimpleGraph W)
    (S T : Finset W) :
    Fintype.card I * (offBoundary X S T).edgeFinset.card ≤
      (gluedGraph X S T I).edgeFinset.card := by
  let Z := offBoundary X S T
  let Y := gluedGraph X S T I
  let f (p : I × Z.Dart) : Y.Dart :=
    ⟨(stamp S p.1 p.2.fst, stamp S p.1 p.2.snd), stamp_adj X S T p.2.adj p.1⟩
  have hf : Function.Injective f := by
    rintro ⟨i, d⟩ ⟨j, e⟩ h
    have hfst : stamp S i d.fst = stamp S j e.fst := congrArg (fun x : Y.Dart => x.fst) h
    have hsnd : stamp S i d.snd = stamp S j e.snd := congrArg (fun x : Y.Dart => x.snd) h
    have heq : d = e := by
      ext
      · simpa only [stamp_base] using congrArg vertexBase hfst
      · simpa only [stamp_base] using congrArg vertexBase hsnd
    subst e
    have hij : i = j := by
      rcases d.adj.2.2.2 with hn | hn
      · simpa [stamp, hn] using hfst
      · simpa [stamp, hn] using hsnd
    exact Prod.ext hij rfl
  have hb := Fintype.card_le_of_injective _ hf
  rw [Fintype.card_prod, dart_card_eq_twice_card_edges, dart_card_eq_twice_card_edges] at hb
  change Fintype.card I * Z.edgeFinset.card ≤ Y.edgeFinset.card
  linarith only [show 2 * (Fintype.card I * Z.edgeFinset.card) ≤ 2 * Y.edgeFinset.card by
    simpa only [← Nat.mul_assoc, Nat.mul_left_comm (Fintype.card I) 2, Nat.mul_assoc] using hb]

private lemma card_edgeFinset_le_extremal_of_card_le {V W : Type*} [Fintype W]
    {H : SimpleGraph V} {X : SimpleGraph W} (active : ∀ v, ∃ w, H.Adj v w)
    (free : H.Free X) {N : ℕ} (hN : Fintype.card W ≤ N) :
    X.edgeFinset.card ≤ extremalNumber N H := by
  let e : W ↪ Fin N := (Function.Embedding.nonempty_of_card_le (by simpa using hN)).some
  have hfree : H.Free (X.map e) := by
    rintro ⟨f⟩
    have hrange (v : V) : ∃ w, e w = f v := by
      obtain ⟨u, hu⟩ := active v
      obtain ⟨a, _, _, ha, _⟩ := (map_adj e X _ _).mp (f.toHom.map_adj hu)
      exact ⟨a, ha⟩
    choose g hg using hrange
    apply free
    refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
    · intro v w hw
      obtain ⟨a, b, hab, ha, hb⟩ := (map_adj e X _ _).mp (f.toHom.map_adj hw)
      exact e.injective (ha.trans (hg v).symm) ▸ e.injective (hb.trans (hg w).symm) ▸ hab
    · intro v w hw
      exact f.injective ((hg v).symm.trans ((congrArg e hw).trans (hg w)))
  have h := card_edgeFinset_le_extremalNumber hfree
  rw [Fintype.card_fin] at h
  have he : (X.map e).edgeFinset.card = X.edgeFinset.card := by
    convert! card_edgeFinset_map e X
  exact he ▸ h

private def boundarySize (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | l + 1 => let b := boundarySize q l; b + (b + 2) ^ q * q

private lemma exists_boundary_with_small_loss {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (X : SimpleGraph W) {l : ℕ} (hl : 0 < l) :
    ∃ S T : Finset W, S.card ≤ boundarySize (Fintype.card V) l ∧
      l * (∑ v ∈ T, X.degree v) ≤ 2 * X.edgeFinset.card ∧ BoundaryRegular H X S T := by
  choose cut hdisj hsize hregular using exists_boundary_regularizer H X
  let chain : ℕ → Finset W := Nat.rec ∅ (fun _ s => s ∪ cut s)
  have hs (j : ℕ) : (chain j).card ≤ boundarySize (Fintype.card V) j := by
    induction j with
    | zero => simp [chain, boundarySize]
    | succ j ih =>
      change (chain j ∪ cut (chain j)).card ≤
        boundarySize (Fintype.card V) j + (boundarySize (Fintype.card V) j + 2) ^
          Fintype.card V * Fintype.card V
      apply (Finset.card_union_le _ _).trans
      exact Nat.add_le_add ih ((hsize _).trans (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_left (Nat.add_le_add_right ih 2) _)))
  have chainMono : Monotone chain :=
    monotone_nat_of_le_succ fun j =>
      (show chain j ⊆ chain j ∪ cut (chain j) from Finset.subset_union_left)
  let loss (j : ℕ) := ∑ v ∈ cut (chain j), X.degree v
  have hsum (j : ℕ) : (∑ i ∈ range j, loss i) = ∑ v ∈ chain j, X.degree v := by
    induction j with
    | zero => simp [chain]
    | succ j ih =>
      rw [sum_range_succ, ih]
      change _ = ∑ v ∈ chain j ∪ cut (chain j), X.degree v
      rw [Finset.sum_union (hdisj _)]
  have htotal : ∑ i ∈ range l, loss i ≤ 2 * X.edgeFinset.card := by
    rw [hsum, ← sum_degrees_eq_twice_card_edges]
    exact Finset.sum_le_sum_of_subset (subset_univ _)
  have hscaled : (∑ i ∈ range l, l * loss i) ≤ ∑ _i ∈ range l, 2 * X.edgeFinset.card := by
    calc
      _ = l * ∑ i ∈ range l, loss i := (Finset.mul_sum _ _ _).symm
      _ ≤ l * (2 * X.edgeFinset.card) := Nat.mul_le_mul_left l htotal
      _ = _ := by simp only [Finset.sum_const_nat, Finset.card_range]
  obtain ⟨i, hi, hsmall⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (by omega : l ≠ 0)) hscaled
  refine ⟨chain i, cut (chain i), ?_, hsmall, hregular _⟩
  exact (Finset.card_le_card (chainMono ((mem_range.mp hi).le))).trans (hs l)

/-- The number of full layers that fit after reserving the boundary is asymptotic to N/n. -/
private lemma tendsto_layer_density {n : ℕ} (hn : 0 < n) (s : ℕ) :
    Tendsto (fun N : ℕ => (((N - s) / n : ℕ) : ℝ) / N) atTop (𝓝 ((n : ℝ)⁻¹)) := by
  have hz : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun N : ℕ => (n : ℝ)⁻¹ - ((s + n : ℕ) : ℝ) / n * (N : ℝ)⁻¹)
      atTop (𝓝 ((n : ℝ)⁻¹)) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub
      (hz.const_mul (((s + n : ℕ) : ℝ) / n))
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (max 1 s)] with N hN
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    let t := (N - s) / n
    have hr := Nat.mod_add_div (N - s) n
    have hm := Nat.mod_lt (N - s) hn
    change (N - s) % n + n * t = N - s at hr
    have hnat : N ≤ n * t + (s + n) := by omega
    have hreal : (N : ℝ) ≤ n * (t : ℝ) + ((s + n : ℕ) : ℝ) := by exact_mod_cast hnat
    change (n : ℝ)⁻¹ - ((s + n : ℕ) : ℝ) / n * (N : ℝ)⁻¹ ≤ (t : ℝ) / N
    field_simp
    nlinarith only [hreal]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have h : ((N - s) / n) * n ≤ N := (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
    have hr : (((N - s) / n : ℕ) : ℝ) * n ≤ N := by exact_mod_cast h
    change (((N - s) / n : ℕ) : ℝ) / N ≤ (n : ℝ)⁻¹
    field_simp
    nlinarith only [hr]

private lemma eventually_extremal_density_ge_of_gluing {q n : ℕ}
    {H : SimpleGraph (Fin q)} {X : SimpleGraph (Fin n)} (hn : 0 < n)
    (active : ∀ v, ∃ w, H.Adj v w) (free : H.Free X) {S T : Finset (Fin n)}
    (regular : BoundaryRegular H X S T) {b : ℝ}
    (hdense : b < ((offBoundary X S T).edgeFinset.card : ℝ) / n) :
    ∀ᶠ N : ℕ in atTop, b ≤ (extremalNumber N H : ℝ) / N := by
  let e := (offBoundary X S T).edgeFinset.card
  have hfit : Tendsto (fun N : ℕ => (e : ℝ) * (((N - S.card) / n : ℕ) : ℝ) / N)
      atTop (𝓝 ((e : ℝ) / n)) := by
    simpa only [div_eq_mul_inv, mul_assoc] using
      (tendsto_layer_density hn S.card).const_mul (e : ℝ)
  have hgt := (tendsto_order.mp hfit).1 b hdense
  filter_upwards [hgt, eventually_ge_atTop (max S.card 1)] with N hN hbound
  let t := (N - S.card) / n
  let Y := gluedGraph X S T (Fin t)
  have hcard : Fintype.card (GluedVertex S (Fin t)) ≤ N := by
    simp only [GluedVertex, Fintype.card_sum, Fintype.card_coe, Fintype.card_prod, Fintype.card_fin]
    rw [Nat.mul_comm n t]
    have h := Nat.div_mul_le_self (N - S.card) n
    change t * n ≤ N - S.card at h
    omega
  have hfree : H.Free Y := gluedGraph_free active free regular
  have hge : t * e ≤ extremalNumber N H := by
    calc
      _ ≤ Y.edgeFinset.card := by
        simpa only [Fintype.card_fin] using
          (gluedGraph_edge_lower (I := Fin t) X S T)
      _ ≤ _ := card_edgeFinset_le_extremal_of_card_le active hfree hcard
  have hgeR : (e : ℝ) * (t : ℝ) ≤ (extremalNumber N H : ℝ) := by
    rw [mul_comm]
    exact_mod_cast hge
  exact hN.le.trans (div_le_div_of_nonneg_right hgeR (by positivity))

/-- A linearly bounded extremal sequence for a graph without isolated vertices has a density. -/
private lemma linear_extremal_density_exists {q : ℕ} (H : SimpleGraph (Fin q))
    (active : ∀ v, ∃ w, H.Adj v w) (edges : 2 ≤ H.edgeFinset.card)
    (bound : ∀ n, extremalNumber n H ≤ q * n) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / n) atTop (𝓝 c) := by
  let density (n : ℕ) := (extremalNumber n H : ℝ) / n
  have nonneg (n : ℕ) : 0 ≤ density n := by dsimp [density]; positivity
  have upper : ∀ᶠ n : ℕ in atTop, density n ≤ (q : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    exact (div_le_iff₀ hnpos).mpr (by exact_mod_cast bound n)
  have nebot : H ≠ ⊥ := by
    intro h
    rw [edgeFinset_eq_empty.mpr h, Finset.card_empty] at edges
    omega
  have crossings (a : ℝ) (_ : a ∈ (Set.univ : Set ℝ)) (b : ℝ)
      (_ : b ∈ (Set.univ : Set ℝ)) (hab : a < b) :
      ¬((∃ᶠ n in atTop, density n < a) ∧ ∃ᶠ n in atTop, b < density n) := by
    rintro ⟨small, large⟩
    let δ := (b - a) / 3
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨l, hl⟩ := exists_nat_gt (max 0 (2 * (q : ℝ) / δ))
    have hlpos : (0 : ℝ) < l := (le_max_left _ _).trans_lt hl
    have hlNat : 0 < l := Nat.cast_pos.mp hlpos
    have hlmul : (2 : ℝ) * q ≤ l * δ :=
      ((div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hl)).le
    let B := boundarySize q l
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((B : ℝ)^2 / δ)
    obtain ⟨n, hnlarge, hn⟩ := (large.and_eventually (eventually_ge_atTop (max n₀ 1))).exists
    have hnpos : 0 < n := (le_max_right n₀ 1).trans hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hB : (B : ℝ)^2 ≤ δ * n := by
      have hlt := hn₀.trans_le (Nat.cast_le.mpr ((le_max_left _ _).trans hn))
      simpa only [mul_comm δ] using ((div_lt_iff₀ hδ).mp hlt).le
    obtain ⟨X, inst, hx⟩ := exists_isExtremal_free (V := Fin n) nebot
    have hX : X.edgeFinset.card = extremalNumber n H := by
      simpa only [Fintype.card_fin] using card_edgeFinset_of_isExtremal_free hx
    obtain ⟨S, T, hS, hT, reg⟩ := exists_boundary_with_small_loss H X hlNat
    rw [Fintype.card_fin] at hS
    have hsc : (S.card : ℝ)^2 ≤ δ * n :=
      (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hS) _).trans hB
    have hTlocal : l * (∑ v ∈ T, X.degree v) ≤ 2 * X.edgeFinset.card := by
      convert! hT
    have hT' : l * (∑ v ∈ T, X.degree v) ≤ 2 * (q * n) :=
      hTlocal.trans (Nat.mul_le_mul_left 2 (hX ▸ bound n))
    have hTreal : (l : ℝ) * (↑(∑ v ∈ T, X.degree v) : ℝ) ≤ 2 * ((q : ℝ) * n) := by
      exact_mod_cast hT'
    have hweight : (↑(∑ v ∈ T, X.degree v) : ℝ) ≤ δ * n := by
      apply le_of_mul_le_mul_left _ hlpos
      calc
        _ ≤ 2 * ((q : ℝ) * n) := hTreal
        _ = (2 * (q : ℝ)) * n := by ring
        _ ≤ ((l : ℝ) * δ) * n := mul_le_mul_of_nonneg_right hlmul hnR.le
        _ = _ := by ring
    let e := (offBoundary X S T).edgeFinset.card
    have hcost : (X.edgeFinset.card : ℝ) ≤ (e : ℝ) +
        (↑(∑ v ∈ T, X.degree v) : ℝ) + (S.card : ℝ)^2 := by
      have hedge : X.edgeFinset.card ≤ e + (∑ v ∈ T, X.degree v) + S.card ^ 2 := by
        convert! offBoundary_edge_bound X S T
      exact_mod_cast hedge
    have hbig : b * (n : ℝ) < X.edgeFinset.card := by
      rw [hX]
      exact (lt_div_iff₀ hnR).mp hnlarge
    have hclean : a < (e : ℝ) / n := by
      apply (lt_div_iff₀ hnR).mpr
      dsimp [δ] at hsc hweight
      nlinarith only [hcost, hsc, hweight, hbig, mul_pos (sub_pos.mpr hab) hnR]
    have hevent := eventually_extremal_density_ge_of_gluing hnpos active hx.prop reg hclean
    obtain ⟨m, ha, he⟩ := (small.and_eventually hevent).exists
    exact (not_lt_of_ge he) ha
  obtain ⟨c, hc⟩ := tendsto_of_no_upcrossings (u := density) dense_univ crossings
    (isBoundedUnder_of_eventually_le upper)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall nonneg))
  refine ⟨c, ?_, hc⟩
  have hpos : (1 / 3 : ℝ) ≤ c := ge_of_tendsto hc (by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    change 1 / 3 ≤ (extremalNumber n H : ℝ) / n
    rw [le_div_iff₀ hnpos]
    have hb : n ≤ 3 * extremalNumber n H :=
      (show n ≤ 3 * (n / 2) by omega).trans
        (Nat.mul_le_mul_left 3 (extremal_linear_lower H edges (by omega)))
    have hr : (n : ℝ) ≤ 3 * (extremalNumber n H : ℝ) := by exact_mod_cast hb
    linarith)
  linarith

private lemma active_of_connected_cyclic {V : Type*} {H : SimpleGraph V}
    (conn : H.Connected) (cyclic : ¬ H.IsAcyclic) (v : V) : ∃ w, H.Adj v w := by
  rcases subsingleton_or_nontrivial V with hs | hs
  · exact (cyclic IsAcyclic.of_subsingleton).elim
  · exact conn.preconnected.exists_adj_of_nontrivial v

private lemma cyclic_induce_compl_leaf {V : Type*} [Fintype V] {H : SimpleGraph V}
    (cyclic : ¬ H.IsAcyclic) {v : V} (leaf : H.degree v = 1) :
    ¬ (H.induce ({v}ᶜ : Set V)).IsAcyclic := by
  obtain ⟨u, p, hp⟩ : ∃ (u : V) (p : H.Walk u u), p.IsCycle := by
    by_contra! hn
    exact cyclic hn
  obtain ⟨w, hvw, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp leaf
  have hno : v ∉ p.support := by
    intro hv
    have hr := hp.rotate hv
    generalize p.rotate v hv = r at hr
    cases r with
    | nil => exact hr.not_nil (by simp)
    | @cons _ x _ adj t =>
      have hx := huniq x adj
      subst x
      have hn : ¬ t.Nil := Walk.not_nil_of_ne hvw.ne.symm
      have hl := t.mk_penultimate_end_mem_edges hn
      have he : t.penultimate = w := huniq _ (t.adj_of_mem_edges hl).symm
      rw [he, Sym2.eq_swap] at hl
      exact ((Walk.isTrail_cons adj t).mp hr.isTrail).2 hl
  have hsub : ∀ w ∈ p.support, w ∈ ({v}ᶜ : Set V) := by
    intro w hw
    exact fun e => hno ((Set.mem_singleton_iff.mp e) ▸ hw)
  let r := p.induce ({v}ᶜ : Set V) hsub
  have hr : r.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce _).toHom)
    simpa [r] using hp
  exact fun forest => forest r hr

private lemma extend_copy_at_leaf {V W : Type*} [Fintype V] [Fintype W]
    {H : SimpleGraph V} {X : SimpleGraph W} {v : V} (leaf : H.degree v = 1)
    (hdeg : ∀ w, Fintype.card V ≤ X.degree w)
    (copy : (H.induce ({v}ᶜ : Set V)) ⊑ X) : H ⊑ X := by
  obtain ⟨p, hparent, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp leaf
  obtain ⟨f⟩ := copy
  let U : Set V := {v}ᶜ
  let parent : U := ⟨p, hparent.ne.symm⟩
  let used := univ.map f.toEmbedding
  have hsize : used.card < Fintype.card V := by
    simp only [used, Finset.card_map, Finset.card_univ]
    exact Fintype.card_lt_of_injective_of_notMem (f := fun x : U => x.val)
      Subtype.val_injective (b := v) (by simp [U])
  have hex : ∃ w ∈ X.neighborFinset (f parent), w ∉ used := by
    by_contra! h
    have hcard := Finset.card_le_card (show X.neighborFinset (f parent) ⊆ used from h)
    rw [card_neighborFinset_eq_degree] at hcard
    exact hsize.not_ge ((hdeg _).trans hcard)
  obtain ⟨y, hy, hynew⟩ := hex
  let g (u : V) : W := if hu : u = v then y else f ⟨u, hu⟩
  have hv : g v = y := by simp [g]
  have hg {u : V} (hu : u ≠ v) : g u = f ⟨u, hu⟩ := dif_neg hu
  have hadj {u : V} (h : H.Adj v u) : X.Adj (g v) (g u) := by
    have hu := huniq u h
    subst u
    rw [hv, hg hparent.ne.symm]
    exact ((mem_neighborFinset X _ _).mp hy).symm
  have hmem {u : V} (hu : u ≠ v) : g u ∈ used := by
    rw [hg hu]
    exact mem_map.mpr ⟨⟨u, hu⟩, mem_univ _, rfl⟩
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro u w h
    rcases eq_or_ne u v with rfl | hu
    · exact hadj h
    rcases eq_or_ne w v with rfl | hw
    · exact (hadj h.symm).symm
    rw [hg hu, hg hw]
    exact f.toHom.map_adj (show (H.induce U).Adj ⟨u, hu⟩ ⟨w, hw⟩ from h)
  · intro u w h
    change g u = g w at h
    by_cases hu : u = v
    · subst u
      by_cases hw : w = v
      · exact hw.symm
      · exfalso
        apply hynew
        rw [← hv, h]
        exact hmem hw
    · by_cases hw : w = v
      · subst w
        exfalso
        apply hynew
        rw [← hv, ← h]
        exact hmem hu
      · rw [hg hu, hg hw] at h
        exact congrArg Subtype.val (f.injective h)

private lemma extremalNumber_monotone_active {V : Type*} {H : SimpleGraph V}
    (active : ∀ v, ∃ w, H.Adj v w) : Monotone (extremalNumber · H) := by
  intro m n hmn
  rw [← Fintype.card_fin m, extremalNumber_le_iff (V := Fin m)]
  intro X _ free
  have h := card_edgeFinset_le_extremal_of_card_le active free (Fintype.card_fin m ▸ hmn)
  convert! h

private lemma extremal_le_after_leaf_pruned {V : Type*} [Fintype V] {H : SimpleGraph V}
    {v : V} (leaf : H.degree v = 1)
    (active : ∀ w, ∃ u, (H.induce ({v}ᶜ : Set V)).Adj w u) (n : ℕ) :
    extremalNumber n H ≤ extremalNumber n (H.induce ({v}ᶜ : Set V)) + Fintype.card V * n := by
  let J := H.induce ({v}ᶜ : Set V)
  induction n with
  | zero =>
    rw [← Fintype.card_fin 0, extremalNumber_le_iff (V := Fin 0)]
    intro X _ _
    have h := X.card_edgeFinset_le_card_choose_two
    simpa using h.trans (by simp : (Fintype.card (Fin 0)).choose 2 ≤ _)
  | succ n ih =>
    rw [← Fintype.card_fin (n + 1), extremalNumber_le_iff (V := Fin (n + 1))]
    intro X _ hfree
    by_cases low : ∃ w, X.degree w < Fintype.card V
    · obtain ⟨x, hx⟩ := low
      have hdel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree x
      rw [card_edgeFinset_deleteIncidenceSet, Fintype.card_fin, Nat.add_sub_cancel] at hdel
      rw [Fintype.card_fin, Nat.mul_succ]
      have hm := extremalNumber_monotone_active active (Nat.le_succ n)
      change extremalNumber n (H.induce ({v}ᶜ : Set V)) ≤
        extremalNumber (n + 1) (H.induce ({v}ᶜ : Set V)) at hm
      omega
    · have hdeg (w : Fin (n + 1)) : Fintype.card V ≤ X.degree w :=
        Nat.le_of_not_gt fun h => low ⟨w, h⟩
      by_contra! h
      have h' : extremalNumber (Fintype.card (Fin (n + 1))) J < X.edgeFinset.card :=
        lt_of_le_of_lt (Nat.le_add_right _ _) h
      have hc := IsContained.of_extremalNumber_lt_card_edgeFinset h'
      have hc' : H ⊑ X := extend_copy_at_leaf leaf (fun w => by convert! hdeg w) hc
      exact hfree hc'

private lemma extremal_limit_of_leaf_pruned {V : Type*} [Fintype V] {H : SimpleGraph V}
    {v : V} (leaf : H.degree v = 1)
    (active : ∀ w, ∃ u, (H.induce ({v}ᶜ : Set V)).Adj w u) {a c : ℝ}
    (ha : 1 < a) (fit : HasExtremalLimit (H.induce ({v}ᶜ : Set V)) a c) :
    HasExtremalLimit H a c := by
  unfold HasExtremalLimit at *
  have hu := fit.add (linear_term_at_higher_power ha (Fintype.card V : ℝ))
  rw [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le fit hu
  · intro n
    have h : extremalNumber n (H.induce ({v}ᶜ : Set V)) ≤ extremalNumber n H :=
      (Copy.induce H _).isContained.extremalNumber_le
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr h) (by positivity)
  · intro n
    dsimp
    rw [← add_div]
    have h := extremal_le_after_leaf_pruned leaf active n
    have hR : (extremalNumber n H : ℝ) ≤
        (extremalNumber n (H.induce ({v}ᶜ : Set V)) : ℝ) + (Fintype.card V : ℝ) * n := by
      exact_mod_cast h
    exact div_le_div_of_nonneg_right hR (by positivity)

private lemma connected_cyclic_limit_from_min_degree
    (core : ∀ {V : Type} [Fintype V] (H : SimpleGraph V), H.IsBipartite → H.Connected →
      ¬ H.IsAcyclic → (∀ v, 2 ≤ H.degree v) →
      ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ HasExtremalLimit H a c) :
    ∀ {V : Type} [Fintype V] (H : SimpleGraph V), H.IsBipartite → H.Connected →
      ¬ H.IsAcyclic → ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ HasExtremalLimit H a c := by
  have aux (k : ℕ) : ∀ (V : Type) [Fintype V], Fintype.card V = k →
      ∀ (H : SimpleGraph V), H.IsBipartite → H.Connected → ¬ H.IsAcyclic →
        ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ HasExtremalLimit H a c := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro V _ hV H bip conn cyclic
      by_cases hdeg : ∀ v, 2 ≤ H.degree v
      · exact core H bip conn cyclic hdeg
      · obtain ⟨v, hv⟩ := not_forall.mp hdeg
        have hpos := (H.degree_pos_iff_exists_adj v).mpr (active_of_connected_cyclic conn cyclic v)
        have leaf : H.degree v = 1 := by omega
        let U : Set V := {v}ᶜ
        let J := H.induce U
        have hJb : J.IsBipartite := bip.of_hom ((Embedding.induce U).toHom)
        have hJconn : J.Connected := conn.induce_compl_singleton_of_degree_eq_one leaf
        have hJcyclic : ¬ J.IsAcyclic := cyclic_induce_compl_leaf cyclic leaf
        have hlt : Fintype.card U < k := by
          rw [← hV]
          exact Fintype.card_lt_of_injective_of_notMem (f := fun x : U => x.val)
            Subtype.val_injective (b := v) (by simp [U])
        obtain ⟨a, c, ha, hc, fit⟩ := ih (Fintype.card U) hlt U rfl J hJb hJconn hJcyclic
        exact ⟨a, c, ha, hc, extremal_limit_of_leaf_pruned leaf
          (active_of_connected_cyclic hJconn hJcyclic) ha fit⟩
  intro V _ H
  exact aux (Fintype.card V) V rfl H

-- Affine polarity graphs have at most one common neighbor for a distinct pair.
private def affinePolarity (K : Type*) [Field K] : SimpleGraph (K × K) where
  Adj a b := a ≠ b ∧ a.1 * b.1 = a.2 + b.2
  symm.symm a b h := ⟨h.1.symm, by simpa only [mul_comm, add_comm] using h.2⟩
  loopless.irrefl a h := h.1 rfl

private lemma affinePolarity_common_neighbor {K : Type*} [Field K] {a b u v : K × K}
    (hab : a ≠ b) (hau : (affinePolarity K).Adj a u)
    (hbu : (affinePolarity K).Adj b u) (hav : (affinePolarity K).Adj a v)
    (hbv : (affinePolarity K).Adj b v) : u = v := by
  change a ≠ u ∧ a.1 * u.1 = a.2 + u.2 at hau
  change b ≠ u ∧ b.1 * u.1 = b.2 + u.2 at hbu
  change a ≠ v ∧ a.1 * v.1 = a.2 + v.2 at hav
  change b ≠ v ∧ b.1 * v.1 = b.2 + v.2 at hbv
  have hfst : a.1 ≠ b.1 := by
    intro heq
    apply hab
    apply Prod.ext heq
    exact add_right_cancel (show a.2 + u.2 = b.2 + u.2 by rw [← hau.2, ← hbu.2, heq])
  have hzero : (a.1 - b.1) * (u.1 - v.1) = 0 := by
    linear_combination hau.2 - hbu.2 - hav.2 + hbv.2
  have heq : u.1 = v.1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hfst))
  apply Prod.ext heq
  exact add_left_cancel (show a.2 + u.2 = a.2 + v.2 by rw [← hau.2, ← hav.2, heq])

private lemma affinePolarity_free (K : Type*) [Field K] :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free (affinePolarity K) := by
  intro h
  let f := h.some
  have adj (i j : Fin 2) : (affinePolarity K).Adj (f (Sum.inl i)) (f (Sum.inr j)) :=
    f.toHom.map_rel' (Or.inl ⟨rfl, rfl⟩)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hne : f (Sum.inl 0) ≠ f (Sum.inl 1) :=
    fun heq => h01 (Sum.inl.inj (f.injective heq))
  have heq := affinePolarity_common_neighbor hne (adj 0 0) (adj 1 0) (adj 0 1) (adj 1 1)
  exact h01 (Sum.inr.inj (f.injective heq))

private lemma affinePolarity_degree {K : Type*} [Field K] [Fintype K] (a : K × K) :
    Fintype.card K - 1 ≤ (affinePolarity K).degree a := by
  let X := affinePolarity K
  let f : K → (↑(insert a (X.neighborFinset a)) : Type _) := fun b =>
    ⟨(b, a.1 * b - a.2), by
      by_cases h : a = (b, a.1 * b - a.2)
      · exact mem_insert.mpr (Or.inl h.symm)
      · apply mem_insert_of_mem
        exact mem_neighborFinset X a _ |>.mpr ⟨h, by ring⟩⟩
  have hi : Function.Injective f := fun _ _ h => congrArg (Prod.fst ∘ Subtype.val) h
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe, Finset.card_insert_of_notMem (X.notMem_neighborFinset_self a), card_neighborFinset_eq_degree] at hc
  change Fintype.card K - 1 ≤ X.degree a
  omega

private lemma fourCycle_extremal_prime_square {p : ℕ} (hp : p.Prime) :
    p ^ 2 * (p - 1) ≤ 2 * extremalNumber (p ^ 2) (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let X := affinePolarity (ZMod p)
  have hsum : p ^ 2 * (p - 1) ≤ ∑ v, X.degree v := calc
    _ = ∑ _ : ZMod p × ZMod p, (p - 1) := by
      simp only [sum_const, card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul, Nat.cast_id, pow_two]
    _ ≤ _ := sum_le_sum fun v _ => by
      simpa only [X, ZMod.card] using affinePolarity_degree (K := ZMod p) v
  rw [X.sum_degrees_eq_twice_card_edges] at hsum
  have hX := card_edgeFinset_le_extremalNumber (affinePolarity_free (ZMod p))
  rw [Fintype.card_prod, ZMod.card, ← pow_two] at hX
  exact hsum.trans (Nat.mul_le_mul_left 2 hX)

private lemma rectangular_extremal_bound {s t n : ℕ} (hs : 0 < s) (hn : 0 < n)
    {C : ℝ} (hC : 0 ≤ C) (ht : ((t - 1 : ℕ) : ℝ) ≤ C ^ s) :
    (extremalNumber n (completeBipartiteGraph (Fin s) (Fin t)) : ℝ) ≤
      (C * (n : ℝ) ^ (2 - 1 / (s : ℝ)) + (s - 1 : ℕ) * (n : ℝ)) / 2 := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro X _ free
  rw [Fintype.card_fin n]
  linarith only [rectangular_edge_bound hs hn X free hC ht]

private abbrev fourCycle := completeBipartiteGraph (Fin 2) (Fin 2)

private lemma fourCycle_normalized_upper {n : ℕ} (hn : 0 < n) :
    (extremalNumber n fourCycle : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ≤
      1 / 2 + ((1 / 2 : ℝ) * n) / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have h := rectangular_extremal_bound (s := 2) (t := 2) (by decide) hn
    (C := 1) (by norm_num) (by norm_num)
  norm_num at h
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpow : (0 : ℝ) < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hnR _
  rw [div_le_iff₀ hpow]
  calc
    _ ≤ ((n : ℝ) ^ (3 / 2 : ℝ) + n) / 2 := by
      simpa only [show (2 : ℝ) - 1 / 2 = 3 / 2 by norm_num] using h
    _ = _ := by field_simp

private lemma fourCycle_normalized_lower_prime_square {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ)⁻¹) / 2 ≤ (extremalNumber (p ^ 2) fourCycle : ℝ) / ((p ^ 2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have h := fourCycle_extremal_prime_square hp
  have hR : (p : ℝ) ^ 2 * (p - 1) ≤ 2 * (extremalNumber (p ^ 2) fourCycle : ℝ) := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr h
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one, Nat.cast_ofNat]
      using hcast
  have he : ((p ^ 2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) = (p : ℝ) ^ (3 : ℕ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_mul hpR.le]
    norm_num [Real.rpow_natCast]
  rw [he, le_div_iff₀ (by positivity)]
  have halg : (1 - (p : ℝ)⁻¹) / 2 * (p : ℝ) ^ (3 : ℕ) = (p : ℝ) ^ 2 * (p - 1) / 2 := by
    field_simp
  rw [halg]
  linarith only [hR]

private lemma tendsto_prime_squares_atTop :
    Tendsto (fun k : ℕ => Nat.nth Nat.Prime k ^ 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [eventually_ge_atTop M] with k hk
  exact hk.trans ((Nat.le_add_right k 2).trans
    ((Nat.add_two_le_nth_prime k).trans (Nat.le_self_pow (by decide) _)))

private lemma fourCycle_limit_prime_squares :
    Tendsto (fun k : ℕ =>
      (extremalNumber (Nat.nth Nat.Prime k ^ 2) fourCycle : ℝ) /
        ((Nat.nth Nat.Prime k ^ 2 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  let p := Nat.nth Nat.Prime
  have hp : Tendsto p atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with k hk
    exact hk.trans ((Nat.le_add_right k 2).trans (Nat.add_two_le_nth_prime k))
  have hlo : Tendsto (fun k => (1 - (p k : ℝ)⁻¹) / 2) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := (tendsto_inv_atTop_nhds_zero_nat.comp hp :
      Tendsto (fun k => (p k : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)))
    simpa only [sub_zero, Function.comp_apply] using (tendsto_const_nhds.sub h).div_const 2
  have hup := (linear_term_at_higher_power (a := 3 / 2) (by norm_num) (1 / 2)).comp tendsto_prime_squares_atTop
  have hhi : Tendsto (fun k =>
      1 / 2 + ((1 / 2 : ℝ) * (p k ^ 2 : ℕ)) / ((p k ^ 2 : ℕ) : ℝ) ^ (3 / 2 : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [add_zero, Function.comp_apply] using tendsto_const_nhds.add hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · exact fun k => fourCycle_normalized_lower_prime_square (Nat.prime_nth_prime k)
  · exact fun k => fourCycle_normalized_upper (pow_pos (Nat.prime_nth_prime k).pos _)

private lemma fourCycle_active (v : Fin 2 ⊕ Fin 2) : ∃ w, fourCycle.Adj v w := by
  cases v with
  | inl i => exact ⟨Sum.inr 0, Or.inl ⟨rfl, rfl⟩⟩
  | inr i => exact ⟨Sum.inl 0, Or.inr ⟨rfl, rfl⟩⟩

private lemma fourCycle_extremal_mono : Monotone (fun n => extremalNumber n fourCycle) := by
  intro m n hmn
  rw [← Fintype.card_fin m, extremalNumber_le_iff]
  intro X _ free
  convert! card_edgeFinset_le_extremal_of_card_le fourCycle_active free (by simpa using hmn)

private lemma fourCycle_normalized_lower_of_prime_square_le {p n : ℕ} (hp : p.Prime)
    (hpn : p ^ 2 ≤ n) :
    ((1 - (p : ℝ)⁻¹) / 2) * ((((p ^ 2 : ℕ) : ℝ) / n) ^ (3 / 2 : ℝ)) ≤
      (extremalNumber n fourCycle : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hp0 : (0 : ℝ) < ((p ^ 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (pow_pos hp.pos _)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr ((pow_pos hp.pos 2).trans_le hpn)
  rw [Real.div_rpow hp0.le hn0.le, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := (le_div_iff₀ (Real.rpow_pos_of_pos hp0 _)).mp (fourCycle_normalized_lower_prime_square hp)
  exact h.trans (Nat.cast_le.mpr (fourCycle_extremal_mono hpn))

private lemma fourCycle_limit_of_prime_approximation (p : ℕ → ℕ)
    (hp : ∀ᶠ n in atTop, (p n).Prime ∧ p n ^ 2 ≤ n)
    (hP : Tendsto p atTop atTop)
    (hsize : Tendsto (fun n => ((p n ^ 2 : ℕ) : ℝ) / n) atTop (𝓝 1)) :
    HasExtremalLimit fourCycle (3 / 2) (1 / 2) := by
  have hinv : Tendsto (fun n => (p n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_nhds_zero_nat.comp hP
  have hlo₁ : Tendsto (fun n => (1 - (p n : ℝ)⁻¹) / 2) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hinv).div_const 2
  have hlo₂ : Tendsto (fun n => (((p n ^ 2 : ℕ) : ℝ) / n) ^ (3 / 2 : ℝ)) atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using hsize.rpow_const (Or.inl one_ne_zero)
  have hlo := hlo₁.mul hlo₂
  rw [mul_one] at hlo
  have hhi := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add
    (linear_term_at_higher_power (a := 3 / 2) (by norm_num) (1 / 2))
  rw [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hp] with n hn using fourCycle_normalized_lower_of_prime_square_le hn.1 hn.2
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn using fourCycle_normalized_upper hn

private lemma two_side_exponent_fixed {V : Type*} {J : SimpleGraph V} {t : ℕ}
    (h₁ : fourCycle ⊑ J) (h₂ : J ⊑ completeBipartiteGraph (Fin 2) (Fin t)) {a c : ℝ}
    (hc : 0 < c) (fit : HasExtremalLimit J a c) : a = 3 / 2 := by
  refine le_antisymm ?_ ?_
  · by_contra! ha
    let C := Real.sqrt ((t - 1 : ℕ) : ℝ)
    have hC : 0 ≤ C := Real.sqrt_nonneg _
    have ht : ((t - 1 : ℕ) : ℝ) ≤ C ^ 2 :=
      (Real.sq_sqrt (Nat.cast_nonneg _)).ge
    have slope : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (3 / 2 - a)) atTop (𝓝 0) := by
      have lim := (tendsto_rpow_neg_atTop (show 0 < a - 3 / 2 by linarith)).comp
        (tendsto_natCast_atTop_atTop : Tendsto ((↑) : ℕ → ℝ) atTop atTop)
      simpa only [neg_sub, mul_zero, Function.comp_apply] using lim.const_mul C
    have lin := linear_term_at_higher_power (a := a) (by linarith) 1
    have hup := (slope.add lin).div_const 2
    simp only [add_zero, zero_div] at hup
    have h : c ≤ 0 := le_of_tendsto_of_tendsto fit hup (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have bound := rectangular_extremal_bound (s := 2) (by decide) hn hC ht
      have hcast := Nat.cast_le (α := ℝ) |>.mpr (h₂.extremalNumber_le (n := n))
      have hdiv := div_le_div_of_nonneg_right (hcast.trans bound)
        (Real.rpow_pos_of_pos hnR a).le
      refine hdiv.trans_eq ?_
      simp only [Nat.cast_ofNat, Nat.reduceSub, Nat.cast_one, one_mul,
        show (2 : ℝ) - 1 / 2 = 3 / 2 by norm_num]
      rw [div_right_comm (C * _ + _), add_div, mul_div_assoc, ← Real.rpow_sub hnR])
    exact hc.not_ge h
  · by_contra! ha
    have zero := extremal_limit_at_higher_power ha fit
    have h := le_of_tendsto_of_tendsto fourCycle_limit_prime_squares
      (zero.comp tendsto_prime_squares_atTop)
      (Eventually.of_forall fun k => div_le_div_of_nonneg_right
        (Nat.cast_le.mpr (h₁.extremalNumber_le (n := Nat.nth Nat.Prime k ^ 2))) (by positivity))
    norm_num at h

private lemma fourCycle_limit_fixed {a c : ℝ} (hc : 0 < c) (fit : HasExtremalLimit fourCycle a c) :
    a = 3 / 2 ∧ c = 1 / 2 := by
  have ha := two_side_exponent_fixed IsContained.rfl IsContained.rfl hc fit
  subst a
  refine ⟨rfl, ?_⟩
  exact tendsto_nhds_unique (fit.comp tendsto_prime_squares_atTop) fourCycle_limit_prime_squares

-- A maximal packing of small sets gives a small set meeting the entire family.
private lemma exists_disjoint_family_or_cover {V : Type*} (P : Finset V → Prop)
    (r k : ℕ) (hP : ∀ S, P S → S.card ≤ r) :
    (∃ S : Fin k → Finset V, (∀ i, P (S i)) ∧ Pairwise fun i j => Disjoint (S i) (S j)) ∨
      ∃ T : Finset V, T.card ≤ r * k ∧ ∀ S, P S → ¬ Disjoint T S := by
  induction k generalizing P with
  | zero =>
    exact Or.inl ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    by_cases hnonempty : ∃ S, P S
    · obtain ⟨A, hA⟩ := hnonempty
      obtain ⟨S, hS, hd⟩ | ⟨T, hT, hhit⟩ :=
        ih (fun B => P B ∧ Disjoint A B) (fun B hB => hP B hB.1)
      · left
        refine ⟨Fin.cons A S, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hA
          · simpa using (hS j).1
        · intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · intro j
            refine Fin.cases ?_ (fun j => ?_) j
            · intro h; exact (h rfl).elim
            · intro _; simpa using (hS j).2
          · intro j
            refine Fin.cases ?_ (fun j => ?_) j
            · intro _; simpa using (hS i).2.symm
            · intro h; exact hd (by simpa using h)
      · right
        refine ⟨A ∪ T, ?_, ?_⟩
        · rw [Nat.mul_succ, add_comm (r * k)]
          exact Finset.card_union_le _ _ |>.trans (Nat.add_le_add (hP A hA) hT)
        · intro B hB hab
          rw [Finset.disjoint_union_left] at hab
          exact hhit B ⟨hB, hab.1⟩ hab.2
    · right
      exact ⟨∅, by simp, fun S hS => (hnonempty ⟨S, hS⟩).elim⟩

private def squareBouquet (k : ℕ) : SimpleGraph (Option (Fin k × Fin 3)) where
  Adj a b := match a, b with
    | none, none => False
    | none, some (_, i) | some (_, i), none => i ≠ 1
    | some (j, i), some (l, h) => j = l ∧ ((i = 1 ∧ h ≠ 1) ∨ (i ≠ 1 ∧ h = 1))
  symm.symm a b h := by
    rcases a with _ | ⟨j, i⟩ <;> rcases b with _ | ⟨l, s⟩
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  loopless.irrefl a h := by
    rcases a with _ | ⟨i, j⟩
    · exact h
    · exact h.2.elim (fun h => h.2 h.1) (fun h => h.1 h.2)

private def SquareAt {V : Type*} (X : SimpleGraph V) (u : V) (S : Finset V) : Prop :=
  ∃ e : Fin 3 ↪ V, S = univ.map e ∧ u ∉ S ∧
    X.Adj u (e 0) ∧ X.Adj (e 0) (e 1) ∧ X.Adj (e 1) (e 2) ∧ X.Adj (e 2) u

private lemma squareAt_of_vertices {V : Type*} {X : SimpleGraph V} {u a b c : V}
    (hu : u ∉ ({a, b, c} : Finset V)) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h₁ : X.Adj u a) (h₂ : X.Adj a b) (h₃ : X.Adj b c) (h₄ : X.Adj c u) :
    SquareAt X u {a, b, c} := by
  let f : Fin 3 → V := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let e : Fin 3 ↪ V := ⟨f, hf⟩
  refine ⟨e, ?_, hu, h₁, h₂, h₃, h₄⟩
  ext v
  constructor
  · intro hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact mem_map.mpr ⟨0, mem_univ _, rfl⟩
    · exact mem_map.mpr ⟨1, mem_univ _, rfl⟩
    · exact mem_map.mpr ⟨2, mem_univ _, rfl⟩
  · intro hv
    obtain ⟨i, _, rfl⟩ := mem_map.mp hv
    fin_cases i <;> simp [e, f]

private lemma squareBouquet_contained_of_squares {V : Type*} {X : SimpleGraph V} {u : V}
    {k : ℕ} {S : Fin k → Finset V} (hS : ∀ i, SquareAt X u (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) : squareBouquet k ⊑ X := by
  choose e he hroot h₁ h₂ h₃ h₄ using hS
  let f : Option (Fin k × Fin 3) → V := fun x => x.elim u (fun z => e z.1 z.2)
  have hmem (i : Fin k) (j : Fin 3) : e i j ∈ S i :=
    (he i).symm ▸ mem_map.mpr ⟨j, mem_univ _, rfl⟩
  have hside (i : Fin k) (j : Fin 3) (hj : j ≠ 1) :
      X.Adj u (e i j) ∧ X.Adj (e i 1) (e i j) := by
    fin_cases j
    · exact ⟨h₁ i, (h₂ i).symm⟩
    · exact (hj rfl).elim
    · exact ⟨(h₄ i).symm, h₃ i⟩
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · rintro (_ | ⟨i, a⟩) (_ | ⟨j, b⟩) h
    · exact h.elim
    · exact (hside j b h).1
    · exact (hside i a h).1.symm
    · change i = j ∧ ((a = 1 ∧ b ≠ 1) ∨ (a ≠ 1 ∧ b = 1)) at h
      obtain ⟨rfl, hab | hab⟩ := h
      · obtain ⟨rfl, hb⟩ := hab
        exact (hside i b hb).2
      · obtain ⟨ha, rfl⟩ := hab
        exact (hside i a ha).2.symm
  · rintro (_ | ⟨i, a⟩) (_ | ⟨j, b⟩) h
    · rfl
    · change u = e j b at h
      exact (hroot j (h.symm ▸ hmem j b)).elim
    · change e i a = u at h
      exact (hroot i (h ▸ hmem i a)).elim
    · change e i a = e j b at h
      have hij : i = j := by
        by_contra hne
        exact (Finset.disjoint_left.mp (hd hne)) (hmem i a) (h.symm ▸ hmem j b)
      subst j
      cases (e i).injective h
      rfl

private lemma exists_square_cover {V : Type*} {X : SimpleGraph V} {k : ℕ}
    (free : (squareBouquet k).Free X) (u : V) :
    ∃ T : Finset V, T.card ≤ 3 * k ∧ ∀ S, SquareAt X u S → ¬ Disjoint T S := by
  apply (exists_disjoint_family_or_cover (SquareAt X u) 3 k ?_).resolve_left
  · rintro ⟨S, hS, hd⟩
    exact free (squareBouquet_contained_of_squares hS hd)
  · rintro S ⟨e, rfl, _⟩
    simp

private noncomputable def commonNeighborFinset {V : Type*} [Fintype V]
    (X : SimpleGraph V) (a b : V) : Finset V :=
  (X.commonNeighbors a b).toFinset

private lemma mem_commonNeighborFinset {V : Type*} [Fintype V] {X : SimpleGraph V} {a b v : V} :
    v ∈ commonNeighborFinset X a b ↔ X.Adj a v ∧ X.Adj b v := by
  simp [commonNeighborFinset, mem_commonNeighbors]

private def RichPair {V : Type*} [Fintype V] (X : SimpleGraph V) (k : ℕ)
    (u : V) (S : Finset V) : Prop :=
  ∃ a b, a ≠ b ∧ S = {a, b} ∧ X.Adj u a ∧ X.Adj u b ∧ 3 * k + 1 < (commonNeighborFinset X a b).card

-- Use Hall's theorem to complete disjoint pairs to squares with distinct new vertices.
private lemma squareBouquet_contained_of_rich_pairs {V : Type*} [Fintype V]
    {X : SimpleGraph V} {k : ℕ} {u : V} {S : Fin k → Finset V}
    (hS : ∀ i, RichPair X k u (S i)) (hd : Pairwise fun i j => Disjoint (S i) (S j)) :
    squareBouquet k ⊑ X := by
  choose a b hne hsets ha hb hbig using hS
  have hcard (i : Fin k) : (S i).card ≤ 2 := by simp [hsets i, hne i]
  let B := insert u (univ.biUnion S)
  have hB : B.card ≤ 2 * k + 1 := calc
    _ ≤ (univ.biUnion S).card + 1 := card_insert_le _ _
    _ ≤ (∑ i, (S i).card) + 1 := Nat.add_le_add_right card_biUnion_le _
    _ ≤ (∑ _ : Fin k, 2) + 1 := Nat.add_le_add_right (sum_le_sum fun i _ => hcard i) _
    _ = _ := by simp [Nat.mul_comm]
  let T (i : Fin k) := commonNeighborFinset X (a i) (b i) \ B
  have hT (i : Fin k) : k ≤ (T i).card := by
    dsimp only [T]
    rw [card_sdiff]
    have hsub : (B ∩ commonNeighborFinset X (a i) (b i)).card ≤ B.card :=
      card_le_card inter_subset_left
    have := hbig i
    omega
  obtain ⟨g, hg, hmem⟩ := (all_card_le_biUnion_card_iff_existsInjective' T).mp (by
    intro I
    by_cases hI : I.Nonempty
    · obtain ⟨i, hi⟩ := hI
      calc
        _ ≤ k := by simpa using (card_le_univ I)
        _ ≤ (T i).card := hT i
        _ ≤ _ := card_le_card (fun x hx => mem_biUnion.mpr ⟨i, hi, hx⟩)
    · simp [not_nonempty_iff_eq_empty.mp hI])
  have havoid (i : Fin k) : g i ∉ B := (mem_sdiff.mp (hmem i)).2
  have hSB (i : Fin k) : S i ⊆ B := fun v hv =>
    mem_insert_of_mem (mem_biUnion.mpr ⟨i, mem_univ _, hv⟩)
  have hin (i : Fin k) : X.Adj (a i) (g i) ∧ X.Adj (b i) (g i) := by
    exact mem_commonNeighborFinset.mp (mem_sdiff.mp (hmem i)).1
  have hamem (i : Fin k) : a i ∈ S i := by simp [hsets i]
  have hbmem (i : Fin k) : b i ∈ S i := by simp [hsets i]
  let U (i : Fin k) := insert (g i) (S i)
  apply squareBouquet_contained_of_squares (S := U) (u := u)
  · intro i
    have hay : a i ≠ g i := fun h => havoid i (h ▸ hSB i (hamem i))
    have hyb : g i ≠ b i := fun h => havoid i (h.symm ▸ hSB i (hbmem i))
    have hroot : u ∉ ({a i, g i, b i} : Finset V) := by
      have huy : u ≠ g i := fun h => havoid i (h ▸ mem_insert_self _ _)
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨(ha i).ne, huy, (hb i).ne⟩
    have h := squareAt_of_vertices hroot hay (hne i) hyb (ha i) (hin i).1 (hin i).2.symm (hb i).symm
    have heq : ({a i, g i, b i} : Finset V) = U i := by
      change ({a i, g i, b i} : Finset V) = insert (g i) (S i)
      rw [hsets i, insert_comm]
    exact heq ▸ h
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    rcases mem_insert.mp hvi with rfl | hvi <;> rcases mem_insert.mp hvj with h | hvj
    · exact hij (hg h)
    · exact havoid i (hSB j hvj)
    · exact havoid j (h ▸ hSB i hvi)
    · exact (Finset.disjoint_left.mp (hd hij)) hvi hvj

private lemma exists_rich_pair_cover {V : Type*} [Fintype V] {X : SimpleGraph V} {k : ℕ}
    (free : (squareBouquet k).Free X) (u : V) :
    ∃ R : Finset V, R.card ≤ 2 * k ∧ ∀ S, RichPair X k u S → ¬ Disjoint R S := by
  apply (exists_disjoint_family_or_cover (RichPair X k u) 2 k ?_).resolve_left
  · rintro ⟨S, hS, hd⟩
    exact free (squareBouquet_contained_of_rich_pairs hS hd)
  · rintro S ⟨a, b, hab, rfl, _⟩
    simp [hab]

private def eraseMarkedEdges {V : Type*} (X : SimpleGraph V) (T : V → Finset V) : SimpleGraph V where
  Adj u v := X.Adj u v ∧ v ∉ T u ∧ u ∉ T v
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl _ h := X.irrefl h.1

private lemma card_edges_eraseMarkedEdges {V : Type*} [Fintype V]
    (X : SimpleGraph V) (T : V → Finset V) :
    X.edgeFinset.card ≤ (eraseMarkedEdges X T).edgeFinset.card + ∑ u, (T u).card := by
  let Y := eraseMarkedEdges X T
  let S (u : V) := (T u).image (fun v => s(u, v))
  have hsub : X.edgeFinset ⊆ Y.edgeFinset ∪ univ.biUnion S := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      have ha : X.Adj u v := mem_edgeFinset.mp he
      by_cases hu : v ∈ T u
      · exact mem_union_right _ (mem_biUnion.mpr ⟨u, mem_univ _, mem_image_of_mem _ hu⟩)
      by_cases hv : u ∈ T v
      · have hm : s(v, u) ∈ univ.biUnion S :=
          mem_biUnion.mpr ⟨v, mem_univ _, mem_image_of_mem _ hv⟩
        exact mem_union_right _ (by simpa only [Sym2.eq_swap] using hm)
      exact mem_union_left _ (mem_edgeFinset.mpr ⟨ha, hu, hv⟩)
  calc
    _ ≤ (Y.edgeFinset ∪ univ.biUnion S).card := card_le_card hsub
    _ ≤ Y.edgeFinset.card + (univ.biUnion S).card := card_union_le _ _
    _ ≤ Y.edgeFinset.card + ∑ u, (S u).card := Nat.add_le_add_left card_biUnion_le _
    _ ≤ _ := Nat.add_le_add_left (sum_le_sum fun u _ => card_image_le) _

private lemma exists_fourCycle_free_subgraph_of_squareBouquet_free {V : Type*} [Fintype V]
    {X : SimpleGraph V} {k : ℕ} (free : (squareBouquet k).Free X) :
    ∃ Y : SimpleGraph V, fourCycle.Free Y ∧
      X.edgeFinset.card ≤ Y.edgeFinset.card + (2 * k + (3 * k + 3 * k * (3 * k + 1))) * Fintype.card V := by
  choose B hB hhit using exists_square_cover free
  choose R hR hrich using exists_rich_pair_cover free
  -- Mark the common neighbors of each opposite vertex of small codegree in the cover.
  let L (u v : V) := if (commonNeighborFinset X u v).card ≤ 3 * k + 1
    then commonNeighborFinset X u v else ∅
  let T (u : V) := R u ∪ (B u ∪ (B u).biUnion (L u))
  let Y := eraseMarkedEdges X T
  have hL (u v : V) : (L u v).card ≤ 3 * k + 1 := by
    dsimp [L]
    split_ifs <;> simp_all
  have hT (u : V) : (T u).card ≤ 2 * k + (3 * k + 3 * k * (3 * k + 1)) := by
    have hBi : ((B u).biUnion (L u)).card ≤ 3 * k * (3 * k + 1) := calc
      _ ≤ ∑ v ∈ B u, (L u v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ B u, (3 * k + 1) := sum_le_sum fun v _ => hL u v
      _ = (B u).card * (3 * k + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (hB u)
    exact (card_union_le _ _).trans (Nat.add_le_add (hR u)
      ((card_union_le _ _).trans (Nat.add_le_add (hB u) hBi)))
  refine ⟨Y, ?_, (card_edges_eraseMarkedEdges X T).trans ?_⟩
  · rintro ⟨f⟩
    let u := f (Sum.inl 0)
    let a := f (Sum.inr 0)
    let b := f (Sum.inl 1)
    let c := f (Sum.inr 1)
    have hadj (i j : Fin 2) : Y.Adj (f (Sum.inl i)) (f (Sum.inr j)) :=
      f.toHom.map_rel' (Or.inl ⟨rfl, rfl⟩)
    have hua : Y.Adj u a := hadj 0 0
    have hba : Y.Adj b a := hadj 1 0
    have hbc : Y.Adj b c := hadj 1 1
    have huc : Y.Adj u c := hadj 0 1
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hub : u ≠ b := fun h => h01 (Sum.inl.inj (f.injective h))
    have hac : a ≠ c := fun h => h01 (Sum.inr.inj (f.injective h))
    have hs := squareAt_of_vertices (X := X) (show u ∉ ({a, b, c} : Finset V) by
      simpa only [mem_insert, mem_singleton, not_or] using ⟨hua.ne, hub, huc.ne⟩)
      hba.ne.symm hac hbc.ne hua.1 hba.1.symm hbc.1 huc.1.symm
    obtain ⟨v, hv, hvS⟩ := Finset.not_disjoint_iff.mp (hhit u _ hs)
    simp only [mem_insert, mem_singleton] at hvS
    rcases hvS with rfl | rfl | rfl
    · exact hua.2.1 (mem_union_right _ (mem_union_left _ hv))
    · by_cases hlow : (commonNeighborFinset X u b).card ≤ 3 * k + 1
      · have ha : a ∈ L u b := by
          dsimp only [L]
          rw [if_pos hlow, mem_commonNeighborFinset]
          exact ⟨hua.1, hba.1⟩
        exact hua.2.1 (mem_union_right _ (mem_union_right _ (mem_biUnion.mpr ⟨b, hv, ha⟩)))
      · have hr : RichPair X k a {u, b} := ⟨u, b, hub, rfl, hua.1.symm, hba.1.symm,
          lt_of_not_ge hlow⟩
        obtain ⟨w, hw, hwS⟩ := Finset.not_disjoint_iff.mp (hrich a _ hr)
        simp only [mem_insert, mem_singleton] at hwS
        rcases hwS with rfl | rfl
        · exact hua.2.2 (mem_union_left _ hw)
        · exact hba.2.2 (mem_union_left _ hw)
    · exact huc.2.1 (mem_union_right _ (mem_union_left _ hv))
  · apply Nat.add_le_add_left
    calc
      _ ≤ ∑ _u : V, (2 * k + (3 * k + 3 * k * (3 * k + 1))) := sum_le_sum fun u _ => hT u
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, mul_comm]

private lemma squareBouquet_extremal_upper (k n : ℕ) :
    extremalNumber n (squareBouquet k) ≤ extremalNumber n fourCycle +
      (2 * k + (3 * k + 3 * k * (3 * k + 1))) * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro X _ free
  obtain ⟨Y, hY, hsize⟩ := exists_fourCycle_free_subgraph_of_squareBouquet_free free
  have hle := hsize.trans (Nat.add_le_add_right (card_edgeFinset_le_extremalNumber hY) _)
  convert! hle using 1
  congr 1
  ext e
  simp only [mem_edgeFinset]

private lemma fourCycle_contained_squareBouquet {k : ℕ} (hk : 0 < k) :
    fourCycle ⊑ squareBouquet k := by
  let i : Fin k := ⟨0, hk⟩
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{none, some (i, 1)}, {some (i, 0), some (i, 2)}, by simp, ?_, ?_⟩
  · have hne : (0 : Fin 3) ≠ 2 := by decide
    simp [hne]
  · intro a ha b hb
    simp only [mem_coe, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (by decide : (0 : Fin 3) ≠ 1)
    · exact (by decide : (2 : Fin 3) ≠ 1)
    · exact ⟨rfl, Or.inl ⟨rfl, by decide⟩⟩
    · exact ⟨rfl, Or.inl ⟨rfl, by decide⟩⟩

private lemma squareBouquet_limit_of_fourCycle {k : ℕ} (hk : 0 < k) {a c : ℝ}
    (ha : 1 < a) (fit : HasExtremalLimit fourCycle a c) :
    HasExtremalLimit (squareBouquet k) a c := by
  let K := 2 * k + (3 * k + 3 * k * (3 * k + 1))
  have hup := fit.add (linear_term_at_higher_power ha (K : ℝ))
  rw [add_zero] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le fit hup
  · intro n
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (fourCycle_contained_squareBouquet hk).extremalNumber_le)
      (by positivity)
  · intro n
    dsimp only []
    rw [← add_div]
    have hnat : extremalNumber n (squareBouquet k) ≤ extremalNumber n fourCycle + K * n :=
      squareBouquet_extremal_upper k n
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnat) (by positivity)

private lemma cyclic_exponent_gt_one {V : Type*} [Fintype V] {H : SimpleGraph V}
    (cyclic : ¬ H.IsAcyclic) {a c : ℝ} (fit : HasExtremalLimit H a c) : 1 < a := by
  have impossible (d : ℝ) (lim : HasExtremalLimit H 1 d) : False := by
    unfold HasExtremalLimit at lim
    simp only [Real.rpow_one] at lim
    have low := tendsto_atTop.mp (cyclic_density_diverges cyclic) (d + 1)
    have high := (tendsto_order.mp lim).2 (d + 1) (by linarith)
    obtain ⟨_, hlo, hhi⟩ := (low.and high).exists
    exact (not_lt_of_ge hlo) hhi
  by_contra! h
  rcases h.lt_or_eq with h | rfl
  · exact impossible 0 (extremal_limit_at_higher_power h fit)
  · exact impossible c fit

theorem OMA.solution : type_of% @Erdos713.erdos_713.parts.i := by
  intro q G bip edges
  have hq : 0 < q := by
    by_contra! hz
    have heq : q = 0 := by omega
    subst q
    have hbot : G = ⊥ := by
      ext v
      exact Fin.elim0 v
    rw [edgeFinset_eq_empty.mpr hbot] at edges
    simp at edges
  obtain ⟨k, H, hbip, hcard, hactive, hstable⟩ := remove_isolated_vertices G bip
  have hedges : 2 ≤ H.edgeFinset.card := hcard.symm ▸ edges
  have hlimit : ∃ α c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ α) atTop (𝓝 c) := by
    have active (v : Fin k) : ∃ w, H.Adj v w :=
      H.mem_support_iff_not_isIsolated.mpr (hactive v)
    by_cases forest : H.IsAcyclic
    · obtain ⟨c, hc, fit⟩ :=
        linear_extremal_density_exists H active hedges (forest_extremal_upper H forest)
      exact ⟨1, c, hc, by simpa only [Real.rpow_one] using fit⟩
    have reducedCore :
        HasExtremalLimit fourCycle (3 / 2) (1 / 2) ∧
        (∀ {V : Type} [Fintype V] (J : SimpleGraph V), J.IsBipartite → J.Connected →
          ¬ J.IsAcyclic → (∀ v, 2 ≤ J.degree v) →
          (∀ k, 0 < k → ¬ Nonempty (J ≃g squareBouquet k)) →
          ∃ a c : ℝ, 0 < c ∧ HasExtremalLimit J a c) := by
      sorry
    have connectedCyclic :
        ∀ {V : Type} [Fintype V] (J : SimpleGraph V), J.IsBipartite → J.Connected →
          ¬ J.IsAcyclic → ∃ a c : ℝ, 1 < a ∧ 0 < c ∧ HasExtremalLimit J a c := by
      apply connected_cyclic_limit_from_min_degree
      intro V _ J bip conn cyclic deg
      by_cases hb : ∃ k, 0 < k ∧ Nonempty (J ≃g squareBouquet k)
      · obtain ⟨m, hm, ⟨iso⟩⟩ := hb
        refine ⟨3 / 2, 1 / 2, by norm_num, by norm_num, ?_⟩
        apply (squareBouquet_limit_of_fourCycle hm (by norm_num) reducedCore.1).congr
        intro n
        rw [extremalNumber_congr_right iso]
      · obtain ⟨a, c, hc, fit⟩ := reducedCore.2 J bip conn cyclic deg (fun m hm hiso => hb ⟨m, hm, hiso⟩)
        exact ⟨a, c, cyclic_exponent_gt_one cyclic fit, hc, fit⟩
    obtain ⟨a, c, _, hc, fit⟩ :=
      limit_of_component_limits H active forest (fun C hC =>
        connectedCyclic C.toSimpleGraph (hbip.of_hom C.toSimpleGraph_hom)
          C.connected_toSimpleGraph hC)
    exact ⟨a, c, hc, fit⟩
  obtain ⟨α, c, hc, hlimH⟩ := hlimit
  have hlim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α)
      atTop (𝓝 c) := by
    apply hlimH.congr'
    filter_upwards [eventually_ge_atTop q] with n hn
    simp only [hstable n hn]
  have hα := exponent_ge_one G edges hlim
  have hup := exponent_le_bipartite_bound hq G bip hc hlim
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  refine ⟨α, c, ⟨hα, hup.trans_lt (sub_lt_self _ (one_div_pos.mpr hqpos))⟩, hc, ?_⟩
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · change Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (c * (n : ℝ) ^ α))
      atTop (𝓝 1)
    simpa only [div_div, mul_comm, div_self hc.ne'] using hlim.div_const c
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    positivity
