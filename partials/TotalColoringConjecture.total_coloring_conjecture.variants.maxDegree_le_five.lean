import FormalConjectures.Wikipedia.TotalColoringConjecture
import Mathlib

-- Problem: The total colouring conjecture (Behzad 1965, Vizing 1968) — maxDegree le five
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/TotalColoringConjecture.lean:65 (declaration TotalColoringConjecture.total_coloring_conjecture.variants.maxDegree_le_five)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Structure of this (partial) proof.

* A total colouring is handled as a pair `φ : V → Fin n` (vertices) and a symmetric
  `ψ : V → V → Fin n` (edges); `totalColorable_of_good` converts it to `TotalColorable`.
* Maximum degree 0 and 1: direct constructions (`case_zero`, `case_one`).
* Maximum degree 2: vertices are added one at a time (`step2`); when the new vertex has two
  coloured neighbours and all three lists coincide, one neighbour is recoloured; the finite core
  is the `decide` lemma `fin2` over `Fin 4`.
* Maximum degree `D` in `3..5`: a vertex with at most two coloured neighbours is added greedily
  (`stepD`), so by strong induction everything reduces to induced subgraphs of minimum degree at
  least three (`reduce_to_core`).
* Kempe-chain tools for the remaining core: `kempe_swap` and the inductive component `KR` with
  `kempe_component`.
* Remaining gap: `core_colorable` (Rosenfeld and Vijayaditya for three, Kostochka for four and
  five). A radius-one local recolouring is provably insufficient there, so a global chain argument
  is required.
-/

open SimpleGraph

namespace OMATC

def Good {V : Type} (G : SimpleGraph V) {n : ℕ} (φ : V → Fin n) (ψ : V → V → Fin n) : Prop :=
  (∀ u v, ψ u v = ψ v u) ∧ (∀ u v, G.Adj u v → φ u ≠ φ v) ∧
  (∀ u v, G.Adj u v → φ u ≠ ψ u v) ∧
  (∀ u v w, G.Adj u v → G.Adj u w → v ≠ w → ψ u v ≠ ψ u w)

lemma totalColorable_of_good {V : Type} (G : SimpleGraph V) {n : ℕ} (φ : V → Fin n)
    (ψ : V → V → Fin n) (h : Good G φ ψ) : G.TotalColorable n := by
  obtain ⟨hs, hv, hve, he⟩ := h
  let c : V ⊕ G.edgeSet → Fin n := fun x =>
    match x with
    | Sum.inl v => φ v
    | Sum.inr e => Sym2.lift ⟨fun a b => ψ a b, fun a b => hs a b⟩ e.1
  refine ⟨c, ?_, ?_, ?_⟩
  · intro u v huv
    exact hv u v huv
  · rintro ⟨e, he1⟩ ⟨f, hf1⟩ hne ⟨v, hve1, hvf1⟩
    obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp hve1
    obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp hvf1
    have hab : a ≠ b := by
      rintro rfl
      exact hne rfl
    have ha : G.Adj v a := (G.mem_edgeSet).mp he1
    have hb : G.Adj v b := (G.mem_edgeSet).mp hf1
    show ψ v a ≠ ψ v b
    exact he v a b ha hb hab
  · rintro v ⟨e, he1⟩ hve1
    obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp hve1
    have ha : G.Adj v a := (G.mem_edgeSet).mp he1
    show φ v ≠ ψ v a
    exact hve v a ha

lemma tcn_le {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
    (h : G.TotalColorable n) : G.totalChromaticNumber ≤ n := Nat.sInf_le h

lemma adj_unique_of_deg_le_one {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 1) {u v w : V} (hv : G.Adj u v) (hw : G.Adj u w) :
    v = w := by
  by_contra hne
  have hsub : ({v, w} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (G.mem_neighborFinset u x).mpr hv
    · exact (G.mem_neighborFinset u x).mpr hw
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_pair hne, G.card_neighborFinset_eq_degree] at h1
  have h2 := G.degree_le_maxDegree u
  omega

lemma no_adj_of_deg_zero {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : G.maxDegree = 0) {u v : V} (hv : G.Adj u v) : False := by
  classical
  have h1 : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hv
  have h2 : 0 < G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨v, h1⟩
  have h3 := G.degree_le_maxDegree u
  omega

lemma case_zero {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : G.maxDegree = 0) : G.TotalColorable 2 := by
  refine totalColorable_of_good G (fun _ => 0) (fun _ _ => 0) ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro u v h; exact (no_adj_of_deg_zero G hΔ h).elim
  · intro u v h; exact (no_adj_of_deg_zero G hΔ h).elim
  · intro u v w h; exact (no_adj_of_deg_zero G hΔ h).elim

lemma case_one {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 1) : G.TotalColorable 3 := by
  classical
  let f : V → ℕ := fun v => (Fintype.equivFin V v : ℕ)
  have hf : Function.Injective f := fun a b h =>
    (Fintype.equivFin V).injective (Fin.ext h)
  let φ : V → Fin 3 := fun v => if ∃ w, G.Adj v w ∧ f w < f v then 1 else 0
  refine totalColorable_of_good G φ (fun _ _ => 2) ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro u v huv
    have key : ∀ a b, G.Adj a b → f a < f b → φ a ≠ φ b := by
      intro a b hab hlt
      have hb : φ b = 1 := by
        simp only [φ]
        rw [if_pos ⟨a, hab.symm, hlt⟩]
      have ha : φ a = 0 := by
        simp only [φ]
        rw [if_neg]
        rintro ⟨w, hw, hwlt⟩
        have := adj_unique_of_deg_le_one G hΔ hab hw
        subst this
        omega
      rw [ha, hb]; decide
    rcases lt_trichotomy (f u) (f v) with h | h | h
    · exact key u v huv h
    · exact (G.ne_of_adj huv (hf h)).elim
    · exact (key v u huv.symm h).symm
  · intro u v huv
    simp only [φ]
    split_ifs <;> decide
  · intro u v w hv hw hne
    exact (hne (adj_unique_of_deg_le_one G hΔ hv hw)).elim


def GoodR {V : Type} (R : V → V → Prop) {n : ℕ} (φ : V → Fin n) (ψ : V → V → Fin n) : Prop :=
  (∀ u v, ψ u v = ψ v u) ∧ (∀ u v, R u v → φ u ≠ φ v) ∧
  (∀ u v, R u v → φ u ≠ ψ u v) ∧
  (∀ u v w, R u v → R u w → v ≠ w → ψ u v ≠ ψ u w)

lemma three_le_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {a x y z : V} (hx : G.Adj a x) (hy : G.Adj a y) (hz : G.Adj a z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : 3 ≤ G.degree a := by
  have hsub : ({x, y, z} : Finset V) ⊆ G.neighborFinset a := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (G.mem_neighborFinset a w).mpr hx
    · exact (G.mem_neighborFinset a w).mpr hy
    · exact (G.mem_neighborFinset a w).mpr hz
  have h1 := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree] at h1
  have h3 : ({x, y, z} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hyz]
    simp [hxy, hxz]
  omega

lemma other_nbr {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 2) (S : Finset V) {v a : V} (hv : v ∉ S)
    (hva : G.Adj v a) {n : ℕ} [NeZero n] (φ : V → Fin n) (ψ : V → V → Fin n) :
    ∃ ea fa : Fin n, ∀ w, w ∈ S → G.Adj a w → ψ a w = ea ∧ φ w = fa := by
  by_cases hex : ∃ w, w ∈ S ∧ G.Adj a w
  · obtain ⟨a', ha'S, ha'⟩ := hex
    refine ⟨ψ a a', φ a', ?_⟩
    intro w hwS hw
    have : w = a' := by
      by_contra hne
      have h3 := three_le_degree G hva.symm ha' hw (fun h => hv (h ▸ ha'S))
        (fun h => hv (h ▸ hwS)) (fun h => hne h.symm)
      have := G.degree_le_maxDegree a
      omega
    subst this
    exact ⟨rfl, rfl⟩
  · exact ⟨0, 0, fun w hwS hw => (hex ⟨w, hwS, hw⟩).elim⟩

def P2 (pa pb ea eb fa na cv cva cvb : Fin 4) : Prop :=
    (na = pa ∨ (na ≠ fa ∧ na ≠ ea)) ∧ cv ≠ na ∧ cv ≠ pb ∧ cva ≠ na ∧ cva ≠ ea ∧ cva ≠ cv ∧
    cvb ≠ pb ∧ cvb ≠ eb ∧ cvb ≠ cv ∧ cva ≠ cvb

instance (pa pb ea eb fa na cv cva cvb : Fin 4) : Decidable (P2 pa pb ea eb fa na cv cva cvb) := by
  unfold P2; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma fin2 : ∀ pa pb ea eb fa : Fin 4, ∃ na cv cva cvb : Fin 4, P2 pa pb ea eb fa na cv cva cvb := by
  decide

lemma fin1 : ∀ pa ea : Fin 4, ∃ cv cva : Fin 4, cv ≠ pa ∧ cva ≠ pa ∧ cva ≠ ea ∧ cva ≠ cv := by
  decide

set_option maxHeartbeats 2000000 in
lemma step2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 2) (S : Finset V) (v : V) (hv : v ∉ S)
    (φ : V → Fin 4) (ψ : V → V → Fin 4)
    (h : GoodR (fun x y => G.Adj x y ∧ x ∈ S ∧ y ∈ S) φ ψ) :
    ∃ φ' : V → Fin 4, ∃ ψ' : V → V → Fin 4,
      GoodR (fun x y => G.Adj x y ∧ x ∈ insert v S ∧ y ∈ insert v S) φ' ψ' := by
  obtain ⟨hs, hvv, hve, hee⟩ := h
  set N := S.filter (G.Adj v) with hN
  have hmemN : ∀ w, w ∈ N ↔ w ∈ S ∧ G.Adj v w := fun w => by simp [hN]
  have hNcard : N.card ≤ 2 := by
    have hsub : N ⊆ G.neighborFinset v := by
      intro w hw
      exact (G.mem_neighborFinset v w).mpr ((hmemN w).mp hw).2
    have := Finset.card_le_card hsub
    rw [G.card_neighborFinset_eq_degree] at this
    have := G.degree_le_maxDegree v
    omega
  have hSv : ∀ x, x ∈ S → x ≠ v := fun x hx h => hv (h ▸ hx)
  interval_cases hc : N.card
  · -- no neighbours in S
    have hN0 : N = ∅ := Finset.card_eq_zero.mp hc
    refine ⟨φ, ψ, hs, ?_, ?_, ?_⟩
    · rintro x y ⟨hxy, hx, hy⟩
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have : y ∈ N := (hmemN y).mpr ⟨hy.resolve_left (G.ne_of_adj hxy).symm, hxy⟩
        simp [hN0] at this
      rcases hy with rfl | hy
      · have : x ∈ N := (hmemN x).mpr ⟨hx, hxy.symm⟩
        simp [hN0] at this
      exact hvv x y ⟨hxy, hx, hy⟩
    · rintro x y ⟨hxy, hx, hy⟩
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have : y ∈ N := (hmemN y).mpr ⟨hy.resolve_left (G.ne_of_adj hxy).symm, hxy⟩
        simp [hN0] at this
      rcases hy with rfl | hy
      · have : x ∈ N := (hmemN x).mpr ⟨hx, hxy.symm⟩
        simp [hN0] at this
      exact hve x y ⟨hxy, hx, hy⟩
    · rintro x y z ⟨hxy, hx, hy⟩ ⟨hxz, -, hz⟩ hyz
      rw [Finset.mem_insert] at hx hy hz
      rcases hx with rfl | hx
      · have : y ∈ N := (hmemN y).mpr ⟨hy.resolve_left (G.ne_of_adj hxy).symm, hxy⟩
        simp [hN0] at this
      rcases hy with rfl | hy
      · have : x ∈ N := (hmemN x).mpr ⟨hx, hxy.symm⟩
        simp [hN0] at this
      rcases hz with rfl | hz
      · have : x ∈ N := (hmemN x).mpr ⟨hx, hxz.symm⟩
        simp [hN0] at this
      exact hee x y z ⟨hxy, hx, hy⟩ ⟨hxz, hx, hz⟩ hyz
  · -- one neighbour a in S
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have haN : a ∈ N := by rw [ha]; exact Finset.mem_singleton_self a
    have haS : a ∈ S := ((hmemN a).mp haN).1
    have hva : G.Adj v a := ((hmemN a).mp haN).2
    have hav : a ≠ v := hSv a haS
    have hNa : ∀ y, y ∈ S → G.Adj v y → y = a := by
      intro y hy hvy
      have : y ∈ N := (hmemN y).mpr ⟨hy, hvy⟩
      rw [ha] at this
      exact Finset.mem_singleton.mp this
    obtain ⟨ea, fa, hA⟩ := other_nbr G hΔ S hv hva φ ψ
    obtain ⟨cv, cva, h1, h2, h3, h4⟩ := fin1 (φ a) ea
    refine ⟨fun x => if x = v then cv else φ x,
      fun x y => if (x = v ∧ y = a) ∨ (x = a ∧ y = v) then cva else ψ x y, ?_, ?_, ?_, ?_⟩
    · intro x y
      simp only []
      by_cases c1 : (x = v ∧ y = a) ∨ (x = a ∧ y = v)
      · rw [if_pos c1, if_pos (by tauto)]
      · rw [if_neg c1, if_neg (by tauto)]
        exact hs x y
    · rintro x y ⟨hxy, hx, hy⟩
      simp only []
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        have := hNa y hyS hxy
        subst this
        rw [if_pos rfl, if_neg hav]
        exact h1
      rcases hy with rfl | hy
      · have := hNa x hx hxy.symm
        subst this
        rw [if_pos rfl, if_neg hav]
        exact h1.symm
      rw [if_neg (hSv x hx), if_neg (hSv y hy)]
      exact hvv x y ⟨hxy, hx, hy⟩
    · rintro x y ⟨hxy, hx, hy⟩
      simp only []
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        have := hNa y hyS hxy
        subst this
        rw [if_pos rfl, if_pos (Or.inl ⟨rfl, rfl⟩)]
        exact h4.symm
      rcases hy with rfl | hy
      · have := hNa x hx hxy.symm
        subst this
        rw [if_neg hav, if_pos (Or.inr ⟨rfl, rfl⟩)]
        exact h2.symm
      have hxv := hSv x hx
      have hyv := hSv y hy
      rw [if_neg hxv, if_neg (by tauto)]
      exact hve x y ⟨hxy, hx, hy⟩
    · rintro x y z ⟨hxy, hx, hy⟩ ⟨hxz, -, hz⟩ hyz
      simp only []
      rw [Finset.mem_insert] at hx hy hz
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        have hzS : z ∈ S := hz.resolve_left (G.ne_of_adj hxz).symm
        exact (hyz ((hNa y hyS hxy).trans (hNa z hzS hxz).symm)).elim
      have hxv := hSv x hx
      rcases hy with rfl | hy
      · have := hNa x hx hxy.symm
        subst this
        have hzS : z ∈ S := hz.resolve_left (Ne.symm hyz)
        have hzv := hSv z hzS
        rw [if_pos (Or.inr ⟨rfl, rfl⟩), if_neg (by tauto), (hA z hzS hxz).1]
        exact h3
      rcases hz with rfl | hz
      · have := hNa x hx hxz.symm
        subst this
        have hyv := hSv y hy
        rw [if_neg (by tauto), if_pos (Or.inr ⟨rfl, rfl⟩), (hA y hy hxy).1]
        exact h3.symm
      have hyv := hSv y hy
      have hzv := hSv z hz
      rw [if_neg (by tauto), if_neg (by tauto)]
      exact hee x y z ⟨hxy, hx, hy⟩ ⟨hxz, hx, hz⟩ hyz
  · -- two neighbours a, b in S
    obtain ⟨a, b, hab, hNab⟩ := Finset.card_eq_two.mp hc
    have haN : a ∈ N := by rw [hNab]; simp
    have hbN : b ∈ N := by rw [hNab]; simp
    have haS : a ∈ S := ((hmemN a).mp haN).1
    have hva : G.Adj v a := ((hmemN a).mp haN).2
    have hbS : b ∈ S := ((hmemN b).mp hbN).1
    have hvb : G.Adj v b := ((hmemN b).mp hbN).2
    have hav : a ≠ v := hSv a haS
    have hbv : b ≠ v := hSv b hbS
    have hba : b ≠ a := Ne.symm hab
    have hNa : ∀ y, y ∈ S → G.Adj v y → y = a ∨ y = b := by
      intro y hy hvy
      have : y ∈ N := (hmemN y).mpr ⟨hy, hvy⟩
      rw [hNab] at this
      simpa using this
    obtain ⟨ea, fa, hA⟩ := other_nbr G hΔ S hv hva φ ψ
    obtain ⟨eb, fb, hB⟩ := other_nbr G hΔ S hv hvb φ ψ
    obtain ⟨na, cv, cva, cvb, hP⟩ := fin2 (φ a) (φ b) ea eb fa
    unfold P2 at hP
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hP
    obtain ⟨φ', hφ'⟩ : ∃ f : V → Fin 4, ∀ x, f x = if x = v then cv else if x = a then na else φ x :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨ψ', hψ'⟩ : ∃ f : V → V → Fin 4, ∀ x y, f x y =
        if (x = v ∧ y = a) ∨ (x = a ∧ y = v) then cva else
        if (x = v ∧ y = b) ∨ (x = b ∧ y = v) then cvb else ψ x y := ⟨_, fun _ _ => rfl⟩
    have pφv : φ' v = cv := by rw [hφ', if_pos rfl]
    have pφa : φ' a = na := by rw [hφ', if_neg hav, if_pos rfl]
    have pφo : ∀ x, x ≠ v → x ≠ a → φ' x = φ x := by
      intro x h1 h2; rw [hφ', if_neg h1, if_neg h2]
    have pψva : ψ' v a = cva := by rw [hψ', if_pos (Or.inl ⟨rfl, rfl⟩)]
    have pψav : ψ' a v = cva := by rw [hψ', if_pos (Or.inr ⟨rfl, rfl⟩)]
    have pψvb : ψ' v b = cvb := by
      rw [hψ', if_neg (by tauto), if_pos (Or.inl ⟨rfl, rfl⟩)]
    have pψbv : ψ' b v = cvb := by
      rw [hψ', if_neg (by tauto), if_pos (Or.inr ⟨rfl, rfl⟩)]
    have pψo : ∀ x y, x ≠ v → y ≠ v → ψ' x y = ψ x y := by
      intro x y h1 h2; rw [hψ', if_neg (by tauto), if_neg (by tauto)]
    refine ⟨φ', ψ', ?_, ?_, ?_, ?_⟩
    · intro x y
      rw [hψ' x y, hψ' y x]
      split_ifs <;> first | rfl | exact hs x y | (exfalso; tauto)
    · rintro x y ⟨hxy, hx, hy⟩
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        rcases hNa y hyS hxy with rfl | rfl
        · rw [pφv, pφa]; exact g2
        · rw [pφv, pφo y hbv hba]; exact g3
      rcases hy with rfl | hy
      · rcases hNa x hx hxy.symm with rfl | rfl
        · rw [pφv, pφa]; exact g2.symm
        · rw [pφv, pφo x hbv hba]; exact g3.symm
      have hxv := hSv x hx
      have hyv := hSv y hy
      by_cases hxa : x = a
      · subst hxa
        have hya : y ≠ x := (G.ne_of_adj hxy).symm
        rw [pφa, pφo y hyv hya]
        rcases g1 with g1 | g1
        · rw [g1]; exact hvv x y ⟨hxy, hx, hy⟩
        · rw [(hA y hy hxy).2]; exact g1.1
      by_cases hya : y = a
      · subst hya
        rw [pφa, pφo x hxv hxa]
        rcases g1 with g1 | g1
        · rw [g1]; exact hvv x y ⟨hxy, hx, hy⟩
        · rw [(hA x hx hxy.symm).2]; exact Ne.symm g1.1
      rw [pφo x hxv hxa, pφo y hyv hya]
      exact hvv x y ⟨hxy, hx, hy⟩
    · rintro x y ⟨hxy, hx, hy⟩
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        rcases hNa y hyS hxy with rfl | rfl
        · rw [pφv, pψva]; exact g6.symm
        · rw [pφv, pψvb]; exact g9.symm
      rcases hy with rfl | hy
      · rcases hNa x hx hxy.symm with rfl | rfl
        · rw [pφa, pψav]; exact g4.symm
        · rw [pφo x hbv hba, pψbv]; exact g7.symm
      have hxv := hSv x hx
      have hyv := hSv y hy
      rw [pψo x y hxv hyv]
      by_cases hxa : x = a
      · subst hxa
        rw [pφa]
        rcases g1 with g1 | g1
        · rw [g1]; exact hve x y ⟨hxy, hx, hy⟩
        · rw [(hA y hy hxy).1]; exact g1.2
      rw [pφo x hxv hxa]
      exact hve x y ⟨hxy, hx, hy⟩
    · rintro x y z ⟨hxy, hx, hy⟩ ⟨hxz, -, hz⟩ hyz
      rw [Finset.mem_insert] at hx hy hz
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        have hzS : z ∈ S := hz.resolve_left (G.ne_of_adj hxz).symm
        rcases hNa y hyS hxy with rfl | rfl <;> rcases hNa z hzS hxz with rfl | rfl
        · exact (hyz rfl).elim
        · rw [pψva, pψvb]; exact g10
        · rw [pψva, pψvb]; exact g10.symm
        · exact (hyz rfl).elim
      have hxv := hSv x hx
      rcases hy with rfl | hy
      · have hzS : z ∈ S := hz.resolve_left (Ne.symm hyz)
        have hzv := hSv z hzS
        rcases hNa x hx hxy.symm with rfl | rfl
        · rw [pψav, pψo x z hxv hzv, (hA z hzS hxz).1]; exact g5
        · rw [pψbv, pψo x z hxv hzv, (hB z hzS hxz).1]; exact g8
      rcases hz with rfl | hz
      · have hyv := hSv y hy
        rcases hNa x hx hxz.symm with rfl | rfl
        · rw [pψav, pψo x y hxv hyv, (hA y hy hxy).1]; exact g5.symm
        · rw [pψbv, pψo x y hxv hyv, (hB y hy hxy).1]; exact g8.symm
      have hyv := hSv y hy
      have hzv := hSv z hz
      rw [pψo x y hxv hyv, pψo x z hxv hzv]
      exact hee x y z ⟨hxy, hx, hy⟩ ⟨hxz, hx, hz⟩ hyz


lemma case_two {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 2) : G.TotalColorable 4 := by
  have key : ∀ S : Finset V, ∃ φ : V → Fin 4, ∃ ψ : V → V → Fin 4,
      GoodR (fun x y => G.Adj x y ∧ x ∈ S ∧ y ∈ S) φ ψ := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · refine ⟨fun _ => 0, fun _ _ => 0, fun _ _ => rfl, ?_, ?_, ?_⟩
      · rintro x y ⟨-, hx, -⟩; simp at hx
      · rintro x y ⟨-, hx, -⟩; simp at hx
      · rintro x y z ⟨-, hx, -⟩; simp at hx
    · intro v S hv ih
      obtain ⟨φ, ψ, h⟩ := ih
      exact step2 G hΔ S v hv φ ψ h
  obtain ⟨φ, ψ, hs, h1, h2, h3⟩ := key Finset.univ
  refine totalColorable_of_good G φ ψ ⟨hs, ?_, ?_, ?_⟩
  · intro u v h; exact h1 u v ⟨h, Finset.mem_univ _, Finset.mem_univ _⟩
  · intro u v h; exact h2 u v ⟨h, Finset.mem_univ _, Finset.mem_univ _⟩
  · intro u v w h h'
    exact h3 u v w ⟨h, Finset.mem_univ _, Finset.mem_univ _⟩ ⟨h', Finset.mem_univ _, Finset.mem_univ _⟩

lemma exists_not_mem_fin {n : ℕ} (F : Finset (Fin n)) (h : F.card < n) : ∃ c, c ∉ F := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ F := fun c _ => hc c
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

lemma other_card_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {D : ℕ} (hΔ : G.maxDegree ≤ D) (S : Finset V) {v a : V} (hv : v ∉ S)
    (hva : G.Adj v a) : (S.filter (G.Adj a)).card + 1 ≤ D := by
  have hsub : insert v (S.filter (G.Adj a)) ⊆ G.neighborFinset a := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact (G.mem_neighborFinset a w).mpr hva.symm
    · exact (G.mem_neighborFinset a w).mpr (Finset.mem_filter.mp hw).2
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (fun h => hv (Finset.mem_filter.mp h).1),
    G.card_neighborFinset_eq_degree] at h1
  have := G.degree_le_maxDegree a
  omega

/-- Choose a colour for the edge from `v` to `a` avoiding the colour of `a`, the colours of the
edges from `a` into `S`, and an extra colour `x`. -/
lemma pick_edge {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {D : ℕ} (hΔ : G.maxDegree ≤ D) (S : Finset V) {v a : V} (hv : v ∉ S)
    (hva : G.Adj v a) (φ : V → Fin (D + 2)) (ψ : V → V → Fin (D + 2)) (x : Fin (D + 2)) :
    ∃ c : Fin (D + 2), c ≠ φ a ∧ c ≠ x ∧ ∀ w, w ∈ S → G.Adj a w → c ≠ ψ a w := by
  have hc := other_card_le G hΔ S hv hva
  obtain ⟨c, hcF⟩ := exists_not_mem_fin
    (insert (φ a) (insert x ((S.filter (G.Adj a)).image (ψ a)))) (by
      have h1 := Finset.card_insert_le (φ a) (insert x ((S.filter (G.Adj a)).image (ψ a)))
      have h2 := Finset.card_insert_le x ((S.filter (G.Adj a)).image (ψ a))
      have h3 := Finset.card_image_le (s := S.filter (G.Adj a)) (f := ψ a)
      omega)
  refine ⟨c, fun h => hcF (h ▸ Finset.mem_insert_self _ _), fun h => hcF ?_, ?_⟩
  · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · intro w hw haw h
    apply hcF
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw, haw⟩)))

set_option maxHeartbeats 2000000 in
/-- For `D ≥ 3`, a vertex with at most two neighbours already coloured can be added greedily. -/
lemma stepD {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} (hD : 3 ≤ D) (hΔ : G.maxDegree ≤ D) (S : Finset V) (v : V) (hv : v ∉ S)
    (hN2 : (S.filter (G.Adj v)).card ≤ 2)
    (φ : V → Fin (D + 2)) (ψ : V → V → Fin (D + 2))
    (h : GoodR (fun x y => G.Adj x y ∧ x ∈ S ∧ y ∈ S) φ ψ) :
    ∃ φ' : V → Fin (D + 2), ∃ ψ' : V → V → Fin (D + 2),
      GoodR (fun x y => G.Adj x y ∧ x ∈ insert v S ∧ y ∈ insert v S) φ' ψ' := by
  obtain ⟨hs, hvv, hve, hee⟩ := h
  set N := S.filter (G.Adj v) with hN
  have hmemN : ∀ w, w ∈ N ↔ w ∈ S ∧ G.Adj v w := fun w => by simp [hN]
  have hSv : ∀ x, x ∈ S → x ≠ v := fun x hx h => hv (h ▸ hx)
  interval_cases hc : N.card
  · -- no neighbours in S
    have hN0 : N = ∅ := Finset.card_eq_zero.mp hc
    refine ⟨φ, ψ, hs, ?_, ?_, ?_⟩
    · rintro x y ⟨hxy, hx, hy⟩
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have : y ∈ N := (hmemN y).mpr ⟨hy.resolve_left (G.ne_of_adj hxy).symm, hxy⟩
        simp [hN0] at this
      rcases hy with rfl | hy
      · have : x ∈ N := (hmemN x).mpr ⟨hx, hxy.symm⟩
        simp [hN0] at this
      exact hvv x y ⟨hxy, hx, hy⟩
    · rintro x y ⟨hxy, hx, hy⟩
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have : y ∈ N := (hmemN y).mpr ⟨hy.resolve_left (G.ne_of_adj hxy).symm, hxy⟩
        simp [hN0] at this
      rcases hy with rfl | hy
      · have : x ∈ N := (hmemN x).mpr ⟨hx, hxy.symm⟩
        simp [hN0] at this
      exact hve x y ⟨hxy, hx, hy⟩
    · rintro x y z ⟨hxy, hx, hy⟩ ⟨hxz, -, hz⟩ hyz
      rw [Finset.mem_insert] at hx hy hz
      rcases hx with rfl | hx
      · have : y ∈ N := (hmemN y).mpr ⟨hy.resolve_left (G.ne_of_adj hxy).symm, hxy⟩
        simp [hN0] at this
      rcases hy with rfl | hy
      · have : x ∈ N := (hmemN x).mpr ⟨hx, hxy.symm⟩
        simp [hN0] at this
      rcases hz with rfl | hz
      · have : x ∈ N := (hmemN x).mpr ⟨hx, hxz.symm⟩
        simp [hN0] at this
      exact hee x y z ⟨hxy, hx, hy⟩ ⟨hxz, hx, hz⟩ hyz
  · -- one neighbour a in S
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have haN : a ∈ N := by rw [ha]; exact Finset.mem_singleton_self a
    have haS : a ∈ S := ((hmemN a).mp haN).1
    have hva : G.Adj v a := ((hmemN a).mp haN).2
    have hav : a ≠ v := hSv a haS
    have hNa : ∀ y, y ∈ S → G.Adj v y → y = a := by
      intro y hy hvy
      have : y ∈ N := (hmemN y).mpr ⟨hy, hvy⟩
      rw [ha] at this
      exact Finset.mem_singleton.mp this
    obtain ⟨cva, h2, -, hA⟩ := pick_edge G hΔ S hv hva φ ψ (φ a)
    obtain ⟨cv, hcvF⟩ := exists_not_mem_fin ({φ a, cva} : Finset (Fin (D + 2))) (by
      have := Finset.card_le_two (a := φ a) (b := cva)
      omega)
    have h1 : cv ≠ φ a := fun h => hcvF (by simp [h])
    have h4 : cva ≠ cv := fun h => hcvF (by simp [h])
    refine ⟨fun x => if x = v then cv else φ x,
      fun x y => if (x = v ∧ y = a) ∨ (x = a ∧ y = v) then cva else ψ x y, ?_, ?_, ?_, ?_⟩
    · intro x y
      simp only []
      by_cases c1 : (x = v ∧ y = a) ∨ (x = a ∧ y = v)
      · rw [if_pos c1, if_pos (by tauto)]
      · rw [if_neg c1, if_neg (by tauto)]
        exact hs x y
    · rintro x y ⟨hxy, hx, hy⟩
      simp only []
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        have := hNa y hyS hxy
        subst this
        rw [if_pos rfl, if_neg hav]
        exact h1
      rcases hy with rfl | hy
      · have := hNa x hx hxy.symm
        subst this
        rw [if_pos rfl, if_neg hav]
        exact h1.symm
      rw [if_neg (hSv x hx), if_neg (hSv y hy)]
      exact hvv x y ⟨hxy, hx, hy⟩
    · rintro x y ⟨hxy, hx, hy⟩
      simp only []
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        have := hNa y hyS hxy
        subst this
        rw [if_pos rfl, if_pos (Or.inl ⟨rfl, rfl⟩)]
        exact h4.symm
      rcases hy with rfl | hy
      · have := hNa x hx hxy.symm
        subst this
        rw [if_neg hav, if_pos (Or.inr ⟨rfl, rfl⟩)]
        exact h2.symm
      have hxv := hSv x hx
      have hyv := hSv y hy
      rw [if_neg hxv, if_neg (by tauto)]
      exact hve x y ⟨hxy, hx, hy⟩
    · rintro x y z ⟨hxy, hx, hy⟩ ⟨hxz, -, hz⟩ hyz
      simp only []
      rw [Finset.mem_insert] at hx hy hz
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        have hzS : z ∈ S := hz.resolve_left (G.ne_of_adj hxz).symm
        exact (hyz ((hNa y hyS hxy).trans (hNa z hzS hxz).symm)).elim
      have hxv := hSv x hx
      rcases hy with rfl | hy
      · have := hNa x hx hxy.symm
        subst this
        have hzS : z ∈ S := hz.resolve_left (Ne.symm hyz)
        have hzv := hSv z hzS
        rw [if_pos (Or.inr ⟨rfl, rfl⟩), if_neg (by tauto)]
        exact hA z hzS hxz
      rcases hz with rfl | hz
      · have := hNa x hx hxz.symm
        subst this
        have hyv := hSv y hy
        rw [if_neg (by tauto), if_pos (Or.inr ⟨rfl, rfl⟩)]
        exact (hA y hy hxy).symm
      have hyv := hSv y hy
      have hzv := hSv z hz
      rw [if_neg (by tauto), if_neg (by tauto)]
      exact hee x y z ⟨hxy, hx, hy⟩ ⟨hxz, hx, hz⟩ hyz
  · -- two neighbours a, b in S
    obtain ⟨a, b, hab, hNab⟩ := Finset.card_eq_two.mp hc
    have haN : a ∈ N := by rw [hNab]; simp
    have hbN : b ∈ N := by rw [hNab]; simp
    have haS : a ∈ S := ((hmemN a).mp haN).1
    have hva : G.Adj v a := ((hmemN a).mp haN).2
    have hbS : b ∈ S := ((hmemN b).mp hbN).1
    have hvb : G.Adj v b := ((hmemN b).mp hbN).2
    have hav : a ≠ v := hSv a haS
    have hbv : b ≠ v := hSv b hbS
    have hba : b ≠ a := Ne.symm hab
    have hNa : ∀ y, y ∈ S → G.Adj v y → y = a ∨ y = b := by
      intro y hy hvy
      have : y ∈ N := (hmemN y).mpr ⟨hy, hvy⟩
      rw [hNab] at this
      simpa using this
    obtain ⟨cva, g1, -, hA⟩ := pick_edge G hΔ S hv hva φ ψ (φ a)
    obtain ⟨cvb, g2, g3, hB⟩ := pick_edge G hΔ S hv hvb φ ψ cva
    obtain ⟨cv, hcvF⟩ := exists_not_mem_fin ({φ a, φ b, cva, cvb} : Finset (Fin (D + 2))) (by
      have := Finset.card_le_four (a := φ a) (b := φ b) (c := cva) (d := cvb)
      omega)
    have k1 : cv ≠ φ a := fun h => hcvF (by simp [h])
    have k2 : cv ≠ φ b := fun h => hcvF (by simp [h])
    have k3 : cv ≠ cva := fun h => hcvF (by simp [h])
    have k4 : cv ≠ cvb := fun h => hcvF (by simp [h])
    obtain ⟨φ', hφ'⟩ : ∃ f : V → Fin (D + 2), ∀ x, f x = if x = v then cv else φ x :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨ψ', hψ'⟩ : ∃ f : V → V → Fin (D + 2), ∀ x y, f x y =
        if (x = v ∧ y = a) ∨ (x = a ∧ y = v) then cva else
        if (x = v ∧ y = b) ∨ (x = b ∧ y = v) then cvb else ψ x y := ⟨_, fun _ _ => rfl⟩
    have pφv : φ' v = cv := by rw [hφ', if_pos rfl]
    have pφo : ∀ x, x ≠ v → φ' x = φ x := by
      intro x h1; rw [hφ', if_neg h1]
    have pψva : ψ' v a = cva := by rw [hψ', if_pos (Or.inl ⟨rfl, rfl⟩)]
    have pψav : ψ' a v = cva := by rw [hψ', if_pos (Or.inr ⟨rfl, rfl⟩)]
    have pψvb : ψ' v b = cvb := by
      rw [hψ', if_neg (by tauto), if_pos (Or.inl ⟨rfl, rfl⟩)]
    have pψbv : ψ' b v = cvb := by
      rw [hψ', if_neg (by tauto), if_pos (Or.inr ⟨rfl, rfl⟩)]
    have pψo : ∀ x y, x ≠ v → y ≠ v → ψ' x y = ψ x y := by
      intro x y h1 h2; rw [hψ', if_neg (by tauto), if_neg (by tauto)]
    refine ⟨φ', ψ', ?_, ?_, ?_, ?_⟩
    · intro x y
      rw [hψ' x y, hψ' y x]
      split_ifs <;> first | rfl | exact hs x y | (exfalso; tauto)
    · rintro x y ⟨hxy, hx, hy⟩
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        rcases hNa y hyS hxy with rfl | rfl
        · rw [pφv, pφo y hav]; exact k1
        · rw [pφv, pφo y hbv]; exact k2
      rcases hy with rfl | hy
      · rcases hNa x hx hxy.symm with rfl | rfl
        · rw [pφv, pφo x hav]; exact k1.symm
        · rw [pφv, pφo x hbv]; exact k2.symm
      rw [pφo x (hSv x hx), pφo y (hSv y hy)]
      exact hvv x y ⟨hxy, hx, hy⟩
    · rintro x y ⟨hxy, hx, hy⟩
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        rcases hNa y hyS hxy with rfl | rfl
        · rw [pφv, pψva]; exact k3
        · rw [pφv, pψvb]; exact k4
      rcases hy with rfl | hy
      · rcases hNa x hx hxy.symm with rfl | rfl
        · rw [pφo x hav, pψav]; exact g1.symm
        · rw [pφo x hbv, pψbv]; exact g2.symm
      rw [pψo x y (hSv x hx) (hSv y hy), pφo x (hSv x hx)]
      exact hve x y ⟨hxy, hx, hy⟩
    · rintro x y z ⟨hxy, hx, hy⟩ ⟨hxz, -, hz⟩ hyz
      rw [Finset.mem_insert] at hx hy hz
      rcases hx with rfl | hx
      · have hyS : y ∈ S := hy.resolve_left (G.ne_of_adj hxy).symm
        have hzS : z ∈ S := hz.resolve_left (G.ne_of_adj hxz).symm
        rcases hNa y hyS hxy with rfl | rfl <;> rcases hNa z hzS hxz with rfl | rfl
        · exact (hyz rfl).elim
        · rw [pψva, pψvb]; exact g3.symm
        · rw [pψva, pψvb]; exact g3
        · exact (hyz rfl).elim
      have hxv := hSv x hx
      rcases hy with rfl | hy
      · have hzS : z ∈ S := hz.resolve_left (Ne.symm hyz)
        have hzv := hSv z hzS
        rcases hNa x hx hxy.symm with rfl | rfl
        · rw [pψav, pψo x z hxv hzv]; exact hA z hzS hxz
        · rw [pψbv, pψo x z hxv hzv]; exact hB z hzS hxz
      rcases hz with rfl | hz
      · have hyv := hSv y hy
        rcases hNa x hx hxz.symm with rfl | rfl
        · rw [pψav, pψo x y hxv hyv]; exact (hA y hy hxy).symm
        · rw [pψbv, pψo x y hxv hyv]; exact (hB y hy hxy).symm
      rw [pψo x y hxv (hSv y hy), pψo x z hxv (hSv z hz)]
      exact hee x y z ⟨hxy, hx, hy⟩ ⟨hxz, hx, hz⟩ hyz

/-- For `D ≥ 3`, total `(D+2)`-colourability reduces to the induced subgraphs of minimum
degree at least three (vertices of degree at most two are added back greedily). -/
lemma reduce_to_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {D : ℕ} (hD : 3 ≤ D) (hΔ : G.maxDegree ≤ D)
    (hcore : ∀ S : Finset V, (∀ v, v ∈ S → 3 ≤ (S.filter (G.Adj v)).card) →
      ∃ φ : V → Fin (D + 2), ∃ ψ : V → V → Fin (D + 2),
        GoodR (fun x y => G.Adj x y ∧ x ∈ S ∧ y ∈ S) φ ψ) :
    ∀ S : Finset V, ∃ φ : V → Fin (D + 2), ∃ ψ : V → V → Fin (D + 2),
      GoodR (fun x y => G.Adj x y ∧ x ∈ S ∧ y ∈ S) φ ψ := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hall : ∀ v, v ∈ S → 3 ≤ (S.filter (G.Adj v)).card
    · exact hcore S hall
    · push Not at hall
      obtain ⟨v, hvS, hlt⟩ := hall
      obtain ⟨φ, ψ, h⟩ := ih (S.erase v) (Finset.erase_ssubset hvS)
      have hN2 : ((S.erase v).filter (G.Adj v)).card ≤ 2 := by
        have := Finset.card_le_card (Finset.filter_subset_filter (G.Adj v) (Finset.erase_subset v S))
        omega
      obtain ⟨φ', ψ', h'⟩ := stepD G hD hΔ (S.erase v) v (Finset.notMem_erase v S) hN2 φ ψ h
      rw [Finset.insert_erase hvS] at h'
      exact ⟨φ', ψ', h'⟩


/-- Swap the colours `α` and `β`. -/
def swapC {n : ℕ} (α β c : Fin n) : Fin n := if c = α then β else if c = β then α else c

lemma swapC_inj {n : ℕ} (α β : Fin n) {x y : Fin n} (h : swapC α β x = swapC α β y) : x = y := by
  unfold swapC at h
  split_ifs at h <;> subst_vars <;> first | rfl | (exfalso; tauto)

lemma swapC_of_ne {n : ℕ} (α β : Fin n) {c : Fin n} (h1 : c ≠ α) (h2 : c ≠ β) :
    swapC α β c = c := by
  unfold swapC; rw [if_neg h1, if_neg h2]

lemma swapC_mem {n : ℕ} (α β : Fin n) {c : Fin n} (h : c = α ∨ c = β) :
    swapC α β c = α ∨ swapC α β c = β := by
  unfold swapC
  rcases h with rfl | rfl
  · rw [if_pos rfl]; exact Or.inr rfl
  · by_cases h : c = α
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h, if_pos rfl]; exact Or.inl rfl

/-- Swapped element versus unswapped element: the new colours differ. -/
lemma swap_vs_fixed {n : ℕ} (α β x y : Fin n) (hxy : x ≠ y)
    (hc : (x = α ∨ x = β) → y ≠ α ∧ y ≠ β) : swapC α β x ≠ y := by
  by_cases hx : x = α ∨ x = β
  · obtain ⟨h1, h2⟩ := hc hx
    rcases swapC_mem α β hx with h | h <;> rw [h] <;> [exact Ne.symm h1; exact Ne.symm h2]
  · push Not at hx
    rw [swapC_of_ne α β hx.1 hx.2]; exact hxy

/-- **Kempe swap.** Swapping two colours on a set of vertices `A` and a symmetric set of edges
`B` that is closed under conflicts preserves the colouring. -/
lemma kempe_swap {V : Type} (R : V → V → Prop) {n : ℕ} (φ : V → Fin n) (ψ : V → V → Fin n)
    (h : GoodR R φ ψ) (α β : Fin n) (A : V → Prop) (B : V → V → Prop)
    [DecidablePred A] [∀ u v, Decidable (B u v)] (hR : ∀ u v, R u v → R v u)
    (hB : ∀ u v, B u v ↔ B v u)
    (cvv : ∀ u v, R u v → A u → ¬ A v → (φ u = α ∨ φ u = β) → φ v ≠ α ∧ φ v ≠ β)
    (cve : ∀ u v, R u v → A u → ¬ B u v → (φ u = α ∨ φ u = β) → ψ u v ≠ α ∧ ψ u v ≠ β)
    (cev : ∀ u v, R u v → B u v → ¬ A u → (ψ u v = α ∨ ψ u v = β) → φ u ≠ α ∧ φ u ≠ β)
    (cee : ∀ u v w, R u v → R u w → v ≠ w → B u v → ¬ B u w →
      (ψ u v = α ∨ ψ u v = β) → ψ u w ≠ α ∧ ψ u w ≠ β) :
    GoodR R (fun v => if A v then swapC α β (φ v) else φ v)
      (fun u v => if B u v then swapC α β (ψ u v) else ψ u v) := by
  obtain ⟨hs, hvv, hve, hee⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v
    simp only []
    by_cases huv : B u v
    · rw [if_pos huv, if_pos ((hB u v).mp huv), hs u v]
    · rw [if_neg huv, if_neg (fun h => huv ((hB u v).mpr h)), hs u v]
  · intro u v hr
    simp only []
    by_cases hu : A u <;> by_cases hv : A v
    · rw [if_pos hu, if_pos hv]
      exact fun h => hvv u v hr (swapC_inj α β h)
    · rw [if_pos hu, if_neg hv]
      exact swap_vs_fixed α β _ _ (hvv u v hr) (cvv u v hr hu hv)
    · rw [if_neg hu, if_pos hv]
      exact Ne.symm (swap_vs_fixed α β _ _ (hvv v u (hR u v hr)) (cvv v u (hR u v hr) hv hu))
    · rw [if_neg hu, if_neg hv]; exact hvv u v hr
  · intro u v hr
    simp only []
    by_cases hu : A u <;> by_cases he : B u v
    · rw [if_pos hu, if_pos he]
      exact fun h => hve u v hr (swapC_inj α β h)
    · rw [if_pos hu, if_neg he]
      exact swap_vs_fixed α β _ _ (hve u v hr) (cve u v hr hu he)
    · rw [if_neg hu, if_pos he]
      exact Ne.symm (swap_vs_fixed α β _ _ (Ne.symm (hve u v hr)) (cev u v hr he hu))
    · rw [if_neg hu, if_neg he]; exact hve u v hr
  · intro u v w hrv hrw hvw
    simp only []
    by_cases hv : B u v <;> by_cases hw : B u w
    · rw [if_pos hv, if_pos hw]
      exact fun h => hee u v w hrv hrw hvw (swapC_inj α β h)
    · rw [if_pos hv, if_neg hw]
      exact swap_vs_fixed α β _ _ (hee u v w hrv hrw hvw) (cee u v w hrv hrw hvw hv hw)
    · rw [if_neg hv, if_pos hw]
      exact Ne.symm (swap_vs_fixed α β _ _ (hee u w v hrw hrv (Ne.symm hvw))
        (cee u w v hrw hrv (Ne.symm hvw) hw hv))
    · rw [if_neg hv, if_neg hw]; exact hee u v w hrv hrw hvw


/-- Elements reachable from `s` through conflicts whose colours lie in `{α, β}` (a Kempe
component; edge elements are ordered pairs, closed under flipping). -/
inductive KR {V : Type} (R : V → V → Prop) {n : ℕ} (φ : V → Fin n) (ψ : V → V → Fin n)
    (α β : Fin n) (s : V ⊕ (V × V)) : V ⊕ (V × V) → Prop
  | base : KR R φ ψ α β s s
  | vv {u v : V} : KR R φ ψ α β s (Sum.inl u) → R u v → (φ v = α ∨ φ v = β) →
      KR R φ ψ α β s (Sum.inl v)
  | ve {u v : V} : KR R φ ψ α β s (Sum.inl u) → R u v → (ψ u v = α ∨ ψ u v = β) →
      KR R φ ψ α β s (Sum.inr (u, v))
  | ev {u v : V} : KR R φ ψ α β s (Sum.inr (u, v)) → R u v → (φ u = α ∨ φ u = β) →
      KR R φ ψ α β s (Sum.inl u)
  | ee {u v w : V} : KR R φ ψ α β s (Sum.inr (u, v)) → R u v → R u w → v ≠ w →
      (ψ u w = α ∨ ψ u w = β) → KR R φ ψ α β s (Sum.inr (u, w))
  | flip {u v : V} : KR R φ ψ α β s (Sum.inr (u, v)) → KR R φ ψ α β s (Sum.inr (v, u))

lemma not_ab {n : ℕ} {α β c : Fin n} (h : ¬ (c = α ∨ c = β)) : c ≠ α ∧ c ≠ β := by
  push Not at h; exact h

/-- **Kempe component swap.** Swapping `α` and `β` on the Kempe component of any element gives
another valid colouring. -/
lemma kempe_component {V : Type} (R : V → V → Prop) (hR : ∀ u v, R u v → R v u) {n : ℕ}
    (φ : V → Fin n) (ψ : V → V → Fin n) (h : GoodR R φ ψ) (α β : Fin n) (s : V ⊕ (V × V)) :
    ∃ φ' : V → Fin n, ∃ ψ' : V → V → Fin n, GoodR R φ' ψ' ∧
      (∀ v, (KR R φ ψ α β s (Sum.inl v) → φ' v = swapC α β (φ v)) ∧
        (¬ KR R φ ψ α β s (Sum.inl v) → φ' v = φ v)) ∧
      (∀ u v, (KR R φ ψ α β s (Sum.inr (u, v)) → ψ' u v = swapC α β (ψ u v)) ∧
        (¬ KR R φ ψ α β s (Sum.inr (u, v)) → ψ' u v = ψ u v)) := by
  classical
  refine ⟨_, _, kempe_swap R φ ψ h α β (fun v => KR R φ ψ α β s (Sum.inl v))
    (fun u v => KR R φ ψ α β s (Sum.inr (u, v))) hR
    (fun u v => ⟨fun h => KR.flip h, fun h => KR.flip h⟩) ?_ ?_ ?_ ?_, ?_, ?_⟩
  · intro u v hr hu hv _
    exact not_ab (fun hc => hv (KR.vv hu hr hc))
  · intro u v hr hu he _
    exact not_ab (fun hc => he (KR.ve hu hr hc))
  · intro u v hr he hu _
    exact not_ab (fun hc => hu (KR.ev he hr hc))
  · intro u v w hrv hrw hvw hv hw _
    exact not_ab (fun hc => hw (KR.ee hv hrv hrw hvw hc))
  · intro v
    exact ⟨fun hk => if_pos hk, fun hk => if_neg hk⟩
  · intro u v
    exact ⟨fun hk => if_pos hk, fun hk => if_neg hk⟩


/-- In the maximum-degree-three core every vertex has all its neighbours inside `S`, and exactly
three of them: the core is a union of cubic components. -/
lemma core_three_closed {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 3) (S : Finset V)
    (hS : ∀ v, v ∈ S → 3 ≤ (S.filter (G.Adj v)).card) (v : V) (hv : v ∈ S) :
    G.degree v = 3 ∧ ∀ w, G.Adj v w → w ∈ S := by
  have hsub : S.filter (G.Adj v) ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset v w).mpr (Finset.mem_filter.mp hw).2
  have h1 := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree] at h1
  have h2 := G.degree_le_maxDegree v
  have h3 := hS v hv
  have heq : S.filter (G.Adj v) = G.neighborFinset v := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [G.card_neighborFinset_eq_degree]
    omega
  refine ⟨by omega, fun w hw => ?_⟩
  have : w ∈ S.filter (G.Adj v) := by
    rw [heq]; exact (G.mem_neighborFinset v w).mpr hw
  exact (Finset.mem_filter.mp this).1


/-- The remaining core (Rosenfeld and Vijayaditya for maximum degree three, Kostochka for four and
five): induced subgraphs of minimum degree at least three. Not yet formalized. -/
lemma core_colorable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hΔ : G.maxDegree ≤ 5) (h3 : 3 ≤ G.maxDegree) (S : Finset V)
    (hS : ∀ v, v ∈ S → 3 ≤ (S.filter (G.Adj v)).card) :
    ∃ φ : V → Fin (G.maxDegree + 2), ∃ ψ : V → V → Fin (G.maxDegree + 2),
      GoodR (fun x y => G.Adj x y ∧ x ∈ S ∧ y ∈ S) φ ψ := by
  sorry

lemma case_high {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 5) (h3 : 3 ≤ G.maxDegree) : G.TotalColorable (G.maxDegree + 2) := by
  obtain ⟨φ, ψ, hs, h1, h2, h4⟩ :=
    reduce_to_core G h3 le_rfl (core_colorable G hΔ h3) Finset.univ
  refine totalColorable_of_good G φ ψ ⟨hs, ?_, ?_, ?_⟩
  · intro u v h; exact h1 u v ⟨h, Finset.mem_univ _, Finset.mem_univ _⟩
  · intro u v h; exact h2 u v ⟨h, Finset.mem_univ _, Finset.mem_univ _⟩
  · intro u v w h h'
    exact h4 u v w ⟨h, Finset.mem_univ _, Finset.mem_univ _⟩ ⟨h', Finset.mem_univ _, Finset.mem_univ _⟩

end OMATC

theorem OMA.solution : type_of% @TotalColoringConjecture.total_coloring_conjecture.variants.maxDegree_le_five := by
  intro V _ _ G _ hΔ
  apply OMATC.tcn_le
  rcases (show G.maxDegree = 0 ∨ G.maxDegree = 1 ∨ G.maxDegree = 2 ∨ 3 ≤ G.maxDegree by omega)
    with h | h | h | h
  · rw [h]; exact OMATC.case_zero G h
  · rw [h]; exact OMATC.case_one G (by omega)
  · rw [h]; exact OMATC.case_two G (by omega)
  · exact OMATC.case_high G hΔ h
