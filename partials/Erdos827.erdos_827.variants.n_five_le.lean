import FormalConjectures.ErdosProblems.«827»

-- Problem: Erdős Problem 827 — n five le
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/827.lean:108 (declaration Erdos827.erdos_827.variants.n_five_le)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E827N5
open Finset EuclideanGeometry Erdos827
open scoped Classical

/-- Two distinct points of the plane have at most two common points at fixed distances. -/
theorem pt_two {c₁ c₂ p q z : ℝ²} {r s : ℝ} (hc : c₁ ≠ c₂) (hpq : p ≠ q)
    (h1 : dist p c₁ = r) (h2 : dist q c₁ = r) (h3 : dist z c₁ = r)
    (h4 : dist p c₂ = s) (h5 : dist q c₂ = s) (h6 : dist z c₂ = s) : z = p ∨ z = q :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (by simp) hc hpq h1 h2 h3 h4 h5 h6

/-- The radius of a circle through three distinct points is unique. -/
theorem radius_unique {x y z : ℝ²} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {r s : ℝ}
    (hr : OnCircleOfRadius {x, y, z} r) (hs : OnCircleOfRadius {x, y, z} s) : r = s := by
  obtain ⟨o, ho⟩ := hr
  obtain ⟨o', ho'⟩ := hs
  by_cases hoo : o = o'
  · subst hoo
    rw [← ho x (by simp), ho' x (by simp)]
  · rcases pt_two hoo hxy (ho x (by simp)) (ho y (by simp)) (ho z (by simp))
      (ho' x (by simp)) (ho' y (by simp)) (ho' z (by simp)) with h | h
    · exact absurd h.symm hxz
    · exact absurd h.symm hyz

theorem radius_unique_card {T : Finset ℝ²} (hT : T.card = 3) {r s : ℝ}
    (hr : OnCircleOfRadius T r) (hs : OnCircleOfRadius T s) : r = s := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hT
  exact radius_unique hxy hxz hyz hr hs

/-- No four distinct points of a set in general position share a circle. -/
theorem no_four {X : Finset ℝ²} (hX : InGeneralPosition (X : Set ℝ²)) {p q u v o : ℝ²} {r : ℝ}
    (hp : p ∈ X) (hq : q ∈ X) (hu : u ∈ X) (hv : v ∈ X)
    (hpq : p ≠ q) (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) (huv : u ≠ v)
    (h1 : dist p o = r) (h2 : dist q o = r) (h3 : dist u o = r) (h4 : dist v o = r) : False := by
  classical
  apply hX.2 ((({p, q, u, v} : Finset ℝ²)) : Set ℝ²)
  · intro w hw
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  · rw [Set.ncard_coe_finset]
    rw [card_insert_of_notMem (by simp [hpq, hpu, hpv]),
      card_insert_of_notMem (by simp [hqu, hqv]), card_insert_of_notMem (by simp [huv]),
      card_singleton]
  · refine ⟨o, r, ?_⟩
    intro w hw
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption

/-- A fixed chord of a set in general position has at most two completions of a given radius. -/
theorem chord_bound {X : Finset ℝ²} (hX : InGeneralPosition (X : Set ℝ²)) {B : Finset ℝ²}
    (hBX : B ⊆ X) (hB : B.card = 2) (r : ℝ) :
    ((X \ B).filter (fun z => OnCircleOfRadius (insert z B) r)).card ≤ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨z₁, h₁, z₂, h₂, z₃, h₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hcon
  obtain ⟨b₁, b₂, hb, rfl⟩ := Finset.card_eq_two.mp hB
  have hb₁ : b₁ ∈ X := hBX (by simp)
  have hb₂ : b₂ ∈ X := hBX (by simp)
  simp only [mem_filter, mem_sdiff, mem_insert, mem_singleton, not_or] at h₁ h₂ h₃
  obtain ⟨⟨x₁, n11, n12⟩, o₁, k₁⟩ := h₁
  obtain ⟨⟨x₂, n21, n22⟩, o₂, k₂⟩ := h₂
  obtain ⟨⟨x₃, n31, n32⟩, o₃, k₃⟩ := h₃
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at k₁ k₂ k₃
  have shared : ∀ {z z' o o' : ℝ²}, z ∈ X → z' ∈ X → z ≠ b₁ → z ≠ b₂ → z' ≠ b₁ → z' ≠ b₂ →
      z ≠ z' → (dist z o = r ∧ dist b₁ o = r ∧ dist b₂ o = r) →
      (dist z' o' = r ∧ dist b₁ o' = r ∧ dist b₂ o' = r) → o ≠ o' := by
    intro z z' o o' hz hz' a1 a2 a3 a4 hzz k k' hoo
    subst hoo
    exact no_four hX hz hz' hb₁ hb₂ hzz a1 a2 a3 a4 hb k.1 k'.1 k.2.1 k.2.2
  have e12 := shared x₁ x₂ n11 n12 n21 n22 h12 k₁ k₂
  have e13 := shared x₁ x₃ n11 n12 n31 n32 h13 k₁ k₃
  have e23 := shared x₂ x₃ n21 n22 n31 n32 h23 k₂ k₃
  rcases pt_two (r := r) (s := r) hb e12 ((dist_comm _ _).trans k₁.2.1)
      ((dist_comm _ _).trans k₂.2.1) ((dist_comm _ _).trans k₃.2.1)
      ((dist_comm _ _).trans k₁.2.2) ((dist_comm _ _).trans k₂.2.2)
      ((dist_comm _ _).trans k₃.2.2) with h | h
  · exact e13 h.symm
  · exact e23 h.symm

/-- Combinatorial core (thin case): a triple relation with unique values, at most two
completions per pair and value, and at most twelve equal-valued triangles at a vertex, has a
rainbow five-set. (Proved upstream in a different form; still to be rewritten here.) -/
theorem rainbow_core (X : Finset ℝ²) (R : Finset ℝ² → ℝ → Prop) (hX : X.card = 37)
    (huniq : ∀ T ⊆ X, T.card = 3 → ∀ r s, R T r → R T s → r = s)
    (chord : ∀ B ⊆ X, B.card = 2 → ∀ r,
      ((X \ B).filter (fun z => R (insert z B) r)).card ≤ 2)
    (thin : ∀ a ∈ X, ∀ r,
      (((X.erase a).powersetCard 2).filter (fun B => R (insert a B) r)).card ≤ 12) :
    ∃ Y ⊆ X, Y.card = 5 ∧ ∀ T ⊆ Y, ∀ T' ⊆ Y, T.card = 3 → T'.card = 3 → T ≠ T' →
      ∀ r : ℝ, R T r → ¬ R T' r := by
  sorry

/-- Geometric dense case: a vertex incident with thirteen triangles of one circumradius. -/
theorem dense_core (X : Finset ℝ²) (hX : X.card = 37) (gp : InGeneralPosition (X : Set ℝ²))
    (a : ℝ²) (ha : a ∈ X) (r : ℝ)
    (many : 12 < (((X.erase a).powersetCard 2).filter
      (fun B => OnCircleOfRadius (insert a B) r)).card) :
    ∃ Y ⊆ X, Y.card = 5 ∧ HasDistinctCircumradii Y := by
  sorry

end OMA.E827N5

theorem OMA.solution : type_of% @Erdos827.erdos_827.variants.n_five_le := by
  classical
  apply Erdos827.n_le
  intro X hX gp
  by_cases thin : ∀ a ∈ X, ∀ r, (((X.erase a).powersetCard 2).filter
      (fun B => Erdos827.OnCircleOfRadius (insert a B) r)).card ≤ 12
  · exact OMA.E827N5.rainbow_core X Erdos827.OnCircleOfRadius hX
      (fun T _ hT _ _ hr hs => OMA.E827N5.radius_unique_card hT hr hs)
      (fun B hB hB2 r => by convert OMA.E827N5.chord_bound gp hB hB2 r) thin
  · push Not at thin
    obtain ⟨a, ha, r, h⟩ := thin
    exact OMA.E827N5.dense_core X hX gp a ha r (by convert h)
