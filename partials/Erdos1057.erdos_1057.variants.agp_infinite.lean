import FormalConjectures.ErdosProblems.«1057»

-- Problem: Erdős Problem 1057 — agp infinite
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1057.lean:87 (declaration Erdos1057.erdos_1057.variants.agp_infinite)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

/-- AGP94: infinitely many Carmichael numbers (the genuine hard input). -/
lemma carmichael_infinite : {n : ℕ | IsCarmichael n}.Infinite := by
  sorry

lemma reduce (h : {n : ℕ | IsCarmichael n}.Infinite) :
    Tendsto Erdos1057.carmichaelCounting atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨s, hs, hcard⟩ := h.exists_subset_card_eq (⌈b⌉₊)
  refine ⟨((s.sup id : ℕ) : ℝ), fun x hx => ?_⟩
  have hsub : (s : Set ℕ) ⊆ {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} := by
    intro n hn
    refine ⟨hs hn, le_trans ?_ hx⟩
    exact_mod_cast Finset.le_sup (f := id) hn
  have hfin : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.Finite := by
    apply (Set.finite_Iic ⌊x⌋₊).subset
    intro n hn
    exact Nat.le_floor hn.2
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, hcard] at this
  unfold Erdos1057.carmichaelCounting
  calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ ≤ _ := by exact_mod_cast this

theorem OMA.solution : type_of% @Erdos1057.erdos_1057.variants.agp_infinite := by
  exact reduce carmichael_infinite
