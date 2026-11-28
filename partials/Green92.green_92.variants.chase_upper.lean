import FormalConjectures.GreensOpenProblems.«92»

-- Problem: Chase's upper bound.
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/92.lean:109 (declaration Green92.green_92.variants.chase_upper)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.G92Upper

open Finset Filter Green92
open scoped Classical

/-- Number of trace samples for which the pairwise test of `x` against `y` fails. -/
noncomputable def failCount {n m : ℕ} (D : (Fin n → Bool) → (Fin n → Bool) → (Fin m → List Bool) → Prop)
    (x y : Fin n → Bool) : ℕ :=
  (univ.filter fun S : Fin m → Finset (Fin n) => ¬ D x y (fun j => trace x (S j))).card

/-- OPEN CORE (Chase 2020): antisymmetric pairwise tests at Chase's sample count, each failing
on at most a 1/(10 * 2^n) fraction of samples. -/
theorem pairwise_tests : ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ D : (Fin n → Bool) → (Fin n → Bool) →
        (Fin ⌈Real.exp (C * (n:ℝ)^(1/5 : ℝ) * Real.log n ^ 5)⌉₊ → List Bool) → Prop,
      (∀ x y o, x ≠ y → D x y o → ¬ D y x o) ∧
      (∀ x y, x ≠ y → failCount D x y ≤
        Fintype.card (Fin ⌈Real.exp (C * (n:ℝ)^(1/5 : ℝ) * Real.log n ^ 5)⌉₊ → Finset (Fin n))
          / (10 * 2^n)) := by
  sorry

/-- Union bound: tests with small failure counts yield a decoder of success probability 9/10. -/
theorem decoder_of_tests (n m : ℕ)
    (D : (Fin n → Bool) → (Fin n → Bool) → (Fin m → List Bool) → Prop)
    (hanti : ∀ x y o, x ≠ y → D x y o → ¬ D y x o)
    (hfail : ∀ x y, x ≠ y → failCount D x y ≤ Fintype.card (Fin m → Finset (Fin n)) / (10 * 2^n)) :
    ∃ R : (Fin m → List Bool) → Fin n → Bool, ∀ x, (9/10 : ℝ) ≤ successProb R x := by
  -- decoder: some string that beats every other string, if there is one
  let R : (Fin m → List Bool) → Fin n → Bool := fun o =>
    if h : ∃ x, ∀ y, y ≠ x → D x y o then h.choose else fun _ => false
  have hR : ∀ o x, (∀ y, y ≠ x → D x y o) → R o = x := by
    intro o x hx
    have h : ∃ x, ∀ y, y ≠ x → D x y o := ⟨x, hx⟩
    simp only [R, dif_pos h]
    by_contra hne
    exact hanti _ _ o hne (h.choose_spec x (Ne.symm hne)) (hx _ hne)
  refine ⟨R, fun x => ?_⟩
  set N := Fintype.card (Fin m → Finset (Fin n)) with hNdef
  set good := (univ.filter fun S : Fin m → Finset (Fin n) => R (fun j => trace x (S j)) = x)
  set bad := (univ.filter fun S : Fin m → Finset (Fin n) => ¬ R (fun j => trace x (S j)) = x)
  have hsum : good.card + bad.card = N := by
    rw [card_filter_add_card_filter_not, card_univ]
  have hsub : bad ⊆ (univ.erase x).biUnion (fun y =>
      univ.filter fun S : Fin m → Finset (Fin n) => ¬ D x y (fun j => trace x (S j))) := by
    intro S hS
    simp only [bad, mem_filter, mem_univ, true_and] at hS
    have : ¬ ∀ y, y ≠ x → D x y (fun j => trace x (S j)) := fun h => hS (hR _ x h)
    push Not at this
    obtain ⟨y, hyx, hy⟩ := this
    simp only [mem_biUnion, mem_erase, mem_univ, and_true, mem_filter, true_and]
    exact ⟨y, hyx, hy⟩
  have hbad : bad.card ≤ 2 ^ n * (N / (10 * 2 ^ n)) := by
    calc bad.card ≤ _ := card_le_card hsub
      _ ≤ ∑ y ∈ univ.erase x, failCount D x y := card_biUnion_le
      _ ≤ ∑ _y ∈ univ.erase x, N / (10 * 2 ^ n) :=
          sum_le_sum fun y hy => hfail x y (Ne.symm (mem_erase.mp hy).1)
      _ = (univ.erase x).card * (N / (10 * 2 ^ n)) := by rw [sum_const, smul_eq_mul]
      _ ≤ 2 ^ n * (N / (10 * 2 ^ n)) := by
          apply Nat.mul_le_mul_right
          exact (card_erase_le).trans (by simp)
  have h10 : 10 * bad.card ≤ N := by
    have := Nat.mul_div_le N (10 * 2 ^ n)
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  have hgood : (9 : ℝ) * N ≤ 10 * (good.card : ℝ) := by
    have : 9 * N ≤ 10 * good.card := by omega
    exact_mod_cast this
  unfold successProb
  rw [le_div_iff₀ hNpos]
  linarith

end OMA.G92Upper

theorem OMA.solution : type_of% @Green92.green_92.variants.chase_upper := by
  obtain ⟨C, hC, h⟩ := OMA.G92Upper.pairwise_tests
  refine ⟨C, hC, ?_⟩
  filter_upwards [h] with n hn
  obtain ⟨D, hD, hf⟩ := hn
  exact Nat.sInf_le (OMA.G92Upper.decoder_of_tests _ _ D hD hf)
