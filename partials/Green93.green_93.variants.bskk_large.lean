import FormalConjectures.GreensOpenProblems.«93»

-- Problem: Ben Green's Open Problem 93 — bskk large
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/93.lean:139 (declaration Green93.green_93.variants.bskk_large)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

namespace BSKKLarge

/-- Constant coefficient of `monicPoly a` for positive degree. -/
lemma monicPoly_coeff_zero {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℕ) :
    (Green93.monicPoly a).coeff 0 = (a ⟨0, hn⟩ : ℤ) := by
  unfold Green93.monicPoly
  rw [coeff_add, coeff_X_pow, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  have h0 : (0 : ℕ) ≠ n := by omega
  rw [if_neg h0, zero_add]
  rw [Finset.sum_eq_single ⟨0, hn⟩]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
    rw [if_neg (Ne.symm this)]
  · simp

/-- The conditioning set is nonempty. -/
lemma eligible_nonempty (M n : ℕ) (hM : 1 ≤ M) :
    (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).Nonempty := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨default, ?_⟩
    simp [Green93.monicPoly]; exact Subsingleton.elim _ _
  · refine ⟨fun _ => ⟨1, by omega⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [monicPoly_coeff_zero hn]
    simp

open scoped Classical in
/-- The genuine BSKK23 Theorem 1(a) content: the reducible eligible polynomials form a
fraction at most n^(-c). OPEN (research-level counting argument). -/
lemma core :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) ↦
          ¬ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))).card : ℝ) ≤
      (n : ℝ) ^ (-c) * ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ) := by
  sorry

end BSKKLarge

theorem OMA.solution : type_of% @Green93.green_93.variants.bskk_large := by
  classical
  obtain ⟨c, hc, n₀, h⟩ := BSKKLarge.core
  refine ⟨c, hc, n₀, fun M n hM hn hlog => ?_⟩
  have hb := h M n hM hn hlog
  set E := (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0) with hE
  have hEpos : (0 : ℝ) < E.card := by
    exact_mod_cast (BSKKLarge.eligible_nonempty M n (by omega)).card_pos
  have hsplit := Finset.card_filter_add_card_filter_not (s := E)
    (p := fun a ↦ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ)))
  have hI : (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
        Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))) =
      E.filter (fun a ↦ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))) := by
    rw [hE, Finset.filter_filter]
  unfold Green93.irreducibleProb
  rw [hI, ← hE, le_div_iff₀ hEpos]
  have hcast : ((E.filter fun a ↦ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))).card : ℝ)
      + ((E.filter fun a ↦ ¬ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))).card : ℝ)
      = E.card := by exact_mod_cast hsplit
  have hb' : ((E.filter fun a ↦ ¬ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))).card : ℝ)
      ≤ (n : ℝ) ^ (-c) * (E.card : ℝ) := by
    convert hb using 4
  nlinarith
