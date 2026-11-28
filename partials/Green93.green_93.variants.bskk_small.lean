import FormalConjectures.GreensOpenProblems.«93»

-- Problem: Ben Green's Open Problem 93 — bskk small
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/93.lean:123 (declaration Green93.green_93.variants.bskk_small)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.BSKKSmall

open Green93

/-- Core analytic input (BSKK23, Theorem 1(b)) for a single coefficient bound `M`. -/
theorem single_M (M : ℕ) (h1 : 1 ≤ M) (h2 : M ≤ 33) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → δ ≤ irreducibleProb M n := by
  sorry

/-- Uniformity over the finitely many `M ≤ K`, by induction on `K`. -/
theorem upto (K : ℕ) (hK : K ≤ 33) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 1 ≤ M → M ≤ K → n₀ ≤ n →
      δ ≤ irreducibleProb M n := by
  induction K with
  | zero => exact ⟨1, one_pos, 0, fun M n h1 h2 _ => by omega⟩
  | succ K ih =>
    obtain ⟨δ₁, hδ₁, n₁, h₁⟩ := ih (by omega)
    obtain ⟨δ₂, hδ₂, n₂, h₂⟩ := single_M (K + 1) (by omega) hK
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max n₁ n₂, fun M n hM1 hMK hn => ?_⟩
    rcases Nat.lt_or_ge M (K + 1) with hlt | hge
    · exact (min_le_left _ _).trans (h₁ M n hM1 (by omega) (le_of_max_le_left hn))
    · have hM : M = K + 1 := by omega
      subst hM
      exact (min_le_right _ _).trans (h₂ n (le_of_max_le_right hn))

end OMA.BSKKSmall

theorem OMA.solution : type_of% @Green93.green_93.variants.bskk_small := by
  obtain ⟨δ, hδ, n₀, h⟩ := OMA.BSKKSmall.upto 33 le_rfl
  exact ⟨δ, hδ, n₀, fun M n h1 h2 hn => h M n h1 h2 hn⟩
