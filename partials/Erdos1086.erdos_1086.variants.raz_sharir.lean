import FormalConjectures.ErdosProblems.«1086»

-- Problem: Erdős Problem 1086 — raz sharir
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1086.lean:97 (declaration Erdos1086.erdos_1086.variants.raz_sharir)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics
open scoped EuclideanGeometry

namespace OMA.RazSharir

open Erdos1086

/-- Core Raz-Sharir estimate (open leaf): uniform bound for every positive area. -/
theorem core : ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset ℝ²) (a : ℝ), 0 < a →
    (triangleAreaCount P a : ℝ) ≤ C * (P.card : ℝ) ^ (20 / 9 : ℝ) := by
  sorry

/-- Glue: a uniform bound for all point sets gives the big-O statement for `g`. -/
theorem glue (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset ℝ²) (a : ℝ), 0 < a →
    (triangleAreaCount P a : ℝ) ≤ C * (P.card : ℝ) ^ (20 / 9 : ℝ)) :
    (fun n : ℕ ↦ (g n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (20 / 9 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := h
  refine Asymptotics.isBigO_iff.mpr ⟨C, Filter.Eventually.of_forall fun n => ?_⟩
  have hp : 0 ≤ (n : ℝ) ^ (20 / 9 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg hp]
  have hB : 0 ≤ C * (n : ℝ) ^ (20 / 9 : ℝ) := mul_nonneg hC hp
  rw [← Nat.le_floor_iff hB]
  unfold g
  apply csSup_le'
  rintro m ⟨P, a, hP, ha, rfl⟩
  rw [Nat.le_floor_iff hB, ← hP]
  exact hb P a ha

end OMA.RazSharir

theorem OMA.solution : type_of% @Erdos1086.erdos_1086.variants.raz_sharir := by
  exact OMA.RazSharir.glue OMA.RazSharir.core
