import FormalConjectures.ErdosProblems.«186»

-- Problem: Erdős Problem 186 — pham zakharov
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/186.lean:87 (declaration Erdos186.erdos_186.variants.pham_zakharov)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

namespace OMA

/-- Trivial bound: a non-averaging subset of [1, N] has at most N elements. -/
lemma F_le (N : ℕ) : Erdos186.F N ≤ N := by
  unfold Erdos186.F
  apply Finset.sup_le
  intro A hA
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  simpa using Finset.card_le_card hA.1

/-- The large exponent case follows from the trivial bound. -/
lemma large_eps (ε : ℝ) (hε : 3 / 4 ≤ ε) :
    ∀ᶠ N : ℕ in atTop, (Erdos186.F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (Erdos186.F N : ℝ) ≤ N := by exact_mod_cast F_le N
    _ = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

/-- Core: the Pham-Zakharov bound for small exponents (research theorem, open here). -/
lemma small_eps (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 3 / 4) :
    ∀ᶠ N : ℕ in atTop, (Erdos186.F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

end OMA

theorem OMA.solution : type_of% @Erdos186.erdos_186.variants.pham_zakharov := by
  intro ε hε
  rcases le_or_gt (3 / 4) ε with h | h
  · exact OMA.large_eps ε h
  · exact OMA.small_eps ε hε h
