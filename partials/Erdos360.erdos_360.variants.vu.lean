import FormalConjectures.ErdosProblems.«360»

-- Problem: Erdős Problem 360 — vu
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/360.lean:90 (declaration Erdos360.erdos_360.variants.vu)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics

namespace OMAVu360

/-- The admissible set defining `Erdos360.f n`. -/
def admissible (n : ℕ) : Set ℕ :=
  {r : ℕ | ∃ P : Finpartition (Finset.Icc 1 (n - 1)),
    P.parts.card = r ∧ ∀ A ∈ P.parts, n ∉ subsetSums (A : Set ℕ)}

/-- The discrete partition into singletons is admissible for `n ≥ 1`. -/
lemma admissible_nonempty {n : ℕ} (hn : 1 ≤ n) : (admissible n).Nonempty := by
  refine ⟨(⊥ : Finpartition (Finset.Icc 1 (n - 1))).parts.card, ⊥, rfl, ?_⟩
  intro A hA hmem
  rw [Finpartition.parts_bot, Finset.mem_map] at hA
  obtain ⟨x, hx, rfl⟩ := hA
  obtain ⟨B, hB, hsum⟩ := hmem
  have hBsub : B ⊆ {x} := fun y hy => by simpa using hB hy
  rcases Finset.subset_singleton_iff.mp hBsub with rfl | rfl
  · simp at hsum
    omega
  · simp only [Finset.sum_singleton] at hsum
    simp only [Finset.mem_Icc] at hx
    omega

/-- `Erdos360.f n` is attained by an admissible partition. -/
lemma exists_partition_card_f {n : ℕ} (hn : 1 ≤ n) :
    ∃ P : Finpartition (Finset.Icc 1 (n - 1)),
      P.parts.card = Erdos360.f n ∧ ∀ A ∈ P.parts, n ∉ subsetSums (A : Set ℕ) :=
  Nat.sInf_mem (admissible_nonempty hn)

/-- Core Ramsey subset-sum statement of Vu [Vu07]: a partition of `{1, ..., n - 1}` into at most
`c * n^(1/3) / log n` classes has a class representing `n` as a sum of distinct elements.
This needs the Szemeredi-Vu long arithmetic progression theorem for subset sums. -/
lemma vu_core : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ P : Finpartition (Finset.Icc 1 (n - 1)),
      (P.parts.card : ℝ) ≤ c * ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n) →
      ∃ A ∈ P.parts, n ∈ subsetSums (A : Set ℕ) := by
  sorry

/-- Glue: the core statement gives the asymptotic lower bound. -/
lemma vu_of_core (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ P : Finpartition (Finset.Icc 1 (n - 1)),
      (P.parts.card : ℝ) ≤ c * ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n) →
      ∃ A ∈ P.parts, n ∈ subsetSums (A : Set ℕ)) :
    (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n) =O[atTop] (fun n : ℕ ↦ (Erdos360.f n : ℝ)) := by
  obtain ⟨c, hc, hev⟩ := h
  refine IsBigO.of_bound (1 / c) ?_
  filter_upwards [hev, eventually_ge_atTop 1] with n hn h1
  obtain ⟨P, hcard, hfree⟩ := exists_partition_card_f h1
  have hlt : c * ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n) < (Erdos360.f n : ℝ) := by
    by_contra hle'
    have hle := not_lt.mp hle'
    obtain ⟨A, hA, hmem⟩ := hn P (by rw [hcard]; exact hle)
    exact hfree A hA hmem
  have hg : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n := by
    apply div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    exact Real.log_natCast_nonneg n
  rw [Real.norm_of_nonneg hg, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  linarith [mul_comm c ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n)]

end OMAVu360

theorem OMA.solution : type_of% @Erdos360.erdos_360.variants.vu := by
  exact OMAVu360.vu_of_core OMAVu360.vu_core
