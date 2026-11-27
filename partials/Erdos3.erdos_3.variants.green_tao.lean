import FormalConjectures.ErdosProblems.«3»

-- Problem: Erdős Problem 3 — green tao
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/3.lean:97 (declaration Erdos3.erdos_3.variants.green_tao)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Asymptotics Filter

namespace OMA

/-- Freeness in the formal-conjectures sense rules out four members
a, a + d, a + 2 d, a + 3 d with a positive step d. -/
lemma free_elem {S : Finset ℕ} (hS : (S : Set ℕ).IsAPOfLengthFree 4) (a d : ℕ) (hd : 0 < d)
    (h0 : a ∈ S) (h1 : a + d ∈ S) (h2 : a + 2 * d ∈ S) (h3 : a + 3 * d ∈ S) : False := by
  classical
  have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro m n hmn
    have hmul : m * d = n * d := Nat.add_left_cancel hmn
    exact Nat.eq_of_mul_eq_mul_right hd hmul
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = (Finset.range 4).image (fun n : ℕ => a + n * d) :=
    ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ T ↔ ∃ n, n < 4 ∧ a + n * d = x := by
    intro x
    rw [hT]
    simp
  have hcard : T.card = 4 := by
    rw [hT, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub : (T : Set ℕ) ⊆ (S : Set ℕ) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := (hmem x).mp hx
    interval_cases n
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  have hAP : (T : Set ℕ).IsAPOfLength 4 := by
    refine ⟨a, d, ?_, ?_⟩
    · change (T : Set ℕ).encard = 4
      rw [Set.encard_coe_eq_coe_finsetCard, hcard]
      rfl
    · ext x
      constructor
      · intro hx
        obtain ⟨n, hn, rfl⟩ := (hmem x).mp hx
        exact ⟨n, by exact_mod_cast hn, by simp⟩
      · rintro ⟨n, hn, rfl⟩
        exact (hmem _).mpr ⟨n, by exact_mod_cast hn, by simp⟩
  have hbad := hS _ hsub hAP
  norm_num at hbad

/-- A uniform bound on all admissible sets bounds the extremal function. -/
lemma r_le_of_forall (N B : ℕ)
    (h : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → (S : Set ℕ).IsAPOfLengthFree 4 → S.card ≤ B) :
    Erdos3.r 4 N ≤ B := by
  show sSup _ ≤ B
  apply csSup_le'
  rintro _ ⟨S, hS, hfree, rfl⟩
  exact h S hS hfree

/-- The elementary core: the Green and Tao polylogarithmic bound for sets of
integers without four members in arithmetic progression. This is the whole
mathematical content of the target. -/
theorem core : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ,
    S ⊆ Finset.Icc 1 N →
    (∀ a d : ℕ, 0 < d → a ∈ S → a + d ∈ S → a + 2 * d ∈ S → a + 3 * d ∈ S → False) →
    (S.card : ℝ) ≤ C * ((N : ℝ) * Real.log N ^ (-c)) := by
  sorry

end OMA

theorem OMA.solution : type_of% @Erdos3.erdos_3.variants.green_tao := by
  obtain ⟨c, hc, C, hC, N₀, hcore⟩ := OMA.core
  refine ⟨c, hc, Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (max 3 N₀)] with N hN'
  have hN : 3 ≤ N := le_trans (le_max_left 3 N₀) hN'
  have hN₀ : N₀ ≤ N := le_trans (le_max_right 3 N₀) hN'
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpow : 0 ≤ Real.log (N : ℝ) ^ (-c) := Real.rpow_nonneg hlog (-c)
  have hy : 0 ≤ (N : ℝ) * Real.log (N : ℝ) ^ (-c) := by positivity
  have hx : 0 ≤ C * ((N : ℝ) * Real.log (N : ℝ) ^ (-c)) := by positivity
  have hr : Erdos3.r 4 N ≤ ⌊C * ((N : ℝ) * Real.log (N : ℝ) ^ (-c))⌋₊ := by
    apply OMA.r_le_of_forall
    intro S hS hfree
    rw [Nat.le_floor_iff hx]
    exact hcore N hN₀ S hS (OMA.free_elem hfree)
  have hr' : (Erdos3.r 4 N : ℝ) ≤ C * ((N : ℝ) * Real.log (N : ℝ) ^ (-c)) :=
    le_trans (by exact_mod_cast hr) (Nat.floor_le hx)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hy]
  exact hr'
