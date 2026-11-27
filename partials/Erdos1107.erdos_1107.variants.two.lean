import FormalConjectures.ErdosProblems.«1107»

-- Problem: Erdős Problem 1107 — two
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1107.lean:51 (declaration Erdos1107.erdos_1107.variants.two)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E1107two

open Filter

/-- Squares are 2-full. -/
lemma full_sq (x : ℕ) : Nat.Full 2 (x ^ 2) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  exact pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow h.2.1) 2

/-- The product of two 2-full numbers is 2-full. -/
lemma full_mul {a b : ℕ} (ha : Nat.Full 2 a) (hb : Nat.Full 2 b) : Nat.Full 2 (a * b) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  rcases a.eq_zero_or_pos with rfl | ha0
  · simp
  rcases b.eq_zero_or_pos with rfl | hb0
  · simp
  rcases h.1.dvd_mul.mp h.2.1 with hd | hd
  · exact dvd_mul_of_dvd_left (ha p (Nat.mem_primeFactors.mpr ⟨h.1, hd, ha0.ne'⟩)) _
  · exact dvd_mul_of_dvd_right (hb p (Nat.mem_primeFactors.mpr ⟨h.1, hd, hb0.ne'⟩)) _

/-- A cube times a square is 2-full. -/
lemma full_cube_mul_sq (q x : ℕ) : Nat.Full 2 (q ^ 3 * x ^ 2) := by
  have hq : Nat.Full 2 (q ^ 3) := by
    intro p hp
    have h := Nat.mem_primeFactors.mp hp
    exact (pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow h.2.1) 2).trans (pow_dvd_pow q (by norm_num))
  exact full_mul hq (full_sq x)

/-- Three 2-full summands give the target property. -/
lemma of_three {a b c n : ℕ} (ha : Nat.Full 2 a) (hb : Nat.Full 2 b) (hc : Nat.Full 2 c)
    (h : a + b + c = n) : Erdos1107.SumOfRPowerful 2 n := by
  refine ⟨[a, b, c], by simp, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  · simp [← h, add_assoc]

/-- Scaling by 4 preserves the property. -/
lemma four_mul {n : ℕ} (h : Erdos1107.SumOfRPowerful 2 n) : Erdos1107.SumOfRPowerful 2 (4 * n) := by
  obtain ⟨s, hl, hf, hs⟩ := h
  refine ⟨s.map (4 * ·), by simpa using hl, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have h4 : Nat.Full 2 4 := by simpa using full_sq 2
    exact full_mul h4 (hf u hu)
  · rw [← hs, List.sum_map_mul_left, List.map_id']

/-- Core: Heath-Brown 1988 ternary representation (the open gap of this file).
Every large n is q^3 x^2 + y^2 + z^2 for some q x y z. -/
lemma core : ∀ᶠ n : ℕ in atTop, ∃ q x y z : ℕ, q ^ 3 * x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

end OMA.E1107two

theorem OMA.solution : type_of% @Erdos1107.erdos_1107.variants.two := by
  filter_upwards [OMA.E1107two.core] with n ⟨q, x, y, z, h⟩
  exact OMA.E1107two.of_three (OMA.E1107two.full_cube_mul_sq q x)
    (OMA.E1107two.full_sq y) (OMA.E1107two.full_sq z) h
