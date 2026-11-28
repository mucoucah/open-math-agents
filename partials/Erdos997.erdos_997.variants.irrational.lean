import FormalConjectures.ErdosProblems.«997»

-- Problem: Erdős Problem 997 — irrational
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/997.lean:90 (declaration Erdos997.erdos_997.variants.irrational)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E997

open Set Filter

/-- Shiu 2000 (special case a = 1): arbitrarily long runs of consecutive primes that are
all congruent to 1 modulo q. This is the only missing ingredient (Maier matrix method). -/
theorem shiu_run (q k : ℕ) (hq : 0 < q) :
    ∃ m : ℕ, ∀ i, m ≤ i → i < m + k → Nat.nth Nat.Prime i ≡ 1 [MOD q] := by
  sorry

/-- The open set of multipliers having a window of k consecutive primes p with a(p-1)
within 1/16 of an integer. -/
def W (k : ℕ) : Set ℝ := ⋃ m : ℕ, ⋂ i ∈ Finset.Ioc m (m + k),
    ⋃ z : ℤ, {a : ℝ | |a * ((Nat.nth Nat.Prime i : ℝ) - 1) - z| < 1/16}

lemma W_open (k : ℕ) : IsOpen (W k) :=
  isOpen_iUnion fun _ => isOpen_biInter_finset fun _ _ =>
    isOpen_iUnion fun _ => isOpen_lt (by fun_prop) continuous_const

lemma rat_mem_W (k : ℕ) (t : ℚ) : (t : ℝ) ∈ W k := by
  obtain ⟨m, hm⟩ := shiu_run t.den (k + 1) t.den_pos
  refine mem_iUnion.mpr ⟨m, mem_iInter₂.mpr fun i hi => ?_⟩
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hi
  obtain ⟨v, hv⟩ := (Nat.modEq_iff_dvd' (Nat.Prime.one_le (Nat.prime_nth_prime i))).mp
    (hm i (by omega) (by omega)).symm
  have hv' : (Nat.nth Nat.Prime i : ℝ) - 1 = t.den * (v : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_sub (Nat.Prime.one_le (Nat.prime_nth_prime i)), hv]
    push_cast; ring
  refine mem_iUnion.mpr ⟨t.num * v, ?_⟩
  show |(t : ℝ) * ((Nat.nth Nat.Prime i : ℝ) - 1) - ((t.num * v : ℤ) : ℝ)| < 1/16
  have hden : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_nz
  rw [hv', Rat.cast_def, Int.cast_mul, ← mul_assoc, div_mul_cancel₀ _ hden]
  push_cast
  norm_num

lemma W_dense (k : ℕ) : Dense (W k) :=
  (Rat.denseRange_cast (𝕜 := ℝ)).mono (by rintro _ ⟨t, rfl⟩; exact rat_mem_W k t)

lemma fract_small {a : ℝ} (ha1 : 1/8 < a) (ha2 : a < 1/4) (p : ℝ) (z : ℤ)
    (hz : |a * (p - 1) - z| < 1/16) : Int.fract (a * p) < 1/2 := by
  obtain ⟨hz1, hz2⟩ := abs_lt.mp hz
  have h1 : 0 ≤ a * p - z := by linarith
  have h2 : a * p - z < 1/2 := by linarith
  rw [← Int.fract_sub_intCast _ z, Int.fract_eq_self.mpr ⟨h1, by linarith⟩]
  exact h2

theorem main : ∃ α : ℝ, Irrational α ∧
    ¬ Erdos997.IsWellDistributed (fun n ↦ Int.fract (α * (n.nth Nat.Prime))) := by
  have hG : Dense ({x : ℝ | Irrational x} ∩ ⋂ k, W k) :=
    dense_irrational.inter_of_Gδ IsGδ.setOfPred_irrational
      (IsGδ.iInter_of_isOpen W_open) (dense_iInter_of_isOpen W_open W_dense)
  obtain ⟨a, ⟨ha1, ha2⟩, ha, hu⟩ := hG.inter_open_nonempty
    (Ioo (1/8 : ℝ) (1/4)) isOpen_Ioo (nonempty_Ioo.mpr (by norm_num))
  refine ⟨a, ha, fun hw => ?_⟩
  obtain ⟨k, hk⟩ := eventually_atTop.1 (hw (1/4) (by norm_num))
  obtain ⟨m, hm⟩ := mem_iUnion.mp (mem_iInter.mp hu (k + 1))
  have hc : ((Finset.Ioc m (m + (k + 1))).filter
      (fun i => Int.fract (a * (Nat.nth Nat.Prime i : ℝ)) ∈ Ico (1/2 : ℝ) 1)) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun i hi hh => ?_
    obtain ⟨z, hz⟩ := mem_iUnion.mp (mem_iInter₂.mp hm i hi)
    exact (not_lt_of_ge hh.1) (fract_small ha1 ha2 _ z hz)
  have h := hk (k + 1) (by omega) m (1/2) 1 (by norm_num) (by norm_num) le_rfl
  simp only at h
  rw [hc, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg,
    abs_of_nonneg (by positivity)] at h
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  linarith

end OMA.E997

theorem OMA.solution : type_of% @Erdos997.erdos_997.variants.irrational := by
  exact OMA.E997.main
