import FormalConjectures.ErdosProblems.«165»

-- Problem: Erdős Problem 165 — conjecture
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/165.lean:69 (declaration Erdos165.erdos_165.variants.conjecture)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- STATUS (leg 4): the target is the OPEN conjecture R(3,k) ~ k^2/(2 log k).
-- Only glue is proved here: the asymptotic equivalence follows from the two one-sided bounds
-- (lower = the HHKP25 theorem, same shape as upstream variants.lower; upper with constant 1/2 = open).
-- The single hole (OMA.core_two_sided) is exactly those two bounds.

open Filter Asymptotics
open scoped Topology

/-- The conjectured main term is positive from `k = 2` on. -/
lemma OMA.main_term_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < (k : ℝ) ^ 2 / (2 * Real.log k) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hk)
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  positivity

/-- Glue: the two one-sided bounds (stated in the shape of the upstream `variants.lower`
and its mirror image) give the asymptotic equivalence. -/
lemma OMA.of_two_sided
    (hlo : ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (1 / 2 - ε) * (k : ℝ) ^ 2 / Real.log k ≤ (SimpleGraph.classicalRamsey 3 k : ℝ))
    (hup : ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (SimpleGraph.classicalRamsey 3 k : ℝ) ≤ (1 / 2 + ε) * (k : ℝ) ^ 2 / Real.log k) :
    (fun k : ℕ ↦ (SimpleGraph.classicalRamsey 3 k : ℝ)) ~[atTop]
      (fun k : ℕ ↦ (k : ℝ) ^ 2 / (2 * Real.log k)) := by
  apply isEquivalent_of_tendsto_one
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / 4 := by positivity
  filter_upwards [hlo (ε / 4) hδ, hup (ε / 4) hδ, eventually_ge_atTop 2] with k hlo' hup' hk
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hk)
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hL : Real.log (k : ℝ) ≠ 0 := hlog.ne'
  have hg : 0 < (k : ℝ) ^ 2 / (2 * Real.log k) := OMA.main_term_pos hk
  have e1 : (1 / 2 - ε / 4) * (k : ℝ) ^ 2 / Real.log k
      = (1 - ε / 2) * ((k : ℝ) ^ 2 / (2 * Real.log k)) := by
    field_simp
    ring
  have e2 : (1 / 2 + ε / 4) * (k : ℝ) ^ 2 / Real.log k
      = (1 + ε / 2) * ((k : ℝ) ^ 2 / (2 * Real.log k)) := by
    field_simp
    ring
  rw [e1] at hlo'
  rw [e2] at hup'
  rw [Pi.div_apply, Real.dist_eq]
  have hrlo : 1 - ε / 2 ≤
      (SimpleGraph.classicalRamsey 3 k : ℝ) / ((k : ℝ) ^ 2 / (2 * Real.log k)) :=
    (le_div_iff₀ hg).2 hlo'
  have hrup : (SimpleGraph.classicalRamsey 3 k : ℝ) / ((k : ℝ) ^ 2 / (2 * Real.log k))
      ≤ 1 + ε / 2 :=
    (div_le_iff₀ hg).2 hup'
  rw [abs_lt]
  constructor <;> linarith

/-- Converse glue: the asymptotic equivalence gives back both one-sided bounds, so the
hole below is exactly as strong as the target (nothing is lost by the reformulation). -/
lemma OMA.two_sided_of_equiv
    (h : (fun k : ℕ ↦ (SimpleGraph.classicalRamsey 3 k : ℝ)) ~[atTop]
      (fun k : ℕ ↦ (k : ℝ) ^ 2 / (2 * Real.log k))) :
    (∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (1 / 2 - ε) * (k : ℝ) ^ 2 / Real.log k ≤ (SimpleGraph.classicalRamsey 3 k : ℝ)) ∧
    (∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (SimpleGraph.classicalRamsey 3 k : ℝ) ≤ (1 / 2 + ε) * (k : ℝ) ^ 2 / Real.log k) := by
  have hbound : ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      |(SimpleGraph.classicalRamsey 3 k : ℝ) - (k : ℝ) ^ 2 / (2 * Real.log k)|
        ≤ (2 * ε) * ((k : ℝ) ^ 2 / (2 * Real.log k)) := by
    intro ε hε
    have h2 : (0 : ℝ) < 2 * ε := by positivity
    have ho := (Asymptotics.isLittleO_iff.1 h.isLittleO) h2
    filter_upwards [ho, eventually_ge_atTop 2] with k hk hk2
    have hg : 0 < (k : ℝ) ^ 2 / (2 * Real.log k) := OMA.main_term_pos hk2
    have hk' : ‖(SimpleGraph.classicalRamsey 3 k : ℝ) - (k : ℝ) ^ 2 / (2 * Real.log k)‖
        ≤ (2 * ε) * ‖(k : ℝ) ^ 2 / (2 * Real.log k)‖ := hk
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hg] at hk'
    exact hk'
  constructor
  · intro ε hε
    filter_upwards [hbound ε hε, eventually_ge_atTop 2] with k hk hk2
    have hk1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hk2)
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hk1
    have hL : Real.log (k : ℝ) ≠ 0 := hlog.ne'
    have e1 : (1 / 2 - ε) * (k : ℝ) ^ 2 / Real.log k
        = (1 - 2 * ε) * ((k : ℝ) ^ 2 / (2 * Real.log k)) := by
      field_simp
    rw [e1]
    have := (abs_le.1 hk).1
    linarith
  · intro ε hε
    filter_upwards [hbound ε hε, eventually_ge_atTop 2] with k hk hk2
    have hk1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hk2)
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hk1
    have hL : Real.log (k : ℝ) ≠ 0 := hlog.ne'
    have e2 : (1 / 2 + ε) * (k : ℝ) ^ 2 / Real.log k
        = (1 + 2 * ε) * ((k : ℝ) ^ 2 / (2 * Real.log k)) := by
      field_simp
    rw [e2]
    have := (abs_le.1 hk).2
    linarith

/-- THE GAP (open problem). First half: the Hefty-Horn-King-Pfender lower bound (a theorem,
research level, not in Mathlib). Second half: the upper bound with constant 1/2, which is
OPEN (Shearer only gives constant 1). -/
lemma OMA.core_two_sided :
    (∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (1 / 2 - ε) * (k : ℝ) ^ 2 / Real.log k ≤ (SimpleGraph.classicalRamsey 3 k : ℝ)) ∧
    (∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (SimpleGraph.classicalRamsey 3 k : ℝ) ≤ (1 / 2 + ε) * (k : ℝ) ^ 2 / Real.log k) := by
  sorry

theorem OMA.solution : type_of% @Erdos165.erdos_165.variants.conjecture := by
  exact OMA.of_two_sided OMA.core_two_sided.1 OMA.core_two_sided.2
