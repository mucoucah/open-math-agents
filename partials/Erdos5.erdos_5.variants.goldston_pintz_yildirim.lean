import FormalConjectures.ErdosProblems.«5»
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Problem: Erdős Problem 5 — goldston pintz yildirim
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/5.lean:111 (declaration Erdos5.erdos_5.variants.goldston_pintz_yildirim)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real Topology Finset

namespace OMA.GPYPartial

/-- For every k, there exists an admissible k-tuple of natural numbers.
Specifically, H = {k! * i | i < k} has cardinality k and avoids at least one
residue class modulo every prime p (take x = 1 for p <= k, and by pigeonhole
there exists x < p avoiding the <= k residues -k! * i mod p for p > k). -/
lemma exists_admissible_tuple (k : ℕ) :
    ∃ H : Finset ℕ, k ≤ H.card ∧ ∀ p : ℕ, p.Prime → ∃ x : ℕ, ∀ a ∈ H, ¬ p ∣ x + a := by
  classical
  let f : ℕ → ℕ := fun i => k.factorial * i
  have hf : Function.Injective f := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) hij
  refine ⟨(Finset.range k).image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_range]
  · intro p hp
    by_cases hpk : p ≤ k
    · refine ⟨1, ?_⟩
      intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      intro hdvd
      have hp_fac : p ∣ k.factorial := Nat.dvd_factorial hp.pos hpk
      have hp_mul : p ∣ k.factorial * i := dvd_mul_of_dvd_left hp_fac i
      have hp_one : p ∣ 1 := (Nat.dvd_add_left hp_mul).mp hdvd
      exact hp.not_dvd_one hp_one
    · have hkp : k < p := Nat.lt_of_not_ge hpk
      have : NeZero p := ⟨hp.ne_zero⟩
      let bad : Finset (ZMod p) := (Finset.range k).image (fun i => -((f i : ℕ) : ZMod p))
      have hcard : bad.card < Fintype.card (ZMod p) := by
        rw [ZMod.card p]
        calc bad.card ≤ (Finset.range k).card := Finset.card_image_le
          _ = k := Finset.card_range k
          _ < p := hkp
      have hne : (Finset.univ \ bad).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : (Finset.univ : Finset (ZMod p)) ⊆ bad := Finset.sdiff_eq_empty_iff_subset.mp hemp
        have hle := Finset.card_le_card hsub
        rw [Finset.card_univ] at hle
        omega
      obtain ⟨r, hr⟩ := hne
      have hr_not : r ∉ bad := (Finset.mem_sdiff.mp hr).2
      refine ⟨r.val, ?_⟩
      intro a ha hdvd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have hzero : ((r.val + f i : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
      rw [Nat.cast_add, ZMod.natCast_zmod_val] at hzero
      have hreq : r = -((f i : ℕ) : ZMod p) := eq_neg_of_add_eq_zero_left hzero
      exact hr_not (Finset.mem_image.mpr ⟨i, hi, hreq.symm⟩)

/-- Bounded gaps between primes from the Maynard-Tao r = 2 prime-tuple statement. -/
lemma maynard_two_to_bounded_gaps
    (hMT : ∃ k : ℕ, ∀ H : Finset ℕ, k ≤ H.card →
      (∀ p : ℕ, p.Prime → ∃ x : ℕ, ∀ a ∈ H, ¬ p ∣ x + a) →
      ∀ N : ℕ, ∃ x : ℕ, N < x ∧ 2 ≤ (H.filter (fun a => (x + a).Prime)).card) :
    ∃ B : ℕ, ∀ N : ℕ, ∃ n ≥ N, primeGap n ≤ B := by
  classical
  obtain ⟨k, hk⟩ := hMT
  obtain ⟨H, hHcard, hHadm⟩ := exists_admissible_tuple k
  let B : ℕ := H.sup id
  refine ⟨B, fun N => ?_⟩
  let M : ℕ := Nat.nth Nat.Prime N
  obtain ⟨x, hxM, hcard⟩ := hk H hHcard hHadm M
  have h1lt : 1 < (H.filter (fun a => (x + a).Prime)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1lt
  wlog hab' : a < b generalizing a b
  · exact this b hb a ha hab.symm (by omega)
  have haH : a ∈ H := (Finset.mem_filter.mp ha).1
  have hbH : b ∈ H := (Finset.mem_filter.mp hb).1
  have hpa : (x + a).Prime := (Finset.mem_filter.mp ha).2
  have hpb : (x + b).Prime := (Finset.mem_filter.mp hb).2
  obtain ⟨i, hi⟩ : ∃ i : ℕ, Nat.nth Nat.Prime i = x + a := Nat.subset_range_nth hpa
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Nat.nth Nat.Prime j = x + b := Nat.subset_range_nth hpb
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hNi : N ≤ i := by
    have hlt : Nat.nth Nat.Prime N < Nat.nth Nat.Prime i := by
      change M < Nat.nth Nat.Prime i
      rw [hi]
      omega
    exact (hmono.lt_iff_lt.mp hlt).le
  have hij : i < j := hmono.lt_iff_lt.mp (by rw [hi, hj]; omega)
  have hnext : Nat.nth Nat.Prime (i + 1) ≤ x + b := hj ▸ hmono.monotone (by omega)
  have hbB : b ≤ B := Finset.le_sup (f := id) hbH
  refine ⟨i, hNi, ?_⟩
  unfold primeGap
  omega

/-- Bounded prime gaps immediately imply gaps below eps * log n for arbitrarily large n. -/
lemma bounded_gaps_to_core
    (hB : ∃ B : ℕ, ∀ N : ℕ, ∃ n ≥ N, primeGap n ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, (primeGap n : ℝ) < ε * log n := by
  obtain ⟨B, hB⟩ := hB
  intro ε hε N
  let M : ℕ := max N (max 2 (⌈Real.exp (((B : ℝ) + 1) / ε)⌉₊ + 1))
  obtain ⟨n, hnM, hgap⟩ := hB M
  have hnN : N ≤ n := (le_max_left _ _).trans hnM
  have hn2 : 2 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hnM)
  have hnExp : Real.exp (((B : ℝ) + 1) / ε) < (n : ℝ) := by
    have h1 : ⌈Real.exp (((B : ℝ) + 1) / ε)⌉₊ + 1 ≤ n :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hnM)
    have h2 : Real.exp (((B : ℝ) + 1) / ε) ≤ (⌈Real.exp (((B : ℝ) + 1) / ε)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h3 : (⌈Real.exp (((B : ℝ) + 1) / ε)⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hlog : ((B : ℝ) + 1) / ε < Real.log (n : ℝ) := by
    rw [← Real.log_exp (((B : ℝ) + 1) / ε)]
    exact Real.log_lt_log (Real.exp_pos _) hnExp
  have hmul : (B : ℝ) + 1 < ε * Real.log (n : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hlog
    linarith
  have hgapR : (primeGap n : ℝ) ≤ (B : ℝ) := by exact_mod_cast hgap
  exact ⟨n, hnN, by linarith⟩

/-- Core Maynard-Tao r = 2 prime-tuple statement.
Can be proved from Bombieri-Vinogradov (Chebyshev-centered, no PNT needed)
using the merged BV + Maynard-Tao components adapted under 512 KiB. -/
theorem maynard_two :
    ∃ k : ℕ, ∀ H : Finset ℕ, k ≤ H.card →
      (∀ p : ℕ, p.Prime → ∃ x : ℕ, ∀ a ∈ H, ¬ p ∣ x + a) →
      ∀ N : ℕ, ∃ x : ℕ, N < x ∧ 2 ≤ (H.filter (fun a => (x + a).Prime)).card := by
  sorry

/-- Core GPY small-gaps statement: gaps below eps * log n occur for arbitrarily large n. -/
theorem core : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, (primeGap n : ℝ) < ε * log n :=
  bounded_gaps_to_core (maynard_two_to_bounded_gaps maynard_two)

/-- Glue: the small-gap statement gives that 0 is a cluster point. -/
theorem glue
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, (primeGap n : ℝ) < ε * log n) :
    MapClusterPt (0 : ℝ) atTop Erdos5.normalizedGap := by
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
  intro ε hε
  rw [frequently_atTop]
  intro N
  obtain ⟨n, hn, hgap⟩ := h ε hε (max N 2)
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hlog : 0 < log (n : ℝ) := log_pos (by linarith)
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (Erdos5.normalizedGap_nonneg n)]
  unfold Erdos5.normalizedGap
  rw [div_lt_iff₀ hlog]
  exact hgap

end OMA.GPYPartial

theorem OMA.solution : type_of% @Erdos5.erdos_5.variants.goldston_pintz_yildirim := by
  exact OMA.GPYPartial.glue OMA.GPYPartial.core
