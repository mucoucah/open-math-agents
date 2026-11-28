import FormalConjectures.ErdosProblems.«964»
import Mathlib

-- Problem: Erdős Problem 964 — eberhard
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/964.lean:69 (declaration Erdos964.erdos_964.variants.eberhard)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Mertens 1st/2nd helper bounds adapted from proofs/Erdos46.erdos_46.variants.positive_rat.R1.H2.lean;
-- CRT normalization pattern adapted from @marcusbuffett PR #3641 (Erdos964 R1.H1.R1.H2).
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Elementary proof of Eberhard's theorem (arXiv:2505.00727) via K-tuple synchronization
and the K-dimensional Selberg sieve (bypassing GGPY and Bombieri-Vinogradov). -/

namespace OMA964

open scoped ArithmeticFunction.sigma

/-- Admissibility conditions on the three forms `A i * x + 1` and prescribed parts `r i`. -/
def Adm (A r : Fin 3 → ℕ) : Prop :=
  (∀ i, 0 < A i ∧ 0 < r i ∧ (r i).Coprime (A i)) ∧ StrictMono A ∧
    (∀ i j, i ≠ j → (r i).Coprime (r j) ∧
      (r i).Coprime (if A i > A j then A i - A j else A j - A i))

/-- Sieve input (GGPY, unweighted, two of three forms). -/
def Sieve : Prop :=
  ∀ A r : Fin 3 → ℕ, Adm A r → ∀ T : ℕ, ∃ i j : Fin 3, i < j ∧
    {x : ℕ | ∀ l ∈ ({i, j} : Finset (Fin 3)), ∃ p s : ℕ,
      p.Prime ∧ s.Prime ∧ p ≠ s ∧ T < p ∧ T < s ∧ A l * x + 1 = r l * (p * s)}.Infinite

/-- Elementary coefficient input. -/
def Coeffs : Prop :=
  ∀ q : ℚ, 0 < q → ∃ A r : Fin 3 → ℕ, ∃ U V : Fin 3 → Fin 3 → ℕ, Adm A r ∧
    ∀ i j, i < j → 0 < U i j ∧ 0 < V i j ∧
      (∀ x : ℕ, U i j * (A i * x + 1) = V i j * (A j * x + 1) + 1) ∧
      (((U i j * r i).divisors.card : ℚ) / (V i j * r j).divisors.card) = q

lemma prime_coprime_of_lt {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (h : m < p) :
    m.Coprime p :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd hm hd)
    (not_le.2 h))

lemma card_mul_E2 {m p s : ℕ} (hm : 0 < m) (hp : p.Prime) (hs : s.Prime)
    (hps : p ≠ s) (hmp : m < p) (hms : m < s) :
    (m * (p * s)).divisors.card = 4 * m.divisors.card := by
  have h1 : m.Coprime (p * s) :=
    Nat.Coprime.mul_right (prime_coprime_of_lt hm hp hmp) (prime_coprime_of_lt hm hs hms)
  have h2 : p.Coprime s := (Nat.coprime_primes hp hs).2 hps
  rw [Nat.Coprime.card_divisors_mul h1, Nat.Coprime.card_divisors_mul h2,
    Nat.Prime.divisors hp, Nat.Prime.divisors hs]
  rw [Finset.card_pair hp.one_lt.ne, Finset.card_pair hs.one_lt.ne]
  ring

theorem of_sieve_coeffs (hS : Sieve) (hC : Coeffs) :
    type_of% @Erdos964.erdos_964.variants.eberhard := by
  classical
  intro q hq
  obtain ⟨A, r, U, V, hadm, hcoef⟩ := hC q hq
  let T : ℕ := ∑ i : Fin 3, ∑ j : Fin 3, (U i j * r i + V i j * r j)
  have hT : ∀ i j, U i j * r i ≤ T ∧ V i j * r j ≤ T := by
    intro i j
    have hi : (∑ j' : Fin 3, (U i j' * r i + V i j' * r j')) ≤ T :=
      Finset.single_le_sum (f := fun i => ∑ j : Fin 3, (U i j * r i + V i j * r j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hj : U i j * r i + V i j * r j ≤ ∑ j' : Fin 3, (U i j' * r i + V i j' * r j') :=
      Finset.single_le_sum (f := fun j => U i j * r i + V i j * r j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  obtain ⟨i, j, hij, hinf⟩ := hS A r hadm T
  obtain ⟨hU, hV, hrel, hq'⟩ := hcoef i j hij
  have hAj := (hadm.1 j).1
  have hri := (hadm.1 i).2.1
  have hrj := (hadm.1 j).2.1
  let f : ℕ → ℕ := fun x => V i j * (A j * x + 1)
  have hf : Function.Injective f := by
    intro x y h
    have := Nat.eq_of_mul_eq_mul_left hV h
    exact Nat.eq_of_mul_eq_mul_left hAj (by omega)
  refine (hinf.image hf.injOn).mono ?_
  rintro n ⟨x, hx, rfl⟩
  obtain ⟨p, s, hp, hs, hps, hTp, hTs, hi⟩ := hx i (by simp)
  obtain ⟨P, S, hP, hS', hPS, hTP, hTS, hj⟩ := hx j (by simp)
  have e1 : f x + 1 = U i j * r i * (p * s) := by
    simp only [f]; rw [← hrel, hi]; ring
  have e0 : f x = V i j * r j * (P * S) := by
    simp only [f]; rw [hj]; ring
  have hu0 : 0 < U i j * r i := Nat.mul_pos hU hri
  have hv0 : 0 < V i j * r j := Nat.mul_pos hV hrj
  refine ⟨Nat.mul_pos hV (Nat.succ_pos _), ?_⟩
  have hqR : (((U i j * r i).divisors.card : ℝ) / (V i j * r j).divisors.card) = (q : ℝ) := by
    rw [← hq']; push_cast; rfl
  have hc1 := card_mul_E2 hu0 hp hs hps (lt_of_le_of_lt (hT i j).1 hTp) (lt_of_le_of_lt (hT i j).1 hTs)
  have hc0 := card_mul_E2 hv0 hP hS' hPS (lt_of_le_of_lt (hT i j).2 hTP) (lt_of_le_of_lt (hT i j).2 hTS)
  rw [Erdos964.tauRatio, ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply,
    e1, e0, hc1, hc0, ← hqR]
  have hpos : (0 : ℝ) < ((V i j * r j).divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hv0.ne'⟩
  push_cast
  field_simp

end OMA964

namespace OMA964K

open Finset
open scoped ArithmeticFunction.sigma BigOperators

/-! ### Module 1: Elementary Mertens 1st and 2nd bounds -/

private lemma log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

private lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using this

private lemma real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

private lemma log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

private lemma log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith

private lemma summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
            rw [← hsq]; field_simp; ring

private noncomputable def primePowerConst : ℝ :=
  ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

private lemma sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

private lemma sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

private lemma sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp; ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

private noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

private lemma mertens1Const_pos : 0 < mertens1Const := by
  have h1 : 0 ≤ primePowerConst := by simpa using sum_log_div_mul_sub_one_le ∅
  have h2 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertens1Const; linarith

private lemma abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 : 0 ≤ primePowerConst := by simpa using sum_log_div_mul_sub_one_le ∅
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

private lemma sum_log_div_Ioc_le (R p m : ℕ) (hp : 2 ≤ p) (hm : 1 ≤ m) :
    ∑ q ∈ (Nat.primesLE (R / m)).filter (fun q => R < p * m * q), Real.log q / q ≤
      Real.log p + (2 * mertens1Const + Real.log 2) := by
  set B := R / m
  set A := R / (p * m)
  have hfilt : (Nat.primesLE B).filter (fun q => R < p * m * q) =
      Nat.primesLE B \ Nat.primesLE A := by
    ext q
    simp only [mem_filter, mem_sdiff, Nat.mem_primesLE, A, B]
    have hpm : 0 < p * m := by positivity
    constructor
    · rintro ⟨⟨hqB, hqp⟩, hgt⟩
      refine ⟨⟨hqB, hqp⟩, fun ⟨hqA, _⟩ => ?_⟩
      have : p * m * q ≤ R := by
        calc p * m * q ≤ p * m * (R / (p * m)) := Nat.mul_le_mul_left _ hqA
          _ ≤ R := Nat.mul_div_le R (p * m)
      omega
    · rintro ⟨⟨hqB, hqp⟩, hnot⟩
      refine ⟨⟨hqB, hqp⟩, ?_⟩
      by_contra hle
      push_neg at hle
      exact hnot ⟨(Nat.le_div_iff_mul_le hpm).mpr (by linarith), hqp⟩
  rw [hfilt]
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · simp [hB0]
    have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith [mertens1Const_pos]
  rcases Nat.eq_zero_or_pos A with hA0 | hApos
  · have hBp : B ≤ p := by
      have hRlt : R < p * m := (Nat.div_eq_zero_iff_lt (by positivity)).mp hA0
      exact (Nat.div_lt_iff_lt_mul hm).mpr hRlt |>.le
    rw [hA0, Nat.primesLE_zero, sdiff_empty]
    have h1 := (abs_le.mp (abs_sum_log_div_sub_log_le_nat B)).2
    have h2 : Real.log B ≤ Real.log p := Real.log_le_log (by exact_mod_cast hBpos) (by exact_mod_cast hBp)
    have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith [mertens1Const_pos]
  · have hAB : A ≤ B := Nat.div_le_div_left (Nat.le_mul_of_pos_left m (by omega)) hm
    have hsub : Nat.primesLE A ⊆ Nat.primesLE B := by
      intro q hq
      rw [Nat.mem_primesLE] at hq ⊢
      exact ⟨hq.1.trans hAB, hq.2⟩
    rw [Finset.sum_sdiff_eq_sub hsub]
    have h1 := (abs_le.mp (abs_sum_log_div_sub_log_le_nat B)).2
    have h2 := (abs_le.mp (abs_sum_log_div_sub_log_le_nat A)).1
    have hBA : (B : ℝ) / A ≤ 2 * p := by
      have hA_ge : R < p * m * (A + 1) := by
        have hlt : R < A * (p * m) + p * m := Nat.lt_div_mul_add (a := R) (b := p * m) (by positivity)
        have hmul : p * m * (A + 1) = A * (p * m) + p * m := by ring
        linarith
      have hA2 : R < 2 * p * m * A := by
        have : A + 1 ≤ 2 * A := by omega
        nlinarith
      have hBm : B * m ≤ R := Nat.div_mul_le_self R m
      have hB_le : B ≤ 2 * p * A := by
        have : B * m < 2 * p * A * m := by nlinarith
        exact (Nat.lt_of_mul_lt_mul_right this).le
      have hAr : (0 : ℝ) < A := by exact_mod_cast hApos
      rw [div_le_iff₀ hAr]
      exact_mod_cast hB_le
    have hlog : Real.log B - Real.log A ≤ Real.log p + Real.log 2 := by
      rw [← Real.log_div (by exact_mod_cast hBpos.ne') (by exact_mod_cast hApos.ne')]
      calc Real.log ((B : ℝ) / A) ≤ Real.log (2 * p) :=
            Real.log_le_log (by positivity) hBA
        _ = Real.log 2 + Real.log p := Real.log_mul (by norm_num) (by positivity)
        _ = Real.log p + Real.log 2 := by ring
    linarith

private lemma abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

private noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

private lemma mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N
  set b := Real.log ((N + 1 : ℕ) : ℝ)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast; rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]; linarith
    linarith
  have sum_succ (f : ℕ → ℝ) :
      ∑ p ∈ Nat.primesLE (N + 1), f p =
        (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
    rw [Nat.primesLE_succ]
    split_ifs with h
    · rw [Finset.sum_insert, add_comm]
      intro hm; have := (Nat.mem_primesLE.mp hm).1; omega
    · simp
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := by
    change (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) / b
    rw [sum_succ, sum_succ]
    split_ifs with h
    · have hl : 0 < b := hb
      field_simp; ring
    · simp
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG, F0, F1, S0, S1, a, b]; ring
    rw [e, hstep]; field_simp; ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]; gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring

private lemma mertensG_diff_le (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const + 1) * (1 / Real.log m - 1 / Real.log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n + 1) - mertensG m| =
        |(mertensG (n + 1) - mertensG n) + (mertensG n - mertensG m)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = _ := by ring

private noncomputable def mertens2Const : ℝ := 3 * mertens1Const + 1

private lemma mertens2_Ioc_le (M N : ℕ) (hM : 2 ≤ M) (hMN : M ≤ N) :
    ∑ p ∈ (Nat.primesLE N).filter (M < ·), (1 : ℝ) / p ≤
      Real.log (Real.log N / Real.log M) + mertens2Const / Real.log M := by
  have hfilt : (Nat.primesLE N).filter (M < ·) = Nat.primesLE N \ Nat.primesLE M := by
    ext p
    simp only [mem_filter, mem_sdiff, Nat.mem_primesLE]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun h3 => by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by by_contra hc; exact h2 ⟨by omega, h1.2⟩⟩⟩
  have hsub : Nat.primesLE M ⊆ Nat.primesLE N := by
    intro p hp; rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hMN, hp.2⟩
  rw [hfilt, Finset.sum_sdiff_eq_sub hsub]
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hle : Real.log M ≤ Real.log N := Real.log_le_log (by positivity) (by exact_mod_cast hMN)
  have hG := (abs_le.mp (mertensG_diff_le M N hM hMN)).2
  have hRN := (abs_le.mp (abs_sum_log_div_sub_log_le_nat N)).2
  have hRM := (abs_le.mp (abs_sum_log_div_sub_log_le_nat M)).1
  have h1 : ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N ≤
      mertens1Const / Real.log M :=
    (div_le_div_of_nonneg_right hRN hlogN.le).trans
      (div_le_div_of_nonneg_left mertens1Const_pos.le hlogM hle)
  have h2 : -(((∑ p ∈ Nat.primesLE M, Real.log p / p) - Real.log M) / Real.log M) ≤
      mertens1Const / Real.log M := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hlogM.le
  have h3 : (mertens1Const + 1) * (1 / Real.log M - 1 / Real.log N) ≤
      (mertens1Const + 1) / Real.log M := by
    have hnn : 0 ≤ 1 / Real.log N := by positivity
    have heq : (mertens1Const + 1) / Real.log M = (mertens1Const + 1) * (1 / Real.log M) := by ring
    rw [heq]; nlinarith [mertens1Const_pos]
  have hlogdiv : Real.log (Real.log N) - Real.log (Real.log M) =
      Real.log (Real.log N / Real.log M) := (Real.log_div hlogN.ne' hlogM.ne').symm
  unfold mertensG at hG
  unfold mertens2Const
  have hadd : (mertens1Const + 1) / Real.log M + mertens1Const / Real.log M +
      mertens1Const / Real.log M = (3 * mertens1Const + 1) / Real.log M := by ring
  linarith

private noncomputable def mertens2BaseConst : ℝ :=
  (∑ p ∈ Nat.primesLE 2, (1 : ℝ) / p) - Real.log (Real.log 2) + mertens2Const / Real.log 2

private lemma mertens2_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p ≤ Real.log (Real.log N) + mertens2BaseConst := by
  have hsub : Nat.primesLE 2 ⊆ Nat.primesLE N := by
    intro p hp; rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hN, hp.2⟩
  have hsplit : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      (∑ p ∈ Nat.primesLE 2, (1 : ℝ) / p) + ∑ p ∈ (Nat.primesLE N).filter (2 < ·), (1 : ℝ) / p := by
    have hfilt : (Nat.primesLE N).filter (2 < ·) = Nat.primesLE N \ Nat.primesLE 2 := by
      ext p
      simp only [mem_filter, mem_sdiff, Nat.mem_primesLE]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun h3 => by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by by_contra hc; exact h2 ⟨by omega, h1.2⟩⟩⟩
    rw [hfilt, Finset.sum_sdiff_eq_sub hsub]; ring
  rw [hsplit]
  have h2 := mertens2_Ioc_le 2 N le_rfl hN
  norm_cast at h2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  rw [Real.log_div hlogN.ne' hlog2.ne'] at h2
  unfold mertens2BaseConst
  linarith

/-! ### Module 2: Elementary K-tuple algebraic construction -/

def AdmK (K : ℕ) (A r : Fin K → ℕ) : Prop :=
  (∀ i, 0 < A i ∧ 0 < r i ∧ (r i).Coprime (A i)) ∧ StrictMono A ∧
    (∀ i j, i ≠ j → (r i).Coprime (r j) ∧
      (r i).Coprime (if A i > A j then A i - A j else A j - A i))

private lemma exists_div_chain (n : ℕ) :
    ∃ A : Fin n → ℕ, (∀ i, 0 < A i) ∧ StrictMono A ∧ ∀ i j, i < j → (A j - A i) ∣ A i := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    rcases n with _ | n
    · refine ⟨![1], fun i => by fin_cases i; norm_num, ?_, ?_⟩
      · intro i j hij; fin_cases i; fin_cases j; simp at hij
      · intro i j hij; fin_cases i; fin_cases j; simp at hij
    · obtain ⟨A, hpos, hmono, hdvd⟩ := ih
      let L : ℕ := ∏ i : Fin (n + 1), A i
      have hL : 0 < L := Finset.prod_pos fun i _ => hpos i
      let B : Fin (n + 2) → ℕ := Fin.cons L (fun i => L + A i)
      refine ⟨B, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero => simpa [B] using hL
        | succ k => dsimp [B]; exact Nat.add_pos_left hL _
      · intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => simp at hij
          | succ l => dsimp [B]; simp only [Fin.cons_zero, Fin.cons_succ]; have := hpos l; omega
        | succ k =>
          induction j using Fin.cases with
          | zero => simp at hij
          | succ l =>
            dsimp [B]; simp only [Fin.cons_succ]
            have hkl : k < l := Fin.succ_lt_succ_iff.mp hij
            have := hmono hkl
            omega
      · intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => simp at hij
          | succ l =>
            dsimp [B]; simp only [Fin.cons_zero, Fin.cons_succ, Nat.add_sub_cancel_left]
            exact Finset.dvd_prod_of_mem A (Finset.mem_univ l)
        | succ k =>
          induction j using Fin.cases with
          | zero => simp at hij
          | succ l =>
            dsimp [B]; simp only [Fin.cons_succ, Nat.add_sub_add_left]
            have hkl : k < l := Fin.succ_lt_succ_iff.mp hij
            have h1 : A l - A k ∣ A k := hdvd k l hkl
            have h2 : A k ∣ L := Finset.dvd_prod_of_mem A (Finset.mem_univ k)
            exact dvd_add (h1.trans h2) h1

private def lamVal (e : ℕ × ℕ × Bool) : ℚ :=
  if e.2.2 then ((e.1 : ℚ) * e.2.1) / ((e.1 : ℚ) + e.2.1 - 1)
  else ((e.1 : ℚ) + e.2.1 - 1) / ((e.1 : ℚ) * e.2.1)

private lemma exists_lambda_nat (m : ℕ) (hm : 1 ≤ m) :
    ∃ l : List (ℕ × ℕ × Bool), (∀ e ∈ l, 2 ≤ e.1 ∧ 2 ≤ e.2.1) ∧ (l.map lamVal).prod = (m : ℚ) := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨[], by simp, by simp⟩
  | succ m hm ih =>
    rcases eq_or_lt_of_le hm with rfl | hm2
    · refine ⟨[(2, 2, true), (2, 3, true)], ?_, ?_⟩
      · intro e he; simp at he; rcases he with rfl | rfl <;> norm_num
      · simp [lamVal]; norm_num
    · obtain ⟨l, hl, hprod⟩ := ih
      refine ⟨(2, 2, true) :: (2, 3, true) :: (2, m, false) :: l, ?_, ?_⟩
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | rfl | rfl | he
        · norm_num
        · norm_num
        · exact ⟨by norm_num, hm2⟩
        · exact hl e he
      · simp only [List.map_cons, List.prod_cons, hprod, lamVal, ite_true, ite_false]
        have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
        push_cast
        field_simp
        ring

private lemma exists_lambda_rat (x : ℚ) (hx : 0 < x) :
    ∃ l : List (ℕ × ℕ × Bool), (∀ e ∈ l, 2 ≤ e.1 ∧ 2 ≤ e.2.1) ∧ (l.map lamVal).prod = x := by
  have hnum : 1 ≤ x.num.toNat := by
    have := Rat.num_pos.mpr hx
    omega
  have hden : 1 ≤ x.den := x.pos
  obtain ⟨l₁, hl₁, hp₁⟩ := exists_lambda_nat x.num.toNat hnum
  obtain ⟨l₂, hl₂, hp₂⟩ := exists_lambda_nat x.den hden
  let flip : ℕ × ℕ × Bool → ℕ × ℕ × Bool := fun e => (e.1, e.2.1, !e.2.2)
  refine ⟨l₁ ++ l₂.map flip, ?_, ?_⟩
  · intro e he
    rw [List.mem_append] at he
    rcases he with h | h
    · exact hl₁ e h
    · obtain ⟨e', he', rfl⟩ := List.mem_map.mp h
      exact hl₂ e' he'
  · rw [List.map_append, List.prod_append, hp₁, List.map_map]
    have hinv : ∀ l : List (ℕ × ℕ × Bool),
        (l.map (lamVal ∘ flip)).prod = ((l.map lamVal).prod)⁻¹ := by
      intro l
      induction l with
      | nil => simp
      | cons a t iht =>
        simp only [List.map_cons, List.prod_cons, iht, mul_inv_rev]
        have hfl : (lamVal ∘ flip) a = (lamVal a)⁻¹ := by
          rcases a with ⟨a1, a2, b⟩
          cases b <;> simp [lamVal, flip, inv_div]
        rw [hfl, mul_comm]
    rw [hinv l₂, hp₂, ← div_eq_mul_inv]
    have hn : (x.num.toNat : ℚ) = (x.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr hx).le
    rw [hn]
    exact x.num_div_den

private lemma fresh_primes (m B : ℕ) :
    ∃ P : Fin m → ℕ, (∀ k, (P k).Prime ∧ B < P k) ∧ StrictMono P := by
  induction m with
  | zero => exact ⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0⟩
  | succ m ih =>
    obtain ⟨P, hP, hmono⟩ := ih
    let M := B + ∑ k : Fin m, P k
    obtain ⟨q, hqM, hqp⟩ := Nat.exists_infinite_primes (M + 1)
    let P' : Fin (m + 1) → ℕ := Fin.snoc P q
    refine ⟨P', ?_, ?_⟩
    · intro k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp only [P', Fin.snoc_last]
        exact ⟨hqp, by omega⟩
      · simp only [P', Fin.snoc_castSucc]
        exact hP j
    · intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt_of_ge (Fin.le_last j))
      | cast i' =>
        induction j using Fin.lastCases with
        | last =>
          simp only [P', Fin.snoc_castSucc, Fin.snoc_last]
          have hle : P i' ≤ ∑ k : Fin m, P k :=
            Finset.single_le_sum (f := P) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i')
          omega
        | cast j' =>
          simp only [P', Fin.snoc_castSucc]
          exact hmono (Fin.castSucc_lt_castSucc_iff.mp hij)

private lemma linear_residue_K (a m t u : ℕ) (hm : 0 < m) (ha : a.Coprime m) :
    ∃ x : ℕ, a * x + t ≡ u [MOD m] := by
  letI : NeZero m := ⟨hm.ne'⟩
  let w : ZMod m := (a : ZMod m)⁻¹ * ((u : ZMod m) - t)
  refine ⟨w.val, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  dsimp [w]
  rw [← mul_assoc, ZMod.coe_mul_inv_eq_one a ha, one_mul]
  ring

private lemma card_divisors_eq_prod_of_subset {m : ℕ} (hm : m ≠ 0) {S : Finset ℕ}
    (hS : m.primeFactors ⊆ S) :
    m.divisors.card = ∏ p ∈ S, (m.factorization p + 1) := by
  rw [Nat.card_divisors hm]
  apply Finset.prod_subset hS
  intro p _ hp
  rw [← Nat.support_factorization] at hp
  rw [Finsupp.notMem_support_iff.mp hp]
  rfl

private lemma local_factor_eq {α : Type*} [LinearOrder α] [DecidableEq α]
    (l m' i0 j0 : α) (hlm : l < m') (hij : i0 < j0)
    (a0 b0 : ℕ) (ha2 : 2 ≤ a0) (hb2 : 2 ≤ b0) (sgn : Bool) :
    let bIdx := if sgn then i0 else j0
    let rIdx := if sgn then j0 else i0
    let cob := fun s : α =>
      if sgn then (if s = i0 then (a0 : ℚ)⁻¹ else if s = j0 then (b0 : ℚ) else 1)
      else (if s = i0 then (b0 : ℚ) else if s = j0 then (a0 : ℚ)⁻¹ else 1)
    let lam : ℚ := if sgn then ((a0 : ℚ) * b0) / ((a0 : ℚ) + b0 - 1)
      else ((a0 : ℚ) + b0 - 1) / ((a0 : ℚ) * b0)
    (((if m' = bIdx then a0 - 1 else 0) + (if rIdx = l then b0 - 1 else 0) + 1 : ℕ) : ℚ) /
      (((if l = bIdx then a0 - 1 else 0) + (if rIdx = m' then b0 - 1 else 0) + 1 : ℕ) : ℚ) =
      (cob l / cob m') * (if i0 = l ∧ j0 = m' then lam else 1) := by
  dsimp only
  have ha1 : ((a0 - 1 + 1 : ℕ) : ℚ) = (a0 : ℚ) := by exact_mod_cast (show a0 - 1 + 1 = a0 by omega)
  have hb1 : ((b0 - 1 + 1 : ℕ) : ℚ) = (b0 : ℚ) := by exact_mod_cast (show b0 - 1 + 1 = b0 by omega)
  have hab1 : ((a0 - 1 + (b0 - 1) + 1 : ℕ) : ℚ) = (a0 : ℚ) + (b0 : ℚ) - 1 := by
    have : a0 - 1 + (b0 - 1) + 1 + 1 = a0 + b0 := by omega
    have hq1 : ((a0 - 1 + (b0 - 1) + 1 : ℕ) : ℚ) + 1 = (a0 : ℚ) + (b0 : ℚ) := by exact_mod_cast this
    linarith
  have hapos : (a0 : ℚ) ≠ 0 := by exact_mod_cast (show a0 ≠ 0 by omega)
  have hbpos : (b0 : ℚ) ≠ 0 := by exact_mod_cast (show b0 ≠ 0 by omega)
  have habpos : (a0 : ℚ) + (b0 : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ a0 := by exact_mod_cast ha2
    have : (2 : ℚ) ≤ b0 := by exact_mod_cast hb2
    linarith
  have hne_ij : i0 ≠ j0 := hij.ne
  have hne_lm : l ≠ m' := hlm.ne
  cases sgn
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : l = i0
    · subst h1
      have h2 : l ≠ j0 := hne_ij
      have h3 : m' ≠ l := hne_lm.symm
      by_cases h4 : m' = j0
      · subst h4
        simp only [↓reduceIte, h2, h3, and_self, add_zero, zero_add, Nat.cast_one, hab1]
        field_simp [hapos, hbpos, habpos]
      · simp only [↓reduceIte, h2, h3, h4, Ne.symm h4, and_false, add_zero, zero_add, Nat.cast_one, hb1]
        field_simp [hapos, hbpos]
    · by_cases h2 : l = j0
      · subst h2
        have h3 : m' ≠ i0 := fun h => by subst h; exact lt_asymm hlm hij
        have h4 : m' ≠ l := hne_lm.symm
        simp only [↓reduceIte, h1, h3, h4, Ne.symm h1, false_and, add_zero, zero_add, Nat.cast_one, ha1]
        field_simp [hapos, hbpos]
      · by_cases h3 : m' = i0
        · subst h3
          have h4 : m' ≠ j0 := hne_ij
          simp only [↓reduceIte, h1, h2, h4, Ne.symm h1, false_and, add_zero, zero_add, Nat.cast_one, hb1]
          field_simp [hapos, hbpos]
        · by_cases h4 : m' = j0
          · subst h4
            simp only [↓reduceIte, h1, h2, h3, Ne.symm h1, false_and, add_zero, zero_add, Nat.cast_one, ha1]
            field_simp [hapos, hbpos]
          · simp only [↓reduceIte, h1, h2, h3, h4, Ne.symm h1, false_and, add_zero, zero_add, Nat.cast_one]
            norm_num
  · simp only [↓reduceIte]
    by_cases h1 : l = i0
    · subst h1
      have h2 : l ≠ j0 := hne_ij
      have h3 : m' ≠ l := hne_lm.symm
      by_cases h4 : m' = j0
      · subst h4
        simp only [↓reduceIte, h2, h3, Ne.symm h2, and_self, add_zero, zero_add, Nat.cast_one, hab1]
        field_simp [hapos, hbpos, habpos]
      · simp only [↓reduceIte, h2, h3, h4, Ne.symm h2, Ne.symm h4, and_false, add_zero, zero_add, Nat.cast_one, ha1]
        field_simp [hapos, hbpos]
    · by_cases h2 : l = j0
      · subst h2
        have h3 : m' ≠ i0 := fun h => by subst h; exact lt_asymm hlm hij
        have h4 : m' ≠ l := hne_lm.symm
        simp only [↓reduceIte, h1, h3, h4, Ne.symm h1, false_and, add_zero, zero_add, Nat.cast_one, hb1]
        field_simp [hapos, hbpos]
      · by_cases h3 : m' = i0
        · subst h3
          have h4 : m' ≠ j0 := hne_ij
          simp only [↓reduceIte, h1, h2, h4, Ne.symm h1, Ne.symm h2, false_and, add_zero, zero_add, Nat.cast_one, ha1]
          field_simp [hapos, hbpos]
        · by_cases h4 : m' = j0
          · subst h4
            simp only [↓reduceIte, h1, h2, h3, Ne.symm h1, Ne.symm h2, false_and, add_zero, zero_add, Nat.cast_one, hb1]
            field_simp [hapos, hbpos]
          · simp only [↓reduceIte, h1, h2, h3, h4, Ne.symm h1, Ne.symm h2, false_and, add_zero, zero_add, Nat.cast_one]
            norm_num

private lemma factorization_eq_of_modEq {N p e : ℕ} (hN : N ≠ 0) (hp : p.Prime)
    (hmod : N ≡ p ^ e [MOD p ^ (e + 1)]) : N.factorization p = e := by
  have hdvd : p ^ e ∣ N := by
    exact (hmod.dvd_iff (pow_dvd_pow p (Nat.le_succ e))).mpr dvd_rfl
  have hndvd : ¬ p ^ (e + 1) ∣ N := by
    intro h
    have h1 : p ^ (e + 1) ∣ p ^ e := (hmod.dvd_iff dvd_rfl).mp h
    have h2 : p ^ (e + 1) ≤ p ^ e := Nat.le_of_dvd (pow_pos hp.pos e) h1
    have h3 : p ^ e < p ^ (e + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self e)
    omega
  have hle : e ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization hN).mp hdvd
  have hlt : ¬ e + 1 ≤ N.factorization p := fun h =>
    hndvd ((hp.pow_dvd_iff_le_factorization hN).mpr h)
  omega

theorem coeffs_succ (n : ℕ) (hn : 1 ≤ n) (q : ℚ) (hq : 0 < q) :
    ∃ B r : Fin (n + 1) → ℕ, ∃ U V : Fin (n + 1) → Fin (n + 1) → ℕ,
      AdmK (n + 1) B r ∧
      ∀ i j, i < j → 0 < U i j ∧ 0 < V i j ∧
        (∀ x : ℕ, U i j * (B i * x + 1) = V i j * (B j * x + 1) + 1) ∧
        (((U i j * r i).divisors.card : ℚ) / (V i j * r j).divisors.card) = q := by
  classical
  obtain ⟨A, hApos, hAmono, hAdvd⟩ := exists_div_chain n
  let L : ℕ := ∏ i : Fin n, A i
  have hLpos : 0 < L := Finset.prod_pos fun i _ => hApos i
  have hAdvdL : ∀ k : Fin n, A k ∣ L := fun k => Finset.dvd_prod_of_mem A (Finset.mem_univ k)
  let c : Fin (n + 1) → ℕ := Fin.cons 0 A
  have hc_le : ∀ i : Fin (n + 1), c i ≤ L := by
    intro i
    refine Fin.cases (Nat.zero_le L) (fun k => Nat.le_of_dvd hLpos (hAdvdL k)) i
  have hc_mono : StrictMono c := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ l => simpa [c] using hApos l
    | succ k =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ l => simpa [c] using hAmono (Fin.succ_lt_succ_iff.mp hij)
  let d : Fin (n + 1) → Fin (n + 1) → ℕ := fun i j => c j - c i
  have hd_pos : ∀ i j, i < j → 0 < d i j := fun i j hij => Nat.sub_pos_of_lt (hc_mono hij)
  have hd_dvd_L : ∀ i j, i < j → d i j ∣ L := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ l => simpa [d, c] using hAdvdL l
    | succ k =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ l =>
        simpa [d, c] using (hAdvd k l (Fin.succ_lt_succ_iff.mp hij)).trans (hAdvdL k)
  have hd_dvd_c : ∀ i j, i < j → d i j ∣ c i := by
    intro i j hij
    induction i using Fin.cases with
    | zero => simp [c]
    | succ k =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ l => simpa [d, c] using hAdvd k l (Fin.succ_lt_succ_iff.mp hij)
  let vfix : ℕ → Fin (n + 1) → ℕ := fun p =>
    Fin.cons (2 * L.factorization p) (fun k => (A k).factorization p)
  let gamma : Fin (n + 1) → Fin (n + 1) → ℚ := fun i j =>
    ∏ p ∈ L.primeFactors,
      (((vfix p j - (d i j).factorization p + 1 : ℕ) : ℚ) /
        ((vfix p i - (d i j).factorization p + 1 : ℕ) : ℚ))
  have hgamma_pos : ∀ i j, 0 < gamma i j := by
    intro i j
    apply Finset.prod_pos
    intro p _
    positivity
  -- Build list of specs across all pairs i < j
  let pairs : List (Fin (n + 1) × Fin (n + 1)) :=
    (Finset.univ.filter (fun ij : Fin (n + 1) × Fin (n + 1) => ij.1 < ij.2)).toList
  have hpairs_nodup : pairs.Nodup := Finset.nodup_toList _
  have hmem_pairs : ∀ i j : Fin (n + 1), (i, j) ∈ pairs ↔ i < j := by
    intro i j; simp [pairs]
  choose lamList hlamList_ge hlamList_prod using
    fun ij : Fin (n + 1) × Fin (n + 1) => exists_lambda_rat (q / gamma ij.1 ij.2)
      (div_pos hq (hgamma_pos ij.1 ij.2))
  let specs : List (Fin (n + 1) × Fin (n + 1) × (ℕ × ℕ × Bool)) :=
    pairs.flatMap fun ij => (lamList ij).map fun e => (ij.1, ij.2, e)
  let m := specs.length
  obtain ⟨P, hP, hPmono⟩ := fresh_primes m L
  let specAt : Fin m → Fin (n + 1) × Fin (n + 1) × (ℕ × ℕ × Bool) := fun k => specs[k.val]
  have hspec_mem : ∀ k : Fin m, specAt k ∈ specs := fun k => List.getElem_mem k.isLt
  have hspec_lt : ∀ k : Fin m, (specAt k).1 < (specAt k).2.1 := by
    intro k
    have hm := hspec_mem k
    simp only [specs, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨⟨i, j⟩, hij, e, _, heq⟩ := hm
    have := (hmem_pairs i j).mp hij
    have h1 : (specAt k).1 = i := congrArg Prod.fst heq.symm
    have h2 : (specAt k).2.1 = j := congrArg (fun x => x.2.1) heq.symm
    omega
  have hspec_ge : ∀ k : Fin m, 2 ≤ (specAt k).2.2.1 ∧ 2 ≤ (specAt k).2.2.2.1 := by
    intro k
    have hm := hspec_mem k
    simp only [specs, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨ij, _, e, he, heq⟩ := hm
    have h1 : (specAt k).2.2 = e := congrArg (fun x => x.2.2) heq.symm
    rw [h1]
    exact hlamList_ge ij e he
  let bIdx : Fin m → Fin (n + 1) := fun k => if (specAt k).2.2.2.2 then (specAt k).1 else (specAt k).2.1
  let rIdx : Fin m → Fin (n + 1) := fun k => if (specAt k).2.2.2.2 then (specAt k).2.1 else (specAt k).1
  let αk : Fin m → ℕ := fun k => (specAt k).2.2.1
  let βk : Fin m → ℕ := fun k => (specAt k).2.2.2.1
  have hbr_ne : ∀ k : Fin m, bIdx k ≠ rIdx k := by
    intro k
    have hlt := hspec_lt k
    dsimp [bIdx, rIdx]
    split_ifs <;> [exact hlt.ne; exact hlt.ne']
  -- Solve CRT for M
  have hcopLP : ∀ k : Fin m, L.Coprime (P k ^ αk k) := by
    intro k
    exact (OMA964.prime_coprime_of_lt hLpos (hP k).1 (hP k).2).pow_right _
  choose solK hsolK using fun k : Fin m =>
    linear_residue_K L (P k ^ αk k) (c (bIdx k)) (P k ^ (αk k - 1))
      (pow_pos (hP k).1.pos _) (hcopLP k)
  let modFn : Option (Fin m) → ℕ := fun o =>
    match o with
    | none => L ^ 2
    | some k => P k ^ αk k
  let resFn : Option (Fin m) → ℕ := fun o =>
    match o with
    | none => L
    | some k => solK k
  have hmod_ne : ∀ o ∈ (Finset.univ : Finset (Option (Fin m))), modFn o ≠ 0 := by
    intro o _
    cases o with
    | none => exact pow_ne_zero 2 hLpos.ne'
    | some k => exact pow_ne_zero _ (hP k).1.ne_zero
  have hmod_cop : ∀ o₁ ∈ (Finset.univ : Finset (Option (Fin m))),
      ∀ o₂ ∈ (Finset.univ : Finset (Option (Fin m))), o₁ ≠ o₂ → (modFn o₁).Coprime (modFn o₂) := by
    intro o₁ _ o₂ _ hne
    cases o₁ with
    | none =>
      cases o₂ with
      | none => exact (hne rfl).elim
      | some k => exact (hcopLP k).pow_left 2
    | some k₁ =>
      cases o₂ with
      | none => exact ((hcopLP k₁).pow_left 2).symm
      | some k₂ =>
        have hk : k₁ ≠ k₂ := fun h => hne (congrArg some h)
        exact (((Nat.coprime_primes (hP k₁).1 (hP k₂).1).mpr (hPmono.injective.ne hk)).pow_left _).pow_right _
  let cr := Nat.chineseRemainderOfFinset resFn modFn Finset.univ hmod_ne hmod_cop
  let Pmod := ∏ o : Option (Fin m), modFn o
  have hPmod_pos : 0 < Pmod := Finset.prod_pos fun o _ => Nat.pos_of_ne_zero (hmod_ne o (Finset.mem_univ o))
  let M : ℕ := cr.val + Pmod
  have hM_mod : ∀ o : Option (Fin m), M ≡ resFn o [MOD modFn o] := by
    intro o
    have hd : modFn o ∣ Pmod := Finset.dvd_prod_of_mem modFn (Finset.mem_univ o)
    have h0 : Pmod ≡ 0 [MOD modFn o] := Nat.modEq_zero_iff_dvd.mpr hd
    simpa [M] using (cr.prop o (Finset.mem_univ o)).add h0
  have hM_ge_L : L ≤ M := by
    have hL2_dvd : L ^ 2 ∣ Pmod := Finset.dvd_prod_of_mem modFn (Finset.mem_univ none)
    have hL2_le : L ^ 2 ≤ Pmod := Nat.le_of_dvd hPmod_pos hL2_dvd
    have : L ≤ L ^ 2 := Nat.le_self_pow (by decide) L
    omega
  have hM_pos : 0 < M := lt_of_lt_of_le hLpos hM_ge_L
  let B : Fin (n + 1) → ℕ := fun i => M * L + c i
  have hBpos : ∀ i, 0 < B i := fun i => Nat.add_pos_left (Nat.mul_pos hM_pos hLpos) _
  have hBmono : StrictMono B := fun i j hij => Nat.add_lt_add_left (hc_mono hij) _
  have hBdiff : ∀ i j, i < j → B j - B i = d i j := by
    intro i j _; dsimp [B, d]; omega
  have hd_dvd_B : ∀ i j, i < j → d i j ∣ B i := fun i j hij =>
    dvd_add (dvd_mul_of_dvd_right (hd_dvd_L i j hij) M) (hd_dvd_c i j hij)
  have hd_dvd_Bj : ∀ i j, i < j → d i j ∣ B j := by
    intro i j hij
    have : B j = B i + d i j := by have := hBdiff i j hij; have := hBmono hij; omega
    rw [this]; exact dvd_add (hd_dvd_B i j hij) dvd_rfl
  let U : Fin (n + 1) → Fin (n + 1) → ℕ := fun i j => B j / d i j
  let V : Fin (n + 1) → Fin (n + 1) → ℕ := fun i j => B i / d i j
  have hU_mul : ∀ i j, i < j → d i j * U i j = B j := fun i j hij =>
    Nat.mul_div_cancel' (hd_dvd_Bj i j hij)
  have hV_mul : ∀ i j, i < j → d i j * V i j = B i := fun i j hij =>
    Nat.mul_div_cancel' (hd_dvd_B i j hij)
  have hU_pos : ∀ i j, i < j → 0 < U i j := by
    intro i j hij
    have hm := hU_mul i j hij
    have hp := hBpos j
    by_contra! h; have h0 : U i j = 0 := by omega
    rw [h0, mul_zero] at hm; omega
  have hV_pos : ∀ i j, i < j → 0 < V i j := by
    intro i j hij
    have hm := hV_mul i j hij
    have hp := hBpos i
    by_contra! h; have h0 : V i j = 0 := by omega
    rw [h0, mul_zero] at hm; omega
  have hUV_rel : ∀ i j, i < j → ∀ x : ℕ, U i j * (B i * x + 1) = V i j * (B j * x + 1) + 1 := by
    intro i j hij x
    have h1 := hU_mul i j hij
    have h2 := hV_mul i j hij
    have h3 : B j = B i + d i j := by have := hBdiff i j hij; have := hBmono hij; omega
    have h4 : d i j * (U i j * (B i * x + 1)) = d i j * (V i j * (B j * x + 1) + 1) := by
      have : d i j * (U i j * (B i * x + 1)) = (d i j * U i j) * (B i * x + 1) := by ring
      rw [this, h1]
      have : d i j * (V i j * (B j * x + 1) + 1) = (d i j * V i j) * (B j * x + 1) + d i j := by ring
      rw [this, h2, h3]; ring
    exact Nat.eq_of_mul_eq_mul_left (hd_pos i j hij) h4
  -- Valuations of B at primes dividing L
  have hML_dvd : L ∣ M := by
    have hML2 : L ^ 2 ∣ M - L := by
      have hm := hM_mod none
      dsimp [modFn, resFn] at hm
      exact (Nat.modEq_iff_dvd' hM_ge_L).mp hm.symm
    have : L ∣ M - L := (dvd_pow_self L (by decide : 2 ≠ 0)).trans hML2
    have hEq : M = (M - L) + L := (Nat.sub_add_cancel hM_ge_L).symm
    rw [hEq]; exact dvd_add this dvd_rfl
  have hB_fact_L : ∀ p ∈ L.primeFactors, ∀ i : Fin (n + 1), (B i).factorization p = vfix p i := by
    intro p hp i
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpL : p ∣ L := (Nat.mem_primeFactors.mp hp).2.1
    induction i using Fin.cases with
    | zero =>
      dsimp only [B, c, vfix]
      simp only [Fin.cons_zero, add_zero]
      rw [Nat.factorization_mul hM_pos.ne' hLpos.ne', Finsupp.add_apply]
      have hM_fact : M.factorization p = L.factorization p := by
        have hML2 : L ^ 2 ∣ M - L := by
          have hm := hM_mod none
          dsimp [modFn, resFn] at hm
          exact (Nat.modEq_iff_dvd' hM_ge_L).mp hm.symm
        obtain ⟨t, ht⟩ := hML2
        have hMeq : M = L * (1 + L * t) := by
          have : M = L + (M - L) := by omega
          rw [this, ht]; ring
        rw [hMeq, Nat.factorization_mul hLpos.ne' (by positivity), Finsupp.add_apply]
        have hnd : ¬ p ∣ 1 + L * t := fun hd =>
          hpp.not_dvd_one ((Nat.dvd_add_left (dvd_mul_of_dvd_left hpL t)).mp hd)
        rw [Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
      omega
    | succ k =>
      dsimp only [B, c, vfix]
      simp only [Fin.cons_succ]
      obtain ⟨qk, hqk⟩ := hAdvdL k
      have hBeq : M * L + A k = A k * (M * qk + 1) := by rw [hqk]; ring
      rw [hBeq, Nat.factorization_mul (hApos k).ne' (by positivity), Finsupp.add_apply]
      have hnd : ¬ p ∣ M * qk + 1 := fun hd =>
        hpp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left (hpL.trans hML_dvd) qk)).mp hd)
      rw [Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  -- Valuations of B at primes P k
  have hB_fact_P_eq : ∀ k : Fin m, (B (bIdx k)).factorization (P k) = αk k - 1 := by
    intro k
    have hm := hM_mod (some k)
    dsimp [modFn, resFn] at hm
    have hmod : B (bIdx k) ≡ P k ^ (αk k - 1) [MOD P k ^ αk k] := by
      dsimp [B]
      have h1 : L * M + c (bIdx k) ≡ L * solK k + c (bIdx k) [MOD P k ^ αk k] :=
        (hm.mul_left L).add_right _
      rw [mul_comm L M] at h1
      exact h1.trans (hsolK k)
    have hα : αk k = (αk k - 1) + 1 := by have hge := (hspec_ge k).1; dsimp only [αk]; omega
    rw [hα] at hmod
    exact factorization_eq_of_modEq (hBpos _).ne' (hP k).1 hmod
  have hB_not_dvd_P : ∀ k : Fin m, ∀ s : Fin (n + 1), s ≠ bIdx k → ¬ P k ∣ B s := by
    intro k s hs hdvd
    have hPk_dvd_b : P k ∣ B (bIdx k) := by
      have hge : 2 ≤ αk k := (hspec_ge k).1
      have hfac := hB_fact_P_eq k
      exact (dvd_pow_self (P k) (by omega : αk k - 1 ≠ 0)).trans
        (((hP k).1.pow_dvd_iff_le_factorization (hBpos _).ne').mpr (by omega))
    have hdiff_ne : c s ≠ c (bIdx k) := hc_mono.injective.ne hs
    rcases lt_or_gt_of_ne hdiff_ne with hlt | hgt
    · have hsub : B (bIdx k) - B s = c (bIdx k) - c s := by dsimp [B]; omega
      have h1 : P k ∣ c (bIdx k) - c s := hsub ▸ Nat.dvd_sub hPk_dvd_b hdvd
      have h2 : c (bIdx k) - c s ≤ L := (Nat.sub_le _ _).trans (hc_le _)
      have h3 := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) h1
      have := (hP k).2; omega
    · have hsub : B s - B (bIdx k) = c s - c (bIdx k) := by dsimp [B]; omega
      have h1 : P k ∣ c s - c (bIdx k) := hsub ▸ Nat.dvd_sub hdvd hPk_dvd_b
      have h2 : c s - c (bIdx k) ≤ L := (Nat.sub_le _ _).trans (hc_le _)
      have h3 := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) h1
      have := (hP k).2; omega
  -- Define r₀
  let r₀ : Fin (n + 1) → ℕ := fun s =>
    ∏ k ∈ Finset.univ.filter (fun k : Fin m => rIdx k = s), P k ^ (βk k - 1)
  have hr₀_pos : ∀ s, 0 < r₀ s := fun s =>
    Finset.prod_pos fun k _ => pow_pos (hP k).1.pos _
  have hr₀_fact : ∀ s : Fin (n + 1), ∀ p : ℕ,
      (r₀ s).factorization p = ∑ k ∈ Finset.univ.filter (fun k : Fin m => rIdx k = s),
        if p = P k then βk k - 1 else 0 := by
    intro s p
    dsimp [r₀]
    rw [Nat.factorization_prod (fun k _ => pow_ne_zero _ (hP k).1.ne_zero), Finsupp.finset_sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, (hP k).1.factorization]
    by_cases hp : p = P k
    · subst hp; simp
    · simp [hp, Finsupp.single_eq_of_ne (Ne.symm hp)]
  have hr₀_fact_P : ∀ s : Fin (n + 1), ∀ k : Fin m,
      (r₀ s).factorization (P k) = if rIdx k = s then βk k - 1 else 0 := by
    intro s k
    rw [hr₀_fact]
    by_cases h : rIdx k = s
    · rw [if_pos h, Finset.sum_eq_single k]
      · simp
      · intro k' _ hne; simp [hPmono.injective.ne hne.symm]
      · intro hnot; exfalso; exact hnot (by simp [h])
    · rw [if_neg h, Finset.sum_eq_zero]
      intro k' hk'
      have hne : k' ≠ k := by intro heq; subst heq; simp [h] at hk'
      simp [hPmono.injective.ne hne.symm]
  have hr₀_fact_other : ∀ s : Fin (n + 1), ∀ p : ℕ, (∀ k : Fin m, p ≠ P k) →
      (r₀ s).factorization p = 0 := by
    intro s p hp
    rw [hr₀_fact]
    exact Finset.sum_eq_zero fun k _ => by simp [hp k]
  -- Compute divisor ratio for (B, r₀) up to a coboundary C l / C m'
  let S₁ : Finset ℕ := L.primeFactors
  let S₂ : Finset ℕ := Finset.univ.image P
  let S_all : Finset ℕ := S₁ ∪ S₂ ∪ Finset.univ.biUnion (fun s : Fin (n + 1) => (B s).primeFactors)
  let S₃ : Finset ℕ := S_all \ (S₁ ∪ S₂)
  have hS₁₂_disj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp₂
    have hle : P k ≤ L := Nat.le_of_dvd hLpos (Nat.mem_primeFactors.mp hp₁).2.1
    have := (hP k).2; omega
  have hS_union : S_all = S₁ ∪ S₂ ∪ S₃ := by
    ext p
    by_cases h1 : p ∈ S₁ <;> by_cases h2 : p ∈ S₂ <;> simp [S₃, S_all, h1, h2]
  have hS_disj₃ : Disjoint (S₁ ∪ S₂) S₃ := disjoint_sdiff_self_right
  have hprime_sub : ∀ l m' : Fin (n + 1), l < m' →
      (U l m' * r₀ l).primeFactors ⊆ S_all ∧ (V l m' * r₀ m').primeFactors ⊆ S_all := by
    have hr₀_sub : ∀ s, (r₀ s).primeFactors ⊆ S₂ := by
      intro s p hp
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hnz : (r₀ s).factorization p ≠ 0 :=
        (Finsupp.mem_support_iff.mp (Nat.support_factorization _ ▸ hp))
      by_contra hnot
      have hall : ∀ k, p ≠ P k := fun k heq => hnot (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, heq.symm⟩)
      exact hnz (hr₀_fact_other s p hall)
    intro l m' hlm
    constructor
    · intro p hp
      rw [Nat.primeFactors_mul (hU_pos l m' hlm).ne' (hr₀_pos l).ne', mem_union] at hp
      rcases hp with hU | hr
      · have hd : p ∣ B m' := (Nat.mem_primeFactors.mp hU).2.1.trans ⟨d l m', by rw [mul_comm, hU_mul l m' hlm]⟩
        have hpm : p ∈ (B m').primeFactors := Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hU).1, hd, (hBpos m').ne'⟩
        exact mem_union_right _ (mem_biUnion.mpr ⟨m', mem_univ m', hpm⟩)
      · exact mem_union_left _ (mem_union_right _ (hr₀_sub l hr))
    · intro p hp
      rw [Nat.primeFactors_mul (hV_pos l m' hlm).ne' (hr₀_pos m').ne', mem_union] at hp
      rcases hp with hV | hr
      · have hd : p ∣ B l := (Nat.mem_primeFactors.mp hV).2.1.trans ⟨d l m', by rw [mul_comm, hV_mul l m' hlm]⟩
        have hpm : p ∈ (B l).primeFactors := Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hV).1, hd, (hBpos l).ne'⟩
        exact mem_union_right _ (mem_biUnion.mpr ⟨l, mem_univ l, hpm⟩)
      · exact mem_union_left _ (mem_union_right _ (hr₀_sub m' hr))
  -- Define coboundary C : Fin (n + 1) → ℚ
  let cobK : Fin m → Fin (n + 1) → ℚ := fun k s =>
    if (specAt k).2.2.2.2 then
      if s = (specAt k).1 then ((αk k : ℚ))⁻¹
      else if s = (specAt k).2.1 then (βk k : ℚ)
      else 1
    else
      if s = (specAt k).1 then (βk k : ℚ)
      else if s = (specAt k).2.1 then ((αk k : ℚ))⁻¹
      else 1
  have hcobK_pos : ∀ k s, 0 < cobK k s := by
    intro k s
    have hα : 0 < (αk k : ℚ) := by
      have hge : 2 ≤ αk k := (hspec_ge k).1
      exact_mod_cast (by omega : 0 < αk k)
    have hβ : 0 < (βk k : ℚ) := by
      have hge : 2 ≤ βk k := (hspec_ge k).2
      exact_mod_cast (by omega : 0 < βk k)
    dsimp [cobK]; split_ifs <;> positivity
  let C : Fin (n + 1) → ℚ := fun s =>
    (∏ k : Fin m, cobK k s) * (∏ p ∈ S₃, (((B s).factorization p + 1 : ℕ) : ℚ))⁻¹
  have hC_pos : ∀ s, 0 < C s := by
    intro s
    apply mul_pos (Finset.prod_pos fun k _ => hcobK_pos k s)
    apply inv_pos.mpr (Finset.prod_pos fun p _ => by positivity)
  have hratio₀ : ∀ l m' : Fin (n + 1), l < m' →
      (((U l m' * r₀ l).divisors.card : ℚ) / (V l m' * r₀ m').divisors.card) = q * (C l / C m') := by
    intro l m' hlm
    have hsub := hprime_sub l m' hlm
    have hU0 : U l m' * r₀ l ≠ 0 := mul_ne_zero (hU_pos l m' hlm).ne' (hr₀_pos l).ne'
    have hV0 : V l m' * r₀ m' ≠ 0 := mul_ne_zero (hV_pos l m' hlm).ne' (hr₀_pos m').ne'
    rw [card_divisors_eq_prod_of_subset hU0 hsub.1, card_divisors_eq_prod_of_subset hV0 hsub.2,
      Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib, hS_union,
      Finset.prod_union hS_disj₃, Finset.prod_union hS₁₂_disj]
    have hfacU : ∀ p, (U l m' * r₀ l).factorization p =
        (B m').factorization p - (d l m').factorization p + (r₀ l).factorization p := by
      intro p
      rw [Nat.factorization_mul (hU_pos l m' hlm).ne' (hr₀_pos l).ne', Finsupp.add_apply]
      have h1 : (d l m' * U l m').factorization p = (B m').factorization p := by rw [hU_mul l m' hlm]
      rw [Nat.factorization_mul (hd_pos l m' hlm).ne' (hU_pos l m' hlm).ne', Finsupp.add_apply] at h1
      omega
    have hfacV : ∀ p, (V l m' * r₀ m').factorization p =
        (B l).factorization p - (d l m').factorization p + (r₀ m').factorization p := by
      intro p
      rw [Nat.factorization_mul (hV_pos l m' hlm).ne' (hr₀_pos m').ne', Finsupp.add_apply]
      have h1 : (d l m' * V l m').factorization p = (B l).factorization p := by rw [hV_mul l m' hlm]
      rw [Nat.factorization_mul (hd_pos l m' hlm).ne' (hV_pos l m' hlm).ne', Finsupp.add_apply] at h1
      omega
    -- Part 1: S₁ = L.primeFactors gives gamma l m'
    have hP1 : ∏ p ∈ S₁, (((U l m' * r₀ l).factorization p + 1 : ℕ) : ℚ) /
        (((V l m' * r₀ m').factorization p + 1 : ℕ) : ℚ) = gamma l m' := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp_ne_P : ∀ k : Fin m, p ≠ P k := by
        intro k heq; subst heq
        have hle : P k ≤ L := Nat.le_of_dvd hLpos (Nat.mem_primeFactors.mp hp).2.1
        have := (hP k).2; omega
      rw [hfacU p, hfacV p, hr₀_fact_other l p hp_ne_P, hr₀_fact_other m' p hp_ne_P,
        hB_fact_L p hp m', hB_fact_L p hp l, add_zero, add_zero]
    -- Part 2: S₂ = image P gives (∏ k, cobK k l / cobK k m') * (q / gamma l m')
    have hP2 : ∏ p ∈ S₂, (((U l m' * r₀ l).factorization p + 1 : ℕ) : ℚ) /
        (((V l m' * r₀ m').factorization p + 1 : ℕ) : ℚ) =
        (∏ k : Fin m, cobK k l / cobK k m') * (q / gamma l m') := by
      rw [Finset.prod_image (fun k₁ _ k₂ _ h => hPmono.injective h)]
      have hterm : ∀ k : Fin m,
          (((U l m' * r₀ l).factorization (P k) + 1 : ℕ) : ℚ) /
            (((V l m' * r₀ m').factorization (P k) + 1 : ℕ) : ℚ) =
          (cobK k l / cobK k m') *
            (if (specAt k).1 = l ∧ (specAt k).2.1 = m' then lamVal (specAt k).2.2 else 1) := by
        intro k
        have hdk : (d l m').factorization (P k) = 0 := by
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hdvd
          have : P k ≤ L := Nat.le_of_dvd hLpos (hdvd.trans (hd_dvd_L l m' hlm))
          have := (hP k).2; omega
        rw [hfacU (P k), hfacV (P k), hdk, Nat.sub_zero, Nat.sub_zero,
          hr₀_fact_P l k, hr₀_fact_P m' k]
        have hBm : (B m').factorization (P k) = if m' = bIdx k then αk k - 1 else 0 := by
          split_ifs with h
          · rw [h]; exact hB_fact_P_eq k
          · exact Nat.factorization_eq_zero_of_not_dvd (hB_not_dvd_P k m' h)
        have hBl : (B l).factorization (P k) = if l = bIdx k then αk k - 1 else 0 := by
          split_ifs with h
          · rw [h]; exact hB_fact_P_eq k
          · exact Nat.factorization_eq_zero_of_not_dvd (hB_not_dvd_P k l h)
        rw [hBm, hBl]
        exact local_factor_eq l m' (specAt k).1 (specAt k).2.1 hlm (hspec_lt k)
          (αk k) (βk k) (hspec_ge k).1 (hspec_ge k).2 (specAt k).2.2.2.2
      rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib]
      congr 1
      -- Show product of the if-expression over k : Fin m equals q / gamma l m'
      have hlist : ∏ k : Fin m, (if (specAt k).1 = l ∧ (specAt k).2.1 = m' then lamVal (specAt k).2.2 else 1) =
          (specs.map fun s => if s.1 = l ∧ s.2.1 = m' then lamVal s.2.2 else 1).prod := by
        rw [← Fin.prod_ofFn]
        congr 1
        apply List.ext_getElem
        · simp [m]
        · intro idx h1 h2; simp [specAt]
      rw [hlist]
      dsimp only [specs]
      rw [List.map_flatMap]
      have hfm : ∀ (ls : List (Fin (n + 1) × Fin (n + 1)))
          (f : Fin (n + 1) × Fin (n + 1) → List ℚ), (ls.flatMap f).prod = (ls.map (fun x => (f x).prod)).prod := by
        intro ls f
        induction ls with
        | nil => simp
        | cons a tl ih => simp [ih]
      rw [hfm]
      have hpair_prod : ∀ ij ∈ pairs,
          ((lamList ij).map (fun e => if ij.1 = l ∧ ij.2 = m' then lamVal e else 1)).prod =
          if ij = (l, m') then q / gamma l m' else 1 := by
        intro ij _
        by_cases heq : ij = (l, m')
        · subst heq; simp [hlamList_prod (l, m')]
        · have hne : ¬ (ij.1 = l ∧ ij.2 = m') := fun ⟨h1, h2⟩ => heq (Prod.ext h1 h2)
          simp [heq, hne]
      have hmap_eq : (pairs.map fun ij => (((lamList ij).map fun e => (ij.1, ij.2, e)).map
            fun s => if s.1 = l ∧ s.2.1 = m' then lamVal s.2.2 else 1).prod) =
          pairs.map (fun ij => if ij = (l, m') then q / gamma l m' else 1) := by
        apply List.map_congr_left
        intro ij hij
        rw [List.map_map]
        exact hpair_prod ij hij
      rw [hmap_eq]
      have hmem : (l, m') ∈ pairs := (hmem_pairs l m').mpr hlm
      clear hmap_eq hpair_prod hlist hterm
      induction pairs with
      | nil => simp at hmem
      | cons hd tl ih =>
        simp only [List.nodup_cons] at hpairs_nodup
        simp only [List.mem_cons] at hmem
        simp only [List.map_cons, List.prod_cons]
        rcases hmem with rfl | htl
        · simp only [↓reduceIte]
          have hones : (tl.map fun ij => if ij = hd then q / gamma hd.1 hd.2 else 1).prod = 1 := by
            apply List.prod_eq_one
            intro x hx
            obtain ⟨ij, hij, rfl⟩ := List.mem_map.mp hx
            have hne : ij ≠ hd := fun h => hpairs_nodup.1 (h ▸ hij)
            simp [hne]
          rw [hones, mul_one]
        · have hne : hd ≠ (l, m') := fun h => hpairs_nodup.1 (h ▸ htl)
          simp only [hne, ↓reduceIte, one_mul]
          exact ih hpairs_nodup.2 htl
    -- Part 3: S₃ gives (∏ p ∈ S₃, (v_p(B m') + 1)) / (∏ p ∈ S₃, (v_p(B l) + 1))
    have hP3 : ∏ p ∈ S₃, (((U l m' * r₀ l).factorization p + 1 : ℕ) : ℚ) /
        (((V l m' * r₀ m').factorization p + 1 : ℕ) : ℚ) =
        (∏ p ∈ S₃, (((B m').factorization p + 1 : ℕ) : ℚ)) /
          (∏ p ∈ S₃, (((B l).factorization p + 1 : ℕ) : ℚ)) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp12 : p ∉ S₁ ∪ S₂ := (mem_sdiff.mp hp).2
      have hp1 : p ∉ S₁ := fun h => hp12 (mem_union_left _ h)
      have hp2 : p ∉ S₂ := fun h => hp12 (mem_union_right _ h)
      have hp_ne_P : ∀ k : Fin m, p ≠ P k := fun k h => hp2 (mem_image.mpr ⟨k, mem_univ k, h.symm⟩)
      have hdp : (d l m').factorization p = 0 := by
        by_cases hpp : p.Prime
        · apply Nat.factorization_eq_zero_of_not_dvd
          intro hdvd
          exact hp1 (Nat.mem_primeFactors.mpr ⟨hpp, hdvd.trans (hd_dvd_L l m' hlm), hLpos.ne'⟩)
        · exact Nat.factorization_eq_zero_of_not_prime _ hpp
      rw [hfacU p, hfacV p, hdp, Nat.sub_zero, Nat.sub_zero,
        hr₀_fact_other l p hp_ne_P, hr₀_fact_other m' p hp_ne_P, add_zero, add_zero]
    rw [hP1, hP2, hP3, Finset.prod_div_distrib]
    dsimp [C]
    have hg0 : gamma l m' ≠ 0 := (hgamma_pos l m').ne'
    have hB3l : ∏ p ∈ S₃, (((B l).factorization p + 1 : ℕ) : ℚ) ≠ 0 :=
      (Finset.prod_pos fun p _ => by positivity).ne'
    have hB3m : ∏ p ∈ S₃, (((B m').factorization p + 1 : ℕ) : ℚ) ≠ 0 :=
      (Finset.prod_pos fun p _ => by positivity).ne'
    have hcm : ∏ k : Fin m, cobK k m' ≠ 0 := (Finset.prod_pos fun k _ => hcobK_pos k m').ne'
    field_simp [hg0, hB3l, hB3m, hcm]
  -- Now synchronize coboundary C using n + 1 fresh primes
  let Dden : ℕ := ∏ s : Fin (n + 1), (C s)⁻¹.den
  have hDden_pos : 0 < Dden := Finset.prod_pos fun s _ => (C s)⁻¹.pos
  let t : Fin (n + 1) → ℕ := fun s => (C s)⁻¹.num.toNat * (Dden / (C s)⁻¹.den)
  have ht_eq : ∀ s : Fin (n + 1), (t s : ℚ) = (C s)⁻¹ * (Dden : ℚ) := by
    intro s
    have hden_dvd : (C s)⁻¹.den ∣ Dden := Finset.dvd_prod_of_mem (fun u => (C u)⁻¹.den) (Finset.mem_univ s)
    have hmul : (C s)⁻¹.den * (Dden / (C s)⁻¹.den) = Dden := Nat.mul_div_cancel' hden_dvd
    have hnum_nn : 0 ≤ (C s)⁻¹.num := (Rat.num_pos.mpr (inv_pos.mpr (hC_pos s))).le
    have hnum_cast : ((C s)⁻¹.num.toNat : ℚ) = ((C s)⁻¹.num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum_nn
    have hdn : ((C s)⁻¹.den : ℚ) ≠ 0 := by exact_mod_cast (C s)⁻¹.pos.ne'
    dsimp [t]
    push_cast
    rw [hnum_cast, ← (C s)⁻¹.num_div_den, ← hmul]
    push_cast
    field_simp [hdn]
  have ht_pos : ∀ s, 0 < t s := by
    intro s
    have : (0 : ℚ) < (t s : ℚ) := by
      rw [ht_eq s]; exact mul_pos (inv_pos.mpr (hC_pos s)) (by exact_mod_cast hDden_pos)
    exact_mod_cast this
  let Big := Finset.univ.sup B + Finset.univ.sup r₀ + L
  obtain ⟨Q, hQ, hQmono⟩ := fresh_primes (n + 1) Big
  let r : Fin (n + 1) → ℕ := fun s => r₀ s * Q s ^ (t s - 1)
  have hQ_gt_B : ∀ s i, B i < Q s := fun s i =>
    lt_of_le_of_lt (le_trans (Finset.le_sup (f := B) (Finset.mem_univ i)) (by omega)) (hQ s).2
  have hQ_gt_r₀ : ∀ s i, r₀ i < Q s := fun s i =>
    lt_of_le_of_lt (le_trans (Finset.le_sup (f := r₀) (Finset.mem_univ i)) (by omega)) (hQ s).2
  have hQ_gt_L : ∀ s, L < Q s := fun s =>
    lt_of_le_of_lt (by omega : L ≤ Big) (hQ s).2
  -- Prove AdmK (n + 1) B r
  have hadm : AdmK (n + 1) B r := by
    refine ⟨?_, hBmono, ?_⟩
    · intro i
      refine ⟨hBpos i, Nat.mul_pos (hr₀_pos i) (pow_pos (hQ i).1.pos _), ?_⟩
      apply Nat.Coprime.mul_left
      · -- (r₀ i).Coprime (B i)
        apply Nat.Coprime.prod_left
        intro k hk
        have hrk : rIdx k = i := (mem_filter.mp hk).2
        have hne : i ≠ bIdx k := hrk ▸ (hbr_ne k).symm
        exact (((hP k).1.coprime_iff_not_dvd.mpr (hB_not_dvd_P k i hne)).pow_left _)
      · exact ((OMA964.prime_coprime_of_lt (hBpos i) (hQ i).1 (hQ_gt_B i i)).symm.pow_left _)
    · intro i j hij
      constructor
      · -- (r i).Coprime (r j)
        have h1 : (r₀ i).Coprime (r₀ j) := by
          apply Nat.Coprime.prod_left
          intro k₁ hk₁
          apply Nat.Coprime.prod_right
          intro k₂ hk₂
          have hne : k₁ ≠ k₂ := by
            intro h; subst h
            exact hij ((mem_filter.mp hk₁).2.symm.trans (mem_filter.mp hk₂).2)
          exact (((Nat.coprime_primes (hP k₁).1 (hP k₂).1).mpr (hPmono.injective.ne hne)).pow_left _).pow_right _
        have h2 : (r₀ i).Coprime (Q j ^ (t j - 1)) :=
          (OMA964.prime_coprime_of_lt (hr₀_pos i) (hQ j).1 (hQ_gt_r₀ j i)).pow_right _
        have h3 : (Q i ^ (t i - 1)).Coprime (r₀ j) :=
          ((OMA964.prime_coprime_of_lt (hr₀_pos j) (hQ i).1 (hQ_gt_r₀ i j)).symm).pow_left _
        have h4 : (Q i ^ (t i - 1)).Coprime (Q j ^ (t j - 1)) :=
          (((Nat.coprime_primes (hQ i).1 (hQ j).1).mpr (hQmono.injective.ne hij)).pow_left _).pow_right _
        exact (h1.mul_right h2).mul_left (h3.mul_right h4)
      · -- (r i).Coprime (|B i - B j|)
        have hdiff_pos : 0 < (if B i > B j then B i - B j else B j - B i) := by
          have := hBmono.injective.ne hij; split_ifs <;> omega
        have hdiff_le : (if B i > B j then B i - B j else B j - B i) ≤ L := by
          have hi := hc_le i; have hj := hc_le j
          dsimp [B]; split_ifs <;> omega
        apply Nat.Coprime.mul_left
        · apply Nat.Coprime.prod_left
          intro k _
          exact ((OMA964.prime_coprime_of_lt hdiff_pos (hP k).1 (lt_of_le_of_lt hdiff_le (hP k).2)).symm).pow_left _
        · exact ((OMA964.prime_coprime_of_lt hdiff_pos (hQ i).1 (lt_of_le_of_lt hdiff_le (hQ_gt_L i))).symm).pow_left _
  refine ⟨B, r, U, V, hadm, ?_⟩
  intro l m' hlm
  refine ⟨hU_pos l m' hlm, hV_pos l m' hlm, hUV_rel l m' hlm, ?_⟩
  have hUl_le : U l m' ≤ B m' := Nat.div_le_self _ _
  have hVm_le : V l m' ≤ B l := Nat.div_le_self _ _
  have hcopU : (U l m' * r₀ l).Coprime (Q l ^ (t l - 1)) := by
    apply Nat.Coprime.pow_right
    exact Nat.Coprime.mul_left
      (OMA964.prime_coprime_of_lt (hU_pos l m' hlm) (hQ l).1 (lt_of_le_of_lt hUl_le (hQ_gt_B l m')))
      (OMA964.prime_coprime_of_lt (hr₀_pos l) (hQ l).1 (hQ_gt_r₀ l l))
  have hcopV : (V l m' * r₀ m').Coprime (Q m' ^ (t m' - 1)) := by
    apply Nat.Coprime.pow_right
    exact Nat.Coprime.mul_left
      (OMA964.prime_coprime_of_lt (hV_pos l m' hlm) (hQ m').1 (lt_of_le_of_lt hVm_le (hQ_gt_B m' l)))
      (OMA964.prime_coprime_of_lt (hr₀_pos m') (hQ m').1 (hQ_gt_r₀ m' m'))
  have htauU : (U l m' * r l).divisors.card = (U l m' * r₀ l).divisors.card * t l := by
    dsimp [r]
    rw [← mul_assoc, hcopU.card_divisors_mul, Nat.divisors_prime_pow (hQ l).1, Finset.card_map,
      Finset.card_range, show t l - 1 + 1 = t l by have := ht_pos l; omega]
  have htauV : (V l m' * r m').divisors.card = (V l m' * r₀ m').divisors.card * t m' := by
    dsimp [r]
    rw [← mul_assoc, hcopV.card_divisors_mul, Nat.divisors_prime_pow (hQ m').1, Finset.card_map,
      Finset.card_range, show t m' - 1 + 1 = t m' by have := ht_pos m'; omega]
  rw [htauU, htauV]
  push_cast
  rw [mul_div_mul_comm, hratio₀ l m' hlm, ht_eq l, ht_eq m']
  have hCl : C l ≠ 0 := (hC_pos l).ne'
  have hCm : C m' ≠ 0 := (hC_pos m').ne'
  have hD0 : (Dden : ℚ) ≠ 0 := by exact_mod_cast hDden_pos.ne'
  field_simp [hCl, hCm, hD0]

/-! ### Module 3: CRT Normalization for Fin K -/

private lemma diff_mod_prime {p a b x : ℕ} (hp : p.Prime)
    (h₁ : p ∣ a * x + 1) (h₂ : p ∣ b * x + 1) : a ≡ b [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  have h1 := (ZMod.natCast_eq_zero_iff _ _).2 h₁
  have h2 := (ZMod.natCast_eq_zero_iff _ _).2 h₂
  push_cast at h1 h2
  have hn : (x : ZMod p) ≠ 0 := fun e => by simp [e] at h1
  apply (ZMod.natCast_eq_natCast_iff _ _ _).1
  apply mul_right_cancel₀ hn
  linear_combination h1 - h2

theorem normalize_K (K : ℕ) (A r : Fin K → ℕ) (h : AdmK K A r) :
    ∃ M x : ℕ, ∃ a b : Fin K → ℕ, 0 < M ∧
      (∀ i, 0 < a i ∧ 0 < b i) ∧
      (∀ i j, i ≠ j → a i * b j ≠ a j * b i) ∧
      (∀ p : ℕ, p.Prime → ∃ z : ℕ, ∀ i, ¬ p ∣ a i * z + b i) ∧
      ∀ i z, A i * (M * z + x) + 1 = r i * (a i * z + b i) := by
  classical
  choose residues hr using fun i => linear_residue_K (A i) (r i ^ 2) 1 (r i)
    (by have := (h.1 i).2.1; positivity) ((h.1 i).2.2.symm.pow_right 2)
  let sol := Nat.chineseRemainderOfFinset residues (fun i => r i ^ 2) univ
    (fun i _ => pow_ne_zero _ (h.1 i).2.1.ne')
    (fun i _ j _ hij => (((h.2.2 i j hij).1.pow_left 2).pow_right 2))
  let x : ℕ := sol.val
  have hx (i) : A i * x + 1 ≡ r i [MOD r i ^ 2] :=
    (((sol.prop i (mem_univ _)).mul_left (A i)).add_right 1).trans (hr i)
  let M := ∏ i, r i ^ 2
  have hM : 0 < M := prod_pos fun i _ => pow_pos (h.1 i).2.1 _
  have hdM (i) : r i ∣ M :=
    (dvd_pow_self _ (by decide : 2 ≠ 0)).trans (dvd_prod_of_mem _ (mem_univ i))
  let a := fun i => A i * M / r i
  let b := fun i => (A i * x + 1) / r i
  have ha (i) : r i * a i = A i * M :=
    Nat.mul_div_cancel' (dvd_mul_of_dvd_right (hdM i) _)
  have hb (i) : r i * b i = A i * x + 1 :=
    Nat.mul_div_cancel' (((hx i).dvd_iff (dvd_pow_self _ (by decide : 2 ≠ 0))).mpr dvd_rfl)
  have hid (i : Fin K) (z : ℕ) : A i * (M * z + x) + 1 = r i * (a i * z + b i) := by
    calc
      _ = (A i * M) * z + (A i * x + 1) := by ring
      _ = _ := by rw [← ha, ← hb]; ring
  refine ⟨M, x, a, b, hM, ?_, ?_, ?_, hid⟩
  · intro i
    constructor
    · by_contra! he
      have hz : a i = 0 := by omega
      have e := ha i
      rw [hz, Nat.mul_zero] at e
      exact (Nat.mul_pos (h.1 i).1 hM).ne' e.symm
    · by_contra! he
      have hz : b i = 0 := by omega
      have e := hb i
      rw [hz, Nat.mul_zero] at e
      omega
  · intro i j hij he
    have e : (r i * a i) * (r j * b j) = (r j * a j) * (r i * b i) := by
      calc
        _ = r i * r j * (a i * b j) := by ring
        _ = _ := by rw [he]; ring
    rw [ha, ha, hb, hb] at e
    have eq : A i * M = A j * M := by nlinarith only [e]
    exact hij (h.2.1.injective (Nat.eq_of_mul_eq_mul_right hM eq))
  · intro p hp
    by_cases pm : p ∣ M
    · obtain ⟨j, _, hj⟩ := (hp.prime.dvd_finsetProd_iff _).mp pm
      have pr : p ∣ r j := hp.dvd_of_dvd_pow hj
      refine ⟨0, fun i => ?_⟩
      simp only [mul_zero, zero_add]
      intro pi
      by_cases ij : j = i
      · subst i
        have hb1 : b j ≡ 1 [MOD r j] := by
          apply Nat.ModEq.mul_left_cancel' (h.1 j).2.1.ne'
          simpa only [ha, hb, pow_two, mul_one] using (hx j)
        exact hp.not_dvd_one ((hb1.dvd_iff pr).mp pi)
      · have di : p ∣ A i * x + 1 := hb i ▸ dvd_mul_of_dvd_right pi (r i)
        have dj : p ∣ A j * x + 1 := hb j ▸ dvd_mul_of_dvd_left pr (b j)
        have eq := diff_mod_prime hp dj di
        apply hp.ne_one (Nat.eq_one_of_dvd_coprimes (h.2.2 j i ij).2 pr ?_)
        split
        · exact eq.symm.dvd'
        · exact eq.dvd'
    · obtain ⟨z, hz⟩ := linear_residue_K M p x 0 hp.pos (hp.coprime_iff_not_dvd.mpr pm).symm
      refine ⟨z, fun i pi => ?_⟩
      have d : p ∣ A i * (M * z + x) + 1 := hid i z ▸ dvd_mul_of_dvd_right pi (r i)
      have one : A i * (M * z + x) + 1 ≡ 1 [MOD p] := by
        simpa using (hz.mul_left (A i)).add_right 1
      exact hp.not_dvd_one ((one.dvd_iff dvd_rfl).mp d)

end OMA964K

theorem OMA.solution : type_of% @Erdos964.erdos_964.variants.eberhard := by
  sorry
