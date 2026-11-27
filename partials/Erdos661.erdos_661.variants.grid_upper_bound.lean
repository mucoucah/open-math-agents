import FormalConjectures.ErdosProblems.«661»
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds

-- Problem: Erdős Problem 661 — grid upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/661.lean:86 (declaration Erdos661.erdos_661.variants.grid_upper_bound)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset Filter

namespace OMA661

open Classical in
/-- numbers at most N that are sums of two squares of naturals -/
noncomputable def S2 (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun m => ∃ a ∈ range (N + 1), ∃ b ∈ range (N + 1), a ^ 2 + b ^ 2 = m

/-- grid point -/
noncomputable def gp (p : ℕ × ℕ) : EuclideanSpace ℝ (Fin 2) := !₂[(p.1 : ℝ), (p.2 : ℝ)]

lemma gp_inj : Function.Injective gp := by
  intro p q h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
  simp [gp] at h0 h1
  exact Prod.ext h0 h1

lemma dist_gp (p q : ℕ × ℕ) :
    dist (gp p) (gp q) = Real.sqrt (((Int.natAbs ((p.1 : ℤ) - q.1)) ^ 2 +
      (Int.natAbs ((p.2 : ℤ) - q.2)) ^ 2 : ℕ)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  simp only [gp, Fin.sum_univ_two]
  push_cast
  simp [Nat.cast_natAbs, sq_abs, Nat.dist_eq]

lemma cross_le (n : ℕ) : Erdos661.minimalCrossDistances (EuclideanSpace ℝ (Fin 2)) n ≤
    #(S2 (2 * (Nat.sqrt (2 * n) + 1) ^ 2)) := by
  set k := Nat.sqrt (2 * n) + 1 with hk
  have hk2 : 2 * n ≤ k ^ 2 := by
    have := Nat.lt_succ_sqrt (2 * n)
    rw [hk]; nlinarith
  set G : Finset (EuclideanSpace ℝ (Fin 2)) := (range k ×ˢ range k).image gp
  have hG : #G = k ^ 2 := by
    rw [card_image_of_injective _ gp_inj, card_product, card_range]; ring
  obtain ⟨Q, hQG, hQ⟩ := exists_subset_card_eq (show 2 * n ≤ #G by omega)
  obtain ⟨A, hAQ, hA⟩ := exists_subset_card_eq (show n ≤ #Q by omega)
  have hB : #(Q \ A) = n := by rw [card_sdiff_of_subset hAQ]; omega
  have h1 : Erdos661.minimalCrossDistances (EuclideanSpace ℝ (Fin 2)) n ≤
      #(Erdos661.crossDistanceSet A (Q \ A)) :=
    Nat.sInf_le ⟨A, Q \ A, hA, hB, disjoint_sdiff, rfl⟩
  refine h1.trans ?_
  refine le_trans (card_le_card (t := (S2 (2 * k ^ 2)).image fun m : ℕ => Real.sqrt m) ?_)
    card_image_le
  intro d hd
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.1 hd
  obtain ⟨hx, hy⟩ := mem_product.1 hxy
  have hxG := hQG (hAQ hx)
  have hyG := hQG (sdiff_subset hy)
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hxG
  obtain ⟨q, hq, rfl⟩ := mem_image.1 hyG
  simp only [mem_product, mem_range] at hp hq
  rw [mem_image]
  refine ⟨_, ?_, (dist_gp p q).symm⟩
  have e1 : Int.natAbs ((p.1 : ℤ) - q.1) < k := by omega
  have e2 : Int.natAbs ((p.2 : ℤ) - q.2) < k := by omega
  have hsq1 : Int.natAbs ((p.1 : ℤ) - q.1) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left e1.le 2
  have hsq2 : Int.natAbs ((p.2 : ℤ) - q.2) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left e2.le 2
  have hkk : k ≤ k ^ 2 := by nlinarith
  simp only [S2, mem_filter, mem_range]
  refine ⟨by omega, _, by omega, _, by omega, rfl⟩

open ArithmeticFunction

private def Good (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 = 1

private lemma good_mul (a b : ℕ) : Good (a * b) ↔ Good a ∧ Good b := by
  by_cases ha : a = 0
  · simp [Good, ha]
  by_cases hb : b = 0
  · simp [Good, hb]
  simp only [Good, ha, hb, mul_ne_zero ha hb, true_and, Nat.primeFactors_mul ha hb,
    Finset.mem_union]
  exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
    fun h p hp => hp.elim (h.1 p) (h.2 p)⟩

open Classical in
private noncomputable def goodWeight : ArithmeticFunction ℝ :=
  ⟨fun n => if Good n then 1 else 0, by simp [Good]⟩

private lemma goodWeight_mul (a b : ℕ) : goodWeight (a * b) = goodWeight a * goodWeight b := by
  classical
  change (if Good (a * b) then 1 else 0 : ℝ) =
    (if Good a then 1 else 0) * (if Good b then 1 else 0)
  by_cases ha : Good a <;> by_cases hb : Good b <;> simp [good_mul, ha, hb]

private lemma goodWeight_nonneg (n : ℕ) : 0 ≤ goodWeight n := by
  classical
  change 0 ≤ (if Good n then 1 else 0 : ℝ)
  split <;> norm_num

private lemma goodWeight_le_one (n : ℕ) : goodWeight n ≤ 1 := by
  classical
  change (if Good n then 1 else 0 : ℝ) ≤ 1
  split <;> norm_num

private def chi4 (d : ℕ) : ℝ :=
  if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

private lemma chi4_mul (a b : ℕ) : chi4 (a * b) = chi4 a * chi4 b := by
  have ha := Nat.mod_lt a (by omega : 0 < 4)
  have hb := Nat.mod_lt b (by omega : 0 < 4)
  unfold chi4
  rw [Nat.mul_mod]
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> norm_num

private lemma chi4_pow (p k : ℕ) : chi4 (p ^ k) = (chi4 p) ^ k := by
  induction k with
  | zero => norm_num [chi4]
  | succ k ih => rw [pow_succ, chi4_mul, ih, pow_succ]

private def divSumChi4 (n : ℕ) : ℝ := ∑ d ∈ n.divisors, chi4 d

private lemma divSumChi4_mul {m n : ℕ} (hmn : m.Coprime n) :
    divSumChi4 (m * n) = divSumChi4 m * divSumChi4 n := by
  simp only [divSumChi4]
  rw [hmn.divisors_mul, Finset.sum_map]
  change ∑ p ∈ (m.divisors ×ˢ n.divisors).attach, chi4 (p.1.1 * p.1.2) = _
  rw [Finset.sum_attach (s := m.divisors ×ˢ n.divisors) (f := fun p => chi4 (p.1 * p.2)),
    Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact chi4_mul a b

private lemma divSumChi4_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divSumChi4 (p ^ k) = ∑ j ∈ Finset.range (k + 1), (chi4 p) ^ j := by
  rw [divSumChi4, Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa using chi4_pow p j

private lemma divSumChi4_nonneg (n : ℕ) : 0 ≤ divSumChi4 n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp [divSumChi4]
  | prime_pow p k hp =>
      rw [divSumChi4_prime_pow hp]
      have hh := Nat.mod_lt p (by omega : 0 < 4)
      unfold chi4
      interval_cases (p % 4) <;> norm_num
      all_goals first | (rw [neg_one_geom_sum]; split <;> norm_num) |
        (exact sum_nonneg fun j _ => pow_nonneg (by norm_num) _)
  | coprime m n _ _ hm ih₁ ih₂ => rw [divSumChi4_mul hm]; exact mul_nonneg ih₁ ih₂

private lemma chi4_of_good {n : ℕ} (hn : Good n) : chi4 n = 1 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => exact (hn.1 rfl).elim
  | prime_pow p k hp =>
      rw [chi4_pow]
      by_cases hk : k = 0
      · simp [hk]
      have h := hn.2 p (by simp [Nat.primeFactors_prime_pow hk hp])
      simp [chi4, h]
  | coprime a b _ _ _ iha ihb =>
      rw [chi4_mul, iha (good_mul a b |>.mp hn).1, ihb (good_mul a b |>.mp hn).2, mul_one]

private lemma divSumChi4_eq_card {n : ℕ} (hn : Good n) :
    divSumChi4 n = (n.divisors.card : ℝ) := by
  rw [divSumChi4, show (n.divisors.card : ℝ) = ∑ _ ∈ n.divisors, (1 : ℝ) by simp]
  refine sum_congr rfl fun d hd => chi4_of_good ⟨?_, ?_⟩
  · exact (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (Nat.pos_of_ne_zero hn.1)).ne'
  · intro p hp
    exact hn.2 p (Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 hn.1 hp)

private lemma goodWeight_sq_le (n : ℕ) :
    (goodWeight * goodWeight) n ≤ divSumChi4 n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal]
  simp_rw [← goodWeight_mul]
  by_cases hn : Good n
  · rw [divSumChi4_eq_card hn]
    rw [show (n.divisors.card : ℝ) = ∑ _ ∈ n.divisors, (1 : ℝ) by simp]
    exact sum_le_sum fun _ _ => goodWeight_le_one _
  · have eq0 : ∑ d ∈ n.divisors, goodWeight (d * (n / d)) = 0 := by
      exact sum_eq_zero fun d hd => by
        rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
        simp [goodWeight, hn]
    rw [eq0]
    exact divSumChi4_nonneg n

private lemma sumsq_goodPart {n : ℕ} (hn : n ≠ 0) (h : ∃ x y : ℕ, n = x ^ 2 + y ^ 2) :
    ∃ a c : ℕ, a ≠ 0 ∧ Good c ∧ (n = a ^ 2 * c ∨ n = 2 * (a ^ 2 * c)) := by
  obtain ⟨a, b, hab, hb⟩ := Nat.eq_sq_add_sq_iff_eq_sq_mul.mp h
  have ha0 : a ≠ 0 := by intro he; simp [he] at hab; exact hn hab
  have hb0 : b ≠ 0 := by intro he; simp [he] at hab; exact hn hab
  have h4 : ¬ 4 ∣ b := by
    intro hd
    exact (by decide : ¬ IsSquare (-1 : ZMod 4)) (ZMod.isSquare_neg_one_of_dvd hd hb)
  have odd_good : ∀ c : ℕ, c ∣ b → c % 2 = 1 → Good c := by
    intro c hc hcodd
    refine ⟨(Nat.pos_of_dvd_of_pos hc (Nat.pos_of_ne_zero hb0)).ne', ?_⟩
    intro p hp
    have hnot3 := Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one
      (Nat.primeFactors_mono hc hb0 hp) hb
    have hp2 : p ≠ 2 := by
      intro he
      have hd : 2 ∣ c := he ▸ Nat.dvd_of_mem_primeFactors hp
      omega
    have hodd := (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two hp2
    have hm := Nat.odd_iff.mp hodd
    omega
  by_cases he : 2 ∣ b
  · obtain ⟨c, rfl⟩ := he
    refine ⟨a, c, ha0, odd_good c (dvd_mul_left _ _) (by omega), Or.inr ?_⟩
    rw [hab]
    ring
  · exact ⟨a, b, ha0, odd_good b dvd_rfl (by omega), Or.inl hab⟩

private lemma sum_mul_pairs {R : Type*} [AddCommMonoid R] (N : ℕ) (w : ℕ → ℕ → R) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, w p.1 p.2) =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 (N / a), w a b := by
  classical
  rw [← sum_sigma (Icc 1 N) Nat.divisorsAntidiagonal
    (fun p => w p.2.1 p.2.2),
    ← sum_sigma (Icc 1 N) (fun a => Icc 1 (N / a))
      (fun p => w p.1 p.2)]
  refine sum_bij (fun p _ => ⟨p.2.1, p.2.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨n, a, b⟩ hp
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨hn, rfl, hn0⟩ := hp
    have ha : 0 < a := Nat.pos_of_ne_zero (fun h => by simp [h] at hn0)
    have hb : 0 < b := Nat.pos_of_ne_zero (fun h => by simp [h] at hn0)
    simp only [mem_sigma, mem_Icc]
    exact ⟨⟨ha, (Nat.le_mul_of_pos_right _ hb).trans hn.2⟩, hb,
      (Nat.le_div_iff_mul_le ha).mpr (by simpa [mul_comm] using hn.2)⟩
  · rintro ⟨n, a, b⟩ hp ⟨m, c, d⟩ hq he
    simp only [mem_sigma, Nat.mem_divisorsAntidiagonal] at hp hq
    have hac : a = c := congrArg Sigma.fst he
    have hbd : b = d := congrArg (fun q : Σ _ : ℕ, ℕ => q.2) he
    subst c
    subst d
    rw [← hp.2.1, ← hq.2.1]
  · rintro ⟨a, b⟩ hp
    simp only [mem_sigma, mem_Icc] at hp
    have hmul := (Nat.le_div_iff_mul_le (show 0 < a from hp.1.1)).mp hp.2.2
    refine ⟨⟨a * b, a, b⟩, ?_, rfl⟩
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal]
    have hpos : 0 < a * b := Nat.mul_pos hp.1.1 hp.2.1
    exact ⟨⟨hpos, by simpa [mul_comm] using hmul⟩, rfl, hpos.ne'⟩
  · intro p hp
    rfl

/-- Landau upper bound (the only missing analytic input) -/
lemma landau_upper : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    (#(S2 N) : ℝ) ≤ C * N / Real.sqrt (Real.log N) := by
  sorry

end OMA661

theorem OMA.solution : type_of% @Erdos661.erdos_661.variants.grid_upper_bound := by
  obtain ⟨C, hC⟩ := OMA661.landau_upper
  rw [Asymptotics.isBigO_iff]
  refine ⟨|C| * 14, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  set k := Nat.sqrt (2 * n) + 1 with hk
  have hk2 : 2 * n ≤ k ^ 2 := by
    have := Nat.lt_succ_sqrt (2 * n)
    rw [hk]; nlinarith
  have hk7 : k ^ 2 ≤ 7 * n := by
    have h1 := Nat.sqrt_le' (2 * n)
    have h2 := Nat.sqrt_le_self (2 * n)
    rw [hk]; nlinarith
  set N := 2 * k ^ 2 with hN
  have hN2 : 2 ≤ N := by omega
  have h1 := OMA661.cross_le n
  have h2 := hC N hN2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hNn : (n : ℝ) ≤ N := by
    have : n ≤ N := by omega
    exact_mod_cast this
  have hN14 : (N : ℝ) ≤ 14 * n := by
    have : N ≤ 14 * n := by omega
    exact_mod_cast this
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlogle : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hNn
  have hsn : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.2 hlogn
  have hsle : Real.sqrt (Real.log n) ≤ Real.sqrt (Real.log N) := Real.sqrt_le_sqrt hlogle
  have hF : (Erdos661.minimalCrossDistances (EuclideanSpace ℝ (Fin 2)) n : ℝ) ≤
      (#(OMA661.S2 N) : ℝ) := by exact_mod_cast h1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc (Erdos661.minimalCrossDistances (EuclideanSpace ℝ (Fin 2)) n : ℝ)
      ≤ C * N / Real.sqrt (Real.log N) := hF.trans h2
    _ ≤ |C| * N / Real.sqrt (Real.log n) := by
        gcongr
        · exact le_abs_self C
    _ ≤ |C| * (14 * n) / Real.sqrt (Real.log n) := by gcongr
    _ = |C| * 14 * (n / Real.sqrt (Real.log n)) := by ring
