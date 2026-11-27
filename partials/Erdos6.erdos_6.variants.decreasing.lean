import FormalConjectures.ErdosProblems.«6»
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals

-- Problem: Erdős Problem 6 — decreasing
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/6.lean:64 (declaration Erdos6.erdos_6.variants.decreasing)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! # Decreasing runs of consecutive prime gaps -/

open Erdos6
open scoped BigOperators

/-- Monotonicity: a longer decreasing run implies a shorter one. -/
lemma OMA.dec_mono {m k : ℕ} (h : m ≤ k) :
    {n | ∀ i ∈ Finset.range k, primeGap (n + i) > primeGap (n + i + 1)} ⊆
    {n | ∀ i ∈ Finset.range m, primeGap (n + i) > primeGap (n + i + 1)} := by
  intro n hn i hi
  exact hn i (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) h))

/-- The case m = 0 is trivial: the set is all of ℕ. -/
lemma OMA.dec_zero :
    {n | ∀ i ∈ Finset.range 0, primeGap (n + i) > primeGap (n + i + 1)}.Infinite := by
  simp only [Finset.range_zero, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
    Set.setOf_true]
  exact Set.infinite_univ

lemma OMA.dec_run_of_window {x w m : ℕ}
    (hcard : m + 2 ≤ ((Finset.Icc x (x + w)).filter Nat.Prime).card)
    (hgap : ∀ {a b c}, x ≤ a → c ≤ x + w → a < b → b < c →
      a.Prime → b.Prime → c.Prime → c - b < b - a) :
    ∃ n, x ≤ Nat.nth Nat.Prime n ∧
      ∀ i ∈ Finset.range m, primeGap (n + i) > primeGap (n + i + 1) := by
  let l := Nat.count Nat.Prime x
  let u := Nat.count Nat.Prime (x + w + 1)
  have hsize : ((Finset.Icc x (x + w)).filter Nat.Prime).card ≤ u - l := by
    rw [← Nat.card_Ico]
    apply Finset.card_le_card_of_injOn (Nat.count Nat.Prime)
    · intro a ha
      obtain ⟨ha, hp⟩ := Finset.mem_filter.mp ha
      obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp ha
      exact Finset.mem_Ico.mpr
        ⟨Nat.count_monotone _ hl, Nat.count_strict_mono hp (by omega)⟩
    · intro a ha b hb hab
      exact Nat.count_injective (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  have hinf := Nat.infinite_setOfPred_prime
  refine ⟨l, Nat.le_nth_count hinf x, ?_⟩
  intro i hi
  have hi := Finset.mem_range.mp hi
  have hleft : x ≤ Nat.nth Nat.Prime (l + i) :=
    (Nat.le_nth_count hinf x).trans (Nat.nth_monotone hinf (Nat.le_add_right l i))
  have hright : Nat.nth Nat.Prime (l + i + 1 + 1) ≤ x + w := by
    apply Nat.lt_succ_iff.mp
    have hil : l + i + 1 + 1 < u := by omega
    exact Nat.nth_lt_of_lt_count hil
  unfold primeGap
  exact hgap hleft hright
    (Nat.nth_strictMono hinf (by omega)) (Nat.nth_strictMono hinf (by omega))
    (Nat.nth_mem_of_infinite hinf _) (Nat.nth_mem_of_infinite hinf _)
    (Nat.nth_mem_of_infinite hinf _)

/-- Reflected powers of two ensure that every ordered triple has decreasing gaps. -/
lemma OMA.exists_dec_offsets (k : ℕ) :
    ∃ w : ℕ, ∃ H : Finset ℕ, H.card = k ∧
      (∀ a ∈ H, a ≤ w ∧ k.factorial ∣ a) ∧
      (∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, a < b → b < c → c - b < b - a) := by
  let f : ℕ → ℕ := fun i => k.factorial * (2 ^ k - 2 ^ i)
  have hpos := Nat.factorial_pos k
  have hanti : ∀ {i j}, i < j → j < k → f j < f i := by
    intro i j hij hj
    have hpow : (2 : ℕ) ^ i < 2 ^ j := pow_lt_pow_right₀ (by decide) hij
    have htop : (2 : ℕ) ^ j ≤ 2 ^ k := pow_le_pow_right' (by decide) hj.le
    exact Nat.mul_lt_mul_of_pos_left (by omega) hpos
  have hrev : ∀ {i j}, i < k → j < k → f i < f j → j < i := by
    intro i j hi hj hlt
    rcases lt_trichotomy i j with hij | hij | hij
    · exact ((hanti hij hj).not_gt hlt).elim
    · exact ((congrArg f hij).not_lt hlt).elim
    · exact hij
  refine ⟨k.factorial * 2 ^ k, (Finset.range k).image f, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj heq
    rcases lt_trichotomy i j with hij | hij | hij
    · exact ((hanti hij (Finset.mem_range.mp hj)).ne heq.symm).elim
    · exact hij
    · exact ((hanti hij (Finset.mem_range.mp hi)).ne heq).elim
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨Nat.mul_le_mul_left _ (Nat.sub_le ..), dvd_mul_right _ _⟩
  · intro a ha b hb c hc hab hbc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
    simp only [Finset.mem_range] at hi hj hl
    have hji := hrev hi hj hab
    have hlj := hrev hj hl hbc
    have htop : (2 : ℕ) ^ i ≤ 2 ^ k := pow_le_pow_right' (by decide) hi.le
    have hji' : 2 ^ j * 2 ≤ (2 : ℕ) ^ i := by
      rw [← pow_succ]
      exact pow_le_pow_right' (by decide) hji
    have hlj' : (2 : ℕ) ^ l < 2 ^ j := pow_lt_pow_right₀ (by decide) hlj
    have hlow : 0 < (2 : ℕ) ^ l := by positivity
    dsimp only [f]
    rw [← Nat.mul_sub_left_distrib, ← Nat.mul_sub_left_distrib]
    exact Nat.mul_lt_mul_of_pos_left (by omega) hpos

/-- A progression covering every excluded offset in a finite window. -/
lemma OMA.dec_cover {w : ℕ} {H : Finset ℕ} (hH : ∀ a ∈ H, a ≤ w) :
    ∃ M b : ℕ, 0 < M ∧
      (∀ x, M < x → ∀ a ≤ w, (M * x + b + a).Prime → a ∈ H) ∧
      (∀ p, p.Prime → p ∣ M → ∀ a ∈ H, ¬ p ∣ b + a) := by
  let S := Finset.Icc 0 w \ H
  let q (a : ℕ) := Nat.nth Nat.Prime (w + 1 + a)
  have hinf := Nat.infinite_setOfPred_prime
  have hqp (a : ℕ) : (q a).Prime := Nat.nth_mem_of_infinite hinf _
  have hqw (a : ℕ) : w < q a :=
    (Nat.lt_succ_self w).trans_le ((Nat.le_add_right (w + 1) a).trans ((Nat.nth_strictMono hinf).id_le _))
  have hqi : Function.Injective q := fun a b hab =>
    Nat.add_left_cancel (Nat.nth_injective hinf hab)
  have hpair : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime q) := by
    intro a ha b hb hab
    exact (Nat.coprime_primes (hqp a) (hqp b)).2 (fun h => hab (hqi h))
  let M := ∏ a ∈ S, q a
  let b := Nat.chineseRemainderOfFinset (fun a => q a - a) q S
    (fun a _ => (hqp a).ne_zero) hpair
  have hM : 0 < M := Finset.prod_pos fun a _ => (hqp a).pos
  have hd (a : ℕ) (ha : a ∈ S) : q a ∣ (b : ℕ) + a := by
    have ha' := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp ha).1).2
    have hc := (b.property a ha).add_right a
    rw [Nat.sub_add_cancel (ha'.trans (hqw a).le)] at hc
    exact Nat.modEq_zero_iff_dvd.mp (hc.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  refine ⟨M, b, hM, ?_, ?_⟩
  · intro x hx a haw hp
    by_contra ha
    have hs : a ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, haw⟩, ha⟩
    have hqM : q a ∣ M := Finset.dvd_prod_of_mem q hs
    have hqx : q a < M * x + (b : ℕ) + a := by
      have hle := Nat.le_of_dvd hM hqM
      have hmx : x ≤ M * x := by
        calc
          x = 1 * x := (Nat.one_mul x).symm
          _ ≤ M * x := Nat.mul_le_mul_right x hM
      omega
    have hd' : q a ∣ M * x + (b : ℕ) + a := by
      rw [add_assoc]
      exact (dvd_mul_of_dvd_left hqM x).add (hd a hs)
    rcases hp.eq_one_or_self_of_dvd (q a) hd' with h | h
    · exact (hqp a).ne_one h
    · exact hqx.ne h
  · intro p hp hpM a ha hpa
    obtain ⟨u, hu, hpu⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff q).mp hpM
    have heq : p = q u := (Nat.prime_dvd_prime_iff_eq hp (hqp u)).mp hpu
    subst p
    have hcong := (Nat.modEq_zero_iff_dvd.mpr hpa).trans
      (Nat.modEq_zero_iff_dvd.mpr (hd u hu)).symm
    have hmod := Nat.ModEq.add_left_cancel' (b : ℕ) hcong
    have hua := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hu).1).2
    have hau := hmod.eq_of_lt_of_lt ((hH a ha).trans_lt (hqw u)) (hua.trans_lt (hqw u))
    exact (Finset.mem_sdiff.mp hu).2 (hau ▸ ha)

/-- A suitable affine progression has no prime dividing a form for every residue. -/
lemma OMA.dec_admissible {k M b : ℕ} {H : Finset ℕ}
    (hcard : H.card = k) (hfac : ∀ a ∈ H, k.factorial ∣ a)
    (hcop : ∀ p, p.Prime → p ∣ M → ∀ a ∈ H, ¬ p ∣ b + a) :
    ∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a := by
  classical
  intro p hp
  by_cases hM : p ∣ M
  · refine ⟨0, ?_⟩
    simpa using hcop p hp hM
  let : Fact p.Prime := ⟨hp⟩
  have hM' : (M : ZMod p) ≠ 0 := fun h => hM ((ZMod.natCast_eq_zero_iff M p).mp h)
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, ∀ a ∈ H, r + (a : ZMod p) ≠ 0 := by
    by_cases hpk : p ≤ k
    · refine ⟨1, ?_⟩
      intro a ha
      have hd := (Nat.dvd_factorial hp.pos hpk).trans (hfac a ha)
      rw [(ZMod.natCast_eq_zero_iff a p).mpr hd, add_zero]
      exact one_ne_zero
    · let T : Finset (ZMod p) := H.image (fun a : ℕ => -(a : ZMod p))
      have hT : T.card < Fintype.card (ZMod p) := by
        rw [ZMod.card p]
        exact Finset.card_image_le.trans_lt (hcard.symm ▸ Nat.lt_of_not_ge hpk)
      obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ T := by
        by_contra! h
        have heq : T = Finset.univ := Finset.eq_univ_of_forall h
        rw [heq, Finset.card_univ] at hT
        exact (lt_irrefl _ hT)
      refine ⟨r, fun a ha h => hr ?_⟩
      exact Finset.mem_image.mpr ⟨a, ha, (eq_neg_of_add_eq_zero_left h).symm⟩
  let t : ZMod p := (M : ZMod p)⁻¹ * (r - (b : ZMod p))
  refine ⟨t.val, ?_⟩
  intro a ha hd
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr hd
  push_cast at hz
  rw [ZMod.natCast_zmod_val] at hz
  have heq : (M : ZMod p) * t + (b : ZMod p) = r := by
    dsimp [t]
    rw [← mul_assoc, mul_inv_cancel₀ hM', one_mul, sub_add_cancel]
  rw [heq] at hz
  exact hr a ha hz

lemma OMA.dec_gap_pos (n : ℕ) : 0 < primeGap n :=
  Nat.sub_pos_of_lt (Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n))

lemma OMA.dec_nth_succ (n : ℕ) : Nat.nth Nat.Prime (n + 1) = Nat.nth Nat.Prime n + primeGap n := by
  unfold primeGap
  exact (Nat.add_sub_of_le (Nat.nth_monotone Nat.infinite_setOfPred_prime (Nat.le_succ n))).symm

/-- A block of equal prime gaps has length less than twice the gap plus two. -/
lemma OMA.dec_not_constant (n d : ℕ) (hd : 0 < d)
    (h : ∀ i < 2 * (d + 1), primeGap (n + i) = d) : False := by
  have hlin : ∀ i ≤ 2 * (d + 1), Nat.nth Nat.Prime (n + i) = Nat.nth Nat.Prime n + d * i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      rw [← Nat.add_assoc, OMA.dec_nth_succ, h i (by omega), ih (by omega), Nat.mul_succ, add_assoc]
  let q := d + 1
  let t := Nat.nth Nat.Prime n % q + q
  have hq : 0 < q := Nat.succ_pos d
  have ht : t ≤ 2 * q := by
    have hmod := Nat.mod_lt (Nat.nth Nat.Prime n) hq
    dsimp [t]
    omega
  have hpt : Nat.nth Nat.Prime n ≡ t [MOD q] := by
    change Nat.nth Nat.Prime n % q = (Nat.nth Nat.Prime n % q + q) % q
    simp
  have hdiv : q ∣ Nat.nth Nat.Prime (n + t) := by
    rw [hlin t ht]
    apply Nat.modEq_zero_iff_dvd.mp
    calc
      Nat.nth Nat.Prime n + d * t ≡ t + d * t [MOD q] := hpt.add_right _
      _ ≡ 0 [MOD q] := by
        apply Nat.modEq_zero_iff_dvd.mpr
        have heq : t + d * t = q * t := by dsimp [q]; ring
        rw [heq]
        exact dvd_mul_right _ _
  have hprime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n + t)
  have hp := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
  rcases hprime.eq_one_or_self_of_dvd q hdiv with heq | heq
  · dsimp [q] at heq
    omega
  · have hqt : q ≤ t := Nat.le_add_left _ _
    have htd : t ≤ d * t := calc
      t = 1 * t := (Nat.one_mul t).symm
      _ ≤ d * t := Nat.mul_le_mul_right t hd
    rw [hlin t ht] at heq
    have hp2 : 2 ≤ Nat.nth Nat.Prime n := hp.two_le
    omega

/-- Eventual monotonicity would force a polynomial lower bound on prime gaps. -/
lemma OMA.dec_gap_growth {N : ℕ} (hg : Monotone fun n => primeGap (N + n)) (n : ℕ) :
    n < 4 * (primeGap (N + n)) ^ 2 := by
  let g : ℕ → ℕ := fun n => primeGap (N + n)
  have hreach : ∀ d, d < g (d * (d + 3)) := by
    intro d
    induction d with
    | zero => exact OMA.dec_gap_pos _
    | succ d ih =>
      let j := d * (d + 3)
      let L := 2 * (d + 2)
      have heq : (d + 1) * (d + 1 + 3) = j + L := by dsimp [j, L]; ring
      change d + 1 < g ((d + 1) * (d + 1 + 3))
      rw [heq]
      by_contra! h
      have hall (i : ℕ) (hi : i < L) : primeGap ((N + j) + i) = d + 1 := by
        rw [add_assoc]
        have hlo : g j ≤ g (j + i) := hg (Nat.le_add_right _ _)
        have hup : g (j + i) ≤ g (j + L) := hg (Nat.add_le_add_left hi.le j)
        change g (j + i) = d + 1
        change d < g j at ih
        omega
      exact OMA.dec_not_constant (N + j) (d + 1) (by omega) hall
  have hn : n < g n * (g n + 3) := by
    by_contra! h
    exact (hreach (g n)).not_ge (hg h)
  have hp : 1 ≤ g n := OMA.dec_gap_pos _
  have hb := Nat.mul_le_mul_left (g n) (show g n + 3 ≤ 4 * g n by omega)
  calc
    n < g n * (g n + 3) := hn
    _ ≤ g n * (4 * g n) := hb
    _ = 4 * g n ^ 2 := by ring

/-- If the gaps were eventually nondecreasing, the prime reciprocals would be summable. -/
lemma OMA.dec_summable_of_monotone {N : ℕ} (hg : Monotone fun n => primeGap (N + n)) :
    Summable (fun n : ℕ => 1 / (Nat.nth Nat.Prime n : ℝ)) := by
  let g (n : ℕ) := primeGap (N + n)
  let p (n : ℕ) : ℝ := Nat.nth Nat.Prime (N + n)
  have hpos (n : ℕ) : 0 < p n := by
    dsimp only [p]
    exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (N + n)).pos
  have hmono : Monotone p := by
    intro i j hij
    dsimp only [p]
    exact_mod_cast Nat.nth_monotone Nat.infinite_setOfPred_prime (Nat.add_le_add_left hij N)
  have hadd (n t : ℕ) : t * g n ≤ Nat.nth Nat.Prime (N + n + t) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [← add_assoc, OMA.dec_nth_succ, Nat.add_mul, one_mul]
      exact Nat.add_le_add ih (by simpa only [← add_assoc] using hg (Nat.le_add_right n t))
  have hlarge (n : ℕ) : n * g n ≤ Nat.nth Nat.Prime (N + 2 * n) := by
    have he : N + 2 * n = N + n + n := by omega
    rw [he]
    exact hadd n n
  have hpow (n : ℕ) : (n : ℝ) ^ (3 / 2 : ℝ) ≤ 2 * p (2 * n) := by
    have hcub : n ^ 3 ≤ 4 * (Nat.nth Nat.Prime (N + 2 * n)) ^ 2 := by
      have hd := (OMA.dec_gap_growth hg n).le
      calc
        n ^ 3 = n ^ 2 * n := by ring
        _ ≤ n ^ 2 * (4 * g n ^ 2) := Nat.mul_le_mul_left _ hd
        _ = 4 * (n * g n) ^ 2 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hlarge n) 2)
    have hcub' : (n : ℝ) ^ 3 ≤ 4 * (p (2 * n)) ^ 2 := by
      dsimp only [p]
      exact_mod_cast hcub
    have hsq : ((n : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ 3 := by
      rw [← Real.rpow_mul_natCast (by positivity)]
      have he : (3 / 2 : ℝ) * (2 : ℕ) = (3 : ℕ) := by norm_num
      rw [he, Real.rpow_natCast]
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (3 / 2 : ℝ), hpos (2 * n)]
  let f (n : ℕ) := 1 / p n
  have hnonneg (n : ℕ) : 0 ≤ f n := (one_div_pos.mpr (hpos n)).le
  have hseries : Summable (fun n : ℕ => 2 * (1 / (n : ℝ) ^ (3 / 2 : ℝ))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 2
  have heven : Summable (fun n : ℕ => f (2 * n)) := by
    apply (summable_nat_add_iff 1).mp
    apply ((summable_nat_add_iff 1).mpr hseries).of_nonneg_of_le (fun n => hnonneg _)
    intro n
    change 1 / p (2 * (n + 1)) ≤ 2 * (1 / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    rw [mul_one_div]
    exact (div_le_div_iff₀ (hpos _) (by positivity)).mpr (by simpa using hpow (n + 1))
  have hodd : Summable (fun n : ℕ => f (2 * n + 1)) :=
    heven.of_nonneg_of_le (fun n => hnonneg _) (fun n =>
      one_div_le_one_div_of_le (hpos _) (hmono (Nat.le_succ (2 * n))))
  have htail : Summable f := Summable.even_add_odd heven hodd
  apply (summable_nat_add_iff N).mp
  simpa only [f, p, add_comm N] using htail

lemma OMA.dec_one : {n | primeGap n > primeGap (n + 1)}.Infinite := by
  by_contra hf
  obtain ⟨N, hN⟩ := (Set.not_infinite.mp hf).bddAbove
  have hg : Monotone fun n => primeGap (N + 1 + n) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [← add_assoc]
    by_contra! h
    have hab : N + 1 + n ≤ N := hN h
    omega
  have hs := OMA.dec_summable_of_monotone hg
  let idx (p : Nat.Primes) := Nat.count Nat.Prime p
  have hi : Function.Injective idx := by
    intro p q hpq
    exact Subtype.ext (Nat.count_injective p.prop q.prop hpq)
  have hs' := hs.comp_injective hi
  have heq : ((fun n : ℕ => 1 / (Nat.nth Nat.Prime n : ℝ)) ∘ idx) =
      (fun p : Nat.Primes => (1 / p : ℝ)) := by
    funext p
    change 1 / (Nat.nth Nat.Prime (Nat.count Nat.Prime (p : ℕ)) : ℝ) = 1 / (p : ℝ)
    rw [Nat.nth_count p.prop]
  exact Nat.Primes.not_summable_one_div (heq ▸ hs')

/-- Maynard's prime-rich tuple theorem for admissible affine forms with a common slope. -/
lemma OMA.dec_maynard (r : ℕ) :
    ∃ k : ℕ, ∀ (H : Finset ℕ) (M b : ℕ), k ≤ H.card → 0 < M →
      (∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a) →
      ∀ N : ℕ, ∃ x, N < x ∧ r ≤ (H.filter fun a => (M * x + b + a).Prime).card := by
  sorry

lemma OMA.dec_core (m : ℕ) :
    {n | ∀ i ∈ Finset.range m, primeGap (n + i) > primeGap (n + i + 1)}.Infinite := by
  obtain ⟨k, hk⟩ := OMA.dec_maynard (m + 2)
  obtain ⟨w, H, hcard, hH, hgap⟩ := OMA.exists_dec_offsets k
  obtain ⟨M, b, hM, hcover, hcop⟩ := OMA.dec_cover (fun a ha => (hH a ha).1)
  have hadm := OMA.dec_admissible hcard (fun a ha => (hH a ha).2) hcop
  apply Set.infinite_of_forall_exists_gt
  intro N
  let pN := Nat.nth Nat.Prime N
  obtain ⟨x, hx, hsize⟩ := hk H M b hcard.ge hM hadm (max M pN)
  let y := M * x + b
  have hxy : x ≤ y := by
    calc
      x = 1 * x := (Nat.one_mul x).symm
      _ ≤ M * x := Nat.mul_le_mul_right x hM
      _ ≤ y := Nat.le_add_right _ _
  have hwindow : m + 2 ≤ ((Finset.Icc y (y + w)).filter Nat.Prime).card := by
    refine hsize.trans (Finset.card_le_card_of_injOn (fun a => y + a) ?_ ?_)
    · intro a ha
      obtain ⟨haH, hap⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.le_add_right _ _, Nat.add_le_add_left (hH a haH).1 y⟩, hap⟩
    · intro a _ c _ hac
      exact Nat.add_left_cancel hac
  have hwindow_gap : ∀ {a c d}, y ≤ a → d ≤ y + w → a < c → c < d →
      a.Prime → c.Prime → d.Prime → d - c < c - a := by
    intro a c d hya hdw hac hcd hpa hpc hpd
    have hMx := (le_max_left M pN).trans_lt hx
    have help (z : ℕ) (hl : y ≤ z) (hu : z ≤ y + w) (hp : z.Prime) : z - y ∈ H := by
      exact hcover x hMx (z - y) (by omega) (by
        change (y + (z - y)).Prime
        rwa [Nat.add_sub_of_le hl])
    have hdec := hgap (a - y) (help a hya (by omega) hpa)
      (c - y) (help c (by omega) (by omega) hpc) (d - y) (help d (by omega) hdw hpd)
      (by omega) (by omega)
    omega
  obtain ⟨n, hn, hrun⟩ := OMA.dec_run_of_window hwindow hwindow_gap
  have hlt : pN < Nat.nth Nat.Prime n :=
    ((le_max_right M pN).trans_lt hx).trans_le (hxy.trans hn)
  exact ⟨n, hrun, (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp hlt⟩

theorem OMA.solution : type_of% @Erdos6.erdos_6.variants.decreasing := by
  intro m
  rcases m with _ | m
  · exact OMA.dec_zero
  rcases m with _ | m
  · simpa [Finset.range_one] using OMA.dec_one
  · exact OMA.dec_core (m + 2)
