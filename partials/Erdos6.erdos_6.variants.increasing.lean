import FormalConjectures.ErdosProblems.«6»

-- Problem: Erdős Problem 6 — increasing
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/6.lean:51 (declaration Erdos6.erdos_6.variants.increasing)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAE6

open Nat

lemma gap_pos (n : ℕ) : 0 < primeGap n := by
  unfold primeGap
  have h2 : n.nth Nat.Prime < (n + 1).nth Nat.Prime :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
  omega

lemma nth_add_const (M c : ℕ) (h : ∀ n, M ≤ n → primeGap n = c) (k : ℕ) :
    (M + k).nth Nat.Prime = M.nth Nat.Prime + k * c := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := h (M + k) (by omega)
    have h2 : (M + k).nth Nat.Prime < (M + k + 1).nth Nat.Prime :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self (M + k))
    unfold primeGap at h1
    rw [show M + (k + 1) = M + k + 1 by omega, Nat.succ_mul]
    omega

/-- Prime gaps cannot be eventually constant. -/
lemma not_eventually_const (M c : ℕ) (h : ∀ n, M ≤ n → primeGap n = c) : False := by
  have hc : 0 < c := by rw [← h M le_rfl]; exact gap_pos M
  set p := M.nth Nat.Prime with hp
  have hpp : p.Prime := Nat.prime_nth_prime M
  have key := nth_add_const M c h p
  have hq : (M + p).nth Nat.Prime = p * (1 + c) := by rw [key]; ring
  have hqp : (p * (1 + c)).Prime := hq ▸ Nat.prime_nth_prime (M + p)
  have := Nat.prime_mul_iff.mp hqp
  rcases this with ⟨_, h1⟩ | ⟨_, h1⟩
  · omega
  · exact hpp.ne_one h1

lemma case_one : {n | primeGap n < primeGap (n + 1)}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have anti : ∀ n, N < n → primeGap (n + 1) ≤ primeGap n := by
    intro n hn
    by_contra h
    have := hN (show n ∈ {n | primeGap n < primeGap (n + 1)} from by
      simp only [Set.mem_setOf_eq]; omega)
    omega
  have anti' : ∀ a b, N < a → a ≤ b → primeGap b ≤ primeGap a := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hb ih => exact (anti b (by omega)).trans ih
  have hex : ∃ v, ∃ n, N < n ∧ primeGap n = v := ⟨_, N + 1, by omega, rfl⟩
  classical
  obtain ⟨M, hM, hMv⟩ := Nat.find_spec hex
  apply not_eventually_const M (Nat.find hex)
  intro n hn
  apply le_antisymm
  · rw [← hMv]; exact anti' M n hM hn
  · exact Nat.find_min' hex ⟨n, by omega, rfl⟩

/-- A finite block of primes with no intervening primes has successive indices. -/
lemma prime_indices_of_block (a : ℕ → ℕ) (k : ℕ)
    (hprime : ∀ i ≤ k, (a i).Prime) (hinc : ∀ i < k, a i < a (i + 1))
    (hclear : ∀ i < k, ∀ q, a i < q → q < a (i + 1) → ¬q.Prime) :
    ∃ n, ∀ i ≤ k, (n + i).nth Nat.Prime = a i := by
  let n := Nat.count Nat.Prime (a 0)
  refine ⟨n, ?_⟩
  intro i
  induction i with
  | zero => intro _; simpa [n] using Nat.nth_count (hprime 0 (Nat.zero_le k))
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    let q := (n + i + 1).nth Nat.Prime
    have hlow : a i < q := by
      rw [← hprev]
      exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self _)
    have hhigh : q ≤ a (i + 1) := by
      by_contra! h
      have hle := Nat.le_nth_of_lt_nth_succ h (hprime (i + 1) hi)
      rw [hprev] at hle
      exact (not_le_of_gt (hinc i (by omega))) hle
    change q = a (i + 1)
    by_contra h
    exact hclear i (by omega) q hlow (by omega) (Nat.prime_nth_prime _)

/-- Any increasing subsequence of the offsets has strictly increasing gaps. -/
lemma geometric_gap_lt {d i j l : ℕ} (hd : 0 < d) (hjl : j < l) :
    d * 3 ^ j - d * 3 ^ i < d * 3 ^ l - d * 3 ^ j := by
  have hpos : 0 < d * 3 ^ j := Nat.mul_pos hd (pow_pos (by decide) _)
  have hle : d * 3 ^ (j + 1) ≤ d * 3 ^ l :=
    Nat.mul_le_mul_left d (Nat.pow_le_pow_right (by decide) hjl)
  rw [pow_succ, ← Nat.mul_assoc] at hle
  omega

/-- A fixed residue class forces the offsets outside the tuple to be composite. -/
lemma isolate_shifts {k B : ℕ} (h : Fin k → ℕ) (hB : ∀ i, h i ≤ B) :
    ∃ A b : ℕ, 0 < A ∧
      (∀ p : ℕ, p.Prime → p ∣ A → ∀ i, ¬p ∣ b + h i) ∧
      ∀ x, A < x → x ≡ b [MOD A] →
        ∀ u ≤ B, (x + u).Prime → u ∈ Set.range h := by
  classical
  let S := (Finset.range (B + 1)).filter (fun u => u ∉ Set.range h)
  let q (u : ℕ) := (B + u).nth Nat.Prime
  have hq (u : ℕ) : (q u).Prime := Nat.prime_nth_prime _
  have hqB (u : ℕ) : B < q u := by
    have := Nat.add_two_le_nth_prime (B + u)
    dsimp [q]
    omega
  have qmono : StrictMono q := by
    intro i j hij
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega : B + i < B + j)
  have hcop : Set.Pairwise (↑S : Set ℕ) (fun i j => (q i).Coprime (q j)) := by
    intro i _ j _ hij
    exact (Nat.coprime_primes (hq i) (hq j)).mpr (qmono.injective.ne hij)
  obtain ⟨b, hb⟩ := Nat.chineseRemainderOfFinset (fun u => q u - u) q S
    (fun u _ => (hq u).ne_zero) hcop
  let A := S.prod q
  have hA : 0 < A := Finset.prod_pos fun u _ => (hq u).pos
  have hbu (u : ℕ) (hu : u ∈ S) : b + u ≡ 0 [MOD q u] := by
    have huB : u ≤ B := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
      omega
    have hmod := (hb u hu).add_right u
    rw [Nat.sub_add_cancel (huB.trans (hqB u).le)] at hmod
    exact hmod.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
  refine ⟨A, b, hA, ?_, ?_⟩
  · intro p hp hpA i hpi
    obtain ⟨u, hu, hpu⟩ := ((_root_.Nat.prime_iff.mp hp).dvd_finsetProd_iff q).mp hpA
    have hpeq := (Nat.prime_dvd_prime_iff_eq hp (hq u)).mp hpu
    rw [hpeq] at hpi
    have heq := Nat.ModEq.add_left_cancel' b
      ((hbu u hu).trans (Nat.modEq_zero_iff_dvd.mpr hpi).symm)
    have huB : u ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hu).1)
    have huhi := heq.eq_of_lt_of_lt (huB.trans_lt (hqB u)) ((hB i).trans_lt (hqB u))
    exact (Finset.mem_filter.mp hu).2 ⟨i, huhi.symm⟩
  · intro x hx hxb u hu hp
    by_contra hu'
    have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hu'⟩
    have hqA : q u ∣ A := Finset.dvd_prod_of_mem q huS
    have hxu := ((hxb.of_dvd hqA).add_right u).trans (hbu u huS)
    have heq := (Nat.prime_dvd_prime_iff_eq (hq u) hp).mp (Nat.modEq_zero_iff_dvd.mp hxu)
    have hqA' := Nat.le_of_dvd hA hqA
    omega

def geometricShifts (k : ℕ) (i : Fin k) : ℕ := k.factorial * 3 ^ i.val

lemma geometricShifts_strictMono (k : ℕ) : StrictMono (geometricShifts k) := by
  intro i j hij
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by decide) hij) (Nat.factorial_pos k)

lemma geometricShifts_admissible (k : ℕ) :
    ∀ p : ℕ, p.Prime → ∃ b : ℕ, ∀ i, ¬p ∣ b + geometricShifts k i := by
  intro p hp
  by_cases hpk : p ≤ k
  · have hfac := Nat.dvd_factorial hp.pos hpk
    refine ⟨1, fun i hi => ?_⟩
    have hs : p ∣ geometricShifts k i := dvd_mul_of_dvd_left hfac _
    exact hp.not_dvd_one ((Nat.dvd_add_iff_left hs).mpr hi)
  · let : NeZero p := ⟨hp.ne_zero⟩
    let f (i : Fin k) : ZMod p := -(geometricShifts k i : ZMod p)
    have hns : ¬Function.Surjective f := by
      intro hf
      have hc := Fintype.card_le_of_surjective f hf
      simp only [ZMod.card, Fintype.card_fin] at hc
      omega
    change ¬∀ a, ∃ i, f i = a at hns
    push Not at hns
    obtain ⟨a, ha⟩ := hns
    refine ⟨a.val, fun i hi => ha i ?_⟩
    have hz := (ZMod.natCast_eq_zero_iff _ _).2 hi
    rw [Nat.cast_add, ZMod.natCast_zmod_val] at hz
    exact (eq_neg_of_add_eq_zero_left hz).symm

/-- Select the first primes in the isolated tuple and convert them to prime indices. -/
lemma gaps_of_isolated_shifts {k m x B : ℕ}
    (hB : ∀ i, geometricShifts k i ≤ B)
    (hcover : ∀ u ≤ B, (x + u).Prime → u ∈ Set.range (geometricShifts k))
    (hcount : m + 2 ≤ (Finset.univ.filter (fun i : Fin k =>
      (x + geometricShifts k i).Prime)).card) :
    ∃ n, x ≤ n.nth Nat.Prime ∧
      ∀ i ∈ Finset.range m, primeGap (n + i) < primeGap (n + i + 1) := by
  let S := Finset.univ.filter (fun i : Fin k => (x + geometricShifts k i).Prime)
  have hS : m + 2 ≤ S.card := hcount
  let e := S.orderEmbOfFin (k := S.card) rfl
  let f (i : Fin S.card) := x + geometricShifts k (e i)
  have hf : StrictMono f := by
    intro i j hij
    exact Nat.add_lt_add_left (geometricShifts_strictMono k (e.strictMono hij)) x
  have hvals (i : Fin S.card) : (f i).Prime :=
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl i)).2
  have hupper (i : Fin S.card) : f i ≤ x + B := Nat.add_le_add_left (hB (e i)) x
  let a (i : ℕ) := if hi : i < S.card then f ⟨i, hi⟩ else 0
  have ha (i : ℕ) (hi : i < S.card) : a i = f ⟨i, hi⟩ := dif_pos hi
  have aclear (i : ℕ) (hi : i < m + 1) (q : ℕ)
      (hqlo : a i < q) (hqhi : q < a (i + 1)) : ¬q.Prime := by
    intro hq
    have hi₁ : i < S.card := by omega
    have hi₂ : i + 1 < S.card := by omega
    rw [ha i hi₁] at hqlo
    rw [ha (i + 1) hi₂] at hqhi
    have hxq : x ≤ q := le_trans (Nat.le_add_right x _) hqlo.le
    have hqB := hupper ⟨i + 1, hi₂⟩
    obtain ⟨j, hj⟩ := hcover (q - x) (by omega)
      (by rwa [Nat.add_sub_of_le hxq])
    have hjeq : x + geometricShifts k j = q := by omega
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjeq ▸ hq⟩
    have hjR : j ∈ Set.range e := by
      rw [show Set.range e = (↑S : Set (Fin k)) from S.range_orderEmbOfFin rfl]
      exact hjS
    obtain ⟨l, hl⟩ := hjR
    have hfl : f l = q := by simpa only [f, hl] using hjeq
    have hlo := hf.lt_iff_lt.mp (hfl ▸ hqlo : f ⟨i, hi₁⟩ < f l)
    have hhi := hf.lt_iff_lt.mp (hfl ▸ hqhi : f l < f ⟨i + 1, hi₂⟩)
    change i < l.val at hlo
    change l.val < i + 1 at hhi
    omega
  obtain ⟨n, hn⟩ := prime_indices_of_block a (m + 1)
    (fun i hi => by rw [ha i (by omega)]; exact hvals _)
    (fun i hi => by
      rw [ha i (by omega), ha (i + 1) (by omega)]
      exact hf (Nat.lt_succ_self i))
    aclear
  refine ⟨n, ?_, ?_⟩
  · have hzero := hn 0 (Nat.zero_le _)
    rw [Nat.add_zero] at hzero
    rw [hzero, ha 0 (by omega)]
    exact Nat.le_add_right x _
  · intro i hi
    have him := Finset.mem_range.mp hi
    rw [primeGap, primeGap, show n + i + 1 = n + (i + 1) by omega,
      show n + (i + 1) + 1 = n + (i + 2) by omega,
      hn i (by omega), hn (i + 1) (by omega), hn (i + 2) (by omega),
      ha i (by omega), ha (i + 1) (by omega), ha (i + 2) (by omega)]
    simp only [f, Nat.add_sub_add_left, geometricShifts]
    exact geometric_gap_lt (Nat.factorial_pos k)
      (e.strictMono (show (⟨i + 1, _⟩ : Fin S.card) < ⟨i + 2, _⟩ from
        Nat.lt_succ_self (i + 1)))

/-- The fixed-progression form of Maynard's theorem for admissible translates. -/
def MaynardInProgressions (r : ℕ) : Prop :=
  ∃ k : ℕ, ∀ h : Fin k → ℕ, StrictMono h →
    (∀ p : ℕ, p.Prime → ∃ a : ℕ, ∀ i, ¬p ∣ a + h i) →
    ∀ A b : ℕ, 0 < A →
      (∀ p : ℕ, p.Prime → p ∣ A → ∀ i, ¬p ∣ b + h i) →
      ∀ X : ℕ, ∃ x > X, x ≡ b [MOD A] ∧
        r ≤ (Finset.univ.filter (fun i : Fin k => (x + h i).Prime)).card

/-- The common-slope specialization of Maynard's admissible affine forms theorem. -/
def MaynardCommonSlope (r : ℕ) : Prop :=
  ∃ k : ℕ, ∀ (A : ℕ) (c : Fin k → ℕ), 0 < A → StrictMono c →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ A * t + c i) →
      ∀ X : ℕ, ∃ t > X,
        r ≤ (Finset.univ.filter (fun i : Fin k => (A * t + c i).Prime)).card

/-- Weak form of the common-slope statement: a single common value of t. -/
def MaynardOnce (r : ℕ) : Prop :=
  ∃ k : ℕ, ∀ (A : ℕ) (c : Fin k → ℕ), 0 < A → StrictMono c →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ A * t + c i) →
      ∃ t : ℕ, r ≤ (Finset.univ.filter (fun i : Fin k => (A * t + c i).Prime)).card

/-- Shifting the constants by a multiple of the slope keeps admissibility, so one value of t
for every admissible family already gives arbitrarily large values. -/
lemma maynardCommonSlope_of_once {r : ℕ} (hm : MaynardOnce r) : MaynardCommonSlope r := by
  obtain ⟨k, hk⟩ := hm
  refine ⟨k, ?_⟩
  intro A c hA hc hadm X
  let c' (i : Fin k) := A * (X + 1) + c i
  have hc' : StrictMono c' := fun _ _ hij => Nat.add_lt_add_left (hc hij) _
  have hadm' : ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ A * t + c' i := by
    intro p hp
    obtain ⟨t, ht⟩ := hadm p hp
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.pos).symm⟩
    refine ⟨t + q * (X + 1), fun i hi => ht i ?_⟩
    have e : A * (t + q * (X + 1)) + c' i = (A * t + c i) + (q + 1) * (A * (X + 1)) := by
      simp only [c']; ring
    rw [e] at hi
    exact (Nat.dvd_add_iff_left (dvd_mul_right (q + 1) _)).mpr hi
  obtain ⟨t, ht⟩ := hk A c' hA hc' hadm'
  refine ⟨t + (X + 1), by omega, ?_⟩
  have e : ∀ i, A * (t + (X + 1)) + c i = A * t + c' i := fun i => by
    simp only [c']; ring
  simpa only [e] using ht

lemma maynardInProgressions_of_commonSlope {r : ℕ} (hm : MaynardCommonSlope r) :
    MaynardInProgressions r := by
  obtain ⟨k, hk⟩ := hm
  refine ⟨k, ?_⟩
  intro h hmono hadm A b hA hb X
  let c (i : Fin k) := b + h i
  have hc : StrictMono c := fun _ _ hij => Nat.add_lt_add_left (hmono hij) b
  have hcAdm (p : ℕ) (hp : p.Prime) : ∃ t : ℕ, ∀ i, ¬p ∣ A * t + c i := by
    by_cases hpA : p ∣ A
    · exact ⟨0, by simpa only [Nat.mul_zero, Nat.zero_add, c] using hb p hp hpA⟩
    · obtain ⟨a, ha⟩ := hadm p hp
      let : Fact p.Prime := ⟨hp⟩
      let : NeZero p := ⟨hp.ne_zero⟩
      have hA0 : (A : ZMod p) ≠ 0 := fun hz => hpA ((ZMod.natCast_eq_zero_iff _ _).mp hz)
      let y : ZMod p := ((a : ZMod p) - b) / A
      have hy : (A : ZMod p) * y + b = a := by
        rw [mul_comm, show y * (A : ZMod p) = (a : ZMod p) - b from div_mul_cancel₀ _ hA0]
        exact sub_add_cancel _ _
      refine ⟨y.val, fun i hi => ha i ((ZMod.natCast_eq_zero_iff _ _).mp ?_)⟩
      have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hi
      simpa only [c, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, ← add_assoc, hy] using hz
  obtain ⟨t, ht, htcount⟩ := hk A c hA hc hcAdm X
  have hmul : t ≤ A * t := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right t hA
  refine ⟨A * t + b, by omega, Nat.ModEq.modulus_mul_add, ?_⟩
  simpa only [c, Nat.add_assoc] using htcount

lemma increasing_of_maynard (m : ℕ) (hmaynard : MaynardInProgressions (m + 2)) :
    {n | ∀ i ∈ Finset.range m, primeGap (n + i) < primeGap (n + i + 1)}.Infinite := by
  obtain ⟨k, hk⟩ := hmaynard
  let B := k.factorial * 3 ^ k
  have hB (i : Fin k) : geometricShifts k i ≤ B :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) i.isLt.le)
  obtain ⟨A, b, hA, hb, hcover⟩ := isolate_shifts (geometricShifts k) hB
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨x, hx, hxb, hcount⟩ := hk (geometricShifts k) (geometricShifts_strictMono k)
    (geometricShifts_admissible k) A b hA hb (max A (N.nth Nat.Prime))
  obtain ⟨n, hn, hnGaps⟩ := gaps_of_isolated_shifts hB
    (hcover x ((le_max_left _ _).trans_lt hx) hxb) hcount
  have hnGreater : N < n := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).lt_iff_lt.mp
    (((le_max_right _ _).trans_lt hx).trans_le hn)
  exact ⟨n, hnGaps, hnGreater⟩

end OMAE6

theorem OMA.solution : type_of% @Erdos6.erdos_6.variants.increasing := by
  intro m
  rcases m with _ | _ | m
  · simp [Set.infinite_univ]
  · simpa using OMAE6.case_one
  · have hmaynard : OMAE6.MaynardOnce (m + 2 + 2) := by
      sorry
    exact OMAE6.increasing_of_maynard (m + 2)
      (OMAE6.maynardInProgressions_of_commonSlope
        (OMAE6.maynardCommonSlope_of_once hmaynard))
