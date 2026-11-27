import FormalConjectures.ErdosProblems.«687»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Elementary covering bounds for the Erdős 687 asymptotic problem. -/

-- Problem: Erdős Problem 687 — i (it asks for a value)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/687.lean:164 (declaration Erdos687.erdos_687.parts.i; placeholder Erdos687.erdos_687.parts.i.answer := sorry)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Give the value explicitly as OMA.answer (same type as the placeholder; not built from Erdos687.…,
-- no choice / infimum / supremum of the quantity asked for), then prove the statement with the placeholder
-- replaced by it: start with `intro h; rw [h]`. No sorry, no axiom, no native_decide. A person checks the answer.

open scoped BigOperators Asymptotics
open Filter

namespace Erdos687Relay

private theorem Y_isGreatest (x : ℕ) :
    IsGreatest {y : ℕ | Green46.IsCoveredByResidues x y} (Erdos687.Y x) := by
  have hn : {y : ℕ | Green46.IsCoveredByResidues x y}.Nonempty :=
    ⟨0, show Green46.IsCoveredByResidues x 0 from ⟨fun _ => 0, by simp⟩⟩
  have hb : BddAbove {y : ℕ | Green46.IsCoveredByResidues x y} :=
    ⟨primorial x, fun _ hy => (Erdos687.lt_primorial_of_isCoveredByResidues hy).le⟩
  exact ⟨Nat.sSup_mem hn hb, fun _ hy => le_csSup hb hy⟩

private theorem covered_iff_le_Y {x y : ℕ} :
    Green46.IsCoveredByResidues x y ↔ y ≤ Erdos687.Y x := by
  refine ⟨fun hy => (Y_isGreatest x).2 (show y ∈ _ from hy), fun hy => ?_⟩
  obtain ⟨a, ha⟩ := (Y_isGreatest x).1
  exact ⟨a, fun m hm => ha m
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hy⟩)⟩

private theorem predecessor_le_Y (x : ℕ) : x - 1 ≤ Erdos687.Y x := by
  apply covered_iff_le_Y.mp
  refine ⟨fun p => p - 1, fun m hm => ?_⟩
  obtain ⟨hm, hmx⟩ := Finset.mem_Icc.mp hm
  let p := (m + 1).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hd : p ∣ m + 1 := Nat.minFac_dvd (m + 1)
  refine ⟨p, (Nat.le_of_dvd (by omega) hd).trans (by omega), hp, ?_⟩
  have hz : (m + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have hlt := Nat.mod_lt m hp.pos
  have hp2 := hp.two_le
  show m % p = (p - 1) % p
  rw [Nat.mod_eq_of_lt (by omega : p - 1 < p)]
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < p)] at hz
  by_contra h
  have : m % p + 1 < p := by omega
  rw [Nat.mod_eq_of_lt this] at hz
  omega

private theorem cover_with_reserve {x y : ℕ} (s t : Finset ℕ)
    (hs : ∀ p ∈ s, p ≤ x ∧ p.Prime) (ht : ∀ p ∈ t, p ≤ x ∧ p.Prime)
    (hst : Disjoint s t) (a : ℕ → ℕ)
    (hcard : ((Finset.Icc 1 y).filter
      (fun m => ∀ p ∈ s, ¬m ≡ a p [MOD p])).card ≤ t.card) :
    Green46.IsCoveredByResidues x y := by
  classical
  let u := (Finset.Icc 1 y).filter (fun m => ∀ p ∈ s, ¬m ≡ a p [MOD p])
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := u) (β := t) (by simpa using hcard)
  let b (p : ℕ) : ℕ := if h : ∃ m : u, (f m : ℕ) = p
    then ((Classical.choose h : u) : ℕ) else a p
  refine ⟨b, fun m hm => ?_⟩
  by_cases hmu : m ∈ u
  · let m' : u := ⟨m, hmu⟩
    let p := f m'
    have he : ∃ n : u, (f n : ℕ) = (p : ℕ) := ⟨m', rfl⟩
    have hchoose : Classical.choose he = m' :=
      f.injective (Subtype.ext (Classical.choose_spec he))
    refine ⟨p, (ht p p.property).1, (ht p p.property).2, ?_⟩
    simp only [b, dif_pos he, hchoose]
    exact Nat.ModEq.refl _
  · have hc : ∃ p ∈ s, m ≡ a p [MOD p] := by
      by_contra! hn
      exact hmu (Finset.mem_filter.mpr ⟨hm, hn⟩)
    obtain ⟨p, hp, hc⟩ := hc
    have he : ¬∃ m : u, (f m : ℕ) = p := by
      rintro ⟨n, hn⟩
      have hpt : p ∈ t := hn ▸ (f n).property
      exact Finset.disjoint_left.mp hst hp hpt
    exact ⟨p, (hs p hp).1, (hs p hp).2, by simpa only [b, dif_neg he] using hc⟩

private theorem sieve_one_modulus (u : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    ∃ a : ℕ, ((u.filter fun m => ¬m ≡ a [MOD p]).card : ℝ) ≤
      (1 - (p : ℝ)⁻¹) * u.card := by
  classical
  let f (r : ℕ) : ℝ := (u.filter fun m => m % p = r).card
  have hsum : (∑ r ∈ Finset.range p, f r) = u.card := by
    unfold f
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (s := u) (t := Finset.range p) (f := fun m => m % p)
      (fun m _ => Finset.mem_range.mpr (Nat.mod_lt m hp))).symm
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨r, hr, hrf⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hp))
    (f := fun _ => (u.card : ℝ) / p) (g := f) (by
      rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      rfl)
  refine ⟨r, ?_⟩
  have hcard := Finset.card_filter_add_card_filter_not (s := u) (fun m => m % p = r)
  have hcard' : f r + ((u.filter fun m => m % p ≠ r).card : ℝ) = u.card := by
    unfold f
    exact_mod_cast hcard
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_range.mp hr), sub_mul, one_mul,
    inv_mul_eq_div] using (show
      ((u.filter fun m => m % p ≠ r).card : ℝ) ≤ (u.card : ℝ) - u.card / p by linarith)

private theorem sieve_small_primes (s u : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∃ a : ℕ → ℕ, ((u.filter (fun m => ∀ p ∈ s, ¬m ≡ a p [MOD p])).card : ℝ) ≤
      (∏ p ∈ s, (1 - (p : ℝ)⁻¹)) * u.card := by
  classical
  induction s using Finset.induction_on generalizing u with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert p s hp ih =>
    have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
    obtain ⟨r, hr⟩ := sieve_one_modulus u hpp.pos
    let v := u.filter fun m => ¬m ≡ r [MOD p]
    obtain ⟨a, ha⟩ := ih v (fun q hq => hs q (Finset.mem_insert_of_mem hq))
    let b (q : ℕ) := if q = p then r else a q
    have he : (u.filter (fun m => ∀ q ∈ insert p s, ¬m ≡ b q [MOD q])) =
        v.filter (fun m => ∀ q ∈ s, ¬m ≡ a q [MOD q]) := by
      ext m
      simp only [Finset.mem_filter, Finset.forall_mem_insert, b, v, and_assoc]
      apply and_congr_right
      intro _
      exact and_congr_right fun _ => forall₂_congr fun q hq => by
        simp [show q ≠ p from fun h => hp (h ▸ hq)]
    refine ⟨b, ?_⟩
    have hnonneg : 0 ≤ ∏ q ∈ s, (1 - (q : ℝ)⁻¹) := by
      apply Finset.prod_nonneg
      intro q hq
      have hpq : (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (hs q (Finset.mem_insert_of_mem hq)).one_le
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hpq)
    rw [he, Finset.prod_insert hp]
    refine ha.trans ((mul_le_mul_of_nonneg_left hr hnonneg).trans_eq ?_)
    ring

private theorem smooth_eq_divisor_mul_square (z n : ℕ) (hn : 0 < n)
    (hz : ∀ p, p.Prime → p ∣ n → p ≤ z) :
    ∃ d k : ℕ, d ∣ primorial z ∧ n = d * k ^ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · exact ⟨1, 1, one_dvd _, by simp [hn1]⟩
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    change n = p * m at hm
    have hpm : p ∣ n := ⟨m, hm⟩
    have hm0 : 0 < m := by
      by_contra! h
      simp [show m = 0 by omega] at hm
      omega
    have hmn : m < n := by
      have := hp.two_le
      nlinarith
    obtain ⟨d, k, hd, hmk⟩ := ih m hmn hm0 fun q hq hqm =>
      hz q hq (hqm.trans (hm ▸ dvd_mul_left m p))
    by_cases hpd : p ∣ d
    · obtain ⟨e, he⟩ := hpd
      refine ⟨e, p * k, (show e ∣ d from he ▸ dvd_mul_left e p).trans hd, ?_⟩
      rw [hm, hmk, he]
      ring
    · refine ⟨p * d, k, ?_, by rw [hm, hmk, mul_assoc]⟩
      exact (hp.coprime_iff_not_dvd.mpr hpd).mul_dvd_of_dvd_of_dvd
        (hp.dvd_primorial_iff.mpr (hz p hp hpm)) hd

private theorem count_medium_survivors_sum (z t y : ℕ) :
    ((Finset.Icc 1 y).filter
      (fun m => ∀ p ∈ (Nat.primesLE t).filter (z < ·), ¬p ∣ m)).card ≤
      (primorial z + 1) * (y.sqrt + 1) +
        ∑ k ∈ Finset.Icc 1 (y / (t + 1)), Nat.primeCounting (y / k) := by
  classical
  let smooth := ((Finset.range (primorial z + 1)) ×ˢ (Finset.range (y.sqrt + 1))).image
    (fun q : ℕ × ℕ => q.1 * q.2 ^ 2)
  let multiples := (Finset.Icc 1 (y / (t + 1))).biUnion
    (fun k => (Nat.primesLE (y / k)).image (· * k))
  calc
    _ ≤ (smooth ∪ multiples).card := by
      apply Finset.card_le_card
      intro m hm
      obtain ⟨hm, hs⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm0, hmy⟩ := Finset.mem_Icc.mp hm
      by_cases h : ∀ p, p.Prime → p ∣ m → p ≤ z
      · obtain ⟨d, k, hd, he⟩ := smooth_eq_divisor_mul_square z m hm0 h
        have hd0 : 1 ≤ d := by by_contra! h; simp [show d = 0 by omega] at he; omega
        have hd' := Nat.le_of_dvd (primorial_pos z) hd
        have hk : k ≤ y.sqrt := Nat.le_sqrt'.mpr (by
          simpa using (Nat.mul_le_mul_right (k ^ 2) hd0).trans (he ▸ hmy))
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨(d, k), Finset.mem_product.mpr
            ⟨Finset.mem_range_succ_iff.mpr hd', Finset.mem_range_succ_iff.mpr hk⟩, he.symm⟩)
      · push Not at h
        obtain ⟨p, hp, hd, hzp⟩ := h
        have htp : t < p := by
          by_contra! ht
          exact hs p (Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨ht, hp⟩, hzp⟩) hd
        obtain ⟨k, rfl⟩ := hd
        have hk : 0 < k := by by_contra! h; simp [show k = 0 by omega] at hm0
        have hkp : k ≤ y / (t + 1) := by
          apply (Nat.le_div_iff_mul_le (Nat.succ_pos t)).mpr
          rw [Nat.mul_comm]
          exact (Nat.mul_le_mul_right _ htp).trans hmy
        have hpy : p ≤ y / k := (Nat.le_div_iff_mul_le hk).mpr hmy
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨k, Finset.mem_Icc.mpr ⟨hk, hkp⟩, Finset.mem_image.mpr
            ⟨p, Nat.mem_primesLE.mpr ⟨hpy, hp⟩, rfl⟩⟩)
    _ ≤ smooth.card + multiples.card := Finset.card_union_le _ _
    _ ≤ _ := by
      apply Nat.add_le_add
      · exact Finset.card_image_le.trans_eq (by simp)
      · apply Finset.card_biUnion_le.trans
        apply Finset.sum_le_sum
        intro k _
        exact Finset.card_image_le.trans_eq (Nat.primesLE_card_eq_primeCounting _)

private theorem count_medium_survivors (z t y : ℕ) :
    ((Finset.Icc 1 y).filter
      (fun m => ∀ p ∈ (Nat.primesLE t).filter (z < ·), ¬p ∣ m)).card ≤
      (primorial z + 1) * (y.sqrt + 1) + (Nat.primeCounting y) * (y / (t + 1) + 1) := by
  refine (count_medium_survivors_sum z t y).trans (Nat.add_le_add_left ?_ _)
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 (y / (t + 1)), Nat.primeCounting y :=
      Finset.sum_le_sum fun k _ => Nat.monotone_primeCounting (Nat.div_le_self y k)
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      change (Finset.Icc 1 (y / (t + 1))).card * Nat.primeCounting y ≤ _
      rw [Nat.mul_comm ((Finset.Icc 1 (y / (t + 1))).card)]
      apply Nat.mul_le_mul_left
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Nat.le_succ (y / (t + 1))

private theorem cover_of_medium_survivors {z t x y : ℕ} (hzt : z ≤ t) (htx : t ≤ x)
    (h : (∏ p ∈ Nat.primesLE z, (1 - (p : ℝ)⁻¹)) *
      ((Finset.Icc 1 y).filter
        (fun m => ∀ p ∈ (Nat.primesLE t).filter (z < ·), ¬p ∣ m)).card ≤
      ((Nat.primeCounting x - Nat.primeCounting t : ℕ) : ℝ)) :
    y ≤ Erdos687.Y x := by
  classical
  let s := Nat.primesLE z
  let r := (Nat.primesLE t).filter (z < ·)
  let u := (Finset.Icc 1 y).filter fun m => ∀ p ∈ r, ¬p ∣ m
  let v := (Nat.primesLE x) \ Nat.primesLE t
  obtain ⟨a, ha⟩ := sieve_small_primes s u (fun p hp => (Nat.mem_primesLE.mp hp).2)
  let b (p : ℕ) := if p ≤ z then a p else 0
  have he : ((Finset.Icc 1 y).filter
      (fun m => ∀ p ∈ Nat.primesLE t, ¬m ≡ b p [MOD p])) =
      u.filter (fun m => ∀ p ∈ s, ¬m ≡ a p [MOD p]) := by
    ext m
    simp only [u, Finset.mem_filter, and_assoc]
    apply and_congr_right
    intro _
    constructor
    · intro hm
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · obtain ⟨hp', hz⟩ := Finset.mem_filter.mp hp
        simpa [b, if_neg (not_le_of_gt hz), Nat.modEq_zero_iff_dvd] using hm p hp'
      · obtain ⟨hz, hpp⟩ := Nat.mem_primesLE.mp hp
        simpa [b, if_pos hz] using hm p (Nat.mem_primesLE.mpr ⟨hz.trans hzt, hpp⟩)
    · rintro ⟨hm, hm'⟩ p hp
      have hpp := (Nat.mem_primesLE.mp hp).2
      by_cases hz : p ≤ z
      · simpa [b, if_pos hz] using hm' p (Nat.mem_primesLE.mpr ⟨hz, hpp⟩)
      · simpa [b, if_neg hz, Nat.modEq_zero_iff_dvd] using
          hm p (Finset.mem_filter.mpr ⟨hp, lt_of_not_ge hz⟩)
  have hv : v.card = Nat.primeCounting x - Nat.primeCounting t := by
    rw [Finset.card_sdiff_of_subset, Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_card_eq_primeCounting]
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans htx, (Nat.mem_primesLE.mp hp).2⟩
  apply covered_iff_le_Y.mp
  apply cover_with_reserve (Nat.primesLE t) v
    (fun p hp => ⟨(Nat.mem_primesLE.mp hp).1.trans htx, (Nat.mem_primesLE.mp hp).2⟩)
    (fun p hp => ⟨(Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).1,
      (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2⟩)
    (Finset.disjoint_left.mpr fun p hp hp' => (Finset.mem_sdiff.mp hp').2 hp) b
  rw [he, hv]
  exact_mod_cast ha.trans h

private theorem cover_of_sieve_bound {z t x y : ℕ} (hzt : z ≤ t) (htx : t ≤ x)
    (h : (∏ p ∈ Nat.primesLE z, (1 - (p : ℝ)⁻¹)) *
      (((primorial z + 1) * (y.sqrt + 1) +
        Nat.primeCounting y * (y / (t + 1) + 1) : ℕ) : ℝ) ≤
      ((Nat.primeCounting x - Nat.primeCounting t : ℕ) : ℝ)) :
    y ≤ Erdos687.Y x := by
  apply cover_of_medium_survivors hzt htx
  refine (mul_le_mul_of_nonneg_left ?_ ?_).trans h
  · exact_mod_cast count_medium_survivors z t y
  · refine Finset.prod_nonneg fun p hp => sub_nonneg.mpr (inv_le_one_of_one_le₀ ?_)
    exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le

private theorem small_prime_product (ε : ℝ) (hε : 0 < ε) :
    ∃ z : ℕ, (∏ p ∈ Nat.primesLE z, (1 - (p : ℝ)⁻¹)) ≤ ε := by
  classical
  let f : ℕ → ℝ := Set.indicator {p | Nat.Prime p} (fun n : ℕ => (1 : ℝ) / n)
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    exact Set.indicator_nonneg (fun p _ => by positivity) n
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp
    not_summable_one_div_on_primes
  obtain ⟨z, hz⟩ := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).eventually
    (gt_mem_nhds hε)).exists
  have he : (∑ p ∈ Finset.range z, f p) =
      ∑ p ∈ Nat.primesLE (z - 1), (p : ℝ)⁻¹ := by
    rw [← Nat.primesBelow_eq_primesLE_sub_one, Nat.primesBelow, Finset.sum_filter]
    simp [f, Set.indicator_apply, one_div]
  refine ⟨z - 1, ?_⟩
  calc
    _ ≤ ∏ p ∈ Nat.primesLE (z - 1), Real.exp (-(p : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp' : (1 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
        exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp')
      · intro p _
        exact Real.one_sub_le_exp_neg _
    _ = Real.exp (-(∑ p ∈ Finset.range z, f p)) := by
      simp only [← Real.exp_sum, Finset.sum_neg_distrib, he]
    _ ≤ ε := hz.le

private theorem primeCounting_eventually_upper :
    ∀ᶠ n : ℕ in atTop, (Nat.primeCounting n : ℝ) ≤ 4 * n / Real.log n := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  have h4 : Real.log 4 + 1 ≤ 4 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  filter_upwards [h] with n hn
  simp only [Nat.floor_natCast] at hn
  have hl := Real.log_natCast_nonneg n
  exact hn.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg n)) hl)

private theorem primeCounting_eventually_lower :
    ∀ᶠ n : ℕ in atTop, (1 / 4 : ℝ) * n / Real.log n ≤ Nat.primeCounting n := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 8 by norm_num)
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    norm_num
  filter_upwards [ht.eventually h, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, id_eq,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1),
    abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ (n : ℝ) + 1))] at hn
  have hmul := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) n)
  refine (div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg n)).trans (Chebyshev.pi_ge n)
  linarith

private theorem primeCounting_eventually_reserve :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / Real.log n ≤
      ((Nat.primeCounting (64 * n) - Nat.primeCounting n : ℕ) : ℝ) := by
  have ht : Tendsto (fun n : ℕ => 64 * n) atTop atTop :=
    tendsto_atTop.mpr fun k => (eventually_ge_atTop k).mono fun n hn =>
      hn.trans (Nat.le_mul_of_pos_left n (by decide))
  filter_upwards [primeCounting_eventually_upper,
    ht.eventually primeCounting_eventually_lower, eventually_ge_atTop (64 : ℕ)] with n hU hL hn
  have hn' : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnlog : 0 < Real.log n := Real.log_pos (by linarith)
  have h64log : Real.log ((64 : ℝ) * n) ≤ 2 * Real.log n := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    linarith [Real.log_le_log (show (0 : ℝ) < 64 by norm_num) hn']
  have hlower : 8 * ((n : ℝ) / Real.log n) ≤ Nat.primeCounting (64 * n) := by
    apply le_trans _ hL
    push_cast
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hnlog (Real.log_pos (by linarith : 1 < (64 : ℝ) * n))).mpr
    have hm := mul_le_mul_of_nonneg_left h64log (show 0 ≤ 8 * (n : ℝ) by positivity)
    linarith only [hm]
  rw [Nat.cast_sub (Nat.monotone_primeCounting (Nat.le_mul_of_pos_left n (by decide)))]
  rw [mul_div_assoc] at hU
  linarith only [hlower, hU, show 0 ≤ (n : ℝ) / Real.log n by positivity]

private theorem eventually_smooth_bound (z c : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (((primorial z + 1) * ((c * n).sqrt + 1) : ℕ) : ℝ) ≤ n / Real.log n := by
  let D : ℝ := (primorial z + 1) * (Real.sqrt c + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have h := ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound (inv_pos.mpr hD)))
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hl : 0 < Real.log n := Real.log_pos (by linarith)
  have hsq : ((c * n).sqrt : ℝ) ≤ Real.sqrt ((c : ℝ) * n) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' (c * n)
  have hsn : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_pos hl,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hlog : D * Real.log n ≤ Real.sqrt (n : ℝ) := by
    calc
      _ ≤ D * (D⁻¹ * Real.sqrt (n : ℝ)) := mul_le_mul_of_nonneg_left hn hD.le
      _ = _ := by field_simp
  have hupper : (((primorial z + 1) * ((c * n).sqrt + 1) : ℕ) : ℝ) ≤
      D * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) c)] at hsq
    push_cast
    calc
      _ ≤ ((primorial z : ℝ) + 1) * (Real.sqrt c * Real.sqrt (n : ℝ) + Real.sqrt n) :=
        mul_le_mul_of_nonneg_left (add_le_add hsq hsn) (by positivity)
      _ = _ := by dsimp [D]; ring
  refine hupper.trans ((le_div_iff₀ hl).mpr ?_)
  calc
    D * Real.sqrt (n : ℝ) * Real.log n = (D * Real.log n) * Real.sqrt (n : ℝ) := by ring
    _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by gcongr
    _ = n := Real.mul_self_sqrt (Nat.cast_nonneg n)

private theorem eventually_mul_le_Y_mul (c : ℕ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * n ≤ Erdos687.Y (64 * n) := by
  let B : ℝ := 1 + 4 * (c : ℝ) * (c + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨z, hz⟩ := small_prime_product B⁻¹ (inv_pos.mpr hB)
  have hmul (k : ℕ) (hk : 0 < k) : Tendsto (fun n : ℕ => k * n) atTop atTop := by
    refine tendsto_atTop.mpr fun N => (eventually_ge_atTop N).mono fun n hn => ?_
    exact hn.trans (Nat.le_mul_of_pos_left n hk)
  filter_upwards [primeCounting_eventually_reserve,
    (hmul c hc).eventually primeCounting_eventually_upper, eventually_smooth_bound z c,
    eventually_ge_atTop (2 : ℕ), eventually_ge_atTop z] with n hreserve hcn hs hn2 hzn
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hl : 0 < Real.log n := Real.log_pos (by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hnt64 : n ≤ 64 * n := Nat.le_mul_of_pos_left _ (by decide)
  have hcnt : (Nat.primeCounting (c * n) : ℝ) ≤ 4 * c * ((n : ℝ) / Real.log n) := by
    have hlog : Real.log n ≤ Real.log ((c * n : ℕ) : ℝ) :=
      Real.log_le_log hn0 (by exact_mod_cast Nat.le_mul_of_pos_left n hc)
    refine hcn.trans ?_
    push_cast at hlog ⊢
    rw [← mul_div_assoc, ← mul_assoc]
    exact div_le_div_of_nonneg_left (by positivity) hl hlog
  have hq : ((c * n / (n + 1) + 1 : ℕ) : ℝ) ≤ (c : ℝ) + 1 := by
    have hk : c * n / (n + 1) < c + 1 := by
      apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr
      nlinarith
    exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt_succ hk) 1
  have hsurv : (((primorial z + 1) * ((c * n).sqrt + 1) +
      Nat.primeCounting (c * n) * (c * n / (n + 1) + 1) : ℕ) : ℝ) ≤
      B * ((n : ℝ) / Real.log n) := by
    push_cast at hs ⊢
    have hm := mul_le_mul hcnt hq (by positivity) (by positivity)
    push_cast at hm
    exact (add_le_add hs hm).trans_eq (by dsimp [B]; ring)
  apply cover_of_sieve_bound hzn hnt64
  refine le_trans (mul_le_mul hz hsurv (by positivity) (inv_nonneg.mpr hB.le)) ?_
  calc
    B⁻¹ * (B * ((n : ℝ) / Real.log n)) = (n : ℝ) / Real.log n := by
      rw [← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]
    _ ≤ _ := hreserve

private theorem Y_monotone : Monotone Erdos687.Y := by
  intro x x' hx
  apply covered_iff_le_Y.mp
  obtain ⟨a, ha⟩ := (Y_isGreatest x).1
  refine ⟨a, fun m hm => ?_⟩
  obtain ⟨p, hp, hpp, hmp⟩ := ha m hm
  exact ⟨p, hp.trans hx, hpp, hmp⟩

/-- Any fixed multiple of the prime cutoff is eventually coverable. -/
theorem eventually_mul_le_Y (c : ℕ) :
    ∀ᶠ x : ℕ in atTop, c * x ≤ Erdos687.Y x := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_mul_le_Y_mul (c * 128) (by positivity))
  filter_upwards [eventually_ge_atTop (64 * max N 1)] with x hx
  let n := x / 64
  have hn : max N 1 ≤ n := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 64)).mpr
    simpa only [Nat.mul_comm] using hx
  have hnx : 64 * n ≤ x := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self x 64
  have hxn : x ≤ 128 * n := by
    have hr := Nat.mod_lt x (by decide : 0 < 64)
    have he := Nat.mod_add_div x 64
    have h1 : 1 ≤ n := (le_max_right _ _).trans hn
    change x % 64 + 64 * n = x at he
    omega
  calc
    c * x ≤ c * (128 * n) := Nat.mul_le_mul_left _ hxn
    _ = (c * 128) * n := (Nat.mul_assoc _ _ _).symm
    _ ≤ Erdos687.Y (64 * n) := hN n ((le_max_left _ _).trans hn)
    _ ≤ Erdos687.Y x := Y_monotone hnx

/-- Westzynthius's superlinear lower bound for this covering function. -/
theorem tendsto_Y_div_atTop :
    Tendsto (fun x : ℕ => (Erdos687.Y x : ℝ) / x) atTop atTop := by
  refine tendsto_atTop.mpr fun C => ?_
  obtain ⟨c, hc⟩ := exists_nat_ge C
  filter_upwards [eventually_mul_le_Y c, eventually_ge_atTop (1 : ℕ)] with x hx hx1
  have hx' : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  exact hc.trans ((le_div_iff₀ hx').mpr (by exact_mod_cast hx))

private theorem sum_inv_divisors_eq_div (n : ℕ) :
    (∑ d ∈ n.divisors, (d : ℝ)⁻¹) = (∑ d ∈ n.divisors, (d : ℝ)) / n := by
  rw [← Nat.sum_div_divisors n (fun d : ℕ => (d : ℝ)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdn, hn⟩ := Nat.mem_divisors.mp hd
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by rintro rfl; simp_all)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Nat.cast_div hdn hd0]
  field_simp [hn0, hd0]

private theorem sum_inv_divisors_prime_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    (∑ d ∈ (∏ p ∈ s, p).divisors, (d : ℝ)⁻¹) =
      ∏ p ∈ s, (1 + (p : ℝ)⁻¹) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hpp := hs p (Finset.mem_insert_self p s)
    have hsp q (hq : q ∈ s) := hs q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ s, q) := by
      apply hpp.coprime_iff_not_dvd.mpr
      rw [hpp.prime.dvd_finsetProd_iff]
      rintro ⟨q, hq, hd⟩
      exact hp (((Nat.prime_dvd_prime_iff_eq hpp (hsp q hq)).mp hd) ▸ hq)
    rw [Finset.prod_insert hp, Finset.prod_insert hp, ← ih hsp,
      sum_inv_divisors_eq_div (p * ∏ q ∈ s, q), ← Nat.cast_sum, hc.sum_divisors_mul,
      Nat.cast_mul, Nat.cast_mul, ← div_mul_div_comm, Nat.cast_sum, Nat.cast_sum,
      ← sum_inv_divisors_eq_div, ← sum_inv_divisors_eq_div]
    simp [hpp.sum_divisors, add_comm]

private theorem sum_inv_sq_le_two (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ((k : ℝ) ^ 2)⁻¹) ≤ 2 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_Ico_add'
    (fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) 0 n (c := 1), Nat.Ico_zero_eq_range]
  have hterm (k : ℕ) :
      (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
        2 * (1 / ((k : ℝ) + 1) - 1 / ((k + 1 : ℕ) + 1 : ℝ)) := by
    push_cast
    have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (k : ℝ) + 1 + 1 := by positivity
    rw [← one_div]
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        2 * (1 / ((k : ℝ) + 1) - 1 / ((k + 1 : ℕ) + 1 : ℝ)) :=
      Finset.sum_le_sum fun k _ => hterm k
    _ = 2 * (1 - 1 / ((n : ℝ) + 1)) := by
      let F (k : ℕ) := 1 / ((k : ℝ) + 1)
      have htel : (∑ i ∈ Finset.range n, (F i - F (i + 1))) = F 0 - F n := by
        simp_rw [show ∀ i, F i - F (i + 1) = -(F (i + 1) - F i) from fun i => by ring,
          Finset.sum_neg_distrib, Finset.sum_range_sub, neg_sub]
      rw [← Finset.mul_sum]
      exact congrArg (fun a : ℝ => 2 * a) (by simpa only [F, Nat.cast_zero, zero_add, div_one] using htel)
    _ ≤ 2 := by have h : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
                linarith

private theorem prime_product_le_two_div_log {z : ℕ} (hz : 2 ≤ z) :
    (∏ p ∈ Nat.primesLE z, (1 - (p : ℝ)⁻¹)) ≤ 2 / Real.log z := by
  classical
  let V := ∏ p ∈ Nat.primesLE z, (1 - (p : ℝ)⁻¹)
  let T := (primorial z).divisors ×ˢ Finset.Icc 1 z
  let f (a : ℕ × ℕ) := a.1 * a.2 ^ 2
  have hsub : Finset.Icc 1 z ⊆ T.image f := by
    intro n hn
    obtain ⟨hn0, hnz⟩ := Finset.mem_Icc.mp hn
    obtain ⟨d, k, hd, he⟩ := smooth_eq_divisor_mul_square z n hn0 fun p _ h =>
      (Nat.le_of_dvd hn0 h).trans hnz
    have hk : 1 ≤ k := by by_contra! h; simp [show k = 0 by omega] at he; omega
    have hkd : k ∣ n := by rw [he, pow_two, ← mul_assoc]; exact dvd_mul_left _ _
    exact Finset.mem_image.mpr ⟨(d, k), Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hd, primorial_ne_zero z⟩,
        Finset.mem_Icc.mpr ⟨hk, (Nat.le_of_dvd hn0 hkd).trans hnz⟩⟩, he.symm⟩
  have hharm : Real.log z ≤ 2 * ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ)⁻¹) := by
    calc
      _ ≤ Real.log ((z + 1 : ℕ) : ℝ) := Real.log_le_log (by exact_mod_cast (show 0 < z by omega)) (by norm_cast; omega)
      _ ≤ harmonic z := log_add_one_le_harmonic z
      _ = ∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹ := by simp [harmonic_eq_sum_Icc]
      _ ≤ ∑ n ∈ T.image f, (n : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
      _ ≤ ∑ a ∈ T, ((f a : ℕ) : ℝ)⁻¹ := Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
      _ = (∑ d ∈ (primorial z).divisors, (d : ℝ)⁻¹) *
          (∑ k ∈ Finset.Icc 1 z, ((k : ℝ) ^ 2)⁻¹) := by
        simp only [T, f, Finset.sum_product, Nat.cast_mul, Nat.cast_pow, mul_inv_rev,
          mul_comm, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ 2 * ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ)⁻¹) := by
        rw [primorial_eq_prod_primesLE, sum_inv_divisors_prime_product _
          (fun _ hp => Nat.prime_of_mem_primesLE hp), mul_comm (2 : ℝ)]
        exact mul_le_mul_of_nonneg_left (sum_inv_sq_le_two z)
          (Finset.prod_nonneg fun _ _ => by positivity)
  have hV : 0 ≤ V := by
    refine Finset.prod_nonneg fun p hp => sub_nonneg.mpr (inv_le_one_of_one_le₀ ?_)
    exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
  have hcomp : V * (∏ p ∈ Nat.primesLE z, (1 + (p : ℝ)⁻¹)) ≤ 1 := by
    dsimp only [V]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_one ?_ (fun p _ => ?_)
    · intro p hp
      have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
      exact mul_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hp')) (by positivity)
    · nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast (show 1 < z by omega)))).mpr
  calc
    V * Real.log z ≤ V * (2 * ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hharm hV
    _ ≤ 2 := by linarith [show V * (2 * ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ)⁻¹)) =
      2 * (V * ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ)⁻¹)) by ring, hcomp]
private theorem primorial_le_rpow_of_le_log {n z : ℕ} (hn : 0 < n)
    (hz : (z : ℝ) ≤ Real.log n / 16) :
    (primorial z : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  calc
    _ ≤ (((4 : ℕ) ^ z : ℕ) : ℝ) := by exact_mod_cast primorial_le_four_pow z
    _ = Real.exp (Real.log 4 * z) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), mul_comm]
    _ ≤ Real.exp (Real.log n * (1 / 8)) := by
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonneg_right hlog4 (Nat.cast_nonneg (α := ℝ) z)]
    _ = _ := (Real.rpow_def_of_pos hn0 _).symm

private theorem eventually_smooth_bound_of_le_log :
    ∀ᶠ n : ℕ in atTop, ∀ z y : ℕ, (z : ℝ) ≤ Real.log n / 16 →
      (y : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) →
      (((primorial z + 1) * (y.sqrt + 1) : ℕ) : ℝ) ≤ (n : ℝ) / Real.log n := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_atTop (r := 1 / 8) (by norm_num)).bound
      (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with n hlog hn z y hz hy
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hp := primorial_le_rpow_of_le_log (show 0 < n by omega) hz
  have hs : (y.sqrt : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ Real.sqrt y := Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' y)
      _ ≤ Real.sqrt ((n : ℝ) ^ (3 / 2 : ℝ)) := Real.sqrt_le_sqrt hy
      _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]; norm_num
  have h8 : 1 ≤ (n : ℝ) ^ (1 / 8 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have h4 : 1 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  simp only [Real.norm_eq_abs, abs_of_pos hnlog, abs_of_nonneg (Real.rpow_nonneg hn0.le _)] at hlog
  push_cast
  apply (le_div_iff₀ hnlog).mpr
  calc
    _ ≤ (2 * (n : ℝ) ^ (1 / 8 : ℝ) * (2 * (n : ℝ) ^ (3 / 4 : ℝ))) * Real.log n := by
      gcongr
      · linarith
      · linarith
    _ = (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) * (4 * Real.log n) := by ring
    _ ≤ (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) := by
      gcongr
      linarith
    _ = _ := by rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; norm_num

private theorem eventually_primeCounting_upper_uniform :
    ∀ᶠ n : ℕ in atTop, ∀ y : ℕ, n ≤ y →
      (Nat.primeCounting y : ℝ) ≤ 4 * y / Real.log y := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp primeCounting_eventually_upper
  exact (eventually_ge_atTop N).mono fun _ hn y hy => hN y (hn.trans hy)


private theorem sum_primeCounting_div_le {n y : ℕ} (hn : 2 ≤ n)
    (hπ : ∀ m : ℕ, n ≤ m → (Nat.primeCounting m : ℝ) ≤ 4 * m / Real.log m) :
    ((∑ k ∈ Finset.Icc 1 (y / (n + 1)), Nat.primeCounting (y / k) : ℕ) : ℝ) ≤
      (4 * (y : ℝ) / Real.log n) * (1 + Real.log (y / (n + 1) : ℕ)) := by
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  push_cast only [Nat.cast_sum]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 (y / (n + 1)), (4 * (y : ℝ) / Real.log n) * (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk0, hk⟩ := Finset.mem_Icc.mp hk
      have hnk : n ≤ y / k := by
        apply (Nat.le_div_iff_mul_le hk0).mpr
        rw [Nat.mul_comm n k]
        exact (Nat.mul_le_mul_left k n.le_succ).trans
          ((Nat.le_div_iff_mul_le (Nat.succ_pos n)).mp hk)
      have hlog := Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (show (n : ℝ) ≤ (y / k : ℕ) by exact_mod_cast hnk)
      refine (hπ _ hnk).trans ?_
      calc
        _ ≤ 4 * ((y / k : ℕ) : ℝ) / Real.log n :=
          div_le_div_of_nonneg_left (by positivity) hnlog hlog
        _ ≤ 4 * ((y : ℝ) / (k : ℝ)) / Real.log n := by
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)) hnlog.le
        _ = _ := by ring
    _ = (4 * (y : ℝ) / Real.log n) * harmonic (y / (n + 1)) := by
      rw [← Finset.mul_sum]
      simp [harmonic_eq_sum_Icc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (by positivity)

private theorem eventually_y_ge_log_sieve :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℕ,
      (z : ℝ) ≤ Real.log n / 16 → 4 ≤ Real.log (z : ℝ) →
      ⌊(n : ℝ) * Real.log (z : ℝ) / (16 * (1 + Real.log (Real.log (z : ℝ))))⌋₊ ≤
        Erdos687.Y (64 * n) := by
  filter_upwards [eventually_primeCounting_upper_uniform, primeCounting_eventually_reserve,
    eventually_smooth_bound_of_le_log, eventually_ge_atTop (2 : ℕ)] with n hπ hreserve hsmooth hn z hz hL
  let L := Real.log (z : ℝ)
  let D := 1 + Real.log L
  let y := ⌊(n : ℝ) * L / (16 * D)⌋₊
  change y ≤ Erdos687.Y (64 * n)
  change 4 ≤ L at hL
  have hL0 : 0 < L := by linarith
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [Real.log_nonneg (show 1 ≤ L by linarith)]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hz2 : 2 ≤ z := by
    by_contra! h
    have he : z = 0 ∨ z = 1 := by omega
    have hzero : L = 0 := by rcases he with he | he <;> simp [L, he]
    linarith
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hzlog : L ≤ (z : ℝ) := by dsimp [L]; linarith [Real.log_le_sub_one_of_pos hz0]
  have hzn : z ≤ n := by
    have h := Real.log_le_sub_one_of_pos hn0
    exact_mod_cast (show (z : ℝ) ≤ n by linarith)
  have hy : (y : ℝ) ≤ (n : ℝ) * L / (16 * D) := Nat.floor_le (by positivity)
  have hy' : (y : ℝ) * (16 * D) ≤ (n : ℝ) * L := (le_div_iff₀ (by positivity)).mp hy
  have hyLarge : (y : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hnroot := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hn0.le] at hnroot
    have hzs : L ≤ Real.sqrt (n : ℝ) := by linarith
    calc
      _ ≤ (y : ℝ) * (16 * D) := by nlinarith [Nat.cast_nonneg (α := ℝ) y]
      _ ≤ (n : ℝ) * L := hy'
      _ ≤ (n : ℝ) * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_left hzs hn0.le
      _ = _ := by
        rw [Real.sqrt_eq_rpow, mul_comm, ← Real.rpow_add_one hn0.ne']
        norm_num
  have hq : ((y / (n + 1) : ℕ) : ℝ) ≤ L := by
    refine Nat.cast_div_le.trans ((div_le_iff₀ (by positivity)).mpr ?_)
    push_cast
    have hY : (y : ℝ) ≤ (y : ℝ) * (16 * D) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) y]
    nlinarith [hY.trans hy']
  have hlogq : 1 + Real.log (y / (n + 1) : ℕ) ≤ D := by
    dsimp [D]
    by_cases hq0 : y / (n + 1) = 0
    · rw [hq0, Nat.cast_zero, Real.log_zero]
      linarith [Real.log_nonneg (show 1 ≤ L by linarith)]
    · have hqpos : (0 : ℝ) < (y / (n + 1) : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
      linarith only [Real.log_le_log hqpos hq]
  let B := (n : ℝ) / Real.log (n : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcount : ((∑ k ∈ Finset.Icc 1 (y / (n + 1)), Nat.primeCounting (y / k) : ℕ) : ℝ) ≤
      (L / 4) * B := by
    calc
      _ ≤ (4 * (y : ℝ) / Real.log n) * (1 + Real.log (y / (n + 1) : ℕ)) :=
        sum_primeCounting_div_le hn hπ
      _ ≤ (4 * (y : ℝ) / Real.log n) * D :=
        mul_le_mul_of_nonneg_left hlogq (by positivity)
      _ = ((y : ℝ) * (16 * D)) / (4 * Real.log n) := by ring
      _ ≤ ((n : ℝ) * L) / (4 * Real.log n) :=
        div_le_div_of_nonneg_right hy' (by positivity)
      _ = _ := by dsimp [B]; ring
  have hsurvivors : (((Finset.Icc 1 y).filter
       (fun m => ∀ p ∈ (Nat.primesLE n).filter (z < ·), ¬p ∣ m)).card : ℝ) ≤
      (1 + L / 4) * B := by
    calc
      _ ≤ (((primorial z + 1) * (y.sqrt + 1) : ℕ) : ℝ) +
          ((∑ k ∈ Finset.Icc 1 (y / (n + 1)), Nat.primeCounting (y / k) : ℕ) : ℝ) := by
        exact_mod_cast count_medium_survivors_sum z n y
      _ ≤ B + (L / 4) * B := add_le_add (hsmooth z y hz hyLarge) hcount
      _ = _ := by ring
  apply cover_of_medium_survivors hzn (Nat.le_mul_of_pos_left n (by decide))
  refine (mul_le_mul (prime_product_le_two_div_log hz2) hsurvivors (by positivity)
    (by positivity : 0 ≤ 2 / L)).trans ?_
  calc
    (2 / L) * ((1 + L / 4) * B) = (2 / L + 1 / 2) * B := by field_simp; ring
    _ ≤ B := by
      have h : 2 / L ≤ 1 / 2 := (div_le_iff₀ hL0).mpr (by linarith)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 2 / L + 1 / 2 ≤ 1 by linarith) hB
    _ ≤ _ := hreserve

private theorem eventually_loglog_floor_le_Y :
    ∀ᶠ x : ℕ in atTop,
      ⌊(x : ℝ) * Real.log (Real.log x) /
        (4096 * (1 + Real.log (Real.log (Real.log x))))⌋₊ ≤ Erdos687.Y x := by
  have ht : Tendsto (fun x : ℕ => x / 64) atTop atTop := by
    refine tendsto_atTop.mpr fun k => (eventually_ge_atTop (64 * k)).mono fun x hx => ?_
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 64)).mpr (by simpa only [Nat.mul_comm] using hx)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [ht.eventually eventually_y_ge_log_sieve,
    ht.eventually (eventually_ge_atTop (128 : ℕ)), hlog.eventually_ge_atTop (64 : ℝ),
    hloglog.eventually_ge_atTop (max 8 (2 * Real.log 64))] with x hcover hn' hxlog hxloglog
  change 64 ≤ Real.log (x : ℝ) at hxlog
  let n := x / 64
  let z := ⌊Real.log (n : ℝ) / 16⌋₊
  let L := Real.log (z : ℝ)
  let Lx := Real.log (Real.log (x : ℝ))
  have hn : 128 ≤ n := hn'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn128 : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hnlog0 : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hxlog0 : 0 < Real.log (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by
      by_contra! h
      have hx : x = 0 := by omega
      simp [n, hx] at hn)
  have h64n : 64 * n ≤ x := by
    simpa only [n, Nat.mul_comm] using Nat.div_mul_le_self x 64
  have h128n : x ≤ 128 * n := by
    have hr := Nat.mod_lt x (by decide : 0 < 64)
    have he : x % 64 + 64 * n = x := Nat.mod_add_div x 64
    omega
  have hxn : (x : ℝ) / 128 ≤ n := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 128)).mpr
    exact_mod_cast (Nat.mul_comm 128 n ▸ h128n)
  have hnlog : Real.log (x : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log ((128 : ℝ) * n) := Real.log_le_log hx0 (by exact_mod_cast h128n)
      _ = Real.log 128 + Real.log (n : ℝ) := Real.log_mul (by norm_num) hn0.ne'
      _ ≤ _ := by
        linarith [Real.log_le_log (show (0 : ℝ) < 128 by norm_num) hn128]
  have hzupper : (z : ℝ) ≤ Real.log (n : ℝ) / 16 := Nat.floor_le (by positivity)
  have hzlower : Real.log (x : ℝ) / 64 ≤ z := by
    have hh := Nat.lt_floor_add_one (Real.log (n : ℝ) / 16)
    change Real.log (n : ℝ) / 16 < (z : ℝ) + 1 at hh
    linarith
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le (by positivity) hzlower
  have hLx8 : 8 ≤ Lx := (le_max_left _ _).trans hxloglog
  have hLx64 : 2 * Real.log 64 ≤ Lx := (le_max_right _ _).trans hxloglog
  have hLlower : Lx / 2 ≤ L := by
    have hh := Real.log_le_log (show 0 < Real.log (x : ℝ) / 64 by positivity) hzlower
    rw [Real.log_div hxlog0.ne' (by norm_num)] at hh
    change Lx - Real.log 64 ≤ L at hh
    linarith
  have hLupper : L ≤ Lx := by
    have hnx : n ≤ x := Nat.div_le_self x 64
    have hh := Real.log_le_log hn0 (show (n : ℝ) ≤ x by exact_mod_cast hnx)
    exact Real.log_le_log hz0 (by linarith)
  have hL4 : 4 ≤ L := by linarith
  have hD : 0 < 1 + Real.log L := by
    linarith [Real.log_nonneg (show 1 ≤ L by linarith)]
  have hDx : 0 < 1 + Real.log Lx := by
    linarith [Real.log_nonneg (show 1 ≤ Lx by linarith)]
  have hDle : 16 * (1 + Real.log L) ≤ 16 * (1 + Real.log Lx) := by
    linarith [Real.log_le_log (show 0 < L by linarith) hLupper]
  have hcompare : (x : ℝ) * Lx / (4096 * (1 + Real.log Lx)) ≤
      (n : ℝ) * L / (16 * (1 + Real.log L)) := by
    calc
      _ = ((x : ℝ) / 128) * (Lx / 2) / (16 * (1 + Real.log Lx)) := by
        field_simp [ne_of_gt hDx]
        ring
      _ ≤ (n : ℝ) * L / (16 * (1 + Real.log Lx)) :=
        div_le_div_of_nonneg_right (mul_le_mul hxn hLlower (by positivity) hn0.le) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hDle
  exact ((Nat.floor_mono hcompare).trans (hcover z hzupper hL4)).trans (Y_monotone h64n)

/-- A quantitative lower bound from the greedy sieve and the prime reserve. -/
theorem loglog_div_logloglog_isBigO_Y :
    (fun x : ℕ => (x : ℝ) * Real.log (Real.log x) /
      (1 + Real.log (Real.log (Real.log x)))) =O[atTop] (fun x => (Erdos687.Y x : ℝ)) := by
  have ht := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  refine Asymptotics.isBigO_iff.mpr ⟨8192, ?_⟩
  filter_upwards [eventually_loglog_floor_le_Y, ht.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2 : ℕ)] with x hx hlog hx2
  let F := (x : ℝ) * Real.log (Real.log x) / (1 + Real.log (Real.log (Real.log x)))
  change ‖F‖ ≤ 8192 * ‖(Erdos687.Y x : ℝ)‖
  have hF : 0 ≤ F := by
    dsimp [F]
    have h : 0 ≤ Real.log (Real.log (Real.log x)) := Real.log_nonneg hlog
    positivity
  have hlt : F / 4096 < (Erdos687.Y x : ℝ) + 1 := by
    rw [show F / 4096 = (x : ℝ) * Real.log (Real.log x) /
      (4096 * (1 + Real.log (Real.log (Real.log x)))) by
        dsimp [F]
        rw [div_div, mul_comm (1 + Real.log (Real.log (Real.log (x : ℝ))))]]
    have hh : (⌊(x : ℝ) * Real.log (Real.log x) /
        (4096 * (1 + Real.log (Real.log (Real.log x))))⌋₊ : ℝ) ≤ (Erdos687.Y x : ℝ) := by
      exact_mod_cast hx
    exact (Nat.lt_floor_add_one _).trans_le (add_le_add hh le_rfl)
  have hY : (1 : ℝ) ≤ Erdos687.Y x := by
    exact_mod_cast (show 1 ≤ Erdos687.Y x from
      (show 1 ≤ x - 1 by omega).trans (predecessor_le_Y x))
  simp only [Real.norm_eq_abs, abs_of_nonneg hF, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  linarith

end Erdos687Relay

noncomputable def OMA.answer : ℕ → ℝ := sorry

theorem OMA.solution : Erdos687.erdos_687.parts.i.answer = OMA.answer → type_of% @Erdos687.erdos_687.parts.i := by
  intro h
  rw [h]
  sorry

