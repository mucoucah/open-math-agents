import FormalConjectures.ErdosProblems.«687»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Bertrand

/-! Residue covers and gaps between integers coprime to a primorial. -/

-- Problem: Erdős Problem 687 — iii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/687.lean:190 (declaration Erdos687.erdos_687.parts.iii)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter
open scoped Asymptotics

namespace Erdos687

private lemma add_residue_complement {p : ℕ} (hp : 0 < p) (a : ℕ) :
    a + (p - a % p) ≡ 0 [MOD p] := by
  have hmod : a ≡ a % p [MOD p] := by simp [Nat.ModEq]
  have hsum : a % p + (p - a % p) = p := by
    have := Nat.mod_lt a hp
    omega
  refine (hmod.add_right _).trans ?_
  simpa only [hsum] using (Nat.modulus_modEq_zero (n := p))

/-- A residue cover is a block without any integer coprime to the primorial.
It suffices to consider starting points in one period. -/
private lemma covered_iff_shifted_nonCoprime (x y : ℕ) :
    Green46.IsCoveredByResidues x y ↔
      ∃ b < primorial x, ∀ m ∈ Finset.Icc 1 y, ¬ (b + m).Coprime (primorial x) := by
  constructor
  · rintro ⟨a, ha⟩
    let ps := (Finset.range (x + 1)).filter Nat.Prime
    have hmem (p : ℕ) : p ∈ ps ↔ p ≤ x ∧ p.Prime := by
      simp [ps]
    have hn (p : ℕ) (hp : p ∈ ps) : p ≠ 0 := ((hmem p).mp hp).2.ne_zero
    have hpair : Set.Pairwise (ps : Set ℕ) (Function.onFun Nat.Coprime id) := by
      intro p hp q hq hpq
      exact (Nat.coprime_primes ((hmem p).mp hp).2 ((hmem q).mp hq).2).mpr hpq
    let b := Nat.chineseRemainderOfFinset (fun p ↦ p - a p % p) id ps hn hpair
    refine ⟨b, Nat.chineseRemainderOfFinset_lt_prod _ _ hn hpair, ?_⟩
    intro m hm
    obtain ⟨p, hpx, hp, hma⟩ := ha m hm
    have hba := b.property p ((hmem p).mpr ⟨hpx, hp⟩)
    have hsum : (b : ℕ) + m ≡ 0 [MOD p] := by
      refine (hba.add hma).trans ?_
      rw [add_comm]
      exact add_residue_complement hp.pos (a p)
    exact Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hp, Nat.modEq_zero_iff_dvd.mp hsum, hp.dvd_primorial_iff.mpr hpx⟩
  · rintro ⟨b, _, hb⟩
    refine ⟨fun p ↦ p - b % p, ?_⟩
    intro m hm
    obtain ⟨p, hp, hpbm, hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp (hb m hm)
    refine ⟨p, hp.dvd_primorial_iff.mp hpx, hp, Nat.ModEq.add_left_cancel' b ?_⟩
    exact (Nat.modEq_zero_iff_dvd.mpr hpbm).trans (add_residue_complement hp.pos b).symm

private lemma covered_iff_le_Y (x y : ℕ) : Green46.IsCoveredByResidues x y ↔ y ≤ Y x := by
  let S : Set ℕ := {n | Green46.IsCoveredByResidues x n}
  have hbounded : BddAbove S :=
    ⟨primorial x, fun n hn ↦ (lt_primorial_of_isCoveredByResidues (x := x) (y := n) hn).le⟩
  have hn : (0 : ℕ) ∈ S := ⟨id, by simp⟩
  change y ∈ S ↔ y ≤ sSup S
  refine ⟨le_csSup hbounded, fun hy ↦ ?_⟩
  obtain ⟨a, ha⟩ : sSup S ∈ S := Nat.sSup_mem ⟨0, hn⟩ hbounded
  exact ⟨a, fun m hm ↦ ha m (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hy⟩)⟩

/-- The first length that guarantees a coprime integer in every block is `Y x + 1`. -/
private lemma Y_lt_iff_uniform_coprime (x y : ℕ) :
    Y x < y ↔
      ∀ b < primorial x, ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  classical
  rw [← not_le, ← covered_iff_le_Y, covered_iff_shifted_nonCoprime]
  push Not
  rfl

private lemma target_iff_uniform_coprime :
    (∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε))) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      ∀ b < primorial x, ∃ m ∈ Finset.Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊,
        (b + m).Coprime (primorial x) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (h (ε / 2) (half_pos hε))
    have hgrowth : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (ε / 2)) atTop atTop :=
      (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
    filter_upwards [hC, (tendsto_atTop.mp hgrowth) (C + 1), eventually_ge_atTop 1] with x hx hlarge hx1
    apply (Y_lt_iff_uniform_coprime _ _).mp
    apply Nat.lt_ceil.mpr
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hx1 : 0 < x)
    have hnonneg : 0 ≤ (x : ℝ) ^ (1 + ε / 2) := Real.rpow_nonneg hxpos.le _
    have hbound : (Y x : ℝ) ≤ C * (x : ℝ) ^ (1 + ε / 2) := by
      simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (Y x)), Real.norm_of_nonneg hnonneg] using hx
    calc
      (Y x : ℝ) ≤ C * (x : ℝ) ^ (1 + ε / 2) := hbound
      _ < (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (1 + ε / 2) :=
        mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hxpos _)
      _ = (x : ℝ) ^ (1 + ε) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
  · intro h ε hε
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [h ε hε] with x hx
    have hy := Nat.lt_ceil.mp ((Y_lt_iff_uniform_coprime _ _).mpr hx)
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (Y x)),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _), one_mul] using hy.le

/-- Bertrand's postulate supplies a coprime integer when the offset is at most the length. -/
private lemma coprime_of_offset_le_length {x y b : ℕ} (hx : 0 < x) (hxy : 2 * x ≤ y)
    (hby : b ≤ y) : ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (max b x)
    (Nat.ne_of_gt (hx.trans_le (le_max_right _ _)))
  have hbp : b < p := (le_max_left _ _).trans_lt hlt
  have hxp : x < p := (le_max_right _ _).trans_lt hlt
  have hupper : p ≤ b + y := by
    rcases le_total b x with hbx | hxb
    · rw [max_eq_right hbx] at hle
      omega
    · rw [max_eq_left hxb] at hle
      omega
  refine ⟨p - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [show b + (p - b) = p by omega]
  exact hp.coprime_iff_not_dvd.mpr (fun hd ↦ (not_le.mpr hxp) (hp.dvd_primorial_iff.mp hd))

/-- A block crossing the end of the period contains `P - 1` or `P + 1`. -/
private lemma coprime_of_crossing_period {P b y : ℕ} (hy : 2 ≤ y)
    (hb : b < P) (hend : P ≤ b + y) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P := by
  by_cases h : b + 1 < P
  · refine ⟨P - 1 - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [show b + (P - 1 - b) = P - 1 by omega]
    exact (Nat.coprime_self_sub_left (by omega : 1 ≤ P)).mpr (Nat.coprime_one_left P)
  · refine ⟨2, Finset.mem_Icc.mpr ⟨by decide, hy⟩, ?_⟩
    rw [show b + 2 = 1 + P by omega, Nat.coprime_add_self_left]
    exact Nat.coprime_one_left P

/-- Reflection within a period preserves coprimality and reverses a block. -/
private lemma coprime_of_reflected_offset {P b y : ℕ} (hend : b + y < P)
    (h : ∃ m ∈ Finset.Icc 1 y, (P - (b + y) - 1 + m).Coprime P) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P := by
  obtain ⟨m, hm, hc⟩ := h
  obtain ⟨hm1, hmy⟩ := Finset.mem_Icc.mp hm
  refine ⟨y + 1 - m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [show b + (y + 1 - m) = P - (P - (b + y) - 1 + m) by omega]
  exact (Nat.coprime_self_sub_left (by omega : P - (b + y) - 1 + m ≤ P)).mpr hc

/-- For long blocks it suffices to test blocks in the first half of the period,
starting more than one block length from zero. -/
private lemma uniform_coprime_of_first_half {x y : ℕ} (hx : 0 < x) (hxy : 2 * x ≤ y)
    (h : ∀ b, y < b → 2 * b + y < primorial x →
      ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x)) :
    ∀ b < primorial x, ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  intro b hb
  by_cases hsmall : b ≤ y
  · exact coprime_of_offset_le_length hx hxy hsmall
  by_cases hfirst : 2 * b + y < primorial x
  · exact h b (lt_of_not_ge hsmall) hfirst
  by_cases hcross : primorial x ≤ b + y
  · exact coprime_of_crossing_period (by omega) hb hcross
  apply coprime_of_reflected_offset (lt_of_not_ge hcross)
  let b' := primorial x - (b + y) - 1
  change ∃ m ∈ Finset.Icc 1 y, (b' + m).Coprime (primorial x)
  by_cases hsmall' : b' ≤ y
  · exact coprime_of_offset_le_length hx hxy hsmall'
  exact h b' (lt_of_not_ge hsmall') (by dsimp [b']; omega)

private lemma eventually_twice_le_length {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, 0 < x ∧ 2 * x ≤ ⌈(x : ℝ) ^ (1 + ε)⌉₊ := by
  have hgrowth : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, (tendsto_atTop.mp hgrowth) 2] with x hx hg
  have hx' : 0 < x := hx
  have hpos : 0 < (x : ℝ) := by exact_mod_cast hx'
  have hreal : ((2 * x : ℕ) : ℝ) ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := by
    calc
      ((2 * x : ℕ) : ℝ) = (x : ℝ) * 2 := by push_cast; ring
      _ ≤ (x : ℝ) * (x : ℝ) ^ ε := mul_le_mul_of_nonneg_left hg hpos.le
      _ = (x : ℝ) ^ (1 + ε) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := Nat.le_ceil _
  exact ⟨hx', by exact_mod_cast hreal⟩

private lemma target_of_first_half
    (h : ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      ∀ b, L < b → 2 * b + L < primorial x →
        ∃ m ∈ Finset.Icc 1 L, (b + m).Coprime (primorial x)) :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  apply target_iff_uniform_coprime.mpr
  intro ε hε
  filter_upwards [h ε hε, eventually_twice_le_length hε] with x hinner hx
  exact uniform_coprime_of_first_half hx.1 hx.2 hinner

/-- A progression through `c` with step `P / gcd P c` reduces coprimality
to the primes of `P` that divide `c`. -/
private lemma coprime_add_reduced_denominator {P c t : ℕ} (hP : Squarefree P) :
    (c + (P / P.gcd c) * t).Coprime P ↔ t.Coprime (P.gcd c) := by
  let g := P.gcd c
  let d := P / g
  have hgP : g ∣ P := Nat.gcd_dvd_left P c
  have hgc : g ∣ c := Nat.gcd_dvd_right P c
  have hdg : d * g = P := Nat.div_mul_cancel hgP
  have hdg' : d.Coprime g := Nat.coprime_of_squarefree_mul (hdg ▸ hP)
  have hcd : c.Coprime d := by
    by_cases hc : c = 0
    · simp [d, g, hc, Nat.div_self (Nat.pos_of_ne_zero hP.ne_zero)]
    · exact (Nat.coprime_div_gcd_of_squarefree hP hc).symm
  change (c + d * t).Coprime P ↔ t.Coprime g
  have hg : (c + d * t).Coprime g ↔ t.Coprime g := by
    calc
      (c + d * t).Coprime g ↔ g.Coprime (c + d * t) := Nat.coprime_comm
      _ ↔ g.Coprime (d * t) := Nat.coprime_add_iff_right hgc
      _ ↔ (d * t).Coprime g := Nat.coprime_comm
      _ ↔ t.Coprime g := Nat.coprime_mul_iff_left.trans (and_iff_right hdg')
  rw [← hdg, Nat.coprime_mul_iff_right, Nat.coprime_add_mul_left_left, hg]
  exact and_iff_right hcd

private lemma coprime_right_of_center {x b c y : ℕ} (hx : 0 < x) (hcb : c ≤ b)
    (hby : b - c ≤ y) (hbudget : 2 * (primorial x / (primorial x).gcd c) * x ≤ y) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  let P := primorial x
  let d := P / P.gcd c
  have hd : 0 < d :=
    Nat.div_pos (Nat.gcd_le_left c (primorial_pos x)) (Nat.gcd_pos_of_pos_left c (primorial_pos x))
  let n := max x ((b - c) / d)
  have hxn : x ≤ n := le_max_left _ _
  obtain ⟨p, hp, hnp, hupper⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hlower : b - c < d * p := by
    rw [mul_comm]
    exact (Nat.div_lt_iff_lt_mul hd).mp ((le_max_right _ _).trans_lt hnp)
  have hdu : d * p ≤ b - c + y := by
    have hp' := Nat.mul_le_mul_left d hupper
    rcases le_total x ((b - c) / d) with hn | hn
    · dsimp [n] at hp'
      rw [max_eq_right hn, ← mul_assoc, mul_comm d 2, mul_assoc, mul_comm d ((b - c) / d)] at hp'
      have hdiv := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self (b - c) d)
      omega
    · dsimp [n] at hp'
      rw [max_eq_left hn, ← mul_assoc, mul_comm d 2] at hp'
      change 2 * d * x ≤ y at hbudget
      omega
  refine ⟨c + d * p - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [show b + (c + d * p - b) = c + d * p by omega]
  apply (coprime_add_reduced_denominator (squarefree_primorial x)).mpr
  refine (hp.coprime_iff_not_dvd.mpr fun hdiv ↦ (hxn.trans_lt hnp).not_ge
    (hp.dvd_primorial_iff.mp hdiv)).of_dvd_right (Nat.gcd_dvd_left P c)

private lemma coprime_near_center_on_right {x b c y : ℕ} (hx : 0 < x)
    (hnear : b ≤ c + y) (hside : 2 * c ≤ 2 * b + y + 1)
    (hbudget : 4 * (primorial x / (primorial x).gcd c) * x ≤ y) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  let u := max b c
  have hbu : b ≤ u := le_max_left _ _
  have hcu : c ≤ u := le_max_right _ _
  have hul : u ≤ b + y := max_le (by omega) (by omega)
  have hdist : u - c ≤ b + y - u := by
    rcases le_total b c with h | h
    · simp [u, max_eq_right h]
    · rw [show u = b from max_eq_left h]
      omega
  have hroom : 2 * (primorial x / (primorial x).gcd c) * x ≤ b + y - u := by
    have hlen : 2 * (b + y - u) + 1 ≥ y := by
      rcases le_total b c with h | h
      · rw [show u = c from max_eq_right h]
        omega
      · rw [show u = b from max_eq_left h]
        omega
    have hh : 4 * (primorial x / (primorial x).gcd c) * x =
        2 * (2 * (primorial x / (primorial x).gcd c) * x) := by ring
    omega
  obtain ⟨m, hm, hc⟩ := coprime_right_of_center hx hcu hdist hroom
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  refine ⟨u - b + m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rwa [show b + (u - b + m) = u + m by omega]

/-- A block near a rational multiple `c` of `primorial x` is guaranteed
a witness when the reduced denominator of `c / primorial x` is small. -/
private lemma coprime_near_reduced_denominator {x b c y : ℕ} (hx : 0 < x)
    (hend : b + y < primorial x) (hc : c ≤ primorial x)
    (hnear : b ≤ c + y) (hnear' : c ≤ b + 2 * y + 1)
    (hbudget : 4 * (primorial x / (primorial x).gcd c) * x ≤ y) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  by_cases hside : 2 * c ≤ 2 * b + y + 1
  · exact coprime_near_center_on_right hx hnear hside hbudget
  apply coprime_of_reflected_offset hend
  apply coprime_near_center_on_right (c := primorial x - c) hx (by omega) (by omega)
  rwa [Nat.gcd_self_sub_right hc]

private lemma target_of_offsets_away_from_centers
    (h : ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      let P := primorial x
      ∀ b, L < b → 2 * b + L < P →
        (∀ c ≤ P, b ≤ c + L → c ≤ b + 2 * L + 1 → L < 4 * (P / P.gcd c) * x) →
        ∃ m ∈ Finset.Icc 1 L, (b + m).Coprime P) :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  apply target_of_first_half
  intro ε hε
  filter_upwards [h ε hε, eventually_ge_atTop 1] with x hinner hx
  intro L b hLb hhalf
  by_cases hcenter : ∃ c ≤ primorial x, b ≤ c + L ∧ c ≤ b + 2 * L + 1 ∧
      4 * (primorial x / (primorial x).gcd c) * x ≤ L
  · obtain ⟨c, hc, hnear, hnear', hbudget⟩ := hcenter
    exact coprime_near_reduced_denominator hx (by omega) hc hnear hnear' hbudget
  exact hinner b hLb hhalf (fun c hc hnear hnear' ↦
    lt_of_not_ge fun hbudget ↦ hcenter ⟨c, hc, hnear, hnear', hbudget⟩)

/-- A left endpoint that is not coprime can be passed by sliding a block
one place to the right, provided the preceding block has a witness. -/
private lemma Y_lt_iff_coprime_offsets {x y : ℕ} (hx : 0 < x) (hxy : 2 * x ≤ y) :
    Y x < y ↔ ∀ b, y < b → 2 * b + y < primorial x → b.Coprime (primorial x) →
      ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  constructor
  · intro hy b _ hb _
    exact (Y_lt_iff_uniform_coprime x y).mp hy b (by omega)
  · intro h
    apply (Y_lt_iff_uniform_coprime x y).mpr
    apply uniform_coprime_of_first_half hx hxy
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro hby hhalf
      by_cases hb : b.Coprime (primorial x)
      · exact h b hby hhalf hb
      have hprev : ∃ m ∈ Finset.Icc 1 y, (b - 1 + m).Coprime (primorial x) := by
        by_cases hsmall : b - 1 ≤ y
        · exact coprime_of_offset_le_length hx hxy hsmall
        · exact ih (b - 1) (by omega) (by omega) (by omega)
      obtain ⟨m, hm, hcop⟩ := hprev
      obtain ⟨hm1, hmy⟩ := Finset.mem_Icc.mp hm
      have hm2 : 2 ≤ m := by
        by_contra! hlt
        exact hb (by simpa only [show b - 1 + m = b by omega] using hcop)
      refine ⟨m - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rwa [show b + (m - 1) = b - 1 + m by omega]

private lemma coprime_center_plus_step {P c : ℕ} (hP : Squarefree P) :
    (c + P / P.gcd c).Coprime P := by
  simpa only [mul_one] using
    (coprime_add_reduced_denominator (c := c) (t := 1) hP).mpr (Nat.coprime_one_left _)

private lemma coprime_center_minus_step {P c : ℕ} (hP : Squarefree P) (hc : c ≤ P)
    (hstep : P / P.gcd c ≤ c) : (c - P / P.gcd c).Coprime P := by
  have h := coprime_center_plus_step (c := P - c) hP
  rw [Nat.gcd_self_sub_right hc] at h
  rw [show c - P / P.gcd c = P - (P - c + P / P.gcd c) by omega]
  exact (Nat.coprime_self_sub_left (by omega)).mpr h

/-- A single step from a center suffices when it lands in the block.
This uses denominators as large as the distance from the center to an endpoint. -/
private lemma coprime_of_center_step_in_block {P b c y : ℕ}
    (hP : Squarefree P) (hc : c ≤ P)
    (hstep : let d := P / P.gcd c
      (b < c + d ∧ c + d ≤ b + y) ∨ (b < c - d ∧ c - d ≤ b + y)) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P := by
  let d := P / P.gcd c
  rcases hstep with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · refine ⟨c + d - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [show b + (c + d - b) = c + d by omega]
    exact coprime_center_plus_step hP
  · refine ⟨c - d - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [show b + (c - d - b) = c - d by omega]
    exact coprime_center_minus_step hP hc (by omega)

private lemma target_of_coprime_offsets_away_from_centers
    (h : ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      let P := primorial x
      ∀ b, L < b → 2 * b + L < P → b.Coprime P →
        (∀ c ≤ P, b ≤ c + L → c ≤ b + 2 * L + 1 → L < 4 * (P / P.gcd c) * x) →
        (∀ c ≤ P, let d := P / P.gcd c
          (b < c + d → b + L < c + d) ∧ (b < c - d → b + L < c - d)) →
        ∃ m ∈ Finset.Icc 1 L, (b + m).Coprime P) :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  apply target_iff_uniform_coprime.mpr
  intro ε hε
  filter_upwards [h ε hε, eventually_twice_le_length hε] with x hinner hx
  apply (Y_lt_iff_uniform_coprime _ _).mp
  apply (Y_lt_iff_coprime_offsets hx.1 hx.2).mpr
  intro b hLb hhalf hb
  let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
  let P := primorial x
  by_cases hnear : ∃ c ≤ P, b ≤ c + L ∧ c ≤ b + 2 * L + 1 ∧
      4 * (P / P.gcd c) * x ≤ L
  · obtain ⟨c, hc, hdist, hdist', hbudget⟩ := hnear
    exact coprime_near_reduced_denominator hx.1 (by omega) hc hdist hdist' hbudget
  by_cases hstep : ∃ c ≤ P, let d := P / P.gcd c
      (b < c + d ∧ c + d ≤ b + L) ∨ (b < c - d ∧ c - d ≤ b + L)
  · obtain ⟨c, hc, hfit⟩ := hstep
    exact coprime_of_center_step_in_block (squarefree_primorial x) hc hfit
  refine hinner b hLb hhalf hb (fun c hc hdist hdist' ↦
    lt_of_not_ge fun hbudget ↦ hnear ⟨c, hc, hdist, hdist', hbudget⟩) ?_
  intro c hc
  refine ⟨fun hlo ↦ lt_of_not_ge fun hhi ↦ hstep ⟨c, hc, Or.inl ⟨hlo, hhi⟩⟩, ?_⟩
  exact fun hlo ↦ lt_of_not_ge fun hhi ↦ hstep ⟨c, hc, Or.inr ⟨hlo, hhi⟩⟩

/-- If the maximum covered length is large, it occurs in the first half
of a period with both neighboring integers coprime. -/
private lemma exists_maximal_gap_in_first_half {x : ℕ} (hx : 0 < x) (hxy : 2 * x ≤ Y x) :
    ∃ b, Y x < b ∧ 2 * b + Y x < primorial x ∧ b.Coprime (primorial x) ∧
      (b + Y x + 1).Coprime (primorial x) ∧
      ∀ m ∈ Finset.Icc 1 (Y x), ¬ (b + m).Coprime (primorial x) := by
  have hbad : ¬ (∀ b, Y x < b → 2 * b + Y x < primorial x → b.Coprime (primorial x) →
      ∃ m ∈ Finset.Icc 1 (Y x), (b + m).Coprime (primorial x)) := fun h ↦
    (lt_irrefl (Y x)) ((Y_lt_iff_coprime_offsets hx hxy).mpr h)
  push Not at hbad
  obtain ⟨b, hby, hhalf, hleft, hgap⟩ := hbad
  obtain ⟨m, hm, hcop⟩ := (Y_lt_iff_uniform_coprime x (Y x + 1)).mp
    (Nat.lt_succ_self _) b (by omega)
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  have hm' : m = Y x + 1 := by
    by_contra hne
    exact hgap m (Finset.mem_Icc.mpr ⟨hm1, by omega⟩) hcop
  exact ⟨b, hby, hhalf, hleft, by simpa only [hm', ← Nat.add_assoc] using hcop, hgap⟩

/-- Each prime used in a maximum cover must be the sole divisor from the
primorial at some point. Otherwise its residue can be moved to extend the cover. -/
private lemma exists_exclusive_point_in_maximal_gap {x b p : ℕ} (hp : p.Prime) (hpx : p ≤ x)
    (hgap : ∀ m ∈ Finset.Icc 1 (Y x), ¬ (b + m).Coprime (primorial x)) :
    ∃ m ∈ Finset.Icc 1 (Y x), p ∣ b + m ∧
      ∀ q ≤ x, q.Prime → q ≠ p → ¬ q ∣ b + m := by
  by_contra! hmiss
  let a (q : ℕ) := if q = p then Y x + 1 else q - b % q
  have hcover : Green46.IsCoveredByResidues x (Y x + 1) := by
    refine ⟨a, ?_⟩
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    by_cases hend : m = Y x + 1
    · exact ⟨p, hpx, hp, by simpa only [a, if_pos rfl, hend] using (Nat.ModEq.refl (Y x + 1))⟩
    have hinside : m ∈ Finset.Icc 1 (Y x) := Finset.mem_Icc.mpr ⟨hm1, by omega⟩
    obtain ⟨q, hq, hqbm, hqP⟩ := Nat.Prime.not_coprime_iff_dvd.mp (hgap m hinside)
    obtain ⟨r, hrx, hr, hrp, hrbm⟩ : ∃ r ≤ x, r.Prime ∧ r ≠ p ∧ r ∣ b + m := by
      by_cases hqp : q = p
      · exact hmiss m hinside (hqp ▸ hqbm)
      · exact ⟨q, hq.dvd_primorial_iff.mp hqP, hq, hqp, hqbm⟩
    refine ⟨r, hrx, hr, Nat.ModEq.add_left_cancel' b ?_⟩
    simpa only [a, if_neg hrp] using
      (Nat.modEq_zero_iff_dvd.mpr hrbm).trans (add_residue_complement hr.pos b).symm
  have := (covered_iff_le_Y _ _).mp hcover
  omega

private lemma target_of_maximal_gaps_away_from_centers
    (h : ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      let P := primorial x
      ∀ b, L ≤ Y x → Y x < b → 2 * b + Y x < P →
        let y := Y x
        b.Coprime P → (b + y + 1).Coprime P →
        (∀ p ≤ x, p.Prime → ∃ m ∈ Finset.Icc 1 y, p ∣ b + m ∧
          ∀ q ≤ x, q.Prime → q ≠ p → ¬ q ∣ b + m) →
        (∀ c ≤ P, b ≤ c + y → c ≤ b + 2 * y + 1 → y < 4 * (P / P.gcd c) * x) →
        (∀ c ≤ P, let d := P / P.gcd c
          (b < c + d → b + y < c + d) ∧ (b < c - d → b + y < c - d)) →
        ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P) :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  apply target_iff_uniform_coprime.mpr
  intro ε hε
  filter_upwards [h ε hε, eventually_twice_le_length hε] with x hinner hx
  apply (Y_lt_iff_uniform_coprime _ _).mp
  by_contra! hlarge
  obtain ⟨b, hby, hhalf, hleft, hright, hgap⟩ :=
    exists_maximal_gap_in_first_half hx.1 (hx.2.trans hlarge)
  have hno : ¬ ∃ m ∈ Finset.Icc 1 (Y x), (b + m).Coprime (primorial x) := by
    rintro ⟨m, hm, hc⟩
    exact hgap m hm hc
  have hend : b + Y x < primorial x := by omega
  refine hno (hinner b hlarge hby hhalf hleft hright
    (fun _ hpx hp ↦ exists_exclusive_point_in_maximal_gap hp hpx hgap) ?_ ?_)
  · intro c hc hdist hdist'
    by_contra! hbudget
    exact hno (coprime_near_reduced_denominator hx.1 hend hc hdist hdist' hbudget)
  · intro c hc
    constructor <;> intro hlo <;> by_contra! hhi
    · exact hno (coprime_of_center_step_in_block (squarefree_primorial x) hc (Or.inl ⟨hlo, hhi⟩))
    · exact hno (coprime_of_center_step_in_block (squarefree_primorial x) hc (Or.inr ⟨hlo, hhi⟩))

end Erdos687

theorem OMA.solution : type_of% @Erdos687.erdos_687.parts.iii := by
  apply Erdos687.target_of_maximal_gaps_away_from_centers
  sorry

