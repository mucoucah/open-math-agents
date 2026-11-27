import FormalConjectures.ErdosProblems.«142»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.NumberTheory.Bertrand

/-! The length-two case and reductions for longer progressions. -/

-- Problem: Erdős Problem 142 — lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/142.lean:50 (declaration Erdos142.erdos_142.variants.lower)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Erdos142Lower

open Asymptotics Erdos142 Filter
open scoped Topology

lemma apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma exists_maximizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      r k N = S.card := by
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = m}
  have hz : 0 ∈ C := by
    refine ⟨∅, Finset.empty_subset _, (apFree_iff hk).mpr ?_, rfl⟩
    rintro ⟨a, d, -, h⟩
    simpa using h 0 (by omega)
  have hb : BddAbove C := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, -, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  exact ⟨S, hS, hf, he.symm⟩

lemma card_le_r {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) : S.card ≤ r k N := by
  unfold r Set.IsAPOfLengthFree.maxCard
  refine le_csSup ?_ ⟨S, hS, hf, rfl⟩
  refine ⟨N, ?_⟩
  rintro _ ⟨U, hU, -, rfl⟩
  simpa using Finset.card_le_card hU

lemma r_mono {k : ℕ} (hk : 1 < k) : Monotone (r k) := by
  intro M N hMN
  obtain ⟨S, hS, hf, hcard⟩ := exists_maximizer hk M
  rw [hcard]
  exact card_le_r (hS.trans (Finset.Icc_subset_Icc_right hMN)) hf

lemma r_add_le {k : ℕ} (hk : 1 < k) (M N : ℕ) :
    r k (M + N) ≤ r k M + r k N := by
  obtain ⟨S, hS, hf, hcard⟩ := exists_maximizer hk (M + N)
  let L := S.filter (· ≤ M)
  let R := S.filter (fun x => ¬ x ≤ M)
  let U := (Finset.Icc 1 N).filter (fun x => M + x ∈ S)
  have hL : L.card ≤ r k M := by
    apply card_le_r
    · intro x hx
      obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hS hxS)).1, hxM⟩
    · exact fun T hT hAP => hf T (hT.trans (Finset.filter_subset _ _)) hAP
  have hU : U.card ≤ r k N := by
    apply card_le_r (Finset.filter_subset _ _)
    rw [apFree_iff hk] at hf ⊢
    rintro ⟨a, d, hd, h⟩
    refine hf ⟨M + a, d, hd, fun i hi => ?_⟩
    change M + a + i * d ∈ S
    simpa only [add_assoc] using (Finset.mem_filter.mp (h i hi)).2
  have hR : R.card ≤ U.card := by
    apply Finset.card_le_card_of_injOn (fun x => x - M)
    · intro x hx
      obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
      have hxN := (Finset.mem_Icc.mp (hS hxS)).2
      change x - M ∈ U
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        by rwa [show M + (x - M) = x by omega]⟩
    · intro x hx y hy he
      have hxM := (Finset.mem_filter.mp hx).2
      have hyM := (Finset.mem_filter.mp hy).2
      change x - M = y - M at he
      omega
  calc
    r k (M + N) = L.card + R.card := hcard.trans
      (Finset.card_filter_add_card_filter_not (s := S) (· ≤ M)).symm
    _ ≤ r k M + r k N := Nat.add_le_add hL (hR.trans hU)

lemma r_mul_le {k : ℕ} (hk : 1 < k) (N q : ℕ) : r k (q * N) ≤ q * r k N := by
  induction q with
  | zero =>
    simp only [zero_mul]
    obtain ⟨S, hS, -, hcard⟩ := exists_maximizer hk 0
    rw [hcard]
    simpa using Finset.card_le_card hS
  | succ q ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact (r_add_le hk (q * N) N).trans (Nat.add_le_add_right ih _)

noncomputable def blockDensity (k j : ℕ) : ℝ := r k (4 ^ j) / (4 : ℝ) ^ j

lemma blockDensity_antitone {k : ℕ} (hk : 1 < k) : Antitone (blockDensity k) := by
  intro i j hij
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hb : (r k (4 ^ (i + t)) : ℝ) ≤ (4 : ℝ) ^ t * r k (4 ^ i) := by
    exact_mod_cast (show r k (4 ^ (i + t)) ≤ 4 ^ t * r k (4 ^ i) by
      rw [pow_add, mul_comm]
      exact r_mul_le hk _ _)
  unfold blockDensity
  have hp : (0 : ℝ) < 4 ^ t := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ t * r k (4 ^ i)) / 4 ^ (i + t) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by rw [pow_add]; field_simp

lemma littleO_of_blockDensity {k : ℕ} (hk : 1 < k)
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ j : ℕ in atTop, (j : ℝ) * blockDensity k j ≤ δ) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  rw [isLittleO_iff]
  intro ε hε
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let C := 8 * Real.log 4
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (h (ε / C) (div_pos hε hC))
  filter_upwards [eventually_ge_atTop (4 ^ max J 1)] with N hN
  let j := Nat.log 4 N
  have hj : max J 1 ≤ j := Nat.le_log_of_pow_le (by decide) hN
  have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
  have hN4 : 4 ≤ N := by
    have hp : 4 ^ 1 ≤ (4 : ℕ) ^ max J 1 :=
      pow_le_pow_right₀ (by decide) (le_max_right _ _)
    simpa using hp.trans hN
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hfloor : 4 ^ j ≤ N := Nat.pow_log_le_self 4 (by omega)
  have hceil : N < 4 ^ (j + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have hr : (r k N : ℝ) ≤ 4 * r k (4 ^ j) := by
    exact_mod_cast ((r_mono hk hceil.le).trans (by
      rw [pow_succ, mul_comm]
      exact r_mul_le hk _ _))
  have hlogN : Real.log (N : ℝ) ≤ 2 * (j : ℝ) * Real.log 4 := by
    have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hc : (N : ℝ) ≤ (4 : ℝ) ^ (j + 1) := by exact_mod_cast hceil.le
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    calc
      _ ≤ Real.log ((4 : ℝ) ^ (j + 1)) := Real.log_le_log hpos hc
      _ ≤ _ := by
        rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
        exact mul_le_mul_of_nonneg_right (by linarith) hlog.le
  have hd := hJ j ((le_max_left _ _).trans hj)
  unfold blockDensity at hd
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)] at hd
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    ← mul_div_assoc, le_div_iff₀ hlN]
  calc
    _ ≤ (4 * (r k (4 ^ j) : ℝ)) * (2 * (j : ℝ) * Real.log 4) := by gcongr
    _ = C * ((j : ℝ) * r k (4 ^ j)) := by dsimp [C]; ring
    _ ≤ C * (ε / C * (4 : ℝ) ^ j) := mul_le_mul_of_nonneg_left hd hC.le
    _ = ε * (4 : ℝ) ^ j := by field_simp
    _ ≤ ε * N := mul_le_mul_of_nonneg_left (by exact_mod_cast hfloor) hε.le

def shiftBlock (j : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.map ⟨fun b => 4 * 4 ^ j + b, fun _ _ => Nat.add_left_cancel⟩

lemma mem_shiftBlock_bounds {j x : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 (4 ^ j))
    (hx : x ∈ shiftBlock j B) : 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j := by
  obtain ⟨b, hb, he⟩ := Finset.mem_map.mp hx
  change 4 * 4 ^ j + b = x at he
  obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp (hB hb)
  omega

lemma pow_four_gap {i j : ℕ} (hij : i < j) : 4 * 4 ^ i ≤ 4 ^ j := by
  rw [mul_comm, ← pow_succ]
  exact pow_le_pow_right₀ (by decide) hij

lemma blockIndex_le {i j x y : ℕ} (hxy : x ≤ y) (hx : 4 * 4 ^ i < x)
    (hy : y ≤ 5 * 4 ^ j) : i ≤ j := by
  by_contra! h
  have hp := pow_four_gap h
  omega

lemma block_indices_of_midpoint {i j l x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hmid : x + z = 2 * y)
    (hx : 4 * 4 ^ i < x ∧ x ≤ 5 * 4 ^ i)
    (hy : 4 * 4 ^ j < y ∧ y ≤ 5 * 4 ^ j)
    (hz : 4 * 4 ^ l < z ∧ z ≤ 5 * 4 ^ l) : i = j ∧ j = l := by
  have hij := blockIndex_le hxy hx.1 hy.2
  have hjl := blockIndex_le hyz hy.1 hz.2
  have he : j = l := by
    by_contra hn
    have hp := pow_four_gap (lt_of_le_of_ne hjl hn)
    omega
  subst l
  refine ⟨?_, rfl⟩
  by_contra hn
  have hp := pow_four_gap (lt_of_le_of_ne hij hn)
  omega

lemma shifted_blocks_free {k : ℕ} (hk : 3 ≤ k) (I : Finset ℕ) (B : ℕ → Finset ℕ)
    (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j))
    (hf : ∀ j, (B j : Set ℕ).IsAPOfLengthFree k) :
    (I.biUnion (fun j => shiftBlock j (B j)) : Set ℕ).IsAPOfLengthFree k := by
  have hk' : 1 < k := by omega
  rw [apFree_iff hk']
  rintro ⟨a, d, hd, h⟩
  have hm (i : ℕ) (hi : i < k) : ∃ j, a + i * d ∈ shiftBlock j (B j) := by
    obtain ⟨j, -, hji⟩ := Finset.mem_biUnion.mp (h i hi)
    exact ⟨j, hji⟩
  choose! J hJ using hm
  have hb (i : ℕ) (hi : i < k) :=
    mem_shiftBlock_bounds (hB (J i)) (hJ i hi)
  have htrip (i : ℕ) (hi : i + 2 < k) : J i = J (i + 1) ∧ J (i + 1) = J (i + 2) := by
    apply block_indices_of_midpoint (x := a + i * d)
      (y := a + (i + 1) * d) (z := a + (i + 2) * d)
    · simp only [Nat.add_mul, one_mul]; omega
    · simp only [Nat.add_mul, one_mul, two_mul]; omega
    · simp only [Nat.add_mul, one_mul, two_mul]; omega
    · exact hb i (by omega)
    · exact hb (i + 1) (by omega)
    · exact hb (i + 2) hi
  have hsame (i : ℕ) (hi : i < k) : J i = J 0 := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have hi' : i < k := by omega
      apply Eq.trans _ (ih hi')
      by_cases ht : i + 2 < k
      · exact (htrip i ht).1.symm
      · have hprev := (htrip (i - 1) (by omega)).2.symm
        rwa [show i - 1 + 2 = i + 1 by omega, show i - 1 + 1 = i by omega] at hprev
  have ha : 4 * 4 ^ J 0 ≤ a := by simpa using (hb 0 (by omega)).1.le
  apply (apFree_iff hk').mp (hf (J 0))
  refine ⟨a - 4 * 4 ^ J 0, d, hd, fun i hi => ?_⟩
  have hm' := hJ i hi
  rw [hsame i hi] at hm'
  obtain ⟨b, hb', he⟩ := Finset.mem_map.mp hm'
  change 4 * 4 ^ J 0 + b = a + i * d at he
  rwa [show a - 4 * 4 ^ J 0 + i * d = b by omega]

lemma shifted_blocks_union_free {k : ℕ} (hk : 3 ≤ k) (B : ℕ → Finset ℕ)
    (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j))
    (hf : ∀ j, (B j : Set ℕ).IsAPOfLengthFree k) :
    {x : ℕ | ∃ j, x ∈ shiftBlock j (B j)}.IsAPOfLengthFree k := by
  have hk' : 1 < k := by omega
  rw [apFree_iff hk']
  rintro ⟨a, d, hd, h⟩
  have hm (i : ℕ) (hi : i < k) : ∃ j, a + i * d ∈ shiftBlock j (B j) := h i hi
  choose! J hJ using hm
  let I := (Finset.range k).image J
  apply (apFree_iff hk').mp (shifted_blocks_free hk I B hB hf)
  exact ⟨a, d, hd, fun i hi => Finset.mem_biUnion.mpr
    ⟨J i, Finset.mem_image_of_mem J (Finset.mem_range.mpr hi), hJ i hi⟩⟩

open scoped BigOperators

/-- Uniform decay of reciprocal mass on finite windows of geometric blocks. -/
def ReciprocalWindowBound (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
    (∀ x ∈ S, ∃ j ∈ Finset.Ico n (2 * n), 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
    (S : Set ℕ).IsAPOfLengthFree k →
    (∑ x ∈ S, (x : ℝ)⁻¹) ≤ ε

lemma shiftBlocks_pairwiseDisjoint (I : Finset ℕ) (B : ℕ → Finset ℕ)
    (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j)) :
    Set.PairwiseDisjoint (I : Set ℕ) (fun j => shiftBlock j (B j)) := by
  intro i _ j _ hne
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi := mem_shiftBlock_bounds (hB i) hxi
  have hj := mem_shiftBlock_bounds (hB j) hxj
  exact hne (le_antisymm (blockIndex_le le_rfl hi.1 hj.2)
    (blockIndex_le le_rfl hj.1 hi.2))

lemma shiftBlock_reciprocal_lower {j : ℕ} {B : Finset ℕ}
    (hB : B ⊆ Finset.Icc 1 (4 ^ j)) :
    (B.card : ℝ) / (5 * 4 ^ j) ≤ ∑ x ∈ shiftBlock j B, (x : ℝ)⁻¹ := by
  calc
    _ = ∑ _x ∈ shiftBlock j B, (5 * (4 : ℝ) ^ j)⁻¹ := by
      simp [shiftBlock, div_eq_mul_inv]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      have hb := mem_shiftBlock_bounds hB hx
      apply inv_anti₀ (by exact_mod_cast (show 0 < x by omega))
      exact_mod_cast hb.2

lemma weighted_blockDensity_of_packed_windows {k : ℕ} (hk : 1 < k) (B : ℕ → Finset ℕ)
    (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j)) (hcard : ∀ j, r k (4 ^ j) = (B j).card)
    (hw : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (∑ x ∈ (Finset.Ico n (2 * n)).biUnion (fun t => shiftBlock t (B t)), (x : ℝ)⁻¹) ≤ ε) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j : ℕ in atTop, (j : ℝ) * blockDensity k j ≤ δ := by
  intro δ hδ
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hw (δ / 15) (by positivity))
  filter_upwards [eventually_ge_atTop (2 * max M 1)] with j hj
  let n := j / 2
  have hn : max M 1 ≤ n := by dsimp [n]; omega
  have hnj : 2 * n ≤ j := by dsimp [n]; omega
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hfactor : (j : ℝ) ≤ 3 * (n : ℝ) := by
    exact_mod_cast (show j ≤ 3 * n by dsimp [n] at *; omega)
  let I := Finset.Ico n (2 * n)
  let S := I.biUnion (fun t => shiftBlock t (B t))
  have hmass : (∑ x ∈ S, (x : ℝ)⁻¹) ≤ δ / 15 :=
    hM n ((le_max_left _ _).trans hn)
  have hcardI : I.card = n := by
    dsimp [I]
    rw [Nat.card_Ico]
    omega
  have hlower : (n : ℝ) * (blockDensity k j / 5) ≤ ∑ x ∈ S, (x : ℝ)⁻¹ := by
    calc
      _ = ∑ _t ∈ I, blockDensity k j / 5 := by simp [hcardI]
      _ ≤ ∑ t ∈ I, ∑ x ∈ shiftBlock t (B t), (x : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro t ht
        have htj : t ≤ j := ((Finset.mem_Ico.mp ht).2.le).trans hnj
        calc
          _ ≤ blockDensity k t / 5 :=
            div_le_div_of_nonneg_right (blockDensity_antitone hk htj) (by norm_num)
          _ = (B t).card / (5 * (4 : ℝ) ^ t) := by
            simp only [blockDensity, hcard, div_div, mul_comm (5 : ℝ)]
          _ ≤ _ := shiftBlock_reciprocal_lower (hB t)
      _ = _ := (Finset.sum_biUnion (shiftBlocks_pairwiseDisjoint I B hB)).symm
  have hc : 0 ≤ blockDensity k j := by unfold blockDensity; positivity
  have hm := mul_le_mul_of_nonneg_right hfactor hc
  have hle := hlower.trans hmass
  linarith only [hm, hle]

lemma weighted_blockDensity_of_window {k : ℕ} (hk : 3 ≤ k)
    (hw : ReciprocalWindowBound k) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j : ℕ in atTop, (j : ℝ) * blockDensity k j ≤ δ := by
  have hk' : 1 < k := by omega
  choose B hB hf hcard using fun t : ℕ => exists_maximizer hk' (4 ^ t)
  apply weighted_blockDensity_of_packed_windows hk' B hB hcard
  intro ε hε
  filter_upwards [hw ε hε] with n hn
  let I := Finset.Ico n (2 * n)
  let S := I.biUnion (fun t => shiftBlock t (B t))
  apply hn S _ (shifted_blocks_free hk I B hB hf)
  intro x hx
  obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
  exact ⟨t, ht, mem_shiftBlock_bounds (hB t) hxt⟩

lemma littleO_of_window {k : ℕ} (hk : 3 ≤ k) (hw : ReciprocalWindowBound k) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  exact littleO_of_blockDensity (by omega) (weighted_blockDensity_of_window hk hw)

lemma weighted_blockDensity_of_littleO {k : ℕ}
    (h : (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j : ℕ in atTop, (j : ℝ) * blockDensity k j ≤ δ := by
  intro δ hδ
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (h.def (mul_pos hδ hlog))
  filter_upwards [eventually_ge_atTop J, eventually_gt_atTop (0 : ℕ)] with j hj hj0
  have hb := hJ (4 ^ j) (hj.trans (Nat.lt_pow_self (by decide : 1 < 4)).le)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Real.norm_natCast] at hb
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ (4 : ℝ) ^ j / ((j : ℝ) * Real.log 4) by
    positivity)] at hb
  rw [← mul_div_assoc, le_div_iff₀ (mul_pos hjR hlog)] at hb
  unfold blockDensity
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  apply (mul_le_mul_iff_right₀ hlog).mp
  convert hb using 1 <;> ring

lemma reciprocalMass_block_upper {k t : ℕ} (hk : 1 < k) {T : Finset ℕ}
    (hT : ∀ x ∈ T, 4 * 4 ^ t < x ∧ x ≤ 5 * 4 ^ t)
    (hf : (T : Set ℕ).IsAPOfLengthFree k) :
    (∑ x ∈ T, (x : ℝ)⁻¹) ≤ (5 / 4 : ℝ) * blockDensity k t := by
  have hs : T ⊆ Finset.Icc 1 (5 * 4 ^ t) := fun x hx =>
    Finset.mem_Icc.mpr ⟨by have := (hT x hx).1; omega, (hT x hx).2⟩
  have hc : (T.card : ℝ) ≤ 5 * r k (4 ^ t) := by
    exact_mod_cast (card_le_r hs hf).trans (r_mul_le hk _ 5)
  calc
    _ ≤ ∑ _x ∈ T, ((4 : ℝ) * 4 ^ t)⁻¹ := Finset.sum_le_sum fun x hx =>
      inv_anti₀ (by positivity) (by exact_mod_cast (hT x hx).1.le)
    _ = (T.card : ℝ) / (4 * 4 ^ t) := by simp [div_eq_mul_inv]
    _ ≤ (5 * (r k (4 ^ t) : ℝ)) / (4 * 4 ^ t) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = _ := by unfold blockDensity; ring

lemma window_of_weighted_blockDensity {k : ℕ} (hk : 1 < k)
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ j : ℕ in atTop, (j : ℝ) * blockDensity k j ≤ δ) :
    ReciprocalWindowBound k := by
  intro ε hε
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (h (4 * ε / 5) (by positivity))
  filter_upwards [eventually_ge_atTop J, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  intro S hs hf
  let I := Finset.Ico n (2 * n)
  let T (t : ℕ) := S.filter (fun x => 4 * 4 ^ t < x ∧ x ≤ 5 * 4 ^ t)
  have hT (t : ℕ) (x : ℕ) (hx : x ∈ T t) : 4 * 4 ^ t < x ∧ x ≤ 5 * 4 ^ t :=
    (Finset.mem_filter.mp hx).2
  have hU : I.biUnion T = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, -, hxt⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hxt).1
    · intro hx
      obtain ⟨t, ht, hxt⟩ := hs x hx
      exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨hx, hxt⟩⟩
  have hdisj : Set.PairwiseDisjoint (I : Set ℕ) T := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hi := hT i x hx
    have hj := hT j x hy
    exact hne (le_antisymm (blockIndex_le le_rfl hi.1 hj.2)
      (blockIndex_le le_rfl hj.1 hi.2))
  have hcardI : I.card = n := by dsimp [I]; rw [Nat.card_Ico]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  calc
    _ = ∑ t ∈ I, ∑ x ∈ T t, (x : ℝ)⁻¹ := by
      rw [← hU, Finset.sum_biUnion hdisj]
    _ ≤ ∑ _t ∈ I, ε / n := by
      apply Finset.sum_le_sum
      intro t ht
      have hnt := (Finset.mem_Ico.mp ht).1
      have hfree : (T t : Set ℕ).IsAPOfLengthFree k :=
        fun P hP hAP => hf P (hP.trans (Finset.filter_subset _ _)) hAP
      apply (reciprocalMass_block_upper hk (hT t) hfree).trans
      have hnR' : (n : ℝ) ≤ t := by exact_mod_cast hnt
      have hnonneg : 0 ≤ blockDensity k t := by unfold blockDensity; positivity
      have hle := (mul_le_mul_of_nonneg_right hnR' hnonneg).trans (hJ t (hn.trans hnt))
      apply (le_div_iff₀ hnR).mpr
      linarith only [hle]
    _ = ε := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcardI]
      field_simp

lemma littleO_iff_window {k : ℕ} (hk : 3 ≤ k) :
    ((fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)) ↔
    ReciprocalWindowBound k :=
  ⟨fun h => window_of_weighted_blockDensity (by omega) (weighted_blockDensity_of_littleO h),
    littleO_of_window hk⟩

/-- The reciprocal mass of a fixed set between each cutoff and its square. -/
noncomputable def squareWindowMass (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ioc N (N ^ 2), A.indicator (fun x : ℕ => (x : ℝ)⁻¹) x

def SquareWindowDecay (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, squareWindowMass A N ≤ ε

lemma squareWindowDecay_iff_tendsto (A : Set ℕ) :
    SquareWindowDecay A ↔ Tendsto (squareWindowMass A) atTop (𝓝 0) := by
  have hnonneg (N : ℕ) : 0 ≤ squareWindowMass A N := by
    exact Finset.sum_nonneg fun x _ => Set.indicator_nonneg (fun _ _ => by positivity) _
  constructor
  · intro h
    refine tendsto_order.mpr ⟨fun a ha => Eventually.of_forall fun N => ha.trans_le
      (hnonneg N), fun b hb => ?_⟩
    filter_upwards [h (b / 2) (by positivity)] with N hN
    linarith
  · intro h ε hε
    exact ((tendsto_order.mp h).2 ε hε).mono fun _ hN => hN.le

lemma squareWindowDecay_of_summable {A : Set ℕ}
    (h : Summable (A.indicator (fun x : ℕ => (x : ℝ)⁻¹))) : SquareWindowDecay A := by
  intro ε hε
  obtain ⟨s, hs⟩ := h.vanishing (Iio_mem_nhds hε)
  filter_upwards [eventually_ge_atTop (s.sup id)] with N hN
  have hd : Disjoint (Finset.Ioc N (N ^ 2)) s := by
    apply Finset.disjoint_left.mpr
    intro x hx hxs
    exact (Finset.mem_Ioc.mp hx).1.not_ge ((Finset.le_sup (f := id) hxs).trans hN)
  exact (show squareWindowMass A N < ε from hs _ hd).le

lemma exists_set_controlling_littleO {k : ℕ} (hk : 3 ≤ k) :
    ∃ A : Set ℕ, A.IsAPOfLengthFree k ∧
      (∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) ∧
      (SquareWindowDecay A →
        (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)) := by
  have hk' : 1 < k := by omega
  choose B hB hf hcard using fun j : ℕ => exists_maximizer hk' (4 ^ j)
  let A : Set ℕ := {x | ∃ j, x ∈ shiftBlock j (B j)}
  refine ⟨A, shifted_blocks_union_free hk B hB hf, ?_, fun hA => littleO_of_blockDensity hk' ?_⟩
  · rintro x ⟨j, hj⟩
    exact ⟨j, mem_shiftBlock_bounds (hB j) hj⟩
  apply weighted_blockDensity_of_packed_windows hk' B hB hcard
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hA ε hε)
  filter_upwards [eventually_ge_atTop M] with n hn
  let S := (Finset.Ico n (2 * n)).biUnion (fun t => shiftBlock t (B t))
  let N : ℕ := 4 * 4 ^ n
  have hS (x : ℕ) (hx : x ∈ S) : x ∈ A ∧ x ∈ Finset.Ioc N (N ^ 2) := by
    obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hnt, htn⟩ := Finset.mem_Ico.mp ht
    obtain ⟨hxlo, hxhi⟩ := mem_shiftBlock_bounds (hB t) hxt
    have hlo : 4 ^ n ≤ (4 : ℕ) ^ t := pow_le_pow_right₀ (by decide) hnt
    have hhi : 4 * 4 ^ t ≤ 4 ^ (2 * n) := pow_four_gap htn
    refine ⟨⟨t, hxt⟩, Finset.mem_Ioc.mpr ⟨by dsimp [N]; omega, ?_⟩⟩
    have he : N ^ 2 = 16 * 4 ^ (2 * n) := by
      simp [N, mul_pow, pow_mul, mul_comm 2 n]
    rw [he]
    omega
  have hN : M ≤ N := hn.trans ((Nat.lt_pow_self (by decide : 1 < 4)).le.trans (by
    dsimp [N]; omega))
  calc
    (∑ x ∈ S, (x : ℝ)⁻¹) =
        ∑ x ∈ S, A.indicator (fun x : ℕ => (x : ℝ)⁻¹) x := by
      exact Finset.sum_congr rfl fun x hx =>
        (Set.indicator_of_mem (hS x hx).1 (fun y : ℕ => (y : ℝ)⁻¹)).symm
    _ ≤ squareWindowMass A N := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (hS x hx).2)
        (fun x _ _ => Set.indicator_nonneg (fun _ _ => by positivity) _)
    _ ≤ ε := hM N hN

lemma squareWindowDecay_of_littleO {k : ℕ} (hk : 1 < k)
    (h : (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log))
    {A : Set ℕ} (hA : A.IsAPOfLengthFree k) : SquareWindowDecay A := by
  classical
  intro ε hε
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (weighted_blockDensity_of_littleO h (ε / 12)
    (by positivity))
  filter_upwards [eventually_ge_atTop (4 ^ max J 1)] with N hN
  let m := Nat.log 4 N
  have hm : max J 1 ≤ m := Nat.le_log_of_pow_le (by decide) hN
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN0 : N ≠ 0 := by
    have hp : 0 < (4 : ℕ) ^ max J 1 := by positivity
    omega
  have hlo : 4 ^ m ≤ N := Nat.pow_log_le_self 4 hN0
  have hhi : N ^ 2 < 4 ^ (2 * (m + 1)) := by
    rw [mul_comm 2, pow_mul]
    have hp : N < 4 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide) N
    gcongr
  let I := Finset.Ico m (2 * (m + 1))
  let S := (Finset.Ioc N (N ^ 2)).filter (· ∈ A)
  let T (t : ℕ) := S.filter (fun x => Nat.log 4 x = t)
  have hU : I.biUnion T = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, -, hxt⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hxt).1
    · intro hx
      obtain ⟨hxlo, hxhi⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1
      refine Finset.mem_biUnion.mpr ⟨Nat.log 4 x, Finset.mem_Ico.mpr ⟨?_, ?_⟩,
        Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
      · exact Nat.le_log_of_pow_le (by decide) (hlo.trans hxlo.le)
      · exact Nat.log_lt_of_lt_pow (by omega) (hxhi.trans_lt hhi)
  have hdisj : Set.PairwiseDisjoint (I : Set ℕ) T := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact hne ((Finset.mem_filter.mp hxi).2.symm.trans (Finset.mem_filter.mp hxj).2)
  have hblock (t : ℕ) : (∑ x ∈ T t, (x : ℝ)⁻¹) ≤ 4 * blockDensity k t := by
    have hxBounds (x : ℕ) (hx : x ∈ T t) : 4 ^ t ≤ x ∧ x < 4 ^ (t + 1) := by
      obtain ⟨hxS, hxt⟩ := Finset.mem_filter.mp hx
      have hxN := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hxS).1).1
      rw [← hxt]
      exact ⟨Nat.pow_log_le_self 4 (by omega), Nat.lt_pow_succ_log_self (by decide) x⟩
    have hc : (T t).card ≤ 4 * r k (4 ^ t) := by
      refine (card_le_r (k := k) (N := 4 ^ (t + 1)) ?_ ?_).trans ?_
      · intro x hx
        have hxN := (Finset.mem_Ioc.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1
        exact Finset.mem_Icc.mpr ⟨by omega, (hxBounds x hx).2.le⟩
      · intro U hU hAP
        exact hA U (fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp (hU hx)).1).2) hAP
      · rw [pow_succ, mul_comm]
        exact r_mul_le hk _ 4
    calc
      _ ≤ ∑ _x ∈ T t, ((4 : ℝ) ^ t)⁻¹ := Finset.sum_le_sum fun x hx =>
        inv_anti₀ (by positivity) (by exact_mod_cast (hxBounds x hx).1)
      _ = ((T t).card : ℝ) / (4 : ℝ) ^ t := by simp [div_eq_mul_inv]
      _ ≤ _ := by
        rw [blockDensity, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  have hcardI : I.card = m + 2 := by dsimp [I]; rw [Nat.card_Ico]; omega
  have hcardR : (I.card : ℝ) ≤ 3 * (m : ℝ) := by
    exact_mod_cast (show I.card ≤ 3 * m by omega)
  calc
    squareWindowMass A N = ∑ x ∈ S, (x : ℝ)⁻¹ := by
      simp [squareWindowMass, S, Finset.sum_filter, Set.indicator]
    _ = ∑ t ∈ I, ∑ x ∈ T t, (x : ℝ)⁻¹ := by
      rw [← hU, Finset.sum_biUnion hdisj]
    _ ≤ ∑ _t ∈ I, ε / (3 * (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      have hmt := (Finset.mem_Ico.mp ht).1
      have hmtR : (m : ℝ) ≤ t := by exact_mod_cast hmt
      have hnonneg : 0 ≤ blockDensity k t := by unfold blockDensity; positivity
      have hle := (mul_le_mul_of_nonneg_right hmtR hnonneg).trans
        (hJ t (((le_max_left _ _).trans hm).trans hmt))
      refine (hblock t).trans ((le_div_iff₀ (by positivity)).mpr ?_)
      linarith only [hle]
    _ ≤ ε := by
      simp only [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).mpr
      exact mul_le_mul_of_nonneg_right hcardR hε.le |>.trans_eq (mul_comm _ _)

lemma littleO_iff_squareWindowDecay {k : ℕ} (hk : 3 ≤ k) :
    ((fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)) ↔
    ∀ A : Set ℕ, A.IsAPOfLengthFree k → SquareWindowDecay A := by
  constructor
  · intro h A hA
    exact squareWindowDecay_of_littleO (by omega) h hA
  · intro h
    obtain ⟨A, hA, -, hcontrol⟩ := exists_set_controlling_littleO hk
    exact hcontrol (h A hA)

lemma littleO_iff_supported_squareWindowDecay {k : ℕ} (hk : 3 ≤ k) :
    ((fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)) ↔
    ∀ A : Set ℕ, A.IsAPOfLengthFree k →
      (∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) → SquareWindowDecay A := by
  constructor
  · intro h A hA _
    exact (littleO_iff_squareWindowDecay hk).mp h A hA
  · intro h
    obtain ⟨A, hA, hsupport, hcontrol⟩ := exists_set_controlling_littleO hk
    exact hcontrol (h A hA hsupport)

lemma threeAPFree_iff {A : Set ℕ} :
    A.IsAPOfLengthFree ((3 : ℕ) : ℕ∞) ↔ ThreeAPFree A := by
  rw [apFree_iff (by decide : 1 < 3)]
  constructor
  · intro h a ha b hb c hc he
    have ordered {x y z : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
        (hxy : x < y) (hm : x + z = y + y) : False := by
      refine h ⟨x, y - x, by omega, fun i hi => ?_⟩
      interval_cases i
      · simpa using hx
      · rwa [one_mul, show x + (y - x) = y by omega]
      · rwa [show x + 2 * (y - x) = z by omega]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact ordered ha hb hc hab he
    · exact ordered hc hb ha (by omega) (by omega)
  · intro h
    rintro ⟨a, d, hd, hm⟩
    have h₀ : a ∈ A := by simpa using hm 0 (by decide)
    have h₁ : a + d ∈ A := by simpa using hm 1 (by decide)
    have h₂ : a + 2 * d ∈ A := hm 2 (by decide)
    have he := h h₀ h₁ h₂ (by omega)
    omega

lemma r_three_eq_roth (N : ℕ) : r 3 N = rothNumberNat N := by
  have he : Finset.Icc 1 N = (Finset.range N).map (addLeftEmbedding (1 : ℕ)) := by
    ext x
    rw [Finset.mem_Icc, Finset.mem_map]
    constructor
    · intro hx
      refine ⟨x - 1, Finset.mem_range.mpr (by omega), ?_⟩
      change 1 + (x - 1) = x
      omega
    · rintro ⟨y, hy, hyx⟩
      have hyn := Finset.mem_range.mp hy
      change 1 + y = x at hyx
      omega
  rw [rothNumberNat_def, ← addRothNumber_map_add_left _ 1, ← he]
  apply le_antisymm
  · obtain ⟨S, hS, hf, hcard⟩ := exists_maximizer (by decide : 1 < 3) N
    rw [hcard]
    exact (threeAPFree_iff.mp hf).le_addRothNumber hS
  · obtain ⟨S, hS, hcard, hf⟩ := addRothNumber_spec (Finset.Icc 1 N)
    rw [← hcard]
    exact card_le_r hS (threeAPFree_iff.mpr hf)

lemma three_littleO_linear :
    (fun N => (r 3 N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)) := by
  simpa only [r_three_eq_roth] using rothNumberNat_isLittleO_id

lemma littleO_of_stretched_exponential {k : ℕ} {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (h : ∀ᶠ N : ℕ in atTop, (r k N : ℝ) ≤
      N * Real.exp (-c * Real.log (N : ℝ) ^ a)) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay :
      Tendsto (fun N : ℕ => Real.log (N : ℝ) * Real.exp (-c * Real.log (N : ℝ) ^ a))
        atTop (𝓝 0) := by
    refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a⁻¹ c hc).comp
      ((tendsto_rpow_atTop ha).comp hlog)).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hp : 1 < (N : ℝ) := by exact_mod_cast hN
    change (Real.log (N : ℝ) ^ a) ^ a⁻¹ * _ = _
    rw [← Real.rpow_mul (Real.log_pos hp).le, mul_inv_cancel₀ ha.ne', Real.rpow_one]
    rfl
  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [h, (tendsto_order.mp hdecay).2 ε hε, eventually_gt_atTop (1 : ℕ)]
    with N hN hsmall hp
  have hl := Real.log_pos (show 1 < (N : ℝ) by exact_mod_cast hp)
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), ← mul_div_assoc, le_div_iff₀ hl]
  calc
    (r k N : ℝ) * Real.log (N : ℝ) ≤
        (N * Real.exp (-c * Real.log (N : ℝ) ^ a)) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hN hl.le
    _ = (Real.log (N : ℝ) * Real.exp (-c * Real.log (N : ℝ) ^ a)) * N := by ring
    _ ≤ ε * N := mul_le_mul_of_nonneg_right hsmall.le (by positivity)

lemma three_littleO_of_roth_estimate
    (h : ∃ c a : ℝ, 0 < c ∧ 0 < a ∧ ∀ᶠ N : ℕ in atTop, (rothNumberNat N : ℝ) ≤
      N * Real.exp (-c * Real.log (N : ℝ) ^ a)) :
    (fun N => (r 3 N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  obtain ⟨c, a, hc, ha, h⟩ := h
  exact littleO_of_stretched_exponential hc ha (by simpa only [r_three_eq_roth] using h)

def CyclicAPFree {q : ℕ} (k : ℕ) (S : Finset (ZMod q)) : Prop :=
  ¬ ∃ a d : ZMod q, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod q) * d ∈ S

lemma cyclic_image_free {k N q : ℕ} (hk : 1 < k) (hq : 2 * N < q)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N) (hfree : (S : Set ℕ).IsAPOfLengthFree k) :
    CyclicAPFree k (S.image (fun x : ℕ => (x : ZMod q))) := by
  have : NeZero q := ⟨by omega⟩
  classical
  rintro ⟨a, d, hd, hmem⟩
  let x (i : ℕ) := (a + (i : ZMod q) * d).val
  have hcast (i : ℕ) : (x i : ZMod q) = a + (i : ZMod q) * d :=
    ZMod.natCast_zmod_val _
  have hx (i : ℕ) (hi : i < k) : x i ∈ S := by
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp (hmem i hi)
    have hsN := (Finset.mem_Icc.mp (hS hs)).2
    have he' := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (show s < q by omega)] at he'
    change s = x i at he'
    exact he' ▸ hs
  have hxN (i : ℕ) (hi : i < k) : x i ≤ N := (Finset.mem_Icc.mp (hS (hx i hi))).2
  have hstep (i : ℕ) : (x (i + 1) : ZMod q) = (x i : ZMod q) + d := by
    simp only [hcast, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc]
  have hne : x 0 ≠ x 1 := by
    intro he
    have hd' := hstep 0
    rw [← he] at hd'
    exact hd (by simpa using hd'.symm)
  rw [apFree_iff hk] at hfree
  apply hfree
  have lift_eq {u v : ℕ} (hu : u < q) (hv : v < q) (h : (u : ZMod q) = v) : u = v := by
    simpa only [ZMod.val_natCast_of_lt hu, ZMod.val_natCast_of_lt hv] using congrArg ZMod.val h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let t := x 1 - x 0
    have ht : 0 < t := by dsimp [t]; omega
    have htN : t ≤ N := (Nat.sub_le ..).trans (hxN 1 hk)
    have htcast : (t : ZMod q) = d := by
      have he : x 0 + t = x 1 := by dsimp [t]; omega
      have hc := congrArg (fun n : ℕ => (n : ZMod q)) he
      rw [Nat.cast_add, hstep 0] at hc
      exact add_left_cancel hc
    have hnext (i : ℕ) (hi : i + 1 < k) : x (i + 1) = x i + t := by
      apply lift_eq (by have := hxN (i + 1) hi; omega) (by have := hxN i (by omega); omega)
      rw [hstep, Nat.cast_add, htcast]
    have he (i : ℕ) (hi : i < k) : x i = x 0 + i * t := by
      induction i with
      | zero => simp
      | succ i ih => rw [hnext i hi, ih (by omega), Nat.succ_mul, add_assoc]
    exact ⟨x 0, t, ht, fun i hi => he i hi ▸ hx i hi⟩
  · let t := x 0 - x 1
    have ht : 0 < t := by dsimp [t]; omega
    have htN : t ≤ N := (Nat.sub_le ..).trans (hxN 0 (by omega))
    have htcast : d + (t : ZMod q) = 0 := by
      have he : x 1 + t = x 0 := by dsimp [t]; omega
      have hc := congrArg (fun n : ℕ => (n : ZMod q)) he
      rw [Nat.cast_add, hstep 0, add_assoc] at hc
      exact add_left_cancel (hc.trans (add_zero _).symm)
    have hnext (i : ℕ) (hi : i + 1 < k) : x (i + 1) + t = x i := by
      apply lift_eq (by have := hxN (i + 1) hi; omega) (by have := hxN i (by omega); omega)
      rw [Nat.cast_add, hstep, add_assoc, htcast, add_zero]
    have he (i : ℕ) (hi : i < k) : x i + i * t = x 0 := by
      induction i with
      | zero => simp
      | succ i ih =>
        have hprev := ih (by omega)
        have hn := hnext i hi
        rw [Nat.succ_mul]
        omega
    refine ⟨x (k - 1), t, ht, fun i hi => ?_⟩
    have hm : k - 1 - i + i = k - 1 := by omega
    have hmul : (k - 1 - i) * t + i * t = (k - 1) * t := by rw [← Nat.add_mul, hm]
    have h₁ := he (k - 1) (by omega)
    have h₂ := he (k - 1 - i) (by omega)
    have hEq : x (k - 1) + i * t = x (k - 1 - i) := by omega
    rw [hEq]
    exact hx _ (by omega)

lemma exists_cyclic_extremal_set {k N q : ℕ} (hk : 1 < k) (hq : 2 * N < q) :
    ∃ S : Finset (ZMod q), CyclicAPFree k S ∧ S.card = r k N := by
  obtain ⟨S, hS, hfree, hcard⟩ := exists_maximizer hk N
  refine ⟨S.image (fun x : ℕ => (x : ZMod q)), cyclic_image_free hk hq hS hfree, ?_⟩
  rw [hcard]
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  have haN := (Finset.mem_Icc.mp (hS ha)).2
  have hbN := (Finset.mem_Icc.mp (hS hb)).2
  simpa only [ZMod.val_natCast_of_lt (show a < q by omega),
    ZMod.val_natCast_of_lt (show b < q by omega)] using congrArg ZMod.val he

lemma cyclic_card_le_r {k q : ℕ} (hk : 1 < k) [NeZero q]
    {S : Finset (ZMod q)} (hS : CyclicAPFree k S) : S.card ≤ r k q := by
  let f : ZMod q ↪ ℕ := ⟨fun a => a.val + 1, fun a b h =>
    ZMod.val_injective q (Nat.add_right_cancel h)⟩
  rw [← Finset.card_map f]
  apply card_le_r
  · intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hn
    have hzq := ZMod.val_lt z
    exact Finset.mem_Icc.mpr ⟨by change 1 ≤ z.val + 1; omega,
      by change z.val + 1 ≤ q; omega⟩
  · rw [apFree_iff hk]
    rintro ⟨a, t, ht, hmem⟩
    have ha : 1 ≤ a := by
      obtain ⟨z, hz, he⟩ := Finset.mem_map.mp (hmem 0 (by omega))
      change z.val + 1 = a + 0 * t at he
      omega
    have htq : t < q := by
      obtain ⟨z, hz, he⟩ := Finset.mem_map.mp (hmem 1 hk)
      change z.val + 1 = a + 1 * t at he
      have hval := ZMod.val_lt z
      omega
    refine hS ⟨((a - 1 : ℕ) : ZMod q), (t : ZMod q), ?_, fun i hi => ?_⟩
    · intro he
      have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt htq, ZMod.val_zero] at hv
      omega
    · obtain ⟨z, hz, he⟩ := Finset.mem_map.mp (hmem i hi)
      change z.val + 1 = a + i * t at he
      have hzval : z.val = (a - 1) + i * t := by omega
      rw [← ZMod.natCast_zmod_val z, hzval, Nat.cast_add, Nat.cast_mul] at hz
      exact hz

def PrimeCyclicBound (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop, q.Prime →
    ∀ S : Finset (ZMod q), CyclicAPFree k S → (S.card : ℝ) ≤ ε * (q / Real.log q)

lemma littleO_iff_primeCyclicBound {k : ℕ} (hk : 1 < k) :
    ((fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)) ↔
    PrimeCyclicBound k := by
  constructor
  · intro h ε hε
    filter_upwards [h.def hε] with q hq hprime S hS
    have : NeZero q := ⟨hprime.ne_zero⟩
    have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)] at hq
    exact (by exact_mod_cast cyclic_card_le_r hk hS : (S.card : ℝ) ≤ r k q).trans hq
  · intro h
    rw [isLittleO_iff]
    intro ε hε
    obtain ⟨Q, hQ⟩ := eventually_atTop.mp (h (ε / 4) (by positivity))
    filter_upwards [eventually_ge_atTop (max Q 2)] with N hN
    have hNQ : Q ≤ N := (le_max_left _ _).trans hN
    have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
    obtain ⟨p, hp, hpLo, hpHi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
    obtain ⟨S, hS, hcard⟩ := exists_cyclic_extremal_set hk hpLo
    have hbound := hQ p (by omega) hp S hS
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos
      (by exact_mod_cast (show 1 < N by omega))
    have hlogLe : Real.log (N : ℝ) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show N ≤ p by omega))
    have hpR : (p : ℝ) ≤ 4 * (N : ℝ) := by
      exact_mod_cast (show p ≤ 4 * N by omega)
    have hscale : (p : ℝ) / Real.log p ≤ 4 * ((N : ℝ) / Real.log N) := by
      calc
        _ ≤ (p : ℝ) / Real.log N := div_le_div_of_nonneg_left (by positivity) hlogN hlogLe
        _ ≤ (4 * (N : ℝ)) / Real.log N := div_le_div_of_nonneg_right hpR hlogN.le
        _ = _ := mul_div_assoc _ _ _
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), ← hcard]
    calc
      _ ≤ (ε / 4) * ((p : ℝ) / Real.log p) := hbound
      _ ≤ (ε / 4) * (4 * ((N : ℝ) / Real.log N)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring

lemma cyclic_threeAPFree_iff {q : ℕ} {S : Finset (ZMod q)} :
    CyclicAPFree 3 S ↔ ThreeAPFree (S : Set (ZMod q)) := by
  constructor
  · intro h a ha b hb c hc he
    by_contra hne
    refine h ⟨a, b - a, sub_ne_zero.mpr (Ne.symm hne), fun i hi => ?_⟩
    interval_cases i
    · simpa using ha
    · have hterm : a + (1 : ZMod q) * (b - a) = b := by ring
      simpa only [Nat.cast_one, hterm] using (show b ∈ S from hb)
    · have hterm : a + (2 : ZMod q) * (b - a) = c := by linear_combination -he
      simpa only [Nat.cast_ofNat, hterm] using (show c ∈ S from hc)
  · intro h
    rintro ⟨a, d, hd, hmem⟩
    have ha : a ∈ S := by simpa using hmem 0 (by decide)
    have hb : a + d ∈ S := by simpa using hmem 1 (by decide)
    have hc : a + 2 * d ∈ S := by simpa using hmem 2 (by decide)
    have he := h ha hb hc (by ring)
    exact hd (add_left_cancel (he.symm.trans (add_zero a).symm))

lemma littleO_three_iff_primeRothBound :
    ((fun N => (r 3 N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop, ∀ hq : q.Prime,
      letI : NeZero q := ⟨hq.ne_zero⟩
      (addRothNumber (Finset.univ : Finset (ZMod q)) : ℝ) ≤ ε * (q / Real.log q) := by
  rw [littleO_iff_primeCyclicBound (by decide : 1 < 3)]
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with q hq hprime
    have : NeZero q := ⟨hprime.ne_zero⟩
    change (addRothNumber (Finset.univ : Finset (ZMod q)) : ℝ) ≤ _
    obtain ⟨S, -, hcard, hfree⟩ := addRothNumber_spec (Finset.univ : Finset (ZMod q))
    rw [← hcard]
    exact hq hprime S (cyclic_threeAPFree_iff.mpr hfree)
  · intro h ε hε
    filter_upwards [h ε hε] with q hq hprime S hS
    have : NeZero q := ⟨hprime.ne_zero⟩
    have hc : S.card ≤ addRothNumber (Finset.univ : Finset (ZMod q)) :=
      (cyclic_threeAPFree_iff.mp hS).le_addRothNumber (Finset.subset_univ _)
    exact (by exact_mod_cast hc :
      (S.card : ℝ) ≤ addRothNumber (Finset.univ : Finset (ZMod q))).trans (hq hprime)

lemma r_two_le_one (N : ℕ) : r 2 N ≤ 1 := by
  unfold r Set.IsAPOfLengthFree.maxCard
  apply csSup_le
  · refine ⟨0, ∅, by simp, ?_, Finset.card_empty⟩
    intro T hT hAP
    have he : T = ∅ := Set.eq_empty_of_subset_empty (by simpa using hT)
    subst T
    exact (Set.not_isAPOfLength_empty (by decide) hAP).elim
  · rintro m ⟨S, -, hfree, rfl⟩
    by_contra! hc
    obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp hc
    have noPair {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : False := by
      have hs : ({x, y} : Set ℕ) ⊆ (S : Set ℕ) :=
        Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩
      exact (by decide : ¬ (2 : ℕ∞) ≤ 1) (hfree _ hs (Nat.isAPOfLength_pair hxy))
    exact (lt_or_gt_of_ne hne).elim (noPair ha hb) (noPair hb ha)

lemma two_littleO :
    (fun N => (r 2 N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  have hlog :
      Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
    apply isLittleO_of_tendsto'
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
      have hp : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      exact fun h => (div_pos (zero_lt_one.trans hp) (Real.log_pos hp)).ne' h |>.elim
    · simpa only [one_div, inv_div] using hlog
  apply IsBigO.trans_isLittleO _ hc
  apply IsBigO.of_bound 1
  exact Eventually.of_forall fun N => by simpa using (show (r 2 N : ℝ) ≤ 1 by
    exact_mod_cast r_two_le_one N)

end OMA.Erdos142Lower

theorem OMA.solution : type_of% @Erdos142.erdos_142.variants.lower := by
  intro k hk
  rcases eq_or_lt_of_le (show 2 ≤ k by omega) with rfl | hk'
  · exact OMA.Erdos142Lower.two_littleO
  apply (OMA.Erdos142Lower.littleO_iff_supported_squareWindowDecay (by omega)).mpr
  sorry

