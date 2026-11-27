import FormalConjectures.ErdosProblems.«142»
import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Combinatorics.Additive.Corner.Roth

/-! Transfer the Mathlib bounds for Roth numbers to the Erdős 142 extremal function. -/

namespace Erdos142Three

open Asymptotics Filter
open scoped Topology

private lemma progression_shape (a d : ℕ) :
    {a + i • d | (i : ℕ) (_ : i < (3 : ℕ∞))} = ({a, a + d, a + 2 * d} : Set ℕ) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < 3 := by exact_mod_cast hi
    interval_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩
    · exact ⟨2, by decide, by simp⟩

private lemma mem_midpoint_eq {S : Set ℕ} (hS : S.IsAPOfLengthFree 3)
    {a b c : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≤ b) (h : a + c = b + b) : a = b := by
  by_contra hne
  let d := b - a
  have hd : 0 < d := by omega
  have hb' : a + d = b := by omega
  have hc' : a + 2 * d = c := by omega
  have hAP : ({a, b, c} : Set ℕ).IsAPOfLength 3 := by
    refine ⟨a, d, ?_, ?_⟩
    · rw [ENat.card_coe_set_eq, Set.encard_insert_of_notMem, Set.encard_pair (by omega : b ≠ c)]
      · rfl
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
    · rw [progression_shape, hb', hc']
  have hSub : ({a, b, c} : Set ℕ) ⊆ S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  exact (by decide : ¬ (3 : ℕ∞) ≤ 1) (hS _ hSub hAP)

theorem threeAPFree_iff {S : Set ℕ} : ThreeAPFree S ↔ S.IsAPOfLengthFree 3 := by
  constructor
  · intro h S' hsub hAP
    obtain ⟨a, d, hcard, hshape⟩ := hAP
    rw [progression_shape] at hshape
    have hd : d = 0 := by
      have heq := h (hsub (by simp [hshape])) (hsub (by simp [hshape]))
        (hsub (by simp [hshape])) (by omega : a + (a + 2 * d) = (a + d) + (a + d))
      omega
    simp [hd] at hshape
    simp [hshape] at hcard
  · intro h a ha b hb c hc heq
    by_cases hab : a ≤ b
    · exact mem_midpoint_eq h ha hb hc hab heq
    · have hcb : c ≤ b := by omega
      have hcb' := mem_midpoint_eq h hc hb ha hcb (by omega)
      omega

theorem maxCard_three_eq_rothNumberNat (N : ℕ) : Erdos142.r 3 N = rothNumberNat N := by
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp
  rw [Erdos142.r, Set.IsAPOfLengthFree.maxCard]
  have hRoth : addRothNumber (Finset.Icc 1 N) = rothNumberNat N := by
    rw [hIcc, addRothNumber_Ico]
    simp
  rw [← hRoth]
  obtain ⟨T, hT, hcard, hfree⟩ := addRothNumber_spec (Finset.Icc 1 N)
  apply le_antisymm
  · apply csSup_le'
    rintro _ ⟨S, hS, hfree, rfl⟩
    exact (threeAPFree_iff.mpr hfree).le_addRothNumber hS
  · apply le_csSup
    · refine ⟨N, ?_⟩
      rintro _ ⟨S, hS, _, rfl⟩
      exact (Finset.card_mono hS).trans_eq (Nat.card_Icc 1 N)
    · exact ⟨T, hT, threeAPFree_iff.mp hfree, hcard⟩

theorem maxCard_three_lower_bound (N : ℕ) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤ (Erdos142.r 3 N : ℝ) := by
  rw [maxCard_three_eq_rothNumberNat]
  exact Behrend.roth_lower_bound

theorem maxCard_three_isLittleO :
    (fun N : ℕ ↦ (Erdos142.r 3 N : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [maxCard_three_eq_rothNumberNat] using rothNumberNat_isLittleO_id

private theorem eventually_rpow_le_maxCard_three {β : ℝ} (hβ : β < 1) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ β ≤ (Erdos142.r 3 N : ℝ) := by
  let δ := 1 - β
  have hδ : 0 < δ := sub_pos.mpr hβ
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlog.eventually_ge_atTop ((4 / δ) ^ 2)]
    with N hN hlarge
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hln : 0 ≤ Real.log (N : ℝ) := (sq_nonneg _).trans hlarge
  have hsqrt : 4 / δ ≤ Real.sqrt (Real.log (N : ℝ)) := by
    simpa [Real.sqrt_sq (by positivity : 0 ≤ 4 / δ)] using Real.sqrt_le_sqrt hlarge
  have hfour : 4 ≤ δ * Real.sqrt (Real.log (N : ℝ)) := by
    simpa [mul_comm] using (div_le_iff₀ hδ).mp hsqrt
  have hmul : 4 * Real.sqrt (Real.log (N : ℝ)) ≤ δ * Real.log (N : ℝ) := calc
    _ ≤ (δ * Real.sqrt (Real.log (N : ℝ))) * Real.sqrt (Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hfour (Real.sqrt_nonneg _)
    _ = _ := by rw [mul_assoc, Real.mul_self_sqrt hln]
  calc
    (N : ℝ) ^ β = Real.exp (Real.log (N : ℝ) * β) := Real.rpow_def_of_pos hN' _
    _ ≤ Real.exp (Real.log (N : ℝ) - 4 * Real.sqrt (Real.log (N : ℝ))) := by
      apply Real.exp_le_exp.mpr
      dsimp [δ] at hmul
      linarith
    _ = (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (N : ℝ))) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hN']
      ring_nf
    _ ≤ (Erdos142.r 3 N : ℝ) := maxCard_three_lower_bound N

theorem rpow_isLittleO_maxCard_three {α : ℝ} (hα : α < 1) :
    (fun N : ℕ ↦ (N : ℝ) ^ α) =o[atTop] (fun N ↦ (Erdos142.r 3 N : ℝ)) := by
  let δ : ℝ := (1 - α) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hαδ : α + δ < 1 := by dsimp [δ]; linarith
  have hsmall : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [eventually_gt_atTop (0 : ℕ), hsmall.eventually (gt_mem_nhds hc),
    eventually_rpow_le_maxCard_three hαδ] with N hN hsmallN hlarge
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hN'.le _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  calc
    (N : ℝ) ^ α = (N : ℝ) ^ (-δ) * (N : ℝ) ^ (α + δ) := by
      rw [← Real.rpow_add hN']
      congr 1
      ring
    _ ≤ c * (Erdos142.r 3 N : ℝ) :=
      mul_le_mul hsmallN.le hlarge (Real.rpow_nonneg hN'.le _) hc.le

theorem not_equivalent_rpow (α : ℝ) :
    ¬ (fun N : ℕ ↦ (Erdos142.r 3 N : ℝ)) ~[atTop] (fun N : ℕ ↦ (N : ℝ) ^ α) := by
  intro h
  have hfreq : ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ α ≠ 0 := by
    apply Eventually.frequently
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hN) _).ne'
  by_cases hα : α < 1
  · exact (rpow_isLittleO_maxCard_three hα).not_isBigO hfreq h.isBigO
  · have hbig : (fun N : ℕ ↦ (N : ℝ)) =O[atTop] (fun N : ℕ ↦ (N : ℝ) ^ α) := by
      refine (IsBigOWith.of_bound (c := 1) ?_).isBigO
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
      have hN' : 1 ≤ (N : ℝ) := by exact_mod_cast hN
      rw [one_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      simpa using Real.rpow_le_rpow_of_exponent_le hN' (le_of_not_gt hα)
    exact isLittleO_irrefl hfreq (h.symm.trans_isLittleO (maxCard_three_isLittleO.trans_isBigO hbig))

theorem maxCard_three_mul_le (m n : ℕ) :
    Erdos142.r 3 m * Erdos142.r 3 n ≤ Erdos142.r 3 (2 * m * n) := by
  simp_rw [maxCard_three_eq_rothNumberNat]
  by_cases hm : m = 0
  · simp [hm]
  obtain ⟨S, hS, hScard, hSfree⟩ := rothNumberNat_spec m
  obtain ⟨T, hT, hTcard, hTfree⟩ := rothNumberNat_spec n
  classical
  let b := 2 * m
  have hb : 0 < b := by dsimp [b]; omega
  let encode (p : ℕ × ℕ) := p.1 + b * p.2
  have hcoords {p q u v : ℕ × ℕ} (hp : p.1 + q.1 < b) (hu : u.1 + v.1 < b)
      (heq : encode p + encode q = encode u + encode v) :
      p.1 + q.1 = u.1 + v.1 ∧ p.2 + q.2 = u.2 + v.2 := by
    have heq' : p.1 + q.1 + b * (p.2 + q.2) = u.1 + v.1 + b * (u.2 + v.2) := by
      simpa only [encode, mul_add, add_add_add_comm] using heq
    have hf := congrArg (· % b) heq'
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hu] at hf
    refine ⟨hf, ?_⟩
    rw [hf, Nat.add_left_cancel_iff, Nat.mul_left_cancel_iff hb] at heq'
    exact heq'
  have hfst {p : ℕ × ℕ} (h : p ∈ S ×ˢ T) : p.1 < m :=
    Finset.mem_range.mp (hS (Finset.mem_product.mp h).1)
  have hsnd {p : ℕ × ℕ} (h : p ∈ S ×ˢ T) : p.2 < n :=
    Finset.mem_range.mp (hT (Finset.mem_product.mp h).2)
  let U := (S ×ˢ T).image encode
  have hUcard : U.card = rothNumberNat m * rothNumberNat n := by
    rw [Finset.card_image_of_injOn, Finset.card_product, hScard, hTcard]
    intro p hp q hq h
    have h' := hcoords (p := p) (q := p) (u := q) (v := q)
      (by have := hfst hp; dsimp [b]; omega)
      (by have := hfst hq; dsimp [b]; omega) (congrArg (fun k => k + k) h)
    exact Prod.ext (by have := h'.1; omega) (by have := h'.2; omega)
  have hUfree : ThreeAPFree (U : Set ℕ) := by
    intro x hx y hy z hz h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h₁, h₂⟩ := hcoords (p := p) (q := s) (u := q) (v := q)
      (by have := hfst hp; have := hfst hs; dsimp [b]; omega)
      (by have := hfst hq; dsimp [b]; omega) h
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    obtain ⟨hs₁, hs₂⟩ := Finset.mem_product.mp hs
    exact congrArg encode (Prod.ext (hSfree hp₁ hq₁ hs₁ h₁) (hTfree hp₂ hq₂ hs₂ h₂))
  apply hUfree.le_rothNumberNat U _ hUcard
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  change p.1 + b * p.2 < b * n
  have hlt : p.1 < b := by have := hfst hp; dsimp [b]; omega
  calc
    p.1 + b * p.2 < b + b * p.2 := Nat.add_lt_add_right hlt _
    _ = b * (p.2 + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ b * n := Nat.mul_le_mul_left _ (hsnd hp)

theorem maxCard_three_tendsto_atTop :
    Tendsto (fun N : ℕ ↦ (Erdos142.r 3 N : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono' _ (eventually_rpow_le_maxCard_three (by norm_num)) hpow

theorem maxCard_three_shift_isEquivalent {ι : Type*} {l : Filter ι} {L K : ι → ℕ}
    (hK : (fun i ↦ (K i : ℝ)) =o[l] (fun i ↦ (L i : ℝ))) :
    (fun i ↦ (Erdos142.r 3 (L i + K i) : ℝ)) ~[l] (fun i ↦ (Erdos142.r 3 (L i) : ℝ)) := by
  change (fun i ↦ (Erdos142.r 3 (L i + K i) : ℝ) - (Erdos142.r 3 (L i) : ℝ)) =o[l] _
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨m, hm⟩ :=
    ((maxCard_three_tendsto_atTop.eventually_ge_atTop c⁻¹).and
      (eventually_gt_atTop (0 : ℕ))).exists
  have hmpos : 0 < m := hm.2
  have hbase : 0 < (2 : ℝ) * m := by positivity
  have hK' := isLittleO_iff.mp hK (inv_pos.mpr hbase)
  filter_upwards [hK'] with i hi
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hi
  have hmulNat : 2 * m * K i ≤ L i := by
    exact_mod_cast (le_inv_mul_iff₀ hbase).mp hi
  have hprod : (Erdos142.r 3 m : ℝ) * (Erdos142.r 3 (K i) : ℝ) ≤ (Erdos142.r 3 (L i) : ℝ) := by
    exact_mod_cast (maxCard_three_mul_le m (K i)).trans
      (by simpa only [maxCard_three_eq_rothNumberNat] using rothNumberNat.monotone hmulNat)
  have hdiff : (Erdos142.r 3 (L i + K i) : ℝ) - (Erdos142.r 3 (L i) : ℝ) ≤
      (Erdos142.r 3 (K i) : ℝ) := by
    apply sub_le_iff_le_add.mpr
    rw [add_comm (Erdos142.r 3 (K i) : ℝ)]
    simp_rw [maxCard_three_eq_rothNumberNat]
    exact_mod_cast rothNumberNat_add_le (L i) (K i)
  have hmono : (Erdos142.r 3 (L i) : ℝ) ≤ (Erdos142.r 3 (L i + K i) : ℝ) := by
    rw [maxCard_three_eq_rothNumberNat, maxCard_three_eq_rothNumberNat]
    exact_mod_cast rothNumberNat.monotone (Nat.le_add_right (L i) (K i))
  rw [Real.norm_of_nonneg (sub_nonneg.mpr hmono), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  refine hdiff.trans ((inv_mul_le_iff₀ hc).mp ?_)
  exact (mul_le_mul_of_nonneg_right hm.1 (Nat.cast_nonneg _)).trans hprod

theorem maxCard_three_reindex_isEquivalent {ι : Type*} {l : Filter ι} {L M : ι → ℕ}
    (h : (fun i ↦ (M i : ℝ)) ~[l] (fun i ↦ (L i : ℝ))) :
    (fun i ↦ (Erdos142.r 3 (M i) : ℝ)) ~[l] (fun i ↦ (Erdos142.r 3 (L i) : ℝ)) := by
  have hmax {L M : ι → ℕ}
      (hLM : (fun i ↦ (M i : ℝ)) ~[l] (fun i ↦ (L i : ℝ))) :
      (fun i ↦ (Erdos142.r 3 (max (L i) (M i)) : ℝ)) ~[l]
        (fun i ↦ (Erdos142.r 3 (L i) : ℝ)) := by
    have hdiff : (fun i ↦ ((M i - L i : ℕ) : ℝ)) =o[l] (fun i ↦ (L i : ℝ)) := by
      rw [isLittleO_iff]
      intro c hc
      filter_upwards [isLittleO_iff.mp hLM.isLittleO hc] with i hi
      by_cases hle : L i ≤ M i
      · simpa only [Nat.cast_sub hle, Pi.sub_apply] using hi
      · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle), Nat.cast_zero, norm_zero]
        positivity
    refine (maxCard_three_shift_isEquivalent hdiff).congr_left (.of_forall fun i ↦ ?_)
    have heq : L i + (M i - L i) = max (L i) (M i) := by omega
    simp only [heq]
  exact ((hmax (L := M) (M := L) h.symm).congr_left (.of_forall fun i ↦ by
    rw [max_comm])).symm.trans (hmax h)

/-- An asymptotic equivalent along squares extends to all inputs by rounding down. -/
theorem maxCard_three_squares_iff {f : ℕ → ℝ} :
    ((fun n : ℕ ↦ (Erdos142.r 3 (n ^ 2) : ℝ)) ~[atTop] f) ↔
    ((fun N : ℕ ↦ (Erdos142.r 3 N : ℝ)) ~[atTop] (fun N ↦ f N.sqrt)) := by
  have hsqrt : Tendsto Nat.sqrt atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun k ↦ ⟨k ^ 2, fun N hN ↦ ?_⟩
    exact Nat.le_sqrt'.mpr hN
  have hround : (fun N : ℕ ↦ ((N.sqrt ^ 2 : ℕ) : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)) := by
    change (fun N : ℕ ↦ ((N.sqrt ^ 2 : ℕ) : ℝ) - (N : ℝ)) =o[atTop] _
    rw [isLittleO_iff]
    intro c hc
    have hlarge : Tendsto (fun N : ℕ ↦ (N.sqrt : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsqrt
    filter_upwards [hlarge.eventually_ge_atTop (2 / c)] with N hN
    have hsq : (N.sqrt : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast Nat.sqrt_le' N
    have hgap : (N : ℝ) ≤ (N.sqrt : ℝ) ^ 2 + (N.sqrt : ℝ) + (N.sqrt : ℝ) := by
      exact_mod_cast (by simpa only [pow_two] using Nat.sqrt_le_add N :
        N ≤ N.sqrt ^ 2 + N.sqrt + N.sqrt)
    have hmul : 2 ≤ c * (N.sqrt : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hc).mp hN
    rw [Nat.cast_pow, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hsq),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc
      -((N.sqrt : ℝ) ^ 2 - (N : ℝ)) ≤ 2 * (N.sqrt : ℝ) := by linarith
      _ ≤ (c * (N.sqrt : ℝ)) * (N.sqrt : ℝ) := mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = c * (N.sqrt : ℝ) ^ 2 := by ring
      _ ≤ c * (N : ℝ) := mul_le_mul_of_nonneg_left hsq hc.le
  constructor
  · intro h
    exact (maxCard_three_reindex_isEquivalent hround).symm.trans (h.comp_tendsto hsqrt)
  · intro h
    have hsquare : Tendsto (fun n : ℕ ↦ n ^ 2) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ by simpa only [id_eq, pow_two] using Nat.le_mul_self n)
        tendsto_id
    have h' := h.comp_tendsto hsquare
    change (fun n : ℕ ↦ (Erdos142.r 3 (n ^ 2) : ℝ)) ~[atTop] (fun n ↦ f (n ^ 2).sqrt) at h'
    simpa only [Nat.sqrt_eq'] using h'

end Erdos142Three

-- Problem: Erdős Problem 142 — three (it asks for a value)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/142.lean:78 (declaration Erdos142.erdos_142.variants.three; placeholder Erdos142.erdos_142.variants.three.answer := sorry)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Give the value explicitly as OMA.answer (same type as the placeholder; not built from Erdos142.…,
-- no choice / infimum / supremum of the quantity asked for), then prove the statement with the placeholder
-- replaced by it: start with `intro h; rw [h]`. No sorry, no axiom, no native_decide. A person checks the answer.

noncomputable def OMA.answer : ℕ → ℝ := sorry

theorem OMA.solution : Erdos142.erdos_142.variants.three.answer = OMA.answer → type_of% @Erdos142.erdos_142.variants.three := by
  intro h
  rw [h]
  sorry
