import FormalConjectures.ErdosProblems.«107»
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Height

-- Problem: Erdős Problem 107 — hmpt bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/107.lean:171 (declaration Erdos107.variants.hmpt_bound)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Finite cardinality thresholds for the Erdős–Szekeres asymptotic bound. -/

open Filter
open scoped Asymptotics EuclideanGeometry ENat BigOperators

namespace HMPT

private theorem cardSet_mono_polygon {m n N : ℕ} (hmn : m ≤ n)
    (hN : N ∈ Erdos107.cardSet n) : N ∈ Erdos107.cardSet m := by
  intro X hX hgp
  obtain ⟨Y, hY, hYX, hconv⟩ := hN X hX hgp
  obtain ⟨Z, hZY, hZ⟩ := Finset.exists_subset_card_eq (hY ▸ hmn)
  have hsub : (Z : Set ℝ²) ⊆ Y := hZY
  refine ⟨Z, hZ, hsub.trans hYX, ?_⟩
  intro z hz hmem
  have hdiff : (Z : Set ℝ²) \ {z} ⊆ (Y : Set ℝ²) \ {z} :=
    fun _ hw => ⟨hsub hw.1, hw.2⟩
  exact hconv z (hsub hz) (convexHull_mono hdiff hmem)

private noncomputable def scale (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) * Real.log n)

private theorem of_eventually_cardSet (r : ℕ → ℝ)
    (hr : r =O[atTop] scale)
    (he : ∀ᶠ n : ℕ in atTop, ∃ N ∈ Erdos107.cardSet n, (N : ℝ) ≤ 2 ^ ((n : ℝ) + r n)) :
    ∃ s : ℕ → ℝ, s =O[atTop] scale ∧ ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ 2 ^ ((n : ℝ) + s n) := by
  obtain ⟨m, hm⟩ := eventually_atTop.1 he
  obtain ⟨M, hM, _⟩ := hm m le_rfl
  let s (n : ℕ) : ℝ := if m ≤ n then r n else M
  refine ⟨s, ?_, fun n _ => ?_⟩
  · obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.1 hr
    refine Asymptotics.isBigO_iff.2 ⟨c, ?_⟩
    filter_upwards [eventually_ge_atTop m, hc] with n hn hcn
    simpa only [s, if_pos hn] using hcn
  · by_cases hn : m ≤ n
    · obtain ⟨N, hN, hbound⟩ := hm n hn
      have hf : (Erdos107.f n : ℝ) ≤ N := by exact_mod_cast Nat.sInf_le hN
      simpa only [s, if_pos hn] using hf.trans hbound
    · have hf : (Erdos107.f n : ℝ) ≤ M := by
        exact_mod_cast Nat.sInf_le (cardSet_mono_polygon (le_of_not_ge hn) hM)
      have hpow : (M : ℝ) ≤ (2 : ℝ) ^ (M : ℝ) := by
        rw [Real.rpow_natCast]
        exact_mod_cast (Nat.lt_two_pow_self (n := M)).le
      have hrpow : (2 : ℝ) ^ (M : ℝ) ≤ 2 ^ ((n : ℝ) + M) := by
        apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
        exact le_add_of_nonneg_left (Nat.cast_nonneg n)
      simpa only [s, if_neg hn] using hf.trans (hpow.trans hrpow)

private noncomputable def balancedParameter (n : ℕ) : ℕ :=
  ⌈Real.sqrt ((n : ℝ) / Real.log n)⌉₊

private theorem balancedParameter_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ balancedParameter n := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hs : 0 < Real.sqrt ((n : ℝ) / Real.log n) :=
    Real.sqrt_pos.2 (div_pos (by positivity) hlog)
  have hceil := Nat.le_ceil (Real.sqrt ((n : ℝ) / Real.log n))
  have hk : (0 : ℝ) < (balancedParameter n : ℝ) := hs.trans_le hceil
  exact_mod_cast hk

private theorem balancedParameter_bound {n : ℕ} (hn : 2 ≤ n) :
    (balancedParameter n : ℝ) * Real.log n + (n : ℝ) / balancedParameter n ≤ 3 * scale n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans hn'
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn'
  have hlogn : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
  let s := Real.sqrt ((n : ℝ) / Real.log n)
  let k : ℝ := balancedParameter n
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos hnpos hlog)
  have hsk : s ≤ k := Nat.le_ceil _
  have hks : k ≤ s + 1 := (Nat.ceil_lt_add_one hs.le).le
  have hsq : s ^ 2 = (n : ℝ) / Real.log n := Real.sq_sqrt (div_nonneg hnpos.le hlog.le)
  have hprod : (s * Real.log (n : ℝ)) * s = n := by
    calc
      (s * Real.log (n : ℝ)) * s = s ^ 2 * Real.log (n : ℝ) := by ring
      _ = n := by rw [hsq, div_mul_cancel₀ _ hlog.ne']
  have hidentity : s * Real.log (n : ℝ) = scale n := by
    dsimp only [scale]
    have hsq' : (s * Real.log (n : ℝ)) ^ 2 = (n : ℝ) * Real.log (n : ℝ) := by
      calc
        (s * Real.log (n : ℝ)) ^ 2 = ((s * Real.log (n : ℝ)) * s) * Real.log (n : ℝ) := by ring
        _ = (n : ℝ) * Real.log (n : ℝ) := by rw [hprod]
    rw [← hsq', Real.sqrt_sq (mul_nonneg hs.le hlog.le)]
  have hg : Real.log (n : ℝ) ≤ scale n := by
    unfold scale
    apply (Real.le_sqrt hlog.le (mul_nonneg hnpos.le hlog.le)).2
    simpa only [pow_two, mul_comm] using mul_le_mul_of_nonneg_right hlogn hlog.le
  have hd : (n : ℝ) / k ≤ scale n := by
    apply (div_le_iff₀ (hs.trans_le hsk)).2
    calc
      (n : ℝ) = (s * Real.log (n : ℝ)) * s := hprod.symm
      _ ≤ (s * Real.log (n : ℝ)) * k := mul_le_mul_of_nonneg_left hsk (mul_nonneg hs.le hlog.le)
      _ = scale n * k := by rw [hidentity]
  have hklog := mul_le_mul_of_nonneg_right hks hlog.le
  rw [add_mul, hidentity, one_mul] at hklog
  change k * Real.log (n : ℝ) + (n : ℝ) / k ≤ 3 * scale n
  linarith

private theorem of_eventually_balanced_cardSet {C : ℝ} (hC : 0 ≤ C)
    (he : ∀ᶠ n : ℕ in atTop, ∃ N ∈ Erdos107.cardSet n,
      (N : ℝ) ≤ 2 ^ ((n : ℝ) + C *
        ((balancedParameter n : ℝ) * Real.log n + (n : ℝ) / balancedParameter n))) :
    ∃ s : ℕ → ℝ, s =O[atTop] scale ∧ ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ 2 ^ ((n : ℝ) + s n) := by
  apply of_eventually_cardSet (fun n => (3 * C) * scale n)
  · refine Asymptotics.isBigO_iff.2 ⟨3 * C, Eventually.of_forall fun n => ?_⟩
    rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (by norm_num) hC)]
  · filter_upwards [eventually_ge_atTop (2 : ℕ), he] with n hn h
    obtain ⟨N, hN, hbound⟩ := h
    refine ⟨N, hN, hbound.trans ((Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 ?_)⟩
    have hmul := mul_le_mul_of_nonneg_left (balancedParameter_bound hn) hC
    linarith only [hmul]

private theorem one_le_scale {n : ℕ} (hn : 2 ≤ n) : 1 ≤ scale n := by
  have hcast : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlin : (1 / 2 : ℝ) ≤ Real.log 2 := by
    calc
      (1 / 2 : ℝ) = 1 - (2 : ℝ)⁻¹ := by norm_num
      _ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hlog := hlin.trans (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hcast)
  unfold scale
  apply Real.le_sqrt_of_sq_le
  calc
    (1 : ℝ) ^ 2 = 2 * (1 / 2) := by norm_num
    _ ≤ (n : ℝ) * Real.log n := mul_le_mul hcast hlog (by norm_num) (by positivity)

private noncomputable def threshold (C : ℝ) (n : ℕ) : ℝ :=
  2 ^ ((n : ℝ) + C * ((balancedParameter n : ℝ) * Real.log n + (n : ℝ) / balancedParameter n))

private theorem of_eventually_planar_bound {C : ℝ} (hC : 0 ≤ C)
    (he : ∀ᶠ n : ℕ in atTop, ∀ X : Finset ℝ², EuclideanGeometry.NonTrilinear (X : Set ℝ²) →
      threshold C n < (X.card : ℝ) → EuclideanGeometry.HasConvexNGon n (X : Set ℝ²)) :
    ∃ s : ℕ → ℝ, s =O[atTop] scale ∧ ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ 2 ^ ((n : ℝ) + s n) := by
  apply of_eventually_cardSet (fun n => (3 * C + 1) * scale n)
  · refine Asymptotics.isBigO_iff.2 ⟨3 * C + 1, Eventually.of_forall fun n => ?_⟩
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 3 * C + 1)]
  · filter_upwards [eventually_ge_atTop (2 : ℕ), he] with n hn h
    let B := threshold C n
    refine ⟨⌊B⌋₊ + 1, ?_, ?_⟩
    · intro X hcard hgp
      apply h X hgp
      rw [hcard, Nat.cast_add, Nat.cast_one]
      exact Nat.lt_floor_add_one B
    · let a : ℝ := (n : ℝ) + C *
          ((balancedParameter n : ℝ) * Real.log n + (n : ℝ) / balancedParameter n)
      have hB : B = (2 : ℝ) ^ a := rfl
      have hlog : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      have ha : 0 ≤ a := by
        dsimp only [a]
        positivity
      have hB1 : 1 ≤ B := hB ▸ Real.one_le_rpow (by norm_num) ha
      rw [Nat.cast_add, Nat.cast_one]
      calc
        (⌊B⌋₊ : ℝ) + 1 ≤ B + 1 := add_le_add_left (Nat.floor_le (show 0 ≤ B from zero_le_one.trans hB1)) 1
        _ ≤ B * 2 := by linarith
        _ = (2 : ℝ) ^ (a + 1) := by rw [Real.rpow_add (by norm_num) a 1, Real.rpow_one, hB]
        _ ≤ 2 ^ ((n : ℝ) + (3 * C + 1) * scale n) := by
          apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
          have hmul := mul_le_mul_of_nonneg_left (balancedParameter_bound hn) hC
          have hscale := one_le_scale hn
          dsimp only [a]
          linarith only [hmul, hscale]

private theorem exists_chain_or_antichain {α : Type*} (r : α → α → Prop)
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    {X : Finset α} {h w : ℕ} (hX : h * w < X.card) :
    (∃ S ⊆ (X : Set α), S.encard = (h + 1 : ℕ) ∧ IsChain r S) ∨
    (∃ S ⊆ (X : Set α), (w : ℕ∞) < S.encard ∧ IsAntichain r S) := by
  classical
  let below (a : α) := {b | b ∈ (X : Set α) ∧ r b a}
  have hfinite (a : α) : (below a).Finite := X.finite_toSet.subset (fun _ hb => hb.1)
  let height (a : α) := (below a).chainHeight r
  have htop (a : α) : height a ≠ ⊤ := Set.chainHeight_ne_top_of_finite _ _ (hfinite a)
  let rank (a : α) := (height a).toNat
  have hrank (a : α) : (rank a : ℕ∞) = height a := ENat.natCast_toNat (htop a)
  have hextend (a : α) {V : Set α} (ha : a ∈ V) (hV : below a ⊆ V) :
      height a + 1 ≤ V.chainHeight r := by
    obtain ⟨S, hS, hcard, hchain⟩ := Set.exists_eq_chainHeight_of_finite _ _ (hfinite a)
    have hnot : a ∉ S := fun hm => hirr a (hS hm).2
    have hcard' : (insert a S).encard = height a + 1 := by
      rw [Set.encard_insert_of_notMem hnot, hcard]
    calc
      height a + 1 = (insert a S).encard := hcard'.symm
      _ ≤ V.chainHeight r := Set.encard_le_chainHeight_of_isChain _ _
        (Set.insert_subset ha (hS.trans hV)) (hchain.insert fun b hb _ => Or.inr (hS hb).2)
  by_cases hlarge : ((h + 1 : ℕ) : ℕ∞) ≤ (X : Set α).chainHeight r
  · exact Or.inl (Set.exists_isChain_of_le_chainHeight _ hlarge)
  · right
    have hheight : (X : Set α).chainHeight r ≤ (h : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one] at hlarge
      exact (ENat.lt_add_one_iff (by simp)).1 (lt_of_not_ge hlarge)
    have hrange (a : α) (ha : a ∈ X) : rank a ∈ Finset.range h := by
      apply Finset.mem_range.2
      have hle : height a + 1 ≤ (h : ℕ∞) :=
        (hextend a ha (fun _ hb => hb.1)).trans hheight
      rw [← hrank a] at hle
      exact_mod_cast (ENat.add_one_le_natCast_iff.1 hle)
    obtain ⟨j, _, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hrange
      (by simpa using hX)
    let Y := X.filter (fun a => rank a = j)
    refine ⟨(Y : Set α), Finset.filter_subset _ _, ?_, ?_⟩
    · rw [Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast hj
    · intro a ha b hb _ hab
      obtain ⟨haX, haj⟩ := Finset.mem_filter.1 ha
      obtain ⟨_, hbj⟩ := Finset.mem_filter.1 hb
      have hle : height a + 1 ≤ height b :=
        hextend a ⟨haX, hab⟩ (fun _ hc => ⟨hc.1, htrans hc.2 hab⟩)
      have hlt := (ENat.add_one_le_iff (htop a)).1 hle
      rw [← hrank a, ← hrank b, haj, hbj] at hlt
      exact (lt_irrefl _) hlt

private def baseDet (x : ℝ) (p q : ℝ × ℝ) : ℝ :=
  (p.1 - x) * q.2 - (q.1 - x) * p.2

private noncomputable def baseOrder (p q : ℝ × ℝ) : Prop :=
  p.1 / p.2 < q.1 / q.2 ∧ (1 - p.1) / p.2 < (1 - q.1) / q.2

private theorem baseOrder_iff {p q : ℝ × ℝ} (hp : 0 < p.2) (hq : 0 < q.2) :
    baseOrder p q ↔ baseDet 0 p q < 0 ∧ 0 < baseDet 1 p q := by
  unfold baseOrder baseDet
  rw [div_lt_div_iff₀ hp hq, div_lt_div_iff₀ hp hq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith only [h₁, h₂]

private theorem baseDet_flip (x : ℝ) (p q : ℝ × ℝ) : baseDet x q p = -baseDet x p q := by
  unfold baseDet
  ring

private theorem exists_subset_by_base_signs
    {X : Finset (ℝ × ℝ)} {h w : ℕ} (hX : h * w < X.card)
    (habove : ∀ p ∈ X, 0 < p.2)
    (hgen : ∀ p ∈ X, ∀ q ∈ X, p ≠ q → baseDet 0 p q ≠ 0 ∧ baseDet 1 p q ≠ 0) :
    (∃ S ⊆ (X : Set (ℝ × ℝ)), S.encard = (h + 1 : ℕ) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → baseDet 0 p q * baseDet 1 p q < 0) ∨
    (∃ S ⊆ (X : Set (ℝ × ℝ)), (w : ℕ∞) < S.encard ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 0 < baseDet 0 p q * baseDet 1 p q) := by
  obtain hchain | hanti := exists_chain_or_antichain baseOrder
    (fun _ h => (lt_irrefl _) h.1)
    (fun hab hbc => ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩) hX
  · obtain ⟨S, hS, hlarge, hchain⟩ := hchain
    left
    refine ⟨S, hS, hlarge, fun p hp q hq hne => ?_⟩
    have hp' := habove p (hS hp)
    have hq' := habove q (hS hq)
    rcases hchain hp hq hne with hpq | hqp
    · obtain ⟨h₀, h₁⟩ := (baseOrder_iff hp' hq').1 hpq
      exact mul_neg_of_neg_of_pos h₀ h₁
    · obtain ⟨h₀, h₁⟩ := (baseOrder_iff hq' hp').1 hqp
      rw [baseDet_flip] at h₀ h₁
      exact mul_neg_of_pos_of_neg (neg_lt_zero.mp h₀) (neg_pos.mp h₁)
  · obtain ⟨S, hS, hlarge, hanti⟩ := hanti
    right
    refine ⟨S, hS, hlarge, fun p hp q hq hne => ?_⟩
    have hp' := habove p (hS hp)
    have hq' := habove q (hS hq)
    obtain ⟨h₀, h₁⟩ := hgen p (hS hp) q (hS hq) hne
    rcases lt_or_gt_of_ne h₀ with hpneg | hppos
    · have hqneg : baseDet 1 p q < 0 := by
        by_contra! hqnonneg
        have hqpos := lt_of_le_of_ne hqnonneg h₁.symm
        exact hanti hp hq hne ((baseOrder_iff hp' hq').2 ⟨hpneg, hqpos⟩)
      exact mul_pos_of_neg_of_neg hpneg hqneg
    · have hqpos : 0 < baseDet 1 p q := by
        by_contra! hqnonpos
        have hqneg := lt_of_le_of_ne hqnonpos h₁
        apply hanti hq hp hne.symm
        apply (baseOrder_iff hq' hp').2
        rw [baseDet_flip 0 p q, baseDet_flip 1 p q]
        exact ⟨neg_lt_zero.mpr hppos, neg_pos.mpr hqneg⟩
      exact mul_pos hppos hqpos

private noncomputable def slope (x y : ℝ² →ₗ[ℝ] ℝ) (p q : ℝ²) : ℝ :=
  (y q - y p) / (x q - x p)

private def score (x y : ℝ² →ₗ[ℝ] ℝ) (s : ℝ) : ℝ² →ₗ[ℝ] ℝ :=
  y - s • x

private theorem exists_support_slope {B : Finset ℝ²} {x y : ℝ² →ₗ[ℝ] ℝ} {lo hi : ℝ}
    (hlohi : lo ≤ hi) (hinj : Set.InjOn x (B : Set ℝ²))
    (hband : ∀ a ∈ B, ∀ b ∈ B, x a < x b → lo < slope x y a b ∧ slope x y a b < hi)
    (hcup : ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, x a < x b → x b < x c →
      slope x y a b < slope x y b c)
    {p : ℝ²} (hp : p ∈ B) :
    ∃ s ∈ Set.Icc lo hi, ∀ q ∈ B, q ≠ p → score x y s p < score x y s q := by
  classical
  let L := B.filter fun q => x q < x p
  let R := B.filter fun q => x p < x q
  have hleft (s : ℝ) {q : ℝ²} (hqp : x q < x p) (h : slope x y q p < s) :
      score x y s p < score x y s q := by
    have h' := (div_lt_iff₀ (sub_pos.mpr hqp)).1 h
    change y p - s * x p < y q - s * x q
    linarith only [h']
  have hright (s : ℝ) {q : ℝ²} (hqp : x p < x q) (h : s < slope x y p q) :
      score x y s p < score x y s q := by
    have h' := (lt_div_iff₀ (sub_pos.mpr hqp)).1 h
    change y p - s * x p < y q - s * x q
    linarith only [h']
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image L (fun q => slope x y q p) hL
      obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image R (slope x y p) hR
      obtain ⟨haB, hap⟩ := Finset.mem_filter.1 ha
      obtain ⟨hbB, hpb⟩ := Finset.mem_filter.1 hb
      obtain ⟨s, hs₁, hs₂⟩ := exists_between (hcup a haB p hp b hbB hap hpb)
      refine ⟨s, ⟨((hband a haB p hp hap).1.trans hs₁).le,
        (hs₂.trans (hband p hp b hbB hpb).2).le⟩, fun q hq hne => ?_⟩
      rcases lt_or_gt_of_ne (fun he => hne (hinj hq hp he)) with hlt | hgt
      · exact hleft s hlt ((hmax q (Finset.mem_filter.2 ⟨hq, hlt⟩)).trans_lt hs₁)
      · exact hright s hgt (hs₂.trans_le (hmin q (Finset.mem_filter.2 ⟨hq, hgt⟩)))
    · refine ⟨hi, ⟨hlohi, le_rfl⟩, fun q hq hne => ?_⟩
      rcases lt_or_gt_of_ne (fun he => hne (hinj hq hp he)) with hlt | hgt
      · exact hleft hi hlt (hband q hq p hp hlt).2
      · exact (hR ⟨q, Finset.mem_filter.2 ⟨hq, hgt⟩⟩).elim
  · refine ⟨lo, ⟨le_rfl, hlohi⟩, fun q hq hne => ?_⟩
    rcases lt_or_gt_of_ne (fun he => hne (hinj hq hp he)) with hlt | hgt
    · exact (hL ⟨q, Finset.mem_filter.2 ⟨hq, hlt⟩⟩).elim
    · exact hright lo hgt (hband p hp q hq hgt).1

private theorem score_lt_of_endpoints {x y : ℝ² →ₗ[ℝ] ℝ} {lo hi s : ℝ} {p q : ℝ²}
    (hs : s ∈ Set.Icc lo hi)
    (hlo : score x y lo p < score x y lo q) (hhi : score x y hi p < score x y hi q) :
    score x y s p < score x y s q := by
  change y p - lo * x p < y q - lo * x q at hlo
  change y p - hi * x p < y q - hi * x q at hhi
  change y p - s * x p < y q - s * x q
  rcases le_total (x p) (x q) with h | h
  · have hmul := mul_le_mul_of_nonneg_right hs.2 (sub_nonneg.mpr h)
    linarith only [hhi, hmul]
  · have hmul := mul_le_mul_of_nonneg_right hs.1 (sub_nonneg.mpr h)
    linarith only [hlo, hmul]

private theorem convexIndep_of_slope_blocks {ι : Type*} (P : Finset ℝ²) (B : ι → Finset ℝ²)
    (x y : ι → ℝ² →ₗ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hcover : ∀ p ∈ P, ∃ i, p ∈ B i)
    (hinterval : ∀ i, lo i ≤ hi i)
    (hinj : ∀ i, Set.InjOn (x i) (B i : Set ℝ²))
    (hband : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, x i a < x i b →
      lo i < slope (x i) (y i) a b ∧ slope (x i) (y i) a b < hi i)
    (hcup : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, ∀ c ∈ B i, x i a < x i b → x i b < x i c →
      slope (x i) (y i) a b < slope (x i) (y i) b c)
    (hsep : ∀ i, ∀ p ∈ B i, ∀ q ∈ P, q ∉ B i →
      score (x i) (y i) (lo i) p < score (x i) (y i) (lo i) q ∧
      score (x i) (y i) (hi i) p < score (x i) (y i) (hi i) q) :
    EuclideanGeometry.ConvexIndep (P : Set ℝ²) := by
  intro p hp hmem
  obtain ⟨i, hpi⟩ := hcover p hp
  obtain ⟨s, hs, hlocal⟩ := exists_support_slope (hinterval i) (hinj i) (hband i) (hcup i) hpi
  let L := score (x i) (y i) s
  have hsub : (P : Set ℝ²) \ {p} ⊆ {q | L p < L q} := by
    intro q hq
    by_cases hqi : q ∈ B i
    · exact hlocal q hqi hq.2
    · obtain ⟨hlo, hhi⟩ := hsep i p hpi q hq.1 hqi
      exact score_lt_of_endpoints hs hlo hhi
  exact (lt_irrefl (L p)) (convexHull_min hsub (convex_halfSpace_gt L.isLinear _) hmem)

private noncomputable def convexSubsets (n : ℕ) (X : Finset ℝ²) : Finset (Finset ℝ²) :=
  open scoped Classical in
  (X.powersetCard n).filter fun Y => EuclideanGeometry.ConvexIndep (Y : Set ℝ²)

private theorem card_choose_le_convexSubsets_mul {n M : ℕ} {X : Finset ℝ²}
    (hM : M ∈ Erdos107.cardSet n) (hgp : EuclideanGeometry.NonTrilinear (X : Set ℝ²)) :
    X.card.choose M ≤ (convexSubsets n X).card * (X.card - n).choose (M - n) := by
  classical
  let extensions (Y : Finset ℝ²) :=
    ((X \ Y).powersetCard (M - n)).image (fun T => Y ∪ T)
  have hcover : X.powersetCard M ⊆ (convexSubsets n X).biUnion extensions := by
    intro U hU
    obtain ⟨hUX, hUM⟩ := Finset.mem_powersetCard.1 hU
    have hsub : (U : Set ℝ²) ⊆ X := hUX
    have hUgp : EuclideanGeometry.NonTrilinear (U : Set ℝ²) := hgp.mono hsub
    obtain ⟨Y, hYn, hYU, hYconv⟩ := hM U hUM hUgp
    have hYU' : Y ⊆ U := hYU
    have hY : Y ∈ convexSubsets n X :=
      Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨hYU'.trans hUX, hYn⟩, hYconv⟩
    apply Finset.mem_biUnion.2
    refine ⟨Y, hY, Finset.mem_image.2 ⟨U \ Y, ?_, ?_⟩⟩
    · apply Finset.mem_powersetCard.2
      refine ⟨fun p hp => Finset.mem_sdiff.2 ⟨hUX (Finset.mem_sdiff.1 hp).1,
        (Finset.mem_sdiff.1 hp).2⟩, ?_⟩
      rw [Finset.card_sdiff_of_subset hYU', hYn, hUM]
    · rw [Finset.union_sdiff_of_subset hYU']
  have hsize (Y : Finset ℝ²) (hY : Y ∈ convexSubsets n X) :
      (extensions Y).card ≤ (X.card - n).choose (M - n) := by
    obtain ⟨hYX, hYn⟩ := Finset.mem_powersetCard.1 (Finset.mem_filter.1 hY).1
    calc
      (extensions Y).card ≤ ((X \ Y).powersetCard (M - n)).card := Finset.card_image_le
      _ = (X.card - n).choose (M - n) := by
        rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hYX, hYn]
  rw [← Finset.card_powersetCard]
  calc
    (X.powersetCard M).card ≤ ((convexSubsets n X).biUnion extensions).card := Finset.card_le_card hcover
    _ ≤ ∑ Y ∈ convexSubsets n X, (extensions Y).card := Finset.card_biUnion_le
    _ ≤ ∑ _Y ∈ convexSubsets n X, (X.card - n).choose (M - n) := Finset.sum_le_sum hsize
    _ = (convexSubsets n X).card * (X.card - n).choose (M - n) := by simp

end HMPT

theorem OMA.solution : type_of% @Erdos107.variants.hmpt_bound := by
  obtain ⟨C, hC, hplanar⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ X : Finset ℝ², EuclideanGeometry.NonTrilinear (X : Set ℝ²) →
        HMPT.threshold C n < (X.card : ℝ) → EuclideanGeometry.HasConvexNGon n (X : Set ℝ²) := by
    sorry
  exact HMPT.of_eventually_planar_bound hC hplanar
