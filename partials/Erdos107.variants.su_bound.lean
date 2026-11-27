import FormalConjectures.ErdosProblems.«107»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators


-- Problem: Erdős Problem 107 — su bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/107.lean:155 (declaration Erdos107.variants.su_bound)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Asymptotic and finite reductions for the Erdős–Szekeres polygon bound. -/

open Filter Asymptotics Finset

namespace Erdos107Suk

private theorem patch_eventual_bound {g : ℕ → ℝ} {e : ℕ → ℝ}
    (he : e =o[atTop] (fun n => (n : ℝ)))
    (h : ∀ᶠ n in atTop, g n ≤ (2 : ℝ) ^ ((n : ℝ) + e n)) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n : ℕ, g n ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let r (n : ℕ) : ℝ := if N ≤ n then e n else Real.logb 2 (max (g n) 1) - n
  have hre : r =ᶠ[atTop] e :=
    (eventually_ge_atTop N).mono fun n hn => if_pos hn
  refine ⟨r, he.congr' hre.symm EventuallyEq.rfl, fun n => ?_⟩
  by_cases hn : N ≤ n
  · simpa only [r, if_pos hn] using hN n hn
  · have hx : (0 : ℝ) < max (g n) 1 := zero_lt_one.trans_le (le_max_right _ _)
    have hlog : (n : ℝ) + r n = Real.logb 2 (max (g n) 1) := by
      simp only [r, if_neg hn]
      ring
    rw [hlog, Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hx]
    exact le_max_left _ _

private theorem sublinear_log_power {a : ℝ} (ha : a < 1) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n) =o[atTop] (fun n => (n : ℝ)) := by
  have hlog := (isLittleO_log_rpow_atTop (sub_pos.mpr ha)).comp_tendsto
    tendsto_natCast_atTop_atTop
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a) atTop).mul_isLittleO hlog
  refine h.congr' EventuallyEq.rfl ((eventually_gt_atTop (0 : ℕ)).mono fun n hn => ?_)
  change (n : ℝ) ^ a * (n : ℝ) ^ (1 - a) = (n : ℝ)
  rw [← Real.rpow_add (Nat.cast_pos.mpr hn), show a + (1 - a) = 1 by ring, Real.rpow_one]

private theorem from_eventual_cardSet {e : ℕ → ℝ}
    (he : e =o[atTop] (fun n => (n : ℝ)))
    (h : ∀ᶠ n in atTop, ⌊(2 : ℝ) ^ ((n : ℝ) + e n)⌋₊ ∈ Erdos107.cardSet n) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  have hh : ∀ᶠ n in atTop, (Erdos107.f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + e n) := by
    filter_upwards [h] with n hn
    exact (Nat.cast_le.mpr (Nat.sInf_le hn)).trans (Nat.floor_le (by positivity))
  obtain ⟨r, hr, hrb⟩ := patch_eventual_bound he hh
  exact ⟨r, hr, fun n _ => hrb n⟩

private theorem from_suk_threshold (C : ℝ)
    (h : ∀ᶠ n in atTop,
      ⌊(2 : ℝ) ^ ((n : ℝ) + C * ((n : ℝ) ^ (2 / 3 : ℝ) * Real.log n))⌋₊ ∈
        Erdos107.cardSet n) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + r n) :=
  from_eventual_cardSet
    ((sublinear_log_power (by norm_num : (2 / 3 : ℝ) < 1)).const_mul_left C) h

private theorem from_eventual_epsilon {g : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, g n ≤ (2 : ℝ) ^ ((1 + ε) * n)) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n : ℕ, g n ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  let r (n : ℕ) : ℝ := max (Real.logb 2 (max (g n) 1) - n) 0
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hpos (n : ℕ) : 0 < max (g n) 1 := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨r, ?_, fun n => ?_⟩
  · refine isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [h ε hε] with n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h₁ : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) := by
      rw [← Real.rpow_zero 2]
      exact (Real.rpow_le_rpow_left_iff htwo).mpr (by positivity)
    have hm := max_le hn h₁
    have hl := (Real.logb_le_iff_le_rpow htwo (hpos n)).mpr hm
    rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_of_nonneg hn0]
    exact max_le (by linarith) (mul_nonneg hε.le hn0)
  · apply (le_max_left _ _).trans
    apply (Real.logb_le_iff_le_rpow htwo (hpos n)).mp
    have hr : Real.logb 2 (max (g n) 1) - n ≤ r n := le_max_left _ _
    linarith

private theorem from_epsilon_cardSet
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ⌊(2 : ℝ) ^ ((1 + ε) * n)⌋₊ ∈ Erdos107.cardSet n) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  obtain ⟨r, hr, hrb⟩ := from_eventual_epsilon (g := fun n => (Erdos107.f n : ℝ)) (by
    intro ε hε
    filter_upwards [h ε hε] with n hn
    exact (Nat.cast_le.mpr (Nat.sInf_le hn)).trans (Nat.floor_le (by positivity)))
  exact ⟨r, hr, fun n _ => hrb n⟩

/-- Counting incidences gives a lower density of good k-subsets from a
hitting property on all m-subsets. -/
private theorem dense_subsets {α : Type*} (S : Finset α) {k m : ℕ}
    (hkm : k ≤ m) (hmS : m ≤ S.card) (good : Finset α → Prop) [DecidablePred good]
    (hit : ∀ U ⊆ S, U.card = m → ∃ T ⊆ U, T.card = k ∧ good T) :
    S.card.choose k ≤ ((S.powersetCard k).filter good).card * m.choose k := by
  classical
  let G := (S.powersetCard k).filter good
  have hcount :
      (S.powersetCard m).card * 1 ≤ G.card * (S.card - k).choose (m - k) := by
    apply Finset.card_mul_le_card_mul (fun U T : Finset α => T ⊆ U)
    · intro U hU
      obtain ⟨hUS, hUm⟩ := mem_powersetCard.mp hU
      obtain ⟨T, hTU, hTk, hg⟩ := hit U hUS hUm
      exact card_pos.mpr ⟨T, by
        exact mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_powersetCard.mpr ⟨hTU.trans hUS, hTk⟩, hg⟩, hTU⟩⟩
    · intro T hT
      obtain ⟨hTS, hTk⟩ := mem_powersetCard.mp (mem_filter.mp hT).1
      change ((S.powersetCard m).filter (T ⊆ ·)).card ≤ _
      rw [card_filter_powersetCard_subset T S m hTS (hTk ▸ hkm), hTk]
  rw [card_powersetCard, mul_one] at hcount
  have hp : 0 < (S.card - k).choose (m - k) := Nat.choose_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hp
  calc
    S.card.choose k * (S.card - k).choose (m - k) =
        S.card.choose m * m.choose k := (Nat.choose_mul hkm).symm
    _ ≤ (G.card * (S.card - k).choose (m - k)) * m.choose k :=
      Nat.mul_le_mul_right _ hcount
    _ = (G.card * m.choose k) * (S.card - k).choose (m - k) := by ac_rfl

/-- Longest chains below a point stratify a finite strict partial order into
antichains. -/
private theorem chain_or_antichain {α : Type*} (S : Finset α) (R : α → α → Prop)
    (hir : ∀ x, ¬ R x x) (ht : ∀ {x y z}, R x y → R y z → R x z)
    {a b : ℕ} (ha : 0 < a) (hsize : a * b < S.card) :
    (∃ C ⊆ S, a ≤ C.card ∧ IsChain R (C : Set α)) ∨
      ∃ A ⊆ S, b < A.card ∧ IsAntichain R (A : Set α) := by
  classical
  by_cases hc : ∃ C ⊆ S, a ≤ C.card ∧ IsChain R (C : Set α)
  · exact Or.inl hc
  right
  let below (p : α) := S.powerset.filter fun (C : Finset α) =>
    IsChain R (C : Set α) ∧ ∀ q ∈ C, R q p
  let rank (p : α) := (below p).sup Finset.card
  have extend {C : Finset α} {p : α} (hC : C ∈ below p) (hp : p ∈ S) :
      insert p C ⊆ S ∧ IsChain R ((insert p C : Finset α) : Set α) ∧
        (insert p C).card = C.card + 1 := by
    obtain ⟨hCS, hchain, hrel⟩ := mem_filter.mp hC
    have hpn : p ∉ C := fun h => hir p (hrel p h)
    refine ⟨insert_subset hp (mem_powerset.mp hCS), ?_, card_insert_of_notMem hpn⟩
    rw [coe_insert]
    exact hchain.insert (fun q hq _ => Or.inr (hrel q hq))
  have hlt p (hp : p ∈ S) : rank p < a := by
    change (below p).sup Finset.card < a
    apply (Finset.sup_lt_iff ha).mpr
    intro C hC
    obtain ⟨hsub, hchain, hcard⟩ := extend hC hp
    have hbound : ¬ a ≤ (insert p C).card := fun hle =>
      hc ⟨insert p C, hsub, hle, hchain⟩
    omega
  have hrank {p q} (hp : p ∈ S) (hpq : R p q) : rank p < rank q := by
    have hne : (below p).Nonempty := ⟨∅, by simp [below]⟩
    obtain ⟨C, hC, he⟩ := Finset.exists_mem_eq_sup (below p) hne Finset.card
    obtain ⟨hsub, hchain, hcard⟩ := extend hC hp
    have hm : insert p C ∈ below q := by
      refine mem_filter.mpr ⟨mem_powerset.mpr hsub, hchain, ?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hpq
      · exact ht ((mem_filter.mp hC).2.2 x hx) hpq
    have hbnd : (insert p C).card ≤ rank q := Finset.le_sup hm
    change rank p = C.card at he
    omega
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := Finset.range a) (f := rank)
    (fun p hp => mem_range.mpr (hlt p hp)) (by simpa using hsize)
  refine ⟨S.filter (fun p => rank p = j), filter_subset _ _, hj, ?_⟩
  intro p hp q hq _ hpq
  obtain ⟨hpS, hpj⟩ := mem_filter.mp hp
  obtain ⟨_, hqj⟩ := mem_filter.mp hq
  exact (hrank hpS hpq).ne (hpj.trans hqj.symm)

/-- If good configurations outnumber the capacity of all anchor choices
with a small region, some anchor has large completion regions throughout. -/
private theorem large_completion_regions {α β γ : Type*}
    {k L : ℕ} (S : Finset α) (G : Finset β) (A : Finset γ)
    (anchor : β → γ) (completion : β → Fin k → α) (R : γ → Fin k → Finset α)
    (hA : ∀ g ∈ G, anchor g ∈ A)
    (hR : ∀ a ∈ A, ∀ i, R a i ⊆ S)
    (hmem : ∀ g ∈ G, ∀ i, completion g i ∈ R (anchor g) i)
    (hinj : ∀ g ∈ G, ∀ g' ∈ G, anchor g = anchor g' →
      completion g = completion g' → g = g')
    (hsize : A.card * (L * S.card ^ (k - 1)) < G.card) :
    ∃ a ∈ A, ∀ i, L < (R a i).card := by
  classical
  obtain ⟨a, haA, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hA hsize
  refine ⟨a, haA, fun i => lt_of_not_ge fun hi => ?_⟩
  let F := G.filter fun g => anchor g = a
  have hm : F.card ≤ (Fintype.piFinset (R a)).card := by
    apply Finset.card_le_card_of_injOn completion
    · intro g hg
      obtain ⟨hgG, hga⟩ := mem_filter.mp hg
      exact Fintype.mem_piFinset.mpr fun j => hga ▸ hmem g hgG j
    · intro g hg g' hg' he
      obtain ⟨hgG, hga⟩ := mem_filter.mp hg
      obtain ⟨hg'G, hg'a⟩ := mem_filter.mp hg'
      exact hinj g hgG g' hg'G (hga.trans hg'a.symm) he
  have hp : (Fintype.piFinset (R a)).card ≤ L * S.card ^ (k - 1) := by
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (mem_univ i)]
    refine Nat.mul_le_mul hi ?_
    calc
      ∏ j ∈ univ.erase i, (R a j).card ≤ ∏ _j ∈ univ.erase i, S.card :=
        Finset.prod_le_prod' fun j _ => card_le_card (hR a haA j)
      _ = S.card ^ (k - 1) := by simp [Finset.prod_const, Finset.card_erase_of_mem]
  exact (not_lt_of_ge (hm.trans hp)) ha

/-- The threshold set is upward closed: pass to a subset of the right size. -/
private theorem cardSet_mono {n N M : ℕ} (hN : N ∈ Erdos107.cardSet n) (hNM : N ≤ M) :
    M ∈ Erdos107.cardSet n := by
  intro pts hcard hnt
  obtain ⟨Q, hQ, hQc⟩ := Finset.exists_subset_card_eq (s := pts) (n := N)
    (hNM.trans hcard.ge)
  have hQ' : (Q : Set (EuclideanSpace ℝ (Fin 2))) ⊆ (pts : Set (EuclideanSpace ℝ (Fin 2))) :=
    Finset.coe_subset.mpr hQ
  obtain ⟨S, hS, hSQ, hconv⟩ := hN Q hQc
    (fun a ha b hb c hc => hnt (hQ' ha) (hQ' hb) (hQ' hc))
  exact ⟨S, hS, hSQ.trans hQ', hconv⟩

/-- It suffices to find, for every positive ε and every large n, SOME threshold
below 2^((1+ε)n); no floor is needed. -/
private theorem from_epsilon_exists
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧ N ∈ Erdos107.cardSet n) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  apply from_epsilon_cardSet
  intro ε hε
  filter_upwards [h ε hε] with n hn
  obtain ⟨N, hN, hmem⟩ := hn
  exact cardSet_mono hmem (Nat.le_floor hN)

/-- A threshold for a larger polygon is a threshold for a smaller one. -/
private theorem cardSet_anti {n m N : ℕ} (hN : N ∈ Erdos107.cardSet n) (hmn : m ≤ n) :
    N ∈ Erdos107.cardSet m := by
  intro pts hcard hnt
  obtain ⟨S, hS, hSP, hconv⟩ := hN pts hcard hnt
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (s := S) (n := m) (hmn.trans hS.ge)
  have hT' : (T : Set (EuclideanSpace ℝ (Fin 2))) ⊆ (S : Set (EuclideanSpace ℝ (Fin 2))) :=
    Finset.coe_subset.mpr hT
  refine ⟨T, hTc, hT'.trans hSP, fun a ha hmem => hconv a (hT' ha) ?_⟩
  exact convexHull_mono (Set.sdiff_subset_sdiff_left hT') hmem

/- Reduction to plain coordinates. -/

private theorem finite_image_pullback {α β : Type*} [DecidableEq β] (L : α → β)
    (X : Finset α) (Z : Finset β) (hZ : Z ⊆ X.image L) (hL : Set.InjOn L (X : Set α)) :
    ∃ Y ⊆ X, Y.image L = Z ∧ Y.card = Z.card := by
  classical
  let Y := X.filter fun y => L y ∈ Z
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image L = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hy).2
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hZ hz)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hz⟩, rfl⟩
  refine ⟨Y, hYX, hYZ, ?_⟩
  rw [← hYZ, Finset.card_image_of_injOn (hL.mono hYX)]

private theorem planar_coordinates (X : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ x y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ,
      Set.InjOn x (X : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  classical
  let bad := (X ×ˢ X).image fun uv : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ :=
    EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : EuclideanSpace ℝ (Fin 2)) (hx : x p = x q) (hy : y p = y q) : p = q := by
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 = q 1 at hy
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      rw [hy] at hx
      exact add_right_cancel hx
    · exact hy
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq hx
  by_cases hy : y p = y q
  · exact hjoint p q hx hy
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 ≠ q 1 at hy
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    nlinarith only [hx]

/-- Signed area of a planar triple. -/
private def orient (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

/-- Coordinate form of convex position: every point is strictly extreme. -/
private def PlanarConvex (Y : Finset (ℝ × ℝ)) : Prop :=
  ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2

/-- General position in coordinates: distinct abscissas and no flat triple. -/
private def PlanarGeneral (X : Finset (ℝ × ℝ)) : Prop :=
  Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) ∧
    ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0

private theorem orient_ne_in_image (X : Finset (EuclideanSpace ℝ (Fin 2)))
    (hX : EuclideanGeometry.NonTrilinear (X : Set (EuclideanSpace ℝ (Fin 2))))
    (x y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ)
    (hjoint : ∀ p q, x p = x q → y p = y q → p = q) :
    ∀ a ∈ X.image (x.prod y), ∀ b ∈ X.image (x.prod y), ∀ c ∈ X.image (x.prod y),
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0 := by
  intro u hu v hv w hw hab hbc he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hw
  change x a < x b at hab
  change x b < x c at hbc
  change (x b - x a) * (y c - y b) - (y b - y a) * (x c - x b) = 0 at he
  have hnab : a ≠ b := fun h => hab.ne (congrArg x h)
  have hnbc : b ≠ c := fun h => hbc.ne (congrArg x h)
  have hnac : a ≠ c := fun h => (hab.trans hbc).ne (congrArg x h)
  apply hX ha hb hc hnab hnbc hnac
  let r := (x b - x a) / (x c - x b)
  have hden := sub_ne_zero.mpr hbc.ne'
  have hxb : x b - x a = r * (x c - x b) := by
    dsimp [r]
    rw [div_mul_cancel₀ _ hden]
  have hyb : y b - y a = r * (y c - y b) := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).2
    linarith only [he]
  have hdiff : b - a = r • (c - b) := by
    apply hjoint
    · simpa only [map_sub, map_smul, smul_eq_mul] using hxb
    · simpa only [map_sub, map_smul, smul_eq_mul] using hyb
  apply (collinear_iff_of_mem (show b ∈ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) by simp)).mpr
  refine ⟨c - b, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨-r, ?_⟩
    change _ = (-r) • (c - b) + b
    rw [neg_smul, ← hdiff]
    abel
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

/-- Bridge: a coordinate statement about finite subsets of the real plane (distinct
abscissas, no flat triple, strictly extreme points) gives a member of the threshold set. -/
private theorem cardSet_of_planar {n N : ℕ}
    (h : ∀ X : Finset (ℝ × ℝ), X.card = N → PlanarGeneral X →
      ∃ Y ⊆ X, Y.card = n ∧ PlanarConvex Y) :
    N ∈ Erdos107.cardSet n := by
  classical
  intro pts hcard hnt
  obtain ⟨x, y, hx, hxy⟩ := planar_coordinates pts
  let L := x.prod y
  have hL : Function.Injective L := fun a b he =>
    hxy a b (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hinj : Set.InjOn Prod.fst (↑(pts.image L) : Set (ℝ × ℝ)) := by
    intro u hu v hv he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
    exact congrArg L (hx ha hb he)
  obtain ⟨Y, hYX, hYc, hYconv⟩ := h (pts.image L)
    (by rw [Finset.card_image_of_injective _ hL, hcard])
    ⟨hinj, orient_ne_in_image pts hnt x y hxy⟩
  obtain ⟨Z, hZP, hZY, hZc⟩ := finite_image_pullback L pts Y hYX hL.injOn
  refine ⟨Z, hZc.trans hYc, Finset.coe_subset.mpr hZP, ?_⟩
  intro a ha hmem
  have haY : L a ∈ Y := by
    rw [← hZY]
    exact Finset.mem_image_of_mem L ha
  obtain ⟨u, v, huv⟩ := hYconv (L a) haY
  let Λ : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ := u • x + v • y
  have hsub : (Z : Set (EuclideanSpace ℝ (Fin 2))) \ {a} ⊆ {q | Λ a < Λ q} := by
    intro q hq
    have hqY : L q ∈ Y := by
      rw [← hZY]
      exact Finset.mem_image_of_mem L hq.1
    have hne : L q ≠ L a := fun he => hq.2 (hL he)
    have hlt := huv (L q) hqY hne
    change u * x a + v * y a < u * x q + v * y q
    exact hlt
  have he := (convexHull_min hsub (convex_halfSpace_gt Λ.isLinear (Λ a))) hmem
  exact lt_irrefl (Λ a) he

/-- Slopes (scaled by σ) increasing along x-sorted triples make every point strictly
extreme. -/
private theorem extreme_of_increasing_slopes (Y : Finset (ℝ × ℝ)) (σ : ℝ)
    (hinj : Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)))
    (hslope : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 →
      (σ * b.2 - σ * a.2) / (b.1 - a.1) < (σ * c.2 - σ * b.2) / (c.1 - b.1)) :
    PlanarConvex Y := by
  classical
  intro p hp
  let A := Y.filter fun q => q.1 < p.1
  let B := Y.filter fun q => p.1 < q.1
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image A
        (fun a : ℝ × ℝ => (σ * p.2 - σ * a.2) / (p.1 - a.1)) hA
      obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image B
        (fun b : ℝ × ℝ => (σ * b.2 - σ * p.2) / (b.1 - p.1)) hB
      obtain ⟨haY, hap⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbY, hpb⟩ := Finset.mem_filter.mp hb
      obtain ⟨s, h₁, h₂⟩ := exists_between (hslope a haY p hp b hbY hap hpb)
      refine ⟨-s, σ, fun q hq hqp => ?_⟩
      have hne : q.1 ≠ p.1 := fun h => hqp (hinj hq hp h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hs : (σ * p.2 - σ * q.2) / (p.1 - q.1) < s :=
          (hmax q (Finset.mem_filter.mpr ⟨hq, hlt⟩)).trans_lt h₁
        have hs' := (div_lt_iff₀ (sub_pos.mpr hlt)).mp hs
        linarith
      · have hs : s < (σ * q.2 - σ * p.2) / (q.1 - p.1) :=
          h₂.trans_le (hmin q (Finset.mem_filter.mpr ⟨hq, hgt⟩))
        have hs' := (lt_div_iff₀ (sub_pos.mpr hgt)).mp hs
        linarith
    · refine ⟨-1, 0, fun q hq hqp => ?_⟩
      have hne : q.1 ≠ p.1 := fun h => hqp (hinj hq hp h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · linarith
      · exact (hB ⟨q, Finset.mem_filter.mpr ⟨hq, hgt⟩⟩).elim
  · refine ⟨1, 0, fun q hq hqp => ?_⟩
    have hne : q.1 ≠ p.1 := fun h => hqp (hinj hq hp h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hA ⟨q, Finset.mem_filter.mpr ⟨hq, hlt⟩⟩).elim
    · linarith

/-- A cup (all x-sorted triples turn left) is in convex position. -/
private theorem planarConvex_of_cup (Y : Finset (ℝ × ℝ))
    (hinj : Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)))
    (h : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → 0 < orient a b c) :
    PlanarConvex Y := by
  apply extreme_of_increasing_slopes Y 1 hinj
  intro a ha b hb c hc hab hbc
  have ht := h a ha b hb c hc hab hbc
  unfold orient at ht
  apply (div_lt_div_iff₀ (sub_pos.2 hab) (sub_pos.2 hbc)).2
  linarith only [ht]

/-- A cap (all x-sorted triples turn right) is in convex position. -/
private theorem planarConvex_of_cap (Y : Finset (ℝ × ℝ))
    (hinj : Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)))
    (h : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → orient a b c < 0) :
    PlanarConvex Y := by
  apply extreme_of_increasing_slopes Y (-1) hinj
  intro a ha b hb c hc hab hbc
  have ht := h a ha b hb c hc hab hbc
  unfold orient at ht
  apply (div_lt_div_iff₀ (sub_pos.2 hab) (sub_pos.2 hbc)).2
  linarith only [ht]

/- Cups and caps (Erdős and Szekeres 1935), ported from the neighbouring standalone proof. -/
section CupsCaps
open scoped Classical

private abbrev Point := ℝ × ℝ

private def turn (up : Bool) (a b c : Point) : Prop :=
  if up then 0 < orient a b c else orient a b c < 0

private def turns (up : Bool) : List Point → Prop
  | a :: b :: c :: l => turn up a b c ∧ turns up (b :: c :: l)
  | _ => True

private def IsSeq (up : Bool) (X : Finset Point) (l : List Point) : Prop :=
  (∀ p ∈ l, p ∈ X) ∧ l.Pairwise (fun p q => p.1 < q.1) ∧ turns up l

private def HasSeq (up : Bool) (X : Finset Point) (k : ℕ) : Prop :=
  ∃ l, IsSeq up X l ∧ l.length = k

private theorem isSeq_mono {up : Bool} {X Y : Finset Point} {l : List Point}
    (hl : IsSeq up X l) (hXY : X ⊆ Y) : IsSeq up Y l :=
  ⟨fun p hp => hXY (hl.1 p hp), hl.2⟩

private theorem turns_append {up : Bool} {a b c : Point} (l : List Point)
    (hl : turns up (l ++ [a, b])) (hc : turn up a b c) :
    turns up (l ++ [a, b, c]) := by
  induction l with
  | nil => simpa [turns] using hc
  | cons x l ih =>
    cases l with
    | nil =>
      have h := (show turn up x a b ∧ turns up [a, b] from hl).1
      exact ⟨h, ih (by trivial)⟩
    | cons y l =>
      cases l with
      | nil =>
        exact ⟨(show turn up x y a ∧ turns up [y, a, b] from hl).1,
          ih (show turns up [y, a, b] from hl.2)⟩
      | cons z l =>
        exact ⟨(show turn up x y z ∧ turns up ((y :: z :: l) ++ [a, b]) from hl).1,
          ih (show turns up ((y :: z :: l) ++ [a, b]) from hl.2)⟩

private theorem isSeq_append {up : Bool} {X : Finset Point} {a b c : Point} {l : List Point}
    (hl : IsSeq up X (l ++ [a, b])) (hc : c ∈ X) (hbc : b.1 < c.1) (ht : turn up a b c) :
    IsSeq up X (l ++ [a, b, c]) := by
  rw [show l ++ [a, b, c] = (l ++ [a, b]) ++ [c] by simp]
  refine ⟨?_, List.pairwise_append.2 ⟨hl.2.1, by simp, ?_⟩, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hl.1 p hp
    · simpa using (List.mem_singleton.1 hp ▸ hc)
  · intro p hp q hq
    have hqc := List.mem_singleton.1 hq
    subst q
    rw [show l ++ [a, b] = (l ++ [a]) ++ [b] by simp] at hp
    rcases List.mem_append.1 hp with hp | hp
    · have hsort := hl.2.1
      rw [show l ++ [a,b] = (l ++ [a]) ++ [b] by simp] at hsort
      exact ((List.pairwise_append.1 hsort).2.2 _ hp _ (by simp)).trans hbc
    · simpa [List.mem_singleton.1 hp] using hbc
  · simpa using turns_append l hl.2.2 ht

private theorem exists_suffix_two {l : List Point} (h : 2 ≤ l.length) :
    ∃ pre a b, l = pre ++ [a, b] := by
  have hrevlen : 2 ≤ l.reverse.length := by simpa using h
  cases hr : l.reverse with
  | nil => simp [hr] at hrevlen
  | cons b r =>
    cases r with
    | nil => simp [hr] at hrevlen
    | cons a pre =>
      exact ⟨pre.reverse, a, b, by
        simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hr⟩

private def IsEnd (s : ℕ) (X : Finset Point) (p : Point) : Prop :=
  ∃ pre a, IsSeq true X (pre ++ [a, p]) ∧ pre.length = s

private theorem no_shorter_cup_outside (s : ℕ) (X : Finset Point) :
    ¬ HasSeq true {p ∈ X | ¬ IsEnd s X p} (s + 2) := by
  rintro ⟨l, hl, hlen⟩
  obtain ⟨pre, a, p, rfl⟩ := exists_suffix_two (by omega : 2 ≤ l.length)
  have hp := Finset.mem_filter.1 (hl.1 p (by simp))
  have hpre : pre.length = s := by simpa using hlen
  exact hp.2 ⟨pre, a, isSeq_mono hl (Finset.filter_subset _ _), hpre⟩

private theorem no_shorter_cap_in_ends (s t : ℕ) (X : Finset Point)
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ HasSeq true X (s + 3)) (hd : ¬ HasSeq false X (t + 3)) :
    ¬ HasSeq false {p ∈ X | IsEnd s X p} (t + 2) := by
  rintro ⟨l, hl, hlen⟩
  cases l with
  | nil => simp at hlen
  | cons p l =>
    cases l with
    | nil => simp at hlen
    | cons q tail =>
      obtain ⟨hp, pre, a, hcup, hpre⟩ := Finset.mem_filter.1 (hl.1 p (by simp))
      have hq := (Finset.mem_filter.1 (hl.1 q (by simp))).1
      have ha := hcup.1 a (by simp)
      have hap : a.1 < p.1 :=
        (List.pairwise_cons.1 (List.pairwise_append.1 hcup.2.1).2.1).1 p (by simp)
      have hpq : p.1 < q.1 := (List.pairwise_cons.1 hl.2.1).1 q (by simp)
      by_cases hturn : 0 < orient a p q
      · apply hc
        exact ⟨pre ++ [a, p, q],
          isSeq_append hcup hq hpq (by simpa [turn] using hturn), by simp [hpre]⟩
      · apply hd
        have hneg : orient a p q < 0 :=
          lt_of_le_of_ne (le_of_not_gt hturn) (hgen a ha p hp q hq hap hpq)
        have hlX := isSeq_mono hl (Finset.filter_subset _ _)
        refine ⟨a :: p :: q :: tail,
          ⟨?_, List.pairwise_cons.2 ⟨?_, hlX.2.1⟩, ?_⟩, ?_⟩
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact ha
          · exact hlX.1 b hb
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact hap
          · exact hap.trans ((List.pairwise_cons.1 hlX.2.1).1 _ hb)
        · change turn false a p q ∧ turns false (p :: q :: tail)
          exact ⟨by simpa [turn] using hneg, hlX.2.2⟩
        · simp only [List.length_cons] at hlen ⊢
          omega

private theorem hasSeq_two {X : Finset Point}
    (hx : Set.InjOn Prod.fst (X : Set Point)) (hX : 1 < X.card) (up : Bool) :
    HasSeq up X 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hX
  have hne : a.1 ≠ b.1 := fun he => hab (hx ha hb he)
  have hseq {a b : Point} (ha : a ∈ X) (hb : b ∈ X) (hab : a.1 < b.1) :
      HasSeq up X 2 := by
    refine ⟨[a, b], ⟨?_, ?_, trivial⟩, rfl⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ha
      · exact hb
    · simp [hab]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hseq ha hb h
  · exact hseq hb ha h

private theorem card_le_binomial (s t : ℕ) (X : Finset Point)
    (hx : Set.InjOn Prod.fst (X : Set Point))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ HasSeq true X (s + 2)) (hd : ¬ HasSeq false X (t + 2)) :
    X.card ≤ (s + t).choose s := by
  induction s generalizing t X with
  | zero =>
    simpa using (le_of_not_gt fun h => hc (hasSeq_two hx h true))
  | succ s ih =>
    induction t generalizing X with
    | zero =>
      simpa using (le_of_not_gt fun h => hd (hasSeq_two hx h false))
    | succ t jt =>
      let T := X.filter (IsEnd s X)
      let U := X.filter (fun p => ¬ IsEnd s X p)
      have hTX : T ⊆ X := Finset.filter_subset _ _
      have hUX : U ⊆ X := Finset.filter_subset _ _
      have hT : T.card ≤ (s + 1 + t).choose (s + 1) := by
        apply jt T (hx.mono hTX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hTX ha) b (hTX hb) c (hTX hc) hab hbc
        · rintro ⟨l, hl, hlen⟩
          exact hc ⟨l, isSeq_mono hl hTX, hlen⟩
        · exact no_shorter_cap_in_ends s t X hgen hc hd
      have hU : U.card ≤ (s + (t + 1)).choose s := by
        apply ih (t + 1) U (hx.mono hUX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hUX ha) b (hUX hb) c (hUX hc) hab hbc
        · exact no_shorter_cup_outside s X
        · rintro ⟨l, hl, hlen⟩
          exact hd ⟨l, isSeq_mono hl hUX, hlen⟩
      have hpart : T.card + U.card = X.card :=
        Finset.card_filter_add_card_filter_not (IsEnd s X)
      have hchoose :
          ((s + 1) + (t + 1)).choose (s + 1) =
            (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        rw [show (s + 1) + (t + 1) = (s + (t + 1)) + 1 by omega,
          Nat.choose_succ_succ', show s + (t + 1) = s + 1 + t by omega]
      rw [hchoose, ← hpart]
      exact (Nat.add_le_add hT hU).trans_eq (Nat.add_comm _ _)

private def signedOrient (up : Bool) (a b c : Point) : ℝ :=
  (if up then 1 else -1) * orient a b c

private theorem turn_iff_signed (up : Bool) (a b c : Point) :
    turn up a b c ↔ 0 < signedOrient up a b c := by
  cases up <;> simp [turn, signedOrient]

private theorem turn_quad {up : Bool} {a b c d : Point}
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (h₁ : turn up a b c) (h₂ : turn up b c d) :
    turn up a b d ∧ turn up a c d := by
  rw [turn_iff_signed] at h₁ h₂
  simp only [turn_iff_signed]
  have hleft :
      (c.1 - b.1) * signedOrient up a b d =
        (d.1 - b.1) * signedOrient up a b c + (b.1 - a.1) * signedOrient up b c d := by
    unfold signedOrient orient
    ring
  have hright :
      (c.1 - b.1) * signedOrient up a c d =
        (c.1 - a.1) * signedOrient up b c d + (d.1 - c.1) * signedOrient up a b c := by
    unfold signedOrient orient
    ring
  constructor
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hleft]
    exact add_pos (mul_pos (sub_pos.mpr (hbc.trans hcd)) h₁) (mul_pos (sub_pos.mpr hab) h₂)
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hright]
    exact add_pos (mul_pos (sub_pos.mpr (hab.trans hbc)) h₂) (mul_pos (sub_pos.mpr hcd) h₁)

private theorem turns_tail {up : Bool} {a : Point} {l : List Point}
    (h : turns up (a :: l)) : turns up l := by
  rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
  · trivial
  · trivial
  · exact h.2

private theorem x_lt_next {a b : Point} {l : List Point}
    (h : (a :: b :: l).Pairwise (fun p q => p.1 < q.1)) : a.1 < b.1 :=
  (List.pairwise_cons.1 h).1 b (by simp)

private theorem turns_delete {up : Bool} {p : Point} {l : List Point} (pre : List Point)
    (hs : (pre ++ p :: l).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ p :: l)) : turns up (pre ++ l) := by
  induction pre with
  | nil => exact turns_tail ht
  | cons a pre ih =>
    cases pre with
    | nil =>
      rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
      · trivial
      · trivial
      · have hs' : (a :: p :: b :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
        have ht' : turns up (a :: p :: b :: c :: l) := ht
        have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
          (x_lt_next hs'.tail.tail) ht'.1 ht'.2.1
        exact ⟨hp.2, ht'.2.2⟩
    | cons b pre =>
      cases pre with
      | nil =>
        cases l with
        | nil => trivial
        | cons c l =>
          have hs' : (a :: b :: p :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
          have ht' : turns up (a :: b :: p :: c :: l) := ht
          have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
            (x_lt_next hs'.tail.tail) ht'.1 ht'.2.1
          exact ⟨hp.1, ih hs'.tail ht'.2⟩
      | cons c pre =>
        have ht' : turns up (a :: b :: c :: (pre ++ p :: l)) := ht
        exact ⟨ht'.1, ih hs.tail ht'.2⟩

private theorem turns_sublist_append {up : Bool} {l₁ l₂ : List Point} (h : List.Sublist l₁ l₂)
    (pre : List Point) (hs : (pre ++ l₂).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ l₂)) : turns up (pre ++ l₁) := by
  induction h generalizing pre with
  | slnil => exact ht
  | cons a h ih =>
    apply ih pre
    · apply List.Pairwise.sublist _ hs
      exact (List.Sublist.refl _).append (List.Sublist.cons _ (List.Sublist.refl _))
    · exact turns_delete pre hs ht
  | cons_cons a h ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [a]) (by simpa only [List.append_assoc, List.singleton_append] using hs)
        (by simpa only [List.append_assoc, List.singleton_append] using ht)

private theorem turn_of_mem {up : Bool} {X : Finset Point} {l : List Point}
    (h : IsSeq up X l) {a b c : Point} (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) : turn up a b c := by
  let r : Point → Point → Prop := fun a b => a.1 < b.1
  let : Std.Antisymm r := ⟨fun _ _ h₁ h₂ => (lt_asymm h₁ h₂).elim⟩
  let : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
  have htri : [a, b, c].Pairwise r := by simp [r, hab, hbc, hab.trans hbc]
  have hsub : [a, b, c] ⊆ l := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hsublist : List.Sublist [a, b, c] l :=
    List.sublist_of_subperm_of_pairwise (List.subperm_of_subset htri.nodup hsub) htri h.2.1
  have hh := turns_sublist_append hsublist [] h.2.1 h.2.2
  exact hh.1

/-- Asymmetric cups and caps: more than C(s+t,s) points in general position contain an
(s+2)-cup or a (t+2)-cap. -/
private theorem cups_caps_planar (s t : ℕ) (X : Finset (ℝ × ℝ)) (hX : PlanarGeneral X)
    (hcard : (s + t).choose s < X.card) :
    (∃ Y ⊆ X, Y.card = s + 2 ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → 0 < orient a b c) ∨
    (∃ Y ⊆ X, Y.card = t + 2 ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → orient a b c < 0) := by
  have key : ∀ (up : Bool) (k : ℕ), HasSeq up X k →
      ∃ Y ⊆ X, Y.card = k ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → turn up a b c := by
    rintro up k ⟨l, hl, hlen⟩
    have hnodup : l.Nodup := by
      apply hl.2.1.imp
      intro a b hab he
      subst b
      exact (lt_irrefl _) hab
    have hsub : l.toFinset ⊆ X := fun p hp => hl.1 p (List.mem_toFinset.1 hp)
    refine ⟨l.toFinset, hsub, (List.toFinset_card_of_nodup hnodup).trans hlen,
      hX.1.mono (Finset.coe_subset.mpr hsub), ?_⟩
    intro a ha b hb c hc hab hbc
    exact turn_of_mem hl (List.mem_toFinset.1 ha) (List.mem_toFinset.1 hb)
      (List.mem_toFinset.1 hc) hab hbc
  by_contra hcon
  rw [not_or] at hcon
  have h1 : ¬ HasSeq true X (s + 2) := fun h => hcon.1 (by
    obtain ⟨Y, hYX, hYc, hYi, hYt⟩ := key true _ h
    exact ⟨Y, hYX, hYc, hYi, fun a ha b hb c hc hab hbc => by
      simpa [turn] using hYt a ha b hb c hc hab hbc⟩)
  have h2 : ¬ HasSeq false X (t + 2) := fun h => hcon.2 (by
    obtain ⟨Y, hYX, hYc, hYi, hYt⟩ := key false _ h
    exact ⟨Y, hYX, hYc, hYi, fun a ha b hb c hc hab hbc => by
      simpa [turn] using hYt a ha b hb c hc hab hbc⟩)
  exact absurd (card_le_binomial s t X hX.1 hX.2 h1 h2) (not_le.mpr hcard)

/-- Consequently s+2 or t+2 points in convex position. -/
private theorem convex_of_cups_caps (s t : ℕ) (X : Finset (ℝ × ℝ)) (hX : PlanarGeneral X)
    (hcard : (s + t).choose s < X.card) :
    ∃ Y ⊆ X, (Y.card = s + 2 ∨ Y.card = t + 2) ∧ PlanarConvex Y := by
  rcases cups_caps_planar s t X hX hcard with
    ⟨Y, hYX, hYc, hYi, hY⟩ | ⟨Y, hYX, hYc, hYi, hY⟩
  · exact ⟨Y, hYX, Or.inl hYc, planarConvex_of_cup Y hYi hY⟩
  · exact ⟨Y, hYX, Or.inr hYc, planarConvex_of_cap Y hYi hY⟩

end CupsCaps

/-- The classical binomial bound settles the range 1 ≤ ε (a full end-to-end test of the
coordinate pipeline). -/
private theorem suk_planar_large_eps (ε : ℝ) (hε : 1 ≤ ε) :
    ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧
        ∀ X : Finset (ℝ × ℝ), X.card = N → PlanarGeneral X →
          ∃ Y ⊆ X, Y.card = n ∧ PlanarConvex Y := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  refine ⟨(2 * n - 4).choose (n - 2) + 1, ?_, ?_⟩
  · have h1 : (2 * n - 4).choose (n - 2) ≤ 2 ^ (2 * n - 4) := Nat.choose_le_two_pow _ _
    have h2 : (2 * n - 4).choose (n - 2) + 1 ≤ 2 ^ (2 * n) := by
      have : 2 ^ (2 * n - 4) < 2 ^ (2 * n) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have h3 : (((2 * n - 4).choose (n - 2) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * n) := by
      exact_mod_cast h2
    refine h3.trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hε) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · intro X hXc hX
    obtain ⟨Y, hYX, hYc, hYconv⟩ := convex_of_cups_caps (n - 2) (n - 2) X hX (by
      rw [hXc, show n - 2 + (n - 2) = 2 * n - 4 by omega]
      exact Nat.lt_succ_self _)
    have hYn : Y.card = n := by
      rcases hYc with h | h <;> omega
    exact ⟨Y, hYX, hYn, hYconv⟩

/-- REMAINING GAP (the whole of Suk 2017), purely in coordinates: for every ε in (0,1)
and all large n there is N at most 2^((1+ε)n) such that every N-point planar set in
general position has n strictly extreme points. -/
private theorem suk_planar_small_eps (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧
        ∀ X : Finset (ℝ × ℝ), X.card = N → PlanarGeneral X →
          ∃ Y ⊆ X, Y.card = n ∧ PlanarConvex Y := by
  sorry

private theorem suk_planar :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧
        ∀ X : Finset (ℝ × ℝ), X.card = N → PlanarGeneral X →
          ∃ Y ⊆ X, Y.card = n ∧ PlanarConvex Y := by
  intro ε hε
  by_cases h1 : 1 ≤ ε
  · exact suk_planar_large_eps ε h1
  · exact suk_planar_small_eps ε hε (lt_of_not_ge h1)

private theorem suk_finite_threshold :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧ N ∈ Erdos107.cardSet n := by
  intro ε hε
  filter_upwards [suk_planar ε hε] with n hn
  obtain ⟨N, hN, hX⟩ := hn
  exact ⟨N, hN, cardSet_of_planar hX⟩

end Erdos107Suk

theorem OMA.solution : type_of% @Erdos107.variants.su_bound := by
  exact Erdos107Suk.from_epsilon_exists Erdos107Suk.suk_finite_threshold
