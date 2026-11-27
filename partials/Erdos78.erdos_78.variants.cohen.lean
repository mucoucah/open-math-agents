import FormalConjectures.ErdosProblems.«78»

-- Problem: Erdős Problem 78 — cohen
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/78.lean:127 (declaration Erdos78.erdos_78.variants.cohen)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Two-source dispersers give Ramsey graphs by evaluating them on ordered pairs. -/

open Filter Real ComplexityTheory

namespace CohenRamsey

private lemma orderedSubsets {V : Type*} [LinearOrder V] (s : Finset V) {k : ℕ}
    (h : 2 * k ≤ s.card) :
    ∃ A B : Finset V, A ⊆ s ∧ B ⊆ s ∧ A.card = k ∧ B.card = k ∧
      ∀ u ∈ A, ∀ v ∈ B, u < v := by
  let e := s.orderEmbOfFin rfl
  let lo (i : Fin k) : Fin s.card := ⟨i, by have := i.isLt; omega⟩
  let hi (i : Fin k) : Fin s.card := ⟨k + i, by have := i.isLt; omega⟩
  have hlo : Function.Injective lo := by
    intro i j hij
    have hval := congrArg Fin.val hij
    exact Fin.ext hval
  have hhi : Function.Injective hi := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    change k + i.val = k + j.val at hval
    omega
  refine ⟨Finset.univ.image (e ∘ lo), Finset.univ.image (e ∘ hi), ?_, ?_,
    ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    exact s.orderEmbOfFin_mem rfl (lo i)
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact s.orderEmbOfFin_mem rfl (hi i)
  · rw [Finset.card_image_of_injective _ (e.injective.comp hlo), Finset.card_univ,
      Fintype.card_fin]
  · rw [Finset.card_image_of_injective _ (e.injective.comp hhi), Finset.card_univ,
      Fintype.card_fin]
  · intro u hu v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    apply e.strictMono
    change i.val < k + j.val
    have := i.isLt
    omega

private lemma noHomogeneousSet_of_rectangles {V : Type*} [LinearOrder V]
    (colour : V → V → Bool) {k m : ℕ} (hm : 2 * k ≤ m)
    (hcolour : ∀ (A B : Finset V), k ≤ A.card → k ≤ B.card →
      ∀ b : Bool, ∃ u ∈ A, ∃ v ∈ B, colour u v = b) :
    Erdos78.NoHomogeneousSet
      (SimpleGraph.fromRel fun u v : V ↦ u < v ∧ colour u v = true) m := by
  let G := SimpleGraph.fromRel fun u v : V ↦ u < v ∧ colour u v = true
  change G.CliqueFree m ∧ Gᶜ.CliqueFree m
  have adj_iff {u v : V} (huv : u < v) : G.Adj u v ↔ colour u v = true := by
    change (_ ∧ (_ ∨ _)) ↔ _
    simp [huv, huv.ne, not_lt.mpr huv.le]
  constructor
  · intro s hs
    obtain ⟨A, B, hAs, hBs, hA, hB, hAB⟩ :=
      orderedSubsets s (by simpa [hs.card_eq] using hm)
    obtain ⟨u, hu, v, hv, hc⟩ := hcolour A B hA.ge hB.ge false
    have huv := hAB u hu v hv
    have hadj := hs.isClique (hAs hu) (hBs hv) huv.ne
    simpa [hc] using (adj_iff huv).mp hadj
  · intro s hs
    obtain ⟨A, B, hAs, hBs, hA, hB, hAB⟩ :=
      orderedSubsets s (by simpa [hs.card_eq] using hm)
    obtain ⟨u, hu, v, hv, hc⟩ := hcolour A B hA.ge hB.ge true
    have huv := hAB u hu v hv
    have hnon := hs.isClique (hAs hu) (hBs hv) huv.ne
    exact ((SimpleGraph.compl_adj G u v).mp hnon).2 ((adj_iff huv).mpr hc)

private def width (n : ℕ) : ℕ := n.log2 + 1

private noncomputable def entropySize (D : ℝ) (d : ℕ) : ℕ := 2 ^ ⌈(log (d : ℝ)) ^ D⌉₊

/-- Both bits occur on every rectangle whose two sides have sufficient cardinality. -/
private def Disperses (f : ℕ → ℕ → ℕ → Bool) (D : ℝ) (d : ℕ) : Prop :=
  ∀ A B : Finset (Fin (2 ^ d)), entropySize D d ≤ A.card →
    entropySize D d ≤ B.card → ∀ b : Bool, ∃ u ∈ A, ∃ v ∈ B, f d u v = b

private def orderedOracle (f : ℕ → ℕ → ℕ → Bool) (x : List Bool × ℕ × ℕ) : Bool :=
  if x.2.1 < x.2.2 then f (width x.1.length) x.2.1 x.2.2 else false

private lemma le_pow_width (n : ℕ) : n ≤ 2 ^ width n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact ((Nat.log2_lt hn).mp (Nat.lt_succ_self n.log2)).le

private lemma tendsto_width : Tendsto width atTop atTop := by
  refine tendsto_atTop.mpr (fun k ↦ ?_)
  filter_upwards [eventually_ge_atTop (2 ^ k)] with n hn
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (Nat.two_pow_pos k) hn).ne'
  exact ((Nat.le_log2 hn0).mpr hn).trans (Nat.le_succ _)

private lemma noHomogeneousSet_of_disperses (f : ℕ → ℕ → ℕ → Bool)
    {D : ℝ} {n m : ℕ} (hm : 2 * entropySize D (width n) ≤ m)
    (hf : Disperses f D (width n)) :
    Erdos78.NoHomogeneousSet (Erdos78.explicitGraph (orderedOracle f) n) m := by
  let colour : Fin n → Fin n → Bool := fun u v ↦ f (width n) u v
  have hgraph : Erdos78.explicitGraph (orderedOracle f) n =
      SimpleGraph.fromRel (fun u v : Fin n ↦ u < v ∧ colour u v = true) := by
    ext u v
    simp only [Erdos78.explicitGraph, SimpleGraph.fromRel_adj]
    have hrel (a b : Fin n) :
        orderedOracle f (List.replicate n true, a.val, b.val) = true ↔
          a < b ∧ colour a b = true := by
      simp only [orderedOracle, List.length_replicate, colour, Fin.lt_def]
      by_cases hab : a.val < b.val <;> simp [hab]
    rw [hrel u v, hrel v u]
  rw [hgraph]
  refine noHomogeneousSet_of_rectangles colour hm (fun A B hA hB b ↦ ?_)
  let e := Fin.castLEEmb (le_pow_width n)
  obtain ⟨u, hu, v, hv, hc⟩ :=
    hf (A.map e) (B.map e) (by simpa using hA) (by simpa using hB) b
  obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
  exact ⟨u', hu', v', hv', hc⟩

private lemma twice_entropySize_le (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, 2 * entropySize D (width n) ≤
      ⌈(2 : ℝ) ^ (log (log (n : ℝ))) ^ (D + 1)⌉₊ := by
  have hlog : Tendsto (fun n : ℕ ↦ log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ ↦ log (log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_ge_atTop (1 : ℕ), tendsto_atTop.mp hlog 1,
    tendsto_atTop.mp hloglog (max 1 (max (log 3) ((2 : ℝ) ^ D + 2)))] with n hn hnlog hz
  let z := log (log (n : ℝ))
  have hz1 : 1 ≤ z := (le_max_left _ _).trans hz
  have hz3 : log 3 ≤ z := ((le_max_left _ _).trans (le_max_right _ _)).trans hz
  have hzD : (2 : ℝ) ^ D + 2 ≤ z :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hz
  have hwidth : (width n : ℝ) ≤ 3 * log (n : ℝ) := by
    have hpow : (2 : ℕ) ^ n.log2 ≤ n := (Nat.le_log2 (by omega)).mp le_rfl
    have hpow' : (2 : ℝ) ^ n.log2 ≤ (n : ℝ) := by exact_mod_cast hpow
    have hbound := Real.log_le_log (by positivity) hpow'
    rw [Real.log_pow] at hbound
    have hhalf : (1 : ℝ) / 2 ≤ log 2 := by linarith [Real.log_two_gt_d9]
    have hmul := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ (n.log2 : ℝ) by positivity)
    simp only [width, Nat.cast_add, Nat.cast_one]
    linarith
  have hw1 : 1 ≤ (width n : ℝ) := by
    exact_mod_cast (show 1 ≤ width n by simp [width])
  have hwlog : log (width n : ℝ) ≤ 2 * z := by
    have hbound := Real.log_le_log (by linarith : 0 < (width n : ℝ)) hwidth
    rw [Real.log_mul (by norm_num) (by linarith : log (n : ℝ) ≠ 0)] at hbound
    change log (width n : ℝ) ≤ 2 * log (log (n : ℝ))
    change log 3 ≤ log (log (n : ℝ)) at hz3
    linarith
  have hp := Real.rpow_le_rpow (Real.log_nonneg hw1) hwlog hD.le
  rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ z)] at hp
  have hbound : log (width n : ℝ) ^ D + 2 ≤ z ^ (D + 1) := by
    have hzp : 1 ≤ z ^ D := Real.one_le_rpow hz1 hD.le
    calc
      log (width n : ℝ) ^ D + 2 ≤ (2 : ℝ) ^ D * z ^ D + 2 := by linarith only [hp]
      _ ≤ ((2 : ℝ) ^ D + 2) * z ^ D := by nlinarith
      _ ≤ z * z ^ D := mul_le_mul_of_nonneg_right hzD (by positivity)
      _ = z ^ (D + 1) := by rw [Real.rpow_add (by linarith : 0 < z), Real.rpow_one, mul_comm]
  let k := ⌈log (width n : ℝ) ^ D⌉₊
  have hk : (k : ℝ) < log (width n : ℝ) ^ D + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Real.log_nonneg hw1) _)
  have hk' : ((k + 1 : ℕ) : ℝ) ≤ z ^ (D + 1) := by
    push_cast
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hk'
  rw [Real.rpow_natCast] at hpow
  change 2 * 2 ^ k ≤ ⌈(2 : ℝ) ^ z ^ (D + 1)⌉₊
  rw [mul_comm 2, ← pow_succ]
  exact_mod_cast (hpow.trans (Nat.le_ceil _))

private lemma cohen_of_disperser (D : ℝ) (hD : 0 < D) (f : ℕ → ℕ → ℕ → Bool)
    (hpoly : IsPolyTime (orderedOracle f)) (hf : ∀ᶠ d in atTop, Disperses f D d) :
    ∃ C > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n : ℕ in atTop,
        Erdos78.NoHomogeneousSet (Erdos78.explicitGraph adj n)
          ⌈(2 : ℝ) ^ (log (log (n : ℝ))) ^ C⌉₊ := by
  refine ⟨D + 1, by linarith, orderedOracle f, hpoly, ?_⟩
  filter_upwards [twice_entropySize_le D hD, tendsto_width.eventually hf] with n hm hfn
  exact noHomogeneousSet_of_disperses f hm hfn

end CohenRamsey

theorem OMA.solution : type_of% @Erdos78.erdos_78.variants.cohen := by
  suffices h : ∃ (D : ℝ) (f : ℕ → ℕ → ℕ → Bool), 0 < D ∧
      IsPolyTime (CohenRamsey.orderedOracle f) ∧
      ∀ᶠ d in atTop, CohenRamsey.Disperses f D d by
    obtain ⟨D, f, hD, hpoly, hf⟩ := h
    exact CohenRamsey.cohen_of_disperser D hD f hpoly hf
  sorry

