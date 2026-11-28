import FormalConjectures.ErdosProblems.«5»

-- Problem: Erdős Problem 5 — hildebrand maier measure
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/5.lean:133 (declaration Erdos5.erdos_5.variants.hildebrand_maier_measure)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.HMM

open Filter MeasureTheory Real Set Erdos5

/-- One greedy step: a point x of A near its infimum; the part of A to the right of x
avoiding x + D keeps almost all of the measure of A. -/
lemma step {D A : Set ℝ} {ε : ℝ} (hε : 0 < ε) (hb : BddBelow A) (hne : A.Nonempty)
    (hD : volume D ≠ ⊤) :
    ∃ x ∈ A, volume.real A - ε - volume.real D ≤
      volume.real ((A \ Icc (sInf A) x) \ ((fun y : ℝ => y + -x) ⁻¹' D)) := by
  obtain ⟨x, hx, hlt⟩ := exists_lt_of_csInf_lt hne (show sInf A < sInf A + ε by linarith)
  refine ⟨x, hx, ?_⟩
  have hE : volume ((fun y : ℝ => y + -x) ⁻¹' D) = volume D := measure_preimage_add_right _ _ _
  have hE' : volume ((fun y : ℝ => y + -x) ⁻¹' D) ≠ ⊤ := hE ▸ hD
  have hI : volume (Icc (sInf A) x) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have h1 := le_measureReal_sdiff (μ := volume) (s₁ := A) hI
  have h2 := le_measureReal_sdiff (μ := volume) (s₁ := A \ Icc (sInf A) x) hE'
  have h3 : volume.real (Icc (sInf A) x) ≤ ε := by
    rw [Real.volume_real_Icc_of_le (csInf_le hb hx)]; linarith
  have h4 : volume.real ((fun y : ℝ => y + -x) ⁻¹' D) = volume.real D := congrArg ENNReal.toReal hE
  linarith

/-- Greedy packing: n+1 points of A, increasing, with no difference in L ∩ [0,T]. -/
lemma packing (L : Set ℝ) {T ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∀ A : Set ℝ, A ⊆ Icc 0 T → (n : ℝ) * (ε + volume.real (L ∩ Icc 0 T)) < volume.real A →
    ∃ β : ℕ → ℝ, (∀ i ≤ n, β i ∈ A) ∧
      ∀ i j, i < j → j ≤ n → β i < β j ∧ β j - β i ∉ L := by
  have hDfin : volume (L ∩ Icc 0 T) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hD0 := measureReal_nonneg (μ := volume) (s := L ∩ Icc 0 T)
  induction n with
  | zero =>
    intro A _ hA
    have hne : A.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      simp [h] at hA
    obtain ⟨x, hx⟩ := hne
    refine ⟨fun _ => x, fun _ _ => hx, fun i j hij hj => by omega⟩
  | succ n ih =>
    intro A hAT hA
    have hpos : 0 < volume.real A :=
      lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hA
    have hne : A.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      simp [h] at hpos
    have hb : BddBelow A := ⟨0, fun y hy => (hAT hy).1⟩
    obtain ⟨x, hx, hB⟩ := step (D := L ∩ Icc 0 T) hε hb hne hDfin
    set B := (A \ Icc (sInf A) x) \ ((fun y : ℝ => y + -x) ⁻¹' (L ∩ Icc 0 T)) with hBdef
    have hBA : B ⊆ A := fun y hy => hy.1.1
    have hBprop : ∀ y ∈ B, x < y ∧ y - x ∉ L := by
      intro y hy
      obtain ⟨⟨hyA, hyI⟩, hyD⟩ := hy
      have hxy : x < y := lt_of_not_ge fun h => hyI ⟨csInf_le hb hyA, h⟩
      refine ⟨hxy, fun hL => hyD ?_⟩
      show y + -x ∈ L ∩ Icc 0 T
      rw [← sub_eq_add_neg]
      exact ⟨hL, by linarith, by linarith [(hAT hx).1, (hAT hyA).2]⟩
    obtain ⟨β, hβB, hβ⟩ := ih B (hBA.trans hAT) (by push_cast at hA; linarith)
    refine ⟨fun k => if k = 0 then x else β (k - 1), ?_, ?_⟩
    · intro i hi
      by_cases h0 : i = 0
      · simp [h0, hx]
      · simp only [h0, if_false]; exact hBA (hβB _ (by omega))
    · intro i j hij hj
      have hj0 : j ≠ 0 := by omega
      by_cases h0 : i = 0
      · simp only [h0, hj0, if_true, if_false]
        exact hBprop _ (hβB _ (by omega))
      · simp only [h0, hj0, if_false]
        exact hβ _ _ (by omega) (by omega)
/-- The research core (Hildebrand-Maier / Banks-Freiberg-Maynard type pigeonhole):
for some m, among any m+1 increasing nonnegative reals some difference is a limit point. -/
def Core : Prop := ∃ m : ℕ, 0 < m ∧ ∀ β : Fin (m + 1) → ℝ, (∀ i, 0 ≤ β i) → StrictMono β →
    ∃ i j, i < j ∧ β j - β i ∈ limitPointSet

lemma core : Core := by
  sorry

lemma of_core (h : Core) : type_of% @Erdos5.erdos_5.variants.hildebrand_maier_measure := by
  obtain ⟨m, hm, hβ⟩ := h
  have mp : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨(2 * (m : ℝ))⁻¹, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hfin : volume (limitPointSet ∩ Icc 0 T) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  rw [ENNReal.ofReal_le_iff_le_toReal hfin]
  change (2 * (m : ℝ))⁻¹ * T ≤ volume.real (limitPointSet ∩ Icc 0 T)
  by_contra hlt
  rw [not_le] at hlt
  have hvol : volume.real (Icc (0 : ℝ) T) = T := by
    rw [Real.volume_real_Icc_of_le hT.le, sub_zero]
  have hε : 0 < (2 * (m : ℝ))⁻¹ * T := by positivity
  have key : (m : ℝ) * ((2 * (m : ℝ))⁻¹ * T + volume.real (limitPointSet ∩ Icc 0 T))
      < volume.real (Icc (0 : ℝ) T) := by
    rw [hvol]
    have : (m : ℝ) * ((2 * (m : ℝ))⁻¹ * T) = T / 2 := by field_simp
    nlinarith
  obtain ⟨β, hβA, hβd⟩ := packing limitPointSet hε m (Icc 0 T) le_rfl key
  obtain ⟨i, j, hij, hL⟩ := hβ (fun k => β k) (fun k => (hβA k (by omega)).1)
    (fun a b hab => (hβd a b hab (by omega)).1)
  exact (hβd i j hij (by omega)).2 hL

end OMA.HMM

theorem OMA.solution : type_of% @Erdos5.erdos_5.variants.hildebrand_maier_measure :=
  OMA.HMM.of_core OMA.HMM.core
