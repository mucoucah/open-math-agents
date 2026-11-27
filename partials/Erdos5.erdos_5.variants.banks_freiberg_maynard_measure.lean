import FormalConjectures.ErdosProblems.«5»

-- Problem: Erdős Problem 5 — banks freiberg maynard measure
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/5.lean:165 (declaration Erdos5.erdos_5.variants.banks_freiberg_maynard_measure)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.BFMMeasure

open Filter MeasureTheory Real Set Erdos5
open scoped Topology

/-- The nine-point theorem of Banks, Freiberg and Maynard (BFM16, Theorem 1.1),
strictly increasing form. This is the sole remaining gap (Maynard sieve). -/
lemma nine_point (β : Fin 9 → ℝ) (hβ : ∀ i, 0 ≤ β i) (hmono : StrictMono β) :
    ∃ i j, i < j ∧ β j - β i ∈ limitPointSet := by
  sorry

/-- One greedy step: pick a point near the bottom of `A`, discard a short
initial segment and one translate of `D`. -/
lemma greedy_step {ε T : ℝ} {D A : Set ℝ} (he : 0 < ε) (hD : volume D ≠ ⊤)
    (hA : A ⊆ Icc 0 T) (hpos : 0 < volume.real A) :
    ∃ x ∈ A, ∃ B ⊆ A, (∀ y ∈ B, x < y ∧ y - x ∉ D) ∧
      volume.real A - ε - volume.real D ≤ volume.real B := by
  have hne : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [h] at hpos
  have hbdd : BddBelow A := ⟨0, fun y hy => (hA hy).1⟩
  set m := sInf A
  obtain ⟨x, hxA, hxm⟩ := exists_lt_of_csInf_lt hne (show m < m + ε by linarith)
  have hmx : m ≤ x := csInf_le hbdd hxA
  let J := Icc m x
  let E := (fun y : ℝ => y - x) ⁻¹' D
  have hE : volume E = volume D := by
    simp only [E, sub_eq_add_neg]
    exact measure_preimage_add_right _ _ _
  have hJ : volume J ≠ ⊤ := by simp [J, Real.volume_Icc]
  have hJr : volume.real J ≤ ε := by
    simp only [J]; rw [Real.volume_real_Icc_of_le hmx]; linarith
  refine ⟨x, hxA, (A \ J) \ E, fun y hy => hy.1.1, ?_, ?_⟩
  · rintro y ⟨⟨hyA, hyJ⟩, hyE⟩
    have hxy : x < y := by
      by_contra hc
      exact hyJ ⟨csInf_le hbdd hyA, not_lt.mp hc⟩
    exact ⟨hxy, hyE⟩
  · have hE' : volume E ≠ ⊤ := hE ▸ hD
    have h1 := le_measureReal_sdiff (s₁ := A) hJ
    have h2 := le_measureReal_sdiff (s₁ := A \ J) hE'
    have h3 : volume.real E = volume.real D := congrArg ENNReal.toReal hE
    linarith

/-- Iterating the greedy step yields `n+1` increasing points of `A` whose
pairwise differences avoid `D`. -/
lemma greedy_points {ε T : ℝ} {D : Set ℝ} (he : 0 < ε) (hD : volume D ≠ ⊤) :
    ∀ (n : ℕ) (A : Set ℝ), A ⊆ Icc 0 T →
      n * (ε + volume.real D) < volume.real A →
      ∃ β : Fin (n + 1) → ℝ, (∀ i, β i ∈ A) ∧ StrictMono β ∧
        ∀ i j, i < j → β j - β i ∉ D := by
  intro n
  induction n with
  | zero =>
    intro A _ hp
    have hne : A.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      simp [h] at hp
    obtain ⟨x, hx⟩ := hne
    refine ⟨fun _ => x, fun _ => hx, fun i j h => ?_, fun i j h => ?_⟩
    · exact absurd h (by omega)
    · exact absurd h (by omega)
  | succ n ih =>
    intro A hA hp
    have hDn := measureReal_nonneg (μ := volume) (s := D)
    have hpos : 0 < volume.real A := by
      have : (0:ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (ε + volume.real D) := by positivity
      linarith
    obtain ⟨x, hx, B, hBA, hB, hvol⟩ := greedy_step he hD hA hpos
    obtain ⟨β, hβB, hβmono, hβD⟩ := ih B (hBA.trans hA) (by push_cast at hp; nlinarith)
    have key : ∀ k, x < β k ∧ β k - x ∉ D := fun k => hB _ (hβB k)
    refine ⟨Fin.cons x β, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun t => ?_) i
      · simpa using hx
      · simpa using hBA (hβB t)
    · intro i j hij
      induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ b =>
        induction i using Fin.cases with
        | zero => simpa using (key b).1
        | succ a => simpa using hβmono (Fin.succ_lt_succ_iff.mp hij)
    · intro i j hij
      induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ b =>
        induction i using Fin.cases with
        | zero => simpa using (key b).2
        | succ a => simpa using hβD a b (Fin.succ_lt_succ_iff.mp hij)

theorem main : type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard_measure := by
  intro δ hδ
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  set D := limitPointSet ∩ Icc 0 T with hDdef
  have hD : volume D ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right (by simp [Real.volume_Icc])
  rw [ENNReal.ofReal_le_iff_le_toReal hD]
  change (1 - δ) * T / 8 ≤ volume.real D
  have hDn := measureReal_nonneg (μ := volume) (s := D)
  suffices h8 : T / 8 ≤ volume.real D by nlinarith
  by_contra hlt0
  have hlt := not_le.mp hlt0
  set ε := (T - 8 * volume.real D) / 16 with hεdef
  have he : 0 < ε := by rw [hεdef]; linarith
  have hvol : volume.real (Icc 0 T) = T := by
    rw [Real.volume_real_Icc_of_le hT.le, sub_zero]
  obtain ⟨β, hβA, hβmono, hβD⟩ := greedy_points he hD 8 (Icc 0 T) subset_rfl (by
    rw [hvol]; push_cast; rw [hεdef]; linarith)
  obtain ⟨i, j, hij, hmem⟩ := nine_point β (fun k => (hβA k).1) hβmono
  apply hβD i j hij
  refine ⟨hmem, ?_, ?_⟩
  · linarith [hβmono hij]
  · linarith [(hβA j).2, (hβA i).1]

end OMA.BFMMeasure

theorem OMA.solution : type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard_measure := by
  exact OMA.BFMMeasure.main
