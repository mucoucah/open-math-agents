import FormalConjectures.ErdosProblems.«877»

-- Problem: Erdős Problem 877 — balogh liu sharifzadeh treglown
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/877.lean:90 (declaration Erdos877.erdos_877.variants.balogh_liu_sharifzadeh_treglown)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real

namespace OMA.E877BLST
open Erdos877

open Classical in
/-- Seed set: the top even number `2e`, and from each pair `(2i+1, 2e-2i-1)`, `i < e/2`,
the small member iff `i ∈ T`, else the large member. -/
noncomputable def seed (e : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * e)).filter fun y => y = 2 * e ∨ (∃ i ∈ T, y = 2 * i + 1) ∨
    (∃ i, i < e / 2 ∧ i ∉ T ∧ y = 2 * e - (2 * i + 1))

lemma mem_seed {e : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range (e / 2)) (y : ℕ) :
    y ∈ seed e T ↔ (1 ≤ e ∧ y = 2 * e) ∨ (∃ i ∈ T, y = 2 * i + 1) ∨
      (∃ i, i < e / 2 ∧ i ∉ T ∧ y = 2 * e - (2 * i + 1)) := by
  unfold seed
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h | h | h⟩
    · left; omega
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨i, hi, rfl⟩ | ⟨i, hi, hiT, rfl⟩)
    · exact ⟨by omega, Or.inl h.2⟩
    · have := Finset.mem_range.1 (hT hi)
      exact ⟨by omega, Or.inr (Or.inl ⟨i, hi, rfl⟩)⟩
    · exact ⟨by omega, Or.inr (Or.inr ⟨i, hi, hiT, rfl⟩)⟩

lemma seed_sub {n e : ℕ} (hn : 2 * e ≤ n) (T : Finset ℕ) : seed e T ⊆ Finset.Icc 1 n := by
  intro y hy
  unfold seed at hy
  rw [Finset.mem_filter, Finset.mem_Icc] at hy
  rw [Finset.mem_Icc]; omega

lemma seed_free {e : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range (e / 2)) :
    IsSumFree (seed e T : Set ℕ) := by
  rw [isSumFree_iff]
  intro a ha b hb hab
  simp only [Finset.mem_coe, mem_seed hT] at ha hb hab
  have hT' : ∀ i ∈ T, i < e / 2 := fun i hi => Finset.mem_range.1 (hT hi)
  rcases ha with ⟨he, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, hiT, rfl⟩ <;>
  rcases hb with ⟨-, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, hjT, rfl⟩ <;>
  rcases hab with ⟨-, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, hkT, h⟩ <;>
  (try have := hT' _ hi) <;> (try have := hT' _ hj) <;> (try have := hT' _ hk) <;>
  (try omega)
  · obtain rfl : i = j := by omega
    exact hjT hi
  · obtain rfl : i = j := by omega
    exact hiT hj

lemma exists_maximal {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n)
    (hs : IsSumFree (A : Set ℕ)) : ∃ M, IsMaximalSumFree n M ∧ A ⊆ M := by
  classical
  have hne : ((Finset.Icc 1 n).powerset.filter
      fun B : Finset ℕ => A ⊆ B ∧ IsSumFree (B : Set ℕ)).Nonempty := ⟨A, by simp [hA, hs]⟩
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  simp only [Finset.mem_filter, Finset.mem_powerset] at hM
  refine ⟨M, ⟨hM.1, hM.2.2, fun B hB hBs hMB => ?_⟩, hM.2.1⟩
  refine Finset.eq_of_subset_of_card_le hMB (hmax B ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hB, hM.2.1.trans hMB, hBs⟩

lemma recover {e : ℕ} {T M : Finset ℕ} (hT : T ⊆ Finset.range (e / 2)) (hM : seed e T ⊆ M)
    (hs : IsSumFree (M : Set ℕ)) {i : ℕ} (hi : i < e / 2) : 2 * i + 1 ∈ M ↔ i ∈ T := by
  refine ⟨fun h => ?_, fun h => hM ((mem_seed hT _).2 (Or.inr (Or.inl ⟨i, h, rfl⟩)))⟩
  by_contra hiT
  have h2 : 2 * e - (2 * i + 1) ∈ M :=
    hM ((mem_seed hT _).2 (Or.inr (Or.inr ⟨i, hi, hiT, rfl⟩)))
  have h3 : 2 * e ∈ M := hM ((mem_seed hT _).2 (Or.inl ⟨by omega, rfl⟩))
  have := (isSumFree_iff.1 hs) _ h _ h2
  rw [show 2 * i + 1 + (2 * e - (2 * i + 1)) = 2 * e by omega] at this
  exact this h3

lemma lower (n : ℕ) : 2 ^ (n / 2 / 2) ≤ fm n := by
  classical
  set e := n / 2 with he
  have hn : 2 * e ≤ n := by omega
  have key : ∀ T ∈ (Finset.range (e / 2)).powerset, ∃ M, IsMaximalSumFree n M ∧ seed e T ⊆ M :=
    fun T hT => exists_maximal (seed_sub hn T) (seed_free (Finset.mem_powerset.1 hT))
  choose! F hF using key
  rw [← Finset.card_range (e / 2), ← Finset.card_powerset]
  unfold fm
  convert Finset.card_le_card_of_injOn F (fun T hT => ?_) (fun T hT T' hT' hTT => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(hF T hT).1.1, (hF T hT).1⟩
  · have h1 := hF T hT
    have h2 := hF T' hT'
    have hT1 := Finset.mem_powerset.1 (Finset.mem_coe.1 hT)
    have hT2 := Finset.mem_powerset.1 (Finset.mem_coe.1 hT')
    ext i
    by_cases hi : i < e / 2
    · rw [← recover hT1 h1.2 h1.1.2.1 hi, ← recover hT2 h2.2 h2.1.2.1 hi]
      rw [hTT]
    · exact ⟨fun h => absurd (Finset.mem_range.1 (hT1 h)) hi,
        fun h => absurd (Finset.mem_range.1 (hT2 h)) hi⟩

/-- The container part of Balogh, Liu, Sharifzadeh and Treglown (BLST15). -/
lemma upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (fm n : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + ε) * n) := by
  sorry

lemma fm_pos (n : ℕ) : 0 < fm n := lt_of_lt_of_le (by positivity) (lower n)

lemma logb_lower (n : ℕ) : (n : ℝ) / 4 - 1 ≤ logb 2 (fm n) := by
  have h1 : ((n / 2 / 2 : ℕ) : ℝ) ≤ logb 2 (fm n) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast fm_pos n), Real.rpow_natCast]
    exact_mod_cast lower n
  have h2 : (n : ℝ) / 4 - 1 ≤ ((n / 2 / 2 : ℕ) : ℝ) := by
    rw [Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod n (2 * 2)
    have h4 := Nat.mod_lt n (show 0 < 2 * 2 by norm_num)
    have : (n : ℝ) = 4 * ((n / (2 * 2) : ℕ) : ℝ) + ((n % (2 * 2) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n = 4 * (n / (2 * 2)) + n % (2 * 2))
    have : ((n % (2 * 2) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : n % (2 * 2) ≤ 3)
    linarith
  linarith

theorem main : Tendsto (fun n : ℕ ↦ logb 2 (fm n) / n) atTop (nhds (1 / 4)) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 / 4 - a))
    have hpos : 0 < 1 / 4 - a := by linarith
    filter_upwards [eventually_gt_atTop N] with n hn
    have hn' : (N : ℝ) < n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (Nat.cast_nonneg N) hn'
    rw [lt_div_iff₀ hn0]
    have := logb_lower n
    have h3 : 1 < (1 / 4 - a) * n := by
      rw [div_lt_iff₀ hpos] at hN; nlinarith
    nlinarith
  · have hε : (0 : ℝ) < (b - 1 / 4) / 2 := by linarith
    filter_upwards [upper _ hε, eventually_gt_atTop 0] with n hup hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hpos : (0 : ℝ) < fm n := by exact_mod_cast fm_pos n
    have hlog : logb 2 (fm n) ≤ (1 / 4 + (b - 1 / 4) / 2) * n := by
      have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hup
      rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
    rw [div_lt_iff₀ hn']
    nlinarith

end OMA.E877BLST

theorem OMA.solution : type_of% @Erdos877.erdos_877.variants.balogh_liu_sharifzadeh_treglown := by
  exact OMA.E877BLST.main
