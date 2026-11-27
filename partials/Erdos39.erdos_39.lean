import FormalConjectures.ErdosProblems.«39»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A finite-prefix criterion for dense infinite Sidon sets. -/

-- Problem: Erdős Problem 39
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/39.lean:38 (declaration Erdos39.erdos_39)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Erdos39

open Asymptotics Filter

private noncomputable def exponent (k : ℕ) : ℝ :=
  1 / 2 - 1 / ((k : ℝ) + 4)

private noncomputable def prefixCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Set.Icc 1 N ∩ A).ncard : ℝ)

/-- At each cutoff a single Sidon set must meet all the prefix bounds tested so far. -/
def HasFiniteWitnesses (T : ℕ → ℕ) : Prop :=
  ∀ M, ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 M ∧ IsSidon (B : Set ℕ) ∧
    ∀ k ≤ M, ∀ N ≤ M, T k ≤ N →
      N ^ (k + 2) ≤ (Finset.Icc 1 N ∩ B).card ^ (2 * (k + 4))

private lemma prefix_power_iff (B : Finset ℕ) (k N : ℕ) :
    N ^ (k + 2) ≤ (Finset.Icc 1 N ∩ B).card ^ (2 * (k + 4)) ↔
      (N : ℝ) ^ exponent k ≤ prefixCount (B : Set ℕ) N := by
  let d : ℕ := 2 * (k + 4)
  have hd : d ≠ 0 := by dsimp [d]; omega
  have hexp : exponent k * (d : ℝ) = ((k + 2 : ℕ) : ℝ) := by
    unfold exponent d
    push_cast
    field_simp
    ring
  have hpow : ((N : ℝ) ^ exponent k) ^ d = ((N ^ (k + 2) : ℕ) : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N), hexp, Real.rpow_natCast, Nat.cast_pow]
  have hc : prefixCount (B : Set ℕ) N = ((Finset.Icc 1 N ∩ B).card : ℝ) := by
    rw [prefixCount, ← Finset.coe_Icc, ← Finset.coe_inter, Set.ncard_coe_finset]
  change N ^ (k + 2) ≤ (Finset.Icc 1 N ∩ B).card ^ d ↔ _
  rw [hc, ← pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (Nat.cast_nonneg _) hd, hpow, ← Nat.cast_pow, Nat.cast_le]

private lemma tendsto_nat_rpow {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) ^ s) atTop atTop :=
  (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop

private lemma exists_exponent_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ k, 1 / 2 - ε ≤ exponent k := by
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / ε)
  refine ⟨k, sub_le_sub_left ?_ _⟩
  have h : 1 / ε ≤ (k : ℝ) + 4 := hk.trans (by linarith)
  have hmul := (div_le_iff₀ hε).mp h
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 4)).mpr
    (by simpa [mul_comm] using hmul)

/-- Big-O at all exponents below one half gives eventual bounds with coefficient one. -/
private lemma eventual_lower_bound {A : Set ℕ}
    (hA : ∀ ε > (0 : ℝ),
      (fun N : ℕ ↦ (N : ℝ) ^ (1 / 2 - ε)) =O[atTop] prefixCount A)
    (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ exponent k ≤ prefixCount A N := by
  let δ : ℝ := (1 / ((k : ℝ) + 4)) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC⟩ := isBigO_iff.mp (hA δ hδ)
  filter_upwards [hC, (tendsto_nat_rpow hδ).eventually_ge_atTop C,
    eventually_gt_atTop (0 : ℕ)] with N hN hNC hNpos
  have hx : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hcount : 0 ≤ prefixCount A N := Nat.cast_nonneg _
  have hN' : (N : ℝ) ^ (1 / 2 - δ) ≤ C * prefixCount A N := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),
      Real.norm_of_nonneg hcount] using hN
  have hexp : exponent k + δ = 1 / 2 - δ := by
    unfold exponent δ
    ring
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hx δ)).mp
  calc
    (N : ℝ) ^ exponent k * (N : ℝ) ^ δ = (N : ℝ) ^ (1 / 2 - δ) := by
      rw [← Real.rpow_add hx, hexp]
    _ ≤ C * prefixCount A N := hN'
    _ ≤ prefixCount A N * (N : ℝ) ^ δ := by
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left hNC hcount

lemma finiteWitnesses_of_bigO {A : Set ℕ} (hs : IsSidon A)
    (hA : ∀ ε > (0 : ℝ),
      (fun N : ℕ ↦ (N : ℝ) ^ (1 / 2 - ε)) =O[atTop] prefixCount A) :
    ∃ T, HasFiniteWitnesses T := by
  classical
  choose T hT using fun k ↦ eventually_atTop.mp (eventual_lower_bound hA k)
  refine ⟨T, fun M ↦ ?_⟩
  let B := (Finset.Icc 1 M).filter (· ∈ A)
  have hB : (B : Set ℕ) = Set.Icc 1 M ∩ A := by
    ext x
    simp [B]
  refine ⟨B, Finset.filter_subset _ _, ?_, ?_⟩
  · rw [hB]
    intro a ha b hb c hc d hd heq
    exact hs a ha.2 b hb.2 c hc.2 d hd.2 heq
  · intro k _ N hNM hTN
    apply (prefix_power_iff B k N).mpr
    have hprefix : Set.Icc 1 N ∩ (B : Set ℕ) = Set.Icc 1 N ∩ A := by
      rw [hB]
      ext x
      exact ⟨fun hx ↦ ⟨hx.1, hx.2.2⟩,
        fun hx ↦ ⟨hx.1, ⟨hx.1.1, hx.1.2.trans hNM⟩, hx.2⟩⟩
    simpa only [prefixCount, hprefix] using hT k N hTN

/-- Take the limit of finite witnesses along an ultrafilter extending the tail filter. -/
private lemma limit_of_finiteWitnesses {T : ℕ → ℕ} (hT : HasFiniteWitnesses T) :
    ∃ A : Set ℕ, IsSidon A ∧
      ∀ k N, T k ≤ N → (N : ℝ) ^ exponent k ≤ prefixCount A N := by
  classical
  choose B _ hsid hlower using hT
  obtain ⟨u, hu⟩ := Filter.exists_ultrafilter_le (atTop : Filter ℕ)
  let A : Set ℕ := {x | ∀ᶠ M in (u : Filter ℕ), x ∈ B M}
  refine ⟨A, ?_, ?_⟩
  · intro a ha b hb c hc d hd heq
    have hpair : ∀ᶠ M in (u : Filter ℕ), (a = b ∧ c = d) ∨ (a = d ∧ c = b) := by
      change (∀ᶠ M in (u : Filter ℕ), a ∈ B M) at ha
      change (∀ᶠ M in (u : Filter ℕ), b ∈ B M) at hb
      change (∀ᶠ M in (u : Filter ℕ), c ∈ B M) at hc
      change (∀ᶠ M in (u : Filter ℕ), d ∈ B M) at hd
      filter_upwards [ha, hb, hc, hd] with M ha' hb' hc' hd'
      exact hsid M a ha' b hb' c hc' d hd' heq
    exact hpair.exists.choose_spec
  · intro k N hTN
    have hagrees : ∀ᶠ M in (u : Filter ℕ), ∀ x ∈ Set.Icc 1 N, x ∈ B M ↔ x ∈ A := by
      apply (Set.finite_Icc 1 N).eventually_all.mpr
      intro x _
      rcases u.em (fun M ↦ x ∈ B M) with hx | hx
      · exact hx.mono fun _ h ↦ iff_of_true h hx
      · have hn : x ∉ A := u.eventually_not.mp hx
        exact hx.mono fun _ h ↦ iff_of_false h hn
    have hfit : ∀ᶠ M in (u : Filter ℕ), (N : ℝ) ^ exponent k ≤ prefixCount A N := by
      filter_upwards [hu (eventually_ge_atTop k), hu (eventually_ge_atTop N), hagrees]
        with M hk hN hsame
      have heq : Set.Icc 1 N ∩ (B M : Set ℕ) = Set.Icc 1 N ∩ A := by
        ext x
        exact and_congr_right (hsame x)
      have hlo := (prefix_power_iff (B M) k N).mp (hlower M k hk N hN hTN)
      simpa only [prefixCount, heq] using hlo
    exact hfit.exists.choose_spec

lemma exists_of_finiteWitnesses {T : ℕ → ℕ} (hT : HasFiniteWitnesses T) :
    ∃ (A : Set ℕ), A.Infinite ∧ IsSidon A ∧ ∀ ε > (0 : ℝ),
      (fun N : ℕ ↦ (N : ℝ) ^ (1 / 2 - ε)) =O[atTop] prefixCount A := by
  obtain ⟨A, hs, hlo⟩ := limit_of_finiteWitnesses hT
  refine ⟨A, ?_, hs, ?_⟩
  · intro hf
    have hp : 0 < exponent 0 := by norm_num [exponent]
    have hlarge := (tendsto_nat_rpow hp).eventually_gt_atTop (A.ncard : ℝ)
    obtain ⟨N, hN, hTN⟩ := (hlarge.and (eventually_ge_atTop (T 0))).exists
    have hcap : prefixCount A N ≤ (A.ncard : ℝ) := by
      unfold prefixCount
      exact_mod_cast Set.ncard_le_ncard Set.inter_subset_right hf
    exact (not_lt_of_ge ((hlo 0 N hTN).trans hcap)) hN
  · intro ε hε
    obtain ⟨k, hk⟩ := exists_exponent_ge hε
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop (T k)] with N hN hTN
    have hx : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _),
      Real.norm_of_nonneg (show 0 ≤ prefixCount A N from Nat.cast_nonneg _)]
    exact (Real.rpow_le_rpow_of_exponent_le hx hk).trans (hlo k N hTN)

private noncomputable def greedyPrefix : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
    open Classical in
    if IsSidon (↑(insert (n + 1) (greedyPrefix n)) : Set ℕ) then
      insert (n + 1) (greedyPrefix n)
    else greedyPrefix n

private lemma greedyPrefix_sidon (n : ℕ) : IsSidon (greedyPrefix n : Set ℕ) := by
  induction n with
  | zero => simp [greedyPrefix, IsSidon]
  | succ n ih =>
    rw [greedyPrefix]
    split_ifs with h
    · exact h
    · exact ih

private lemma greedyPrefix_subset (n : ℕ) : greedyPrefix n ⊆ Finset.Icc 1 n := by
  induction n with
  | zero => simp [greedyPrefix]
  | succ n ih =>
    have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 (n + 1) := by
      intro x hx
      obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨h₁, h₂.trans (Nat.le_succ n)⟩
    rw [greedyPrefix]
    split_ifs
    · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ih.trans hsub⟩
    · exact ih.trans hsub

private lemma greedyPrefix_mono : Monotone greedyPrefix := by
  apply monotone_nat_of_le_succ
  intro n
  rw [greedyPrefix]
  split_ifs
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

private lemma greedyPrefix_card (N : ℕ) : N ≤ (greedyPrefix N).card ^ 3 := by
  classical
  let B := greedyPrefix N
  let blocked := (B.offDiag ×ˢ B).image (fun p ↦ p.1.2 + p.2 - p.1.1)
  have hsub : Finset.Icc 1 N ⊆ B ∪ blocked := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _ hxB
    obtain ⟨hpos, hxN⟩ := Finset.mem_Icc.mp hx
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
    have hnN : n ≤ N := by omega
    have hbad : ¬ IsSidon (↑(insert (n + 1) (greedyPrefix n)) : Set ℕ) := by
      intro hs
      apply hxB
      apply greedyPrefix_mono hxN
      rw [greedyPrefix, if_pos hs]
      exact Finset.mem_insert_self _ _
    rw [Finset.coe_insert, ← Set.union_singleton, Set.IsSidon.insert (greedyPrefix_sidon n)] at hbad
    push Not at hbad
    obtain ⟨a, ha, b, hb, hab⟩ := hbad.2
    have ha' := (Finset.mem_Icc.mp (greedyPrefix_subset n ha)).2
    have hb' := (Finset.mem_Icc.mp (greedyPrefix_subset n hb)).2
    obtain ⟨c, hc, heq⟩ := hab (by omega)
    have hc' := (Finset.mem_Icc.mp (greedyPrefix_subset n hc)).2
    have hne : a ≠ b := by omega
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨((a, b), c), Finset.mem_product.mpr
        ⟨Finset.mem_offDiag.mpr ⟨greedyPrefix_mono hnN ha, greedyPrefix_mono hnN hb, hne⟩,
          greedyPrefix_mono hnN hc⟩, by dsimp; omega⟩
  have hblocked : blocked.card ≤ (B.card * B.card - B.card) * B.card := by
    unfold blocked
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.offDiag_card]
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  change N ≤ B.card ^ 3
  calc
    N ≤ B.card + ((B.card * B.card - B.card) * B.card) :=
      hcard.trans ((Finset.card_union_le B blocked).trans (Nat.add_le_add_left hblocked _))
    _ ≤ B.card ^ 3 := by
      by_cases hm : B.card = 0
      · simp [hm]
      have hm' : B.card ≤ B.card * B.card :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm)
      calc
        _ ≤ B.card * B.card + ((B.card * B.card - B.card) * B.card) :=
          Nat.add_le_add_right hm' _
        _ = B.card ^ 3 := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hm']
          ring

/-- Scanning the integers in order gives one finite Sidon set with a cubic bound
at every prefix. -/
lemma exists_cubic_prefix_witness (M : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 M ∧ IsSidon (B : Set ℕ) ∧
      ∀ N ≤ M, N ≤ (Finset.Icc 1 N ∩ B).card ^ 3 := by
  refine ⟨greedyPrefix M, greedyPrefix_subset M, greedyPrefix_sidon M, ?_⟩
  intro N hNM
  have hsub : greedyPrefix N ⊆ Finset.Icc 1 N ∩ greedyPrefix M :=
    fun _ hx ↦ Finset.mem_inter.mpr ⟨greedyPrefix_subset N hx, greedyPrefix_mono hNM hx⟩
  exact (greedyPrefix_card N).trans (Nat.pow_le_pow_left (Finset.card_le_card hsub) 3)

/-- The first three exponents in the finite-prefix criterion have simultaneous witnesses. -/
lemma finiteWitnesses_through_two (M : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 M ∧ IsSidon (B : Set ℕ) ∧
      ∀ k ≤ 2, ∀ N ≤ M, N ^ (k + 2) ≤ (Finset.Icc 1 N ∩ B).card ^ (2 * (k + 4)) := by
  obtain ⟨B, hsub, hs, hc⟩ := exists_cubic_prefix_witness M
  refine ⟨B, hsub, hs, ?_⟩
  intro k hk N hNM
  by_cases hN : N = 0
  · simp [hN, Nat.zero_pow (by omega : 0 < k + 2)]
  let m := (Finset.Icc 1 N ∩ B).card
  have hNm : N ≤ m ^ 3 := hc N hNM
  have hm : 0 < m := by
    by_contra! h
    have hm' : m = 0 := by omega
    simp [hm'] at hNm
    omega
  have hp := Nat.pow_le_pow_left hNm (k + 2)
  rw [← pow_mul] at hp
  exact hp.trans (Nat.pow_le_pow_right hm (by omega))

end OMA.Erdos39

theorem OMA.solution : type_of% @Erdos39.erdos_39 := by
  have h : ∃ T, OMA.Erdos39.HasFiniteWitnesses T := by
    sorry
  obtain ⟨T, hT⟩ := h
  exact OMA.Erdos39.exists_of_finiteWitnesses hT

