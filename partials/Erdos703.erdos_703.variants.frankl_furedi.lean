import FormalConjectures.ErdosProblems.«703»
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Bounds on families that avoid an intersection of prescribed size. -/

-- Problem: Erdős Problem 703 — frankl furedi
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/703.lean:113 (declaration Erdos703.erdos_703.variants.frankl_furedi)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset
open scoped FinsetFamily

namespace OMA703

lemma half_card {α : Type*} [Fintype α] (φ : α → α) (hφ : ∀ a, φ (φ a) = a)
    (P : α → Prop) [DecidablePred P] (h : ∀ a, P (φ a) ↔ ¬ P a) :
    2 * (univ.filter P).card = Fintype.card α := by
  have e : (univ.filter P).card = (univ.filter fun a => ¬ P a).card := by
    refine Finset.card_bij' (fun a _ => φ a) (fun a _ => φ a) ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact (h a).not.mpr (not_not.mpr ha)
    · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha ⊢; rw [h]; exact ha
    · intro a _; exact hφ a
    · intro a _; exact hφ a
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) P
  rw [card_univ] at this
  omega

lemma T0_eq (n : ℕ) (hn : 1 ≤ n) (S : Finset (Finset (Fin n)))
    (hS : ∀ A ∈ S, ∀ B ∈ S, (A ∩ B).card ≠ 0) (hc : 2 * S.card = 2 ^ n) :
    Erdos703.T n 0 = S.card := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold Erdos703.T
  apply le_antisymm
  · refine csSup_le' ?_
    rintro _ ⟨F, hF, rfl⟩
    have h : (F : Set (Finset (Fin n))).Intersecting := by
      intro A hA B hB hd
      rw [Finset.disjoint_iff_inter_eq_empty] at hd
      exact hF A (Finset.mem_coe.1 hA) B (Finset.mem_coe.1 hB) (by rw [hd]; rfl)
    have := h.card_le
    rw [Fintype.card_finset, Fintype.card_fin] at this
    omega
  · refine le_csSup ⟨2 ^ n, ?_⟩ ⟨S, hS, rfl⟩
    rintro _ ⟨F, -, rfl⟩
    exact (Finset.card_le_univ F).trans (by rw [Fintype.card_finset, Fintype.card_fin])

lemma odd_case (n : ℕ) (hn : n % 2 = 1) :
    Erdos703.T n 0 = ((univ : Finset (Finset (Fin n))).filter fun A ↦
        (n + (0:ℕ) : ℝ) / 2 < A.card ∨ A.card < 0).card := by
  have key : ∀ A : Finset (Fin n), ((n + (0:ℕ) : ℝ) / 2 < A.card ∨ A.card < 0) ↔ n < 2 * A.card := by
    intro A
    simp only [Nat.cast_zero, add_zero, Nat.not_lt_zero, or_false]
    constructor
    · intro h; exact_mod_cast (by linarith : (n:ℝ) < 2 * A.card)
    · intro h; have : (n:ℝ) < 2 * A.card := by exact_mod_cast h
      linarith
  simp_rw [key]
  apply T0_eq n (by omega)
  · intro A hA B hB
    simp only [mem_filter, mem_univ, true_and] at hA hB
    have h1 := Finset.card_union_add_card_inter A B
    have h2 : (A ∪ B).card ≤ n := by
      simpa using Finset.card_le_univ (A ∪ B)
    omega
  · rw [half_card (fun A => Aᶜ) (fun A => compl_compl A)]
    · rw [Fintype.card_finset, Fintype.card_fin]
    · intro A
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_univ A
      rw [Fintype.card_fin] at this
      omega

lemma even_case (n : ℕ) (hn1 : 1 ≤ n) (hn : n % 2 = 0) :
    Erdos703.T n 0 = ((univ : Finset (Finset (Fin n))).filter fun A ↦
        (n + (0:ℕ) : ℝ) / 2 ≤ (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card ∨
          A.card < 0).card := by
  have key : ∀ A : Finset (Fin n), ((n + (0:ℕ) : ℝ) / 2 ≤ (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card ∨ A.card < 0) ↔ n ≤ 2 * (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card := by
    intro A
    simp only [Nat.cast_zero, add_zero, Nat.not_lt_zero, or_false]
    constructor
    · intro h; exact_mod_cast (by linarith : (n:ℝ) ≤ 2 * (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card)
    · intro h; have : (n:ℝ) ≤ 2 * (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card := by exact_mod_cast h
      linarith
  simp_rw [key]
  set N : Finset (Fin n) := univ.filter fun i : Fin n ↦ (i : ℕ) ≠ 0 with hN
  have hNc : N.card = n - 1 := by
    have h0 : N = univ.erase ⟨0, hn1⟩ := by
      ext i; simp [hN, Fin.ext_iff]
    rw [h0, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have hAN : ∀ A : Finset (Fin n), (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0) = A ∩ N := by
    intro A; ext i; simp [hN]
  apply T0_eq n hn1
  · intro A hA B hB
    simp only [mem_filter, mem_univ, true_and] at hA hB
    rw [hAN] at hA hB
    have h1 := Finset.card_union_add_card_inter (A ∩ N) (B ∩ N)
    have h2 : (A ∩ N ∪ B ∩ N).card ≤ n - 1 := by
      rw [← hNc]; apply card_le_card; intro x; simp only [mem_union, mem_inter]; tauto
    have h3 : (A ∩ N ∩ (B ∩ N)).card ≤ (A ∩ B).card := by
      apply card_le_card; intro x; simp only [mem_inter]; tauto
    omega
  · let φ : Finset (Fin n) → Finset (Fin n) := fun A => univ.filter fun i => (i ∈ A ↔ (i : ℕ) = 0)
    rw [half_card φ]
    · rw [Fintype.card_finset, Fintype.card_fin]
    · intro A; ext i; simp only [φ, mem_filter, mem_univ, true_and]; tauto
    · intro A
      rw [hAN, hAN]
      have e : φ A ∩ N = N \ (A ∩ N) := by
        ext i; simp only [φ, hN, mem_inter, mem_filter, mem_univ, true_and, mem_sdiff]; tauto
      rw [e, card_sdiff_of_subset inter_subset_right, hNc]
      have : (A ∩ N).card ≤ n - 1 := hNc ▸ card_le_card inter_subset_right
      omega

lemma card_le_T {n r : ℕ} {F : Finset (Finset (Fin n))}
    (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r) : F.card ≤ Erdos703.T n r := by
  unfold Erdos703.T
  refine le_csSup ⟨2 ^ n, ?_⟩ ⟨F, hF, rfl⟩
  rintro _ ⟨G, -, rfl⟩
  exact (card_le_univ G).trans (by rw [Fintype.card_finset, Fintype.card_fin])

lemma odd_lower_bound (n r : ℕ) :
    ((univ : Finset (Finset (Fin n))).filter fun A ↦
        (n + r : ℝ) / 2 < A.card ∨ A.card < r).card ≤ Erdos703.T n r := by
  apply card_le_T
  intro A hA B hB
  simp only [mem_filter, mem_univ, true_and] at hA hB
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · have hU : (A ∪ B).card ≤ n := by simpa using card_le_univ (A ∪ B)
      have hAU : n + r < 2 * A.card := by
        exact_mod_cast (by linarith : (n : ℝ) + r < 2 * A.card)
      have hBU : n + r < 2 * B.card := by
        exact_mod_cast (by linarith : (n : ℝ) + r < 2 * B.card)
      have hcard := card_union_add_card_inter A B
      omega
    · exact ne_of_lt ((card_le_card inter_subset_right).trans_lt hB)
  · exact ne_of_lt ((card_le_card inter_subset_left).trans_lt hA)

lemma even_lower_bound (n r : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (Finset (Fin n))).filter fun A ↦
        (n + r : ℝ) / 2 ≤ (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card ∨
          A.card < r).card ≤ Erdos703.T n r := by
  apply card_le_T
  intro A hA B hB
  simp only [mem_filter, mem_univ, true_and] at hA hB
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · let z : Fin n := ⟨0, hn⟩
      have hfilter (U : Finset (Fin n)) :
          (U.filter fun i : Fin n ↦ (i : ℕ) ≠ 0) = U.erase z := by
        ext i
        simp [z, Fin.ext_iff, and_comm]
      rw [hfilter] at hA hB
      have hU : (A.erase z ∪ B.erase z).card ≤ n - 1 := by
        have hs : A.erase z ∪ B.erase z ⊆ univ.erase z := by
          intro i hi
          simp only [mem_union, mem_erase, mem_univ, and_true] at hi ⊢
          exact hi.elim And.left And.left
        simpa [card_erase_of_mem (mem_univ z)] using card_le_card hs
      have hAU : n + r ≤ 2 * (A.erase z).card := by
        exact_mod_cast (by linarith : (n : ℝ) + r ≤ 2 * (A.erase z).card)
      have hBU : n + r ≤ 2 * (B.erase z).card := by
        exact_mod_cast (by linarith : (n : ℝ) + r ≤ 2 * (B.erase z).card)
      have hcard := card_union_add_card_inter (A.erase z) (B.erase z)
      have hI : (A.erase z ∩ B.erase z).card ≤ (A ∩ B).card :=
        card_le_card (inter_subset_inter (erase_subset _ _) (erase_subset _ _))
      omega
    · exact ne_of_lt ((card_le_card inter_subset_right).trans_lt hB)
  · exact ne_of_lt ((card_le_card inter_subset_left).trans_lt hA)

noncomputable def candidate (n r : ℕ) : ℕ :=
  if (n + r) % 2 = 1 then
    ((univ : Finset (Finset (Fin n))).filter fun A ↦
      (n + r : ℝ) / 2 < A.card ∨ A.card < r).card
  else
    ((univ : Finset (Finset (Fin n))).filter fun A ↦
      (n + r : ℝ) / 2 ≤ (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card ∨ A.card < r).card

lemma candidate_le_T (n r : ℕ) (hn : 1 ≤ n) : candidate n r ≤ Erdos703.T n r := by
  unfold candidate
  split_ifs
  · exact odd_lower_bound n r
  · exact even_lower_bound n r hn

lemma compl_shadow_notMem {n r k : ℕ} {F : Finset (Finset (Fin n))}
    (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r)
    {B : Finset (Fin n)} (hB : B ∈ (∂^[r] (F.slice k))ᶜˢ) :
    B ∉ F := by
  intro hBF
  obtain ⟨A, hA, hBA, hr⟩ :=
    mem_shadow_iterate_iff_exists_sdiff.mp (mem_compls.mp hB)
  apply hF A (slice_subset hA) B hBF
  have heq : A ∩ B = A \ Bᶜ := by
    ext i
    simp
  rwa [heq]

lemma sized_compl_shadow {n r k : ℕ} (F : Finset (Finset (Fin n)))
    (hr : r ≤ k) (hk : k ≤ n) :
    ((∂^[r] (F.slice k))ᶜˢ : Set (Finset (Fin n))).Sized (n + r - k) := by
  have hs := (sized_slice (𝒜 := F) (r := k)).shadow_iterate (k := r)
  have h : n - (k - r) = n + r - k := by omega
  simpa [Fintype.card_fin, h] using hs.compls

lemma card_slice_add_card_shadow_le {n r k : ℕ} {F : Finset (Finset (Fin n))}
    (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r) (hr : r ≤ k) (hk : k ≤ n) :
    (F.slice (n + r - k)).card + (∂^[r] (F.slice k)).card ≤ n.choose (n + r - k) := by
  have hd : Disjoint (F.slice (n + r - k)) (∂^[r] (F.slice k))ᶜˢ :=
    disjoint_left.mpr fun _ hA hAc => compl_shadow_notMem hF hAc (slice_subset hA)
  have hs : (↑(F.slice (n + r - k) ∪ (∂^[r] (F.slice k))ᶜˢ) :
      Set (Finset (Fin n))).Sized (n + r - k) := by
    rw [coe_union, Set.sized_union]
    exact ⟨sized_slice, sized_compl_shadow F hr hk⟩
  simpa [card_union_of_disjoint hd] using hs.card_le

lemma card_middle_slice_le {n r k : ℕ} {F : Finset (Finset (Fin n))}
    (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r) (hr : r ≤ k) (hk : k < n)
    (hm : 2 * k = n + r) :
    (F.slice k).card ≤ (n - 1).choose k := by
  by_contra! hlarge
  have hshadow := kruskal_katona_lovasz_form hr (show k ≤ n - 1 by omega)
    (Nat.sub_le n 1) sized_slice hlarge.le
  have hpair := card_slice_add_card_shadow_le hF hr hk.le
  rw [show n + r - k = k by omega] at hpair
  have hbinom : n.choose k = (n - 1).choose k + (n - 1).choose (k - r) := by
    have hsym : (n - 1).choose (k - r) = (n - 1).choose (k - 1) :=
      Nat.choose_symm_of_eq_add (by omega)
    rw [hsym]
    have hpascal := Nat.choose_succ_succ' (n - 1) (k - 1)
    rw [show n - 1 + 1 = n by omega, show k - 1 + 1 = k by omega] at hpascal
    omega
  omega

def baseFamily (n r : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter fun A ↦ A.card < r ∨ n + r < 2 * A.card

lemma candidate_eq_card_base_add (n r : ℕ) (hn : r < n) :
    candidate n r = (baseFamily n r).card +
      if (n + r) % 2 = 1 then 0 else (n - 1).choose ((n + r) / 2) := by
  have hlt (a : ℕ) : (n + r : ℝ) / 2 < a ↔ n + r < 2 * a := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [mul_comm]
    exact_mod_cast Iff.rfl
  unfold candidate
  split_ifs with hp
  · simp only [add_zero]
    congr 1
    ext A
    simp [baseFamily, hlt, or_comm]
  · let z : Fin n := ⟨0, by omega⟩
    let m := (n + r) / 2
    have hm : n + r = 2 * m := by omega
    have hle (a : ℕ) : (n + r : ℝ) / 2 ≤ a ↔ m ≤ a := by
      have hreal : (n : ℝ) + r = 2 * m := by exact_mod_cast hm
      rw [hreal, mul_comm, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      exact_mod_cast Iff.rfl
    let M := (univ.erase z).powersetCard m
    have heq : (univ.filter fun A : Finset (Fin n) ↦
        (n + r : ℝ) / 2 ≤ (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0).card ∨
          A.card < r) = baseFamily n r ∪ M := by
      ext A
      have he : (A.filter fun i : Fin n ↦ (i : ℕ) ≠ 0) = A.erase z := by
        ext i
        simp [z, Fin.ext_iff, and_comm]
      have hsub : A ⊆ univ.erase z ↔ z ∉ A := by
        constructor
        · intro h hz
          simpa using h hz
        · intro hz i hi
          exact mem_erase.mpr ⟨fun e ↦ hz (e ▸ hi), mem_univ _⟩
      simp only [mem_filter, mem_univ, true_and, hle, he, mem_union, baseFamily,
        M, mem_powersetCard, hsub]
      have hmc : r < m := by omega
      by_cases hz : z ∈ A
      · simp [hz, card_erase_of_mem hz]
        omega
      · simp [hz]
        omega
    have hd : Disjoint (baseFamily n r) M := by
      refine disjoint_left.mpr fun A hA hM ↦ ?_
      have hAm := (mem_powersetCard.mp hM).2
      simp only [baseFamily, mem_filter, mem_univ, true_and] at hA
      omega
    rw [heq, card_union_of_disjoint hd]
    simp [M, m, card_powersetCard, card_erase_of_mem (mem_univ z)]

lemma card_le_candidate_of_missing {n r : ℕ} {F missing : Finset (Finset (Fin n))}
    (hn : r < n) (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r)
    (hmissing : missing ⊆ baseFamily n r) (hd : Disjoint F missing)
    (hcount : (F.filter fun A ↦ r ≤ A.card ∧ 2 * A.card < n + r).card ≤ missing.card) :
    F.card ≤ candidate n r := by
  let m := (n + r) / 2
  let low := F.filter fun A ↦ r ≤ A.card ∧ 2 * A.card < n + r
  let base := F ∩ baseFamily n r
  let middle := if (n + r) % 2 = 1 then ∅ else F.slice m
  have hcover : F ⊆ base ∪ low ∪ middle := by
    intro A hA
    by_cases ha : A.card < r ∨ n + r < 2 * A.card
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr
        ⟨hA, mem_filter.mpr ⟨mem_univ _, ha⟩⟩))
    · by_cases hb : 2 * A.card < n + r
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hA, by omega⟩))
      · have he : (n + r) % 2 ≠ 1 := by omega
        apply mem_union_right
        simp only [middle, if_neg he, mem_slice]
        exact ⟨hA, by omega⟩
  have hpart := (card_le_card hcover).trans (card_union_le _ _)
  have hbase := card_union_le base low
  have hbaseMissing : base.card + missing.card ≤ (baseFamily n r).card := by
    have h := card_le_card (union_subset inter_subset_right hmissing : base ∪ missing ⊆ _)
    rwa [card_union_of_disjoint (hd.mono_left inter_subset_left)] at h
  have hmid : middle.card ≤ if (n + r) % 2 = 1 then 0 else (n - 1).choose ((n + r) / 2) := by
    dsimp only [middle]
    split_ifs with h
    · simp
    · exact card_middle_slice_le hF (by omega) (by omega) (by omega)
  rw [candidate_eq_card_base_add n r hn]
  change low.card ≤ missing.card at hcount
  omega

lemma card_le_candidate_of_shadow {n r : ℕ} {F : Finset (Finset (Fin n))}
    (hn : r < n) (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r)
    (hshadow : ∀ k, r ≤ k → 2 * k < n + r →
      (F.slice k).card ≤ (∂^[r] (F.slice k)).card) :
    F.card ≤ candidate n r := by
  let I := (range (n + 1)).filter fun k ↦ r ≤ k ∧ 2 * k < n + r
  let S (k : ℕ) := (∂^[r] (F.slice k))ᶜˢ
  have hI {k : ℕ} : k ∈ I ↔ k ≤ n ∧ r ≤ k ∧ 2 * k < n + r := by
    simp [I]
  have hs {k : ℕ} (hk : k ∈ I) {A : Finset (Fin n)} (hA : A ∈ S k) :
      A.card = n + r - k :=
    sized_compl_shadow F (hI.mp hk).2.1 (hI.mp hk).1 hA
  have hdisj : (I : Set ℕ).PairwiseDisjoint S := by
    intro k hk l hl hne
    refine disjoint_left.mpr fun A hAk hAl ↦ ?_
    have hk' := hs hk hAk
    have hl' := hs hl hAl
    have hk'' := (hI.mp hk).1
    have hl'' := (hI.mp hl).1
    omega
  apply card_le_candidate_of_missing hn hF (missing := I.biUnion S)
  · intro A hA
    obtain ⟨k, hk, hAk⟩ := mem_biUnion.mp hA
    have hc := hs hk hAk
    have hk' := hI.mp hk
    exact mem_filter.mpr ⟨mem_univ _, Or.inr (by omega)⟩
  · refine disjoint_left.mpr fun A hA hAm ↦ ?_
    obtain ⟨k, _, hAk⟩ := mem_biUnion.mp hAm
    exact compl_shadow_notMem hF hAk hA
  · rw [card_biUnion hdisj]
    have hsum : ∑ k ∈ I, (F.slice k).card =
        (F.filter fun A ↦ r ≤ A.card ∧ 2 * A.card < n + r).card := by
      simp only [slice]
      rw [sum_card_fiberwise_eq_card_filter]
      congr 1
      ext A
      have hA : A.card ≤ n := by simpa using card_le_univ A
      simp [hI, hA]
    rw [← hsum]
    exact sum_le_sum fun k hk ↦ by
      simpa only [S, card_compls] using hshadow k (hI.mp hk).2.1 (hI.mp hk).2.2

private def shadowWeight (k : ℕ) : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | t + 2 => -((t + 2 : ℕ) : ℚ) * shadowWeight k (t + 1) / ((k : ℚ) - (t + 2 : ℕ))

private lemma shadowWeight_ne_zero {k t : ℕ} (ht : 0 < t) (hk : t < k) :
    shadowWeight k t ≠ 0 := by
  induction t with
  | zero => omega
  | succ t ih =>
    cases t with
    | zero => simp [shadowWeight]
    | succ t =>
      have hden : (k : ℚ) - (t + 2 : ℕ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hk))
      have hnum : (((t + 2 : ℕ) : ℚ)) ≠ 0 := by positivity
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hnum) (ih (by omega) (by omega))) hden

private lemma shadowWeight_cancel {k t : ℕ} (ht : t ≠ 1) (hk : t < k) :
    (t : ℚ) * shadowWeight k (t - 1) + (k - t : ℕ) * shadowWeight k t = 0 := by
  rcases t with _ | _ | t
  · simp [shadowWeight]
  · exact (ht rfl).elim
  · have hden : (k : ℚ) - (t + 2 : ℕ) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hk))
    rw [Nat.cast_sub hk.le]
    change ((t + 2 : ℕ) : ℚ) * shadowWeight k (t + 1) +
      ((k : ℚ) - (t + 2 : ℕ)) *
        (-((t + 2 : ℕ) : ℚ) * shadowWeight k (t + 1) / ((k : ℚ) - (t + 2 : ℕ))) = 0
    field_simp
    ring

private lemma sum_shadowWeight_erase {n k : ℕ} (A B : Finset (Fin n)) (hB : B.card = k) :
    let t := (A ∩ B).card
    (∑ b ∈ B, shadowWeight k (A ∩ B.erase b).card) =
      (t : ℚ) * shadowWeight k (t - 1) + (k - t : ℕ) * shadowWeight k t := by
  dsimp only
  set t := (A ∩ B).card
  have hcard : (B.filter fun b ↦ b ∈ A).card = t := by
    congr 1
    ext b
    simp [and_comm]
  have hcardNot : (B.filter fun b ↦ b ∉ A).card = k - t := by
    have h := card_filter_add_card_filter_not (s := B) (fun b ↦ b ∈ A)
    rw [hcard, hB] at h
    omega
  rw [← sum_filter_add_sum_filter_not B (fun b ↦ b ∈ A)]
  congr 1
  · calc
      _ = ∑ _ ∈ B.filter (fun b ↦ b ∈ A), shadowWeight k (t - 1) := by
        refine sum_congr rfl fun b hb ↦ ?_
        obtain ⟨hbB, hbA⟩ := mem_filter.mp hb
        rw [inter_erase, card_erase_of_mem (mem_inter.mpr ⟨hbA, hbB⟩)]
      _ = _ := by rw [sum_const, hcard, nsmul_eq_mul]
  · calc
      _ = ∑ _ ∈ B.filter (fun b ↦ b ∉ A), shadowWeight k t := by
        refine sum_congr rfl fun b hb ↦ ?_
        have hbA := (mem_filter.mp hb).2
        rw [inter_erase, erase_eq_of_notMem (fun h ↦ hbA (mem_inter.mp h).1)]
      _ = _ := by rw [sum_const, hcardNot, nsmul_eq_mul]

lemma card_le_shadow_of_avoids_one {n k : ℕ} {F : Finset (Finset (Fin n))}
    (hsize : (F : Set (Finset (Fin n))).Sized k) (hk : 1 < k)
    (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ 1) :
    F.card ≤ (∂ F).card := by
  classical
  let v (B : F) (D : ∂ F) : ℚ := if D.val ⊆ B.val then 1 else 0
  let test (A : F) : ((∂ F) → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun f ↦ ∑ D : ∂ F, shadowWeight k (A.val ∩ D.val).card * f D
      map_add' := by intro f g; simp [mul_add, sum_add_distrib]
      map_smul' := by intro c f; simp [mul_sum, mul_left_comm] }
  have htest (A B : F) :
      test A (v B) = ∑ b ∈ B.val, shadowWeight k (A.val ∩ B.val.erase b).card := by
    change (∑ D : ∂ F, shadowWeight k (A.val ∩ D.val).card *
      (if D.val ⊆ B.val then 1 else 0)) = _
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    symm
    refine sum_bij (fun b hb ↦ (⟨B.val.erase b, erase_mem_shadow B.property hb⟩ : ∂ F))
      ?_ ?_ ?_ ?_
    · intro b hb
      exact mem_filter.mpr ⟨mem_univ _, erase_subset _ _⟩
    · intro b hb d _ h
      exact (erase_inj B.val hb).mp (congrArg Subtype.val h)
    · intro D hD
      have hDB := (mem_filter.mp hD).2
      have hDc := hsize.shadow D.property
      have hd : (B.val \ D.val).card = 1 := by
        rw [card_sdiff_of_subset hDB, hsize B.property, hDc]
        omega
      obtain ⟨b, hb⟩ := card_eq_one.mp hd
      have hbB : b ∈ B.val := by
        have hmem : b ∈ B.val \ D.val := by simp [hb]
        exact (mem_sdiff.mp hmem).1
      refine ⟨b, hbB, Subtype.ext ?_⟩
      simpa [hb, sdiff_singleton_eq_erase] using
        (Finset.sdiff_sdiff_eq_self hDB : B.val \ (B.val \ D.val) = D.val)
    · intro b hb
      rfl
  have hoff (A B : F) (hAB : A ≠ B) : test A (v B) = 0 := by
    rw [htest, sum_shadowWeight_erase _ _ (hsize B.property)]
    have hlt : (A.val ∩ B.val).card < k := by
      by_contra! hle
      have hl : A.val ∩ B.val = A.val :=
        eq_of_subset_of_card_le inter_subset_left (by rwa [hsize A.property])
      have hr : A.val ∩ B.val = B.val :=
        eq_of_subset_of_card_le inter_subset_right (by rwa [hsize B.property])
      exact hAB (Subtype.ext (hl.symm.trans hr))
    exact shadowWeight_cancel (hF A.val A.property B.val B.property) hlt
  have hdiag (A : F) : test A (v A) ≠ 0 := by
    rw [htest, sum_shadowWeight_erase _ _ (hsize A.property), inter_self, hsize A.property]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    exact mul_ne_zero (by positivity) (shadowWeight_ne_zero (by omega) (by omega))
  have hi : LinearIndependent ℚ v := by
    rw [linearIndependent_iff']
    intro S c hc A hA
    have he := congrArg (test A) hc
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at he
    rw [sum_eq_single_of_mem A hA] at he
    · exact (mul_eq_zero.mp he).resolve_right (hdiag A)
    · intro B hB hBA
      rw [hoff A B (Ne.symm hBA), mul_zero]
  simpa [Module.finrank_fintype_fun_eq_card] using hi.fintype_card_le_finrank

lemma T_le_candidate_one (n : ℕ) (hn : 1 < n) : Erdos703.T n 1 ≤ candidate n 1 := by
  unfold Erdos703.T
  refine csSup_le' ?_
  rintro _ ⟨F, hF, rfl⟩
  apply card_le_candidate_of_shadow hn hF
  intro k hk _
  rcases eq_or_lt_of_le hk with rfl | hk'
  · have he : F.slice 1 = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun A hA ↦ ?_
      exact hF A (slice_subset hA) A (slice_subset hA)
        (by simpa using sized_slice hA)
    simp [he]
  · simpa using card_le_shadow_of_avoids_one sized_slice hk' (fun A hA B hB ↦
      hF A (slice_subset hA) B (slice_subset hB))

lemma det_scalar_add_int_matrix_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : Matrix ι ι ℤ) {L s : ℕ} (hL : 0 < L) (hs : L < s) :
    (Matrix.scalar ι (L : ℚ) + (s : ℚ) • Z.map (algebraMap ℤ ℚ)).det ≠ 0 := by
  let x : ℚ := -(L : ℚ) / s
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have hx : -(s : ℚ) * x = L := by dsimp [x]; field_simp
  have hm : Matrix.scalar ι (L : ℚ) + (s : ℚ) • Z.map (algebraMap ℤ ℚ) =
      (-(s : ℚ)) • (Matrix.scalar ι x - Z.map (algebraMap ℤ ℚ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply, ← hx]
      ring
    · simp [Matrix.scalar_apply, Matrix.natCast_apply, hij]
  intro hd
  rw [hm, Matrix.det_smul] at hd
  have hd' := (mul_eq_zero.mp hd).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr hsQ))
  have hroot : Polynomial.aeval x Z.charpoly = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
    exact hd'
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic Z.charpoly_monic hroot
  have hneg : x < 0 := by
    have hL' : (0 : ℚ) < L := by exact_mod_cast hL
    have hs' : (0 : ℚ) < s := by exact_mod_cast (show 0 < s by omega)
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hL') hs'
  have hgt : -1 < x := by
    dsimp [x]
    apply (lt_div_iff₀ (show (s : ℚ) > 0 by exact_mod_cast (show 0 < s by omega))).2
    have ht : (L : ℚ) < s := by exact_mod_cast hs
    linarith
  change x = (z : ℚ) at hz
  have hz1 : -1 < z := by exact_mod_cast (hz ▸ hgt)
  have hz2 : z < 0 := by exact_mod_cast (hz ▸ hneg)
  omega

private def blockFlip {α : Type*} [Fintype α] [DecidableEq α]
    (C A : Finset α) : Finset α :=
  univ.filter fun x ↦ (x ∈ A ↔ x ∈ C)

private lemma blockFlip_involutive {α : Type*} [Fintype α] [DecidableEq α] (C : Finset α) :
    Function.Involutive (blockFlip C) := by
  intro A
  ext x
  simp only [blockFlip, mem_filter, mem_univ, true_and]
  tauto

private lemma inter_blockFlip {α : Type*} [Fintype α] [DecidableEq α] (A C : Finset α) :
    A ∩ blockFlip C A = A ∩ C := by
  ext x
  simp only [blockFlip, mem_filter, mem_univ, true_and, mem_inter]
  tauto

private lemma blockFlip_inter_of_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) {C D : Finset α} (hd : Disjoint C D) :
    blockFlip C A ∩ D = D \ (A ∩ D) := by
  ext x
  have h : x ∈ C → x ∈ D → False := fun hC hD ↦ disjoint_left.mp hd hC hD
  simp only [blockFlip, mem_filter, mem_univ, true_and, mem_inter, mem_sdiff]
  tauto

lemma exists_involutive_inter_card {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] (s : ℕ) (blocks : ι → Finset α)
    (hdisj : Pairwise fun i j ↦ Disjoint (blocks i) (blocks j))
    (hsize : ∀ i, (blocks i).card = 2 * s) :
    ∃ f : Finset α → Finset α, Function.Involutive f ∧
      ∀ A, (∃ i, (A ∩ blocks i).card = s) → (A ∩ f A).card = s := by
  classical
  let good (A : Finset α) : Finset ι := univ.filter fun i ↦ (A ∩ blocks i).card = s
  let pick (S : Finset ι) : Finset α := if h : S.Nonempty then blocks h.choose else ∅
  let f (A : Finset α) := blockFlip (pick (good A)) A
  have hgood (A : Finset α) : good (f A) = good A := by
    ext j
    simp only [good, mem_filter, mem_univ, true_and]
    have hC : pick (good A) = blocks j ∨ Disjoint (pick (good A)) (blocks j) := by
      by_cases hg : (good A).Nonempty
      · rw [show pick (good A) = blocks hg.choose from dif_pos hg]
        rcases eq_or_ne hg.choose j with h | h
        · exact Or.inl (congrArg blocks h)
        · exact Or.inr (hdisj h)
      · exact Or.inr (by simp [pick, hg])
    change (blockFlip (pick (good A)) A ∩ blocks j).card = s ↔ _
    rcases hC with h | h
    · rw [h]
      have he : blockFlip (blocks j) A ∩ blocks j = A ∩ blocks j := by
        ext x
        simp only [blockFlip, mem_filter, mem_univ, true_and, mem_inter]
        tauto
      rw [he]
    · rw [blockFlip_inter_of_disjoint A h, card_sdiff_of_subset inter_subset_right, hsize]
      have hc := card_le_card (inter_subset_right : A ∩ blocks j ⊆ blocks j)
      rw [hsize] at hc
      omega
  refine ⟨f, fun A ↦ ?_, fun A ⟨i, hi⟩ ↦ ?_⟩
  · change blockFlip (pick (good (f A))) (f A) = A
    rw [hgood]
    exact blockFlip_involutive (pick (good A)) A
  · have h : (good A).Nonempty := ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    change (A ∩ blockFlip (pick (good A)) A).card = s
    rw [inter_blockFlip, show pick (good A) = blocks h.choose from dif_pos h]
    exact (mem_filter.mp h.choose_spec).2

lemma card_add_card_le_of_involution {α : Type*} [Fintype α] [DecidableEq α]
    {left right good : Finset α} {f : α → α} (hf : Function.Involutive f)
    (h : ∀ A ∈ left, A ∈ good → f A ∉ right) :
    left.card + right.card ≤ Fintype.card α + goodᶜ.card := by
  let e : α ↪ α := ⟨f, hf.injective⟩
  have hu := card_le_univ (left ∪ right.map e)
  have hi : left ∩ right.map e ⊆ goodᶜ := by
    intro A hA
    obtain ⟨hAl, hAr⟩ := mem_inter.mp hA
    obtain ⟨B, hB, hAB⟩ := mem_map.mp hAr
    change f B = A at hAB
    have he : f A = B := by rw [← hAB, hf B]
    exact mem_compl.mpr fun hg ↦ h A hAl hg (he ▸ hB)
  have h' := (card_union_add_card_inter left (right.map e)).symm
  rw [card_map] at h'
  exact h'.le.trans (add_le_add hu (card_le_card hi))

lemma card_add_card_le_of_cross_avoids {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] (s : ℕ) (blocks : ι → Finset α)
    (hdisj : Pairwise fun i j ↦ Disjoint (blocks i) (blocks j))
    (hsize : ∀ i, (blocks i).card = 2 * s) {left right : Finset (Finset α)}
    (h : ∀ A ∈ left, ∀ B ∈ right, (A ∩ B).card ≠ s) :
    left.card + right.card ≤ 2 ^ Fintype.card α +
      ((univ : Finset (Finset α)).filter fun A ↦ ∀ i, (A ∩ blocks i).card ≠ s).card := by
  obtain ⟨f, hf, hpair⟩ := exists_involutive_inter_card s blocks hdisj hsize
  have hcount := card_add_card_le_of_involution
    (good := (univ : Finset (Finset α)).filter fun A ↦ ∃ i, (A ∩ blocks i).card = s) hf
    (left := left) (right := right) fun A hA hg hB ↦ h A hA (f A) hB (hpair _ (mem_filter.mp hg).2)
  have he : ((univ : Finset (Finset α)).filter fun A ↦ ∃ i, (A ∩ blocks i).card = s)ᶜ =
      (univ : Finset (Finset α)).filter fun A ↦ ∀ i, (A ∩ blocks i).card ≠ s := by
    ext A
    simp
  rwa [he, Fintype.card_finset] at hcount

lemma eval_eq_sum_choose {s : ℕ} (P : Polynomial ℚ) (hp : P.natDegree ≤ s) :
    ∃ c : ℕ → ℚ, ∀ t : ℕ, P.eval (t : ℚ) =
      ∑ j ∈ range (s + 1), c j * (t.choose j : ℚ) := by
  induction s generalizing P with
  | zero =>
    refine ⟨fun _ ↦ P.coeff 0, fun t ↦ ?_⟩
    have he := congrArg (Polynomial.eval (t : ℚ)) (Polynomial.eq_C_of_natDegree_le_zero hp)
    simpa using he
  | succ s ih =>
    let D := descPochhammer ℚ (s + 1)
    let Q := P - Polynomial.C (P.coeff (s + 1)) * D
    have hD : D.natDegree = s + 1 := descPochhammer_natDegree _ _
    have hmono : D.Monic := monic_descPochhammer _ _
    have hQ : Q.natDegree ≤ s := by
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ ?_
      simp only [Q, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le (show s + 1 ≤ j by omega) with h | h
      · subst j
        have hd : D.coeff (s + 1) = 1 := by rw [← hD]; exact hmono
        rw [hd, mul_one, sub_self]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_lt h),
          Polynomial.coeff_eq_zero_of_natDegree_lt (hD.trans_lt h), mul_zero, sub_zero]
    obtain ⟨c, hc⟩ := ih Q hQ
    refine ⟨Function.update c (s + 1) (P.coeff (s + 1) * (s + 1).factorial), fun t ↦ ?_⟩
    rw [sum_range_succ, Function.update_self]
    have hs :
        ∑ j ∈ range (s + 1),
          Function.update c (s + 1) (P.coeff (s + 1) * (s + 1).factorial) j *
            (t.choose j : ℚ) = ∑ j ∈ range (s + 1), c j * (t.choose j : ℚ) := by
      refine sum_congr rfl fun j hj ↦ ?_
      rw [Function.update_of_ne (mem_range.mp hj).ne]
    rw [hs, ← hc]
    have he : (t.choose (s + 1) : ℚ) = D.eval (t : ℚ) / (s + 1).factorial :=
      Nat.cast_choose_eq_descPochhammer_div ℚ _ _
    rw [he]
    dsimp [Q]
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    have hn : ((s + 1).factorial : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring

lemma sum_choose_inter_powersetCard {α : Type*} [DecidableEq α]
    (A B : Finset α) {s j : ℕ} (hj : j ≤ s) :
    ∑ D ∈ B.powersetCard s, (A ∩ D).card.choose j =
      (A ∩ B).card.choose j * (B.card - j).choose (s - j) := by
  let E := (A ∩ B).powersetCard j
  calc
    _ = ∑ D ∈ B.powersetCard s, ∑ X ∈ E, if X ⊆ D then 1 else 0 := by
      refine sum_congr rfl fun D hD ↦ ?_
      rw [← sum_filter, ← card_eq_sum_ones, ← card_powersetCard]
      congr 1
      ext X
      have hDB := (mem_powersetCard.mp hD).1
      simp only [E, mem_powersetCard, mem_filter, subset_inter_iff]
      constructor
      · rintro ⟨⟨hXA, hXD⟩, hXj⟩
        exact ⟨⟨⟨hXA, hXD.trans hDB⟩, hXj⟩, hXD⟩
      · rintro ⟨⟨⟨hXA, _⟩, hXj⟩, hXD⟩
        exact ⟨⟨hXA, hXD⟩, hXj⟩
    _ = ∑ X ∈ E, ∑ D ∈ B.powersetCard s, if X ⊆ D then 1 else 0 := sum_comm
    _ = ∑ _X ∈ E, (B.card - j).choose (s - j) := by
      refine sum_congr rfl fun X hX ↦ ?_
      obtain ⟨hX, hc⟩ := mem_powersetCard.mp hX
      rw [← sum_filter, ← card_eq_sum_ones,
        card_filter_powersetCard_subset X B s (hX.trans inter_subset_right) (hc ▸ hj), hc]
    _ = _ := by simp [E, sum_const, card_powersetCard]

lemma card_le_shadow_of_eval_det_ne_zero {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} {k r : ℕ} (hF : (F : Set (Finset α)).Sized k) (hr : r ≤ k)
    (P : Polynomial ℚ) (hP : P.natDegree ≤ k - r)
    (hdet : (Matrix.of fun A B : F ↦ P.eval ((A.val ∩ B.val).card : ℚ)).det ≠ 0) :
    F.card ≤ (∂^[r] F).card := by
  classical
  let s := k - r
  let G := ∂^[r] F
  obtain ⟨c, hc⟩ := eval_eq_sum_choose P hP
  let w (A D : Finset α) :=
    ∑ j ∈ range (s + 1), c j / ((k - j).choose (s - j) : ℚ) *
      ((A ∩ D).card.choose j : ℚ)
  let W : Matrix F G ℚ := Matrix.of fun A D ↦ w A.val D.val
  let V : Matrix G F ℚ := Matrix.of fun D B ↦ if D.val ⊆ B.val then 1 else 0
  have hprod : W * V = Matrix.of (fun A B : F ↦ P.eval ((A.val ∩ B.val).card : ℚ)) := by
    ext A B
    rw [Matrix.mul_apply]
    change (∑ D : G, w A.val D.val * (if D.val ⊆ B.val then 1 else 0)) = _
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    have heq : (∑ D ∈ B.val.powersetCard s, w A.val D) =
        ∑ D ∈ (univ : Finset G).filter (fun D ↦ D.val ⊆ B.val), w A.val D.val := by
      have hG {D : Finset α} (hD : D ∈ B.val.powersetCard s) : D ∈ G := by
        have ⟨hs, hD⟩ := mem_powersetCard.mp hD
        apply mem_shadow_iterate_iff_exists_mem_card_add.mpr
        exact ⟨B.val, B.property, hs, by rw [hF B.property, hD]; omega⟩
      refine sum_bij (fun D hD ↦ (⟨D, hG hD⟩ : G)) ?_ ?_ ?_ ?_
      · exact fun _ hD ↦ mem_filter.mpr ⟨mem_univ _, (mem_powersetCard.mp hD).1⟩
      · exact fun _ _ _ _ h ↦ congrArg Subtype.val h
      · intro D hD
        have hs := (hF.shadow_iterate (k := r)) D.property
        exact ⟨D.val, mem_powersetCard.mpr ⟨(mem_filter.mp hD).2, hs⟩, Subtype.ext rfl⟩
      · intros
        rfl
    rw [← heq]
    change (∑ D ∈ B.val.powersetCard s, w A.val D) = P.eval ((A.val ∩ B.val).card : ℚ)
    rw [hc]
    simp only [w]
    rw [sum_comm]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j ≤ s := by simpa using mem_range.mp hj
    have hsum : ∑ D ∈ B.val.powersetCard s, ((A.val ∩ D).card.choose j : ℚ) =
        ((A.val ∩ B.val).card.choose j : ℚ) * ((k - j).choose (s - j) : ℚ) := by
      exact_mod_cast (by simpa [hF B.property] using
        sum_choose_inter_powersetCard A.val B.val hj')
    have hden : ((k - j).choose (s - j) : ℚ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))
    rw [← mul_sum, hsum]
    field_simp
  have h := Matrix.rank_of_det_ne_zero (show (W * V).det ≠ 0 by rwa [hprod])
  have hc' := (Matrix.rank_mul_le_left W V).trans W.rank_le_card_width
  rw [h] at hc'
  simpa [G] using hc'

lemma exists_forbidden_intersection_polynomial (r d : ℕ) (hr : 2 ≤ r) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ d + 1 ∧
      P.eval ((r + d + 1 : ℕ) : ℚ) = (r.factorial : ℚ) ∧
      ∀ t : ℕ, t < r + d + 1 → t ≠ r →
        ∃ z : ℤ, P.eval (t : ℚ) = ((d + 1 : ℕ) : ℚ) * (z : ℚ) := by
  let D := descPochhammer ℚ d
  let x : Polynomial ℚ := Polynomial.X
  let a : ℚ := (r.factorial : ℚ) / (((d + 2 : ℕ) : ℚ) * (d.factorial : ℚ))
  let P := Polynomial.C a * (x - Polynomial.C ((r - 1 : ℕ) : ℚ)) *
    D.comp (x - Polynomial.C ((r + 1 : ℕ) : ℚ))
  have hD : D.natDegree = d := descPochhammer_natDegree ℚ d
  have hdeg : P.natDegree ≤ d + 1 := by
    apply Polynomial.natDegree_mul_le.trans
    have h1 : (Polynomial.C a * (x - Polynomial.C ((r - 1 : ℕ) : ℚ))).natDegree ≤ 1 := by
      exact Polynomial.natDegree_mul_le.trans (by
        simp only [x, Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C, zero_add, le_refl])
    have h2 : (D.comp (x - Polynomial.C ((r + 1 : ℕ) : ℚ))).natDegree ≤ d := by
      exact Polynomial.natDegree_comp_le.trans (by
        simp only [hD, x, Polynomial.natDegree_X_sub_C, mul_one, le_refl])
    omega
  have heval (t : ℕ) : P.eval (t : ℚ) = a * ((t : ℚ) - (r - 1 : ℕ)) *
      D.eval ((t : ℚ) - (r + 1 : ℕ)) := by simp [P, x, Polynomial.eval_comp]
  have heD (t : ℕ) : D.eval (t : ℚ) = (t.choose d : ℚ) * (d.factorial : ℚ) := by
    exact (eq_div_iff (show (d.factorial : ℚ) ≠ 0 by positivity)).mp
      (Nat.cast_choose_eq_descPochhammer_div ℚ t d) |>.symm
  have hrSub : ((r - 1 : ℕ) : ℚ) = (r : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  refine ⟨P, hdeg, ?_, fun t ht htr ↦ ?_⟩
  · rw [heval, hrSub, show (((r + d + 1 : ℕ) : ℚ) - (r + 1 : ℕ)) = d by push_cast; ring]
    rw [heD, Nat.choose_self]
    dsimp [a]
    have hleft : (((r + d + 1 : ℕ) : ℚ) - ((r : ℚ) - 1)) = (d + 2 : ℕ) := by
      push_cast
      ring
    rw [hleft]
    field_simp
  · by_cases ht1 : r + 1 ≤ t
    · refine ⟨0, ?_⟩
      have hdiff : ((t : ℚ) - (r + 1 : ℕ)) = ((t - (r + 1) : ℕ) : ℚ) := by
        rw [Nat.cast_sub ht1]
      rw [heval, hdiff, heD, Nat.choose_eq_zero_of_lt (show t - (r + 1) < d by omega)]
      simp
    · by_cases ht2 : t = r - 1
      · refine ⟨0, ?_⟩
        simp [heval, ht2]
      · let b := r + d - t
        have hdiff : ((t : ℚ) - (r + 1 : ℕ)) - (d : ℚ) + 1 = -(b : ℚ) := by
          simp only [b, Nat.cast_sub (show t ≤ r + d by omega), Nat.cast_add, Nat.cast_one]
          ring
        have heDneg : D.eval ((t : ℚ) - (r + 1 : ℕ)) =
            (-1 : ℚ)^d * ((b.choose d : ℚ) * (d.factorial : ℚ)) := by
          change (descPochhammer ℚ d).eval _ = _
          rw [descPochhammer_eval_eq_ascPochhammer, hdiff, ascPochhammer_eval_neg_eq_descPochhammer]
          rw [show (descPochhammer ℚ d).eval (b : ℚ) = _ from heD b]
        have hbin1 : (b.choose (d + 1) : ℚ) * (d + 1 : ℕ) =
            (b.choose d : ℚ) * (r - t : ℕ) := by
          exact_mod_cast (by simpa [show b - d = r - t by omega] using
            Nat.choose_succ_right_eq b d)
        have hbin2 : (b.choose (d + 2) : ℚ) * (d + 2 : ℕ) =
            (b.choose (d + 1) : ℚ) * (r - 1 - t : ℕ) := by
          exact_mod_cast (by simpa [show b - (d + 1) = r - 1 - t by omega] using
            Nat.choose_succ_right_eq b (d + 1))
        obtain ⟨u, hu⟩ := Nat.dvd_factorial (show 0 < r - t by omega) (Nat.sub_le r t)
        refine ⟨(-1 : ℤ)^(d + 1) * (u : ℤ) * (b.choose (d + 2) : ℤ), ?_⟩
        rw [heval, heDneg, show (t : ℚ) - (r - 1 : ℕ) = -((r - 1 - t : ℕ) : ℚ) by
          rw [Nat.cast_sub (show t ≤ r - 1 by omega)]; ring]
        have hbin : (b.choose d : ℚ) * (r - t : ℕ) * (r - 1 - t : ℕ) =
            (b.choose (d + 2) : ℚ) * (d + 2 : ℕ) * (d + 1 : ℕ) := by
          rw [← hbin1]
          linear_combination ((d + 1 : ℕ) : ℚ) * -hbin2
        dsimp [a]
        rw [hu, Nat.cast_mul]
        calc
          _ = -(((-1 : ℚ)^d * (u : ℚ) * (d.factorial : ℚ)) *
              ((b.choose d : ℚ) * (r - t : ℕ) * (r - 1 - t : ℕ))) /
              (((d + 2 : ℕ) : ℚ) * (d.factorial : ℚ)) := by ring
          _ = _ := by
            rw [hbin]
            push_cast
            rw [pow_succ]
            field_simp

lemma card_le_shadow_of_large_rank {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} {k r : ℕ} (hF : (F : Set (Finset α)).Sized k) (hr : 2 ≤ r)
    (hk : r + r.factorial < k)
    (havoid : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r) :
    F.card ≤ (∂^[r] F).card := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = r + d + 1 := ⟨k - r - 1, by omega⟩
  obtain ⟨P, hdeg, hdiag, hoff⟩ := exists_forbidden_intersection_polynomial r d hr
  have ht (A B : F) (hne : A ≠ B) : (A.val ∩ B.val).card < r + d + 1 := by
    by_contra! hle
    have hA := eq_of_subset_of_card_le (inter_subset_left : A.val ∩ B.val ⊆ A.val)
      (by rwa [hF A.property])
    have hB := eq_of_subset_of_card_le (inter_subset_right : A.val ∩ B.val ⊆ B.val)
      (by rwa [hF B.property])
    exact hne (Subtype.ext (hA.symm.trans hB))
  let z (A B : F) (h : A ≠ B) :=
    hoff _ (ht A B h) (havoid A.val A.property B.val B.property)
  let Z : Matrix F F ℤ := Matrix.of fun A B ↦ if h : A = B then 0 else (z A B h).choose
  apply card_le_shadow_of_eval_det_ne_zero hF (by omega) P (hdeg.trans (by omega))
  have heq : Matrix.of (fun A B : F ↦ P.eval ((A.val ∩ B.val).card : ℚ)) =
      Matrix.scalar F (r.factorial : ℚ) + ((d + 1 : ℕ) : ℚ) • Z.map (algebraMap ℤ ℚ) := by
    ext A B
    by_cases h : A = B
    · subst B
      simpa [inter_self, hF A.property, Matrix.natCast_apply, Z] using hdiag
    · have hp := (z A B h).choose_spec
      simpa [Matrix.scalar_apply, Matrix.natCast_apply, Z, h] using hp
  rw [heq]
  exact det_scalar_add_int_matrix_ne_zero Z (Nat.factorial_pos _) (by omega)

lemma card_le_candidate_of_no_small_member {n r : ℕ} {F : Finset (Finset (Fin n))}
    (hr : 2 ≤ r) (hn : r < n) (hF : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r)
    (hsmall : ¬ ∃ A ∈ F, r ≤ A.card ∧ A.card ≤ r + r.factorial) :
    F.card ≤ candidate n r := by
  apply card_le_candidate_of_shadow hn hF
  intro k hk _
  by_cases hlarge : r + r.factorial < k
  · exact card_le_shadow_of_large_rank sized_slice hr hlarge fun A hA B hB ↦
      hF A (slice_subset hA) B (slice_subset hB)
  · have he : F.slice k = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun A hA ↦ hsmall ?_
      refine ⟨A, slice_subset hA, ?_⟩
      rw [sized_slice hA]
      exact ⟨hk, le_of_not_gt hlarge⟩
    simp [he]

end OMA703

theorem OMA.solution : type_of% @Erdos703.erdos_703.variants.frankl_furedi := by
  intro r
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    split_ifs with h
    · exact OMA703.odd_case n (by omega)
    · exact OMA703.even_case n hn (by omega)
  · change ∀ᶠ n : ℕ in Filter.atTop, Erdos703.T n r = OMA703.candidate n r
    have hupper : ∀ᶠ n : ℕ in Filter.atTop, Erdos703.T n r ≤ OMA703.candidate n r := by
      rcases eq_or_lt_of_le (show 1 ≤ r by omega) with h1 | hr
      · subst r
        filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
        exact OMA703.T_le_candidate_one n hn
      · have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
            ∀ F : Finset (Finset (Fin n)),
              (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r) →
              (∃ A ∈ F, r ≤ A.card ∧ A.card ≤ r + r.factorial) →
              F.card ≤ OMA703.candidate n r := by
          sorry
        filter_upwards [hsmall, Filter.eventually_ge_atTop (r + 1)] with n hs hn
        unfold Erdos703.T
        refine csSup_le' ?_
        rintro _ ⟨F, hF, rfl⟩
        by_cases h : ∃ A ∈ F, r ≤ A.card ∧ A.card ≤ r + r.factorial
        · exact hs F hF h
        · exact OMA703.card_le_candidate_of_no_small_member (by omega) (by omega) hF h
    filter_upwards [hupper, Filter.eventually_ge_atTop (1 : ℕ)] with n hu hn
    exact le_antisymm hu (OMA703.candidate_le_T n r hn)
