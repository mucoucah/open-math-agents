import FormalConjectures.ErdosProblems.«40»

/-!
# Partial results toward Erdős Problem 40 (weaker variant)

This file proves:
1. Erdős (1955) for Sidon sets (`sumRep A n ≤ 2`): no set with at most 2 ordered
   representations per sum satisfies `|A ∩ [1, N]| ≫ √N`.
2. General odd-cap thinning (`2 * h + 1 → 2 * h` for all `h ≥ 1`) via greedy removal
   of saturated diagonal sums, immediately extending Erdős (1955) to `sumRep A n ≤ 3`.
3. Positive-shift intersection cap lowering (`A ∩ (A - d)` drops the global cap by 1).
4. Exact additive energy identity (`∑ r_S(s)^2 = |S|^2 + 2 ∑ δ_S(d)^2`), sharp cap
   prefix bound `(|A ∩ [1, N]| - 1)^2 ≤ 2 * (k - 1) * (N - 1)`, unbounded close-pair
   and difference multiplicity for any `√N`-dense bounded-representation set, and
   generalization of Erdős (1955) to all uniformly difference-bounded sets.
5. Cross-block saturation bound for `B_2[2]` sets (`sumRep A n ≤ 4`): the inner product
   of positive shift multiplicities over `1 ≤ d < P` across blocks separated by `P` is `≤ N`.
6. Exact equivalence `weaker_iff_constant_one` between `Erdos40.erdos_40.variants.weaker`
   and `Erdos40For (fun _ ↦ 1)`.
7. Two-shift and multi-shift cap lowering: any two distinct positive shifts drop a global
   cap by at least 2 (so every two-shift intersection of a `B_2[2]` set is Sidon, and of a
   cap-3 set is subsingleton), and intersecting with more than `(k - 1)(k - 2)/2` positive
   shifts cuts any cap `k` at least in half.
8. Sharp dyadic summation-by-parts master inequality at scale `P = 2^m, N = P^2`, yielding
   Erdős's full 1955 quantitative bound `|A ∩ [1, N]|^2 * log N ≤ C * N` in every dyadic
   window `[2^m, 2^(2m)]` for Sidon, cap-3, and uniformly difference-bounded sets, plus
   sharp logarithmic close-pair (`Ω(m * 2^m)`) and difference-multiplicity (`Ω(m)`) growth
   at scale `N = P^2` for any `√N`-dense bounded-representation set.
9. Flexible dyadic windows force a positive proportion of directions with any fixed
   multiplicity inside a fixed multiple of every sufficiently large scale. A positive shift
   intersection can be thinned to half the cap while retaining at least half of every
   prefix. At cap four, deleting at most one point makes any such intersection Sidon,
   and the common sum of opposite pairs determines a rectangle with its shorter side
   designated.
10. Compactness and diagonalization reducing `Erdos40.erdos_40.variants.weaker` to
   `even_cap_no_dense_shift_not_sqrt_dense` (even caps `2 * g`, `g ≥ 2`, with no dense
   positive shift intersection and logarithmic difference multiplicity at scale `P^2`),
   which implies the Erdős-Turán conjecture (`Erdos28.erdos_28`).
-/

-- Problem: Erdős Problem 40 — weaker
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/40.lean:67 (declaration Erdos40.erdos_40.variants.weaker)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos40WeakerPartial

open AdditiveCombinatorics Filter Real Set

/-- Ordered representation pairs of `n` in `A`. -/
noncomputable def repPairs (A : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  by classical exact (_root_.Finset.HasAntidiagonal.antidiagonal n).filter (fun p ↦ p.1 ∈ A ∧ p.2 ∈ A)

lemma mem_repPairs {A : Set ℕ} {n : ℕ} {p : ℕ × ℕ} :
    p ∈ repPairs A n ↔ p.1 + p.2 = n ∧ p.1 ∈ A ∧ p.2 ∈ A := by
  classical
  simp [repPairs]

lemma card_repPairs (A : Set ℕ) (n : ℕ) :
    (repPairs A n).card = sumRep A n := by
  classical
  rw [sumRep_def, repPairs]

/-- In a Sidon set (`sumRep A n ≤ 2`), positive differences determine the pair uniquely. -/
lemma sidon_diff_inj {A : Set ℕ} (hS : ∀ n, sumRep A n ≤ 2)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hba : b < a) (hdc : d < c) (hdiff : a - b = c - d) :
    a = c ∧ b = d := by
  classical
  have hsum : a + d = c + b := by omega
  by_contra hne
  have hac : a ≠ c := by
    intro heq
    apply hne
    exact ⟨heq, by omega⟩
  have hle : (repPairs A (a + d)).card ≤ 2 := by
    rw [card_repPairs]
    exact hS (a + d)
  by_cases had : a = d
  · have hsub : ({(a, a), (c, b), (b, c)} : Finset (ℕ × ℕ)) ⊆ repPairs A (a + d) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_repPairs.mpr ⟨by omega, ha, ha⟩
      · exact mem_repPairs.mpr ⟨by omega, hc, hb⟩
      · exact mem_repPairs.mpr ⟨by omega, hb, hc⟩
    have hcard : ({(a, a), (c, b), (b, c)} : Finset (ℕ × ℕ)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton, Prod.mk.injEq]
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega
    have := (Finset.card_le_card hsub).trans hle
    omega
  · have hsub : ({(a, d), (d, a), (c, b)} : Finset (ℕ × ℕ)) ⊆ repPairs A (a + d) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_repPairs.mpr ⟨rfl, ha, hd⟩
      · exact mem_repPairs.mpr ⟨by omega, hd, ha⟩
      · exact mem_repPairs.mpr ⟨by omega, hc, hb⟩
    have hcard : ({(a, d), (d, a), (c, b)} : Finset (ℕ × ℕ)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton, Prod.mk.injEq]
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega
    have := (Finset.card_le_card hsub).trans hle
    omega

/-- Decomposition of `S ×ˢ S` into strictly ordered pairs and the diagonal. -/
lemma card_sq_eq_two_mul_lt_add_self (S : Finset ℕ) :
    S.card * S.card = 2 * ((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card + S.card := by
  classical
  have hswap : ((S ×ˢ S).filter (fun p ↦ p.1 < p.2)).card =
      ((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _; exact Prod.swap_swap p
    · intro p _; exact Prod.swap_swap p
  have hdiag : ((S ×ˢ S).filter (fun p ↦ p.1 = p.2)).card = S.card := by
    refine Finset.card_nbij' Prod.fst (fun x ↦ (x, x)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx ⊢
      exact ⟨⟨hx, hx⟩, trivial⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter] at hp
      exact Prod.ext rfl hp.2
    · intro x _; rfl
  have h1 := Finset.card_filter_add_card_filter_not (s := S ×ˢ S) (fun p : ℕ × ℕ ↦ p.2 < p.1)
  have h2 : ((S ×ˢ S).filter (fun p ↦ ¬ p.2 < p.1)).card =
      ((S ×ˢ S).filter (fun p ↦ p.1 < p.2)).card + ((S ×ˢ S).filter (fun p ↦ p.1 = p.2)).card := by
    have heq : (S ×ˢ S).filter (fun p ↦ ¬ p.2 < p.1) =
        (S ×ˢ S).filter (fun p ↦ p.1 < p.2) ∪ (S ×ˢ S).filter (fun p ↦ p.1 = p.2) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro ⟨hp, hle⟩
        rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr ⟨hp, h⟩
      · rintro (⟨hp, h⟩ | ⟨hp, h⟩) <;> exact ⟨hp, by omega⟩
    rw [heq, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    omega
  rw [Finset.card_product] at h1
  omega

/-- Every finite Sidon prefix satisfies `|A ∩ [1, N]|^2 ≤ 4 * N + 1`. -/
lemma sidon_prefix_sq_le {A : Set ℕ} (hS : ∀ n, sumRep A n ≤ 2) (N : ℕ) :
    ((A ∩ Icc 1 N).ncard) ^ 2 ≤ 4 * N + 1 := by
  classical
  let S := (Finset.Icc 1 N).filter (· ∈ A)
  have hScard : S.card = (A ∩ Icc 1 N).ncard := by
    have heq : (S : Set ℕ) = A ∩ Icc 1 N := by
      ext x
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
        Set.mem_Icc]
      tauto
    rw [← Set.ncard_coe_finset, heq]
  let D := (S ×ˢ S).filter (fun p ↦ p.2 < p.1)
  have hDle : D.card ≤ N := by
    have hcard_ico : (Finset.Ico 1 N).card ≤ N := by
      simp only [Nat.card_Ico]
      omega
    refine le_trans ?_ hcard_ico
    refine Finset.card_le_card_of_injOn (fun p ↦ p.1 - p.2) ?_ ?_
    · intro p hp
      simp only [D, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Ico] at hp ⊢
      omega
    · intro p hp q hq heq
      simp only [D, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
      have h := sidon_diff_inj hS hp.1.1.2 hp.1.2.2 hq.1.1.2 hq.1.2.2 hp.2 hq.2 heq
      exact Prod.ext h.1 h.2
  have hsq : S.card * S.card = 2 * D.card + S.card := card_sq_eq_two_mul_lt_add_self S
  have hZ : (S.card : ℤ) ^ 2 ≤ 4 * (N : ℤ) + 1 := by
    have hsqZ : (S.card : ℤ) * (S.card : ℤ) = 2 * (D.card : ℤ) + (S.card : ℤ) := by
      exact_mod_cast hsq
    have hDZ : (D.card : ℤ) ≤ (N : ℤ) := by exact_mod_cast hDle
    nlinarith [sq_nonneg ((S.card : ℤ) - 1)]
  rw [← hScard]
  exact_mod_cast hZ

/-- Cauchy-Schwarz inequality for finite sums of natural numbers. -/
lemma sq_sum_le_card_mul_sum_sq_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · have hs : s = ∅ := Finset.card_eq_zero.mp h0
      subst hs
      simp
    · have hZ : ((f a : ℤ) + ∑ i ∈ s, (f i : ℤ)) ^ 2 ≤
          ((s.card : ℤ) + 1) * ((f a : ℤ) ^ 2 + ∑ i ∈ s, (f i : ℤ) ^ 2) := by
        have ihZ : (∑ i ∈ s, (f i : ℤ)) ^ 2 ≤ (s.card : ℤ) * ∑ i ∈ s, (f i : ℤ) ^ 2 := by
          exact_mod_cast ih
        have hposZ : (0 : ℤ) < (s.card : ℤ) := by exact_mod_cast hpos
        nlinarith [sq_nonneg ((s.card : ℤ) * (f a : ℤ) - ∑ i ∈ s, (f i : ℤ))]
      exact_mod_cast hZ

/-- Bucketing `T ⊆ [0, N]` into blocks of width `P` bounds close pairs from below via Cauchy-Schwarz. -/
lemma bucket_close_pairs_bound (T : Finset ℕ) {N P : ℕ} (hP : 0 < P)
    (hTN : ∀ x ∈ T, x ≤ N) :
    T.card ^ 2 ≤ (N / P + 1) *
      (2 * ((T ×ˢ T).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)).card + T.card) := by
  classical
  let B := N / P + 1
  let bucket : ℕ → Finset ℕ := fun b ↦ T.filter (fun x ↦ x / P = b)
  let E : ℕ → Finset (ℕ × ℕ) := fun b ↦ (bucket b ×ˢ bucket b).filter (fun p ↦ p.2 < p.1)
  have hsum_card : ∑ b ∈ Finset.range B, (bucket b).card = T.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_range, bucket, Finset.mem_filter]
      constructor
      · rintro ⟨_, _, hx, _⟩; exact hx
      · intro hx
        refine ⟨x / P, ?_, hx, rfl⟩
        exact Nat.lt_succ_of_le (Nat.div_le_div_right (hTN x hx))
    · intro b₁ _ b₂ _ hne
      change Disjoint (bucket b₁) (bucket b₂)
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      simp only [bucket, Finset.mem_filter] at hx₁ hx₂
      exact hne (hx₁.2.symm.trans hx₂.2)
  have hcs : (∑ b ∈ Finset.range B, (bucket b).card) ^ 2 ≤
      (Finset.range B).card * ∑ b ∈ Finset.range B, (bucket b).card ^ 2 :=
    sq_sum_le_card_mul_sum_sq_nat (Finset.range B) (fun b ↦ (bucket b).card)
  rw [hsum_card, Finset.card_range] at hcs
  have hsq_sum : ∑ b ∈ Finset.range B, (bucket b).card ^ 2 =
      2 * (∑ b ∈ Finset.range B, (E b).card) + T.card := by
    have hterm : ∀ b ∈ Finset.range B, (bucket b).card ^ 2 = 2 * (E b).card + (bucket b).card := by
      intro b _
      rw [pow_two]
      exact card_sq_eq_two_mul_lt_add_self (bucket b)
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hsum_card]
  have hE_le : ∑ b ∈ Finset.range B, (E b).card ≤
      ((T ×ˢ T).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)).card := by
    rw [← Finset.card_biUnion]
    · apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_biUnion, E, bucket, Finset.mem_filter, Finset.mem_product] at hp ⊢
      rcases hp with ⟨b, _, ⟨⟨⟨hp1, hd1⟩, ⟨hp2, hd2⟩⟩, hlt⟩⟩
      refine ⟨⟨hp1, hp2⟩, hlt, ?_⟩
      have hdiv1 := Nat.div_add_mod p.1 P
      have hdiv2 := Nat.div_add_mod p.2 P
      have hm1 := Nat.mod_lt p.1 hP
      have hm2 := Nat.mod_lt p.2 hP
      rw [hd1] at hdiv1
      rw [hd2] at hdiv2
      omega
    · intro b₁ _ b₂ _ hne
      change Disjoint (E b₁) (E b₂)
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      simp only [E, bucket, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
      exact hne (hp₁.1.1.2.symm.trans hp₂.1.1.2)
  rw [hsq_sum] at hcs
  exact hcs.trans (Nat.mul_le_mul_left B (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hE_le) _))

/-- Erdos (1955): no infinite Sidon set satisfies `|A ∩ [1, N]| ≫ √N`. -/
theorem sidon_not_sqrt_dense {A : Set ℕ} (hS : ∀ n, sumRep A n ≤ 2) :
    ¬ ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) := by
  classical
  intro hdense
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hdense
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hc
  obtain ⟨C₀, hC₀⟩ := exists_nat_ge (max c 1)
  let C := max C₀ 1
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := by omega
  have hcC : c ≤ (C : ℝ) := (le_max_left c 1).trans (hC₀.trans (by exact_mod_cast le_max_left C₀ 1))
  have hlower : ∀ N, N₀ ≤ N → N ≤ C ^ 2 * ((A ∩ Icc 1 N).ncard) ^ 2 := by
    intro N hN
    have h1 := hN₀ N hN
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast] at h1
    have h2 : √(N : ℝ) ≤ (C : ℝ) * ((A ∩ Icc 1 N).ncard : ℝ) :=
      h1.trans (mul_le_mul_of_nonneg_right hcC (Nat.cast_nonneg _))
    have h3 : (N : ℝ) ≤ ((C : ℝ) * ((A ∩ Icc 1 N).ncard : ℝ)) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
      rwa [Real.sq_sqrt (Nat.cast_nonneg _)] at this
    have h4 : (N : ℝ) ≤ ((C ^ 2 * ((A ∩ Icc 1 N).ncard) ^ 2 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h4
  let r := 32 * C ^ 2
  have hr_pos : 0 < r := by positivity
  let K := 32 * C ^ 2
  let P := max (max N₀ 1) (64 * C ^ 2 * r ^ K)
  have hP1 : 1 ≤ P := (le_max_right N₀ 1).trans (le_max_left _ _)
  have hPpos : 0 < P := by omega
  have hPN0 : N₀ ≤ P := (le_max_left N₀ 1).trans (le_max_left _ _)
  have hPbig : 64 * C ^ 2 * r ^ K ≤ P := le_max_right _ _
  let T : ℕ → Finset ℕ := fun k ↦ (Finset.Icc (P * r ^ k + 1) (P * r ^ (k + 1))).filter (· ∈ A)
  let E : ℕ → Finset (ℕ × ℕ) := fun k ↦ (T k ×ˢ T k).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)
  have hblock : ∀ k ∈ Finset.range K, P ≤ 32 * C ^ 2 * (E k).card := by
    intro k hk
    have hkK : k < K := Finset.mem_range.mp hk
    let Mk := P * r ^ k
    let Nk := P * r ^ (k + 1)
    have hNk_eq : Nk = r * Mk := by
      dsimp [Nk, Mk]
      rw [pow_succ]
      ring
    have hMk1 : 1 ≤ Mk := by
      dsimp [Mk]
      exact Nat.mul_pos hPpos (pow_pos hr_pos k)
    have hNkN0 : N₀ ≤ Nk := by
      refine hPN0.trans ?_
      dsimp [Nk]
      exact Nat.le_mul_of_pos_right P (pow_pos hr_pos (k + 1))
    have haN : Nk ≤ C ^ 2 * ((A ∩ Icc 1 Nk).ncard) ^ 2 := hlower Nk hNkN0
    have haM : ((A ∩ Icc 1 Mk).ncard) ^ 2 ≤ 4 * Mk + 1 := sidon_prefix_sq_le hS Mk
    have hsplit : (A ∩ Icc 1 Nk).ncard = (A ∩ Icc 1 Mk).ncard + (T k).card := by
      let SM := (Finset.Icc 1 Mk).filter (· ∈ A)
      let SN := (Finset.Icc 1 Nk).filter (· ∈ A)
      have hSM : SM.card = (A ∩ Icc 1 Mk).ncard := by
        have heq : (SM : Set ℕ) = A ∩ Icc 1 Mk := by
          ext x
          simp only [SM, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
            Set.mem_Icc]
          tauto
        rw [← Set.ncard_coe_finset, heq]
      have hSN : SN.card = (A ∩ Icc 1 Nk).ncard := by
        have heq : (SN : Set ℕ) = A ∩ Icc 1 Nk := by
          ext x
          simp only [SN, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
            Set.mem_Icc]
          tauto
        rw [← Set.ncard_coe_finset, heq]
      rw [← hSM, ← hSN, ← Finset.card_union_of_disjoint]
      · congr 1
        ext x
        simp only [SN, SM, T, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
        have hMkNk : Mk ≤ Nk := by
          rw [hNk_eq]
          exact Nat.le_mul_of_pos_left Mk hr_pos
        constructor
        · rintro ⟨⟨h1, h2⟩, hxA⟩
          by_cases hxM : x ≤ Mk
          · exact Or.inl ⟨⟨h1, hxM⟩, hxA⟩
          · exact Or.inr ⟨⟨by omega, h2⟩, hxA⟩
        · rintro (⟨⟨h1, h2⟩, hxA⟩ | ⟨⟨h1, h2⟩, hxA⟩) <;> exact ⟨⟨by omega, by omega⟩, hxA⟩
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [SM, T, Finset.mem_filter, Finset.mem_Icc] at hx1 hx2
        omega
    have hhalf : 2 * (A ∩ Icc 1 Mk).ncard < (A ∩ Icc 1 Nk).ncard := by
      have hlt : (2 * (A ∩ Icc 1 Mk).ncard) ^ 2 < ((A ∩ Icc 1 Nk).ncard) ^ 2 := by
        have hC2pos : 0 < C ^ 2 := pow_pos hCpos 2
        have hmul : C ^ 2 * (2 * (A ∩ Icc 1 Mk).ncard) ^ 2 < C ^ 2 * ((A ∩ Icc 1 Nk).ncard) ^ 2 := by
          calc C ^ 2 * (2 * (A ∩ Icc 1 Mk).ncard) ^ 2
              = 4 * C ^ 2 * ((A ∩ Icc 1 Mk).ncard) ^ 2 := by ring
            _ ≤ 4 * C ^ 2 * (4 * Mk + 1) := Nat.mul_le_mul_left _ haM
            _ ≤ 4 * C ^ 2 * (5 * Mk) := Nat.mul_le_mul_left _ (by omega)
            _ = 20 * C ^ 2 * Mk := by ring
            _ < 32 * C ^ 2 * Mk := by nlinarith
            _ = Nk := hNk_eq.symm
            _ ≤ C ^ 2 * ((A ∩ Icc 1 Nk).ncard) ^ 2 := haN
        exact (Nat.mul_lt_mul_left hC2pos).mp hmul
      nlinarith
    have hTlb : Nk ≤ 4 * C ^ 2 * (T k).card ^ 2 := by
      have : (A ∩ Icc 1 Nk).ncard ≤ 2 * (T k).card := by omega
      calc Nk ≤ C ^ 2 * ((A ∩ Icc 1 Nk).ncard) ^ 2 := haN
        _ ≤ C ^ 2 * (2 * (T k).card) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 2)
        _ = 4 * C ^ 2 * (T k).card ^ 2 := by ring
    have hcs := bucket_close_pairs_bound (T k) hPpos (fun x hx ↦ by
      simp only [T, Finset.mem_filter, Finset.mem_Icc] at hx
      exact hx.1.2)
    have hdiv : Nk / P = r ^ (k + 1) := by
      dsimp [Nk]
      exact Nat.mul_div_right _ hPpos
    rw [hdiv] at hcs
    let Bk := r ^ (k + 1) + 1
    have hBk_le : Bk ≤ 2 * r ^ (k + 1) := by
      dsimp [Bk]
      have : 1 ≤ r ^ (k + 1) := Nat.one_le_pow _ _ hr_pos
      omega
    have h2Bk_le : 2 * Bk ≤ (T k).card := by
      have hrk : r ^ (k + 1) ≤ r ^ K := Nat.pow_le_pow_right hr_pos (by omega)
      have hsq_le : 4 * C ^ 2 * (2 * Bk) ^ 2 ≤ 4 * C ^ 2 * (T k).card ^ 2 := by
        calc 4 * C ^ 2 * (2 * Bk) ^ 2
            ≤ 4 * C ^ 2 * (4 * r ^ (k + 1)) ^ 2 :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
          _ = 64 * C ^ 2 * r ^ (k + 1) * r ^ (k + 1) := by ring
          _ ≤ 64 * C ^ 2 * r ^ K * r ^ (k + 1) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrk)
          _ ≤ P * r ^ (k + 1) := Nat.mul_le_mul_right _ hPbig
          _ ≤ 4 * C ^ 2 * (T k).card ^ 2 := hTlb
      have hC4pos : 0 < 4 * C ^ 2 := by positivity
      have := Nat.le_of_mul_le_mul_left hsq_le hC4pos
      nlinarith
    have hTsq_le : (T k).card ^ 2 ≤ 8 * r ^ (k + 1) * (E k).card := by
      have hcs' : (T k).card ^ 2 ≤ Bk * (2 * (E k).card + (T k).card) := hcs
      have h2 : 2 * (T k).card ^ 2 ≤ 4 * Bk * (E k).card + (2 * Bk) * (T k).card := by
        nlinarith
      have h3 : (2 * Bk) * (T k).card ≤ (T k).card ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_right _ h2Bk_le
      have h4 : (T k).card ^ 2 ≤ 4 * Bk * (E k).card := by omega
      calc (T k).card ^ 2 ≤ 4 * Bk * (E k).card := h4
        _ ≤ 4 * (2 * r ^ (k + 1)) * (E k).card :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hBk_le)
        _ = 8 * r ^ (k + 1) * (E k).card := by ring
    have hfinal : P * r ^ (k + 1) ≤ 32 * C ^ 2 * (E k).card * r ^ (k + 1) := by
      calc P * r ^ (k + 1) ≤ 4 * C ^ 2 * (T k).card ^ 2 := hTlb
        _ ≤ 4 * C ^ 2 * (8 * r ^ (k + 1) * (E k).card) := Nat.mul_le_mul_left _ hTsq_le
        _ = 32 * C ^ 2 * (E k).card * r ^ (k + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hfinal (pow_pos hr_pos (k + 1))
  have hsum_lb : K * P ≤ 32 * C ^ 2 * ∑ k ∈ Finset.range K, (E k).card := by
    calc K * P = ∑ _k ∈ Finset.range K, P := by simp
      _ ≤ ∑ k ∈ Finset.range K, 32 * C ^ 2 * (E k).card := Finset.sum_le_sum hblock
      _ = 32 * C ^ 2 * ∑ k ∈ Finset.range K, (E k).card := by rw [← Finset.mul_sum]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range K) : Set ℕ) E := by
    intro k₁ _ k₂ _ hne
    change Disjoint (E k₁) (E k₂)
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [E, T, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : P * r ^ (k₁ + 1) ≤ P * r ^ k₂ :=
        Nat.mul_le_mul_left P (Nat.pow_le_pow_right hr_pos hlt)
      omega
    · have : P * r ^ (k₂ + 1) ≤ P * r ^ k₁ :=
        Nat.mul_le_mul_left P (Nat.pow_le_pow_right hr_pos hgt)
      omega
  have hsum_ub : ∑ k ∈ Finset.range K, (E k).card < P := by
    rw [← Finset.card_biUnion hdisj]
    have hico : (Finset.Ico 1 P).card < P := by
      simp only [Nat.card_Ico]
      omega
    refine lt_of_le_of_lt ?_ hico
    refine Finset.card_le_card_of_injOn (fun p ↦ p.1 - p.2) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_biUnion, E, Finset.mem_filter, Finset.mem_Ico] at hp ⊢
      rcases hp with ⟨_, _, _, hlt, hdiff⟩
      omega
    · intro p hp q hq heq
      simp only [Finset.mem_coe, Finset.mem_biUnion, E, T, Finset.mem_filter,
        Finset.mem_product] at hp hq
      rcases hp with ⟨_, _, ⟨⟨_, hp1A⟩, ⟨_, hp2A⟩⟩, hplt, _⟩
      rcases hq with ⟨_, _, ⟨⟨_, hq1A⟩, ⟨_, hq2A⟩⟩, hqlt, _⟩
      have h := sidon_diff_inj hS hp1A hp2A hq1A hq2A hplt hqlt heq
      exact Prod.ext h.1 h.2
  have hKmul : K * P < 32 * C ^ 2 * P := by
    calc K * P ≤ 32 * C ^ 2 * ∑ k ∈ Finset.range K, (E k).card := hsum_lb
      _ < 32 * C ^ 2 * P := Nat.mul_lt_mul_of_pos_left hsum_ub (by positivity)
  dsimp [K] at hKmul
  omega

/-- An odd representation count forces a diagonal pair `(c, c)`. -/
lemma exists_diag_of_odd_rep {A : Set ℕ} {n : ℕ} (hodd : Odd (repPairs A n).card) :
    ∃ c ∈ A, n = c + c := by
  classical
  by_contra hno
  have hswap : ((repPairs A n).filter (fun p ↦ p.1 < p.2)).card =
      ((repPairs A n).filter (fun p ↦ p.2 < p.1)).card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, mem_repPairs, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact ⟨⟨by omega, hp.1.2.2, hp.1.2.1⟩, hp.2⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, mem_repPairs, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact ⟨⟨by omega, hp.1.2.2, hp.1.2.1⟩, hp.2⟩
    · intro p _; exact Prod.swap_swap p
    · intro p _; exact Prod.swap_swap p
  have hunion : repPairs A n =
      (repPairs A n).filter (fun p ↦ p.1 < p.2) ∪ (repPairs A n).filter (fun p ↦ p.2 < p.1) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      have hmem := mem_repPairs.mp hp
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl ⟨hp, h⟩
      · exfalso
        exact hno ⟨p.1, hmem.2.1, by omega⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint ((repPairs A n).filter (fun p ↦ p.1 < p.2))
      ((repPairs A n).filter (fun p ↦ p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    omega
  have hcard : (repPairs A n).card = 2 * ((repPairs A n).filter (fun p ↦ p.1 < p.2)).card := by
    conv_lhs => rw [hunion]
    rw [Finset.card_union_of_disjoint hdisj, hswap]
    omega
  rcases hodd with ⟨k, hk⟩
  omega

/-- Greedy drop predicate defined by strong recursion on `ℕ`. -/
noncomputable def greedyDrop (sat : ℕ → Prop) (hi : ℕ → ℕ) : ℕ → Prop :=
  Nat.lt_wfRel.wf.fix (fun v rec ↦ ∃ c, ∃ h : c < v, sat c ∧ ¬ rec c h ∧ hi c = v)

lemma greedyDrop_iff (sat : ℕ → Prop) (hi : ℕ → ℕ) (v : ℕ) :
    greedyDrop sat hi v ↔ ∃ c < v, sat c ∧ ¬ greedyDrop sat hi c ∧ hi c = v := by
  unfold greedyDrop
  rw [WellFounded.fix_eq]
  simp only [exists_prop]

/-- Any set with `sumRep A n ≤ 2 * h + 1` (`1 ≤ h`) contains a subset with `sumRep B n ≤ 2 * h`
retaining at least half of every prefix `[1, N]`. -/
lemma exists_even_cap_sub {h : ℕ} (hh : 1 ≤ h) {A : Set ℕ} (hcap : ∀ n, sumRep A n ≤ 2 * h + 1) :
    ∃ B : Set ℕ, B ⊆ A ∧ (∀ n, sumRep B n ≤ 2 * h) ∧
      ∀ N : ℕ, (A ∩ Icc 1 N).ncard ≤ 2 * (B ∩ Icc 1 N).ncard := by
  classical
  let sat (c : ℕ) : Prop := c ∈ A ∧ sumRep A (c + c) = 2 * h + 1
  have hex_hi : ∀ c, sat c → ∃ b, c < b ∧ b ≤ c + c ∧ b ∈ A ∧ c + c - b ∈ A := by
    intro c ⟨hcA, hrep⟩
    have hgt : 1 < (repPairs A (c + c)).card := by
      rw [card_repPairs, hrep]
      omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hgt
    have pick : ∀ r ∈ repPairs A (c + c), r ≠ (c, c) →
        ∃ b, c < b ∧ b ≤ c + c ∧ b ∈ A ∧ c + c - b ∈ A := by
      rintro ⟨x, y⟩ hr hne
      obtain ⟨hs, hx, hy⟩ := mem_repPairs.mp hr
      simp only at hs hx hy
      rcases lt_trichotomy x y with hlt | heq | hgt
      · exact ⟨y, by omega, by omega, hy, by rwa [show c + c - y = x by omega]⟩
      · exfalso; apply hne; exact Prod.ext (by omega) (by omega)
      · exact ⟨x, by omega, by omega, hx, by rwa [show c + c - x = y by omega]⟩
    by_cases hpc : p = (c, c)
    · exact pick q hq (fun hqc ↦ hpq (hpc.trans hqc.symm))
    · exact pick p hp hpc
  let hi (c : ℕ) : ℕ := if h' : sat c then Classical.choose (hex_hi c h') else 0
  have hi_spec : ∀ {c}, sat c → c < hi c ∧ hi c ≤ c + c ∧ hi c ∈ A ∧ c + c - hi c ∈ A := by
    intro c hc
    simp only [hi, dif_pos hc]
    exact Classical.choose_spec (hex_hi c hc)
  let drop := greedyDrop sat hi
  have drop_iff : ∀ v, drop v ↔ ∃ c < v, sat c ∧ ¬ drop c ∧ hi c = v :=
    greedyDrop_iff sat hi
  let B : Set ℕ := {x | x ∈ A ∧ ¬ drop x}
  refine ⟨B, fun _ hx ↦ hx.1, ?_, ?_⟩
  · intro n
    have hle : sumRep B n ≤ sumRep A n := by
      rw [← card_repPairs, ← card_repPairs]
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hs, h1, h2⟩ := mem_repPairs.mp hp
      exact mem_repPairs.mpr ⟨hs, h1.1, h2.1⟩
    by_cases hAsat : sumRep A n = 2 * h + 1
    · have hodd : Odd (repPairs A n).card := by
        rw [card_repPairs, hAsat]
        exact ⟨h, rfl⟩
      obtain ⟨c, hcA, rfl⟩ := exists_diag_of_odd_rep hodd
      have hsat : sat c := ⟨hcA, hAsat⟩
      have hstrict : repPairs B (c + c) ⊂ repPairs A (c + c) := by
        rw [Finset.ssubset_iff_of_subset (fun p hp ↦ by
          obtain ⟨hs, h1, h2⟩ := mem_repPairs.mp hp
          exact mem_repPairs.mpr ⟨hs, h1.1, h2.1⟩)]
        by_cases hdropc : drop c
        · refine ⟨(c, c), mem_repPairs.mpr ⟨rfl, hcA, hcA⟩, ?_⟩
          intro hmem
          exact (mem_repPairs.mp hmem).2.1.2 hdropc
        · obtain ⟨hchi, hhi2, hhiA, hloA⟩ := hi_spec hsat
          have hdrophi : drop (hi c) := (drop_iff (hi c)).mpr ⟨c, hchi, hsat, hdropc, rfl⟩
          refine ⟨(c + c - hi c, hi c), mem_repPairs.mpr ⟨by omega, hloA, hhiA⟩, ?_⟩
          intro hmem
          exact (mem_repPairs.mp hmem).2.2.2 hdrophi
      have hlt := Finset.card_lt_card hstrict
      rw [card_repPairs, card_repPairs, hAsat] at hlt
      omega
    · have := hcap n
      omega
  · intro N
    let FA := (Finset.Icc 1 N).filter (· ∈ A)
    let FB := (Finset.Icc 1 N).filter (· ∈ B)
    let FD := (Finset.Icc 1 N).filter (fun x ↦ x ∈ A ∧ drop x)
    have hFA : FA.card = (A ∩ Icc 1 N).ncard := by
      have heq : (FA : Set ℕ) = A ∩ Icc 1 N := by
        ext x
        simp only [FA, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
          Set.mem_Icc]
        tauto
      rw [← Set.ncard_coe_finset, heq]
    have hFB : FB.card = (B ∩ Icc 1 N).ncard := by
      have heq : (FB : Set ℕ) = B ∩ Icc 1 N := by
        ext x
        simp only [FB, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
          Set.mem_Icc]
        tauto
      rw [← Set.ncard_coe_finset, heq]
    have hsplit : FA.card = FB.card + FD.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext x
        simp only [FA, FB, FD, B, Finset.mem_union, Finset.mem_filter, Set.mem_ofPred_eq]
        tauto
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [FB, FD, B, Finset.mem_filter, Set.mem_ofPred_eq] at hx1 hx2
        exact hx1.2.2 hx2.2.2
    have hFD_le : FD.card ≤ FB.card := by
      let parent : ℕ → ℕ := fun v ↦
        if h' : drop v then Classical.choose ((drop_iff v).mp h') else 0
      refine Finset.card_le_card_of_injOn parent ?_ ?_
      · intro v hv
        simp only [FD, FB, B, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc,
          Set.mem_ofPred_eq] at hv ⊢
        have hdv : drop v := hv.2.2
        have hspec := Classical.choose_spec ((drop_iff v).mp hdv)
        simp only [parent, dif_pos hdv]
        obtain ⟨hcv, hsatc, hndropc, _⟩ := hspec
        have hcpos : 1 ≤ Classical.choose ((drop_iff v).mp hdv) := by
          by_contra hc0
          have h0 : Classical.choose ((drop_iff v).mp hdv) = 0 := by omega
          have hrep0 : sumRep A 0 = 2 * h + 1 := by
            have := hsatc.2
            rw [h0] at this
            exact this
          have hle1 : sumRep A 0 ≤ 1 := by
            rw [← card_repPairs]
            have hsub : repPairs A 0 ⊆ {(0, 0)} := by
              intro p hp
              have := (mem_repPairs.mp hp).1
              simp only [Finset.mem_singleton]
              exact Prod.ext (by omega) (by omega)
            exact (Finset.card_le_card hsub).trans (by simp)
          omega
        exact ⟨⟨hcpos, by omega⟩, ⟨hsatc.1, hndropc⟩⟩
      · intro v₁ hv₁ v₂ hv₂ heq
        simp only [FD, Finset.mem_coe, Finset.mem_filter] at hv₁ hv₂
        have hd1 : drop v₁ := hv₁.2.2
        have hd2 : drop v₂ := hv₂.2.2
        have hs1 := Classical.choose_spec ((drop_iff v₁).mp hd1)
        have hs2 := Classical.choose_spec ((drop_iff v₂).mp hd2)
        simp only [parent, dif_pos hd1, dif_pos hd2] at heq
        rw [← hs1.2.2.2, heq, hs2.2.2.2]
    omega

/-- Extending Erdos (1955) to `sumRep A n ≤ 3`: no such set satisfies `|A ∩ [1, N]| ≫ √N`. -/
theorem cap_three_not_sqrt_dense {A : Set ℕ} (h3 : ∀ n, sumRep A n ≤ 3) :
    ¬ ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) := by
  intro hA
  obtain ⟨B, _, hB2, hprefix⟩ := exists_even_cap_sub (h := 1) le_rfl h3
  apply sidon_not_sqrt_dense hB2
  refine hA.trans (Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun N ↦ ?_))
  simp only [Real.norm_natCast]
  exact_mod_cast hprefix N

/-- Passing to `{x ∈ A | x + d ∈ A}` for `d > 0` strictly lowers every positive representation count. -/
lemma sumRep_shift_inter_lt {A : Set ℕ} {d n : ℕ} (hd : 0 < d)
    (hpos : 0 < sumRep {x | x ∈ A ∧ x + d ∈ A} n) :
    sumRep {x | x ∈ A ∧ x + d ∈ A} n < sumRep A (n + d) := by
  classical
  let B : Set ℕ := {x | x ∈ A ∧ x + d ∈ A}
  have hne : (repPairs B n).Nonempty :=
    Finset.card_pos.mp (by rw [card_repPairs]; exact hpos)
  let fsts := (repPairs B n).image Prod.fst
  obtain ⟨p, hp, hpmax⟩ := Finset.mem_image.mp (Finset.max'_mem fsts (hne.image _))
  obtain ⟨hpsum, hp1, hp2⟩ := mem_repPairs.mp hp
  let emb : ℕ × ℕ ↪ ℕ × ℕ :=
    ⟨fun q ↦ (q.1, q.2 + d), fun q₁ q₂ h ↦ by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Nat.add_right_cancel h.2)⟩
  have hsub : (repPairs B n).map emb ⊆ repPairs A (n + d) := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hq
    obtain ⟨hrsum, hr1, hr2⟩ := mem_repPairs.mp hr
    change (r.1, r.2 + d) ∈ repPairs A (n + d)
    exact mem_repPairs.mpr ⟨by dsimp; omega, hr1.1, hr2.2⟩
  have hmem_out : (p.1 + d, p.2) ∈ repPairs A (n + d) :=
    mem_repPairs.mpr ⟨by omega, hp1.2, hp2.1⟩
  have hnotmem_out : (p.1 + d, p.2) ∉ (repPairs B n).map emb := by
    intro hmem
    obtain ⟨r, hr, hreq⟩ := Finset.mem_map.mp hmem
    have hrle : r.1 ≤ p.1 := by
      have := Finset.le_max' fsts r.1 (Finset.mem_image_of_mem _ hr)
      omega
    have hrfst : r.1 = p.1 + d := congrArg Prod.fst hreq
    omega
  have hssub : (repPairs B n).map emb ⊂ repPairs A (n + d) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h ↦ hnotmem_out (h ▸ hmem_out)⟩
  have hlt := Finset.card_lt_card hssub
  rw [Finset.card_map, card_repPairs, card_repPairs] at hlt
  exact hlt

/-- Passing to `{x ∈ A | x + d ∈ A}` lowers any positive global representation cap by at least 1. -/
lemma sumRep_shift_inter_le {A : Set ℕ} {d k : ℕ} (hd : 0 < d)
    (hcap : ∀ n, sumRep A n ≤ k + 1) :
    ∀ n, sumRep {x | x ∈ A ∧ x + d ∈ A} n ≤ k := by
  intro n
  by_contra hgt
  have hlt := sumRep_shift_inter_lt hd (show 0 < sumRep {x | x ∈ A ∧ x + d ∈ A} n by omega)
  have := hcap (n + d)
  omega

/-- For any `B_2[2]` set (`sumRep A n ≤ 4`), no positive shift intersection `A ∩ (A - d)` has `≫ √N` density. -/
theorem shift_inter_not_sqrt_dense_of_cap_four {A : Set ℕ} (h4 : ∀ n, sumRep A n ≤ 4)
    {d : ℕ} (hd : 0 < d) :
    ¬ ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop]
      (fun N ↦ (({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard : ℝ))) :=
  cap_three_not_sqrt_dense (sumRep_shift_inter_le hd h4)

/-- Bounded `limsup` of `sumRep A` implies a uniform global upper bound. -/
lemma exists_global_cap_of_limsup_ne_top {A : Set ℕ}
    (h : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤) :
    ∃ k : ℕ, ∀ n, sumRep A n ≤ k := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
  have hlt : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop < ((m + 1 : ℕ) : ℕ∞) := by
    rw [← hm]
    exact_mod_cast Nat.lt_succ_self m
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
  refine ⟨max m ((Finset.range N).sup (sumRep A)), fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · have : sumRep A n < m + 1 := by exact_mod_cast hN n hn
    exact (Nat.le_of_lt_succ this).trans (le_max_left _ _)
  · exact (Finset.le_sup (f := sumRep A) (Finset.mem_range.mpr (by omega : n < N))).trans
      (le_max_right _ _)

/-- Compactness on Cantor space gives uniform density-drop windows for bounded-representation sets. -/
lemma exists_uniform_drop_window (h1 : Erdos40.Erdos40For (fun _ ↦ 1)) (k L : ℕ) :
    ∃ U : ℕ, ∀ A : Set ℕ, (∀ n, sumRep A n ≤ k) →
      ∃ n, L ≤ n ∧ n ≤ U ∧ (k : ℝ) ^ 2 * ((A ∩ Icc 1 n).ncard : ℝ) < √(n : ℝ) := by
  classical
  let toSet : (ℕ → Bool) → Set ℕ := fun f ↦ {i | f i = true}
  have hopen_prefix : ∀ {P : (ℕ → Bool) → Prop} (m : ℕ),
      (∀ f g, (∀ i ≤ m, f i = g i) → (P f ↔ P g)) → IsOpen {f | P f} := by
    intro P m hP
    refine isOpen_pi_iff.mpr fun f hf ↦ ?_
    refine ⟨Finset.range (m + 1), fun i ↦ {f i}, fun _ _ ↦ ⟨isOpen_discrete _, rfl⟩, fun g hg ↦ ?_⟩
    exact (hP f g fun i hi ↦
      (Set.mem_singleton_iff.mp (Set.mem_pi.mp hg i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))).symm).mp hf
  have hsum_congr : ∀ {f g : ℕ → Bool} {m : ℕ}, (∀ i ≤ m, f i = g i) →
      sumRep (toSet f) m = sumRep (toSet g) m := by
    intro f g m hfg
    rw [← card_repPairs, ← card_repPairs]
    congr 1
    ext p
    simp only [mem_repPairs, toSet, Set.mem_ofPred_eq]
    by_cases hs : p.1 + p.2 = m
    · rw [hfg p.1 (by omega), hfg p.2 (by omega)]
    · simp [hs]
  have hcnt_congr : ∀ {f g : ℕ → Bool} {m : ℕ}, (∀ i ≤ m, f i = g i) →
      (toSet f ∩ Icc 1 m).ncard = (toSet g ∩ Icc 1 m).ncard := by
    intro f g m hfg
    congr 1
    ext i
    simp only [Set.mem_inter_iff, Set.mem_Icc, toSet, Set.mem_ofPred_eq]
    by_cases hi : i ≤ m
    · rw [hfg i hi]
    · simp [hi]
  let K : Set (ℕ → Bool) := {f | ∀ n, sumRep (toSet f) n ≤ k}
  have hK : IsCompact K := by
    apply IsClosed.isCompact
    have hKe : K = ⋂ n : ℕ, {f | sumRep (toSet f) n ≤ k} := by ext f; simp [K]
    rw [hKe]
    refine isClosed_iInter fun n ↦ isOpen_compl_iff.mp ?_
    exact hopen_prefix n fun f g hfg ↦ by
      change ¬ sumRep (toSet f) n ≤ k ↔ ¬ sumRep (toSet g) n ≤ k
      rw [hsum_congr hfg]
  let V : {n : ℕ // L ≤ n} → Set (ℕ → Bool) := fun n ↦
    {f | (k : ℝ) ^ 2 * ((toSet f ∩ Icc 1 n.val).ncard : ℝ) < √(n.val : ℝ)}
  have hV : ∀ n, IsOpen (V n) := fun n ↦ hopen_prefix n.val fun f g hfg ↦ by
    rw [hcnt_congr hfg]
  have hcover : K ⊆ ⋃ n, V n := by
    intro f hf
    by_contra hnone
    have hall : ∀ n, L ≤ n → √(n : ℝ) ≤ (k : ℝ) ^ 2 * ((toSet f ∩ Icc 1 n).ncard : ℝ) := by
      intro n hn
      by_contra hlt
      exact hnone (Set.mem_iUnion.mpr ⟨⟨n, hn⟩, lt_of_not_ge hlt⟩)
    have htop := h1 (toSet f) (Asymptotics.IsBigO.of_bound ((k : ℝ) ^ 2) (by
      filter_upwards [eventually_ge_atTop L] with n hn
      simpa only [div_one, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast]
        using hall n hn))
    have hle : limsup (fun n ↦ (sumRep (toSet f) n : ℕ∞)) atTop ≤ (k : ℕ∞) :=
      limsup_le_of_le (h := Eventually.of_forall fun n ↦ by exact_mod_cast hf n)
    rw [htop] at hle
    exact (ENat.natCast_lt_top k).not_ge hle
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV hcover
  refine ⟨s.sup Subtype.val, fun A hA ↦ ?_⟩
  let f : ℕ → Bool := fun i ↦ decide (i ∈ A)
  have hfA : toSet f = A := by ext i; exact decide_eq_true_iff
  have hfK : f ∈ K := fun n ↦ by simpa only [hfA] using hA n
  obtain ⟨n, hn, hfail⟩ := Set.mem_iUnion₂.mp (hs hfK)
  refine ⟨n.val, n.property, Finset.le_sup (f := Subtype.val) hn, ?_⟩
  simpa only [V, Set.mem_ofPred_eq, hfA] using hfail

/-- `Erdos40For (fun _ ↦ 1)` implies the existence of a diverging denominator `g`. -/
theorem weaker_of_constant_one (h1 : Erdos40.Erdos40For (fun _ ↦ 1)) :
    ∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40.Erdos40For g := by
  classical
  choose U hU using fun j : ℕ ↦ exists_uniform_drop_window h1 (j + 1) j
  let ep (j : ℕ) : ℕ := max j (U j)
  have hreach (n : ℕ) : ∃ j, n ≤ ep j := ⟨n, le_max_left _ _⟩
  let idx (n : ℕ) : ℕ := Nat.find (hreach n)
  let g (n : ℕ) : ℝ := ((idx n + 1 : ℕ) : ℝ)
  have hgpos (n : ℕ) : 0 < g n := by dsimp [g]; positivity
  refine ⟨g, ?_, ?_⟩
  · refine tendsto_atTop.mpr fun x ↦ ?_
    obtain ⟨j, hj⟩ := exists_nat_ge x
    filter_upwards [eventually_ge_atTop ((Finset.range j).sup ep + 1)] with n hn
    have hjle : j ≤ idx n := by
      by_contra hlt
      have h1' : n ≤ ep (idx n) := Nat.find_spec (hreach n)
      have h2' : ep (idx n) ≤ (Finset.range j).sup ep :=
        Finset.le_sup (Finset.mem_range.mpr (lt_of_not_ge hlt))
      omega
    exact hj.trans (by dsimp [g]; exact_mod_cast (show j ≤ idx n + 1 by omega))
  · intro A hbig
    by_contra hne
    obtain ⟨k, hk⟩ := exists_global_cap_of_limsup_ne_top hne
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hbig
    obtain ⟨L, hL⟩ := eventually_atTop.mp hC
    obtain ⟨c, hc⟩ := exists_nat_ge C
    let j := max k (max c L)
    obtain ⟨n, hjn, hnU, hsmall⟩ := hU j A (fun m ↦ (hk m).trans (by omega))
    have hidx : idx n ≤ j := Nat.find_min' (hreach n) (hnU.trans (le_max_right _ _))
    have hgj : g n ≤ ((j + 1 : ℕ) : ℝ) := by dsimp [g]; exact_mod_cast Nat.succ_le_succ hidx
    have hcj : C ≤ ((j + 1 : ℕ) : ℝ) :=
      hc.trans (by exact_mod_cast (show c ≤ j + 1 by omega))
    have hbn := hL n (by omega)
    rw [Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (hgpos n).le),
      Real.norm_natCast] at hbn
    have hcoeff : C * g n ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
      rw [pow_two]
      exact (mul_le_mul_of_nonneg_right hcj (hgpos n).le).trans
        (mul_le_mul_of_nonneg_left hgj (Nat.cast_nonneg _))
    have hsq : √(n : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 2 * ((A ∩ Icc 1 n).ncard : ℝ) := by
      calc √(n : ℝ) ≤ (C * ((A ∩ Icc 1 n).ncard : ℝ)) * g n := (div_le_iff₀ (hgpos n)).mp hbn
        _ = (C * g n) * ((A ∩ Icc 1 n).ncard : ℝ) := by ring
        _ ≤ ((j + 1 : ℕ) : ℝ) ^ 2 * ((A ∩ Icc 1 n).ncard : ℝ) :=
            mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)
    exact hsmall.not_ge hsq

/-- Ordered pairs in `S ×ˢ S` with positive difference `d`. -/
def diffPairs (S : Finset ℕ) (d : ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 = d)

lemma mem_diffPairs {S : Finset ℕ} {d : ℕ} {p : ℕ × ℕ} :
    p ∈ diffPairs S d ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ p.2 < p.1 ∧ p.1 - p.2 = d := by
  simp only [diffPairs, Finset.mem_filter, Finset.mem_product]
  tauto

lemma sum_card_diffPairs_eq {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Finset.Icc 1 N) :
    ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card =
      ((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card := by
  classical
  rw [← Finset.card_biUnion]
  · congr 1
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Ico, diffPairs, Finset.mem_filter,
      Finset.mem_product]
    constructor
    · rintro ⟨_, _, hp, hlt, _⟩
      exact ⟨hp, hlt⟩
    · rintro ⟨⟨hp1, hp2⟩, hlt⟩
      have h1 := Finset.mem_Icc.mp (hS hp1)
      have h2 := Finset.mem_Icc.mp (hS hp2)
      exact ⟨p.1 - p.2, ⟨by omega, by omega⟩, ⟨hp1, hp2⟩, hlt, rfl⟩
  · intro d₁ _ d₂ _ hne
    change Disjoint (diffPairs S d₁) (diffPairs S d₂)
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [diffPairs, Finset.mem_filter] at hp1 hp2
    exact hne (hp1.2.2.symm.trans hp2.2.2)

lemma sum_card_repPairs_eq {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Finset.Icc 1 N) :
    ∑ s ∈ Finset.Icc 2 (2 * N), (repPairs (S : Set ℕ) s).card = S.card ^ 2 := by
  classical
  rw [← Finset.card_biUnion]
  · rw [pow_two, ← Finset.card_product]
    congr 1
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Icc, mem_repPairs, Finset.mem_coe,
      Finset.mem_product]
    constructor
    · rintro ⟨_, _, _, h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have ha := Finset.mem_Icc.mp (hS h1)
      have hb := Finset.mem_Icc.mp (hS h2)
      exact ⟨p.1 + p.2, ⟨by omega, by omega⟩, rfl, h1, h2⟩
  · intro s₁ _ s₂ _ hne
    change Disjoint (repPairs (S : Set ℕ) s₁) (repPairs (S : Set ℕ) s₂)
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact hne ((mem_repPairs.mp hp1).1.symm.trans (mem_repPairs.mp hp2).1)

/-- Exact additive energy identity on `S ⊆ [1, N]`:
`∑ s, r_S(s)^2 = |S|^2 + 2 * ∑ d, δ_S(d)^2`. -/
lemma additive_energy_eq_sq_add_two_mul_diff_sq {S : Finset ℕ} {N : ℕ}
    (hS : S ⊆ Finset.Icc 1 N) :
    ∑ s ∈ Finset.Icc 2 (2 * N), (repPairs (S : Set ℕ) s).card ^ 2 =
      S.card ^ 2 + 2 * ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card ^ 2 := by
  classical
  let Q := ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter (fun q ↦ q.1.1 + q.1.2 = q.2.1 + q.2.2)
  have hQ_sum : Q.card = ∑ s ∈ Finset.Icc 2 (2 * N), (repPairs (S : Set ℕ) s).card ^ 2 := by
    have hcard : ∀ s ∈ Finset.Icc 2 (2 * N),
        (repPairs (S : Set ℕ) s ×ˢ repPairs (S : Set ℕ) s).card =
          (repPairs (S : Set ℕ) s).card ^ 2 := by
      intro s _
      rw [Finset.card_product, pow_two]
    rw [← Finset.sum_congr rfl hcard, ← Finset.card_biUnion]
    · congr 1
      ext q
      simp only [Q, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_Icc,
        mem_repPairs, Finset.mem_coe]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hsum⟩
        have hb1 := Finset.mem_Icc.mp (hS h1)
        have hb2 := Finset.mem_Icc.mp (hS h2)
        exact ⟨q.1.1 + q.1.2, ⟨by omega, by omega⟩, ⟨rfl, h1, h2⟩, ⟨hsum.symm, h3, h4⟩⟩
      · rintro ⟨s, _, ⟨hs1, h1, h2⟩, ⟨hs2, h3, h4⟩⟩
        exact ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hs1.trans hs2.symm⟩
    · intro s₁ _ s₂ _ hne
      change Disjoint (repPairs (S : Set ℕ) s₁ ×ˢ repPairs (S : Set ℕ) s₁)
        (repPairs (S : Set ℕ) s₂ ×ˢ repPairs (S : Set ℕ) s₂)
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      simp only [Finset.mem_product, mem_repPairs] at hq1 hq2
      exact hne (hq1.1.1.symm.trans hq2.1.1)
  let Qeq := Q.filter (fun q ↦ q.1.1 = q.2.1)
  let Qgt := Q.filter (fun q ↦ q.2.1 < q.1.1)
  let Qlt := Q.filter (fun q ↦ q.1.1 < q.2.1)
  have hQeq : Qeq.card = S.card ^ 2 := by
    rw [pow_two, ← Finset.card_product]
    refine Finset.card_nbij' (fun q ↦ q.1) (fun p ↦ (p, p)) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Qeq, Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact hq.1.1.1
    · intro p hp
      simp only [Qeq, Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨⟨hp, hp⟩, trivial⟩, trivial⟩
    · intro q hq
      simp only [Qeq, Q, Finset.mem_coe, Finset.mem_filter] at hq
      rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      simp only at hq
      have hac : a = c := hq.2
      have hbd : b = d := by omega
      subst hac; subst hbd; rfl
    · intro p _; rfl
  have hQlt_eq : Qlt.card = Qgt.card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Qlt, Qgt, Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Prod.fst_swap, Prod.snd_swap] at hq ⊢
      exact ⟨⟨⟨hq.1.1.2, hq.1.1.1⟩, hq.1.2.symm⟩, hq.2⟩
    · intro q hq
      simp only [Qlt, Qgt, Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Prod.fst_swap, Prod.snd_swap] at hq ⊢
      exact ⟨⟨⟨hq.1.1.2, hq.1.1.1⟩, hq.1.2.symm⟩, hq.2⟩
    · intro q _; exact Prod.swap_swap q
    · intro q _; exact Prod.swap_swap q
  have hQgt : Qgt.card = ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card ^ 2 := by
    let D2 := (Finset.Ico 1 N).biUnion (fun d ↦ diffPairs S d ×ˢ diffPairs S d)
    have hD2_card : D2.card = ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card ^ 2 := by
      have hcard : ∀ d ∈ Finset.Ico 1 N,
          (diffPairs S d ×ˢ diffPairs S d).card = (diffPairs S d).card ^ 2 := by
        intro d _
        rw [Finset.card_product, pow_two]
      rw [← Finset.sum_congr rfl hcard, Finset.card_biUnion]
      intro d₁ _ d₂ _ hne
      change Disjoint (diffPairs S d₁ ×ˢ diffPairs S d₁) (diffPairs S d₂ ×ˢ diffPairs S d₂)
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      simp only [Finset.mem_product, mem_diffPairs] at hq1 hq2
      exact hne (hq1.1.2.2.2.symm.trans hq2.1.2.2.2)
    rw [← hD2_card]
    refine Finset.card_nbij'
      (fun q ↦ ((q.1.1, q.2.1), (q.2.2, q.1.2)))
      (fun q ↦ ((q.1.1, q.2.2), (q.1.2, q.2.1))) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Qgt, Q, D2, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_Ico, mem_diffPairs] at hq ⊢
      rcases hq with ⟨⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩, hsum⟩, hlt⟩
      have hba := Finset.mem_Icc.mp (hS ha)
      have hbc := Finset.mem_Icc.mp (hS hc)
      refine ⟨q.1.1 - q.2.1, ⟨by omega, by omega⟩,
        ⟨ha, hc, hlt, rfl⟩, ⟨hd, hb, by omega, by omega⟩⟩
    · intro q hq
      simp only [Qgt, Q, D2, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_Ico, mem_diffPairs] at hq ⊢
      rcases hq with ⟨d, _, ⟨ha, hc, hlt1, hd1⟩, ⟨hd, hb, hlt2, hd2⟩⟩
      exact ⟨⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩, by omega⟩, hlt1⟩
    · intro q _; rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
    · intro q _; rcases q with ⟨⟨a, c⟩, ⟨d, b⟩⟩; rfl
  have hQ_part : Q.card = Qeq.card + Qgt.card + Qlt.card := by
    have hunion : Q = (Qeq ∪ Qgt) ∪ Qlt := by
      ext q
      simp only [Qeq, Qgt, Qlt, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hq
        rcases lt_trichotomy q.1.1 q.2.1 with h | h | h
        · exact Or.inr ⟨hq, h⟩
        · exact Or.inl (Or.inl ⟨hq, h⟩)
        · exact Or.inl (Or.inr ⟨hq, h⟩)
      · rintro ((⟨hq, _⟩ | ⟨hq, _⟩) | ⟨hq, _⟩) <;> exact hq
    have hd1 : Disjoint Qeq Qgt := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      simp only [Qeq, Qgt, Finset.mem_filter] at h1 h2
      omega
    have hd2 : Disjoint (Qeq ∪ Qgt) Qlt := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      simp only [Qeq, Qgt, Qlt, Finset.mem_union, Finset.mem_filter] at h1 h2
      rcases h1 with h1 | h1 <;> omega
    conv_lhs => rw [hunion]
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  rw [← hQ_sum, hQ_part, hQeq, hQlt_eq, hQgt]
  omega

/-- Finite prefix `A ∩ [1, N]` as a `Finset`. -/
noncomputable def prefixSet (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  by classical exact (Finset.Icc 1 N).filter (· ∈ A)

lemma mem_prefixSet {A : Set ℕ} {N x : ℕ} :
    x ∈ prefixSet A N ↔ 1 ≤ x ∧ x ≤ N ∧ x ∈ A := by
  classical
  simp only [prefixSet, Finset.mem_filter, Finset.mem_Icc]
  tauto

lemma prefixSet_subset_Icc (A : Set ℕ) (N : ℕ) : prefixSet A N ⊆ Finset.Icc 1 N := by
  classical
  exact Finset.filter_subset _ _

lemma card_prefixSet (A : Set ℕ) (N : ℕ) :
    (prefixSet A N).card = (A ∩ Icc 1 N).ncard := by
  classical
  have heq : (prefixSet A N : Set ℕ) = A ∩ Icc 1 N := by
    ext x
    simp only [Finset.mem_coe, mem_prefixSet, Set.mem_inter_iff, Set.mem_Icc]
    tauto
  rw [← Set.ncard_coe_finset, heq]

/-- Additive energy upper bound for sets with `sumRep A n ≤ k`:
`|S|^2 + 2 * ∑ d, δ_S(d)^2 ≤ k * |S|^2`. -/
lemma cap_diff_sq_sum_le {A : Set ℕ} {k : ℕ} (hcap : ∀ n, sumRep A n ≤ k) (N : ℕ) :
    (prefixSet A N).card ^ 2 +
      2 * ∑ d ∈ Finset.Ico 1 N, (diffPairs (prefixSet A N) d).card ^ 2 ≤
      k * (prefixSet A N).card ^ 2 := by
  classical
  let S := prefixSet A N
  have hS : S ⊆ Finset.Icc 1 N := prefixSet_subset_Icc A N
  change S.card ^ 2 + 2 * ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card ^ 2 ≤ k * S.card ^ 2
  rw [← additive_energy_eq_sq_add_two_mul_diff_sq hS, ← sum_card_repPairs_eq hS, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  have hle : (repPairs (S : Set ℕ) s).card ≤ k := by
    have hsub : repPairs (S : Set ℕ) s ⊆ repPairs A s := by
      intro p hp
      obtain ⟨hs, h1, h2⟩ := mem_repPairs.mp hp
      simp only [S, Finset.mem_coe, mem_prefixSet] at h1 h2
      exact mem_repPairs.mpr ⟨hs, h1.2.2, h2.2.2⟩
    exact (Finset.card_le_card hsub).trans ((card_repPairs A s).symm ▸ hcap s)
  rw [pow_two]
  exact Nat.mul_le_mul_right _ hle

/-- Sharp finite prefix bound from additive energy: for `1 ≤ k` and `sumRep A n ≤ k`,
`(|A ∩ [1, N]| - 1)^2 ≤ 2 * (k - 1) * (N - 1)`. -/
theorem cap_prefix_sq_le_sharp {A : Set ℕ} {k : ℕ} (hk : 1 ≤ k)
    (hcap : ∀ n, sumRep A n ≤ k) (N : ℕ) :
    ((A ∩ Icc 1 N).ncard - 1) ^ 2 ≤ 2 * (k - 1) * (N - 1) := by
  classical
  let S := prefixSet A N
  rw [← card_prefixSet A N]
  change (S.card - 1) ^ 2 ≤ 2 * (k - 1) * (N - 1)
  by_cases hs1 : S.card ≤ 1
  · have : S.card - 1 = 0 := by omega
    rw [this]
    simp
  · have hspos : 0 < S.card := by omega
    have hS : S ⊆ Finset.Icc 1 N := prefixSet_subset_Icc A N
    let D := ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card
    have hsq : S.card * S.card = 2 * D + S.card := by
      dsimp only [D]
      rw [sum_card_diffPairs_eq hS]
      exact card_sq_eq_two_mul_lt_add_self S
    have hcs : D ^ 2 ≤ (N - 1) * ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card ^ 2 := by
      have h1 := sq_sum_le_card_mul_sum_sq_nat (Finset.Ico 1 N) (fun d ↦ (diffPairs S d).card)
      simpa only [Nat.card_Ico] using h1
    have henergy : 2 * ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card ^ 2 ≤ (k - 1) * S.card ^ 2 := by
      have h : S.card ^ 2 + 2 * ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card ^ 2 ≤ k * S.card ^ 2 :=
        cap_diff_sq_sum_le hcap N
      have hk1 : k * S.card ^ 2 = S.card ^ 2 + (k - 1) * S.card ^ 2 := by
        cases k with
        | zero => omega
        | succ m =>
          simp only [Nat.add_sub_cancel, Nat.succ_mul]
          omega
      omega
    have h2D : 2 * D = S.card * (S.card - 1) := by
      have hsub : S.card * (S.card - 1) + S.card = S.card * S.card := by
        cases h : S.card with
        | zero => omega
        | succ m => simp [Nat.mul_succ]
      omega
    have hmul : S.card ^ 2 * (S.card - 1) ^ 2 ≤ S.card ^ 2 * (2 * (k - 1) * (N - 1)) := by
      calc S.card ^ 2 * (S.card - 1) ^ 2
          = (S.card * (S.card - 1)) ^ 2 := by ring
        _ = (2 * D) ^ 2 := by rw [h2D]
        _ = 4 * D ^ 2 := by ring
        _ ≤ 4 * ((N - 1) * ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card ^ 2) :=
            Nat.mul_le_mul_left 4 hcs
        _ = 2 * (N - 1) * (2 * ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card ^ 2) := by ring
        _ ≤ 2 * (N - 1) * ((k - 1) * S.card ^ 2) := Nat.mul_le_mul_left _ henergy
        _ = S.card ^ 2 * (2 * (k - 1) * (N - 1)) := by ring
    exact Nat.le_of_mul_le_mul_left hmul (pow_pos hspos 2)

/-- General finite prefix upper bound for sets with `sumRep A n ≤ k`:
`|A ∩ [1, N]|^2 ≤ 2 * k * N`. -/
lemma cap_prefix_sq_le {A : Set ℕ} {k : ℕ} (hcap : ∀ n, sumRep A n ≤ k) (N : ℕ) :
    ((A ∩ Icc 1 N).ncard) ^ 2 ≤ 2 * k * N := by
  classical
  let S := (Finset.Icc 1 N).filter (· ∈ A)
  have hScard : S.card = (A ∩ Icc 1 N).ncard := by
    have heq : (S : Set ℕ) = A ∩ Icc 1 N := by
      ext x
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
        Set.mem_Icc]
      tauto
    rw [← Set.ncard_coe_finset, heq]
  have hS : S ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  rw [← hScard, ← sum_card_repPairs_eq hS]
  calc ∑ s ∈ Finset.Icc 2 (2 * N), (repPairs (S : Set ℕ) s).card
      ≤ ∑ _s ∈ Finset.Icc 2 (2 * N), k := by
        refine Finset.sum_le_sum fun s _ ↦ ?_
        have hsub : repPairs (S : Set ℕ) s ⊆ repPairs A s := by
          intro p hp
          obtain ⟨hs, h1, h2⟩ := mem_repPairs.mp hp
          simp only [S, Finset.mem_coe, Finset.mem_filter] at h1 h2
          exact mem_repPairs.mpr ⟨hs, h1.2, h2.2⟩
        exact (Finset.card_le_card hsub).trans ((card_repPairs A s).symm ▸ hcap s)
    _ = (Finset.Icc 2 (2 * N)).card * k := by simp
    _ ≤ (2 * N) * k := by
        apply Nat.mul_le_mul_right
        simp only [Nat.card_Icc]
        omega
    _ = 2 * k * N := by ring

/-- Any set satisfying both a quadratic prefix upper bound `|A ∩ [1, N]|^2 ≤ B * N` and
square-root lower density `√N =O |A ∩ [1, N]|` has superlinear close-pair count:
for every `M`, there exist `P > 0` and `N` with more than `M * P` pairs `(a, b)` in
`A ∩ [1, N]` satisfying `0 < a - b < P`. -/
theorem close_pairs_unbounded_of_quad_prefix {A : Set ℕ} {B : ℕ} (hB : 1 ≤ B)
    (hquad : ∀ N, ((A ∩ Icc 1 N).ncard) ^ 2 ≤ B * N)
    (hdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ)))
    (M : ℕ) :
    ∃ P : ℕ, 0 < P ∧ ∃ N : ℕ,
      M * P < ((prefixSet A N ×ˢ prefixSet A N).filter
        (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)).card := by
  classical
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hdense
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hc
  obtain ⟨C₀, hC₀⟩ := exists_nat_ge (max c 1)
  let C := max C₀ 1
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := by omega
  have hcC : c ≤ (C : ℝ) := (le_max_left c 1).trans (hC₀.trans (by exact_mod_cast le_max_left C₀ 1))
  have hlower : ∀ N, N₀ ≤ N → N ≤ C ^ 2 * ((A ∩ Icc 1 N).ncard) ^ 2 := by
    intro N hN
    have h1 := hN₀ N hN
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast] at h1
    have h2 : √(N : ℝ) ≤ (C : ℝ) * ((A ∩ Icc 1 N).ncard : ℝ) :=
      h1.trans (mul_le_mul_of_nonneg_right hcC (Nat.cast_nonneg _))
    have h3 : (N : ℝ) ≤ ((C : ℝ) * ((A ∩ Icc 1 N).ncard : ℝ)) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
      rwa [Real.sq_sqrt (Nat.cast_nonneg _)] at this
    have h4 : (N : ℝ) ≤ ((C ^ 2 * ((A ∩ Icc 1 N).ncard) ^ 2 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h4
  let r := 8 * B * C ^ 2
  have hr_pos : 0 < r := by positivity
  let K := 32 * C ^ 2 * M + 1
  let P := max (max N₀ 1) (64 * C ^ 2 * r ^ K)
  have hP1 : 1 ≤ P := (le_max_right N₀ 1).trans (le_max_left _ _)
  have hPpos : 0 < P := by omega
  have hPN0 : N₀ ≤ P := (le_max_left N₀ 1).trans (le_max_left _ _)
  have hPbig : 64 * C ^ 2 * r ^ K ≤ P := le_max_right _ _
  let T : ℕ → Finset ℕ := fun k ↦ (Finset.Icc (P * r ^ k + 1) (P * r ^ (k + 1))).filter (· ∈ A)
  let E : ℕ → Finset (ℕ × ℕ) := fun k ↦ (T k ×ˢ T k).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)
  have hblock : ∀ k ∈ Finset.range K, P ≤ 32 * C ^ 2 * (E k).card := by
    intro k hk
    have hkK : k < K := Finset.mem_range.mp hk
    let Mk := P * r ^ k
    let Nk := P * r ^ (k + 1)
    have hNk_eq : Nk = r * Mk := by
      dsimp [Nk, Mk]
      rw [pow_succ]
      ring
    have hMk1 : 1 ≤ Mk := by
      dsimp [Mk]
      exact Nat.mul_pos hPpos (pow_pos hr_pos k)
    have hNkN0 : N₀ ≤ Nk := by
      refine hPN0.trans ?_
      dsimp [Nk]
      exact Nat.le_mul_of_pos_right P (pow_pos hr_pos (k + 1))
    have haN : Nk ≤ C ^ 2 * ((A ∩ Icc 1 Nk).ncard) ^ 2 := hlower Nk hNkN0
    have haM : ((A ∩ Icc 1 Mk).ncard) ^ 2 ≤ B * Mk := hquad Mk
    have hsplit : (A ∩ Icc 1 Nk).ncard = (A ∩ Icc 1 Mk).ncard + (T k).card := by
      let SM := (Finset.Icc 1 Mk).filter (· ∈ A)
      let SN := (Finset.Icc 1 Nk).filter (· ∈ A)
      have hSM : SM.card = (A ∩ Icc 1 Mk).ncard := by
        have heq : (SM : Set ℕ) = A ∩ Icc 1 Mk := by
          ext x
          simp only [SM, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
            Set.mem_Icc]
          tauto
        rw [← Set.ncard_coe_finset, heq]
      have hSN : SN.card = (A ∩ Icc 1 Nk).ncard := by
        have heq : (SN : Set ℕ) = A ∩ Icc 1 Nk := by
          ext x
          simp only [SN, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
            Set.mem_Icc]
          tauto
        rw [← Set.ncard_coe_finset, heq]
      rw [← hSM, ← hSN, ← Finset.card_union_of_disjoint]
      · congr 1
        ext x
        simp only [SN, SM, T, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
        have hMkNk : Mk ≤ Nk := by
          rw [hNk_eq]
          exact Nat.le_mul_of_pos_left Mk hr_pos
        constructor
        · rintro ⟨⟨h1, h2⟩, hxA⟩
          by_cases hxM : x ≤ Mk
          · exact Or.inl ⟨⟨h1, hxM⟩, hxA⟩
          · exact Or.inr ⟨⟨by omega, h2⟩, hxA⟩
        · rintro (⟨⟨h1, h2⟩, hxA⟩ | ⟨⟨h1, h2⟩, hxA⟩) <;> exact ⟨⟨by omega, by omega⟩, hxA⟩
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [SM, T, Finset.mem_filter, Finset.mem_Icc] at hx1 hx2
        omega
    have hhalf : 2 * (A ∩ Icc 1 Mk).ncard < (A ∩ Icc 1 Nk).ncard := by
      have hlt : (2 * (A ∩ Icc 1 Mk).ncard) ^ 2 < ((A ∩ Icc 1 Nk).ncard) ^ 2 := by
        have hC2pos : 0 < C ^ 2 := pow_pos hCpos 2
        have hmul : C ^ 2 * (2 * (A ∩ Icc 1 Mk).ncard) ^ 2 < C ^ 2 * ((A ∩ Icc 1 Nk).ncard) ^ 2 := by
          have h4lt8 : 4 * B * C ^ 2 * Mk < 8 * B * C ^ 2 * Mk := by
            have hpos : 0 < B * C ^ 2 * Mk := by positivity
            nlinarith
          calc C ^ 2 * (2 * (A ∩ Icc 1 Mk).ncard) ^ 2
              = 4 * C ^ 2 * ((A ∩ Icc 1 Mk).ncard) ^ 2 := by ring
            _ ≤ 4 * C ^ 2 * (B * Mk) := Nat.mul_le_mul_left _ haM
            _ = 4 * B * C ^ 2 * Mk := by ring
            _ < 8 * B * C ^ 2 * Mk := h4lt8
            _ = Nk := hNk_eq.symm
            _ ≤ C ^ 2 * ((A ∩ Icc 1 Nk).ncard) ^ 2 := haN
        exact (Nat.mul_lt_mul_left hC2pos).mp hmul
      nlinarith
    have hTlb : Nk ≤ 4 * C ^ 2 * (T k).card ^ 2 := by
      have : (A ∩ Icc 1 Nk).ncard ≤ 2 * (T k).card := by omega
      calc Nk ≤ C ^ 2 * ((A ∩ Icc 1 Nk).ncard) ^ 2 := haN
        _ ≤ C ^ 2 * (2 * (T k).card) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 2)
        _ = 4 * C ^ 2 * (T k).card ^ 2 := by ring
    have hcs := bucket_close_pairs_bound (T k) hPpos (fun x hx ↦ by
      simp only [T, Finset.mem_filter, Finset.mem_Icc] at hx
      exact hx.1.2)
    have hdiv : Nk / P = r ^ (k + 1) := by
      dsimp [Nk]
      exact Nat.mul_div_right _ hPpos
    rw [hdiv] at hcs
    let Bk := r ^ (k + 1) + 1
    have hBk_le : Bk ≤ 2 * r ^ (k + 1) := by
      dsimp [Bk]
      have : 1 ≤ r ^ (k + 1) := Nat.one_le_pow _ _ hr_pos
      omega
    have h2Bk_le : 2 * Bk ≤ (T k).card := by
      have hrk : r ^ (k + 1) ≤ r ^ K := Nat.pow_le_pow_right hr_pos (by omega)
      have hsq_le : 4 * C ^ 2 * (2 * Bk) ^ 2 ≤ 4 * C ^ 2 * (T k).card ^ 2 := by
        calc 4 * C ^ 2 * (2 * Bk) ^ 2
            ≤ 4 * C ^ 2 * (4 * r ^ (k + 1)) ^ 2 :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
          _ = 64 * C ^ 2 * r ^ (k + 1) * r ^ (k + 1) := by ring
          _ ≤ 64 * C ^ 2 * r ^ K * r ^ (k + 1) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrk)
          _ ≤ P * r ^ (k + 1) := Nat.mul_le_mul_right _ hPbig
          _ ≤ 4 * C ^ 2 * (T k).card ^ 2 := hTlb
      have hC4pos : 0 < 4 * C ^ 2 := by positivity
      have := Nat.le_of_mul_le_mul_left hsq_le hC4pos
      nlinarith
    have hTsq_le : (T k).card ^ 2 ≤ 8 * r ^ (k + 1) * (E k).card := by
      have hcs' : (T k).card ^ 2 ≤ Bk * (2 * (E k).card + (T k).card) := hcs
      have h2 : 2 * (T k).card ^ 2 ≤ 4 * Bk * (E k).card + (2 * Bk) * (T k).card := by
        nlinarith
      have h3 : (2 * Bk) * (T k).card ≤ (T k).card ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_right _ h2Bk_le
      have h4 : (T k).card ^ 2 ≤ 4 * Bk * (E k).card := by omega
      calc (T k).card ^ 2 ≤ 4 * Bk * (E k).card := h4
        _ ≤ 4 * (2 * r ^ (k + 1)) * (E k).card :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hBk_le)
        _ = 8 * r ^ (k + 1) * (E k).card := by ring
    have hfinal : P * r ^ (k + 1) ≤ 32 * C ^ 2 * (E k).card * r ^ (k + 1) := by
      calc P * r ^ (k + 1) ≤ 4 * C ^ 2 * (T k).card ^ 2 := hTlb
        _ ≤ 4 * C ^ 2 * (8 * r ^ (k + 1) * (E k).card) := Nat.mul_le_mul_left _ hTsq_le
        _ = 32 * C ^ 2 * (E k).card * r ^ (k + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hfinal (pow_pos hr_pos (k + 1))
  have hsum_lb : K * P ≤ 32 * C ^ 2 * ∑ k ∈ Finset.range K, (E k).card := by
    calc K * P = ∑ _k ∈ Finset.range K, P := by simp
      _ ≤ ∑ k ∈ Finset.range K, 32 * C ^ 2 * (E k).card := Finset.sum_le_sum hblock
      _ = 32 * C ^ 2 * ∑ k ∈ Finset.range K, (E k).card := by rw [← Finset.mul_sum]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range K) : Set ℕ) E := by
    intro k₁ _ k₂ _ hne
    change Disjoint (E k₁) (E k₂)
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [E, T, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : P * r ^ (k₁ + 1) ≤ P * r ^ k₂ :=
        Nat.mul_le_mul_left P (Nat.pow_le_pow_right hr_pos hlt)
      omega
    · have : P * r ^ (k₂ + 1) ≤ P * r ^ k₁ :=
        Nat.mul_le_mul_left P (Nat.pow_le_pow_right hr_pos hgt)
      omega
  refine ⟨P, hPpos, P * r ^ K, ?_⟩
  let S := prefixSet A (P * r ^ K)
  let Eall := (S ×ˢ S).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)
  change M * P < Eall.card
  have hsub : (Finset.range K).biUnion E ⊆ Eall := by
    intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_range, E, T, Eall, S, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc, mem_prefixSet] at hp ⊢
    rcases hp with ⟨k, hk, ⟨⟨⟨h1a, h1b⟩, hp1A⟩, ⟨⟨h2a, h2b⟩, hp2A⟩⟩, hlt, hdiff⟩
    have hrk : P * r ^ (k + 1) ≤ P * r ^ K :=
      Nat.mul_le_mul_left P (Nat.pow_le_pow_right hr_pos (by omega))
    exact ⟨⟨⟨by omega, h1b.trans hrk, hp1A⟩, ⟨by omega, h2b.trans hrk, hp2A⟩⟩, hlt, hdiff⟩
  have hsum_le : ∑ k ∈ Finset.range K, (E k).card ≤ Eall.card := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card hsub
  have hlt_mul : 32 * C ^ 2 * (M * P) < 32 * C ^ 2 * Eall.card := by
    calc 32 * C ^ 2 * (M * P)
        < (32 * C ^ 2 * M + 1) * P := by nlinarith
      _ = K * P := rfl
      _ ≤ 32 * C ^ 2 * ∑ k ∈ Finset.range K, (E k).card := hsum_lb
      _ ≤ 32 * C ^ 2 * Eall.card := Nat.mul_le_mul_left _ hsum_le
  exact Nat.lt_of_mul_lt_mul_left hlt_mul

/-- Any bounded-representation set with `|A ∩ [1, N]| ≫ √N` has superlinear close-pair count. -/
theorem cap_close_pairs_unbounded {A : Set ℕ} {k : ℕ} (hcap : ∀ n, sumRep A n ≤ k)
    (hdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ)))
    (M : ℕ) :
    ∃ P : ℕ, 0 < P ∧ ∃ N : ℕ,
      M * P < ((prefixSet A N ×ˢ prefixSet A N).filter
        (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)).card :=
  close_pairs_unbounded_of_quad_prefix (B := max (2 * k) 1) (le_max_right _ _)
    (fun N ↦ (cap_prefix_sq_le hcap N).trans (Nat.mul_le_mul_right N (le_max_left _ _)))
    hdense M

/-- Any bounded-representation set with `|A ∩ [1, N]| ≫ √N` has unbounded positive difference
multiplicity `|A ∩ (A - d) ∩ [1, N]|`. -/
theorem cap_diff_mult_unbounded {A : Set ℕ} {k : ℕ} (hcap : ∀ n, sumRep A n ≤ k)
    (hdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ)))
    (M : ℕ) :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ, M < (({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard) := by
  classical
  obtain ⟨P, hP, N, hbig⟩ := cap_close_pairs_unbounded hcap hdense M
  let S := prefixSet A N
  let Eall := (S ×ˢ S).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)
  have hbig' : M * P < Eall.card := hbig
  have hE_eq : Eall.card = ∑ d ∈ Finset.Ico 1 P, (diffPairs S d).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Eall, Finset.mem_biUnion, Finset.mem_Ico, diffPairs, Finset.mem_filter,
        Finset.mem_product]
      constructor
      · rintro ⟨hp, hlt, hdiff⟩
        exact ⟨p.1 - p.2, ⟨by omega, hdiff⟩, hp, hlt, rfl⟩
      · rintro ⟨d, ⟨hd1, hd2⟩, hp, hlt, rfl⟩
        exact ⟨hp, hlt, hd2⟩
    · intro d₁ _ d₂ _ hne
      change Disjoint (diffPairs S d₁) (diffPairs S d₂)
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [diffPairs, Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.2.symm.trans hp2.2.2)
  have hdiff_le : ∀ d : ℕ, (diffPairs S d).card ≤ ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard := by
    intro d
    let F := (Finset.Icc 1 N).filter (fun x ↦ x ∈ A ∧ x + d ∈ A)
    have hF : F.card = ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard := by
      have heq : (F : Set ℕ) = {x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N := by
        ext x
        simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
          Set.mem_Icc, Set.mem_ofPred_eq]
        tauto
      rw [← Set.ncard_coe_finset, heq]
    rw [← hF]
    refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
    · intro p hp
      simp only [diffPairs, S, F, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        mem_prefixSet, Finset.mem_Icc] at hp ⊢
      rcases hp with ⟨⟨⟨_, _, hp1A⟩, ⟨h2lo, h2hi, hp2A⟩⟩, hlt, hdiff⟩
      refine ⟨⟨h2lo, h2hi⟩, hp2A, ?_⟩
      rwa [show p.2 + d = p.1 by omega]
    · intro p hp q hq heq
      simp only [diffPairs, Finset.mem_coe, Finset.mem_filter] at hp hq
      exact Prod.ext (by omega) heq
  by_contra hno
  push Not at hno
  have hle : Eall.card ≤ M * P := by
    rw [hE_eq]
    calc ∑ d ∈ Finset.Ico 1 P, (diffPairs S d).card
        ≤ ∑ _d ∈ Finset.Ico 1 P, M := Finset.sum_le_sum fun d hd ↦
          (hdiff_le d).trans (hno d (Finset.mem_Ico.mp hd).1 N)
      _ = (Finset.Ico 1 P).card * M := by simp
      _ ≤ P * M := by
          apply Nat.mul_le_mul_right
          simp only [Nat.card_Ico]
          omega
      _ = M * P := Nat.mul_comm P M
  omega

/-- Generalization of Erdos (1955) to all uniformly difference-bounded sets:
if every positive difference occurs at most `M` times in `A`, then `|A ∩ [1, N]|` cannot be `≫ √N`. -/
theorem diff_bounded_not_sqrt_dense {A : Set ℕ} {M : ℕ}
    (hM : ∀ d : ℕ, 0 < d → ∀ N : ℕ, ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard ≤ M) :
    ¬ ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) := by
  classical
  intro hdense
  have hdiff_le : ∀ (N d : ℕ), 0 < d →
      (diffPairs (prefixSet A N) d).card ≤ M := by
    intro N d hd
    let F := (Finset.Icc 1 N).filter (fun x ↦ x ∈ A ∧ x + d ∈ A)
    have hF : F.card = ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard := by
      have heq : (F : Set ℕ) = {x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N := by
        ext x
        simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
          Set.mem_Icc, Set.mem_ofPred_eq]
        tauto
      rw [← Set.ncard_coe_finset, heq]
    refine le_trans ?_ (hF ▸ hM d hd N)
    refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
    · intro p hp
      simp only [diffPairs, F, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        mem_prefixSet, Finset.mem_Icc] at hp ⊢
      rcases hp with ⟨⟨⟨_, _, hp1A⟩, ⟨h2lo, h2hi, hp2A⟩⟩, hlt, hdiff⟩
      refine ⟨⟨h2lo, h2hi⟩, hp2A, ?_⟩
      rwa [show p.2 + d = p.1 by omega]
    · intro p hp q hq heq
      simp only [diffPairs, Finset.mem_coe, Finset.mem_filter] at hp hq
      exact Prod.ext (by omega) heq
  have hquad : ∀ N, ((A ∩ Icc 1 N).ncard) ^ 2 ≤ (4 * M + 2) * N := by
    intro N
    let S := prefixSet A N
    rw [← card_prefixSet A N]
    change S.card ^ 2 ≤ (4 * M + 2) * N
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · have hS0 : S = ∅ := by
        ext x
        simp only [S, mem_prefixSet, Finset.notMem_empty, iff_false]
        omega
      simp [hS0]
    · have hS : S ⊆ Finset.Icc 1 N := prefixSet_subset_Icc A N
      have hDle : ((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card ≤ M * N := by
        rw [← sum_card_diffPairs_eq hS]
        calc ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card
            ≤ ∑ _d ∈ Finset.Ico 1 N, M := Finset.sum_le_sum fun d hd ↦
              hdiff_le N d (Finset.mem_Ico.mp hd).1
          _ = (Finset.Ico 1 N).card * M := by simp
          _ ≤ N * M := by
              apply Nat.mul_le_mul_right
              simp only [Nat.card_Ico]
              omega
          _ = M * N := Nat.mul_comm N M
      have hsq : S.card * S.card = 2 * ((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card + S.card :=
        card_sq_eq_two_mul_lt_add_self S
      have hZ : (S.card : ℤ) ^ 2 ≤ 4 * (M : ℤ) * (N : ℤ) + 1 := by
        have hsqZ : (S.card : ℤ) * (S.card : ℤ) =
            2 * (((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card : ℤ) + (S.card : ℤ) := by
          exact_mod_cast hsq
        have hDZ : (((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card : ℤ) ≤ (M : ℤ) * (N : ℤ) := by
          exact_mod_cast hDle
        nlinarith [sq_nonneg ((S.card : ℤ) - 1)]
      have hnat : S.card ^ 2 ≤ 4 * M * N + 1 := by exact_mod_cast hZ
      nlinarith
  obtain ⟨P, hP, N, hbig⟩ :=
    close_pairs_unbounded_of_quad_prefix (B := 4 * M + 2) (by omega) hquad hdense M
  let S := prefixSet A N
  let Eall := (S ×ˢ S).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)
  have hbig' : M * P < Eall.card := hbig
  have hE_eq : Eall.card = ∑ d ∈ Finset.Ico 1 P, (diffPairs S d).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Eall, Finset.mem_biUnion, Finset.mem_Ico, diffPairs, Finset.mem_filter,
        Finset.mem_product]
      constructor
      · rintro ⟨hp, hlt, hdiff⟩
        exact ⟨p.1 - p.2, ⟨by omega, hdiff⟩, hp, hlt, rfl⟩
      · rintro ⟨d, ⟨hd1, hd2⟩, hp, hlt, rfl⟩
        exact ⟨hp, hlt, hd2⟩
    · intro d₁ _ d₂ _ hne
      change Disjoint (diffPairs S d₁) (diffPairs S d₂)
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [diffPairs, Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.2.symm.trans hp2.2.2)
  have hle : Eall.card ≤ M * P := by
    rw [hE_eq]
    calc ∑ d ∈ Finset.Ico 1 P, (diffPairs S d).card
        ≤ ∑ _d ∈ Finset.Ico 1 P, M := Finset.sum_le_sum fun d hd ↦
          hdiff_le N d (Finset.mem_Ico.mp hd).1
      _ = (Finset.Ico 1 P).card * M := by simp
      _ ≤ P * M := by
          apply Nat.mul_le_mul_right
          simp only [Nat.card_Ico]
          omega
      _ = M * P := Nat.mul_comm P M
  omega

/-- Saturation bound for `B_2[2]` sets (`sumRep A n ≤ 4`): across blocks separated by `P`,
the inner product of positive shift multiplicities for `1 ≤ d < P` is bounded by `N`. -/
theorem cap_four_cross_shift_mul_sum_le {A : Set ℕ} (h4 : ∀ n, sumRep A n ≤ 4)
    (M P N : ℕ) :
    ∑ d ∈ Finset.Ico 1 P,
      (({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 M).ncard) *
      (({x | x ∈ A ∧ x + d ∈ A} ∩ Icc (M + P + 1) N).ncard) ≤ N := by
  classical
  let F : ℕ → Finset ℕ := fun d ↦ (Finset.Icc 1 M).filter (fun x ↦ x ∈ A ∧ x + d ∈ A)
  let G : ℕ → Finset ℕ := fun d ↦ (Finset.Icc (M + P + 1) N).filter (fun y ↦ y ∈ A ∧ y + d ∈ A)
  have hF : ∀ d, (F d).card = ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 M).ncard := by
    intro d
    have heq : (F d : Set ℕ) = {x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 M := by
      ext x
      simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
        Set.mem_Icc, Set.mem_ofPred_eq]
      tauto
    rw [← Set.ncard_coe_finset, heq]
  have hG : ∀ d, (G d).card = ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc (M + P + 1) N).ncard := by
    intro d
    have heq : (G d : Set ℕ) = {x | x ∈ A ∧ x + d ∈ A} ∩ Icc (M + P + 1) N := by
      ext y
      simp only [G, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
        Set.mem_Icc, Set.mem_ofPred_eq]
      tauto
    rw [← Set.ncard_coe_finset, heq]
  let slice : ℕ → Finset (ℕ × ℕ × ℕ) := fun d ↦
    (F d ×ˢ G d).image (fun p ↦ (d, p.1, p.2))
  let T : Finset (ℕ × ℕ × ℕ) := (Finset.Ico 1 P).biUnion slice
  have hTcard : T.card = ∑ d ∈ Finset.Ico 1 P,
      (({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 M).ncard) *
      (({x | x ∈ A ∧ x + d ∈ A} ∩ Icc (M + P + 1) N).ncard) := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun d _ ↦ ?_
      have hinj : Function.Injective (fun p : ℕ × ℕ ↦ (d, p.1, p.2)) := by
        intro p₁ p₂ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 h.2.2
      simp only [slice, Finset.card_image_of_injective _ hinj, Finset.card_product, hF, hG]
    · intro d₁ _ d₂ _ hne
      change Disjoint (slice d₁) (slice d₂)
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [slice, Finset.mem_image] at ht1 ht2
      rcases ht1 with ⟨_, _, rfl⟩
      rcases ht2 with ⟨_, _, heq⟩
      exact hne (congrArg Prod.fst heq).symm
  rw [← hTcard]
  have hico : (Finset.Ico (M + P + 1) (M + P + 1 + N)).card = N := by
    simp only [Nat.card_Ico]
    omega
  rw [← hico]
  refine Finset.card_le_card_of_injOn (fun t ↦ t.2.1 + t.2.2 + t.1) ?_ ?_
  · intro t ht
    simp only [T, slice, F, G, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_Ico,
      Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at ht ⊢
    rcases ht with ⟨d, ⟨hd1, hd2⟩, ⟨x, y⟩, ⟨⟨⟨hx1, hx2⟩, _⟩, ⟨⟨hy1, hy2⟩, _⟩⟩, rfl⟩
    dsimp only
    omega
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [T, slice, F, G, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_Ico,
      Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at ht₁ ht₂
    rcases ht₁ with ⟨d₁, ⟨hd1lo, hd1hi⟩, ⟨x₁, y₁⟩,
      ⟨⟨⟨hx1lo, hx1hi⟩, hx1A, hxd1A⟩, ⟨⟨hy1lo, hy1hi⟩, hy1A, hyd1A⟩⟩, rfl⟩
    rcases ht₂ with ⟨d₂, ⟨hd2lo, hd2hi⟩, ⟨x₂, y₂⟩,
      ⟨⟨⟨hx2lo, hx2hi⟩, hx2A, hxd2A⟩, ⟨⟨hy2lo, hy2hi⟩, hy2A, hyd2A⟩⟩, rfl⟩
    dsimp only at heq
    let s := x₁ + y₁ + d₁
    let R₁ : Finset (ℕ × ℕ) := {(x₁, y₁ + d₁), (y₁ + d₁, x₁), (x₁ + d₁, y₁), (y₁, x₁ + d₁)}
    let R₂ : Finset (ℕ × ℕ) := {(x₂, y₂ + d₂), (y₂ + d₂, x₂), (x₂ + d₂, y₂), (y₂, x₂ + d₂)}
    have hR₁_sub : R₁ ⊆ repPairs A s := by
      intro p hp
      simp only [R₁, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact mem_repPairs.mpr ⟨by dsimp [s]; omega, hx1A, hyd1A⟩
      · exact mem_repPairs.mpr ⟨by dsimp [s]; omega, hyd1A, hx1A⟩
      · exact mem_repPairs.mpr ⟨by dsimp [s]; omega, hxd1A, hy1A⟩
      · exact mem_repPairs.mpr ⟨by dsimp [s]; omega, hy1A, hxd1A⟩
    have hR₂_sub : R₂ ⊆ repPairs A s := by
      intro p hp
      simp only [R₂, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact mem_repPairs.mpr ⟨by dsimp [s]; omega, hx2A, hyd2A⟩
      · exact mem_repPairs.mpr ⟨by dsimp [s]; omega, hyd2A, hx2A⟩
      · exact mem_repPairs.mpr ⟨by dsimp [s]; omega, hxd2A, hy2A⟩
      · exact mem_repPairs.mpr ⟨by dsimp [s]; omega, hy2A, hxd2A⟩
    have hR₁_card : R₁.card = 4 := by
      dsimp only [R₁]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton, Prod.mk.injEq]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega
    have hR₂_card : R₂.card = 4 := by
      dsimp only [R₂]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton, Prod.mk.injEq]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega
    have hrep_le : (repPairs A s).card ≤ 4 := by
      rw [card_repPairs]
      exact h4 s
    have hR₁_eq : R₁ = repPairs A s := Finset.eq_of_subset_of_card_le hR₁_sub (by omega)
    have hR₂_eq : R₂ = repPairs A s := Finset.eq_of_subset_of_card_le hR₂_sub (by omega)
    have hR_eq : R₁ = R₂ := hR₁_eq.trans hR₂_eq.symm
    have hfst : R₁.image Prod.fst = R₂.image Prod.fst := congrArg (Finset.image Prod.fst) hR_eq
    have hmem12 : ∀ z, z ∈ R₁.image Prod.fst ↔ z ∈ R₂.image Prod.fst := fun z ↦ by rw [hfst]
    have hx1_in : x₁ ∈ R₂.image Prod.fst := (hmem12 x₁).mp (by simp [R₁])
    have hx2_in : x₂ ∈ R₁.image Prod.fst := (hmem12 x₂).mpr (by simp [R₂])
    have hxd1_in : x₁ + d₁ ∈ R₂.image Prod.fst := (hmem12 (x₁ + d₁)).mp (by simp [R₁])
    have hxd2_in : x₂ + d₂ ∈ R₁.image Prod.fst := (hmem12 (x₂ + d₂)).mpr (by simp [R₂])
    simp only [R₁, R₂, Finset.image_insert, Finset.image_singleton, Finset.mem_insert,
      Finset.mem_singleton] at hx1_in hx2_in hxd1_in hxd2_in
    have hx_eq : x₁ = x₂ := by omega
    have hd_eq : d₁ = d₂ := by omega
    have hy_eq : y₁ = y₂ := by omega
    exact Prod.ext hd_eq (Prod.ext hx_eq hy_eq)

/-- Any diverging denominator witnessing `Erdos40For g` implies `Erdos40For (fun _ ↦ 1)`. -/
theorem constant_one_of_weaker
    (h : ∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40.Erdos40For g) :
    Erdos40.Erdos40For (fun _ ↦ 1) := by
  obtain ⟨g, hg, h40⟩ := h
  intro A hA
  apply h40 A
  refine (Asymptotics.IsBigO.of_bound 1 ?_).trans hA
  filter_upwards [hg.eventually_ge_atTop 1] with N hN
  have hgn : 0 ≤ g N := le_trans zero_le_one hN
  rw [one_mul, Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hgn),
    Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) zero_le_one), div_one]
  exact div_le_self (Real.sqrt_nonneg _) hN

/-- Exact equivalence between the weaker Erdos 40 statement and `Erdos40For (fun _ ↦ 1)`. -/
theorem weaker_iff_constant_one :
    (∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40.Erdos40For g) ↔
      Erdos40.Erdos40For (fun _ ↦ 1) :=
  ⟨constant_one_of_weaker, weaker_of_constant_one⟩

/-- If `|X| ≥ 2` and shifting `X` by `d > 0` adds at most one element, then `d` is uniquely
determined as the gap between the two smallest elements of `X`. -/
lemma shift_eq_min_gap_of_card_union_le_add_one {X : Finset ℕ} (hX : 2 ≤ X.card)
    {d : ℕ} (hd : 0 < d) (hle : (X ∪ X.image (· + d)).card ≤ X.card + 1) :
    ∃ x0 x1 : ℕ, x0 ∈ X ∧ x1 ∈ X ∧ x0 < x1 ∧
      (∀ x ∈ X, x0 ≤ x) ∧ (∀ x ∈ X, x ≠ x0 → x1 ≤ x) ∧ d = x1 - x0 := by
  classical
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  let x0 := X.min' hXne
  let xmax := X.max' hXne
  have hx0_mem : x0 ∈ X := Finset.min'_mem X hXne
  have hxmax_mem : xmax ∈ X := Finset.max'_mem X hXne
  have hx0_lt_max : x0 < xmax := by
    by_contra hge
    have hsub : X ⊆ {x0} := by
      intro x hx
      have h1 : x0 ≤ x := Finset.min'_le X x hx
      have h2 : x ≤ xmax := Finset.le_max' X x hx
      simp only [Finset.mem_singleton]
      omega
    have hle1 := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hle1
    omega
  have hX'ne : (X.erase x0).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hx0_mem]
    omega)
  let x1 := (X.erase x0).min' hX'ne
  have hx1_mem' : x1 ∈ X.erase x0 := Finset.min'_mem (X.erase x0) hX'ne
  have hx1_mem : x1 ∈ X := Finset.mem_of_mem_erase hx1_mem'
  have hx1_ne : x1 ≠ x0 := Finset.ne_of_mem_erase hx1_mem'
  have hx0_lt_x1 : x0 < x1 := lt_of_le_of_ne (Finset.min'_le X x1 hx1_mem) hx1_ne.symm
  let Y := X.image (· + d)
  have hYcard : Y.card = X.card := Finset.card_image_of_injective X (fun _ _ h ↦ by omega)
  have hUY1 : (X ∪ Y).card = X.card + (Y \ X).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext z
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    · rw [Finset.disjoint_left]
      intro z hz1 hz2
      exact (Finset.mem_sdiff.mp hz2).2 hz1
  have hUY2 : (X ∪ Y).card = Y.card + (X \ Y).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext z
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    · rw [Finset.disjoint_left]
      intro z hz1 hz2
      exact (Finset.mem_sdiff.mp hz2).2 hz1
  have hle' : (X ∪ Y).card ≤ X.card + 1 := hle
  have hYX_le : (Y \ X).card ≤ 1 := by omega
  have hXY_le : (X \ Y).card ≤ 1 := by omega
  have hxmax_sdiff : xmax + d ∈ Y \ X := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hxmax_mem, fun hmem ↦ ?_⟩
    have := Finset.le_max' X (xmax + d) hmem
    omega
  have hx0d_mem : x0 + d ∈ X := by
    by_contra hnot
    have hx0d_sdiff : x0 + d ∈ Y \ X :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hx0_mem, hnot⟩
    have hsub : ({x0 + d, xmax + d} : Finset ℕ) ⊆ Y \ X := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx0d_sdiff
      · exact hxmax_sdiff
    have hcard2 : ({x0 + d, xmax + d} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      omega
    have := (Finset.card_le_card hsub).trans hYX_le
    omega
  have hx1_le : x1 ≤ x0 + d :=
    Finset.min'_le (X.erase x0) (x0 + d) (Finset.mem_erase.mpr ⟨by omega, hx0d_mem⟩)
  have hx0_sdiff : x0 ∈ X \ Y := by
    refine Finset.mem_sdiff.mpr ⟨hx0_mem, fun hmem ↦ ?_⟩
    obtain ⟨y, hy, hyd⟩ := Finset.mem_image.mp hmem
    have := Finset.min'_le X y hy
    omega
  have hx1_inY : x1 ∈ Y := by
    by_contra hnot
    have hx1_sdiff : x1 ∈ X \ Y := Finset.mem_sdiff.mpr ⟨hx1_mem, hnot⟩
    have hsub : ({x0, x1} : Finset ℕ) ⊆ X \ Y := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx0_sdiff
      · exact hx1_sdiff
    have hcard2 : ({x0, x1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      omega
    have := (Finset.card_le_card hsub).trans hXY_le
    omega
  obtain ⟨y, hy, hyd⟩ := Finset.mem_image.mp hx1_inY
  have hy_ge : x0 ≤ y := Finset.min'_le X y hy
  refine ⟨x0, x1, hx0_mem, hx1_mem, hx0_lt_x1, fun x hx ↦ Finset.min'_le X x hx,
    fun x hx hne ↦ Finset.min'_le (X.erase x0) x (Finset.mem_erase.mpr ⟨hne, hx⟩), by omega⟩

/-- For any finite set `X` with `|X| ≥ 2` and two distinct positive shifts `d₁ ≠ d₂`,
at least one shift adds at least two new elements to `X`. -/
lemma exists_shift_card_union_ge_add_two {X : Finset ℕ} (hX : 2 ≤ X.card)
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hne : d₁ ≠ d₂) :
    X.card + 2 ≤ (X ∪ X.image (· + d₁)).card ∨ X.card + 2 ≤ (X ∪ X.image (· + d₂)).card := by
  by_contra hno
  push Not at hno
  obtain ⟨x0, x1, hx0m, hx1m, hx01, hx0min, hx1min, hd1_eq⟩ :=
    shift_eq_min_gap_of_card_union_le_add_one hX hd₁ (by omega)
  obtain ⟨y0, y1, hy0m, hy1m, hy01, hy0min, hy1min, hd2_eq⟩ :=
    shift_eq_min_gap_of_card_union_le_add_one hX hd₂ (by omega)
  have h0 : x0 = y0 := le_antisymm (hx0min y0 hy0m) (hy0min x0 hx0m)
  subst h0
  have h1 : x1 = y1 := le_antisymm (hx1min y1 hy1m (by omega)) (hy1min x1 hx1m (by omega))
  omega

/-- First coordinates of `repPairs B n` have cardinality equal to `sumRep B n`. -/
lemma card_fst_repPairs (B : Set ℕ) (n : ℕ) :
    ((repPairs B n).image Prod.fst).card = sumRep B n := by
  classical
  rw [← card_repPairs B n]
  refine Finset.card_image_of_injOn fun p hp q hq heq ↦ ?_
  have hp' := (mem_repPairs.mp hp).1
  have hq' := (mem_repPairs.mp hq).1
  exact Prod.ext heq (by omega)

/-- If every element of `B` lies in `A ∩ (A - d)`, then the union of the first coordinates of
`repPairs B n` and their `d`-shift embeds into `repPairs A (n + d)`. -/
lemma card_union_fst_shift_le_sumRep {A B : Set ℕ} {d n : ℕ}
    (hBA : ∀ x ∈ B, x ∈ A ∧ x + d ∈ A) :
    (((repPairs B n).image Prod.fst) ∪
      ((repPairs B n).image Prod.fst).image (· + d)).card ≤ sumRep A (n + d) := by
  classical
  rw [← card_repPairs A (n + d)]
  refine Finset.card_le_card_of_injOn (fun z ↦ (z, n + d - z)) ?_ ?_
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image] at hz
    rcases hz with ⟨p, hp, rfl⟩ | ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    · obtain ⟨hsum, hp1, hp2⟩ := mem_repPairs.mp hp
      have h1A := (hBA p.1 hp1).1
      have h2dA := (hBA p.2 hp2).2
      refine mem_repPairs.mpr ?_
      dsimp only
      refine ⟨by omega, h1A, ?_⟩
      rwa [show n + d - p.1 = p.2 + d by omega]
    · obtain ⟨hsum, hp1, hp2⟩ := mem_repPairs.mp hp
      have h1dA := (hBA p.1 hp1).2
      have h2A := (hBA p.2 hp2).1
      refine mem_repPairs.mpr ?_
      dsimp only
      refine ⟨by omega, h1dA, ?_⟩
      rwa [show n + d - (p.1 + d) = p.2 by omega]
  · intro z₁ _ z₂ _ heq
    exact congrArg Prod.fst heq

/-- Two-shift intersection cap lowering: for any distinct positive shifts `d₁ ≠ d₂`,
`A ∩ (A - d₁) ∩ (A - d₂)` lowers any global cap `k + 2` (`1 ≤ k`) to at most `k`. -/
theorem sumRep_two_shift_inter_le {A : Set ℕ} {d₁ d₂ k : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hne : d₁ ≠ d₂) (hk : 1 ≤ k)
    (hcap : ∀ n, sumRep A n ≤ k + 2) :
    ∀ n, sumRep {x | x ∈ A ∧ x + d₁ ∈ A ∧ x + d₂ ∈ A} n ≤ k := by
  classical
  let B : Set ℕ := {x | x ∈ A ∧ x + d₁ ∈ A ∧ x + d₂ ∈ A}
  intro n
  change sumRep B n ≤ k
  by_cases h1 : sumRep B n ≤ 1
  · omega
  · let X := (repPairs B n).image Prod.fst
    have hXcard : X.card = sumRep B n := card_fst_repPairs B n
    have hX2 : 2 ≤ X.card := by omega
    rcases exists_shift_card_union_ge_add_two hX2 hd₁ hd₂ hne with h | h
    · have hle : (X ∪ X.image (· + d₁)).card ≤ sumRep A (n + d₁) :=
        card_union_fst_shift_le_sumRep (A := A) (B := B) (d := d₁) (n := n)
          (fun x hx ↦ ⟨hx.1, hx.2.1⟩)
      have hcap1 := hcap (n + d₁)
      omega
    · have hle : (X ∪ X.image (· + d₂)).card ≤ sumRep A (n + d₂) :=
        card_union_fst_shift_le_sumRep (A := A) (B := B) (d := d₂) (n := n)
          (fun x hx ↦ ⟨hx.1, hx.2.2⟩)
      have hcap2 := hcap (n + d₂)
      omega

/-- In any `B_2[2]` set (`sumRep A n ≤ 4`), every two-shift intersection
`A ∩ (A - d₁) ∩ (A - d₂)` (`0 < d₁`, `0 < d₂`, `d₁ ≠ d₂`) is a Sidon set. -/
theorem two_shift_inter_sidon_of_cap_four {A : Set ℕ} (h4 : ∀ n, sumRep A n ≤ 4)
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hne : d₁ ≠ d₂) :
    ∀ n, sumRep {x | x ∈ A ∧ x + d₁ ∈ A ∧ x + d₂ ∈ A} n ≤ 2 :=
  sumRep_two_shift_inter_le hd₁ hd₂ hne (by omega) h4

/-- In any set with `sumRep A n ≤ 3`, every two-shift intersection `A ∩ (A - d₁) ∩ (A - d₂)`
(`0 < d₁`, `0 < d₂`, `d₁ ≠ d₂`) has at most one element. -/
theorem two_shift_inter_subsingleton_of_cap_three {A : Set ℕ} (h3 : ∀ n, sumRep A n ≤ 3)
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hne : d₁ ≠ d₂) :
    {x | x ∈ A ∧ x + d₁ ∈ A ∧ x + d₂ ∈ A}.Subsingleton := by
  classical
  let B : Set ℕ := {x | x ∈ A ∧ x + d₁ ∈ A ∧ x + d₂ ∈ A}
  have h1 : ∀ n, sumRep B n ≤ 1 := sumRep_two_shift_inter_le hd₁ hd₂ hne le_rfl h3
  intro a ha b hb
  by_contra hab
  have hsub : ({(a, b), (b, a)} : Finset (ℕ × ℕ)) ⊆ repPairs B (a + b) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact mem_repPairs.mpr ⟨rfl, ha, hb⟩
    · exact mem_repPairs.mpr ⟨by omega, hb, ha⟩
  have hcard2 : ({(a, b), (b, a)} : Finset (ℕ × ℕ)).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    omega
  have hle : (repPairs B (a + b)).card ≤ 1 := by
    rw [card_repPairs]
    exact h1 (a + b)
  have := (Finset.card_le_card hsub).trans hle
  omega

/-- Overlap of `X` with `X + d` equals the number of positive-difference pairs in `X` of gap `d`. -/
lemma card_inter_image_add_eq_diffPairs (X : Finset ℕ) {d : ℕ} (hd : 0 < d) :
    (X ∩ X.image (· + d)).card = (diffPairs X d).card := by
  classical
  refine Finset.card_nbij' (fun y ↦ (y, y - d)) Prod.fst ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_inter, Finset.mem_image, mem_diffPairs] at hy ⊢
    obtain ⟨hyX, x, hxX, hxd⟩ := hy
    refine ⟨hyX, ?_, by omega, by omega⟩
    rwa [show y - d = x by omega]
  · intro p hp
    simp only [Finset.mem_coe, mem_diffPairs, Finset.mem_inter, Finset.mem_image] at hp ⊢
    exact ⟨hp.1, p.2, hp.2.1, by omega⟩
  · intro y _; rfl
  · intro p hp
    simp only [Finset.mem_coe, mem_diffPairs] at hp
    dsimp only
    exact Prod.ext rfl (by omega)

/-- Multi-shift pigeonhole bound: for any finite set `D` of positive shifts and
`B = {x ∈ A | ∀ d ∈ D, x + d ∈ A}` with `∀ n, sumRep A n ≤ k`, every `n` satisfies
`4 * |D| * sumRep B n ≤ 2 * |D| * k + sumRep B n * (sumRep B n - 1)`. -/
theorem sumRep_multi_shift_inter_bound {A : Set ℕ} {D : Finset ℕ} {k : ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (hcap : ∀ n, sumRep A n ≤ k) (n : ℕ) :
    4 * D.card * sumRep {x | x ∈ A ∧ ∀ d ∈ D, x + d ∈ A} n ≤
      2 * D.card * k +
        sumRep {x | x ∈ A ∧ ∀ d ∈ D, x + d ∈ A} n *
          (sumRep {x | x ∈ A ∧ ∀ d ∈ D, x + d ∈ A} n - 1) := by
  classical
  let B : Set ℕ := {x | x ∈ A ∧ ∀ d ∈ D, x + d ∈ A}
  change 4 * D.card * sumRep B n ≤ 2 * D.card * k + sumRep B n * (sumRep B n - 1)
  let X := (repPairs B n).image Prod.fst
  have hXcard : X.card = sumRep B n := card_fst_repPairs B n
  have hterm : ∀ d ∈ D, 2 * X.card ≤ k + (diffPairs X d).card := by
    intro d hd
    have hYcard : (X.image (· + d)).card = X.card :=
      Finset.card_image_of_injective X (fun _ _ h ↦ by omega)
    have hui := Finset.card_union_add_card_inter X (X.image (· + d))
    have hu_le : (X ∪ X.image (· + d)).card ≤ k :=
      (card_union_fst_shift_le_sumRep (A := A) (B := B) (d := d) (n := n)
        (fun x hx ↦ ⟨hx.1, hx.2 d hd⟩)).trans (hcap (n + d))
    have hi_eq : (X ∩ X.image (· + d)).card = (diffPairs X d).card :=
      card_inter_image_add_eq_diffPairs X (hDpos d hd)
    omega
  have hsum_le : D.card * (2 * X.card) ≤ D.card * k + ∑ d ∈ D, (diffPairs X d).card := by
    calc D.card * (2 * X.card)
        = ∑ _d ∈ D, 2 * X.card := by simp
      _ ≤ ∑ d ∈ D, (k + (diffPairs X d).card) := Finset.sum_le_sum hterm
      _ = D.card * k + ∑ d ∈ D, (diffPairs X d).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  have hdisj : Set.PairwiseDisjoint (↑D : Set ℕ) (fun d ↦ diffPairs X d) := by
    intro d₁ _ d₂ _ hne
    change Disjoint (diffPairs X d₁) (diffPairs X d₂)
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact hne ((mem_diffPairs.mp hp1).2.2.2.symm.trans (mem_diffPairs.mp hp2).2.2.2)
  have hdiff_sum_le : ∑ d ∈ D, (diffPairs X d).card ≤
      ((X ×ˢ X).filter (fun p ↦ p.2 < p.1)).card := by
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card fun p hp ↦ ?_
    simp only [Finset.mem_biUnion, mem_diffPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    rcases hp with ⟨_, _, h1, h2, hlt, _⟩
    exact ⟨⟨h1, h2⟩, hlt⟩
  have h2lt : 2 * ((X ×ˢ X).filter (fun p ↦ p.2 < p.1)).card = X.card * (X.card - 1) := by
    have hsq := card_sq_eq_two_mul_lt_add_self X
    have hsub : X.card * (X.card - 1) + X.card = X.card * X.card := by
      cases h : X.card with
      | zero => simp
      | succ m => simp [Nat.mul_succ]
    omega
  rw [← hXcard]
  nlinarith

/-- Large multi-shift cap halving: intersecting `A` with more than `(k - 1) * (k - 2) / 2`
positive shifts cuts any global cap `k ≥ 1` at least in half (`sumRep B n ≤ k / 2`). -/
theorem sumRep_multi_shift_inter_le_half {A : Set ℕ} {D : Finset ℕ} {k : ℕ}
    (hDne : D.Nonempty) (hDpos : ∀ d ∈ D, 0 < d) (hk : 1 ≤ k)
    (hcap : ∀ n, sumRep A n ≤ k) (hDcard : (k - 1) * (k - 2) < 2 * D.card) :
    ∀ n, 2 * sumRep {x | x ∈ A ∧ ∀ d ∈ D, x + d ∈ A} n ≤ k := by
  let B : Set ℕ := {x | x ∈ A ∧ ∀ d ∈ D, x + d ∈ A}
  intro n
  change 2 * sumRep B n ≤ k
  obtain ⟨d₀, hd₀⟩ := hDne
  have hB_le : sumRep B n ≤ k - 1 := by
    have hsub : sumRep B n ≤ sumRep {x | x ∈ A ∧ x + d₀ ∈ A} n := by
      rw [← card_repPairs, ← card_repPairs]
      refine Finset.card_le_card fun p hp ↦ ?_
      obtain ⟨hs, h1, h2⟩ := mem_repPairs.mp hp
      exact mem_repPairs.mpr ⟨hs, ⟨h1.1, h1.2 d₀ hd₀⟩, ⟨h2.1, h2.2 d₀ hd₀⟩⟩
    have hdrop := sumRep_shift_inter_le (A := A) (d := d₀) (k := k - 1) (hDpos d₀ hd₀)
      (by
        have : k = (k - 1) + 1 := by omega
        exact this ▸ hcap) n
    exact hsub.trans hdrop
  have hbound := sumRep_multi_shift_inter_bound hDpos hcap n
  change 4 * D.card * sumRep B n ≤ 2 * D.card * k + sumRep B n * (sumRep B n - 1) at hbound
  by_contra hgt
  have h2m : k + 1 ≤ 2 * sumRep B n := by omega
  have hmul : 2 * D.card * (k + 1) ≤ 4 * D.card * sumRep B n := by
    have : 4 * D.card * sumRep B n = 2 * D.card * (2 * sumRep B n) := by ring
    rw [this]
    exact Nat.mul_le_mul_left _ h2m
  have hquad : sumRep B n * (sumRep B n - 1) ≤ (k - 1) * (k - 2) :=
    Nat.mul_le_mul hB_le (by omega)
  have hlin : 2 * D.card * (k + 1) = 2 * D.card * k + 2 * D.card := by ring
  omega

/-- Cauchy-Schwarz inequality for finite sums of real numbers. -/
lemma sq_sum_le_card_mul_sum_sq_real {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    push_cast
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · have hs : s = ∅ := Finset.card_eq_zero.mp h0
      subst hs
      simp
    · have hposR : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hpos
      have hmul : (s.card : ℝ) * (f a + ∑ i ∈ s, f i) ^ 2 ≤
          (s.card : ℝ) * (((s.card : ℝ) + 1) * (f a ^ 2 + ∑ i ∈ s, f i ^ 2)) := by
        have h1 : 0 ≤ ((s.card : ℝ) * f a - ∑ i ∈ s, f i) ^ 2 := sq_nonneg _
        have h2 : 0 ≤ ((s.card : ℝ) + 1) * ((s.card : ℝ) * ∑ i ∈ s, f i ^ 2 - (∑ i ∈ s, f i) ^ 2) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr ih)
        nlinarith
      exact le_of_mul_le_mul_left hmul hposR

/-- Telescoping sum over a contiguous integer interval `[m, m + n)`. -/
lemma sum_Ico_succ_sub (f : ℕ → ℝ) (m n : ℕ) :
    ∑ j ∈ Finset.Ico m (m + n), (f (j + 1) - f j) = f (m + n) - f m := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show m + (k + 1) = (m + k) + 1 by omega,
      Finset.sum_Ico_succ_top (by omega : m ≤ m + k), ih]
    ring

/-- Dyadic block `A ∩ (2^j, 2^(j+1)]` as a `Finset`. -/
noncomputable def dyadBlock (A : Set ℕ) (j : ℕ) : Finset ℕ :=
  by classical exact (Finset.Icc (2 ^ j + 1) (2 ^ (j + 1))).filter (· ∈ A)

lemma mem_dyadBlock {A : Set ℕ} {j x : ℕ} :
    x ∈ dyadBlock A j ↔ 2 ^ j + 1 ≤ x ∧ x ≤ 2 ^ (j + 1) ∧ x ∈ A := by
  classical
  simp only [dyadBlock, Finset.mem_filter, Finset.mem_Icc]
  tauto

lemma card_prefixSet_pow_two_succ (A : Set ℕ) (j : ℕ) :
    (prefixSet A (2 ^ (j + 1))).card = (prefixSet A (2 ^ j)).card + (dyadBlock A j).card := by
  classical
  have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by omega)
  have hpow2 : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, mem_prefixSet, mem_dyadBlock]
    constructor
    · rintro ⟨h1, h2, hxA⟩
      by_cases hxj : x ≤ 2 ^ j
      · exact Or.inl ⟨h1, hxj, hxA⟩
      · exact Or.inr ⟨by omega, h2, hxA⟩
    · rintro (⟨h1, h2, hxA⟩ | ⟨h1, h2, hxA⟩) <;> exact ⟨by omega, by omega, hxA⟩
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [mem_prefixSet, mem_dyadBlock] at hx1 hx2
    omega

/-- Dyadic bucketing bound on a single block `(2^j, 2^(j+1)]` at width `2^m` (`m ≤ j`). -/
lemma dyadBlock_close_pairs_bound (A : Set ℕ) {m j : ℕ} (hmj : m ≤ j) :
    ((dyadBlock A j).card : ℝ) ^ 2 / ((2 ^ j : ℕ) : ℝ) ≤
      (8 * (((dyadBlock A j ×ˢ dyadBlock A j).filter
          (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < 2 ^ m)).card : ℝ) +
        4 * ((dyadBlock A j).card : ℝ)) / ((2 ^ m : ℕ) : ℝ) := by
  classical
  let T := dyadBlock A j
  let E := (T ×ˢ T).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < 2 ^ m)
  have hPm : 0 < 2 ^ m := Nat.pow_pos (by omega)
  have hPj : 0 < 2 ^ j := Nat.pow_pos (by omega)
  have hcs := bucket_close_pairs_bound T (N := 2 ^ (j + 1)) (P := 2 ^ m) hPm (fun x hx ↦
    (mem_dyadBlock.mp hx).2.1)
  have hdiv : 2 ^ (j + 1) / 2 ^ m = 2 * 2 ^ (j - m) := by
    have heq : 2 ^ (j + 1) = 2 ^ m * (2 * 2 ^ (j - m)) := by
      calc 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
        _ = 2 * (2 ^ m * 2 ^ (j - m)) := by rw [← pow_add, Nat.add_sub_cancel' hmj]
        _ = 2 ^ m * (2 * 2 ^ (j - m)) := by ring
    rw [heq, Nat.mul_div_right _ hPm]
  have hB_le : 2 ^ (j + 1) / 2 ^ m + 1 ≤ 4 * 2 ^ (j - m) := by
    rw [hdiv]
    have h1 : 1 ≤ 2 ^ (j - m) := Nat.one_le_pow _ 2 (by omega)
    omega
  have hnat : T.card ^ 2 * 2 ^ m ≤ 2 ^ j * (8 * E.card + 4 * T.card) := by
    have hpow : 2 ^ (j - m) * 2 ^ m = 2 ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hmj]
    calc T.card ^ 2 * 2 ^ m
        ≤ ((2 ^ (j + 1) / 2 ^ m + 1) * (2 * E.card + T.card)) * 2 ^ m :=
          Nat.mul_le_mul_right _ hcs
      _ ≤ (4 * 2 ^ (j - m) * (2 * E.card + T.card)) * 2 ^ m :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hB_le)
      _ = (2 ^ (j - m) * 2 ^ m) * (8 * E.card + 4 * T.card) := by ring
      _ = 2 ^ j * (8 * E.card + 4 * T.card) := by rw [hpow]
  have hR : (T.card : ℝ) ^ 2 * ((2 ^ m : ℕ) : ℝ) ≤
      ((2 ^ j : ℕ) : ℝ) * (8 * (E.card : ℝ) + 4 * (T.card : ℝ)) := by
    exact_mod_cast hnat
  have hPjR : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hPj
  have hPmR : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hPm
  rw [div_le_div_iff₀ hPjR hPmR]
  nlinarith

/-- Dyadic summation-by-parts and bucketing through `t` dyadic blocks starting at `2^m`. -/
theorem dyadic_close_pairs_master_window (A : Set ℕ) (m t : ℕ) :
    ∃ W : ℝ, 0 ≤ W ∧
      (√2 - 1) * ∑ j ∈ Finset.Ico m (m + t),
        ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) ≤
        ((A ∩ Icc 1 (2 ^ m)).ncard : ℝ) / √((2 ^ m : ℕ) : ℝ) + W ∧
      W ^ 2 ≤ (t : ℝ) *
        ((8 * (((prefixSet A (2 ^ (m + t)) ×ˢ prefixSet A (2 ^ (m + t))).filter
            (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < 2 ^ m)).card : ℝ) +
          4 * ((A ∩ Icc 1 (2 ^ (m + t))).ncard : ℝ)) / ((2 ^ m : ℕ) : ℝ)) := by
  classical
  let r : ℕ → ℝ := fun j ↦ ((A ∩ Icc 1 (2 ^ j)).ncard : ℝ) / √((2 ^ j : ℕ) : ℝ)
  let W : ℝ := ∑ j ∈ Finset.Ico m (m + t), ((dyadBlock A j).card : ℝ) / √((2 ^ j : ℕ) : ℝ)
  refine ⟨W, Finset.sum_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _), ?_, ?_⟩
  · have hterm : ∀ j, ((dyadBlock A j).card : ℝ) / √((2 ^ j : ℕ) : ℝ) =
        (√2 - 1) * r (j + 1) + (r (j + 1) - r j) := by
      intro j
      have hcard : ((dyadBlock A j).card : ℝ) =
          ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) - ((A ∩ Icc 1 (2 ^ j)).ncard : ℝ) := by
        have h := card_prefixSet_pow_two_succ A j
        rw [card_prefixSet, card_prefixSet] at h
        have hR : ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) =
            ((A ∩ Icc 1 (2 ^ j)).ncard : ℝ) + ((dyadBlock A j).card : ℝ) := by
          exact_mod_cast h
        linarith
      have hsqrt_pos : (0 : ℝ) < √((2 ^ j : ℕ) : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast Nat.pow_pos (a := 2) (n := j) (by omega))
      have hsqrt2 : √((2 ^ (j + 1) : ℕ) : ℝ) = √2 * √((2 ^ j : ℕ) : ℝ) := by
        have h2 : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * ((2 ^ j : ℕ) : ℝ) := by
          rw [pow_succ]
          push_cast
          ring
        rw [h2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hsqrt2_ne : √2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      have hsqrtj_ne : √((2 ^ j : ℕ) : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
      dsimp only [r]
      rw [hcard, hsqrt2]
      field_simp [hsqrt2_ne, hsqrtj_ne]
      ring
    have hW_eq : W = (√2 - 1) * ∑ j ∈ Finset.Ico m (m + t), r (j + 1) + (r (m + t) - r m) := by
      dsimp only [W]
      rw [Finset.sum_congr rfl (fun j _ ↦ hterm j), Finset.sum_add_distrib, ← Finset.mul_sum]
      have htel : ∑ j ∈ Finset.Ico m (m + t), (r (j + 1) - r j) = r (m + t) - r m := by
        exact sum_Ico_succ_sub r m t
      rw [htel]
    have hr2m : 0 ≤ r (m + t) := div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    dsimp only [r] at hW_eq hr2m ⊢
    linarith
  · let E : ℕ → Finset (ℕ × ℕ) := fun j ↦
      (dyadBlock A j ×ˢ dyadBlock A j).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < 2 ^ m)
    let Eall := (prefixSet A (2 ^ (m + t)) ×ˢ prefixSet A (2 ^ (m + t))).filter
      (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < 2 ^ m)
    have hcs := sq_sum_le_card_mul_sum_sq_real (Finset.Ico m (m + t))
      (fun j ↦ ((dyadBlock A j).card : ℝ) / √((2 ^ j : ℕ) : ℝ))
    have hcard_ico : (Finset.Ico m (m + t)).card = t := by
      simp only [Nat.card_Ico]
      omega
    rw [hcard_ico] at hcs
    have hsq_term : ∀ j ∈ Finset.Ico m (m + t),
        (((dyadBlock A j).card : ℝ) / √((2 ^ j : ℕ) : ℝ)) ^ 2 ≤
          (8 * ((E j).card : ℝ) + 4 * ((dyadBlock A j).card : ℝ)) / ((2 ^ m : ℕ) : ℝ) := by
      intro j hj
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      exact dyadBlock_close_pairs_bound A (Finset.mem_Ico.mp hj).1
    have hsum_bound : ∑ j ∈ Finset.Ico m (m + t),
        (((dyadBlock A j).card : ℝ) / √((2 ^ j : ℕ) : ℝ)) ^ 2 ≤
        (8 * (∑ j ∈ Finset.Ico m (m + t), ((E j).card : ℝ)) +
          4 * (∑ j ∈ Finset.Ico m (m + t), ((dyadBlock A j).card : ℝ))) / ((2 ^ m : ℕ) : ℝ) := by
      calc ∑ j ∈ Finset.Ico m (m + t),
            (((dyadBlock A j).card : ℝ) / √((2 ^ j : ℕ) : ℝ)) ^ 2
          ≤ ∑ j ∈ Finset.Ico m (m + t),
              (8 * ((E j).card : ℝ) + 4 * ((dyadBlock A j).card : ℝ)) / ((2 ^ m : ℕ) : ℝ) :=
            Finset.sum_le_sum hsq_term
        _ = (∑ j ∈ Finset.Ico m (m + t),
              (8 * ((E j).card : ℝ) + 4 * ((dyadBlock A j).card : ℝ))) / ((2 ^ m : ℕ) : ℝ) := by
            rw [Finset.sum_div]
        _ = (8 * (∑ j ∈ Finset.Ico m (m + t), ((E j).card : ℝ)) +
              4 * (∑ j ∈ Finset.Ico m (m + t), ((dyadBlock A j).card : ℝ))) /
              ((2 ^ m : ℕ) : ℝ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hdisjT : Set.PairwiseDisjoint (↑(Finset.Ico m (m + t)) : Set ℕ) (dyadBlock A) := by
      intro j₁ _ j₂ _ hne
      change Disjoint (dyadBlock A j₁) (dyadBlock A j₂)
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [mem_dyadBlock] at hx1 hx2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : 2 ^ (j₁ + 1) ≤ 2 ^ j₂ := Nat.pow_le_pow_right (by omega) hlt
        omega
      · have : 2 ^ (j₂ + 1) ≤ 2 ^ j₁ := Nat.pow_le_pow_right (by omega) hgt
        omega
    have hsumT_nat : ∑ j ∈ Finset.Ico m (m + t), (dyadBlock A j).card ≤
        (A ∩ Icc 1 (2 ^ (m + t))).ncard := by
      rw [← card_prefixSet, ← Finset.card_biUnion hdisjT]
      refine Finset.card_le_card fun x hx ↦ ?_
      simp only [Finset.mem_biUnion, Finset.mem_Ico, mem_dyadBlock, mem_prefixSet] at hx ⊢
      rcases hx with ⟨j, ⟨_, hjhi⟩, h1, h2, hxA⟩
      have hpow : 2 ^ (j + 1) ≤ 2 ^ (m + t) := Nat.pow_le_pow_right (by omega) hjhi
      exact ⟨by omega, h2.trans hpow, hxA⟩
    have hdisjE : Set.PairwiseDisjoint (↑(Finset.Ico m (m + t)) : Set ℕ) E := by
      intro j₁ hj₁ j₂ hj₂ hne
      change Disjoint (E j₁) (E j₂)
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [E, Finset.mem_filter, Finset.mem_product] at hp1 hp2
      exact Finset.disjoint_left.mp (hdisjT hj₁ hj₂ hne) hp1.1.1 hp2.1.1
    have hsumE_nat : ∑ j ∈ Finset.Ico m (m + t), (E j).card ≤ Eall.card := by
      rw [← Finset.card_biUnion hdisjE]
      refine Finset.card_le_card fun p hp ↦ ?_
      simp only [Finset.mem_biUnion, Finset.mem_Ico, E, Eall, Finset.mem_filter,
        Finset.mem_product, mem_dyadBlock, mem_prefixSet] at hp ⊢
      rcases hp with ⟨j, ⟨_, hjhi⟩, ⟨⟨h1a, h1b, h1A⟩, ⟨h2a, h2b, h2A⟩⟩, hlt, hdiff⟩
      have hpow : 2 ^ (j + 1) ≤ 2 ^ (m + t) := Nat.pow_le_pow_right (by omega) hjhi
      exact ⟨⟨⟨by omega, h1b.trans hpow, h1A⟩, ⟨by omega, h2b.trans hpow, h2A⟩⟩, hlt, hdiff⟩
    have hsumT_R : ∑ j ∈ Finset.Ico m (m + t), ((dyadBlock A j).card : ℝ) ≤
        ((A ∩ Icc 1 (2 ^ (m + t))).ncard : ℝ) := by exact_mod_cast hsumT_nat
    have hsumE_R : ∑ j ∈ Finset.Ico m (m + t), ((E j).card : ℝ) ≤ (Eall.card : ℝ) := by
      exact_mod_cast hsumE_nat
    have hPmR : (0 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := Nat.cast_nonneg _
    have hdiv_le : (8 * (∑ j ∈ Finset.Ico m (m + t), ((E j).card : ℝ)) +
          4 * (∑ j ∈ Finset.Ico m (m + t), ((dyadBlock A j).card : ℝ))) / ((2 ^ m : ℕ) : ℝ) ≤
        (8 * (Eall.card : ℝ) + 4 * ((A ∩ Icc 1 (2 ^ (m + t))).ncard : ℝ)) /
          ((2 ^ m : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hPmR
    exact hcs.trans (mul_le_mul_of_nonneg_left (hsum_bound.trans hdiv_le) (Nat.cast_nonneg _))

/-- Master dyadic summation-by-parts and bucketing inequality at scale `P = 2^m, N = 2^(2*m)`. -/
theorem dyadic_close_pairs_master (A : Set ℕ) (m : ℕ) :
    ∃ W : ℝ, 0 ≤ W ∧
      (√2 - 1) * ∑ j ∈ Finset.Ico m (2 * m),
        ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) ≤
        ((A ∩ Icc 1 (2 ^ m)).ncard : ℝ) / √((2 ^ m : ℕ) : ℝ) + W ∧
      W ^ 2 ≤ (m : ℝ) *
        ((8 * (((prefixSet A (2 ^ (2 * m)) ×ˢ prefixSet A (2 ^ (2 * m))).filter
            (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < 2 ^ m)).card : ℝ) +
          4 * ((A ∩ Icc 1 (2 ^ (2 * m))).ncard : ℝ)) / ((2 ^ m : ℕ) : ℝ)) := by
  simpa only [two_mul] using dyadic_close_pairs_master_window A m m

/-- Quadratic prefix bound for uniformly difference-bounded sets:
if every positive difference occurs at most `M` times, then `|A ∩ [1, N]|^2 ≤ (4 * M + 2) * N`. -/
lemma diff_bounded_prefix_sq_le {A : Set ℕ} {M : ℕ}
    (hM : ∀ d : ℕ, 0 < d → ∀ N : ℕ, ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard ≤ M) (N : ℕ) :
    ((A ∩ Icc 1 N).ncard) ^ 2 ≤ (4 * M + 2) * N := by
  classical
  let S := prefixSet A N
  rw [← card_prefixSet A N]
  change S.card ^ 2 ≤ (4 * M + 2) * N
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have hS0 : S = ∅ := by
      ext x
      simp only [S, mem_prefixSet, Finset.notMem_empty, iff_false]
      omega
    simp [hS0]
  · have hdiff_le : ∀ d : ℕ, 0 < d → (diffPairs S d).card ≤ M := by
      intro d hd
      let F := (Finset.Icc 1 N).filter (fun x ↦ x ∈ A ∧ x + d ∈ A)
      have hF : F.card = ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard := by
        have heq : (F : Set ℕ) = {x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N := by
          ext x
          simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
            Set.mem_Icc, Set.mem_ofPred_eq]
          tauto
        rw [← Set.ncard_coe_finset, heq]
      refine le_trans ?_ (hF ▸ hM d hd N)
      refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
      · intro p hp
        simp only [diffPairs, S, F, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
          mem_prefixSet, Finset.mem_Icc] at hp ⊢
        rcases hp with ⟨⟨⟨_, _, hp1A⟩, ⟨h2lo, h2hi, hp2A⟩⟩, hlt, hdiff⟩
        refine ⟨⟨h2lo, h2hi⟩, hp2A, ?_⟩
        rwa [show p.2 + d = p.1 by omega]
      · intro p hp q hq heq
        simp only [diffPairs, Finset.mem_coe, Finset.mem_filter] at hp hq
        exact Prod.ext (by omega) heq
    have hS : S ⊆ Finset.Icc 1 N := prefixSet_subset_Icc A N
    have hDle : ((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card ≤ M * N := by
      rw [← sum_card_diffPairs_eq hS]
      calc ∑ d ∈ Finset.Ico 1 N, (diffPairs S d).card
          ≤ ∑ _d ∈ Finset.Ico 1 N, M := Finset.sum_le_sum fun d hd ↦
            hdiff_le d (Finset.mem_Ico.mp hd).1
        _ = (Finset.Ico 1 N).card * M := by simp
        _ ≤ N * M := by
            apply Nat.mul_le_mul_right
            simp only [Nat.card_Ico]
            omega
        _ = M * N := Nat.mul_comm N M
    have hsq : S.card * S.card = 2 * ((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card + S.card :=
      card_sq_eq_two_mul_lt_add_self S
    have hZ : (S.card : ℤ) ^ 2 ≤ 4 * (M : ℤ) * (N : ℤ) + 1 := by
      have hsqZ : (S.card : ℤ) * (S.card : ℤ) =
          2 * (((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card : ℤ) + (S.card : ℤ) := by
        exact_mod_cast hsq
      have hDZ : (((S ×ˢ S).filter (fun p ↦ p.2 < p.1)).card : ℤ) ≤ (M : ℤ) * (N : ℤ) := by
        exact_mod_cast hDle
      nlinarith [sq_nonneg ((S.card : ℤ) - 1)]
    have hnat : S.card ^ 2 ≤ 4 * M * N + 1 := by exact_mod_cast hZ
    nlinarith

/-- Quantitative Erdos (1955) for all uniformly difference-bounded sets:
if every positive difference occurs at most `M` times, then in every dyadic window
`[2^m, 2^(2*m)]` (`m ≥ 1`), there is `N` with `|A ∩ [1, N]|^2 * log N ≤ 2 * (84 * M + 30)^2 * N`. -/
theorem diff_bounded_erdos_1955_quantitative {A : Set ℕ} {M : ℕ}
    (hM : ∀ d : ℕ, 0 < d → ∀ N : ℕ, ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard ≤ M)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ N : ℕ, 2 ^ m ≤ N ∧ N ≤ 2 ^ (2 * m) ∧
      ((A ∩ Icc 1 N).ncard : ℝ) ^ 2 * Real.log (N : ℝ) ≤
        2 * ((84 * M + 30 : ℕ) : ℝ) ^ 2 * (N : ℝ) := by
  classical
  obtain ⟨W, hW0, hsum_le, hWsq⟩ := dyadic_close_pairs_master A m
  let P := 2 ^ m
  let N0 := 2 ^ (2 * m)
  let S := prefixSet A N0
  let Eall := (S ×ˢ S).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)
  have hE_le : Eall.card ≤ M * P := by
    have hE_eq : Eall.card = ∑ d ∈ Finset.Ico 1 P, (diffPairs S d).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext p
        simp only [Eall, Finset.mem_biUnion, Finset.mem_Ico, diffPairs, Finset.mem_filter,
          Finset.mem_product]
        constructor
        · rintro ⟨hp, hlt, hdiff⟩
          exact ⟨p.1 - p.2, ⟨by omega, hdiff⟩, hp, hlt, rfl⟩
        · rintro ⟨d, ⟨hd1, hd2⟩, hp, hlt, rfl⟩
          exact ⟨hp, hlt, hd2⟩
      · intro d₁ _ d₂ _ hne
        change Disjoint (diffPairs S d₁) (diffPairs S d₂)
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [diffPairs, Finset.mem_filter] at hp1 hp2
        exact hne (hp1.2.2.symm.trans hp2.2.2)
    have hdiff_le : ∀ d : ℕ, 0 < d → (diffPairs S d).card ≤ M := by
      intro d hd
      let F := (Finset.Icc 1 N0).filter (fun x ↦ x ∈ A ∧ x + d ∈ A)
      have hF : F.card = ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N0).ncard := by
        have heq : (F : Set ℕ) = {x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N0 := by
          ext x
          simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
            Set.mem_Icc, Set.mem_ofPred_eq]
          tauto
        rw [← Set.ncard_coe_finset, heq]
      refine le_trans ?_ (hF ▸ hM d hd N0)
      refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
      · intro p hp
        simp only [diffPairs, S, F, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
          mem_prefixSet, Finset.mem_Icc] at hp ⊢
        rcases hp with ⟨⟨⟨_, _, hp1A⟩, ⟨h2lo, h2hi, hp2A⟩⟩, hlt, hdiff⟩
        refine ⟨⟨h2lo, h2hi⟩, hp2A, ?_⟩
        rwa [show p.2 + d = p.1 by omega]
      · intro p hp q hq heq
        simp only [diffPairs, Finset.mem_coe, Finset.mem_filter] at hp hq
        exact Prod.ext (by omega) heq
    rw [hE_eq]
    calc ∑ d ∈ Finset.Ico 1 P, (diffPairs S d).card
        ≤ ∑ _d ∈ Finset.Ico 1 P, M := Finset.sum_le_sum fun d hd ↦
          hdiff_le d (Finset.mem_Ico.mp hd).1
      _ = (Finset.Ico 1 P).card * M := by simp
      _ ≤ P * M := by
          apply Nat.mul_le_mul_right
          simp only [Nat.card_Ico]
          exact Nat.sub_le P 1
      _ = M * P := Nat.mul_comm P M
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast Nat.pow_pos (a := 2) (n := m) (by omega)
  have hrm_le : ((A ∩ Icc 1 (2 ^ m)).ncard : ℝ) / √((2 ^ m : ℕ) : ℝ) ≤ ((4 * M + 2 : ℕ) : ℝ) := by
    have hq := diff_bounded_prefix_sq_le hM (2 ^ m)
    have hqR : ((A ∩ Icc 1 (2 ^ m)).ncard : ℝ) ^ 2 ≤ ((4 * M + 2 : ℕ) : ℝ) * ((2 ^ m : ℕ) : ℝ) := by
      exact_mod_cast hq
    have hsq : (((A ∩ Icc 1 (2 ^ m)).ncard : ℝ) / √((2 ^ m : ℕ) : ℝ)) ^ 2 ≤
        ((4 * M + 2 : ℕ) : ℝ) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_le_iff₀ hPpos]
      have hge1 : (1 : ℝ) ≤ ((4 * M + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 4 * M + 2 by omega)
      nlinarith
    nlinarith [div_nonneg (Nat.cast_nonneg (A ∩ Icc 1 (2 ^ m)).ncard) (Real.sqrt_nonneg ((2 ^ m : ℕ) : ℝ))]
  have hN0_le : ((A ∩ Icc 1 (2 ^ (2 * m))).ncard : ℝ) / ((2 ^ m : ℕ) : ℝ) ≤
      ((4 * M + 2 : ℕ) : ℝ) := by
    have hq := diff_bounded_prefix_sq_le hM (2 ^ (2 * m))
    have hpow : (2 ^ (2 * m) : ℕ) = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
    have hqR : ((A ∩ Icc 1 (2 ^ (2 * m))).ncard : ℝ) ^ 2 ≤
        ((4 * M + 2 : ℕ) : ℝ) * ((2 ^ m : ℕ) : ℝ) ^ 2 := by
      have hqR0 : ((A ∩ Icc 1 (2 ^ (2 * m))).ncard : ℝ) ^ 2 ≤
          ((4 * M + 2 : ℕ) : ℝ) * ((2 ^ (2 * m) : ℕ) : ℝ) := by exact_mod_cast hq
      have hpowR : ((2 ^ (2 * m) : ℕ) : ℝ) = ((2 ^ m : ℕ) : ℝ) ^ 2 := by exact_mod_cast hpow
      rwa [hpowR] at hqR0
    have hsq : (((A ∩ Icc 1 (2 ^ (2 * m))).ncard : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ 2 ≤
        ((4 * M + 2 : ℕ) : ℝ) ^ 2 := by
      rw [div_pow, div_le_iff₀ (pow_pos hPpos 2)]
      have hge1 : (1 : ℝ) ≤ ((4 * M + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 4 * M + 2 by omega)
      nlinarith
    nlinarith [div_nonneg (Nat.cast_nonneg (A ∩ Icc 1 (2 ^ (2 * m))).ncard) hPpos.le]
  have hE_div : (Eall.card : ℝ) / ((2 ^ m : ℕ) : ℝ) ≤ (M : ℝ) := by
    rw [div_le_iff₀ hPpos]
    exact_mod_cast hE_le
  have hW_le : W ≤ ((24 * M + 8 : ℕ) : ℝ) * √(m : ℝ) := by
    have hWsq2 : W ^ 2 ≤ (((24 * M + 8 : ℕ) : ℝ) * √(m : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
      have hcomb : (8 * (Eall.card : ℝ) + 4 * ((A ∩ Icc 1 (2 ^ (2 * m))).ncard : ℝ)) /
            ((2 ^ m : ℕ) : ℝ) ≤ ((24 * M + 8 : ℕ) : ℝ) ^ 2 := by
        rw [add_div, mul_div_assoc, mul_div_assoc]
        have h24eq : ((24 * M + 8 : ℕ) : ℝ) = 8 * (M : ℝ) + 4 * ((4 * M + 2 : ℕ) : ℝ) := by
          push_cast; ring
        have h1 : 8 * ((Eall.card : ℝ) / ((2 ^ m : ℕ) : ℝ)) +
            4 * (((A ∩ Icc 1 (2 ^ (2 * m))).ncard : ℝ) / ((2 ^ m : ℕ) : ℝ)) ≤
            ((24 * M + 8 : ℕ) : ℝ) := by
          linarith
        have hge1 : (1 : ℝ) ≤ ((24 * M + 8 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ 24 * M + 8 by omega)
        nlinarith
      have hWsq' : W ^ 2 ≤ (m : ℝ) *
          ((8 * (Eall.card : ℝ) + 4 * ((A ∩ Icc 1 (2 ^ (2 * m))).ncard : ℝ)) /
            ((2 ^ m : ℕ) : ℝ)) := hWsq
      calc W ^ 2 ≤ (m : ℝ) * ((24 * M + 8 : ℕ) : ℝ) ^ 2 :=
            hWsq'.trans (mul_le_mul_of_nonneg_left hcomb (Nat.cast_nonneg m))
        _ = ((24 * M + 8 : ℕ) : ℝ) ^ 2 * (m : ℝ) := by ring
    nlinarith [mul_nonneg (Nat.cast_nonneg (24 * M + 8)) (Real.sqrt_nonneg (m : ℝ))]
  have hsqrtm_ge : (1 : ℝ) ≤ √(m : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
  have hsqrt2_lb : (1 / 3 : ℝ) ≤ √2 - 1 := by
    have : (4 / 3 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have hsum_ub : ∑ j ∈ Finset.Ico m (2 * m),
      ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) ≤
      ((84 * M + 30 : ℕ) : ℝ) * √(m : ℝ) := by
    have hsum_nn : 0 ≤ ∑ j ∈ Finset.Ico m (2 * m),
        ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) :=
      Finset.sum_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    have h28eq : ((28 * M + 10 : ℕ) : ℝ) = ((4 * M + 2 : ℕ) : ℝ) + ((24 * M + 8 : ℕ) : ℝ) := by
      push_cast; ring
    have h84eq : ((84 * M + 30 : ℕ) : ℝ) = 3 * ((28 * M + 10 : ℕ) : ℝ) := by
      push_cast; ring
    have h1 : (1 / 3 : ℝ) * ∑ j ∈ Finset.Ico m (2 * m),
        ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) ≤
        ((28 * M + 10 : ℕ) : ℝ) * √(m : ℝ) := by
      have hrm_mul : ((4 * M + 2 : ℕ) : ℝ) ≤ ((4 * M + 2 : ℕ) : ℝ) * √(m : ℝ) :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) hsqrtm_ge
      have hstep : (1 / 3 : ℝ) * ∑ j ∈ Finset.Ico m (2 * m),
          ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) ≤
          ((A ∩ Icc 1 (2 ^ m)).ncard : ℝ) / √((2 ^ m : ℕ) : ℝ) + W :=
        (mul_le_mul_of_nonneg_right hsqrt2_lb hsum_nn).trans hsum_le
      nlinarith
    nlinarith
  have hex_j : ∃ j ∈ Finset.Ico m (2 * m),
      (m : ℝ) * (((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ)) ≤
        ((84 * M + 30 : ℕ) : ℝ) * √(m : ℝ) := by
    by_contra hno
    push Not at hno
    have hne : (Finset.Ico m (2 * m)).Nonempty := ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    have hlt : ∑ _j ∈ Finset.Ico m (2 * m), (((84 * M + 30 : ℕ) : ℝ) * √(m : ℝ)) <
        ∑ j ∈ Finset.Ico m (2 * m),
          (m : ℝ) * (((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty hne hno
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hlt
    have hcard_ico : (Finset.Ico m (2 * m)).card = m := by simp only [Nat.card_Ico]; omega
    rw [hcard_ico] at hlt
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have := lt_of_mul_lt_mul_left hlt hm_pos.le
    linarith
  obtain ⟨j, hj, hjle⟩ := hex_j
  obtain ⟨hmj, hj2m⟩ := Finset.mem_Ico.mp hj
  refine ⟨2 ^ (j + 1), Nat.pow_le_pow_right (by omega) (by omega),
    Nat.pow_le_pow_right (by omega) (by omega), ?_⟩
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hsq : ((m : ℝ) * (((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) /
        √((2 ^ (j + 1) : ℕ) : ℝ))) ^ 2 ≤
      (((84 * M + 30 : ℕ) : ℝ) * √(m : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hm_pos.le (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)))
      hjle 2
  rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg _), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg m)] at hsq
  have hm_cancel : (m : ℝ) * (((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) ^ 2 /
      ((2 ^ (j + 1) : ℕ) : ℝ)) ≤ ((84 * M + 30 : ℕ) : ℝ) ^ 2 := by
    have : (m : ℝ) * ((m : ℝ) * (((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) ^ 2 /
        ((2 ^ (j + 1) : ℕ) : ℝ))) ≤ (m : ℝ) * ((84 * M + 30 : ℕ) : ℝ) ^ 2 := by
      linarith
    exact le_of_mul_le_mul_left this hm_pos
  have h2j1_pos : (0 : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (a := 2) (n := j + 1) (by omega)
  have hmul_m : ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) ^ 2 * (m : ℝ) ≤
      ((84 * M + 30 : ℕ) : ℝ) ^ 2 * ((2 ^ (j + 1) : ℕ) : ℝ) := by
    have h1 := (div_le_iff₀ h2j1_pos).mp (by
      calc ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) ^ 2 * (m : ℝ) / ((2 ^ (j + 1) : ℕ) : ℝ)
          = (m : ℝ) * (((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) ^ 2 / ((2 ^ (j + 1) : ℕ) : ℝ)) := by
            ring
        _ ≤ ((84 * M + 30 : ℕ) : ℝ) ^ 2 := hm_cancel)
    exact h1
  have hlog_le : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    have hle_pow : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ ((2 ^ (2 * m) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega : j + 1 ≤ 2 * m)
    have hlog1 : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ≤ Real.log ((2 ^ (2 * m) : ℕ) : ℝ) :=
      Real.log_le_log h2j1_pos hle_pow
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlog_pow : Real.log ((2 ^ (2 * m) : ℕ) : ℝ) = (2 * m : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      push_cast
      ring
    rw [hlog_pow] at hlog1
    nlinarith
  calc ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) ^ 2 * Real.log ((2 ^ (j + 1) : ℕ) : ℝ)
      ≤ ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) ^ 2 * (2 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_le (sq_nonneg _)
    _ = 2 * (((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) ^ 2 * (m : ℝ)) := by ring
    _ ≤ 2 * (((84 * M + 30 : ℕ) : ℝ) ^ 2 * ((2 ^ (j + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hmul_m (by norm_num)
    _ = 2 * ((84 * M + 30 : ℕ) : ℝ) ^ 2 * ((2 ^ (j + 1) : ℕ) : ℝ) := by ring

/-- Erdos (1955) full quantitative theorem for Sidon sets (`sumRep A n ≤ 2`):
in every dyadic window `[2^m, 2^(2*m)]` (`m ≥ 1`), there is `N` with
`|A ∩ [1, N]|^2 * log N ≤ 2 * 114^2 * N`. -/
theorem sidon_erdos_1955_quantitative {A : Set ℕ} (hS : ∀ n, sumRep A n ≤ 2)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ N : ℕ, 2 ^ m ≤ N ∧ N ≤ 2 ^ (2 * m) ∧
      ((A ∩ Icc 1 N).ncard : ℝ) ^ 2 * Real.log (N : ℝ) ≤ 2 * (114 : ℝ) ^ 2 * (N : ℝ) := by
  have hM : ∀ d : ℕ, 0 < d → ∀ N : ℕ, ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard ≤ 1 := by
    intro d hd N
    classical
    let F := (Finset.Icc 1 N).filter (fun x ↦ x ∈ A ∧ x + d ∈ A)
    have hF : F.card = ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard := by
      have heq : (F : Set ℕ) = {x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N := by
        ext x
        simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
          Set.mem_Icc, Set.mem_ofPred_eq]
        tauto
      rw [← Set.ncard_coe_finset, heq]
    rw [← hF]
    refine Finset.card_le_one.mpr fun x hx y hy ↦ ?_
    simp only [F, Finset.mem_filter] at hx hy
    have h := sidon_diff_inj hS hx.2.2 hx.2.1 hy.2.2 hy.2.1 (by omega) (by omega) (by omega)
    exact h.2
  simpa using diff_bounded_erdos_1955_quantitative (M := 1) hM hm

/-- Quantitative Erdos (1955) extended to `sumRep A n ≤ 3` via odd thinning:
in every dyadic window `[2^m, 2^(2*m)]` (`m ≥ 1`), there is `N` with
`|A ∩ [1, N]|^2 * log N ≤ 8 * 114^2 * N`. -/
theorem cap_three_erdos_1955_quantitative {A : Set ℕ} (h3 : ∀ n, sumRep A n ≤ 3)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ N : ℕ, 2 ^ m ≤ N ∧ N ≤ 2 ^ (2 * m) ∧
      ((A ∩ Icc 1 N).ncard : ℝ) ^ 2 * Real.log (N : ℝ) ≤ 8 * (114 : ℝ) ^ 2 * (N : ℝ) := by
  obtain ⟨B, _, hB2, hprefix⟩ := exists_even_cap_sub (h := 1) le_rfl h3
  obtain ⟨N, hN1, hN2, hBquant⟩ := sidon_erdos_1955_quantitative hB2 hm
  refine ⟨N, hN1, hN2, ?_⟩
  have hpreR : ((A ∩ Icc 1 N).ncard : ℝ) ≤ 2 * ((B ∩ Icc 1 N).ncard : ℝ) := by
    exact_mod_cast hprefix N
  have hsq : ((A ∩ Icc 1 N).ncard : ℝ) ^ 2 ≤ 4 * ((B ∩ Icc 1 N).ncard : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hpreR 2
    linarith
  have hlog_nn : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by
      have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
      exact_mod_cast (by omega : 1 ≤ N))
  calc ((A ∩ Icc 1 N).ncard : ℝ) ^ 2 * Real.log (N : ℝ)
      ≤ 4 * ((B ∩ Icc 1 N).ncard : ℝ) ^ 2 * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_right hsq hlog_nn
    _ = 4 * (((B ∩ Icc 1 N).ncard : ℝ) ^ 2 * Real.log (N : ℝ)) := by ring
    _ ≤ 4 * (2 * (114 : ℝ) ^ 2 * (N : ℝ)) := mul_le_mul_of_nonneg_left hBquant (by norm_num)
    _ = 8 * (114 : ℝ) ^ 2 * (N : ℝ) := by ring

/-- Uniform lower bound on close pairs across a dyadic window of length `t ≤ m`. -/
theorem cap_close_pairs_in_dyadic_window {A : Set ℕ} {k : ℕ} (hcap : ∀ n, sumRep A n ≤ k)
    (hdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) :
    ∃ K₀ t₀ : ℕ, 0 < K₀ ∧ ∀ m t : ℕ, t₀ ≤ t → t ≤ m →
      t * 2 ^ m ≤ K₀ * ((prefixSet A (2 ^ (m + t)) ×ˢ prefixSet A (2 ^ (m + t))).filter
        (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < 2 ^ m)).card := by
  classical
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hdense
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hc
  obtain ⟨C₀, hC₀⟩ := exists_nat_ge (max c 1)
  let C := max C₀ 1
  have hCpos : 0 < C := by omega
  have hCposR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCpos
  have hcC : c ≤ (C : ℝ) := (le_max_left c 1).trans (hC₀.trans (by exact_mod_cast le_max_left C₀ 1))
  have hinv_lb : ∀ N, N₀ ≤ N → 0 < N →
      (1 : ℝ) / (C : ℝ) ≤ ((A ∩ Icc 1 N).ncard : ℝ) / √(N : ℝ) := by
    intro N hN hNpos
    have h1 := hN₀ N hN
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast] at h1
    have h2 : √(N : ℝ) ≤ (C : ℝ) * ((A ∩ Icc 1 N).ncard : ℝ) :=
      h1.trans (mul_le_mul_of_nonneg_right hcC (Nat.cast_nonneg _))
    have hsqrt_pos : (0 : ℝ) < √(N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
    rw [div_le_div_iff₀ hCposR hsqrt_pos]
    linarith
  have hratio_ub : ∀ N, 0 < N →
      ((A ∩ Icc 1 N).ncard : ℝ) / √(N : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
    intro N hNpos
    have hq := cap_prefix_sq_le hcap N
    have hqR : ((A ∩ Icc 1 N).ncard : ℝ) ^ 2 ≤ ((2 * k : ℕ) : ℝ) * (N : ℝ) := by exact_mod_cast hq
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hsq : (((A ∩ Icc 1 N).ncard : ℝ) / √(N : ℝ)) ^ 2 ≤ ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hNR.le, div_le_iff₀ hNR]
      have hge1 : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * k + 1 by omega)
      have h2k : ((2 * k : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 * k ≤ 2 * k + 1 by omega)
      have h2ksq : ((2 * k : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      exact hqR.trans (mul_le_mul_of_nonneg_right h2ksq hNR.le)
    nlinarith [div_nonneg (Nat.cast_nonneg (A ∩ Icc 1 N).ncard) (Real.sqrt_nonneg (N : ℝ))]
  let t₀ := max (max N₀ 1) (288 * C ^ 2 * (2 * k + 1))
  refine ⟨576 * C ^ 2, t₀, by positivity, fun m t ht htm ↦ ?_⟩
  have ht1 : 1 ≤ t := le_trans ((le_max_right N₀ 1).trans (le_max_left _ _)) ht
  have hmN0 : N₀ ≤ m := (((le_max_left N₀ 1).trans (le_max_left _ _)).trans ht).trans htm
  have hmbig : 288 * C ^ 2 * (2 * k + 1) ≤ t := le_trans (le_max_right _ _) ht
  obtain ⟨W, hW0, hsum_le, hWsq⟩ := dyadic_close_pairs_master_window A m t
  let Eall := (prefixSet A (2 ^ (m + t)) ×ˢ prefixSet A (2 ^ (m + t))).filter
    (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < 2 ^ m)
  have hsum_lb : (t : ℝ) / (C : ℝ) ≤ ∑ j ∈ Finset.Ico m (m + t),
      ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) := by
    have hcard_ico : (Finset.Ico m (m + t)).card = t := by simp only [Nat.card_Ico]; omega
    calc (t : ℝ) / (C : ℝ)
        = (t : ℝ) * ((1 : ℝ) / (C : ℝ)) := by ring
      _ = ∑ _j ∈ Finset.Ico m (m + t), ((1 : ℝ) / (C : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard_ico]
      _ ≤ ∑ j ∈ Finset.Ico m (m + t),
            ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          have hmj : m ≤ j := (Finset.mem_Ico.mp hj).1
          have hpow_ge : N₀ ≤ 2 ^ (j + 1) := by
            have hlt : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
            omega
          exact hinv_lb (2 ^ (j + 1)) hpow_ge (Nat.pow_pos (by omega))
  have hsqrt2_lb : (1 / 3 : ℝ) ≤ √2 - 1 := by
    have : (4 / 3 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have hrm_ub : ((A ∩ Icc 1 (2 ^ m)).ncard : ℝ) / √((2 ^ m : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) :=
    hratio_ub (2 ^ m) (Nat.pow_pos (by omega))
  have hN0_ub : ((A ∩ Icc 1 (2 ^ (m + t))).ncard : ℝ) / ((2 ^ m : ℕ) : ℝ) ≤
      ((2 * k + 1 : ℕ) : ℝ) := by
    have h := hratio_ub (2 ^ (2 * m)) (Nat.pow_pos (by omega))
    have hsq2m : √((2 ^ (2 * m) : ℕ) : ℝ) = ((2 ^ m : ℕ) : ℝ) := by
      have hp : ((2 ^ (2 * m) : ℕ) : ℝ) = ((2 ^ m : ℕ) : ℝ) ^ 2 := by
        rw [← Nat.cast_pow, ← pow_mul, mul_comm]
      rw [hp, Real.sqrt_sq (Nat.cast_nonneg _)]
    rw [hsq2m] at h
    have hle : (A ∩ Icc 1 (2 ^ (m + t))).ncard ≤ (A ∩ Icc 1 (2 ^ (2 * m))).ncard := by
      rw [← card_prefixSet, ← card_prefixSet]
      refine Finset.card_le_card fun x hx ↦ ?_
      obtain ⟨hlo, hhi, hxA⟩ := mem_prefixSet.mp hx
      exact mem_prefixSet.mpr ⟨hlo, hhi.trans (Nat.pow_le_pow_right (by decide) (by omega)), hxA⟩
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity)).trans h
  have hm_bigR : (288 : ℝ) * (C : ℝ) ^ 2 * ((2 * k + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hmbig
  have hC1R : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hCpos
  have hW_lb : (t : ℝ) / (6 * (C : ℝ)) ≤ W := by
    have h1 : (1 / 3 : ℝ) * ((t : ℝ) / (C : ℝ)) ≤
        ((A ∩ Icc 1 (2 ^ m)).ncard : ℝ) / √((2 ^ m : ℕ) : ℝ) + W := by
      have hsum_nn : 0 ≤ ∑ j ∈ Finset.Ico m (m + t),
          ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) :=
        Finset.sum_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      calc (1 / 3 : ℝ) * ((t : ℝ) / (C : ℝ))
          ≤ (1 / 3 : ℝ) * ∑ j ∈ Finset.Ico m (m + t),
              ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hsum_lb (by norm_num)
        _ ≤ (√2 - 1) * ∑ j ∈ Finset.Ico m (m + t),
              ((A ∩ Icc 1 (2 ^ (j + 1))).ncard : ℝ) / √((2 ^ (j + 1) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hsqrt2_lb hsum_nn
        _ ≤ ((A ∩ Icc 1 (2 ^ m)).ncard : ℝ) / √((2 ^ m : ℕ) : ℝ) + W := hsum_le
    have hrm_small : ((2 * k + 1 : ℕ) : ℝ) ≤ (t : ℝ) / (6 * (C : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h1' : (t : ℝ) / (3 * (C : ℝ)) ≤ ((2 * k + 1 : ℕ) : ℝ) + W := by
      have : (1 / 3 : ℝ) * ((t : ℝ) / (C : ℝ)) = (t : ℝ) / (3 * (C : ℝ)) := by ring
      linarith
    have : (t : ℝ) / (3 * (C : ℝ)) - (t : ℝ) / (6 * (C : ℝ)) = (t : ℝ) / (6 * (C : ℝ)) := by ring
    linarith
  have ht_posR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hPposR : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.pow_pos (a := 2) (n := m) (by omega)
  have hWsq_lb : ((t : ℝ) / (6 * (C : ℝ))) ^ 2 ≤
      (t : ℝ) * ((8 * (Eall.card : ℝ) + 4 * ((A ∩ Icc 1 (2 ^ (m + t))).ncard : ℝ)) /
        ((2 ^ m : ℕ) : ℝ)) :=
    (pow_le_pow_left₀ (by positivity) hW_lb 2).trans hWsq
  have hdiv_m : (t : ℝ) / (36 * (C : ℝ) ^ 2) ≤
      8 * ((Eall.card : ℝ) / ((2 ^ m : ℕ) : ℝ)) +
        4 * (((A ∩ Icc 1 (2 ^ (m + t))).ncard : ℝ) / ((2 ^ m : ℕ) : ℝ)) := by
    have hmul : (t : ℝ) * ((t : ℝ) / (36 * (C : ℝ) ^ 2)) ≤
        (t : ℝ) * (8 * ((Eall.card : ℝ) / ((2 ^ m : ℕ) : ℝ)) +
          4 * (((A ∩ Icc 1 (2 ^ (m + t))).ncard : ℝ) / ((2 ^ m : ℕ) : ℝ))) := by
      have hl : ((t : ℝ) / (6 * (C : ℝ))) ^ 2 = (t : ℝ) * ((t : ℝ) / (36 * (C : ℝ) ^ 2)) := by
        ring
      have hr : (8 * (Eall.card : ℝ) + 4 * ((A ∩ Icc 1 (2 ^ (m + t))).ncard : ℝ)) /
            ((2 ^ m : ℕ) : ℝ) =
          8 * ((Eall.card : ℝ) / ((2 ^ m : ℕ) : ℝ)) +
            4 * (((A ∩ Icc 1 (2 ^ (m + t))).ncard : ℝ) / ((2 ^ m : ℕ) : ℝ)) := by
        ring
      rwa [hl, hr] at hWsq_lb
    exact le_of_mul_le_mul_left hmul ht_posR
  have h4small : 4 * ((2 * k + 1 : ℕ) : ℝ) ≤ (t : ℝ) / (72 * (C : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hE_lbR : (t : ℝ) / (576 * (C : ℝ) ^ 2) ≤ (Eall.card : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
    have h72 : (t : ℝ) / (72 * (C : ℝ) ^ 2) ≤ 8 * ((Eall.card : ℝ) / ((2 ^ m : ℕ) : ℝ)) := by
      have hsub : (t : ℝ) / (36 * (C : ℝ) ^ 2) - (t : ℝ) / (72 * (C : ℝ) ^ 2) =
          (t : ℝ) / (72 * (C : ℝ) ^ 2) := by ring
      linarith
    have hdiv8 : (t : ℝ) / (576 * (C : ℝ) ^ 2) = ((t : ℝ) / (72 * (C : ℝ) ^ 2)) / 8 := by ring
    linarith
  have hfinalR : (t : ℝ) * ((2 ^ m : ℕ) : ℝ) ≤ (576 * (C : ℝ) ^ 2) * (Eall.card : ℝ) := by
    have := (div_le_div_iff₀ (by positivity : (0 : ℝ) < 576 * (C : ℝ) ^ 2) hPposR).mp hE_lbR
    linarith
  exact_mod_cast hfinalR

/-- Sharp logarithmic close-pair lower bound at scale `P = 2^m, N = 2^(2*m) = P^2`:
any bounded-representation set with `|A ∩ [1, N]| ≫ √N` has `Ω(m * 2^m)` close pairs
with difference `< 2^m` already inside `[1, 2^(2*m)]` for all sufficiently large `m`. -/
theorem cap_log_close_pairs_at_sq {A : Set ℕ} {k : ℕ} (hcap : ∀ n, sumRep A n ≤ k)
    (hdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) :
    ∃ K₀ m₀ : ℕ, 0 < K₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      m * 2 ^ m ≤ K₀ * ((prefixSet A (2 ^ (2 * m)) ×ˢ prefixSet A (2 ^ (2 * m))).filter
        (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < 2 ^ m)).card := by
  obtain ⟨K₀, t₀, hK, h⟩ := cap_close_pairs_in_dyadic_window hcap hdense
  exact ⟨K₀, t₀, hK, fun m hm ↦ by simpa only [two_mul] using h m m hm le_rfl⟩

/-- Sharp logarithmic difference multiplicity at scale `P = 2^m, N = 2^(2*m) = P^2`:
any bounded-representation set with `|A ∩ [1, N]| ≫ √N` has, for all sufficiently large `m`,
a positive difference `d < 2^m` occurring at least `Ω(m)` times in `A ∩ [1, 2^(2*m)]`. -/
theorem cap_log_diff_mult_at_sq {A : Set ℕ} {k : ℕ} (hcap : ∀ n, sumRep A n ≤ k)
    (hdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) :
    ∃ K₀ m₀ : ℕ, 0 < K₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ d : ℕ, 0 < d ∧ d < 2 ^ m ∧
        m ≤ K₀ * ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 (2 ^ (2 * m))).ncard := by
  classical
  obtain ⟨K₀, m₀, hK₀, hclose⟩ := cap_log_close_pairs_at_sq hcap hdense
  refine ⟨K₀, max m₀ 1, hK₀, fun m hm ↦ ?_⟩
  have hm0 : m₀ ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hbig := hclose m hm0
  let P := 2 ^ m
  let N := 2 ^ (2 * m)
  let S := prefixSet A N
  let Eall := (S ×ˢ S).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)
  have hE_eq : Eall.card = ∑ d ∈ Finset.Ico 1 P, (diffPairs S d).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Eall, Finset.mem_biUnion, Finset.mem_Ico, diffPairs, Finset.mem_filter,
        Finset.mem_product]
      constructor
      · rintro ⟨hp, hlt, hdiff⟩
        exact ⟨p.1 - p.2, ⟨by omega, hdiff⟩, hp, hlt, rfl⟩
      · rintro ⟨d, ⟨hd1, hd2⟩, hp, hlt, rfl⟩
        exact ⟨hp, hlt, hd2⟩
    · intro d₁ _ d₂ _ hne
      change Disjoint (diffPairs S d₁) (diffPairs S d₂)
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [diffPairs, Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.2.symm.trans hp2.2.2)
  have hdiff_le : ∀ d : ℕ, (diffPairs S d).card ≤ ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard := by
    intro d
    let F := (Finset.Icc 1 N).filter (fun x ↦ x ∈ A ∧ x + d ∈ A)
    have hF : F.card = ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard := by
      have heq : (F : Set ℕ) = {x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N := by
        ext x
        simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_inter_iff,
          Set.mem_Icc, Set.mem_ofPred_eq]
        tauto
      rw [← Set.ncard_coe_finset, heq]
    rw [← hF]
    refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
    · intro p hp
      simp only [diffPairs, S, F, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        mem_prefixSet, Finset.mem_Icc] at hp ⊢
      rcases hp with ⟨⟨⟨_, _, hp1A⟩, ⟨h2lo, h2hi, hp2A⟩⟩, hlt, hdiff⟩
      refine ⟨⟨h2lo, h2hi⟩, hp2A, ?_⟩
      rwa [show p.2 + d = p.1 by omega]
    · intro p hp q hq heq
      simp only [diffPairs, Finset.mem_coe, Finset.mem_filter] at hp hq
      exact Prod.ext (by omega) heq
  by_contra hno
  push Not at hno
  have hPge2 : 2 ≤ P := by
    dsimp [P]
    exact Nat.le_self_pow (by omega) 2
  have hsum_lt : K₀ * Eall.card < m * P := by
    rw [hE_eq, Finset.mul_sum]
    have hne : (Finset.Ico 1 P).Nonempty := ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun d hd ↦ by
      obtain ⟨hd1, hd2⟩ := Finset.mem_Ico.mp hd
      exact lt_of_le_of_lt (Nat.mul_le_mul_left K₀ (hdiff_le d)) (hno d hd1 hd2))
    rw [Finset.sum_const, smul_eq_mul] at hlt
    have hcard_ico : (Finset.Ico 1 P).card ≤ P := by simp only [Nat.card_Ico]; omega
    exact lt_of_lt_of_le hlt (by
      calc (Finset.Ico 1 P).card * m ≤ P * m := Nat.mul_le_mul_right m hcard_ico
        _ = m * P := Nat.mul_comm P m)
  have hbig' : m * P ≤ K₀ * Eall.card := hbig
  omega

/-- A fixed positive shift admits a subset retaining at least half of every prefix
and whose representation cap is at most half of the original cap. -/
theorem exists_shift_inter_half_cap_sub {A : Set ℕ} {d k : ℕ} (hd : 0 < d)
    (hcap : ∀ n, sumRep A n ≤ k) :
    ∃ B : Set ℕ, B ⊆ {x | x ∈ A ∧ x + d ∈ A} ∧
      (∀ n, 2 * sumRep B n ≤ k) ∧
      ∀ N, ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard ≤
        2 * (B ∩ Icc 1 N).ncard := by
  classical
  let S : Set ℕ := {x | x ∈ A ∧ x + d ∈ A}
  let sat : ℕ → Prop := fun x ↦ 1 ≤ x ∧ x ∈ S
  let drop := greedyDrop sat (· + d)
  let B : Set ℕ := {x | x ∈ S ∧ ¬ drop x}
  have hdrop (x : ℕ) : drop x ↔ ∃ y < x, sat y ∧ ¬ drop y ∧ y + d = x :=
    greedyDrop_iff sat (· + d) x
  have hsep {x : ℕ} (hx : 1 ≤ x) (hxB : x ∈ B) (hxdB : x + d ∈ B) : False :=
    hxdB.2 ((hdrop (x + d)).mpr ⟨x, by omega, ⟨hx, hxB.1⟩, hxB.2, rfl⟩)
  let C : Set ℕ := {x | 1 ≤ x ∧ x ∈ B}
  refine ⟨C, fun x hx ↦ hx.2.1, ?_, ?_⟩
  · intro n
    let X := (repPairs C n).image Prod.fst
    have hxC (x : ℕ) (hx : x ∈ X) : x ∈ C := by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_repPairs.mp hp).2.1
    have hdisj : Disjoint X (X.image (· + d)) := by
      rw [Finset.disjoint_left]
      intro x hx hxs
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxs
      exact hsep (hxC y hy).1 (hxC y hy).2 (hxC _ hx).2
    have hu := (card_union_fst_shift_le_sumRep (n := n)
      (A := A) (B := C) (d := d) (fun x hx ↦ hx.2.1)).trans (hcap (n + d))
    change (X ∪ X.image (· + d)).card ≤ k at hu
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective X (fun _ _ heq ↦ Nat.add_right_cancel heq)] at hu
    have hX : X.card = sumRep C n := card_fst_repPairs C n
    omega
  · intro N
    rw [← card_prefixSet, ← card_prefixSet]
    change (prefixSet S N).card ≤ 2 * (prefixSet C N).card
    have hkeep : (prefixSet S N).filter (fun x ↦ ¬ drop x) = prefixSet C N := by
      ext x
      simp only [Finset.mem_filter, mem_prefixSet, C, B, Set.mem_ofPred_eq]
      tauto
    let D := (prefixSet S N).filter drop
    have hdcard : D.card ≤ (prefixSet C N).card := by
      refine Finset.card_le_card_of_injOn (· - d) ?_ ?_
      · intro x hx
        simp only [D, Finset.mem_coe, Finset.mem_filter, mem_prefixSet] at hx ⊢
        obtain ⟨y, hy, hyS, hykeep, hyx⟩ := (hdrop x).mp hx.2
        rw [show x - d = y by omega]
        exact ⟨hyS.1, hy.le.trans hx.1.2.1, hyS.1, hyS.2, hykeep⟩
      · intro x hx y hy heq
        simp only [D, Finset.mem_coe, Finset.mem_filter] at hx hy
        change x - d = y - d at heq
        obtain ⟨a, _, _, _, ha⟩ := (hdrop x).mp hx.2
        obtain ⟨b, _, _, _, hb⟩ := (hdrop y).mp hy.2
        omega
    have hsplit := Finset.card_filter_add_card_filter_not (s := prefixSet S N) (p := drop)
    rw [hkeep] at hsplit
    change D.card + (prefixSet C N).card = (prefixSet S N).card at hsplit
    omega

lemma card_reflected_le_sumRep {A : Set ℕ} {n : ℕ} (X : Finset ℕ)
    (hX : ∀ x ∈ X, x ≤ n ∧ x ∈ A ∧ n - x ∈ A) :
    X.card ≤ sumRep A n := by
  rw [← card_repPairs]
  refine Finset.card_le_card_of_injOn (fun x ↦ (x, n - x)) ?_ ?_
  · intro x hx
    obtain ⟨hle, hxA, hsubA⟩ := hX x hx
    exact mem_repPairs.mpr ⟨by dsimp; omega, hxA, hsubA⟩
  · intro x _ y _ heq
    exact congrArg Prod.fst heq

/-- Under cap four, distinct anchors of a rectangle with positive side lengths
are possible only for the collapsed rectangle, and then they are one side length apart. -/
theorem cap_four_rectangle_anchor_gap {A : Set ℕ} (hcap : ∀ n, sumRep A n ≤ 4)
    {d e x y : ℕ} (hd : 0 < d) (he : 0 < e) (hxy : x < y)
    (hx : x ∈ A ∧ x + d ∈ A ∧ x + e ∈ A ∧ x + d + e ∈ A)
    (hy : y ∈ A ∧ y + d ∈ A ∧ y + e ∈ A ∧ y + d + e ∈ A) :
    d = e ∧ y = x + d := by
  classical
  obtain ⟨hx₀, hx₁, hx₂, hx₃⟩ := hx
  obtain ⟨hy₀, hy₁, hy₂, hy₃⟩ := hy
  have hde : d = e := by
    by_contra hn
    let X : Finset ℕ := {x, y, y + d, y + e, y + d + e}
    have hcard : X.card = 5 := by
      dsimp only [X]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      all_goals simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hle := card_reflected_le_sumRep (A := A) (n := x + y + d + e) X (by
      intro z hz
      simp only [X, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h | h
      · subst z
        exact ⟨by omega, hx₀, by rwa [show x + y + d + e - x = y + d + e by omega]⟩
      · subst z
        exact ⟨by omega, hy₀, by rwa [show x + y + d + e - y = x + d + e by omega]⟩
      · subst z
        exact ⟨by omega, hy₁, by rwa [show x + y + d + e - (y + d) = x + e by omega]⟩
      · subst z
        exact ⟨by omega, hy₂, by rwa [show x + y + d + e - (y + e) = x + d by omega]⟩
      · subst z
        exact ⟨by omega, hy₃, by rwa [show x + y + d + e - (y + d + e) = x by omega]⟩)
    have := hle.trans (hcap _)
    omega
  subst e
  refine ⟨rfl, ?_⟩
  by_contra hn
  let X : Finset ℕ := {x, x + d, x + d + d, y + d, y + d + d}
  have hcard : X.card = 5 := by
    dsimp only [X]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hle := card_reflected_le_sumRep (A := A) (n := x + y + d + d) X (by
    intro z hz
    simp only [X, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h | h | h
    · subst z
      exact ⟨by omega, hx₀, by rwa [show x + y + d + d - x = y + d + d by omega]⟩
    · subst z
      exact ⟨by omega, hx₁, by rwa [show x + y + d + d - (x + d) = y + d by omega]⟩
    · subst z
      exact ⟨by omega, hx₃, by rwa [show x + y + d + d - (x + d + d) = y by omega]⟩
    · subst z
      exact ⟨by omega, hy₁, by rwa [show x + y + d + d - (y + d) = x + d by omega]⟩
    · subst z
      exact ⟨by omega, hy₃, by rwa [show x + y + d + d - (y + d + d) = x by omega]⟩)
  have := hle.trans (hcap _)
  omega

lemma sumRep_le_two_of_unique_shifts {A : Set ℕ}
    (huniq : ∀ d : ℕ, 0 < d → {x | x ∈ A ∧ x + d ∈ A}.Subsingleton) :
    ∀ n, sumRep A n ≤ 2 := by
  classical
  intro n
  by_cases hne : (repPairs A n).Nonempty
  · obtain ⟨⟨a, b⟩, hp⟩ := hne
    rw [← card_repPairs]
    refine (Finset.card_le_card (t := {(a, b), (b, a)}) ?_).trans Finset.card_le_two
    rintro ⟨c, e⟩ hq
    obtain ⟨hab, ha, hb⟩ := mem_repPairs.mp hp
    obtain ⟨hce, hc, he⟩ := mem_repPairs.mp hq
    change a + b = n at hab
    change c + e = n at hce
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    rcases lt_trichotomy a c with hlt | heq | hlt
    · have h := huniq (c - a) (by omega) (show a ∈ {x | x ∈ A ∧ x + (c - a) ∈ A} from
        ⟨ha, by rwa [show a + (c - a) = c by omega]⟩)
        (show e ∈ {x | x ∈ A ∧ x + (c - a) ∈ A} from
          ⟨he, by rwa [show e + (c - a) = b by omega]⟩)
      exact Or.inr ⟨by omega, h.symm⟩
    · exact Or.inl ⟨heq.symm, by omega⟩
    · have h := huniq (a - c) (by omega) (show c ∈ {x | x ∈ A ∧ x + (a - c) ∈ A} from
        ⟨hc, by rwa [show c + (a - c) = a by omega]⟩)
        (show b ∈ {x | x ∈ A ∧ x + (a - c) ∈ A} from
          ⟨hb, by rwa [show b + (a - c) = e by omega]⟩)
      exact Or.inr ⟨h, by omega⟩
  · rw [← card_repPairs, Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    omega

/-- Each positive shift intersection of a cap-four set becomes Sidon after
removing at most one element. -/
theorem cap_four_shift_inter_sidon_except_one {A : Set ℕ} (hcap : ∀ n, sumRep A n ≤ 4)
    {d : ℕ} (hd : 0 < d) :
    ∃ a : ℕ, ∀ n, sumRep ({x | x ∈ A ∧ x + d ∈ A} \ {a}) n ≤ 2 := by
  classical
  let S : Set ℕ := {x | x ∈ A ∧ x + d ∈ A}
  let T : Set ℕ := {x | x ∈ S ∧ x + d ∈ S}
  have hrect {e x y : ℕ} (he : 0 < e) (hxy : x < y) (hx : x ∈ S) (hxe : x + e ∈ S)
      (hy : y ∈ S) (hye : y + e ∈ S) : d = e ∧ y = x + d := by
    exact cap_four_rectangle_anchor_gap hcap hd he hxy
      ⟨hx.1, hx.2, hxe.1, by simpa only [Nat.add_right_comm] using hxe.2⟩
      ⟨hy.1, hy.2, hye.1, by simpa only [Nat.add_right_comm] using hye.2⟩
  by_cases hT : T.Nonempty
  · obtain ⟨a, ha⟩ := hT
    refine ⟨a, sumRep_le_two_of_unique_shifts ?_⟩
    intro e he
    suffices hlt : ∀ {x y : ℕ}, x < y → x ∈ (S \ {a}) → x + e ∈ (S \ {a}) →
        y ∈ (S \ {a}) → y + e ∈ (S \ {a}) → False by
      intro x hx y hy
      rcases lt_trichotomy x y with h | h | h
      · exact (hlt h hx.1 hx.2 hy.1 hy.2).elim
      · exact h
      · exact (hlt h hy.1 hy.2 hx.1 hx.2).elim
    intro x y hxy hx hxe hy hye
    obtain ⟨rfl, hyx⟩ := hrect he hxy hx.1 hxe.1 hy.1 hye.1
    have hxne : x ≠ a := hx.2
    have hyne : y ≠ a := hy.2
    have hstep {u v : ℕ} (hu : u ∈ T) (hv : v ∈ T) (hlt : u < v) : v = u + d :=
      (hrect hd hlt hu.1 hu.2 hv.1 hv.2).2
    have hxT : x ∈ T := ⟨hx.1, hxe.1⟩
    have hyT : y ∈ T := ⟨hy.1, hye.1⟩
    rcases lt_or_gt_of_ne hxne with hxa | hax
    · have := hstep hxT ha hxa
      omega
    · have := hstep ha hxT hax
      have := hstep ha hyT (by omega)
      omega
  · refine ⟨0, sumRep_le_two_of_unique_shifts ?_⟩
    intro e he
    suffices hlt : ∀ {x y : ℕ}, x < y → x ∈ S → x + e ∈ S →
        y ∈ S → y + e ∈ S → False by
      intro x hx y hy
      rcases lt_trichotomy x y with h | h | h
      · exact (hlt h hx.1.1 hx.2.1 hy.1.1 hy.2.1).elim
      · exact h
      · exact (hlt h hy.1.1 hy.2.1 hx.1.1 hx.2.1).elim
    intro x y hxy hx hxe hy hye
    obtain ⟨rfl, _⟩ := hrect he hxy hx hxe hy hye
    exact hT ⟨x, hx, hxe⟩

/-- Partition short pairs by their positive difference. -/
lemma short_diff_pairs_sum (S : Finset ℕ) (P : ℕ) :
    ((S ×ˢ S).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)).card =
      ∑ d ∈ Finset.Ico 1 P, (diffPairs S d).card := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Ico 1 P) : Set ℕ) (diffPairs S) := by
    intro d _ e _ hde
    change Disjoint (diffPairs S d) (diffPairs S e)
    rw [Finset.disjoint_left]
    intro p hd he
    exact hde ((mem_diffPairs.mp hd).2.2.2.symm.trans (mem_diffPairs.mp he).2.2.2)
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_Ico,
    mem_diffPairs]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hlt, hP⟩
    exact ⟨p.1 - p.2, ⟨by omega, hP⟩, h₁, h₂, hlt, rfl⟩
  · rintro ⟨_, ⟨_, hP⟩, h₁, h₂, hlt, rfl⟩
    exact ⟨⟨h₁, h₂⟩, hlt, hP⟩

/-- At every sufficiently large dyadic scale, a positive proportion of directions
have at least `L` witnesses within a fixed multiple of that scale. The
proportion and the multiple may depend on `L`. -/
theorem cap_popular_differences_in_linear_window {A : Set ℕ} {k : ℕ}
    (hcap : ∀ n, sumRep A n ≤ k)
    (hdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ)))
    (L : ℕ) :
    ∃ K t : ℕ, 0 < K ∧ ∀ m ≥ t,
      2 ^ m ≤ K * ((Finset.Ico 1 (2 ^ m)).filter
        (fun d ↦ L ≤ (diffPairs (prefixSet A (2 ^ (m + t))) d).card)).card := by
  classical
  obtain ⟨K₀, t₀, hK₀, hpairs⟩ := cap_close_pairs_in_dyadic_window hcap hdense
  let t := max t₀ (K₀ * (L + 1))
  refine ⟨k * (2 * k * 2 ^ t) + 1, t, by omega, fun m hm ↦ ?_⟩
  let P : ℕ := 2 ^ m
  let N : ℕ := 2 ^ (m + t)
  let S := prefixSet A N
  let f (d : ℕ) : ℕ := (diffPairs S d).card
  let I := Finset.Ico 1 P
  let D := I.filter (fun d ↦ L ≤ f d)
  let U := I.filter (fun d ↦ ¬ L ≤ f d)
  have htotal := hpairs m t (le_max_left _ _) hm
  change t * P ≤ K₀ * ((S ×ˢ S).filter (fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < P)).card at htotal
  rw [short_diff_pairs_sum] at htotal
  change t * P ≤ K₀ * ∑ d ∈ I, f d at htotal
  have hlarge : (L + 1) * P ≤ ∑ d ∈ I, f d := by
    apply Nat.le_of_mul_le_mul_left _ hK₀
    calc K₀ * ((L + 1) * P) = (K₀ * (L + 1)) * P := by ring
      _ ≤ t * P := Nat.mul_le_mul_right _ (le_max_right _ _)
      _ ≤ _ := htotal
  have hU : ∑ d ∈ U, f d ≤ L * P := by
    calc ∑ d ∈ U, f d ≤ ∑ _d ∈ U, L := by
          refine Finset.sum_le_sum fun d hd ↦ ?_
          exact (lt_of_not_ge (Finset.mem_filter.mp hd).2).le
      _ = U.card * L := by simp
      _ ≤ P * L := Nat.mul_le_mul_right _ (by
        have hcard := Finset.card_le_card (Finset.filter_subset (s := I) (fun d ↦ ¬ L ≤ f d))
        have hI : I.card ≤ P := by simp [I, Nat.card_Ico]
        exact hcard.trans hI)
      _ = L * P := Nat.mul_comm _ _
  have hsplit : (∑ d ∈ D, f d) + (∑ d ∈ U, f d) = ∑ d ∈ I, f d :=
    Finset.sum_filter_add_sum_filter_not I (fun d ↦ L ≤ f d) f
  have hmass : P ≤ ∑ d ∈ D, f d := by
    rw [Nat.add_mul, one_mul] at hlarge
    omega
  have hsubset : D ⊆ Finset.Ico 1 N := by
    intro d hd
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hd).1
    exact Finset.mem_Ico.mpr ⟨hlo, hhi.trans_le (Nat.pow_le_pow_right (by decide) (by omega))⟩
  have henergy := cap_diff_sq_sum_le hcap N
  have hprefix : S.card ^ 2 ≤ 2 * k * N := by
    rw [card_prefixSet]
    exact cap_prefix_sq_le hcap N
  have he2 : ∑ d ∈ D, f d ^ 2 ≤ k * (2 * k * N) := by
    calc ∑ d ∈ D, f d ^ 2 ≤ ∑ d ∈ Finset.Ico 1 N, f d ^ 2 :=
          Finset.sum_le_sum_of_subset hsubset
      _ ≤ k * S.card ^ 2 := by
        change S.card ^ 2 + 2 * (∑ d ∈ Finset.Ico 1 N, f d ^ 2) ≤ k * S.card ^ 2 at henergy
        omega
      _ ≤ _ := Nat.mul_le_mul_left _ hprefix
  have hsq : P ^ 2 ≤ D.card * (k * (2 * k * N)) :=
    (Nat.pow_le_pow_left hmass _).trans
      ((sq_sum_le_card_mul_sum_sq_nat D f).trans (Nat.mul_le_mul_left _ he2))
  change P ≤ (k * (2 * k * 2 ^ t) + 1) * D.card
  have hN : N = P * 2 ^ t := pow_add 2 m t
  rw [hN] at hsq
  have hmul : P * P ≤ P * (k * (2 * k * 2 ^ t) * D.card) := by
    calc P * P = P ^ 2 := by ring
      _ ≤ D.card * (k * (2 * k * (P * 2 ^ t))) := hsq
      _ = P * (k * (2 * k * 2 ^ t) * D.card) := by ring
  have hP : 0 < P := Nat.pow_pos (by decide)
  exact (Nat.le_of_mul_le_mul_left hmul hP).trans
    (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- Count unordered representations by their smaller coordinates. The diagonal
is the only representation with just one orientation. -/
lemma lower_rep_card_le {A : Set ℕ} {n : ℕ} (X : Finset ℕ)
    (hX : ∀ x ∈ X, x ≤ n - x ∧ x ≤ n ∧ x ∈ A ∧ n - x ∈ A) :
    2 * X.card ≤ sumRep A n + 1 := by
  classical
  let Y := X.image (n - ·)
  have hY : Y.card = X.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb heq
    have ha' := (hX a ha).2.1
    have hb' := (hX b hb).2.1
    change n - a = n - b at heq
    omega
  have hI : (X ∩ Y).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have hdiag (u : ℕ) (hu : u ∈ X ∩ Y) : u + u = n := by
      obtain ⟨huX, huY⟩ := Finset.mem_inter.mp hu
      obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp huY
      have hu' := hX u huX
      have hv' := hX v hv
      change n - v = u at hvu
      omega
    have := hdiag a ha
    have := hdiag b hb
    omega
  have hU := card_reflected_le_sumRep (A := A) (n := n) (X ∪ Y) (by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact (hX u h).2
    · obtain ⟨v, hv, huv⟩ := Finset.mem_image.mp h
      have ⟨_, hvle, hvA, hvsub⟩ := hX v hv
      change n - v = u at huv
      rw [← huv, show n - (n - v) = v by omega]
      exact ⟨Nat.sub_le _ _, hvsub, hvA⟩)
  have hcard := Finset.card_union_add_card_inter X Y
  omega

/-- For a cap-four set, a rectangle with the shorter side designated as its
shift is determined by the common sum of its two opposite pairs. -/
theorem cap_four_rectangle_sum_inj {A : Set ℕ} (hcap : ∀ n, sumRep A n ≤ 4) :
    Set.InjOn (fun t : ℕ × ℕ × ℕ ↦ t.2.1 + t.2.2 + t.1)
      {t | 0 < t.1 ∧ t.2.1 + t.1 ≤ t.2.2 ∧
        t.2.1 ∈ A ∧ t.2.1 + t.1 ∈ A ∧ t.2.2 ∈ A ∧ t.2.2 + t.1 ∈ A} := by
  classical
  rintro ⟨d, x, y⟩ hd ⟨e, u, v⟩ he hsum
  change x + y + d = u + v + e at hsum
  obtain ⟨hd, hxy, hx, hxd, hy, hyd⟩ := hd
  obtain ⟨he, huv, hu, hue, hv, hve⟩ := he
  dsimp only at hd hxy he huv
  let n := x + y + d
  let F := ((repPairs A n).image Prod.fst).filter (fun a ↦ a ≤ n - a)
  have hF (a : ℕ) : a ∈ F ↔ a ≤ n - a ∧ a ≤ n ∧ a ∈ A ∧ n - a ∈ A := by
    constructor
    · intro ha
      obtain ⟨haF, hle⟩ := Finset.mem_filter.mp ha
      obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp haF
      obtain ⟨hpsum, hp₁, hp₂⟩ := mem_repPairs.mp hp
      exact ⟨hle, by omega, hpa ▸ hp₁, by rwa [show n - a = p.2 by omega]⟩
    · rintro ⟨hle, han, ha, hna⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a, n - a), ?_, rfl⟩, hle⟩
      exact mem_repPairs.mpr ⟨by dsimp; omega, ha, hna⟩
  have hFcard : F.card ≤ 2 := by
    have h := lower_rep_card_le F (fun a ha ↦ (hF a).mp ha)
    have := hcap n
    omega
  have hxF : x ∈ F := (hF x).mpr
    ⟨by dsimp [n]; omega, by dsimp [n]; omega, hx, by rwa [show n - x = y + d by dsimp [n]; omega]⟩
  have hxdF : x + d ∈ F := (hF (x + d)).mpr
    ⟨by dsimp [n]; omega, by dsimp [n]; omega, hxd, by rwa [show n - (x + d) = y by dsimp [n]; omega]⟩
  have huF : u ∈ F := (hF u).mpr
    ⟨by dsimp [n]; omega, by dsimp [n]; omega, hu, by rwa [show n - u = v + e by dsimp [n]; omega]⟩
  have hueF : u + e ∈ F := (hF (u + e)).mpr
    ⟨by dsimp [n]; omega, by dsimp [n]; omega, hue, by rwa [show n - (u + e) = v by dsimp [n]; omega]⟩
  have heq (a b : ℕ) (hab : a < b) (ha : a ∈ F) (hb : b ∈ F) :
      ({a, b} : Finset ℕ) = F := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
    · rwa [Finset.card_insert_of_notMem (by simpa using hab.ne), Finset.card_singleton]
  rw [← heq x (x + d) (by omega) hxF hxdF] at hueF huF
  simp only [Finset.mem_insert, Finset.mem_singleton] at hueF huF
  have hxu : x = u := by omega
  have hde : d = e := by omega
  have hyv : y = v := by omega
  exact Prod.ext hde (Prod.ext hxu hyv)

/-- The positive-proportion bound for repeated differences holds at every
sufficiently large scale, with all witnesses inside a fixed multiple of the scale. -/
theorem cap_popular_differences_in_linear_prefix {A : Set ℕ} {k : ℕ}
    (hcap : ∀ n, sumRep A n ≤ k)
    (hdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ)))
    (L : ℕ) :
    ∃ K M P₀ : ℕ, 0 < K ∧ 1 ≤ M ∧ ∀ P ≥ P₀,
      P ≤ K * ((Finset.Ico 1 P).filter
        (fun d ↦ L ≤ (diffPairs (prefixSet A (M * P)) d).card)).card := by
  classical
  obtain ⟨K, t, hK, hpop⟩ := cap_popular_differences_in_linear_window hcap hdense L
  refine ⟨2 * K, 2 ^ t, 2 ^ t, by omega, Nat.one_le_pow _ _ (by decide), fun P hP ↦ ?_⟩
  let m := Nat.log 2 P
  have htm : t ≤ m := Nat.le_log_of_pow_le (by decide) hP
  have hPpos : 0 < P := (Nat.pow_pos (by decide : 0 < 2) (n := t)).trans_le hP
  have hmP : 2 ^ m ≤ P := Nat.pow_log_le_self 2 hPpos.ne'
  have hPm : P ≤ 2 * 2 ^ m := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) P
    change P < 2 ^ (m + 1) at h
    rw [pow_succ, Nat.mul_comm] at h
    exact h.le
  have hmul : 2 ^ (m + t) ≤ 2 ^ t * P := by
    rw [pow_add, Nat.mul_comm (2 ^ m)]
    exact Nat.mul_le_mul_left _ hmP
  have hmono (d : ℕ) :
      (diffPairs (prefixSet A (2 ^ (m + t))) d).card ≤
        (diffPairs (prefixSet A (2 ^ t * P)) d).card := by
    refine Finset.card_le_card fun p hp ↦ ?_
    simp only [mem_diffPairs, mem_prefixSet] at hp ⊢
    obtain ⟨⟨h₁lo, h₁hi, h₁A⟩, ⟨h₂lo, h₂hi, h₂A⟩, hlt, hdiff⟩ := hp
    exact ⟨⟨h₁lo, h₁hi.trans hmul, h₁A⟩, ⟨h₂lo, h₂hi.trans hmul, h₂A⟩, hlt, hdiff⟩
  have hsub :
      ((Finset.Ico 1 (2 ^ m)).filter (fun d ↦ L ≤ (diffPairs (prefixSet A (2 ^ (m + t))) d).card)) ⊆
      ((Finset.Ico 1 P).filter (fun d ↦ L ≤ (diffPairs (prefixSet A (2 ^ t * P)) d).card)) := by
    intro d hd
    obtain ⟨hdi, hdL⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd₁, hd₂⟩ := Finset.mem_Ico.mp hdi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hd₁, hd₂.trans_le hmP⟩, hdL.trans (hmono d)⟩
  rw [mul_assoc]
  exact hPm.trans (Nat.mul_le_mul_left 2 ((hpop m htm).trans
    (Nat.mul_le_mul_left K (Finset.card_le_card hsub))))

/-- Three occurrences of a positive difference give a rectangle whose four
vertices are distinct. -/
lemma exists_nondegenerate_rectangle_of_diffPairs {S : Finset ℕ} {d : ℕ}
    (h : 3 ≤ (diffPairs S d).card) :
    ∃ x y, x < y ∧ x + d ≠ y ∧ x ∈ S ∧ x + d ∈ S ∧ y ∈ S ∧ y + d ∈ S := by
  classical
  let F := (diffPairs S d).image Prod.snd
  have hFcard : F.card = (diffPairs S d).card := by
    refine Finset.card_image_of_injOn ?_
    intro p hp q hq heq
    obtain ⟨_, _, hp₂, hp₃⟩ := mem_diffPairs.mp hp
    obtain ⟨_, _, hq₂, hq₃⟩ := mem_diffPairs.mp hq
    exact Prod.ext (by omega) heq
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  let x := F.min' hFne
  have hx : x ∈ F := Finset.min'_mem _ _
  have hf (z : ℕ) (hz : z ∈ F) : z ∈ S ∧ z + d ∈ S := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h₁, h₂, hlt, hdiff⟩ := mem_diffPairs.mp hp
    exact ⟨h₂, by rwa [show p.2 + d = p.1 by omega]⟩
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ F, y ∉ ({x, x + d} : Finset ℕ) := by
    by_contra! hnone
    have hle := (Finset.card_le_card (show F ⊆ {x, x + d} from hnone)).trans Finset.card_le_two
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyne
  have hxy := lt_of_le_of_ne (Finset.min'_le F y hy) (fun heq ↦ hyne.1 heq.symm)
  exact ⟨x, y, hxy, (fun heq ↦ hyne.2 heq.symm), (hf x hx).1, (hf x hx).2, (hf y hy).1, (hf y hy).2⟩

/-- A square-root-dense cap-four set must saturate its cap on a positive
proportion of sums in every sufficiently large prefix. -/
theorem cap_four_saturated_sums_in_linear_prefix {A : Set ℕ}
    (hcap : ∀ n, sumRep A n ≤ 4)
    (hdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) :
    ∃ C M P₀ : ℕ, 0 < C ∧ 1 ≤ M ∧ ∀ P ≥ P₀,
      P ≤ C * ((Finset.Icc 1 (2 * M * P)).filter (fun n ↦ sumRep A n = 4)).card := by
  classical
  obtain ⟨K, M, P₀, hK, hM, hpop⟩ := cap_popular_differences_in_linear_prefix hcap hdense 3
  refine ⟨K * 2, M, P₀, by positivity, hM, fun P hP ↦ ?_⟩
  let S := prefixSet A (M * P)
  let D := (Finset.Ico 1 P).filter (fun d ↦ 3 ≤ (diffPairs S d).card)
  let R := (Finset.Icc 1 (2 * M * P)).filter (fun n ↦ sumRep A n = 4)
  have hdir (d : D) : 0 < (d : ℕ) :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp d.property).1).1
  have hvertices (d : D) : ∃ x y, x < y ∧ x + (d : ℕ) ≠ y ∧ x ∈ S ∧ x + (d : ℕ) ∈ S ∧
      y ∈ S ∧ y + (d : ℕ) ∈ S :=
    exists_nondegenerate_rectangle_of_diffPairs (Finset.mem_filter.mp d.property).2
  choose x y hw using hvertices
  let t (d : D) : ℕ × ℕ × ℕ :=
    if x d + (d : ℕ) ≤ y d then (d, x d, y d) else (y d - x d, x d, x d + (d : ℕ))
  let f (d : D) : ℕ × Bool :=
    ((t d).2.1 + (t d).2.2 + (t d).1, decide (x d + (d : ℕ) ≤ y d))
  have hsum (d : D) : (f d).1 = x d + y d + (d : ℕ) := by
    have hxy := (hw d).1
    by_cases h : x d + (d : ℕ) ≤ y d
    · simp [f, t, h]
    · simp only [f, t, if_neg h]; omega
  have ht (d : D) : 0 < (t d).1 ∧ (t d).2.1 + (t d).1 ≤ (t d).2.2 ∧
      (t d).2.1 ∈ A ∧ (t d).2.1 + (t d).1 ∈ A ∧
      (t d).2.2 ∈ A ∧ (t d).2.2 + (t d).1 ∈ A := by
    obtain ⟨hxy, _, hx, hxd, hy, hyd⟩ := hw d
    have hxA := (mem_prefixSet.mp hx).2.2
    have hxdA := (mem_prefixSet.mp hxd).2.2
    have hyA := (mem_prefixSet.mp hy).2.2
    have hydA := (mem_prefixSet.mp hyd).2.2
    by_cases h : x d + (d : ℕ) ≤ y d
    · simpa only [t, if_pos h] using And.intro (hdir d) (And.intro h ⟨hxA, hxdA, hyA, hydA⟩)
    · simp only [t, if_neg h]
      refine ⟨by omega, by omega, hxA, ?_, hxdA, ?_⟩
      · rwa [show x d + (y d - x d) = y d by omega]
      · rwa [show x d + (d : ℕ) + (y d - x d) = y d + (d : ℕ) by omega]
  have hdecode (d : D) :
      (if (f d).2 then (t d).1 else (t d).2.2 - (t d).2.1) = (d : ℕ) := by
    by_cases h : x d + (d : ℕ) ≤ y d <;> simp [f, t, h]
  have hf (d : D) : (f d).1 ∈ R := by
    rw [hsum]
    obtain ⟨hxy, hne, hx, hxd, hy, hyd⟩ := hw d
    obtain ⟨_, hxhi, hxA⟩ := mem_prefixSet.mp hx
    obtain ⟨_, _, hxdA⟩ := mem_prefixSet.mp hxd
    obtain ⟨_, _, hyA⟩ := mem_prefixSet.mp hy
    obtain ⟨_, hydhi, hydA⟩ := mem_prefixSet.mp hyd
    have hd := hdir d
    let n := x d + y d + (d : ℕ)
    have hnle : n ≤ 2 * M * P := by
      rw [show 2 * M * P = M * P + M * P by ring]
      dsimp [n]
      omega
    let X : Finset ℕ := {x d, x d + (d : ℕ), y d, y d + (d : ℕ)}
    have hXcard : X.card = 4 := by
      dsimp only [X]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      all_goals simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hrep := card_reflected_le_sumRep (A := A) (n := n) X (by
      intro a ha
      simp only [X, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact ⟨by dsimp [n]; omega, hxA, by rwa [show n - x d = y d + (d : ℕ) by dsimp [n]; omega]⟩
      · exact ⟨by dsimp [n]; omega, hxdA, by rwa [show n - (x d + (d : ℕ)) = y d by dsimp [n]; omega]⟩
      · exact ⟨by dsimp [n]; omega, hyA, by rwa [show n - y d = x d + (d : ℕ) by dsimp [n]; omega]⟩
      · exact ⟨by dsimp [n]; omega, hydA, by rwa [show n - (y d + (d : ℕ)) = x d by dsimp [n]; omega]⟩)
    rw [hXcard] at hrep
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by change 1 ≤ x d + y d + (d : ℕ); omega, hnle⟩,
      le_antisymm (hcap n) hrep⟩
  have hc : (Finset.univ : Finset D).card ≤ (R ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro d _
      exact Finset.mem_product.mpr ⟨hf d, Finset.mem_univ _⟩
    · intro d _ e _ h
      have hs : (t d).2.1 + (t d).2.2 + (t d).1 = (t e).2.1 + (t e).2.2 + (t e).1 :=
        congrArg Prod.fst h
      have htde := cap_four_rectangle_sum_inj hcap (ht d) (ht e) hs
      have hb := congrArg Prod.snd h
      have hdecode_d := hdecode d
      rw [htde, hb] at hdecode_d
      exact Subtype.ext (hdecode_d.symm.trans (hdecode e))
  simp only [Finset.card_univ, Fintype.card_coe, Finset.card_product, Fintype.card_bool] at hc
  exact (hpop P hP).trans (by
    change K * D.card ≤ (K * 2) * R.card
    calc K * D.card ≤ K * (R.card * 2) := Nat.mul_le_mul_left K hc
      _ = _ := by ring)

/-- Open core: a putative counterexample has no square-root-dense positive
shift intersection, has logarithmically repeated short differences at scale
`P^2`, and has a positive proportion of directions of each fixed multiplicity
already at scale `M * P`. -/
theorem even_cap_popular_differences_not_sqrt_dense :
    ∀ g : ℕ, 2 ≤ g → ∀ A : Set ℕ, (∀ n, sumRep A n ≤ 2 * g) →
      (∀ d : ℕ, 0 < d →
        ¬ ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop]
          (fun N ↦ (({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard : ℝ)))) →
      (∃ K₀ m₀ : ℕ, 0 < K₀ ∧ ∀ m : ℕ, m₀ ≤ m →
        ∃ d : ℕ, 0 < d ∧ d < 2 ^ m ∧
          m ≤ K₀ * ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 (2 ^ (2 * m))).ncard) →
      (∀ L : ℕ, ∃ K M P₀ : ℕ, 0 < K ∧ 1 ≤ M ∧ ∀ P ≥ P₀,
        P ≤ K * ((Finset.Ico 1 P).filter
          (fun d ↦ L ≤ (diffPairs (prefixSet A (M * P)) d).card)).card) →
      ¬ ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) := by
  sorry

theorem even_cap_no_dense_shift_not_sqrt_dense :
    ∀ g : ℕ, 2 ≤ g → ∀ A : Set ℕ, (∀ n, sumRep A n ≤ 2 * g) →
      (∀ d : ℕ, 0 < d →
        ¬ ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop]
          (fun N ↦ (({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard : ℝ)))) →
      (∃ K₀ m₀ : ℕ, 0 < K₀ ∧ ∀ m : ℕ, m₀ ≤ m →
        ∃ d : ℕ, 0 < d ∧ d < 2 ^ m ∧
          m ≤ K₀ * ({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 (2 ^ (2 * m))).ncard) →
      ¬ ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) := by
  intro g hg A hcap hshift hlog hdense
  exact even_cap_popular_differences_not_sqrt_dense g hg A hcap hshift hlog
    (cap_popular_differences_in_linear_prefix hcap hdense) hdense

/-- Reduction from arbitrary global cap `k` to the even no-dense-shift core via odd thinning,
positive-shift cap lowering, and sharp logarithmic difference multiplicity at scale `P^2`. -/
theorem bounded_cap_not_sqrt_dense (k : ℕ) :
    ∀ A : Set ℕ, (∀ n, sumRep A n ≤ k) →
      ¬ ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((A ∩ Icc 1 N).ncard : ℝ))) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro A hcap hdense
    by_cases h3 : k ≤ 3
    · exact cap_three_not_sqrt_dense (fun n ↦ (hcap n).trans h3) hdense
    · by_cases hodd : k % 2 = 1
      · let h := k / 2
        have hh : 1 ≤ h := by omega
        have hk : k = 2 * h + 1 := by omega
        obtain ⟨B, _, hBcap, hprefix⟩ := exists_even_cap_sub hh (hk ▸ hcap)
        have hBdense : (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((B ∩ Icc 1 N).ncard : ℝ)) :=
          hdense.trans (Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun N ↦ by
            simp only [Real.norm_natCast]
            exact_mod_cast hprefix N))
        exact ih (2 * h) (by omega) B hBcap hBdense
      · let g := k / 2
        have hg : 2 ≤ g := by omega
        have hk : k = 2 * g := by omega
        by_cases hshift : ∃ d : ℕ, 0 < d ∧
            ((fun N : ℕ ↦ √(N : ℝ)) =O[atTop]
              (fun N ↦ (({x | x ∈ A ∧ x + d ∈ A} ∩ Icc 1 N).ncard : ℝ)))
        · obtain ⟨d, hd, hSdense⟩ := hshift
          obtain ⟨B, _, hBcap, hprefix⟩ := exists_shift_inter_half_cap_sub hd hcap
          have hBdense :
              (fun N : ℕ ↦ √(N : ℝ)) =O[atTop] (fun N ↦ ((B ∩ Icc 1 N).ncard : ℝ)) :=
            hSdense.trans (Asymptotics.IsBigO.of_bound 2
              (Eventually.of_forall fun N ↦ by
                simp only [Real.norm_natCast]
                exact_mod_cast hprefix N))
          exact ih g (by omega) B (fun n ↦ by have := hBcap n; omega) hBdense
        · exact even_cap_no_dense_shift_not_sqrt_dense g hg A (hk ▸ hcap)
            (fun d hd hD ↦ hshift ⟨d, hd, hD⟩)
            (cap_log_diff_mult_at_sq hcap hdense) hdense

end Erdos40WeakerPartial

theorem OMA.solution : type_of% @Erdos40.erdos_40.variants.weaker := by
  apply Erdos40WeakerPartial.weaker_of_constant_one
  intro A hA
  by_contra hne
  obtain ⟨k, hk⟩ := Erdos40WeakerPartial.exists_global_cap_of_limsup_ne_top hne
  exact Erdos40WeakerPartial.bounded_cap_not_sqrt_dense k A hk (by simpa only [div_one] using hA)
