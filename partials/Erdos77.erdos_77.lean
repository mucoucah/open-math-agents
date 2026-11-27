import FormalConjectures.ErdosProblems.«77»
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-! Diagonal Ramsey numbers and bounds on their possible exponential growth rate. -/

-- Problem: Erdős Problem 77 (it asks for a value)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/77.lean:54 (declaration Erdos77.erdos_77; placeholder Erdos77.erdos_77.answer := sorry)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Give the value explicitly as OMA.answer (same type as the placeholder; not built from Erdos77.…,
-- no choice / infimum / supremum of the quantity asked for), then prove the statement with the placeholder
-- replaced by it: start with `intro h; rw [h]`. No sorry, no axiom, no native_decide. A person checks the answer.

namespace OMA.DiagonalRamsey

open SimpleGraph
open scoped Topology

private lemma graph_ramsey_choose (a b : ℕ)
    (G : SimpleGraph (Fin (Nat.choose (a + b) a))) :
    (completeGraph (Fin a)).IsContained G ∨ (completeGraph (Fin b)).IsContained Gᶜ := by
  classical
  let c (e : Finset (Fin (Nat.choose (a + b) a))) : Bool :=
    decide (∃ x ∈ e, ∃ y ∈ e, G.Adj x y)
  have hc (x y) (hxy : x ≠ y) : c {x, y} = true ↔ G.Adj x y := by
    simp [c, Finset.mem_insert, G.adj_comm y x]
  obtain ⟨S, _, hcard, hS⟩ | ⟨S, _, hcard, hS⟩ :=
    Combinatorics.Diagonal.hasRamseyProperty_choose b a
      (m := Nat.choose (a + b) a)
      (c := c) (V := Finset.univ) (by
        rw [Finset.card_univ, Fintype.card_fin, Nat.add_comm b a, ← Nat.choose_symm_add])
  · right
    apply (not_cliqueFree_iff_top_isContained b).mp
    refine IsNClique.not_cliqueFree (s := S) ⟨?_, hcard⟩
    intro x hx y hy hxy
    have hcolor := hS {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) (by simp [hxy])
    exact ⟨hxy, fun h => Bool.noConfusion (hcolor.symm.trans ((hc x y hxy).mpr h))⟩
  · left
    apply (not_cliqueFree_iff_top_isContained a).mp
    refine IsNClique.not_cliqueFree (s := S) ⟨?_, hcard⟩
    intro x hx y hy hxy
    exact (hc x y hxy).mp (hS {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) (by simp [hxy]))

private lemma diagonal_ramsey_le (k : ℕ) : diagonalRamsey k ≤ 4 ^ k := by
  have h : diagonalRamsey k ≤ Nat.choose (k + k) k :=
    Nat.sInf_le (graph_ramsey_choose k k)
  rw [← two_mul] at h
  exact h.trans (Nat.centralBinom_le_four_pow k)

private lemma rpow_nat_root {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : k ≠ 0) :
    (x ^ k) ^ (1 / (k : ℝ)) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_one_div_cancel, Real.rpow_one]
  exact_mod_cast hk

private lemma ramsey_root_le_four {k : ℕ} (hk : k ≠ 0) :
    (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)) ≤ 4 := by
  rw [← rpow_nat_root (x := 4) (by norm_num) hk]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact_mod_cast diagonal_ramsey_le k

private lemma ramsey_limit_le_four {L : ℝ}
    (hL : Filter.Tendsto (fun k : ℕ => (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (𝓝 L)) : L ≤ 4 := by
  apply le_of_tendsto hL
  exact Filter.eventually_atTop.mpr ⟨1, fun _ hk => ramsey_root_le_four (by omega)⟩

private lemma ramsey_property_at_number (k : ℕ)
    (G : SimpleGraph (Fin (diagonalRamsey k))) :
    (completeGraph (Fin k)).IsContained G ∨ (completeGraph (Fin k)).IsContained Gᶜ := by
  let S := {n : ℕ | ∀ C : SimpleGraph (Fin n),
    (completeGraph (Fin k)).IsContained C ∨ (completeGraph (Fin k)).IsContained Cᶜ}
  have hmem : sInf S ∈ S := Nat.sInf_mem ⟨_, graph_ramsey_choose k k⟩
  exact hmem G

private lemma lt_ramsey_of_cliqueFree {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree k) (hGc : Gᶜ.CliqueFree k) :
    n < diagonalRamsey k := by
  by_contra! h
  let e : Fin (diagonalRamsey k) ↪ Fin n := Fin.castLEEmb h
  let f := Embedding.comap e G
  rcases ramsey_property_at_number k (G.comap e) with hK | hK
  · exact (hK.trans f.isContained).not_cliqueFree hG
  · exact (hK.trans (Embedding.complEquiv f).isContained).not_cliqueFree hGc

private noncomputable def constantColourings {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : Bool) : Finset (α → Bool) := by
  classical
  exact Finset.univ.filter (fun c => ∀ e ∈ s, c e = b)

private lemma mem_constantColourings {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} {b : Bool} {c : α → Bool} :
    c ∈ constantColourings s b ↔ ∀ e ∈ s, c e = b := by
  classical
  simp [constantColourings]

private lemma card_constantColourings {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : Bool) :
    (constantColourings s b).card ≤ 2 ^ (Fintype.card α - s.card) := by
  classical
  let f (c : constantColourings s b) (e : {e : α // e ∉ s}) := c.val e.val
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    funext e
    by_cases he : e ∈ s
    · exact ((mem_constantColourings.mp c.property) e he).trans
        ((mem_constantColourings.mp d.property) e he).symm
    · exact congrFun h ⟨e, he⟩
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective f hf

private lemma exists_avoiding_colouring {n k : ℕ} (hkn : k ≤ n)
    (hcount : 2 * n.choose k < 2 ^ k.choose 2) :
    ∃ c : Finset (Fin n) → Bool, ∀ S : Finset (Fin n), S.card = k →
      ∀ b : Bool, ¬ ∀ e ∈ S.powersetCard 2, c e = b := by
  classical
  let T := (Finset.univ : Finset (Fin n)).powersetCard k
  let I := T ×ˢ (Finset.univ : Finset Bool)
  let B (p : Finset (Fin n) × Bool) := constantColourings (p.1.powersetCard 2) p.2
  let D := Fintype.card (Finset (Fin n))
  have hD : k.choose 2 ≤ D := calc
    k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
    _ = ((Finset.univ : Finset (Fin n)).powersetCard 2).card := by
      simp [Finset.card_powersetCard]
    _ ≤ D := Finset.card_le_univ _
  have hB (p : Finset (Fin n) × Bool) (hp : p ∈ I) :
      (B p).card ≤ 2 ^ (D - k.choose 2) := by
    have hcard := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
    simpa [B, D, Finset.card_powersetCard, hcard] using
      card_constantColourings (p.1.powersetCard 2) p.2
  have hcardI : I.card = 2 * n.choose k := by
    simp [I, T, Finset.card_powersetCard, Nat.mul_comm]
  have hbad : (I.biUnion B).card < Fintype.card (Finset (Fin n) → Bool) := calc
    (I.biUnion B).card ≤ ∑ p ∈ I, (B p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ I, 2 ^ (D - k.choose 2) := Finset.sum_le_sum hB
    _ = (2 * n.choose k) * 2 ^ (D - k.choose 2) := by simp [hcardI]
    _ < 2 ^ (k.choose 2) * 2 ^ (D - k.choose 2) :=
      Nat.mul_lt_mul_of_pos_right hcount (by positivity)
    _ = Fintype.card (Finset (Fin n) → Bool) := by
      rw [← pow_add, Nat.add_sub_of_le hD]
      simp [D]
  obtain ⟨c, _, hc⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := I.biUnion B)
      (t := Finset.univ) (by simpa using hbad)
  refine ⟨c, fun S hS b hmono => hc (Finset.mem_biUnion.mpr ?_)⟩
  refine ⟨(S, b), ?_, mem_constantColourings.mpr hmono⟩
  simp [I, T, hS]

private lemma lt_ramsey_of_count {n k : ℕ}
    (hcount : 2 * n.choose k < 2 ^ k.choose 2) : n < diagonalRamsey k := by
  classical
  by_cases hkn : k ≤ n
  · obtain ⟨c, hc⟩ := exists_avoiding_colouring hkn hcount
    let G : SimpleGraph (Fin n) :=
      { Adj := fun x y => x ≠ y ∧ c {x, y} = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa [Finset.pair_comm y x] using h.2⟩⟩
        loopless := ⟨fun _ h => h.1 rfl⟩ }
    apply lt_ramsey_of_cliqueFree (G := G)
    · intro S hS
      refine hc S hS.card_eq true (fun e he => ?_)
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      exact (hS.isClique (hsub (by simp)) (hsub (by simp)) hxy).2
    · intro S hS
      refine hc S hS.card_eq false (fun e he => ?_)
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      have h := (compl_adj G x y).mp (hS.isClique (hsub (by simp)) (hsub (by simp)) hxy)
      exact Bool.eq_false_iff.mpr (fun ht => h.2 ⟨hxy, ht⟩)
  · have hfree (G : SimpleGraph (Fin n)) : G.CliqueFree k := by
      intro S hS
      exact hkn (hS.card_eq ▸ (by simpa using S.card_le_univ : S.card ≤ n))
    exact lt_ramsey_of_cliqueFree (hfree ⊥) (hfree _)

private lemma ramsey_count_power_lt {k : ℕ} (hk : 3 ≤ k) :
    2 * (2 ^ ((k - 3) / 2)) ^ k < 2 ^ k.choose 2 := by
  let m := (k - 3) / 2
  have hm : 2 * m + 2 ≤ k - 1 := by dsimp [m]; omega
  have hmul : 2 * (m * k) + 2 * k ≤ k * (k - 1) := by
    simpa only [Nat.add_mul, mul_assoc, mul_comm (k - 1) k] using
      Nat.mul_le_mul_right k hm
  have hexp : 1 + m * k < k.choose 2 := by
    rw [Nat.choose_two_right]
    omega
  change 2 * (2 ^ m) ^ k < 2 ^ k.choose 2
  calc
    2 * (2 ^ m) ^ k = 2 ^ (1 + m * k) := by rw [pow_add, pow_one, pow_mul]
    _ < _ := Nat.pow_lt_pow_right (by decide) hexp

private lemma ramsey_exp_lower {k : ℕ} (hk : 3 ≤ k) :
    2 ^ ((k - 3) / 2) < diagonalRamsey k := by
  apply lt_ramsey_of_count
  exact (Nat.mul_le_mul_left 2 (Nat.choose_le_pow _ _)).trans_lt (ramsey_count_power_lt hk)

private lemma third_pow_le_factorial (k : ℕ) : (k / 3) ^ k ≤ k.factorial := by
  have hk : (3 : ℝ) * ((k / 3 : ℕ) : ℝ) ≤ k := by
    exact_mod_cast (Nat.mul_div_le k 3)
  have hc : ((k / 3 : ℕ) : ℝ) ≤ (k : ℝ) / 3 := by linarith
  have h := Real.pow_div_factorial_le_exp (k : ℝ) (by positivity) k
  have hExp : Real.exp (k : ℝ) ≤ (3 : ℝ) ^ k := calc
    _ = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hkF : (k : ℝ) ^ k ≤ (3 : ℝ) ^ k * (k.factorial : ℝ) :=
    (div_le_iff₀ hfac).mp (h.trans hExp)
  have h' : ((k : ℝ) / 3) ^ k ≤ (k.factorial : ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ (by positivity)).2
    simpa only [mul_comm (k.factorial : ℝ)] using hkF
  exact_mod_cast ((pow_le_pow_left₀ (by positivity) hc k).trans h')

private lemma ramsey_exp_lower_linear {k : ℕ} (hk : 3 ≤ k) :
    (k / 3) * 2 ^ ((k - 3) / 2) < diagonalRamsey k := by
  let m := (k - 3) / 2
  let n := (k / 3) * 2 ^ m
  have hchoose : n.choose k ≤ (2 ^ m) ^ k := by
    refine Nat.le_of_mul_le_mul_left ?_ k.factorial_pos
    calc
      k.factorial * n.choose k = n.descFactorial k :=
        (Nat.descFactorial_eq_factorial_mul_choose n k).symm
      _ ≤ n ^ k := n.descFactorial_le_pow k
      _ = (k / 3) ^ k * (2 ^ m) ^ k := mul_pow _ _ _
      _ ≤ k.factorial * (2 ^ m) ^ k :=
        Nat.mul_le_mul_right _ (third_pow_le_factorial k)
  apply lt_ramsey_of_count (n := n)
  exact (Nat.mul_le_mul_left 2 hchoose).trans_lt (ramsey_count_power_lt hk)

private lemma ramsey_root_lower {k : ℕ} (hk : 3 ≤ k) :
    (2 : ℝ) ^ (1 / 2 - 2 / (k : ℝ)) ≤
      (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)) := by
  let m := (k - 3) / 2
  have hm : k ≤ 2 * m + 4 := by dsimp [m]; omega
  have hm' : (k : ℝ) ≤ 2 * (m : ℝ) + 4 := by exact_mod_cast hm
  have hkm : (k : ℝ) / 2 - 2 ≤ m := by linarith
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hi : 0 ≤ 1 / (k : ℝ) := by positivity
  have hr : ((k : ℝ) / 2 - 2) * (1 / (k : ℝ)) = 1 / 2 - 2 / (k : ℝ) := by
    field_simp
  calc
    (2 : ℝ) ^ (1 / 2 - 2 / (k : ℝ)) = (2 : ℝ) ^ (((k : ℝ) / 2 - 2) * (1 / (k : ℝ))) := by
      rw [hr]
    _ ≤ (2 : ℝ) ^ ((m : ℝ) * (1 / (k : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hkm hi)
    _ = ((2 ^ m : ℕ) : ℝ) ^ (1 / (k : ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      norm_cast
    _ ≤ (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast (ramsey_exp_lower hk).le) hi

private lemma ramsey_lower_comparison_tendsto :
    Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ (1 / 2 - 2 / (k : ℝ)))
      Filter.atTop (𝓝 (Real.sqrt 2)) := by
  have h_inv : Filter.Tendsto (fun k : ℕ => (k : ℝ)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h_exp : Filter.Tendsto (fun k : ℕ => (1 / 2 : ℝ) - 2 / (k : ℝ))
      Filter.atTop (𝓝 (1 / 2)) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub (h_inv.const_mul 2)
  rw [Real.sqrt_eq_rpow]
  exact (Real.continuousAt_const_rpow (a := 2) (b := (1 / 2 : ℝ))
    (by norm_num)).tendsto.comp h_exp

private lemma ramsey_limit_ge_sqrt_two {L : ℝ}
    (hL : Filter.Tendsto (fun k : ℕ => (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (𝓝 L)) : Real.sqrt 2 ≤ L := by
  exact le_of_tendsto_of_tendsto ramsey_lower_comparison_tendsto hL
    (Filter.eventually_atTop.mpr ⟨3, fun _ hk => ramsey_root_lower hk⟩)

private lemma ramsey_subsequence_limit_bounds {φ : ℕ → ℕ} (hφ : StrictMono φ) {L : ℝ}
    (hL : Filter.Tendsto (fun k : ℕ => (diagonalRamsey (φ k) : ℝ) ^ (1 / (φ k : ℝ)))
      Filter.atTop (𝓝 L)) : L ∈ Set.Icc (Real.sqrt 2) 4 := by
  constructor
  · have hlower := Filter.eventually_atTop.mpr ⟨3, fun _ hk => ramsey_root_lower hk⟩
    exact le_of_tendsto_of_tendsto
      (ramsey_lower_comparison_tendsto.comp hφ.tendsto_atTop) hL
      (hφ.tendsto_atTop.eventually hlower)
  · apply le_of_tendsto hL
    filter_upwards [hφ.tendsto_atTop.eventually (Filter.eventually_ge_atTop (1 : ℕ))] with k hk
    exact ramsey_root_le_four (by omega)

private lemma ramsey_roots_have_convergent_subsequence :
    ∃ L ∈ Set.Icc (Real.sqrt 2) 4, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun k : ℕ => (diagonalRamsey (φ k) : ℝ) ^ (1 / (φ k : ℝ)))
        Filter.atTop (𝓝 L) := by
  have hbounded : ∀ᶠ k : ℕ in Filter.atTop,
      (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)) ∈ Set.Icc 0 4 :=
    Filter.eventually_atTop.mpr ⟨1, fun _ hk => ⟨by positivity, ramsey_root_le_four (by omega)⟩⟩
  obtain ⟨L, _, φ, hφ, hL⟩ :=
    (isCompact_Icc (α := ℝ) (a := 0) (b := 4)).isSeqCompact.subseq_of_frequently_in
      hbounded.frequently
  exact ⟨L, ramsey_subsequence_limit_bounds hφ hL, φ, hφ, hL⟩

private lemma diagonal_ramsey_mono : Monotone diagonalRamsey := by
  intro a b hab
  have hem : (completeGraph (Fin a)).IsContained (completeGraph (Fin b)) :=
    isContained_top_iff.mpr ⟨Fin.castLEEmb hab⟩
  exact Nat.sInf_le (fun G => (ramsey_property_at_number b G).imp
    (fun h => hem.trans h) (fun h => hem.trans h))

private noncomputable def ramseyRoot (k : ℕ) : ℝ :=
  (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ))

private lemma ramsey_root_step {k : ℕ} (hk : 0 < k) :
    ramseyRoot k ≤ ramseyRoot (k + 1) * (4 : ℝ) ^ (1 / (k : ℝ)) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1R : (k : ℝ) + 1 ≠ 0 := by positivity
  have h_exp : 1 / (k : ℝ) = (1 / ((k : ℝ) + 1)) * (1 + 1 / (k : ℝ)) := by
    field_simp
  have hmono : (diagonalRamsey k : ℝ) ≤ diagonalRamsey (k + 1) := by
    exact_mod_cast diagonal_ramsey_mono (Nat.le_succ k)
  calc
    ramseyRoot k ≤ (diagonalRamsey (k + 1) : ℝ) ^ (1 / (k : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hmono (by positivity)
    _ = ramseyRoot (k + 1) * ramseyRoot (k + 1) ^ (1 / (k : ℝ)) := by
      conv_lhs => rw [h_exp]
      rw [Real.rpow_mul (by positivity), Real.rpow_add_of_nonneg (by positivity)
        (by positivity) (by positivity), Real.rpow_one]
      simp only [ramseyRoot, Nat.cast_add, Nat.cast_one]
    _ ≤ ramseyRoot (k + 1) * (4 : ℝ) ^ (1 / (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by unfold ramseyRoot; positivity)
          (ramsey_root_le_four (by omega)) (by positivity)) (by unfold ramseyRoot; positivity)

private lemma ramsey_root_eventually_small_drop {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop, ramseyRoot k < ramseyRoot (k + 1) + ε := by
  have hinv : Filter.Tendsto (fun k : ℕ => (k : ℝ)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hrpow : Filter.Tendsto (fun k : ℕ => (4 : ℝ) ^ (1 / (k : ℝ))) Filter.atTop (𝓝 1) := by
    simpa only [Real.rpow_zero, one_div, Function.comp_def] using
      (Real.continuousAt_const_rpow (a := 4) (b := 0) (by norm_num)).tendsto.comp hinv
  have herr : Filter.Tendsto (fun k : ℕ => (4 : ℝ) * ((4 : ℝ) ^ (1 / (k : ℝ)) - 1))
      Filter.atTop (𝓝 0) := by
    simpa using (hrpow.sub_const 1).const_mul 4
  filter_upwards [herr.eventually_lt_const hε, Filter.eventually_ge_atTop (1 : ℕ)] with k he hk
  have hfac : 0 ≤ (4 : ℝ) ^ (1 / (k : ℝ)) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_rpow (by norm_num) (by positivity))
  have hdrop := mul_le_mul_of_nonneg_right
    (show ramseyRoot (k + 1) ≤ 4 from ramsey_root_le_four (by omega)) hfac
  linarith [ramsey_root_step hk]

/-- Vanishing downward steps make every value between two cluster points a cluster point. -/
private lemma mapClusterPt_of_small_drops {u : ℕ → ℝ}
    (hdrop : ∀ ε > 0, ∀ᶠ k : ℕ in Filter.atTop, u k < u (k + 1) + ε)
    {a b L : ℝ} (ha : MapClusterPt a Filter.atTop u) (hb : MapClusterPt b Filter.atTop u)
    (haL : a < L) (hLb : L < b) : MapClusterPt L Filter.atTop u := by
  classical
  refine (Metric.nhds_basis_ball.mapClusterPt_iff_frequently).mpr (fun ε hε => ?_)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hdrop ε hε)
  refine Filter.frequently_atTop.mpr (fun N => ?_)
  obtain ⟨m, hm, hmb⟩ := Filter.frequently_atTop.mp
    (mapClusterPt_iff_frequently.mp hb (Set.Ioi L) (Ioi_mem_nhds hLb)) (max N K)
  have hLm : L < u m := hmb
  have hex : ∃ j, m ≤ j ∧ u j < L :=
    Filter.frequently_atTop.mp
      (mapClusterPt_iff_frequently.mp ha (Set.Iio L) (Iio_mem_nhds haL)) m
  let j := Nat.find hex
  have hj : m ≤ j ∧ u j < L := Nat.find_spec hex
  have hmj : m < j := by
    by_contra! h
    have heq : j = m := le_antisymm h hj.1
    rw [heq] at hj
    exact (not_lt_of_gt hLm) hj.2
  have hprev : L ≤ u (j - 1) := by
    by_contra! h
    exact Nat.find_min hex (show j - 1 < j by omega) ⟨by omega, h⟩
  have hstep := hK (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at hstep
  refine ⟨j, by omega, ?_⟩
  change dist (u j) L < ε
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hj.2]

private lemma ramsey_root_cluster_interval {a b L : ℝ}
    (ha : MapClusterPt a Filter.atTop ramseyRoot) (hb : MapClusterPt b Filter.atTop ramseyRoot)
    (hL : L ∈ Set.Icc a b) : MapClusterPt L Filter.atTop ramseyRoot := by
  rcases eq_or_lt_of_le hL.1 with rfl | haL
  · exact ha
  rcases eq_or_lt_of_le hL.2 with rfl | hLb
  · exact hb
  exact mapClusterPt_of_small_drops (fun _ hε => ramsey_root_eventually_small_drop hε)
    ha hb haL hLb

private lemma ramsey_root_bounded_above : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop ramseyRoot :=
  Filter.isBoundedUnder_of_eventually_le
    (Filter.eventually_atTop.mpr ⟨1, fun _ hk => ramsey_root_le_four (by omega)⟩)

private lemma ramsey_root_bounded_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop ramseyRoot :=
  Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall (fun k => by
    unfold ramseyRoot
    positivity))

private lemma ramsey_root_subsequential_limits :
    {L : ℝ | ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (ramseyRoot ∘ φ) Filter.atTop (𝓝 L)} =
      Set.Icc (Filter.liminf ramseyRoot Filter.atTop) (Filter.limsup ramseyRoot Filter.atTop) := by
  have hmin := MapClusterPt.liminf (u := ramseyRoot)
    ramsey_root_bounded_above.isCobounded_ge ramsey_root_bounded_below
  have hmax := MapClusterPt.limsup (u := ramseyRoot)
    ramsey_root_bounded_below.isCobounded_le ramsey_root_bounded_above
  ext L
  constructor
  · rintro ⟨φ, hφ, hL⟩
    have hcluster := MapClusterPt.of_comp hφ.tendsto_atTop hL.mapClusterPt
    exact ⟨hcluster.liminf_le ramsey_root_bounded_below,
      hcluster.le_limsup ramsey_root_bounded_above⟩
  · intro hL
    exact (ramsey_root_cluster_interval hmin hmax hL).tendsto_subseq

private lemma ramsey_root_tendsto_iff {L : ℝ} :
    Filter.Tendsto ramseyRoot Filter.atTop (𝓝 L) ↔
      Filter.liminf ramseyRoot Filter.atTop = L ∧ Filter.limsup ramseyRoot Filter.atTop = L := by
  constructor
  · exact fun h => ⟨h.liminf_eq, h.limsup_eq⟩
  · rintro ⟨hmin, hmax⟩
    exact tendsto_of_liminf_eq_limsup hmin hmax ramsey_root_bounded_above ramsey_root_bounded_below

private lemma ramsey_root_rpow_ratio {a b : ℕ} (ha : 0 < a) :
    ramseyRoot a ^ ((a : ℝ) / (b : ℝ)) =
      (diagonalRamsey a : ℝ) ^ (1 / (b : ℝ)) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  unfold ramseyRoot
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  rw [one_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ haR, one_mul, one_div]

private lemma ramsey_root_interpolation {a n b : ℕ} (ha : 3 ≤ a)
    (han : a ≤ n) (hnb : n ≤ b) :
    ramseyRoot a ^ ((a : ℝ) / (b : ℝ)) ≤ ramseyRoot n ∧
      ramseyRoot n ≤ ramseyRoot b ^ ((b : ℝ) / (a : ℝ)) := by
  have hn : 3 ≤ n := ha.trans han
  have hb : 3 ≤ b := hn.trans hnb
  have hn1 : (1 : ℝ) ≤ diagonalRamsey n := by
    exact_mod_cast (show 1 ≤ diagonalRamsey n from
      Nat.succ_le_of_lt ((Nat.pow_pos (by decide : 0 < 2)).trans (ramsey_exp_lower hn)))
  have hb1 : (1 : ℝ) ≤ diagonalRamsey b := by
    exact hn1.trans (by exact_mod_cast diagonal_ramsey_mono hnb)
  have hanR : (a : ℝ) ≤ n := by exact_mod_cast han
  have hnbR : (n : ℝ) ≤ b := by exact_mod_cast hnb
  have haR : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [ramsey_root_rpow_ratio (by omega : 0 < a), ramsey_root_rpow_ratio (by omega : 0 < b)]
  constructor
  · calc
      _ ≤ (diagonalRamsey n : ℝ) ^ (1 / (b : ℝ)) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast diagonal_ramsey_mono han)
          (by positivity)
      _ ≤ ramseyRoot n :=
        Real.rpow_le_rpow_of_exponent_le hn1 (one_div_le_one_div_of_le hnR hnbR)
  · calc
      ramseyRoot n ≤ (diagonalRamsey b : ℝ) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast diagonal_ramsey_mono hnb)
          (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb1 (one_div_le_one_div_of_le haR hanR)

/-- A convergent subsequence whose consecutive index ratios tend to one determines the full limit. -/
private lemma ramsey_root_tendsto_of_subsequence_ratio_one {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {L : ℝ} (hL : Filter.Tendsto (ramseyRoot ∘ φ) Filter.atTop (𝓝 L))
    (hratio : Filter.Tendsto (fun j : ℕ => (φ (j + 1) : ℝ) / (φ j : ℝ))
      Filter.atTop (𝓝 1)) : Filter.Tendsto ramseyRoot Filter.atTop (𝓝 L) := by
  let j (n : ℕ) := Nat.findGreatest (fun i => φ i ≤ n) n
  have hj : Filter.Tendsto j Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr (fun i => Filter.eventually_atTop.mpr ⟨φ i, fun n h => ?_⟩)
    exact Nat.le_findGreatest ((hφ.id_le i).trans h) h
  have hbracket : ∀ᶠ n : ℕ in Filter.atTop, 3 ≤ φ (j n) ∧ φ (j n) ≤ n ∧ n ≤ φ (j n + 1) := by
    filter_upwards [Filter.eventually_ge_atTop (φ 0),
      hj.eventually (Filter.eventually_ge_atTop (3 : ℕ))] with n h0 h3
    refine ⟨h3.trans (hφ.id_le _), ?_, ?_⟩
    · exact Nat.findGreatest_spec (P := fun i => φ i ≤ n) (Nat.zero_le n) h0
    · by_contra! h
      have hidx := (hφ.id_le (j n + 1)).trans h.le
      exact Nat.findGreatest_is_greatest (P := fun i => φ i ≤ n)
        (Nat.lt_succ_self (j n)) hidx h.le
  have hratio_inv : Filter.Tendsto (fun i : ℕ => (φ i : ℝ) / (φ (i + 1) : ℝ))
      Filter.atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hratio.inv₀ one_ne_zero
  have hlo : Filter.Tendsto
      (fun n => ramseyRoot (φ (j n)) ^ ((φ (j n) : ℝ) / (φ (j n + 1) : ℝ)))
      Filter.atTop (𝓝 L) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (hL.comp hj).rpow (hratio_inv.comp hj) (Or.inr zero_lt_one)
  have hhi : Filter.Tendsto
      (fun n => ramseyRoot (φ (j n + 1)) ^ ((φ (j n + 1) : ℝ) / (φ (j n) : ℝ)))
      Filter.atTop (𝓝 L) := by
    have hshift := (Filter.tendsto_add_atTop_nat 1).comp hj
    simpa only [Real.rpow_one, Function.comp_def] using
      (hL.comp hshift).rpow (hratio.comp hj) (Or.inr zero_lt_one)
  have hbound := hbracket.mono (fun _ ⟨h3, hlo, hhi⟩ => ramsey_root_interpolation h3 hlo hhi)
  exact hlo.squeeze' hhi (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)

private lemma classical_ramsey_property (a b : ℕ)
    (G : SimpleGraph (Fin (classicalRamsey a b))) :
    (completeGraph (Fin a)).IsContained G ∨ (completeGraph (Fin b)).IsContained Gᶜ := by
  let S := {n : ℕ | ∀ C : SimpleGraph (Fin n),
    (completeGraph (Fin a)).IsContained C ∨ (completeGraph (Fin b)).IsContained Cᶜ}
  have hmem : sInf S ∈ S := Nat.sInf_mem ⟨_, graph_ramsey_choose a b⟩
  exact hmem G

private lemma lt_classical_ramsey_of_cliqueFree {n a b : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree a) (hGc : Gᶜ.CliqueFree b) :
    n < classicalRamsey a b := by
  by_contra! h
  let e : Fin (classicalRamsey a b) ↪ Fin n := Fin.castLEEmb h
  let f := Embedding.comap e G
  rcases classical_ramsey_property a b (G.comap e) with hK | hK
  · exact (hK.trans f.isContained).not_cliqueFree hG
  · exact (hK.trans (Embedding.complEquiv f).isContained).not_cliqueFree hGc

private lemma classical_ramsey_symm (a b : ℕ) :
    classicalRamsey a b = classicalRamsey b a := by
  have hle (x y : ℕ) : classicalRamsey x y ≤ classicalRamsey y x := by
    apply Nat.sInf_le
    intro G
    rcases classical_ramsey_property y x Gᶜ with h1 | h2
    · exact Or.inr h1
    · rw [compl_compl] at h2
      exact Or.inl h2
  exact le_antisymm (hle a b) (hle b a)

private lemma classical_ramsey_zero_left (b : ℕ) : classicalRamsey 0 b = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  intro G
  left
  refine (not_cliqueFree_iff_top_isContained 0).mp ?_
  exact IsNClique.not_cliqueFree (s := ∅) ⟨by simp, by simp⟩

private lemma classical_ramsey_pos {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ classicalRamsey a b := by
  have h0 : 0 < classicalRamsey a b := by
    apply lt_classical_ramsey_of_cliqueFree (G := (⊥ : SimpleGraph (Fin 0)))
    · intro S hS
      have hcard : S.card = 0 := by simp [Finset.eq_empty_of_isEmpty S]
      have heq := hS.card_eq
      omega
    · intro S hS
      have hcard : S.card = 0 := by simp [Finset.eq_empty_of_isEmpty S]
      have heq := hS.card_eq
      omega
  omega

private lemma classical_ramsey_one_left {b : ℕ} (hb : 1 ≤ b) : classicalRamsey 1 b = 1 := by
  apply le_antisymm _ (classical_ramsey_pos le_rfl hb)
  apply Nat.sInf_le
  intro G
  left
  apply (not_cliqueFree_iff_top_isContained 1).mp
  refine IsNClique.not_cliqueFree (s := {⟨0, Nat.zero_lt_one⟩}) ⟨?_, by simp⟩
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_singleton] at hx hy
  exact (hxy (hx.trans hy.symm)).elim

private lemma classical_ramsey_two_left (b : ℕ) : classicalRamsey 2 b = b := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [classical_ramsey_symm, classical_ramsey_zero_left]
  have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
  apply le_antisymm
  · apply Nat.sInf_le
    intro G
    by_cases h : ∃ x y : Fin b, G.Adj x y
    · obtain ⟨x, y, hxy⟩ := h
      left
      apply (not_cliqueFree_iff_top_isContained 2).mp
      refine IsNClique.not_cliqueFree (s := {x, y}) ⟨?_, Finset.card_pair hxy.ne⟩
      intro u hu v hv huv
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (huv rfl).elim
      · exact hxy
      · exact hxy.symm
      · exact (huv rfl).elim
    · push Not at h
      right
      apply (not_cliqueFree_iff_top_isContained b).mp
      refine IsNClique.not_cliqueFree (s := Finset.univ) ⟨?_, by simp⟩
      intro u _ v _ huv
      exact ⟨huv, h u v⟩
  · have hlt : b - 1 < classicalRamsey 2 b := by
      apply lt_classical_ramsey_of_cliqueFree (G := (⊥ : SimpleGraph (Fin (b - 1))))
      · intro S hS
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hS.card_eq
        exact hS.isClique (by simp) (by simp) hxy
      · intro S hS
        have hle : S.card ≤ b - 1 := by simpa using S.card_le_univ
        have heq := hS.card_eq
        omega
    omega

private lemma isContained_succ_of_neighbor_set {n m : ℕ} {G : SimpleGraph (Fin n)}
    {v : Fin n} {A : Finset (Fin n)} (hA : ∀ u ∈ A, G.Adj v u)
    {k : ℕ} (e : Fin m ↪ Fin n) (he : ∀ i, e i ∈ A)
    (hK : (completeGraph (Fin k)).IsContained (G.comap e)) :
    (completeGraph (Fin (k + 1))).IsContained G := by
  classical
  have hncf := (not_cliqueFree_iff_top_isContained k).mpr hK
  rw [SimpleGraph.CliqueFree] at hncf
  push Not at hncf
  obtain ⟨S, hS⟩ := hncf
  have hv_not_mem : v ∉ S.image e := by
    intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    exact G.loopless.irrefl v (hi ▸ hA (e i) (he i))
  apply (not_cliqueFree_iff_top_isContained (k + 1)).mp
  refine IsNClique.not_cliqueFree (s := insert v (S.image e)) ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_image] at hx hy
    rcases hx with rfl | ⟨i, hi, rfl⟩
    · rcases hy with rfl | ⟨j, hj, rfl⟩
      · exact (hxy rfl).elim
      · exact hA (e j) (he j)
    · rcases hy with rfl | ⟨j, hj, rfl⟩
      · exact (hA (e i) (he i)).symm
      · have hij : i ≠ j := fun h => hxy (congrArg e h)
        exact hS.isClique hi hj hij
  · rw [Finset.card_insert_of_notMem hv_not_mem, Finset.card_image_of_injective S e.injective,
      hS.card_eq]

private lemma classical_ramsey_add_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    classicalRamsey (a + 1) (b + 1) ≤ classicalRamsey a (b + 1) + classicalRamsey (a + 1) b := by
  classical
  apply Nat.sInf_le
  intro G
  let r₁ := classicalRamsey a (b + 1)
  let r₂ := classicalRamsey (a + 1) b
  have hr₁ : 1 ≤ r₁ := classical_ramsey_pos ha (by omega)
  have hr₂ : 1 ≤ r₂ := classical_ramsey_pos (by omega) hb
  let v₀ : Fin (r₁ + r₂) := ⟨0, by omega⟩
  let R : Finset (Fin (r₁ + r₂)) := (Finset.univ.erase v₀).filter (fun u => G.Adj v₀ u)
  let B : Finset (Fin (r₁ + r₂)) := (Finset.univ.erase v₀).filter (fun u => ¬ G.Adj v₀ u)
  have hsum : R.card + B.card = r₁ + r₂ - 1 := by
    have hdisj : Disjoint R B := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
    have hunion : R ∪ B = Finset.univ.erase v₀ :=
      Finset.filter_union_filter_not_eq (fun u => G.Adj v₀ u) (Finset.univ.erase v₀)
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    simp
  by_cases hR : r₁ ≤ R.card
  · let eqR : R ≃ Fin R.card := Fintype.equivFinOfCardEq (Fintype.card_coe R)
    let e : Fin r₁ ↪ Fin (r₁ + r₂) :=
      (Fin.castLEEmb hR).trans (eqR.symm.toEmbedding.trans (Function.Embedding.subtype _))
    have he : ∀ i, e i ∈ R := fun i => (eqR.symm (Fin.castLEEmb hR i)).property
    rcases classical_ramsey_property a (b + 1) (G.comap e) with hK | hK
    · left
      exact isContained_succ_of_neighbor_set (fun u hu => (Finset.mem_filter.mp hu).2) e he hK
    · right
      exact hK.trans (Embedding.complEquiv (Embedding.comap e G)).isContained
  · have hB : r₂ ≤ B.card := by omega
    let eqB : B ≃ Fin B.card := Fintype.equivFinOfCardEq (Fintype.card_coe B)
    let e : Fin r₂ ↪ Fin (r₁ + r₂) :=
      (Fin.castLEEmb hB).trans (eqB.symm.toEmbedding.trans (Function.Embedding.subtype _))
    have he : ∀ i, e i ∈ B := fun i => (eqB.symm (Fin.castLEEmb hB i)).property
    rcases classical_ramsey_property (a + 1) b (G.comap e) with hK | hK
    · left
      exact hK.trans (Embedding.comap e G).isContained
    · right
      have hB_adj : ∀ u ∈ B, Gᶜ.Adj v₀ u := by
        intro u hu
        have hmem := Finset.mem_filter.mp hu
        exact ⟨(Finset.mem_erase.mp hmem.1).1.symm, hmem.2⟩
      have hK' : (completeGraph (Fin b)).IsContained (Gᶜ.comap e) := by
        have hEq : (G.comap e)ᶜ = Gᶜ.comap e := by
          ext x y
          simp [SimpleGraph.compl_adj, e.injective.ne_iff]
        rwa [hEq] at hK
      exact isContained_succ_of_neighbor_set hB_adj e he hK'

private lemma classical_ramsey_le_choose :
    ∀ n a b : ℕ, a + b = n → classicalRamsey (a + 1) (b + 1) ≤ Nat.choose n a := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    simp [classical_ramsey_one_left]
  | succ n ih =>
    intro a b hab
    rcases a with _ | a
    · simp [classical_ramsey_one_left]
    rcases b with _ | b
    · have : a + 1 = n + 1 := by omega
      rw [classical_ramsey_symm, classical_ramsey_one_left (by omega), this, Nat.choose_self]
    · calc
        classicalRamsey (a + 2) (b + 2)
            ≤ classicalRamsey (a + 1) (b + 2) + classicalRamsey (a + 2) (b + 1) :=
              classical_ramsey_add_le (by omega) (by omega)
        _ ≤ Nat.choose n a + Nat.choose n (a + 1) :=
              Nat.add_le_add (ih a (b + 1) (by omega)) (ih (a + 1) b (by omega))
        _ = Nat.choose (n + 1) (a + 1) := (Nat.choose_succ_succ n a).symm

private lemma diagonal_ramsey_le_centralBinom_pred {k : ℕ} (hk : 1 ≤ k) :
    diagonalRamsey k ≤ Nat.choose (2 * k - 2) (k - 1) := by
  have hk1 : k - 1 + 1 = k := by omega
  have h2 : (k - 1) + (k - 1) = 2 * k - 2 := by omega
  simpa [diagonalRamsey, hk1] using classical_ramsey_le_choose (2 * k - 2) (k - 1) (k - 1) h2

private lemma diagonal_ramsey_le_four_pow_pred {k : ℕ} (hk : 1 ≤ k) :
    diagonalRamsey k ≤ 4 ^ (k - 1) := by
  have h := diagonal_ramsey_le_centralBinom_pred hk
  have h2 : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [h2] at h
  exact h.trans (Nat.centralBinom_le_four_pow (k - 1))

private lemma ramsey_root_lt_four {k : ℕ} (hk : 1 ≤ k) : ramseyRoot k < 4 := by
  have hlt : (diagonalRamsey k : ℝ) < (4 : ℝ) ^ k := by
    have hnat : diagonalRamsey k < 4 ^ k :=
      (diagonal_ramsey_le_four_pow_pred hk).trans_lt
        (Nat.pow_lt_pow_right (by decide) (by omega))
    exact_mod_cast hnat
  have hk0 : k ≠ 0 := by omega
  have hpos : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  rw [← rpow_nat_root (x := 4) (by norm_num) hk0]
  exact Real.rpow_lt_rpow (by positivity) hlt hpos

private lemma card_lt_of_cliqueFree {α : Type*} {G : SimpleGraph α} {k : ℕ}
    (hG : G.CliqueFree k) {S : Finset α} (hS : G.IsClique (S : Set α)) : S.card < k := by
  by_contra! hk
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hk
  exact hG T ⟨hS.subset (Finset.coe_subset.mpr hTS), hTcard⟩

private lemma classical_ramsey_succ_le {k : ℕ} (hk : 1 ≤ k) :
    classicalRamsey k (k + 1) ≤ (k - 1) * diagonalRamsey k + 1 := by
  classical
  apply Nat.sInf_le
  intro G
  by_contra h
  rcases not_or.mp h with ⟨h1, h2⟩
  have hG : G.CliqueFree k := by
    by_contra hn
    exact h1 ((not_cliqueFree_iff_top_isContained k).mp hn)
  have hGc : Gᶜ.CliqueFree (k + 1) := by
    by_contra hn
    exact h2 ((not_cliqueFree_iff_top_isContained (k + 1)).mp hn)
  let N := (k - 1) * diagonalRamsey k + 1
  let B (v : Fin N) : Finset (Fin N) := Finset.univ.filter (fun u => Gᶜ.Adj v u)
  have hBcard (v : Fin N) : (insert v (B v)).card ≤ diagonalRamsey k := by
    have hlt : (B v).card < diagonalRamsey k := by
      by_contra! hge
      let eqB : B v ≃ Fin (B v).card := Fintype.equivFinOfCardEq (Fintype.card_coe (B v))
      let e : Fin (diagonalRamsey k) ↪ Fin N :=
        (Fin.castLEEmb hge).trans (eqB.symm.toEmbedding.trans (Function.Embedding.subtype _))
      have he : ∀ i, e i ∈ B v := fun i => (eqB.symm (Fin.castLEEmb hge i)).property
      rcases ramsey_property_at_number k (G.comap e) with hK | hK
      · exact (hK.trans (Embedding.comap e G).isContained).not_cliqueFree hG
      · have hEq : (G.comap e)ᶜ = Gᶜ.comap e := by
          ext x y
          simp [SimpleGraph.compl_adj, e.injective.ne_iff]
        rw [hEq] at hK
        exact (isContained_succ_of_neighbor_set (G := Gᶜ)
          (fun u hu => (Finset.mem_filter.mp hu).2) e he hK).not_cliqueFree hGc
    have hv : v ∉ B v := by simp [B]
    rw [Finset.card_insert_of_notMem hv]
    omega
  let C : Finset (Finset (Fin N)) :=
    Finset.univ.filter (fun S => G.IsClique (S : Set (Fin N)))
  have hCne : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨S, hSC, hSmax⟩ := Finset.exists_max_image C Finset.card hCne
  have hSclique : G.IsClique (S : Set (Fin N)) := (Finset.mem_filter.mp hSC).2
  have hScard : S.card ≤ k - 1 := by
    have := card_lt_of_cliqueFree hG hSclique
    omega
  have hcover : (Finset.univ : Finset (Fin N)) ⊆ S.biUnion (fun v => insert v (B v)) := by
    intro u _
    by_cases hu : u ∈ S
    · exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_insert_self u _⟩
    · have hex : ∃ v ∈ S, ¬ G.Adj v u := by
        by_contra hall
        push Not at hall
        have hins : G.IsClique ((insert u S : Finset (Fin N)) : Set (Fin N)) := by
          intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
          rcases hx with rfl | hx
          · rcases hy with rfl | hy
            · exact (hxy rfl).elim
            · exact (hall y hy).symm
          · rcases hy with rfl | hy
            · exact hall x hx
            · exact hSclique hx hy hxy
        have hle := hSmax (insert u S) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hins⟩)
        rw [Finset.card_insert_of_notMem hu] at hle
        omega
      obtain ⟨v, hvS, hnv⟩ := hex
      have hvu : v ≠ u := fun heq => hu (heq ▸ hvS)
      exact Finset.mem_biUnion.mpr
        ⟨v, hvS, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hvu, hnv⟩⟩)⟩
  have hNle : N ≤ (k - 1) * diagonalRamsey k := calc
    N = (Finset.univ : Finset (Fin N)).card := by simp
    _ ≤ (S.biUnion (fun v => insert v (B v))).card := Finset.card_le_card hcover
    _ ≤ ∑ v ∈ S, (insert v (B v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ S, diagonalRamsey k := Finset.sum_le_sum (fun v _ => hBcard v)
    _ = S.card * diagonalRamsey k := by simp
    _ ≤ (k - 1) * diagonalRamsey k := Nat.mul_le_mul_right _ hScard
  omega

private lemma diagonal_ramsey_succ_le {k : ℕ} (hk : 1 ≤ k) :
    diagonalRamsey (k + 1) ≤ 2 * k * diagonalRamsey k := by
  have hpos : 1 ≤ diagonalRamsey k := classical_ramsey_pos hk hk
  have hadd : diagonalRamsey (k + 1) ≤ 2 * classicalRamsey k (k + 1) := by
    calc
      diagonalRamsey (k + 1)
          ≤ classicalRamsey k (k + 1) + classicalRamsey (k + 1) k :=
            classical_ramsey_add_le hk hk
      _ = 2 * classicalRamsey k (k + 1) := by
            rw [classical_ramsey_symm (k + 1) k, two_mul]
  have hstep := classical_ramsey_succ_le hk
  have hmul : (k - 1) * diagonalRamsey k + diagonalRamsey k = k * diagonalRamsey k := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel hk]
  calc
    diagonalRamsey (k + 1) ≤ 2 * classicalRamsey k (k + 1) := hadd
    _ ≤ 2 * ((k - 1) * diagonalRamsey k + 1) := Nat.mul_le_mul_left 2 hstep
    _ ≤ 2 * ((k - 1) * diagonalRamsey k + diagonalRamsey k) :=
          Nat.mul_le_mul_left 2 (Nat.add_le_add_left hpos _)
    _ = 2 * (k * diagonalRamsey k) := by rw [hmul]
    _ = 2 * k * diagonalRamsey k := by ring

private lemma ramsey_root_succ_le {k : ℕ} (hk : 1 ≤ k) :
    ramseyRoot (k + 1) ≤ ramseyRoot k * (2 * (k : ℝ)) ^ (1 / ((k : ℝ) + 1)) := by
  have hR1 : (1 : ℝ) ≤ diagonalRamsey k := by exact_mod_cast classical_ramsey_pos hk hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hinv_le : 1 / ((k : ℝ) + 1) ≤ 1 / (k : ℝ) :=
    one_div_le_one_div_of_le hkpos (by linarith)
  have hnat : (diagonalRamsey (k + 1) : ℝ) ≤ (2 * (k : ℝ)) * (diagonalRamsey k : ℝ) := by
    exact_mod_cast (show diagonalRamsey (k + 1) ≤ 2 * k * diagonalRamsey k from
      diagonal_ramsey_succ_le hk)
  unfold ramseyRoot
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    (diagonalRamsey (k + 1) : ℝ) ^ (1 / ((k : ℝ) + 1))
        ≤ ((2 * (k : ℝ)) * (diagonalRamsey k : ℝ)) ^ (1 / ((k : ℝ) + 1)) :=
          Real.rpow_le_rpow (by positivity) hnat (by positivity)
    _ = (2 * (k : ℝ)) ^ (1 / ((k : ℝ) + 1)) *
          (diagonalRamsey k : ℝ) ^ (1 / ((k : ℝ) + 1)) :=
          Real.mul_rpow (by positivity) (by positivity)
    _ = (diagonalRamsey k : ℝ) ^ (1 / ((k : ℝ) + 1)) *
          (2 * (k : ℝ)) ^ (1 / ((k : ℝ) + 1)) := mul_comm _ _
    _ ≤ (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)) *
          (2 * (k : ℝ)) ^ (1 / ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hR1 hinv_le) (by positivity)

private lemma tendsto_two_mul_rpow_inv_succ :
    Filter.Tendsto (fun k : ℕ => (2 * (k : ℝ)) ^ (1 / ((k : ℝ) + 1))) Filter.atTop (𝓝 1) := by
  have hlog : Filter.Tendsto (fun k : ℕ => Real.log (2 * (k : ℝ)) / ((k : ℝ) + 1))
      Filter.atTop (𝓝 0) := by
    have hupper : Filter.Tendsto (fun k : ℕ => 2 * Real.sqrt 2 * ((Real.sqrt (k : ℝ))⁻¹))
        Filter.atTop (𝓝 0) := by
      have hsqrt : Filter.Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) Filter.atTop Filter.atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa using (tendsto_inv_atTop_zero.comp hsqrt).const_mul (2 * Real.sqrt 2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
      have hk1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      exact div_nonneg (Real.log_nonneg hk1) (by positivity)
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hsq : Real.sqrt (2 * (k : ℝ)) ^ 2 = 2 * (k : ℝ) := Real.sq_sqrt (by positivity)
      have hlog_le : Real.log (2 * (k : ℝ)) ≤ 2 * Real.sqrt (2 * (k : ℝ)) := by
        have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * k))
        have h2 : Real.log (2 * (k : ℝ)) = 2 * Real.log (Real.sqrt (2 * (k : ℝ))) := by
          conv_lhs => rw [← hsq]
          rw [Real.log_pow]
          push_cast
          ring
        linarith
      have hdiv1 : Real.log (2 * (k : ℝ)) / ((k : ℝ) + 1) ≤
          2 * Real.sqrt (2 * (k : ℝ)) / (k : ℝ) := calc
        Real.log (2 * (k : ℝ)) / ((k : ℝ) + 1)
            ≤ 2 * Real.sqrt (2 * (k : ℝ)) / ((k : ℝ) + 1) :=
              div_le_div_of_nonneg_right hlog_le (by positivity)
        _ ≤ 2 * Real.sqrt (2 * (k : ℝ)) / (k : ℝ) :=
              div_le_div_of_nonneg_left (by positivity) hkpos (by linarith)
      have hrew : 2 * Real.sqrt (2 * (k : ℝ)) / (k : ℝ) =
          2 * Real.sqrt 2 * (Real.sqrt (k : ℝ))⁻¹ := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hsk : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hkpos).ne'
        have hmul : (k : ℝ) = Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) :=
          (Real.mul_self_sqrt hkpos.le).symm
        conv_lhs => arg 2; rw [hmul]
        field_simp [hsk]
      linarith
  have hexp : Filter.Tendsto (fun k : ℕ => Real.exp (Real.log (2 * (k : ℝ)) / ((k : ℝ) + 1)))
      Filter.atTop (𝓝 1) := by
    simpa [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hlog
  refine hexp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
  have hpos : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  rw [Real.rpow_def_of_pos hpos, mul_one_div]

private lemma ramsey_root_diff_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => ramseyRoot (k + 1) - ramseyRoot k) Filter.atTop (𝓝 0) := by
  have hinv : Filter.Tendsto (fun k : ℕ => (k : ℝ)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hfour : Filter.Tendsto (fun k : ℕ => (4 : ℝ) ^ (1 / (k : ℝ))) Filter.atTop (𝓝 1) := by
    simpa only [Real.rpow_zero, one_div, Function.comp_def] using
      (Real.continuousAt_const_rpow (a := 4) (b := 0) (by norm_num)).tendsto.comp hinv
  have hlo : Filter.Tendsto (fun k : ℕ => -((4 : ℝ) * ((4 : ℝ) ^ (1 / (k : ℝ)) - 1)))
      Filter.atTop (𝓝 0) := by
    simpa using ((hfour.sub_const 1).const_mul 4).neg
  have hhi : Filter.Tendsto
      (fun k : ℕ => (4 : ℝ) * ((2 * (k : ℝ)) ^ (1 / ((k : ℝ) + 1)) - 1))
      Filter.atTop (𝓝 0) := by
    simpa using (tendsto_two_mul_rpow_inv_succ.sub_const 1).const_mul 4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
    have hstep := ramsey_root_step (by omega : 0 < k)
    have hfac : 0 ≤ (4 : ℝ) ^ (1 / (k : ℝ)) - 1 :=
      sub_nonneg.mpr (Real.one_le_rpow (by norm_num) (by positivity))
    have hmul := mul_le_mul_of_nonneg_right
      (show ramseyRoot (k + 1) ≤ 4 from ramsey_root_le_four (by omega)) hfac
    linarith
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
    have hstep := ramsey_root_succ_le hk
    have h2k : (1 : ℝ) ≤ 2 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hfac : 0 ≤ (2 * (k : ℝ)) ^ (1 / ((k : ℝ) + 1)) - 1 :=
      sub_nonneg.mpr (Real.one_le_rpow h2k (by positivity))
    have hmul := mul_le_mul_of_nonneg_right
      (show ramseyRoot k ≤ 4 from ramsey_root_le_four (by omega)) hfac
    linarith

private lemma diagonal_ramsey_zero : diagonalRamsey 0 = 0 :=
  classical_ramsey_zero_left 0

private lemma diagonal_ramsey_one : diagonalRamsey 1 = 1 :=
  classical_ramsey_one_left le_rfl

private lemma diagonal_ramsey_two : diagonalRamsey 2 = 2 :=
  classical_ramsey_two_left 2

private lemma diagonal_ramsey_three : diagonalRamsey 3 = 6 := by
  apply le_antisymm
  · calc
      diagonalRamsey 3 ≤ classicalRamsey 2 3 + classicalRamsey 3 2 :=
        classical_ramsey_add_le (by omega) (by omega)
      _ = 6 := by
        rw [classical_ramsey_symm 3 2, classical_ramsey_two_left]
  · let C5 : SimpleGraph (Fin 5) :=
      { Adj := fun x y => x - y = 1 ∨ y - x = 1
        symm := ⟨fun _ _ h => h.symm⟩
        loopless := ⟨fun x h => by rcases h with h | h <;> simp at h⟩ }
    have hlt : 5 < diagonalRamsey 3 := by
      apply lt_ramsey_of_cliqueFree (G := C5)
      · intro S hS
        obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :
            ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
          obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
          exact ⟨x, by simp, y, by simp, z, by simp, hxy, hxz, hyz⟩
        have h1 : C5.Adj x y := hS.isClique hx hy hxy
        have h2 : C5.Adj x z := hS.isClique hx hz hxz
        have h3 : C5.Adj y z := hS.isClique hy hz hyz
        revert h1 h2 h3 hxy hxz hyz
        fin_cases x <;> fin_cases y <;> fin_cases z <;> decide
      · intro S hS
        obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :
            ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
          obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
          exact ⟨x, by simp, y, by simp, z, by simp, hxy, hxz, hyz⟩
        have h1 : C5ᶜ.Adj x y := hS.isClique hx hy hxy
        have h2 : C5ᶜ.Adj x z := hS.isClique hx hz hxz
        have h3 : C5ᶜ.Adj y z := hS.isClique hy hz hyz
        revert h1 h2 h3 hxy hxz hyz
        fin_cases x <;> fin_cases y <;> fin_cases z <;> decide
    omega

private lemma exists_cliqueFree_below_ramsey {n k : ℕ} (h : n < diagonalRamsey k) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  by_contra hnone
  push Not at hnone
  have hle : diagonalRamsey k ≤ n := by
    apply Nat.sInf_le
    intro G
    by_cases hG : G.CliqueFree k
    · right
      exact (not_cliqueFree_iff_top_isContained k).mp (hnone G hG)
    · left
      exact (not_cliqueFree_iff_top_isContained k).mp hG
  omega

private lemma diagonal_ramsey_strictMono : StrictMono diagonalRamsey := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  rcases eq_or_ne k 0 with rfl | hk
  · rw [diagonal_ramsey_zero, diagonal_ramsey_one]; omega
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hpos : 1 ≤ diagonalRamsey k := classical_ramsey_pos hk1 hk1
  obtain ⟨G, hG, hGc⟩ := exists_cliqueFree_below_ramsey
    (n := diagonalRamsey k - 1) (k := k) (by omega)
  let m := diagonalRamsey k - 1
  have hm : m + 1 = diagonalRamsey k := by omega
  let G' : SimpleGraph (Fin (m + 1)) :=
    { Adj := fun x y =>
        if hx : x.val < m then
          if hy : y.val < m then G.Adj ⟨x.val, hx⟩ ⟨y.val, hy⟩ else True
        else
          y.val < m
      symm := ⟨fun x y h => by
        by_cases hx : x.val < m <;> by_cases hy : y.val < m <;> simp_all [G.adj_comm]⟩
      loopless := ⟨fun x h => by
        by_cases hx : x.val < m
        · simp [hx] at h
        · simp [hx] at h⟩ }
  have hcastAdj (i j : Fin m) : G'.Adj i.castSucc j.castSucc ↔ G.Adj i j := by
    simp [G', i.isLt, j.isLt]
  have hlastAdj (i : Fin m) : G'.Adj (Fin.last m) i.castSucc := by
    simp [G', i.isLt]
  have hlt : m + 1 < diagonalRamsey (k + 1) := by
    apply lt_ramsey_of_cliqueFree (G := G')
    · intro S hS
      let S₀ : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.castSucc ∈ S)
      have hS₀clique : G.IsClique (S₀ : Set (Fin m)) := by
        intro i hi j hj hij
        have hiS : i.castSucc ∈ S := (Finset.mem_filter.mp hi).2
        have hjS : j.castSucc ∈ S := (Finset.mem_filter.mp hj).2
        exact (hcastAdj i j).mp (hS.isClique hiS hjS (fun h => hij (Fin.castSucc_inj.mp h)))
      have hS₀lt : S₀.card < k := card_lt_of_cliqueFree hG hS₀clique
      have hsub : S.erase (Fin.last m) ⊆ S₀.image Fin.castSucc := by
        intro x hx
        have hne : x ≠ Fin.last m := (Finset.mem_erase.mp hx).1
        have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
        have hxlt : x.val < m := by
          have hval : x.val ≠ m := fun h => hne (Fin.ext h)
          omega
        refine Finset.mem_image.mpr ⟨⟨x.val, hxlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · convert hxS using 1
          ext; rfl
        · ext; rfl
      have hcard_erase : (S.erase (Fin.last m)).card ≤ S₀.card :=
        (Finset.card_le_card hsub).trans Finset.card_image_le
      have hcard_le : S.card ≤ (S.erase (Fin.last m)).card + 1 := by
        by_cases hl : Fin.last m ∈ S
        · rw [Finset.card_erase_of_mem hl]; omega
        · rw [Finset.erase_eq_of_notMem hl]; omega
      have hScard := hS.card_eq
      omega
    · intro S hS
      have hlast_not_mem : Fin.last m ∉ S := by
        intro hl
        have hcard1 : 1 < S.card := by rw [hS.card_eq]; omega
        obtain ⟨y, hyS, hyl⟩ := Finset.exists_mem_ne hcard1 (Fin.last m)
        have hylt : y.val < m := by
          have hval : y.val ≠ m := fun h => hyl (Fin.ext h)
          omega
        have hadj := hS.isClique hl hyS hyl.symm
        have hG'adj : G'.Adj (Fin.last m) y := by
          have : y = (⟨y.val, hylt⟩ : Fin m).castSucc := by ext; rfl
          rw [this]
          exact hlastAdj ⟨y.val, hylt⟩
        exact hadj.2 hG'adj
      let S₀ : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.castSucc ∈ S)
      have hS₀clique : Gᶜ.IsClique (S₀ : Set (Fin m)) := by
        intro i hi j hj hij
        have hiS : i.castSucc ∈ S := (Finset.mem_filter.mp hi).2
        have hjS : j.castSucc ∈ S := (Finset.mem_filter.mp hj).2
        have hadj := hS.isClique hiS hjS (fun h => hij (Fin.castSucc_inj.mp h))
        exact ⟨hij, fun h => hadj.2 ((hcastAdj i j).mpr h)⟩
      have hS₀lt : S₀.card < k := card_lt_of_cliqueFree hGc hS₀clique
      have hsub : S ⊆ S₀.image Fin.castSucc := by
        intro x hx
        have hne : x ≠ Fin.last m := fun h => hlast_not_mem (h ▸ hx)
        have hxlt : x.val < m := by
          have hval : x.val ≠ m := fun h => hne (Fin.ext h)
          omega
        refine Finset.mem_image.mpr ⟨⟨x.val, hxlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · convert hx using 1
          ext; rfl
        · ext; rfl
      have hcard_le : S.card ≤ S₀.card :=
        (Finset.card_le_card hsub).trans Finset.card_image_le
      have hScard := hS.card_eq
      omega
  omega

private def lexProd {α β : Type*} (G₁ : SimpleGraph α) (G₂ : SimpleGraph β) :
    SimpleGraph (α × β) where
  Adj p q := G₁.Adj p.1 q.1 ∨ (p.1 = q.1 ∧ G₂.Adj p.2 q.2)
  symm := ⟨fun _ _ h => h.imp (fun h1 => h1.symm) (fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩)⟩
  loopless := ⟨fun p h => by
    rcases h with h1 | ⟨_, h2⟩
    · exact G₁.loopless.irrefl p.1 h1
    · exact G₂.loopless.irrefl p.2 h2⟩

private lemma lexProd_compl {α β : Type*} (G₁ : SimpleGraph α) (G₂ : SimpleGraph β) :
    (lexProd G₁ G₂)ᶜ = lexProd G₁ᶜ G₂ᶜ := by
  ext p q
  simp only [SimpleGraph.compl_adj, lexProd]
  by_cases h : p.1 = q.1
  · constructor
    · rintro ⟨hpq, hnot⟩
      right
      refine ⟨h, ?_, fun h2 => hnot (Or.inr ⟨h, h2⟩)⟩
      intro hp2
      exact hpq (Prod.ext h hp2)
    · rintro (⟨h1, _⟩ | ⟨_, hp2, hn2⟩)
      · exact (h1 h).elim
      · refine ⟨fun hpq => hp2 (congrArg Prod.snd hpq), ?_⟩
        rintro (h1 | ⟨_, h2⟩)
        · exact G₁.loopless.irrefl p.1 (h ▸ h1)
        · exact hn2 h2
  · constructor
    · rintro ⟨_, hnot⟩
      left
      exact ⟨h, fun h1 => hnot (Or.inl h1)⟩
    · rintro (⟨_, hn1⟩ | ⟨h1, _⟩)
      · refine ⟨fun hpq => h (congrArg Prod.fst hpq), ?_⟩
        rintro (h1 | ⟨h1, _⟩)
        · exact hn1 h1
        · exact h h1
      · exact (h h1).elim

private lemma lexProd_cliqueFree {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G₁ : SimpleGraph α} {G₂ : SimpleGraph β} {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (h₁ : G₁.CliqueFree a) (h₂ : G₂.CliqueFree b) :
    (lexProd G₁ G₂).CliqueFree ((a - 1) * (b - 1) + 1) := by
  intro S hS
  let P : Finset α := S.image Prod.fst
  have hPclique : G₁.IsClique (P : Set α) := by
    intro x hx y hy hxy
    simp only [P, Finset.mem_coe, Finset.mem_image] at hx hy
    obtain ⟨p, hpS, rfl⟩ := hx
    obtain ⟨q, hqS, rfl⟩ := hy
    have hpq : p ≠ q := fun h => hxy (congrArg Prod.fst h)
    rcases hS.isClique hpS hqS hpq with h1 | ⟨h1, _⟩
    · exact h1
    · exact (hxy h1).elim
  have hPcard : P.card ≤ a - 1 := by
    have := card_lt_of_cliqueFree h₁ hPclique
    omega
  have hfiber (x : α) : (S.filter (fun p => p.1 = x)).card ≤ b - 1 := by
    let F : Finset β := (S.filter (fun p => p.1 = x)).image Prod.snd
    have hFclique : G₂.IsClique (F : Set β) := by
      intro u hu v hv huv
      simp only [F, Finset.mem_coe, Finset.mem_image, Finset.mem_filter] at hu hv
      obtain ⟨p, ⟨hpS, hp1⟩, rfl⟩ := hu
      obtain ⟨q, ⟨hqS, hq1⟩, rfl⟩ := hv
      have hpq : p ≠ q := fun h => huv (congrArg Prod.snd h)
      rcases hS.isClique hpS hqS hpq with h1 | ⟨_, h2⟩
      · rw [hp1, hq1] at h1
        exact (G₁.loopless.irrefl x h1).elim
      · exact h2
    have hFlt : F.card < b := card_lt_of_cliqueFree h₂ hFclique
    have hFeq : F.card = (S.filter (fun p => p.1 = x)).card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq hpq
      have hp1 := (Finset.mem_filter.mp hp).2
      have hq1 := (Finset.mem_filter.mp hq).2
      exact Prod.ext (hp1.trans hq1.symm) hpq
    omega
  have hScard_le : S.card ≤ (a - 1) * (b - 1) := calc
    S.card = ∑ x ∈ P, (S.filter (fun p => p.1 = x)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem Prod.fst hp)
    _ ≤ ∑ _x ∈ P, (b - 1) := Finset.sum_le_sum (fun x _ => hfiber x)
    _ = P.card * (b - 1) := by simp
    _ ≤ (a - 1) * (b - 1) := Nat.mul_le_mul_right _ hPcard
  have hSeq := hS.card_eq
  omega

/-- Abbott's lexicographic product lower bound for diagonal Ramsey numbers. -/
private lemma diagonal_ramsey_lex_lower {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (diagonalRamsey a - 1) * (diagonalRamsey b - 1) <
      diagonalRamsey ((a - 1) * (b - 1) + 1) := by
  have ha1 : 1 ≤ diagonalRamsey a := classical_ramsey_pos ha ha
  have hb1 : 1 ≤ diagonalRamsey b := classical_ramsey_pos hb hb
  obtain ⟨G₁, hG₁, hG₁c⟩ := exists_cliqueFree_below_ramsey
    (n := diagonalRamsey a - 1) (k := a) (by omega)
  obtain ⟨G₂, hG₂, hG₂c⟩ := exists_cliqueFree_below_ramsey
    (n := diagonalRamsey b - 1) (k := b) (by omega)
  let e : Fin ((diagonalRamsey a - 1) * (diagonalRamsey b - 1)) ↪
      Fin (diagonalRamsey a - 1) × Fin (diagonalRamsey b - 1) :=
    finProdFinEquiv.symm.toEmbedding
  let H : SimpleGraph (Fin ((diagonalRamsey a - 1) * (diagonalRamsey b - 1))) :=
    (lexProd G₁ G₂).comap e
  apply lt_ramsey_of_cliqueFree (G := H)
  · exact (lexProd_cliqueFree ha hb hG₁ hG₂).comap (Embedding.comap e (lexProd G₁ G₂)).isContained
  · have hEq : Hᶜ = (lexProd G₁ᶜ G₂ᶜ).comap e := by
      ext x y
      simp only [H, SimpleGraph.compl_adj, SimpleGraph.comap_adj, ← lexProd_compl]
      simp [e.injective.ne_iff]
    rw [hEq]
    exact (lexProd_cliqueFree ha hb hG₁c hG₂c).comap
      (Embedding.comap e (lexProd G₁ᶜ G₂ᶜ)).isContained

/-- Strict Erdős-Szekeres bound when both predecessor Ramsey numbers are even. -/
private lemma classical_ramsey_add_lt_of_even {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (he₁ : Even (classicalRamsey a (b + 1))) (he₂ : Even (classicalRamsey (a + 1) b)) :
    classicalRamsey (a + 1) (b + 1) ≤
      classicalRamsey a (b + 1) + classicalRamsey (a + 1) b - 1 := by
  classical
  let r₁ := classicalRamsey a (b + 1)
  let r₂ := classicalRamsey (a + 1) b
  have hr₁_pos : 1 ≤ r₁ := classical_ramsey_pos ha (by omega)
  have hr₂_pos : 1 ≤ r₂ := classical_ramsey_pos (by omega) hb
  rcases he₁ with ⟨k₁, hk₁⟩
  rcases he₂ with ⟨k₂, hk₂⟩
  have hk₁_pos : 1 ≤ k₁ := by omega
  have hk₂_pos : 1 ≤ k₂ := by omega
  let N := r₁ + r₂ - 1
  apply Nat.sInf_le
  intro G
  by_contra h
  rcases not_or.mp h with ⟨h1, h2⟩
  have hG : G.CliqueFree (a + 1) := by
    by_contra hn
    exact h1 ((not_cliqueFree_iff_top_isContained (a + 1)).mp hn)
  have hGc : Gᶜ.CliqueFree (b + 1) := by
    by_contra hn
    exact h2 ((not_cliqueFree_iff_top_isContained (b + 1)).mp hn)
  have hdeg : ∀ v : Fin N, G.degree v = r₁ - 1 := by
    intro v
    let R : Finset (Fin N) := (Finset.univ.erase v).filter (fun u => G.Adj v u)
    let B : Finset (Fin N) := (Finset.univ.erase v).filter (fun u => ¬ G.Adj v u)
    have hsum : R.card + B.card = N - 1 := by
      have hdisj : Disjoint R B := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
      have hunion : R ∪ B = Finset.univ.erase v :=
        Finset.filter_union_filter_not_eq (fun u => G.Adj v u) (Finset.univ.erase v)
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
      simp
    have hRlt : R.card < r₁ := by
      by_contra! hR
      let eqR : R ≃ Fin R.card := Fintype.equivFinOfCardEq (Fintype.card_coe R)
      let e : Fin r₁ ↪ Fin N :=
        (Fin.castLEEmb hR).trans (eqR.symm.toEmbedding.trans (Function.Embedding.subtype _))
      have he : ∀ i, e i ∈ R := fun i => (eqR.symm (Fin.castLEEmb hR i)).property
      rcases classical_ramsey_property a (b + 1) (G.comap e) with hK | hK
      · exact (isContained_succ_of_neighbor_set (fun u hu => (Finset.mem_filter.mp hu).2)
          e he hK).not_cliqueFree hG
      · exact (hK.trans (Embedding.complEquiv (Embedding.comap e G)).isContained).not_cliqueFree hGc
    have hBlt : B.card < r₂ := by
      by_contra! hB
      let eqB : B ≃ Fin B.card := Fintype.equivFinOfCardEq (Fintype.card_coe B)
      let e : Fin r₂ ↪ Fin N :=
        (Fin.castLEEmb hB).trans (eqB.symm.toEmbedding.trans (Function.Embedding.subtype _))
      have he : ∀ i, e i ∈ B := fun i => (eqB.symm (Fin.castLEEmb hB i)).property
      rcases classical_ramsey_property (a + 1) b (G.comap e) with hK | hK
      · exact (hK.trans (Embedding.comap e G).isContained).not_cliqueFree hG
      · have hB_adj : ∀ u ∈ B, Gᶜ.Adj v u := by
          intro u hu
          have hmem := Finset.mem_filter.mp hu
          exact ⟨(Finset.mem_erase.mp hmem.1).1.symm, hmem.2⟩
        have hEq : (G.comap e)ᶜ = Gᶜ.comap e := by
          ext x y
          simp [SimpleGraph.compl_adj, e.injective.ne_iff]
        rw [hEq] at hK
        exact (isContained_succ_of_neighbor_set hB_adj e he hK).not_cliqueFree hGc
    have hR_eq : R.card = r₁ - 1 := by omega
    have hneigh : G.neighborFinset v = R := by
      ext u
      simp only [SimpleGraph.mem_neighborFinset, R, Finset.mem_filter, Finset.mem_erase,
        Finset.mem_univ, and_true]
      exact ⟨fun hadj => ⟨hadj.ne.symm, hadj⟩, fun h => h.2⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hneigh, hR_eq]
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hsum_deg : ∑ v : Fin N, G.degree v = N * (r₁ - 1) := by
    simp [hdeg]
  have heven : N * (r₁ - 1) = 2 * G.edgeFinset.card := hsum_deg.symm.trans hhand
  have hN : Odd N := ⟨k₁ + k₂ - 1, by dsimp [N]; omega⟩
  have hr : Odd (r₁ - 1) := ⟨k₁ - 1, by omega⟩
  obtain ⟨t, ht⟩ := hN.mul hr
  rw [heven] at ht
  omega

private lemma exists_four_of_card_eq_four {α : Type*} {S : Finset α} (hS : S.card = 4) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hne
  have hcard3 : (S.erase a).card = 3 := by
    rw [Finset.card_erase_of_mem ha, hS]
  obtain ⟨b, c, d, hbc, hbd, hcd, heq⟩ := Finset.card_eq_three.mp hcard3
  have hb_er : b ∈ S.erase a := heq ▸ by simp
  have hc_er : c ∈ S.erase a := heq ▸ by simp
  have hd_er : d ∈ S.erase a := heq ▸ by simp
  refine ⟨a, ha, b, (Finset.mem_erase.mp hb_er).2, c, (Finset.mem_erase.mp hc_er).2,
    d, (Finset.mem_erase.mp hd_er).2, (Finset.mem_erase.mp hb_er).1.symm,
    (Finset.mem_erase.mp hc_er).1.symm, (Finset.mem_erase.mp hd_er).1.symm, hbc, hbd, hcd⟩

private def adjCirc8 (x y : Fin 8) : Bool :=
  let d := x - y
  d == 1 || d == 4 || d == 7

private lemma classical_ramsey_three_four : classicalRamsey 3 4 = 9 := by
  apply le_antisymm
  · have he₁ : Even (classicalRamsey 2 4) := by
      rw [classical_ramsey_two_left]
      exact ⟨2, rfl⟩
    have he₂ : Even (classicalRamsey 3 3) := by
      change Even (diagonalRamsey 3)
      rw [diagonal_ramsey_three]
      exact ⟨3, rfl⟩
    have hle := classical_ramsey_add_lt_of_even (a := 2) (b := 3) (by omega) (by omega) he₁ he₂
    change classicalRamsey 3 4 ≤ classicalRamsey 2 4 + classicalRamsey 3 3 - 1 at hle
    have h24 : classicalRamsey 2 4 = 4 := classical_ramsey_two_left 4
    have h33 : classicalRamsey 3 3 = 6 := diagonal_ramsey_three
    omega
  · have hsym : ∀ x y : Fin 8, adjCirc8 x y = true → adjCirc8 y x = true := by decide
    have hloop : ∀ x : Fin 8, adjCirc8 x x = false := by decide
    have htri : ∀ x y z : Fin 8,
        adjCirc8 x y = true → adjCirc8 x z = true → adjCirc8 y z = false := by decide
    have hind4 : ∀ x y z : Fin 8,
        x ≠ 0 → y ≠ 0 → z ≠ 0 → x ≠ y → x ≠ z → y ≠ z →
        adjCirc8 0 x = false → adjCirc8 0 y = false → adjCirc8 0 z = false →
        adjCirc8 x y = false → adjCirc8 x z = false → adjCirc8 y z = false → False := by decide
    have hshift : ∀ a x y : Fin 8, adjCirc8 (x - a) (y - a) = adjCirc8 x y := by
      intro a x y
      simp only [adjCirc8, sub_sub_sub_cancel_right]
    let G8 : SimpleGraph (Fin 8) :=
      { Adj := fun x y => adjCirc8 x y = true
        symm := ⟨fun x y h => hsym x y h⟩
        loopless := ⟨fun x h => Bool.noConfusion (h.symm.trans (hloop x))⟩ }
    have hlt : 8 < classicalRamsey 3 4 := by
      apply lt_classical_ramsey_of_cliqueFree (G := G8)
      · intro S hS
        obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
        have h1 : adjCirc8 x y = true := hS.isClique (by simp) (by simp) hxy
        have h2 : adjCirc8 x z = true := hS.isClique (by simp) (by simp) hxz
        have h3 : adjCirc8 y z = true := hS.isClique (by simp) (by simp) hyz
        exact Bool.noConfusion (h3.symm.trans (htri x y z h1 h2))
      · intro S hS
        obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
          exists_four_of_card_eq_four hS.card_eq
        have hne (u v : Fin 8) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
            adjCirc8 u v = false :=
          Bool.eq_false_iff.mpr (hS.isClique hu hv huv).2
        have hx0 : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
        have hy0 : c - a ≠ 0 := sub_ne_zero.mpr hac.symm
        have hz0 : d - a ≠ 0 := sub_ne_zero.mpr had.symm
        have hxy : b - a ≠ c - a := fun h => hbc (sub_left_inj.mp h)
        have hxz : b - a ≠ d - a := fun h => hbd (sub_left_inj.mp h)
        have hyz : c - a ≠ d - a := fun h => hcd (sub_left_inj.mp h)
        have h0x : adjCirc8 0 (b - a) = false := by
          simpa [sub_self] using (hshift a a b).trans (hne a b ha hb hab)
        have h0y : adjCirc8 0 (c - a) = false := by
          simpa [sub_self] using (hshift a a c).trans (hne a c ha hc hac)
        have h0z : adjCirc8 0 (d - a) = false := by
          simpa [sub_self] using (hshift a a d).trans (hne a d ha hd had)
        have hxy' : adjCirc8 (b - a) (c - a) = false :=
          (hshift a b c).trans (hne b c hb hc hbc)
        have hxz' : adjCirc8 (b - a) (d - a) = false :=
          (hshift a b d).trans (hne b d hb hd hbd)
        have hyz' : adjCirc8 (c - a) (d - a) = false :=
          (hshift a c d).trans (hne c d hc hd hcd)
        exact hind4 (b - a) (c - a) (d - a) hx0 hy0 hz0 hxy hxz hyz
          h0x h0y h0z hxy' hxz' hyz'
    omega

private def isQR17 (d : Fin 17) : Bool :=
  d == 1 || d == 2 || d == 4 || d == 8 || d == 9 || d == 13 || d == 15 || d == 16

private lemma diagonal_ramsey_four : diagonalRamsey 4 = 18 := by
  apply le_antisymm
  · calc
      diagonalRamsey 4 ≤ classicalRamsey 3 4 + classicalRamsey 4 3 :=
        classical_ramsey_add_le (by omega) (by omega)
      _ = 18 := by
        rw [classical_ramsey_symm 4 3, classical_ramsey_three_four]
  · have hsym : ∀ d : Fin 17, isQR17 (-d) = isQR17 d := by decide
    have hzero : isQR17 0 = false := by decide
    have hmul : ∀ a b : Fin 17,
        isQR17 a = true → isQR17 b = true → isQR17 (a * b) = true := by decide
    have hinv : ∀ u : Fin 17,
        isQR17 u = true → ∃ t : Fin 17, isQR17 t = true ∧ t * u = 1 := by decide
    have hcommon : ∀ x y : Fin 17,
        isQR17 x = true → isQR17 (x - 1) = true →
        isQR17 y = true → isQR17 (y - 1) = true → isQR17 (x - y) = false := by decide
    have h3 : ∀ d : Fin 17, d ≠ 0 → (isQR17 (3 * d) = true ↔ isQR17 d = false) := by decide
    let P17 : SimpleGraph (Fin 17) :=
      { Adj := fun x y => isQR17 (x - y) = true
        symm := ⟨fun x y h => by
          have hneg : y - x = -(x - y) := (neg_sub x y).symm
          rw [hneg, hsym]
          exact h⟩
        loopless := ⟨fun x h => by
          rw [sub_self] at h
          exact Bool.noConfusion (h.symm.trans hzero)⟩ }
    have hP17_free : P17.CliqueFree 4 := by
      intro S hS
      obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
        exists_four_of_card_eq_four hS.card_eq
      have hu : isQR17 (b - a) = true := hS.isClique hb ha hab.symm
      have hv : isQR17 (c - a) = true := hS.isClique hc ha hac.symm
      have hw : isQR17 (d - a) = true := hS.isClique hd ha had.symm
      have hvu : isQR17 (c - b) = true := hS.isClique hc hb hbc.symm
      have hwu : isQR17 (d - b) = true := hS.isClique hd hb hbd.symm
      have hvw : isQR17 (c - d) = true := hS.isClique hc hd hcd
      obtain ⟨t, ht, htu⟩ := hinv (b - a) hu
      let x := t * (c - a)
      let y := t * (d - a)
      have hx : isQR17 x = true := hmul t (c - a) ht hv
      have hy : isQR17 y = true := hmul t (d - a) ht hw
      have hx1 : isQR17 (x - 1) = true := by
        have heq : x - 1 = t * (c - b) := by
          dsimp [x]
          rw [← htu, ← mul_sub, sub_sub_sub_cancel_right]
        rw [heq]
        exact hmul t (c - b) ht hvu
      have hy1 : isQR17 (y - 1) = true := by
        have heq : y - 1 = t * (d - b) := by
          dsimp [y]
          rw [← htu, ← mul_sub, sub_sub_sub_cancel_right]
        rw [heq]
        exact hmul t (d - b) ht hwu
      have hxy : isQR17 (x - y) = true := by
        have heq : x - y = t * (c - d) := by
          dsimp [x, y]
          rw [← mul_sub, sub_sub_sub_cancel_right]
        rw [heq]
        exact hmul t (c - d) ht hvw
      exact Bool.noConfusion (hxy.symm.trans (hcommon x y hx hx1 hy hy1))
    have hP17c_free : P17ᶜ.CliqueFree 4 := by
      intro S hS
      have h3_inj : Function.Injective (fun x : Fin 17 => 3 * x) := by
        intro x y h
        have h6 : (6 : Fin 17) * (3 * x) = 6 * (3 * y) := congrArg (6 * ·) h
        have h63 : (6 : Fin 17) * 3 = 1 := by decide
        simpa [← mul_assoc, h63] using h6
      refine hP17_free (S.image (fun x => 3 * x)) ⟨?_, ?_⟩
      · intro u hu v hv huv
        simp only [Finset.mem_coe, Finset.mem_image] at hu hv
        obtain ⟨x, hxS, rfl⟩ := hu
        obtain ⟨y, hyS, rfl⟩ := hv
        have hxy : x ≠ y := fun h => huv (congrArg (3 * ·) h)
        have hnot : isQR17 (x - y) = false :=
          Bool.eq_false_iff.mpr (hS.isClique hxS hyS hxy).2
        change isQR17 (3 * x - 3 * y) = true
        rw [← mul_sub]
        exact (h3 (x - y) (sub_ne_zero.mpr hxy)).mpr hnot
      · rw [Finset.card_image_of_injective S h3_inj, hS.card_eq]
    have hlt : 17 < diagonalRamsey 4 := lt_ramsey_of_cliqueFree hP17_free hP17c_free
    omega

private lemma centralBinom_sq_mul_le (m : ℕ) :
    (2 * m + 1) * (Nat.choose (2 * m) m) ^ 2 ≤ 4 ^ (2 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : (m + 1) * Nat.choose (2 * (m + 1)) (m + 1) =
        2 * (2 * m + 1) * Nat.choose (2 * m) m := by
      have h1 : Nat.choose (2 * m + 2) (m + 1) =
          Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) :=
        Nat.choose_succ_succ (2 * m + 1) m
      have hsym : Nat.choose (2 * m + 1) m = Nat.choose (2 * m + 1) (m + 1) := by
        rw [show 2 * m + 1 = m + (m + 1) by omega]
        exact Nat.choose_symm_add
      have h2 : Nat.choose (2 * (m + 1)) (m + 1) = 2 * Nat.choose (2 * m + 1) (m + 1) := by
        rw [show 2 * (m + 1) = 2 * m + 2 by omega, h1, hsym]
        exact (two_mul _).symm
      have h3 : (2 * m + 1) * Nat.choose (2 * m) m =
          (m + 1) * Nat.choose (2 * m + 1) (m + 1) := by
        simpa only [mul_comm ((2 * m + 1).choose (m + 1)) (m + 1)] using
          Nat.add_one_mul_choose_eq (2 * m) m
      calc
        (m + 1) * Nat.choose (2 * (m + 1)) (m + 1)
            = 2 * ((m + 1) * Nat.choose (2 * m + 1) (m + 1)) := by rw [h2]; ring
        _ = 2 * ((2 * m + 1) * Nat.choose (2 * m) m) := by rw [← h3]
        _ = 2 * (2 * m + 1) * Nat.choose (2 * m) m := by ring
    have hpos : 0 < (m + 1) ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    have hquad : (2 * m + 3) * (2 * m + 1) ≤ 4 * (m + 1) ^ 2 := by nlinarith
    have hpow : 4 ^ (2 * (m + 1)) = 16 * 4 ^ (2 * m) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
      ring
    calc
      (m + 1) ^ 2 * ((2 * (m + 1) + 1) * Nat.choose (2 * (m + 1)) (m + 1) ^ 2)
          = (2 * m + 3) * ((m + 1) * Nat.choose (2 * (m + 1)) (m + 1)) ^ 2 := by ring
      _ = (2 * m + 3) * (2 * (2 * m + 1) * Nat.choose (2 * m) m) ^ 2 := by rw [hstep]
      _ = 4 * ((2 * m + 3) * (2 * m + 1)) * ((2 * m + 1) * Nat.choose (2 * m) m ^ 2) := by ring
      _ ≤ 4 * ((2 * m + 3) * (2 * m + 1)) * 4 ^ (2 * m) := Nat.mul_le_mul_left _ ih
      _ ≤ 4 * (4 * (m + 1) ^ 2) * 4 ^ (2 * m) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hquad)
      _ = (m + 1) ^ 2 * (16 * 4 ^ (2 * m)) := by ring
      _ = (m + 1) ^ 2 * 4 ^ (2 * (m + 1)) := by rw [hpow]

private lemma diagonal_ramsey_sq_mul_le {k : ℕ} (hk : 1 ≤ k) :
    (2 * k - 1) * (diagonalRamsey k) ^ 2 ≤ 4 ^ (2 * (k - 1)) := by
  have h1 := diagonal_ramsey_le_centralBinom_pred hk
  have h2 : 2 * k - 2 = 2 * (k - 1) := by omega
  have h3 : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  rw [h2] at h1
  rw [h3]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)).trans (centralBinom_sq_mul_le (k - 1))

private lemma diagonal_ramsey_le_four_pow_div_sqrt {k : ℕ} (hk : 1 ≤ k) :
    (diagonalRamsey k : ℝ) ≤ (4 : ℝ) ^ (k - 1) / Real.sqrt (2 * (k : ℝ) - 1) := by
  have hpos : (0 : ℝ) < 2 * (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hsqrt_pos : 0 < Real.sqrt (2 * (k : ℝ) - 1) := Real.sqrt_pos.mpr hpos
  rw [le_div_iff₀ hsqrt_pos]
  have hnat : ((2 * k - 1 : ℕ) : ℝ) * (diagonalRamsey k : ℝ) ^ 2 ≤ ((4 : ℝ) ^ (k - 1)) ^ 2 := by
    have h := diagonal_ramsey_sq_mul_le hk
    have hcast : ((2 * k - 1 : ℕ) : ℝ) * (diagonalRamsey k : ℝ) ^ 2 ≤ (4 : ℝ) ^ (2 * (k - 1)) := by
      exact_mod_cast h
    simpa [pow_mul, mul_comm 2 (k - 1)] using hcast
  have hsub : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    have h1 : 1 ≤ 2 * k := by omega
    rw [Nat.cast_sub h1]
    push_cast
    ring
  rw [hsub] at hnat
  have hsq : ((diagonalRamsey k : ℝ) * Real.sqrt (2 * (k : ℝ) - 1)) ^ 2 ≤
      ((4 : ℝ) ^ (k - 1)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpos.le, mul_comm]
    exact hnat
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ diagonalRamsey k by positivity) hsqrt_pos.le,
    show (0 : ℝ) ≤ (4 : ℝ) ^ (k - 1) by positivity]

/-- Iterated Abbott lower bound from lexicographic products. -/
private lemma diagonal_ramsey_lex_pow {a : ℕ} (ha : 1 ≤ a) :
    ∀ r : ℕ, 1 ≤ r → (diagonalRamsey a - 1) ^ r < diagonalRamsey ((a - 1) ^ r + 1) := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ih =>
    intro _
    rcases eq_or_ne r 0 with rfl | hr
    · have h1 : 1 ≤ diagonalRamsey a := classical_ramsey_pos ha ha
      have ha1 : a - 1 + 1 = a := by omega
      simp [ha1]
      omega
    · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
      have hih := ih hr1
      have hstep := diagonal_ramsey_lex_lower (a := (a - 1) ^ r + 1) (b := a) (by omega) ha
      have hpow_eq : ((a - 1) ^ r + 1 - 1) * (a - 1) + 1 = (a - 1) ^ (r + 1) + 1 := by
        rw [Nat.add_sub_cancel, pow_succ]
      rw [hpow_eq] at hstep
      have hmul : (diagonalRamsey a - 1) ^ (r + 1) ≤
          (diagonalRamsey ((a - 1) ^ r + 1) - 1) * (diagonalRamsey a - 1) := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right _ (by omega)
      exact hmul.trans_lt hstep

private lemma diagonal_ramsey_pow_two_lower {r : ℕ} (hr : 1 ≤ r) :
    5 ^ r < diagonalRamsey (2 ^ r + 1) := by
  simpa [diagonal_ramsey_three] using diagonal_ramsey_lex_pow (a := 3) (by omega) r hr

private lemma diagonal_ramsey_pow_three_lower {r : ℕ} (hr : 1 ≤ r) :
    17 ^ r < diagonalRamsey (3 ^ r + 1) := by
  simpa [diagonal_ramsey_four] using diagonal_ramsey_lex_pow (a := 4) (by omega) r hr

/-- Erdős alteration (deletion) lower bound for diagonal Ramsey numbers. -/
private lemma lt_ramsey_of_alteration {n k m : ℕ} (hk : 1 ≤ k)
    (hcount : 2 * n.choose k < (m + 1) * 2 ^ k.choose 2) :
    n - m < diagonalRamsey k := by
  classical
  by_cases hkn : k ≤ n - m
  · have hmn : m ≤ n := by omega
    have hkn' : k ≤ n := by omega
    let T := (Finset.univ : Finset (Fin n)).powersetCard k
    let I := T ×ˢ (Finset.univ : Finset Bool)
    let D := Fintype.card (Finset (Fin n))
    have hD : k.choose 2 ≤ D := calc
      k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn'
      _ = ((Finset.univ : Finset (Fin n)).powersetCard 2).card := by
        simp [Finset.card_powersetCard]
      _ ≤ D := Finset.card_le_univ _
    let bad (c : Finset (Fin n) → Bool) : Finset (Finset (Fin n) × Bool) :=
      I.filter (fun p => ∀ e ∈ p.1.powersetCard 2, c e = p.2)
    have hsum_eq : ∑ c : Finset (Fin n) → Bool, (bad c).card =
        ∑ p ∈ I, (constantColourings (p.1.powersetCard 2) p.2).card := by
      simp_rw [bad, Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [constantColourings, Finset.card_filter]
    have hB (p : Finset (Fin n) × Bool) (hp : p ∈ I) :
        (constantColourings (p.1.powersetCard 2) p.2).card ≤ 2 ^ (D - k.choose 2) := by
      have hcard := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
      simpa [D, Finset.card_powersetCard, hcard] using
        card_constantColourings (p.1.powersetCard 2) p.2
    have hcardI : I.card = 2 * n.choose k := by
      simp [I, T, Finset.card_powersetCard, Nat.mul_comm]
    have hsum_lt : ∑ c : Finset (Fin n) → Bool, (bad c).card <
        ∑ _c : Finset (Fin n) → Bool, (m + 1) := calc
      ∑ c : Finset (Fin n) → Bool, (bad c).card
          = ∑ p ∈ I, (constantColourings (p.1.powersetCard 2) p.2).card := hsum_eq
      _ ≤ ∑ _p ∈ I, 2 ^ (D - k.choose 2) := Finset.sum_le_sum hB
      _ = (2 * n.choose k) * 2 ^ (D - k.choose 2) := by simp [hcardI]
      _ < ((m + 1) * 2 ^ k.choose 2) * 2 ^ (D - k.choose 2) :=
            Nat.mul_lt_mul_of_pos_right hcount (by positivity)
      _ = (m + 1) * 2 ^ D := by
            rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hD]
      _ = ∑ _c : Finset (Fin n) → Bool, (m + 1) := by
            simp [D, mul_comm]
    have hex : ∃ c : Finset (Fin n) → Bool, (bad c).card ≤ m := by
      by_contra hall
      push Not at hall
      have hge : ∑ _c : Finset (Fin n) → Bool, (m + 1) ≤
          ∑ c : Finset (Fin n) → Bool, (bad c).card :=
        Finset.sum_le_sum (fun c _ => Nat.succ_le_of_lt (hall c))
      omega
    obtain ⟨c, hc⟩ := hex
    have hn_pos : 0 < n := by omega
    let v0 : Fin n := ⟨0, hn_pos⟩
    let pick (p : Finset (Fin n) × Bool) : Fin n :=
      if h : p.1.Nonempty then h.choose else v0
    let Del : Finset (Fin n) := (bad c).image pick
    have hDel_card : Del.card ≤ m := Finset.card_image_le.trans hc
    let Keep : Finset (Fin n) := Finset.univ \ Del
    have hKeep_card : n - m ≤ Keep.card := by
      have hsub : Del ⊆ Finset.univ := Finset.subset_univ _
      change n - m ≤ (Finset.univ \ Del).card
      rw [Finset.card_sdiff_of_subset hsub]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    let eqK : Keep ≃ Fin Keep.card := Fintype.equivFinOfCardEq (Fintype.card_coe Keep)
    let emb : Fin (n - m) ↪ Fin n :=
      (Fin.castLEEmb hKeep_card).trans (eqK.symm.toEmbedding.trans (Function.Embedding.subtype _))
    have hemb_keep (i : Fin (n - m)) : emb i ∈ Keep := (eqK.symm (Fin.castLEEmb hKeep_card i)).property
    let G : SimpleGraph (Fin (n - m)) :=
      { Adj := fun x y => x ≠ y ∧ c {emb x, emb y} = true
        symm := ⟨fun x y h => ⟨h.1.symm, by simpa [Finset.pair_comm (emb y) (emb x)] using h.2⟩⟩
        loopless := ⟨fun _ h => h.1 rfl⟩ }
    have hno_mono (S : Finset (Fin (n - m))) (hScard : S.card = k) (b : Bool)
        (hmono : ∀ e ∈ (S.image emb).powersetCard 2, c e = b) : False := by
      let S' := S.image emb
      have hS'card : S'.card = k := by
        rw [Finset.card_image_of_injective S emb.injective, hScard]
      have hmem : (S', b) ∈ bad c := by
        refine Finset.mem_filter.mpr ⟨?_, hmono⟩
        simp [I, T, hS'card]
      have hne : S'.Nonempty := Finset.card_pos.mp (by omega)
      have hpick_in_S' : pick (S', b) ∈ S' := by
        dsimp [pick]
        rw [dif_pos hne]
        exact hne.choose_spec
      have hpick_in_Del : pick (S', b) ∈ Del := Finset.mem_image_of_mem pick hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hpick_in_S'
      have hi_keep : emb i ∈ Keep := hemb_keep i
      rw [hi] at hi_keep
      exact (Finset.mem_sdiff.mp hi_keep).2 hpick_in_Del
    apply lt_ramsey_of_cliqueFree (G := G)
    · intro S hS
      refine hno_mono S hS.card_eq true (fun e he => ?_)
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hsub (x := u) (by simp))
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hsub (x := v) (by simp))
      have hxy : x ≠ y := fun h => huv (congrArg emb h)
      exact (hS.isClique hx hy hxy).2
    · intro S hS
      refine hno_mono S hS.card_eq false (fun e he => ?_)
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hsub (x := u) (by simp))
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hsub (x := v) (by simp))
      have hxy : x ≠ y := fun h => huv (congrArg emb h)
      have h := (compl_adj G x y).mp (hS.isClique hx hy hxy)
      exact Bool.eq_false_iff.mpr (fun ht => h.2 ⟨hxy, ht⟩)
  · have hfree (G : SimpleGraph (Fin (n - m))) : G.CliqueFree k := by
      intro S hS
      exact hkn (hS.card_eq ▸ (by simpa using S.card_le_univ : S.card ≤ n - m))
    exact lt_ramsey_of_cliqueFree (hfree ⊥) (hfree _)

/-- The exponential series gives a lower bound for the factorial. -/
private lemma factorial_ge_div_exp_pow (k : ℕ) :
    ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (k : ℝ) (by positivity) k
  have he : Real.exp (k : ℝ) = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul, mul_one]
  rw [he] at h
  rw [div_pow, div_le_iff₀ (by positivity)]
  simpa only [mul_comm (k.factorial : ℝ)] using
    (div_le_iff₀ (by exact_mod_cast k.factorial_pos)).mp h

private lemma twice_choose_two_real (k : ℕ) :
    (2 : ℝ) * (k.choose 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · norm_num
  have h : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd]
  have hr : (2 : ℝ) * (k.choose 2 : ℝ) = (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  rwa [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at hr

private lemma two_half_rpow_pow (k : ℕ) :
    ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ k =
      (2 : ℝ) ^ k.choose 2 * (2 : ℝ) ^ ((k : ℝ) / 2) := by
  rw [← Real.rpow_natCast (((2 : ℝ) ^ ((k : ℝ) / 2))) k,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast (2 : ℝ) (k.choose 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  nlinarith [twice_choose_two_real k]

/-- Deleting one vertex per monochromatic clique gives a lower bound of
`(k / exp 1 - 2) * 2^(k/2)`. -/
private lemma ramsey_alteration_exp_lower {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ) / Real.exp 1 - 2) * (2 : ℝ) ^ ((k : ℝ) / 2) <
      (diagonalRamsey k : ℝ) := by
  let s : ℝ := (2 : ℝ) ^ ((k : ℝ) / 2)
  let x : ℝ := (k : ℝ) / Real.exp 1 * s
  let n := ⌊x⌋₊
  let m := ⌊2 * s⌋₊
  have hx : 0 ≤ x := by positivity
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hcount : (n.choose k : ℝ) ≤ (2 : ℝ) ^ k.choose 2 * s := calc
    (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) := Nat.choose_le_pow_div k n
    _ ≤ x ^ k / (k.factorial : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (Nat.floor_le hx) k) hfac.le
    _ ≤ s ^ k := by
      apply (div_le_iff₀ hfac).mpr
      rw [mul_pow, mul_comm (s ^ k)]
      exact mul_le_mul_of_nonneg_right (factorial_ge_div_exp_pow k) (by positivity)
    _ = (2 : ℝ) ^ k.choose 2 * s := two_half_rpow_pow k
  have hstrict : (2 : ℝ) * (n.choose k : ℝ) < ((m : ℝ) + 1) * (2 : ℝ) ^ k.choose 2 := calc
    _ ≤ 2 * ((2 : ℝ) ^ k.choose 2 * s) := mul_le_mul_of_nonneg_left hcount (by norm_num)
    _ = (2 * s) * (2 : ℝ) ^ k.choose 2 := by ring
    _ < _ := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (2 * s)) (by positivity)
  have hramsey := lt_ramsey_of_alteration hk (n := n) (m := m) (by exact_mod_cast hstrict)
  have hn : n + 1 ≤ diagonalRamsey k + m := by omega
  have hn' : (n : ℝ) + 1 ≤ (diagonalRamsey k : ℝ) + (m : ℝ) := by exact_mod_cast hn
  have hfloor : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hm : (m : ℝ) ≤ 2 * s := Nat.floor_le (by positivity)
  change ((k : ℝ) / Real.exp 1 - 2) * s < (diagonalRamsey k : ℝ)
  rw [sub_mul]
  change x - 2 * s < (diagonalRamsey k : ℝ)
  linarith

/-- Every coefficient below `1 / exp 1` eventually gives a strict lower bound at scale
`k * 2^(k/2)`. -/
private lemma ramsey_eventually_gt_const_mul_half_exp {c : ℝ} (hc : c < 1 / Real.exp 1) :
    ∀ᶠ k : ℕ in Filter.atTop,
      c * ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) < (diagonalRamsey k : ℝ) := by
  have hδ : 0 < 1 / Real.exp 1 - c := sub_pos.mpr hc
  have ht : Filter.Tendsto (fun k : ℕ => (k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (Filter.eventually_gt_atTop (2 / (1 / Real.exp 1 - c))),
    Filter.eventually_ge_atTop (1 : ℕ)] with k hk hk1
  have h := (div_lt_iff₀ hδ).mp hk
  have hcoeff : c * (k : ℝ) < (k : ℝ) / Real.exp 1 - 2 := by
    rw [mul_sub, mul_one_div] at h
    linarith
  rw [← mul_assoc]
  exact (mul_lt_mul_of_pos_right hcoeff (by positivity)).trans (ramsey_alteration_exp_lower hk1)

private lemma ramsey_root_liminf_le_limsup :
    Filter.liminf ramseyRoot Filter.atTop ≤ Filter.limsup ramseyRoot Filter.atTop :=
  Filter.liminf_le_limsup ramsey_root_bounded_above ramsey_root_bounded_below

private lemma ramsey_root_liminf_mem_Icc :
    Filter.liminf ramseyRoot Filter.atTop ∈ Set.Icc (Real.sqrt 2) 4 := by
  have hmem : Filter.liminf ramseyRoot Filter.atTop ∈
      Set.Icc (Filter.liminf ramseyRoot Filter.atTop) (Filter.limsup ramseyRoot Filter.atTop) :=
    ⟨le_rfl, ramsey_root_liminf_le_limsup⟩
  rw [← ramsey_root_subsequential_limits] at hmem
  obtain ⟨φ, hφ, hL⟩ := hmem
  exact ramsey_subsequence_limit_bounds hφ hL

private lemma ramsey_root_limsup_mem_Icc :
    Filter.limsup ramseyRoot Filter.atTop ∈ Set.Icc (Real.sqrt 2) 4 := by
  have hmem : Filter.limsup ramseyRoot Filter.atTop ∈
      Set.Icc (Filter.liminf ramseyRoot Filter.atTop) (Filter.limsup ramseyRoot Filter.atTop) :=
    ⟨ramsey_root_liminf_le_limsup, le_rfl⟩
  rw [← ramsey_root_subsequential_limits] at hmem
  obtain ⟨φ, hφ, hL⟩ := hmem
  exact ramsey_subsequence_limit_bounds hφ hL

/-- A superadditive inequality for pairs within a factor of two suffices to combine any
number of equal blocks. -/
private lemma le_balanced_block_multiple {v : ℕ → ℝ} {K m : ℕ}
    (h : ∀ a b, K ≤ a → a ≤ b → b ≤ 2 * a → v a + v b ≤ v (a + b)) (hm : K ≤ m) :
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) * v m ≤ v (q * m) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq
    by_cases h1 : q = 1
    · subst q
      simp
    let a := q / 2
    let b := q - a
    have ha : 1 ≤ a := by dsimp [a]; omega
    have hab : a ≤ b := by dsimp [a, b]; omega
    have hba : b ≤ 2 * a := by dsimp [a, b]; omega
    have hsum : a + b = q := by dsimp [a, b]; omega
    have hK : K ≤ a * m := hm.trans (by simpa using Nat.mul_le_mul_right m ha)
    have hcomb := h (a * m) (b * m) hK (Nat.mul_le_mul_right m hab)
      (by simpa only [mul_assoc] using Nat.mul_le_mul_right m hba)
    have hleft := ih a (by omega) ha
    have hright := ih b (by omega) (ha.trans hab)
    calc
      (q : ℝ) * v m = (a : ℝ) * v m + (b : ℝ) * v m := by
        rw [← add_mul, ← Nat.cast_add, hsum]
      _ ≤ v (a * m) + v (b * m) := add_le_add hleft hright
      _ ≤ v (a * m + b * m) := hcomb
      _ = v (q * m) := by rw [← add_mul, hsum]

private noncomputable def ramseyLog (k : ℕ) : ℝ := Real.log (diagonalRamsey k : ℝ)

private lemma exp_ramseyLog_div {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (ramseyLog k / k) = ramseyRoot k := by
  have hR : (0 : ℝ) < (diagonalRamsey k : ℝ) := by
    exact_mod_cast classical_ramsey_pos hk hk
  rw [ramseyLog, ramseyRoot, Real.rpow_def_of_pos hR]
  congr 1
  ring

private lemma tendsto_block_multiple_ratio {m : ℕ} (hm : 0 < m) :
    Filter.Tendsto (fun k : ℕ => ((k / m * m : ℕ) : ℝ) / (k : ℝ))
      Filter.atTop (𝓝 1) := by
  have h_inv : Filter.Tendsto (fun k : ℕ => (k : ℝ)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlo : Filter.Tendsto (fun k : ℕ => 1 - (m : ℝ) / k) Filter.atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (h_inv.const_mul (m : ℝ))
  refine hlo.squeeze' tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have h₁ : k ≤ k / m * m + m := by
      have hmod := Nat.mod_add_div k m
      rw [mul_comm m] at hmod
      have := Nat.mod_lt k hm
      omega
    have h₂ : (k : ℝ) ≤ ((k / m * m : ℕ) : ℝ) + m := by exact_mod_cast h₁
    apply (le_div_iff₀ hkpos).mpr
    calc
      (1 - (m : ℝ) / k) * k = (k : ℝ) - m := by field_simp
      _ ≤ ((k / m * m : ℕ) : ℝ) := by linarith
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    apply (div_le_iff₀ hkpos).mpr
    simpa using (show ((k / m * m : ℕ) : ℝ) ≤ k by exact_mod_cast Nat.div_mul_le_self k m)

private lemma ramsey_subsequence_ge_balanced_block {C : ℝ} (hC : 0 ≤ C) {K : ℕ}
    (h : ∀ a b, K ≤ a → a ≤ b → b ≤ 2 * a →
      (ramseyLog a - C * Real.sqrt a) + (ramseyLog b - C * Real.sqrt b) ≤
        ramseyLog (a + b) - C * Real.sqrt (a + b : ℕ))
    {m : ℕ} (hm : 1 ≤ m) (hKm : K ≤ m) {φ : ℕ → ℕ} (hφ : StrictMono φ) {L : ℝ}
    (hL : Filter.Tendsto (ramseyRoot ∘ φ) Filter.atTop (𝓝 L)) :
    Real.exp ((ramseyLog m - C * Real.sqrt m) / m) ≤ L := by
  let r := (ramseyLog m - C * Real.sqrt m) / (m : ℝ)
  have hcomparison : Filter.Tendsto
      (fun k : ℕ => Real.exp (r * (((k / m * m : ℕ) : ℝ) / k)))
      Filter.atTop (𝓝 (Real.exp r)) := by
    have ht := (tendsto_block_multiple_ratio (show 0 < m by omega)).const_mul r
    rw [mul_one] at ht
    exact Real.continuous_exp.continuousAt.tendsto.comp ht
  have hevent : ∀ᶠ k in Filter.atTop,
      Real.exp (r * (((k / m * m : ℕ) : ℝ) / k)) ≤ ramseyRoot k := by
    filter_upwards [Filter.eventually_ge_atTop m] with k hk
    have hk1 := hm.trans hk
    have hq : 1 ≤ k / m := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hk)
    have hqm : 1 ≤ k / m * m := hm.trans (by simpa using Nat.mul_le_mul_right m hq)
    have hblock := le_balanced_block_multiple h hKm (k / m) hq
    have hmono : ramseyLog (k / m * m) ≤ ramseyLog k := by
      apply Real.log_le_log
      · exact_mod_cast classical_ramsey_pos hqm hqm
      · exact_mod_cast diagonal_ramsey_mono (Nat.div_mul_le_self k m)
    rw [← exp_ramseyLog_div hk1, Real.exp_le_exp]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    calc
      r * (((k / m * m : ℕ) : ℝ) / k) =
          ((k / m : ℕ) : ℝ) * (ramseyLog m - C * Real.sqrt m) / k := by
        dsimp [r]
        rw [Nat.cast_mul]
        field_simp
      _ ≤ ramseyLog k / k := by
        apply div_le_div_of_nonneg_right _ hkpos.le
        linarith [mul_nonneg hC (Real.sqrt_nonneg ((k / m * m : ℕ) : ℝ))]
  exact le_of_tendsto_of_tendsto (hcomparison.comp hφ.tendsto_atTop) hL
    (hφ.tendsto_atTop.eventually hevent)

private lemma ramsey_log_sqrt_correction_tendsto {C : ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {L : ℝ} (hL : Filter.Tendsto (ramseyRoot ∘ φ) Filter.atTop (𝓝 L)) :
    Filter.Tendsto (fun j : ℕ => Real.exp ((ramseyLog (φ j) - C * Real.sqrt (φ j)) / (φ j : ℝ)))
      Filter.atTop (𝓝 L) := by
  have hcast : Filter.Tendsto (fun k : ℕ => (k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h₀ : Filter.Tendsto (fun k : ℕ => C * (Real.sqrt (k : ℝ))⁻¹) Filter.atTop (𝓝 0) := by
    have hsqrt : Filter.Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) Filter.atTop Filter.atTop := by
      simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
        (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp hcast
    simpa using (tendsto_inv_atTop_zero.comp hsqrt).const_mul C
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp ((h₀.comp hφ.tendsto_atTop).neg)
  rw [neg_zero, Real.exp_zero] at hexp
  rw [← mul_one L]
  refine (hL.mul hexp).congr' ?_
  filter_upwards [hφ.tendsto_atTop.eventually (Filter.eventually_ge_atTop (1 : ℕ))] with j hj
  change ramseyRoot (φ j) * Real.exp (-(C * (Real.sqrt (φ j))⁻¹)) = _
  rw [← exp_ramseyLog_div hj, ← Real.exp_add]
  congr 1
  rw [sub_div, mul_div_assoc, Real.sqrt_div_self]
  ring

private lemma sqrt_add_le_sqrt_right_add_half_sqrt_left {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt b + Real.sqrt a / 2 := by
  have hb := ha.trans hab
  have hs := Real.sqrt_le_sqrt hab
  have hprod := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg a)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- A square-root error in superadditivity of log Ramsey numbers at comparable indices suffices
for existence of the exponential growth rate. -/
private lemma ramsey_roots_converge_of_balanced_log_bound {C : ℝ} (hC : 0 ≤ C) {K : ℕ}
    (h : ∀ m n, K ≤ m → m ≤ n → n ≤ 2 * m →
      ramseyLog m + ramseyLog n - ramseyLog (m + n) ≤ C * Real.sqrt m) :
    ∃ L : ℝ, Filter.Tendsto ramseyRoot Filter.atTop (𝓝 L) := by
  have hcorrected (a b : ℕ) (ha : K ≤ a) (hab : a ≤ b) (hba : b ≤ 2 * a) :
      (ramseyLog a - 2 * C * Real.sqrt a) + (ramseyLog b - 2 * C * Real.sqrt b) ≤
        ramseyLog (a + b) - 2 * C * Real.sqrt (a + b : ℕ) := by
    have hlog := h a b ha hab hba
    have hsqrt := sqrt_add_le_sqrt_right_add_half_sqrt_left
      (show (0 : ℝ) ≤ a by positivity) (show (a : ℝ) ≤ b by exact_mod_cast hab)
    have hmul := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2 * C by positivity)
    push_cast
    nlinarith only [hlog, hmul]
  let a := Filter.liminf ramseyRoot Filter.atTop
  let b := Filter.limsup ramseyRoot Filter.atTop
  have hab : a ≤ b := ramsey_root_liminf_le_limsup
  have hamem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  rw [← ramsey_root_subsequential_limits] at hamem hbmem
  obtain ⟨φ, hφ, hφL⟩ := hamem
  obtain ⟨ψ, hψ, hψL⟩ := hbmem
  have hba : b ≤ a := by
    refine le_of_tendsto_of_tendsto (ramsey_log_sqrt_correction_tendsto (C := 2 * C) hψ hψL)
      tendsto_const_nhds ?_
    filter_upwards [hψ.tendsto_atTop.eventually (Filter.eventually_ge_atTop (max K 1))] with j hj
    exact ramsey_subsequence_ge_balanced_block (show 0 ≤ 2 * C by positivity) hcorrected
      ((le_max_right K 1).trans hj) ((le_max_left K 1).trans hj) hφ hφL
  exact ⟨a, ramsey_root_tendsto_iff.mpr ⟨rfl, hba.antisymm hab⟩⟩

/-- A polynomial loss in a multiplicative lower bound at comparable indices still gives
convergence of the diagonal Ramsey roots. -/
private lemma ramsey_roots_converge_of_balanced_polynomial_loss {A : ℝ} (hA : 0 ≤ A) {K : ℕ}
    (h : ∀ m n, K ≤ m → m ≤ n → n ≤ 2 * m →
      (diagonalRamsey m : ℝ) * (diagonalRamsey n : ℝ) ≤
        (diagonalRamsey (m + n) : ℝ) * (((m + n : ℕ) : ℝ) ^ A)) :
    ∃ L : ℝ, Filter.Tendsto ramseyRoot Filter.atTop (𝓝 L) := by
  apply ramsey_roots_converge_of_balanced_log_bound (C := 4 * A) (K := max K 1) (by positivity)
  intro m n hm hmn hnm
  have hm₁ : 1 ≤ m := (le_max_right K 1).trans hm
  have hn₁ := hm₁.trans hmn
  have hmn₁ : 1 ≤ m + n := by omega
  have hRm : (0 : ℝ) < diagonalRamsey m := by exact_mod_cast classical_ramsey_pos hm₁ hm₁
  have hRn : (0 : ℝ) < diagonalRamsey n := by exact_mod_cast classical_ramsey_pos hn₁ hn₁
  have hRmn : (0 : ℝ) < diagonalRamsey (m + n) := by exact_mod_cast classical_ramsey_pos hmn₁ hmn₁
  have hsum : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log (mul_pos hRm hRn) (h m n ((le_max_left K 1).trans hm) hmn hnm)
  rw [Real.log_mul hRm.ne' hRn.ne', Real.log_mul hRmn.ne' (Real.rpow_pos_of_pos hsum A).ne',
    Real.log_rpow hsum] at hlog
  have hsqrt : Real.sqrt ((m + n : ℕ) : ℝ) ≤ 2 * Real.sqrt m := by
    have hle : ((m + n : ℕ) : ℝ) ≤ 4 * (m : ℝ) := by
      exact_mod_cast (show m + n ≤ 4 * m by omega)
    have hs := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hs
  have hlog_sqrt := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hsum)
  rw [Real.log_sqrt hsum.le] at hlog_sqrt
  have hsize : Real.log ((m + n : ℕ) : ℝ) ≤ 4 * Real.sqrt m := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsize hA
  unfold ramseyLog
  nlinarith only [hlog, hmul]

open MeasureTheory

private def avoidsEvents {Ω ι : Type*} (E : ι → Set Ω) (S : Finset ι) : Set Ω :=
  {ω | ∀ i ∈ S, ω ∉ E i}

private lemma avoidsEvents_antitone {Ω ι : Type*} (E : ι → Set Ω) :
    Antitone (avoidsEvents E) :=
  fun _ _ h _ hω i hi => hω i (h hi)

private lemma avoidsEvents_insert {Ω ι : Type*} [DecidableEq ι] (E : ι → Set Ω)
    (i : ι) (S : Finset ι) :
    avoidsEvents E (insert i S) = avoidsEvents E S \ E i := by
  ext ω
  simp [avoidsEvents, and_comm]

private lemma measure_avoids_insert_ge {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {E : ι → Set Ω} {i : ι} {S : Finset ι} {x : ℝ}
    (hE : MeasurableSet (E i))
    (h : μ.real (E i ∩ avoidsEvents E S) ≤ x * μ.real (avoidsEvents E S)) :
    (1 - x) * μ.real (avoidsEvents E S) ≤ μ.real (avoidsEvents E (insert i S)) := by
  rw [avoidsEvents_insert]
  have hadd := measureReal_sdiff_add_inter (μ := μ) (s := avoidsEvents E S) hE
  rw [Set.inter_comm] at hadd
  linarith

private lemma measure_avoids_grow {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} {E : ι → Set Ω} {w : ℝ} (hw : 0 ≤ w)
    {S T : Finset ι} (hTS : T ⊆ S)
    (h : ∀ V ⊂ S, ∀ i ∈ S, i ∉ V →
      w * μ.real (avoidsEvents E V) ≤ μ.real (avoidsEvents E (insert i V))) :
    w ^ (S.card - T.card) * μ.real (avoidsEvents E T) ≤ μ.real (avoidsEvents E S) := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases heq : S = T
    · subst S
      simp
    have hST : ¬ S ⊆ T := fun h => heq (Finset.Subset.antisymm h hTS)
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
    have hT' : T ⊆ S.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun hji => hiT (hji ▸ hj), hTS hj⟩
    have hS' : S.erase i ⊂ S := Finset.erase_ssubset hiS
    have hprev := ih (S.erase i) hS' hT' (fun V hV j hj hin =>
      h V (hV.trans hS') j (Finset.erase_subset _ _ hj) hin)
    have hlast := h (S.erase i) hS' i hiS (Finset.notMem_erase _ _)
    rw [Finset.insert_erase hiS] at hlast
    have hcard : S.card - T.card = (S.erase i).card - T.card + 1 := by
      rw [Finset.card_erase_of_mem hiS]
      have := Finset.card_le_card hT'
      rw [Finset.card_erase_of_mem hiS] at this
      have := Finset.card_pos.mpr ⟨i, hiS⟩
      omega
    rw [hcard, pow_succ', mul_assoc]
    exact (mul_le_mul_of_nonneg_left hprev hw).trans hlast

/-- Symmetric Lovász local lemma in a probability space, using independence from avoidance
of any subfamily outside an event's dependency neighbourhood. -/
private lemma exists_avoids_of_local_lemma {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (D : ι → Finset ι) {d : ℕ}
    (hD : ∀ i, (D i).card ≤ d) {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hp : ∀ i, μ.real (E i) ≤ x * (1 - x) ^ d)
    (hindep : ∀ (i : ι) (S : Finset ι), i ∉ S → Disjoint S (D i) →
      μ.real (E i ∩ avoidsEvents E S) = μ.real (E i) * μ.real (avoidsEvents E S)) :
    ∃ ω : Ω, ∀ i, ω ∉ E i := by
  have hw : 0 < 1 - x := sub_pos.mpr hx₁
  have hcond (S : Finset ι) : ∀ i ∉ S,
      μ.real (E i ∩ avoidsEvents E S) ≤ x * μ.real (avoidsEvents E S) := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro i hi
      let T := S \ D i
      have hTS : T ⊆ S := Finset.sdiff_subset
      have hti : i ∉ T := fun hit => hi (hTS hit)
      have htd : Disjoint T (D i) :=
        Finset.disjoint_left.mpr (fun _ hj hjD => (Finset.mem_sdiff.mp hj).2 hjD)
      have hcard : S.card - T.card ≤ d := by
        dsimp [T]
        rw [Finset.card_sdiff, Nat.sub_sub_self (Finset.card_le_card Finset.inter_subset_right)]
        exact (Finset.card_le_card Finset.inter_subset_left).trans (hD i)
      have hgrow := measure_avoids_grow hw.le hTS (fun V hV j _ hj =>
        measure_avoids_insert_ge (hE j) (ih V hV j hj))
      calc
        μ.real (E i ∩ avoidsEvents E S)
            ≤ μ.real (E i ∩ avoidsEvents E T) :=
              measureReal_mono (Set.inter_subset_inter_right _ (avoidsEvents_antitone E hTS))
        _ = μ.real (E i) * μ.real (avoidsEvents E T) := hindep i T hti htd
        _ ≤ x * (1 - x) ^ (S.card - T.card) * μ.real (avoidsEvents E T) := by
          refine mul_le_mul_of_nonneg_right ((hp i).trans ?_) measureReal_nonneg
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw.le (by linarith) hcard) hx₀
        _ ≤ x * μ.real (avoidsEvents E S) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hgrow hx₀
  have hfull := measure_avoids_grow (μ := μ) (E := E) hw.le
    (Finset.empty_subset (Finset.univ : Finset ι))
    (fun V _ j _ hj => measure_avoids_insert_ge (hE j) (hcond V j hj))
  have hempty : avoidsEvents E ∅ = Set.univ := by ext ω; simp [avoidsEvents]
  rw [hempty] at hfull
  have hpos : 0 < μ.real (avoidsEvents E Finset.univ) :=
    (mul_pos (pow_pos hw _) measureReal_univ_pos).trans_le hfull
  have hne : avoidsEvents E Finset.univ ≠ ∅ := by
    intro heq
    rw [heq, measureReal_empty] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact ⟨ω, fun i => hω i (Finset.mem_univ i)⟩

open ProbabilityTheory

private lemma exists_avoiding_local_colourings {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (J : ι → Finset α) (b : ι → Bool) (D : ι → Finset ι)
    {d : ℕ} (hD : ∀ i, (D i).card ≤ d)
    (hJ : ∀ i j, j ∉ D i → Disjoint (J i) (J j))
    {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hp : ∀ i, (1 / 2 : ℝ) ^ (J i).card ≤ x * (1 - x) ^ d) :
    ∃ c : α → Bool, ∀ i, ¬ ∀ e ∈ J i, c e = b i := by
  classical
  let ν := (PMF.uniformOfFintype Bool).toMeasure
  let μ := Measure.pi (fun _ : α => ν)
  let E (i : ι) : Set (α → Bool) := (J i : Set α).pi (fun _ => {b i})
  have hbits (v : Bool) : ν ({v} : Set Bool) = (1 / 2 : ENNReal) := by
    change (PMF.uniformOfFintype Bool).toMeasure {v} = _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply, Fintype.card_bool]
    norm_num [one_div]
  have hν : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hμ : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hmeasure (i : ι) : μ.real (E i) = (1 / 2 : ℝ) ^ (J i).card := by
    change (Measure.pi (fun _ : α => ν)).real ((J i : Set α).pi (fun _ => {b i})) = _
    rw [measureReal_def, Measure.pi_pi_finset]
    simp [hbits]
  have hcoord : iIndepFun (fun (e : α) (c : α → Bool) => c e) μ :=
    iIndepFun_pi (μ := fun _ : α => ν) (X := fun _ => id)
      (fun _ => aemeasurable_id)
  refine exists_avoids_of_local_lemma (μ := μ) E (fun _ => MeasurableSet.of_discrete)
    D hD hx₀ hx₁ (fun i => hmeasure i ▸ hp i) ?_
  intro i S hi hdisj
  let T := S.biUnion J
  have hT (j : S) (e : J j.val) : e.val ∈ T :=
    Finset.mem_biUnion.mpr ⟨j.val, j.property, e.property⟩
  have hd : Disjoint (J i) T := by
    refine Finset.disjoint_left.mpr (fun e he het => ?_)
    obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp het
    have hjD : j ∉ D i := fun hjD => Finset.disjoint_left.mp hdisj hj hjD
    exact Finset.disjoint_left.mp (hJ i j hjD) he hej
  let A : Set (J i → Bool) := {f | ∀ e, f e = b i}
  let B : Set (T → Bool) := {f | ∀ j : S, ¬ ∀ e : J j.val, f ⟨e.val, hT j e⟩ = b j.val}
  have hA : (fun (c : α → Bool) (e : J i) => c e.val) ⁻¹' A = E i := by
    ext c
    simp [A, E, Set.mem_pi, Subtype.forall]
  have hB : (fun (c : α → Bool) (e : T) => c e.val) ⁻¹' B = avoidsEvents E S := by
    ext c
    simp [B, E, avoidsEvents, Set.mem_pi, Subtype.forall]
  have hproj := iIndepFun.indepFun_finset (J i) T hd hcoord (fun _ => measurable_pi_apply _)
  have hmul := hproj.measure_inter_preimage_eq_mul A B MeasurableSet.of_discrete MeasurableSet.of_discrete
  rw [hA, hB] at hmul
  exact (congrArg ENNReal.toReal hmul).trans ENNReal.toReal_mul

/-- A local-lemma criterion using only the size of a clique and the number of possible
cliques that share one of its edges. -/
private lemma lt_ramsey_of_local_bound {n k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hp : (1 / 2 : ℝ) ^ k.choose 2 ≤
      x * (1 - x) ^ (k.choose 2 * (2 * (n - 2).choose (k - 2)))) :
    n < diagonalRamsey k := by
  classical
  let K := (Finset.univ : Finset (Fin n)).powersetCard k
  let I := K ×ˢ (Finset.univ : Finset Bool)
  let J (i : I) := i.val.1.powersetCard 2
  let D (i : I) := Finset.univ.filter (fun j : I => ¬ Disjoint (J i) (J j))
  let F (e : Finset (Fin n)) := (K.filter (e ⊆ ·)) ×ˢ (Finset.univ : Finset Bool)
  have hJ (i : I) : (J i).card = k.choose 2 := by
    have hi := (Finset.mem_powersetCard.mp (Finset.mem_product.mp i.property).1).2
    change (i.val.1.powersetCard 2).card = _
    rw [Finset.card_powersetCard, hi]
  have hF (i : I) (e : Finset (Fin n)) (he : e ∈ J i) :
      (F e).card = 2 * (n - 2).choose (k - 2) := by
    have he₂ := (Finset.mem_powersetCard.mp he).2
    have heq := Finset.card_filter_powersetCard_subset e Finset.univ k (Finset.subset_univ e)
      (show e.card ≤ k by omega)
    change ((K.filter (e ⊆ ·)) ×ˢ (Finset.univ : Finset Bool)).card = _
    rw [Finset.card_product]
    simp [K, heq, he₂, mul_comm]
  have hD (i : I) : (D i).card ≤ k.choose 2 * (2 * (n - 2).choose (k - 2)) := by
    let emb : I ↪ Finset (Fin n) × Bool := Function.Embedding.subtype _
    have hsub : (D i).map emb ⊆ (J i).biUnion F := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨e, hei, hej⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hj).2
      refine Finset.mem_biUnion.mpr ⟨e, hei, Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp j.property).1,
        (Finset.mem_powersetCard.mp hej).1⟩
    calc
      (D i).card = ((D i).map emb).card := (Finset.card_map _).symm
      _ ≤ ((J i).biUnion F).card := Finset.card_le_card hsub
      _ ≤ ∑ e ∈ J i, (F e).card := Finset.card_biUnion_le
      _ = k.choose 2 * (2 * (n - 2).choose (k - 2)) := by
        rw [Finset.sum_congr rfl (hF i), Finset.sum_const, hJ]
        rfl
  have hdisj (i j : I) (hj : j ∉ D i) : Disjoint (J i) (J j) := by
    by_contra h
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  obtain ⟨c, hc⟩ := exists_avoiding_local_colourings J (fun i => i.val.2) D hD hdisj hx₀ hx₁
    (fun i => by rw [hJ]; exact hp)
  have hmono (S : Finset (Fin n)) (hS : S.card = k) (b : Bool) :
      ¬ ∀ e ∈ S.powersetCard 2, c e = b :=
    hc ⟨(S, b), by simp [I, K, hS]⟩
  let G : SimpleGraph (Fin n) :=
    { Adj := fun u v => u ≠ v ∧ c {u, v} = true
      symm := ⟨fun u v h => ⟨h.1.symm, by simpa [Finset.pair_comm v u] using h.2⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  apply lt_ramsey_of_cliqueFree (G := G)
  · intro S hS
    refine hmono S hS.card_eq true (fun e he => ?_)
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
    exact (hS.isClique (hsub (by simp)) (hsub (by simp)) huv).2
  · intro S hS
    refine hmono S hS.card_eq false (fun e he => ?_)
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
    have h := (compl_adj G u v).mp (hS.isClique (hsub (by simp)) (hsub (by simp)) huv)
    exact Bool.eq_false_iff.mpr (fun ht => h.2 ⟨huv, ht⟩)

private lemma lt_ramsey_of_local_count {n k : ℕ} (hk : 2 ≤ k)
    (hp : (1 / 2 : ℝ) ^ k.choose 2 ≤
      1 / (4 * (((k.choose 2 * (2 * (n - 2).choose (k - 2)) : ℕ) : ℝ) + 1))) :
    n < diagonalRamsey k := by
  let d := k.choose 2 * (2 * (n - 2).choose (k - 2))
  let x : ℝ := 1 / (2 * ((d : ℝ) + 1))
  have hx : 0 ≤ x := by positivity
  have hmul : x * (2 * ((d : ℝ) + 1)) = 1 := by
    dsimp [x]
    field_simp
  have hdx := mul_nonneg (show (0 : ℝ) ≤ d by positivity) hx
  have hxle : x ≤ 1 / 2 := by nlinarith only [hmul, hdx]
  have hhalf : (1 / 2 : ℝ) ≤ (1 - x) ^ d := by
    have hb := one_add_mul_sub_le_pow (a := 1 - x) (by linarith : (-1 : ℝ) ≤ 1 - x) d
    nlinarith only [hb, hmul, hx]
  have heq : 1 / (4 * ((d : ℝ) + 1)) = x * (1 / 2) := by
    dsimp [x]
    field_simp
    ring
  apply lt_ramsey_of_local_bound hk hx (show x < 1 by linarith)
  exact hp.trans (heq.trans_le (mul_le_mul_of_nonneg_left hhalf hx))

private lemma two_shift_rpow_pow (j : ℕ) :
    ((2 : ℝ) ^ (((j : ℝ) + 3) / 2)) ^ j * 2 = (2 : ℝ) ^ (j + 2).choose 2 := by
  calc
    _ = (2 : ℝ) ^ ((((j : ℝ) + 3) / 2) * j + 1) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    _ = _ := by
      rw [← Real.rpow_natCast]
      congr 1
      have h := twice_choose_two_real (j + 2)
      push_cast at h
      nlinarith only [h]

private lemma ramsey_eventually_gt_local_comparison {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ∀ᶠ j : ℕ in Filter.atTop,
      t * ((j : ℝ) / Real.exp 1) * (2 : ℝ) ^ (((j : ℝ) + 3) / 2) <
        (diagonalRamsey (j + 2) : ℝ) := by
  have hpoly : Filter.Tendsto (fun j : ℕ => ((j : ℝ) + 2) ^ (2 : ℕ) * t ^ j)
      Filter.atTop (𝓝 0) := by
    have h₂ := tendsto_pow_const_mul_const_pow_of_lt_one 2 ht₀ ht₁
    have h₁ := tendsto_pow_const_mul_const_pow_of_lt_one 1 ht₀ ht₁
    have h₀ := tendsto_pow_atTop_nhds_zero_of_lt_one ht₀ ht₁
    have h := (h₂.add (h₁.const_mul 4)).add (h₀.const_mul 4)
    simp only [mul_zero, add_zero] at h
    refine h.congr fun j => ?_
    ring
  have hpow : Filter.Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 2).choose 2)
      Filter.atTop (𝓝 0) := by
    have h₀ := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    refine h₀.comp (Filter.tendsto_atTop.mpr (fun N => ?_))
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    have hlarge : j ≤ (j + 2).choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      omega
    exact hj.trans hlarge
  have hs := hpoly.add hpow
  rw [add_zero] at hs
  filter_upwards [hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with j hj
  let s : ℝ := (2 : ℝ) ^ (((j : ℝ) + 3) / 2)
  let y : ℝ := t * ((j : ℝ) / Real.exp 1) * s
  let n : ℕ := ⌊y⌋₊
  let B := (j + 2).choose 2
  let d := B * (2 * (n - 2).choose j)
  have hy : 0 ≤ y := by positivity
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  have hn : ((n - 2 : ℕ) : ℝ) ≤ y := (by exact_mod_cast Nat.sub_le n 2 : _ ≤ (n : ℝ)).trans
    (Nat.floor_le hy)
  have hcount : ((n - 2).choose j : ℝ) ≤ t ^ j * s ^ j := calc
    _ ≤ ((n - 2 : ℕ) : ℝ) ^ j / (j.factorial : ℝ) := Nat.choose_le_pow_div j (n - 2)
    _ ≤ y ^ j / (j.factorial : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn j) hfac.le
    _ ≤ t ^ j * s ^ j := by
      apply (div_le_iff₀ hfac).mpr
      dsimp [y]
      rw [mul_pow, mul_pow, mul_right_comm (t ^ j)]
      exact mul_le_mul_of_nonneg_left (factorial_ge_div_exp_pow j) (by positivity)
  have hunit : (s ^ j * 2) * (1 / 2 : ℝ) ^ B = 1 := by
    rw [two_shift_rpow_pow j, one_div, inv_pow, mul_inv_cancel₀ (by positivity)]
  have hdp : (d : ℝ) * (1 / 2 : ℝ) ^ B ≤ (B : ℝ) * t ^ j := calc
    _ = (B : ℝ) * (2 * ((n - 2).choose j : ℝ)) * (1 / 2 : ℝ) ^ B := by simp [d]
    _ ≤ (B : ℝ) * (2 * (t ^ j * s ^ j)) * (1 / 2 : ℝ) ^ B := by gcongr
    _ = (B : ℝ) * t ^ j * ((s ^ j * 2) * (1 / 2 : ℝ) ^ B) := by ring
    _ = _ := by rw [hunit, mul_one]
  have hB : (B : ℝ) ≤ ((j : ℝ) + 2) ^ 2 := by exact_mod_cast Nat.choose_le_pow (j + 2) 2
  have hB' := mul_le_mul_of_nonneg_right hB (pow_nonneg ht₀ j)
  have hprob : (1 / 2 : ℝ) ^ B ≤ 1 / (4 * ((d : ℝ) + 1)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    change (((j : ℝ) + 2) ^ (2 : ℕ) * t ^ j + (1 / 2 : ℝ) ^ B) < 1 / 4 at hj
    nlinarith only [hdp, hB', hj]
  have hramsey : n < diagonalRamsey (j + 2) := by
    apply lt_ramsey_of_local_count (by omega)
    simpa [B, d] using hprob
  have hcast : (n : ℝ) + 1 ≤ (diagonalRamsey (j + 2) : ℝ) := by exact_mod_cast hramsey
  exact (Nat.lt_floor_add_one y).trans_le hcast

/-- The local lemma gives every leading coefficient below `sqrt 2 / exp 1` in the Ramsey
lower bound at the scale `k * 2^(k/2)`. -/
private lemma ramsey_eventually_gt_spencer_lower {c : ℝ} (hc : c < Real.sqrt 2 / Real.exp 1) :
    ∀ᶠ k : ℕ in Filter.atTop,
      c * ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)) < (diagonalRamsey k : ℝ) := by
  let A := Real.sqrt 2 / Real.exp 1
  have hA : 0 < A := by positivity
  obtain ⟨a, ha, haA⟩ := exists_between (max_lt hc hA)
  have ha₀ : 0 < a := (le_max_right c 0).trans_lt ha
  have hca : c < a := (le_max_left c 0).trans_lt ha
  let t := a / A
  have ht₀ : 0 ≤ t := div_nonneg ha₀.le hA.le
  have ht₁ : t < 1 := (div_lt_one hA).mpr haA
  have htA : t * A = a := div_mul_cancel₀ _ hA.ne'
  have hcast : Filter.Tendsto (fun j : ℕ => (j : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hcoeff : ∀ᶠ j : ℕ in Filter.atTop, c * ((j : ℝ) + 2) < a * (j : ℝ) := by
    filter_upwards [hcast.eventually (Filter.eventually_gt_atTop (2 * c / (a - c)))] with j hj
    have h := (div_lt_iff₀ (sub_pos.mpr hca)).mp hj
    linarith
  have hshift : ∀ᶠ j : ℕ in Filter.atTop,
      c * (((j + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (((j + 2 : ℕ) : ℝ) / 2)) <
        (diagonalRamsey (j + 2) : ℝ) := by
    filter_upwards [hcoeff, ramsey_eventually_gt_local_comparison ht₀ ht₁] with j hj hc'
    have hexp : (2 : ℝ) ^ (((j : ℝ) + 3) / 2) =
        Real.sqrt 2 * (2 : ℝ) ^ (((j : ℝ) + 2) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have heq : t * ((j : ℝ) / Real.exp 1) * (2 : ℝ) ^ (((j : ℝ) + 3) / 2) =
        (a * (j : ℝ)) * (2 : ℝ) ^ (((j : ℝ) + 2) / 2) := by
      rw [hexp, ← htA]
      dsimp [A]
      ring
    rw [heq] at hc'
    push_cast
    rw [← mul_assoc]
    exact (mul_lt_mul_of_pos_right hj (by positivity)).trans hc'
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hshift
  refine Filter.eventually_atTop.mpr ⟨N + 2, fun k hk => ?_⟩
  simpa only [Nat.sub_add_cancel (show 2 ≤ k by omega)] using hN (k - 2) (by omega)

private lemma ramsey_root_eventually_gt_spencer_comparison {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < Real.sqrt 2 / Real.exp 1) :
    ∀ᶠ k : ℕ in Filter.atTop,
      Real.sqrt 2 * (c * (k : ℝ)) ^ (1 / (k : ℝ)) < ramseyRoot k := by
  filter_upwards [ramsey_eventually_gt_spencer_lower hc,
    Filter.eventually_ge_atTop (1 : ℕ)] with k hR hk
  have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hs : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ (1 / (k : ℝ)) = Real.sqrt 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow]
    congr 1
    field_simp
  have h := Real.rpow_lt_rpow (by positivity) hR (by positivity : 0 < 1 / (k : ℝ))
  rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity), hs] at h
  simpa only [ramseyRoot, mul_comm] using h


/-- A balanced superadditive minorant gives a lower bound on every subsequential limit. -/
private lemma ramsey_subsequence_ge_balanced_minorant {v : ℕ → ℝ} {K : ℕ}
    (hv : ∀ k, 1 ≤ k → v k ≤ ramseyLog k)
    (h : ∀ a b, K ≤ a → a ≤ b → b ≤ 2 * a → v a + v b ≤ v (a + b))
    {m : ℕ} (hm : 1 ≤ m) (hKm : K ≤ m) {φ : ℕ → ℕ} (hφ : StrictMono φ) {L : ℝ}
    (hL : Filter.Tendsto (ramseyRoot ∘ φ) Filter.atTop (𝓝 L)) :
    Real.exp (v m / m) ≤ L := by
  let r := v m / (m : ℝ)
  have hcomparison : Filter.Tendsto
      (fun k : ℕ => Real.exp (r * (((k / m * m : ℕ) : ℝ) / k)))
      Filter.atTop (𝓝 (Real.exp r)) := by
    have ht := (tendsto_block_multiple_ratio hm).const_mul r
    rw [mul_one] at ht
    exact Real.continuous_exp.continuousAt.tendsto.comp ht
  have hevent : ∀ᶠ k in Filter.atTop,
      Real.exp (r * (((k / m * m : ℕ) : ℝ) / k)) ≤ ramseyRoot k := by
    filter_upwards [Filter.eventually_ge_atTop m] with k hk
    have hk1 := hm.trans hk
    have hq : 1 ≤ k / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hk)
    have hqm : 1 ≤ k / m * m := hm.trans (by simpa using Nat.mul_le_mul_right m hq)
    have hblock := (le_balanced_block_multiple h hKm (k / m) hq).trans (hv _ hqm)
    have hmono : ramseyLog (k / m * m) ≤ ramseyLog k := by
      apply Real.log_le_log
      · exact_mod_cast classical_ramsey_pos hqm hqm
      · exact_mod_cast diagonal_ramsey_mono (Nat.div_mul_le_self k m)
    rw [← exp_ramseyLog_div hk1, Real.exp_le_exp]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    calc
      r * (((k / m * m : ℕ) : ℝ) / k) =
          ((k / m : ℕ) : ℝ) * v m / k := by
        dsimp [r]
        rw [Nat.cast_mul]
        field_simp
      _ ≤ ramseyLog k / k :=
        div_le_div_of_nonneg_right (hblock.trans hmono) (by positivity)
  exact le_of_tendsto_of_tendsto (hcomparison.comp hφ.tendsto_atTop) hL
    (hφ.tendsto_atTop.eventually hevent)

/-- Convergence follows if large corrected roots bound every subsequential limit from below. -/
private lemma ramsey_roots_converge_of_correction {c : ℕ → ℝ} {K : ℕ}
    (hc₀ : Filter.Tendsto c Filter.atTop (𝓝 0))
    (h : ∀ {m}, 1 ≤ m → K ≤ m → ∀ {φ : ℕ → ℕ}, StrictMono φ → ∀ {L : ℝ},
      Filter.Tendsto (ramseyRoot ∘ φ) Filter.atTop (𝓝 L) →
        Real.exp (ramseyLog m / (m : ℝ) - c m) ≤ L) :
    ∃ L : ℝ, Filter.Tendsto ramseyRoot Filter.atTop (𝓝 L) := by
  let a := Filter.liminf ramseyRoot Filter.atTop
  let b := Filter.limsup ramseyRoot Filter.atTop
  have hab : a ≤ b := ramsey_root_liminf_le_limsup
  have hamem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  rw [← ramsey_root_subsequential_limits] at hamem hbmem
  obtain ⟨φ, hφ, hφL⟩ := hamem
  obtain ⟨ψ, hψ, hψL⟩ := hbmem
  have ht : Filter.Tendsto
      (fun j : ℕ => Real.exp (ramseyLog (ψ j) / (ψ j : ℝ) - c (ψ j)))
      Filter.atTop (𝓝 b) := by
    have ht' := Real.continuous_exp.continuousAt.tendsto.comp ((hc₀.comp hψ.tendsto_atTop).neg)
    rw [neg_zero, Real.exp_zero] at ht'
    rw [← mul_one b]
    refine (hψL.mul ht').congr' ?_
    filter_upwards [hψ.tendsto_atTop.eventually (Filter.eventually_ge_atTop (1 : ℕ))] with j hj
    change ramseyRoot (ψ j) * Real.exp (-c (ψ j)) = _
    rw [← exp_ramseyLog_div hj, ← Real.exp_add, sub_eq_add_neg]
  have hba : b ≤ a := by
    refine le_of_tendsto_of_tendsto ht tendsto_const_nhds ?_
    filter_upwards [hψ.tendsto_atTop.eventually (Filter.eventually_ge_atTop (max K 1))] with j hj
    exact h ((le_max_right K 1).trans hj) ((le_max_left K 1).trans hj) hφ hφL
  exact ⟨a, ramsey_root_tendsto_iff.mpr ⟨rfl, hba.antisymm hab⟩⟩

/-- Subtracting a vanishing normalized correction preserves the limit along any subsequence. -/
private lemma ramsey_roots_converge_of_balanced_correction {c : ℕ → ℝ} {K : ℕ}
    (hc : ∀ k, 0 ≤ c k) (hc₀ : Filter.Tendsto c Filter.atTop (𝓝 0))
    (h : ∀ a b, K ≤ a → a ≤ b → b ≤ 2 * a →
      (ramseyLog a - (a : ℝ) * c a) + (ramseyLog b - (b : ℝ) * c b) ≤
        ramseyLog (a + b) - ((a + b : ℕ) : ℝ) * c (a + b)) :
    ∃ L : ℝ, Filter.Tendsto ramseyRoot Filter.atTop (𝓝 L) := by
  apply ramsey_roots_converge_of_correction (K := K) hc₀
  intro m hm hKm φ hφ L hL
  let v (k : ℕ) := ramseyLog k - (k : ℝ) * c k
  have hv (k : ℕ) (_ : 1 ≤ k) : v k ≤ ramseyLog k :=
    sub_le_self _ (mul_nonneg (by positivity) (hc k))
  have hm₀ : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hdiv : v m / (m : ℝ) = ramseyLog m / (m : ℝ) - c m := by
    dsimp [v]
    field_simp
  rw [← hdiv]
  exact ramsey_subsequence_ge_balanced_minorant hv h hm hKm hφ hL

/-- The tail of a summable error bound pays one error term whenever the index doubles. -/
private lemma exists_dyadic_correction {e : ℕ → ℝ} (he : ∀ j, 0 ≤ e j) (hs : Summable e) :
    ∃ c : ℕ → ℝ, (∀ k, 0 ≤ c k) ∧ Filter.Tendsto c Filter.atTop (𝓝 0) ∧ Antitone c ∧
      ∀ a b, 1 ≤ a → 2 * a ≤ b → e (Nat.log 2 a) + c b ≤ c a := by
  let p (j : ℕ) := ∑ i ∈ Finset.range j, e i
  let t (j : ℕ) := (∑' i, e i) - p j
  have hpstep (j : ℕ) : p (j + 1) = p j + e j := Finset.sum_range_succ e j
  have hp : Monotone p := monotone_nat_of_le_succ fun j => by rw [hpstep]; exact le_add_of_nonneg_right (he j)
  have ht (j : ℕ) : 0 ≤ t j := sub_nonneg.mpr (hs.sum_le_tsum (Finset.range j) (fun i _ => he i))
  have ht₀ : Filter.Tendsto t Filter.atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := ∑' i, e i)).sub hs.tendsto_sum_tsum_nat
  have hlog : Filter.Tendsto (Nat.log 2) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr fun j => ?_
    filter_upwards [Filter.eventually_ge_atTop (2 ^ j : ℕ)] with m hm
    exact Nat.le_log_of_pow_le (by omega) hm
  refine ⟨t ∘ Nat.log 2, fun _ => ht _, ht₀.comp hlog, ?_, ?_⟩
  · intro a b hab
    exact sub_le_sub_left (hp (Nat.log_mono_right hab)) _
  · intro a b ha hab
    have hpow := Nat.pow_log_le_self 2 (by omega : a ≠ 0)
    have hpa : Nat.log 2 a + 1 ≤ Nat.log 2 b := by
      apply Nat.le_log_of_pow_le (by omega)
      rw [pow_succ]
      omega
    have hh := hp hpa
    rw [hpstep] at hh
    dsimp [t]
    linarith

/-- Convergence follows if the normalized balanced superadditivity errors admit summable
bounds on dyadic ranges. -/
private lemma ramsey_roots_converge_of_summable_dyadic_loss {e : ℕ → ℝ}
    (he : ∀ j, 0 ≤ e j) (hs : Summable e) {K : ℕ}
    (h : ∀ m n, K ≤ m → m ≤ n → n ≤ 2 * m →
      ramseyLog m + ramseyLog n - ramseyLog (m + n) ≤ (m : ℝ) * e (Nat.log 2 m)) :
    ∃ L : ℝ, Filter.Tendsto ramseyRoot Filter.atTop (𝓝 L) := by
  obtain ⟨c, hc, hc₀, hanti, hstep⟩ := exists_dyadic_correction he hs
  apply ramsey_roots_converge_of_balanced_correction (K := max K 1) hc hc₀
  intro a b ha hab hba
  have hA := mul_le_mul_of_nonneg_left
    (hstep a (a + b) ((le_max_right K 1).trans ha) (by omega)) (show (0 : ℝ) ≤ a by positivity)
  have hB := mul_le_mul_of_nonneg_left (hanti (show b ≤ a + b by omega))
    (show (0 : ℝ) ≤ b by positivity)
  have hAB := h a b ((le_max_left K 1).trans ha) hab hba
  simp only [Nat.cast_add]
  nlinarith only [hA, hB, hAB]


private lemma irrational_log_two_div_log_three : Irrational (Real.log 2 / Real.log 3) := by
  rintro ⟨r, hr⟩
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₃ : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  rw [Rat.cast_def] at hr
  have h : (r.den : ℝ) * Real.log 2 = (r.num : ℝ) * Real.log 3 := by
    field_simp at hr
    linarith only [hr]
  have hn : 0 ≤ r.num := by
    have hnum := nonneg_of_mul_nonneg_left (h ▸ mul_nonneg hd.le h₂.le) h₃
    exact_mod_cast hnum
  rw [← Int.toNat_of_nonneg hn, Int.cast_natCast, ← Real.log_pow, ← Real.log_pow] at h
  have hp := congrArg Real.exp h
  rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at hp
  have hp' : 2 ^ r.den = 3 ^ r.num.toNat := by exact_mod_cast hp
  have hdvd : 2 ∣ 3 ^ r.num.toNat := hp' ▸ dvd_pow_self 2 r.den_ne_zero
  exact (by decide : ¬ (2 : ℕ) ∣ 3) (Nat.prime_two.dvd_of_dvd_pow hdvd)

/-- Positive integral combinations of two incommensurable positive reals eventually
approximate every real from below to any prescribed accuracy. -/
private lemma eventually_approximate_by_additive_semigroup {A B : ℝ}
    (hA : 0 < A) (hAB : Irrational (A / B)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop, ∃ i j : ℕ,
      x - ε < (i : ℝ) * A + (j : ℝ) * B ∧ (i : ℝ) * A + (j : ℝ) * B ≤ x := by
  have hd := dense_addSubgroupClosure_pair_iff.mpr hAB
  have hn : Set.Ioo (0 : ℝ) ε ∈ 𝓝 (ε / 2) := Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨d, hds, hdε⟩ := hd.inter_nhds_nonempty hn
  obtain ⟨a, b, hab⟩ := AddSubgroup.mem_closure_pair.mp hds
  rw [zsmul_eq_mul, zsmul_eq_mul] at hab
  have hdp : 0 < d := hdε.1
  obtain ⟨H, hH⟩ := exists_int_gt (A / d)
  have hH₀ : 0 ≤ H := by exact_mod_cast ((div_pos hA hdp).trans hH).le
  let C : ℤ := H * (|a| + |b|)
  filter_upwards [Filter.eventually_ge_atTop ((C : ℝ) * A + (C : ℝ) * B)] with x hx
  let n : ℤ := ⌊(x - (C : ℝ) * B) / A⌋
  have hnC : C ≤ n := Int.le_floor.mpr ((le_div_iff₀ hA).2 (by linarith))
  let r : ℝ := x - (C : ℝ) * B - (n : ℝ) * A
  have hr₀ : 0 ≤ r := by
    have hh : (n : ℝ) * A ≤ x - (C : ℝ) * B := (le_div_iff₀ hA).1 (Int.floor_le _)
    dsimp [r]
    linarith
  have hrA : r < A := by
    have hh := (div_lt_iff₀ hA).1 (Int.lt_floor_add_one ((x - (C : ℝ) * B) / A))
    change x - (C : ℝ) * B < ((n : ℝ) + 1) * A at hh
    dsimp [r]
    linarith
  let q : ℤ := ⌊r / d⌋
  have hq₀ : 0 ≤ q := Int.le_floor.mpr (by simpa using div_nonneg hr₀ hdp.le)
  have hqH : q ≤ H := by
    have hh : (q : ℝ) ≤ r / d := Int.floor_le _
    exact_mod_cast (hh.trans ((div_lt_div_of_pos_right hrA hdp).trans hH).le)
  have hqz (z : ℤ) (hz : |z| ≤ |a| + |b|) : -C ≤ q * z := by
    have hqabs := mul_le_mul hqH hz (abs_nonneg z) hH₀
    have hqle : |q * z| ≤ C := by simpa [C, abs_mul, abs_of_nonneg hq₀] using hqabs
    exact (abs_le.mp hqle).1
  have hi : 0 ≤ n + q * a := by
    have := hqz a (le_add_of_nonneg_right (abs_nonneg b))
    omega
  have hj : 0 ≤ C + q * b := by
    have := hqz b (le_add_of_nonneg_left (abs_nonneg a))
    omega
  refine ⟨(n + q * a).toNat, (C + q * b).toNat, ?_⟩
  have heq : ((n + q * a).toNat : ℝ) * A + ((C + q * b).toNat : ℝ) * B =
      (n : ℝ) * A + (C : ℝ) * B + (q : ℝ) * d := by
    have hi' : ((n + q * a).toNat : ℝ) = ((n + q * a : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hi
    have hj' : ((C + q * b).toNat : ℝ) = ((C + q * b : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hj
    rw [hi', hj', ← hab]
    push_cast
    ring
  have hqu : (q : ℝ) * d ≤ r := (le_div_iff₀ hdp).1 (Int.floor_le _)
  have hql : r < ((q : ℝ) + 1) * d := (div_lt_iff₀ hdp).1 (Int.lt_floor_add_one _)
  rw [heq]
  dsimp [r] at hqu hql
  constructor <;> linarith [hdε.2]

/-- For fixed m, multiples of m by powers of 2 and 3 approximate every sufficiently
large integer from below with arbitrarily small relative error. -/
private lemma eventually_smooth_multiple {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop, ∃ i j : ℕ,
      m * 2 ^ i * 3 ^ j ≤ k ∧
      Real.exp (-ε) * (k : ℝ) < ((m * 2 ^ i * 3 ^ j : ℕ) : ℝ) := by
  have hlog : Filter.Tendsto (fun k : ℕ => Real.log ((k : ℝ) / m)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by exact_mod_cast hm))
  have h := hlog.eventually (eventually_approximate_by_additive_semigroup
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    irrational_log_two_div_log_three hε)
  filter_upwards [h, Filter.eventually_ge_atTop (1 : ℕ)] with k hk hk₁
  obtain ⟨i, j, hlo, hhi⟩ := hk
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast hm
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast hk₁
  rw [← Real.log_pow, ← Real.log_pow, ← Real.log_mul (by positivity) (by positivity)] at hlo hhi
  have hh := Real.exp_le_exp.mpr hhi
  have hl := Real.exp_lt_exp.mpr hlo
  rw [Real.exp_sub, Real.exp_log (div_pos hk₀ hm₀), Real.exp_log (by positivity)] at hl
  rw [Real.exp_log (div_pos hk₀ hm₀), Real.exp_log (by positivity)] at hh
  refine ⟨i, j, ?_, ?_⟩
  · have hh' := (le_div_iff₀ hm₀).mp hh
    exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using hh' :
      (m : ℝ) * (2 : ℝ) ^ i * (3 : ℝ) ^ j ≤ (k : ℝ))
  · push_cast
    have hl' : Real.exp (-ε) * (k : ℝ) / m < (2 : ℝ) ^ i * (3 : ℝ) ^ j := by
      calc
        Real.exp (-ε) * (k : ℝ) / m = (k : ℝ) / m / Real.exp ε := by
          rw [Real.exp_neg]
          ring
        _ < _ := hl
    simpa [mul_comm, mul_left_comm, mul_assoc] using (div_lt_iff₀ hm₀).mp hl'

private lemma le_of_smooth_multiple {g : ℕ → ℝ} {K : ℕ}
    (h₂ : ∀ m, K ≤ m → g m ≤ g (m * 2)) (h₃ : ∀ m, K ≤ m → g m ≤ g (m * 3))
    {m : ℕ} (hm : K ≤ m) (i j : ℕ) : g m ≤ g (m * 2 ^ i * 3 ^ j) := by
  have hleft (t : ℕ) : m ≤ m * 2 ^ t :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have h' : g m ≤ g (m * 2 ^ i) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← mul_assoc]
      exact ih.trans (h₂ _ (hm.trans (hleft i)))
  induction j with
  | zero => simpa using h'
  | succ j ih =>
    rw [pow_succ, ← mul_assoc]
    exact ih.trans (h₃ _ ((hm.trans (hleft i)).trans (Nat.le_mul_of_pos_right _ (by positivity))))

private lemma ramsey_log_mono_pos {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ramseyLog a ≤ ramseyLog b := by
  apply Real.log_le_log
  · exact_mod_cast classical_ramsey_pos ha ha
  · exact_mod_cast diagonal_ramsey_mono hab

private lemma ramsey_subsequence_ge_dilation_minorant {c : ℕ → ℝ} {K : ℕ}
    (hc : ∀ k, 0 ≤ c k)
    (h₂ : ∀ m, K ≤ m → ramseyLog m / m - c m ≤ ramseyLog (m * 2) / (m * 2 : ℕ) - c (m * 2))
    (h₃ : ∀ m, K ≤ m → ramseyLog m / m - c m ≤ ramseyLog (m * 3) / (m * 3 : ℕ) - c (m * 3))
    {m : ℕ} (hm : 1 ≤ m) (hKm : K ≤ m) {φ : ℕ → ℕ} (hφ : StrictMono φ) {L : ℝ}
    (hL : Filter.Tendsto (ramseyRoot ∘ φ) Filter.atTop (𝓝 L)) :
    Real.exp (ramseyLog m / m - c m) ≤ L := by
  let r := ramseyLog m / (m : ℝ) - c m
  by_cases hr : r ≤ 0
  · have hL₁ : 1 ≤ L := by
      have hL₂ := (ramsey_subsequence_limit_bounds hφ hL).1
      exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num) |>.trans hL₂
    rw [← Real.exp_zero] at hL₁
    exact (Real.exp_le_exp.mpr hr).trans hL₁
  have hεδ (ε : ℝ) (hε : 0 < ε) : Real.exp (Real.exp (-ε) * r) ≤ L := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hL
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_smooth_multiple hm hε),
      hφ.tendsto_atTop.eventually (Filter.eventually_ge_atTop (1 : ℕ))] with t ht ht₁
    obtain ⟨i, j, hij, hratio⟩ := ht
    let s := m * 2 ^ i * 3 ^ j
    have hs : 1 ≤ s := by
      change 0 < m * 2 ^ i * 3 ^ j
      have : 0 < m := hm
      positivity
    have hs₀ : (0 : ℝ) < s := by exact_mod_cast hs
    have ht₀ : (0 : ℝ) < φ t := by exact_mod_cast ht₁
    have hprop : r ≤ ramseyLog s / (s : ℝ) - c s := le_of_smooth_multiple h₂ h₃ hKm i j
    have hlow : r * (s : ℝ) ≤ ramseyLog s :=
      (le_div_iff₀ hs₀).1 (hprop.trans (sub_le_self _ (hc s)))
    have hmono := ramsey_log_mono_pos hs hij
    have hmul := mul_le_mul_of_nonneg_right hratio.le (le_of_not_ge hr)
    change Real.exp (Real.exp (-ε) * r) ≤ ramseyRoot (φ t)
    rw [← exp_ramseyLog_div ht₁, Real.exp_le_exp, le_div_iff₀ ht₀]
    calc
      (Real.exp (-ε) * r) * (φ t : ℝ) = (Real.exp (-ε) * (φ t : ℝ)) * r := by ring
      _ ≤ (s : ℝ) * r := hmul
      _ ≤ ramseyLog (φ t) := by rw [mul_comm]; exact hlow.trans hmono
  have hcont : Continuous (fun ε : ℝ => Real.exp (Real.exp (-ε) * r)) := by fun_prop
  have ht : Filter.Tendsto (fun ε : ℝ => Real.exp (Real.exp (-ε) * r))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp r)) := by
    have ht' : ContinuousWithinAt (fun ε : ℝ => Real.exp (Real.exp (-ε) * r))
        (Set.Ioi 0) 0 := hcont.continuousAt.continuousWithinAt
    simpa using ht'.tendsto
  exact le_of_tendsto ht (eventually_mem_nhdsWithin.mono fun ε hε => hεδ ε hε)

/-- It suffices to obtain summable normalized growth errors just for doubling and tripling. -/
private lemma ramsey_roots_converge_of_summable_dilation_loss {e : ℕ → ℝ}
    (he : ∀ j, 0 ≤ e j) (hs : Summable e) {K : ℕ}
    (h : ∀ q : ℕ, q = 2 ∨ q = 3 → ∀ m, K ≤ m →
      ramseyLog m / (m : ℝ) - ramseyLog (m * q) / ((m * q : ℕ) : ℝ) ≤ e (Nat.log 2 m)) :
    ∃ L : ℝ, Filter.Tendsto ramseyRoot Filter.atTop (𝓝 L) := by
  obtain ⟨c, hc, hc₀, _, hstep⟩ := exists_dyadic_correction he hs
  have hcscale (q : ℕ) (hq : q = 2 ∨ q = 3) (m : ℕ) (hm : max K 1 ≤ m) :
      ramseyLog m / (m : ℝ) - c m ≤ ramseyLog (m * q) / ((m * q : ℕ) : ℝ) - c (m * q) := by
    have hq' : 2 ≤ q := by omega
    have hmq : 2 * m ≤ m * q := by
      rw [mul_comm 2 m]
      exact Nat.mul_le_mul_left _ hq'
    linarith only [h q hq m ((le_max_left K 1).trans hm),
      hstep m (m * q) ((le_max_right K 1).trans hm) hmq]
  apply ramsey_roots_converge_of_correction (K := max K 1) hc₀
  intro m hm hKm φ hφ L hL
  exact ramsey_subsequence_ge_dilation_minorant hc (hcscale 2 (Or.inl rfl))
    (hcscale 3 (Or.inr rfl)) hm hKm hφ hL

end OMA.DiagonalRamsey

noncomputable def OMA.answer : ℝ := sorry

theorem OMA.solution : Erdos77.erdos_77.answer = OMA.answer → type_of% @Erdos77.erdos_77 := by
  intro h
  rw [h]
  sorry

