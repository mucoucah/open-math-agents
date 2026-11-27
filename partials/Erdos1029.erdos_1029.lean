import FormalConjectures.ErdosProblems.«1029»

/-! Finite graph formulations of the diagonal Ramsey lower bound. -/

-- Problem: Erdős Problem 1029
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1029.lean:48 (declaration Erdos1029.erdos_1029)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter SimpleGraph

namespace Erdos1029Relay

private def ForcesClique (n k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ Gᶜ.CliqueFree k)

private lemma forcesClique_mono {n m k : ℕ} (hnm : n ≤ m) :
    ForcesClique n k → ForcesClique m k := by
  intro hn G hG
  let e : Fin n ↪ Fin m := Fin.castLEEmb hnm
  let H := G.comap e
  let f : H ↪g G := SimpleGraph.Embedding.comap e G
  exact hn H ⟨hG.1.comap f.isContained, hG.2.comap f.complEquiv.isContained⟩

private lemma forcesClique_choose (k : ℕ) : ForcesClique ((k + k).choose k) k := by
  classical
  intro G hG
  let c (s : Finset (Fin ((k + k).choose k))) : Bool :=
    decide (G.IsClique (s : Set _))
  rcases Combinatorics.Diagonal.hasRamseyProperty_choose k k c Finset.univ (by simp)
    with ⟨s, _, hs, hm⟩ | ⟨s, _, hs, hm⟩
  · apply hG.2 s
    refine ⟨?_, hs⟩
    intro x hx y hy hxy
    have hc := hm {x, y}
      (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) (Finset.card_pair hxy)
    have hn : ¬ G.Adj x y := by simpa [c, hxy] using hc
    exact (G.compl_adj x y).2 ⟨hxy, hn⟩
  · apply hG.1 s
    refine ⟨?_, hs⟩
    intro x hx y hy hxy
    have hc := hm {x, y}
      (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) (Finset.card_pair hxy)
    simpa [c, hxy] using hc

private lemma lt_diagonalRamsey_iff (n k : ℕ) :
    n < diagonalRamsey k ↔
      ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  classical
  have heq : diagonalRamsey k = sInf {m | ForcesClique m k} := by
    simp only [diagonalRamsey, classicalRamsey, graphRamsey, ForcesClique,
      not_and_or, not_cliqueFree_iff_top_isContained]
  have hmem : diagonalRamsey k ∈ {m | ForcesClique m k} :=
    heq ▸ Nat.sInf_mem ⟨_, forcesClique_choose k⟩
  have hiff : diagonalRamsey k ≤ n ↔ ForcesClique n k :=
    ⟨fun hn ↦ forcesClique_mono hn hmem, fun hn ↦ heq.trans_le (Nat.sInf_le hn)⟩
  rw [← not_le, hiff]
  simp [ForcesClique]

private noncomputable def scale (k : ℕ) : ℝ :=
  (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2)

private lemma scale_pos {k : ℕ} (hk : 0 < k) : 0 < scale k := by
  unfold scale
  positivity

private lemma tendsto_iff_cliqueFree_graphs :
    Tendsto (fun k : ℕ ↦ (diagonalRamsey k : ℝ) / scale k) atTop atTop ↔
      ∀ a : ℕ, ∀ᶠ k : ℕ in atTop,
        ∃ G : SimpleGraph (Fin ⌊(a : ℝ) * scale k⌋₊), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  have hk : ∀ᶠ k : ℕ in atTop, 0 < k := eventually_gt_atTop 0
  constructor
  · intro h a
    filter_upwards [(tendsto_atTop.1 h) ((a : ℝ) + 1), hk] with k ha hk'
    apply (lt_diagonalRamsey_iff _ _).mp
    have hlt : (a : ℝ) < (diagonalRamsey k : ℝ) / scale k := by linarith
    exact (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg a) (scale_pos hk').le)).2
      ((lt_div_iff₀ (scale_pos hk')).1 hlt)
  · intro h
    refine tendsto_atTop.2 fun b ↦ ?_
    obtain ⟨a, ha⟩ := exists_nat_ge b
    filter_upwards [h a, hk] with k hG hk'
    have hlt := (lt_diagonalRamsey_iff _ _).2 hG
    exact ha.trans ((lt_div_iff₀ (scale_pos hk')).2 (Nat.lt_of_floor_lt hlt)).le

private lemma scale_even (t : ℕ) : scale (2 * t) = (2 : ℝ) * t * 2 ^ t := by
  have hexp : ((2 * t : ℕ) : ℝ) / 2 = (t : ℝ) := by push_cast; ring
  rw [scale, hexp, Real.rpow_natCast]
  push_cast
  norm_num

private lemma floor_mul_scale_even (a t : ℕ) :
    ⌊(a : ℝ) * scale (2 * t)⌋₊ = a * (2 * t * 2 ^ t) := by
  have h : (a : ℝ) * scale (2 * t) = ((a * (2 * t * 2 ^ t) : ℕ) : ℝ) := by
    simp only [scale_even, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [h, Nat.floor_natCast]

private lemma scale_le_four_mul_of_div_two {k : ℕ} (hk : 2 ≤ k) :
    scale k ≤ 4 * scale (2 * (k / 2)) := by
  let j := 2 * (k / 2)
  change scale k ≤ 4 * scale j
  have hnat : k ≤ j + 1 ∧ 1 ≤ j := by dsimp [j]; omega
  have hk' : (k : ℝ) ≤ 2 * j := by
    exact_mod_cast (show k ≤ 2 * j by omega)
  have hpow : (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 2 * (2 : ℝ) ^ ((j : ℝ) / 2) := by
    have hreal : (k : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hnat.1
    calc
      (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (2 : ℝ) ^ (1 + (j : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 * (2 : ℝ) ^ ((j : ℝ) / 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  calc
    scale k ≤ (2 * (j : ℝ)) * (2 * (2 : ℝ) ^ ((j : ℝ) / 2)) :=
      mul_le_mul hk' hpow (by positivity) (by positivity)
    _ = 4 * scale j := by unfold scale; ring

private lemma tendsto_iff_even_cliqueFree_graphs :
    Tendsto (fun k : ℕ ↦ (diagonalRamsey k : ℝ) / scale k) atTop atTop ↔
      ∀ a : ℕ, ∀ᶠ t : ℕ in atTop,
        ∃ G : SimpleGraph (Fin (a * (2 * t * 2 ^ t))),
          G.CliqueFree (2 * t) ∧ Gᶜ.CliqueFree (2 * t) := by
  rw [tendsto_iff_cliqueFree_graphs]
  constructor
  · intro h a
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h a)
    refine eventually_atTop.2 ⟨N, fun t ht ↦ ?_⟩
    rw [← floor_mul_scale_even a t]
    exact hN (2 * t) (by omega)
  · intro h a
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h (4 * a))
    refine eventually_atTop.2 ⟨2 * N + 2, fun k hk ↦ ?_⟩
    let j := 2 * (k / 2)
    have hjk : j ≤ k := by dsimp [j]; omega
    have hn : ⌊(a : ℝ) * scale k⌋₊ ≤ (4 * a) * (2 * (k / 2) * 2 ^ (k / 2)) := by
      rw [← floor_mul_scale_even (4 * a) (k / 2)]
      apply Nat.floor_mono
      calc
        (a : ℝ) * scale k ≤ (a : ℝ) * (4 * scale j) :=
          mul_le_mul_of_nonneg_left (scale_le_four_mul_of_div_two (by omega)) (by positivity)
        _ = ((4 * a : ℕ) : ℝ) * scale j := by push_cast; ring
    obtain ⟨G, hG, hGc⟩ := hN (k / 2) (by omega)
    let e := Fin.castLEEmb hn
    let f := SimpleGraph.Embedding.comap e G
    exact ⟨G.comap e, (hG.mono hjk).comap f.isContained,
      (hGc.mono hjk).comap f.complEquiv.isContained⟩

end Erdos1029Relay

theorem OMA.solution : type_of% @Erdos1029.erdos_1029 := by
  apply Erdos1029Relay.tendsto_iff_even_cliqueFree_graphs.mpr
  sorry

