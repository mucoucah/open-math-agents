import FormalConjectures.ErdosProblems.«552»

-- Problem: Erdős Problem 552 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/552.lean:60 (declaration Erdos552.erdos_552.parts.ii)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Local degree bounds for the four-cycle versus star Ramsey problem. -/

namespace OMA.Erdos552Helpers

open SimpleGraph Finset

private theorem star_iff_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    (completeBipartiteGraph (Fin 1) (Fin n)).IsContained G ↔
      ∃ v, n ≤ G.degree v := by
  classical
  constructor
  · rintro ⟨copy⟩
    let v := copy (Sum.inl 0)
    let leaves : Fin n ↪ G.neighborSet v :=
      ⟨fun i => ⟨copy (Sum.inr i), copy.toHom.map_adj (by simp [completeBipartiteGraph])⟩,
       fun i j h => Sum.inr_injective (copy.injective (congrArg Subtype.val h))⟩
    refine ⟨v, ?_⟩
    simpa only [Fintype.card_fin, card_neighborSet_eq_degree] using
      Fintype.card_le_of_embedding leaves
  · rintro ⟨v, hv⟩
    have hcard : Fintype.card (Fin n) ≤ Fintype.card (G.neighborSet v) := by
      simpa only [Fintype.card_fin, card_neighborSet_eq_degree] using hv
    obtain ⟨leaves⟩ := Function.Embedding.nonempty_of_card_le hcard
    let f : Fin 1 ⊕ Fin n → V := Sum.elim (fun _ => v) (fun i => (leaves i).val)
    have hleaf (i : Fin n) : G.Adj v (leaves i).val := (leaves i).property
    have hinj : Function.Injective f := by
      intro a b h
      cases a <;> cases b <;> simp only [f, Sum.elim_inl, Sum.elim_inr] at h
      · congr 1
        apply Subsingleton.elim
      · exact (G.ne_of_adj (hleaf _) h).elim
      · exact (G.ne_of_adj (hleaf _) h.symm).elim
      · exact congrArg Sum.inr (leaves.injective (Subtype.ext h))
    apply isContained_iff_exists_le_comap.mpr
    refine ⟨⟨f, hinj⟩, ?_⟩
    intro a b h
    cases a <;> cases b <;> simp_all [completeBipartiteGraph, f, Adj.symm]

private theorem common_neighbor_unique {V : Type*} (G : SimpleGraph V)
    (hfree : ¬ (cycleGraph 4).IsContained G) {v w a b : V}
    (hvw : v ≠ w) (hva : G.Adj v a) (haw : G.Adj a w)
    (hvb : G.Adj v b) (hbw : G.Adj b w) : a = b := by
  classical
  by_contra hab
  have hne₁ := G.ne_of_adj hva
  have hne₂ := G.ne_of_adj haw
  have hne₃ := G.ne_of_adj hvb
  have hne₄ := G.ne_of_adj hbw
  let f : Fin 4 → V := ![v, a, w, b]
  have hinj : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [f] at h ⊢ <;> grind
  apply hfree
  apply isContained_iff_exists_le_comap.mpr
  refine ⟨⟨f, hinj⟩, ?_⟩
  intro i j h
  change G.Adj (f i) (f j)
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact absurd h (by decide)
    | exact hva
    | exact hva.symm
    | exact haw
    | exact haw.symm
    | exact hvb
    | exact hvb.symm
    | exact hbw
    | exact hbw.symm

theorem degree_mul_sub_one_le {N d : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (hfree : ¬ (cycleGraph 4).IsContained G)
    (hmin : ∀ x, d ≤ G.degree x) (v : Fin N) :
    G.degree v * (d - 1) ≤ N - 1 := by
  classical
  let second (a : Fin N) := (G.neighborFinset a).erase v
  have hdisj : ((G.neighborFinset v : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint second := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr fun w hwa hwb => hab ?_
    have hva : G.Adj v a := (G.mem_neighborFinset v a).mp ha
    have hvb : G.Adj v b := (G.mem_neighborFinset v b).mp hb
    have hwa' := Finset.mem_erase.mp hwa
    have hwb' := Finset.mem_erase.mp hwb
    exact common_neighbor_unique G hfree (Ne.symm hwa'.1) hva
      ((G.mem_neighborFinset a w).mp hwa'.2) hvb ((G.mem_neighborFinset b w).mp hwb'.2)
  have hsub : (G.neighborFinset v).biUnion second ⊆ Finset.univ.erase v := by
    intro w hw
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, Finset.mem_univ _⟩
  have hsum : ∑ _a ∈ G.neighborFinset v, (d - 1) ≤
      ∑ a ∈ G.neighborFinset v, (second a).card := by
    apply Finset.sum_le_sum
    intro a ha
    have hrev : v ∈ G.neighborFinset a := (G.mem_neighborFinset a v).mpr ((G.mem_neighborFinset v a).mp ha).symm
    rw [show (second a).card = G.degree a - 1 from Finset.card_erase_of_mem hrev]
    exact Nat.sub_le_sub_right (hmin a) 1
  calc
    G.degree v * (d - 1) = ∑ _a ∈ G.neighborFinset v, (d - 1) := by
      simp only [Finset.sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul, Nat.cast_id]
    _ ≤ ∑ a ∈ G.neighborFinset v, (second a).card := hsum
    _ = ((G.neighborFinset v).biUnion second).card := (Finset.card_biUnion hdisj).symm
    _ ≤ N - 1 := by simpa using Finset.card_le_card hsub

open scoped Classical

private noncomputable abbrev fourStarRamsey (n : ℕ) :=
  graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n))

private def RamseyOrders (n : ℕ) : Set ℕ :=
  {N | ∀ G : SimpleGraph (Fin N), (cycleGraph 4).IsContained G ∨
    (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Gᶜ}

def DegreeObstruction (N d : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin N), ¬ (cycleGraph 4).IsContained G ∧
    ∀ v, d ≤ G.degree v

private theorem mem_orders_iff {n N : ℕ} :
    N ∈ RamseyOrders n ↔ ¬ DegreeObstruction N (N - n) := by
  have hdeg (G : SimpleGraph (Fin N)) (v : Fin N) :
      n ≤ Gᶜ.degree v ↔ G.degree v < N - n := by
    have hlt := G.degree_lt_card_verts v
    rw [G.degree_compl, Fintype.card_fin]
    simp only [Fintype.card_fin] at hlt
    omega
  constructor
  · intro h
    rintro ⟨G, hfree, hmin⟩
    rcases h G with hcycle | hstar
    · exact hfree hcycle
    · obtain ⟨v, hv⟩ := (star_iff_degree _ _).mp hstar
      exact (Nat.not_lt_of_ge (hmin v)) ((hdeg G v).mp hv)
  · intro h G
    by_cases hcycle : (cycleGraph 4).IsContained G
    · exact Or.inl hcycle
    · right
      by_contra hstar
      apply h
      refine ⟨G, hcycle, fun v => Nat.le_of_not_gt ?_⟩
      exact fun hv => hstar ((star_iff_degree _ _).mpr ⟨v, (hdeg G v).mpr hv⟩)

private theorem orders_nonempty (n : ℕ) : (RamseyOrders n).Nonempty := by
  refine ⟨2 * n + 2, mem_orders_iff.mpr ?_⟩
  rintro ⟨G, hfree, hmin⟩
  let v : Fin (2 * n + 2) := ⟨0, by omega⟩
  have hv := hmin v
  rw [show 2 * n + 2 - n = n + 2 by omega] at hv hmin
  have hcount := degree_mul_sub_one_le G hfree hmin v
  rw [show n + 2 - 1 = n + 1 by omega, show 2 * n + 2 - 1 = 2 * n + 1 by omega] at hcount
  have hlower := Nat.mul_le_mul_right (n + 1) hv
  nlinarith

private theorem orders_mono {n M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ RamseyOrders n) : N ∈ RamseyOrders n := by
  intro G
  let e := Fin.castLEEmb hMN
  have hc : (G.comap e)ᶜ = Gᶜ.comap e := by
    ext u v
    simp only [compl_adj, comap_adj, e.injective.ne_iff]
  rcases hM (G.comap e) with h | h
  · exact Or.inl (h.trans ⟨(SimpleGraph.Embedding.comap e G).toCopy⟩)
  · rw [hc] at h
    exact Or.inr (h.trans ⟨(SimpleGraph.Embedding.comap e Gᶜ).toCopy⟩)

private theorem ramsey_le_iff_no_obstruction {n N : ℕ} :
    fourStarRamsey n ≤ N ↔ ¬ DegreeObstruction N (N - n) := by
  change sInf (RamseyOrders n) ≤ N ↔ _
  rw [← mem_orders_iff]
  exact ⟨fun h => orders_mono h (Nat.sInf_mem (orders_nonempty n)), Nat.sInf_le⟩

/-- For every fixed degree deficit there are arbitrarily large orders with no obstruction. -/
def DegreeCriterion : Prop :=
  ∀ K B : ℕ, ∃ N : ℕ, B < N ∧ ¬ DegreeObstruction N (Nat.sqrt N - K)

theorem degree_criterion_iff :
    DegreeCriterion ↔ ∀ c : ℝ, 0 < c →
      Set.Infinite {n : ℕ | (fourStarRamsey n : ℝ) ≤ (n : ℝ) + Real.sqrt n - c} := by
  constructor
  · intro criterion c hc
    rw [Set.infinite_iff_exists_gt]
    intro B
    obtain ⟨K, hK⟩ := exists_nat_ge (c + 1)
    obtain ⟨N, hN, hno⟩ := criterion K ((B + K + 2)^2)
    let s := Nat.sqrt N
    let d := s - K
    let n := N - d
    have hsB : B + K + 2 ≤ s := Nat.le_sqrt'.mpr hN.le
    have hsN : s ≤ N := Nat.sqrt_le_self N
    have hs2 : s^2 ≤ N := Nat.sqrt_le' N
    have hd : d ≤ s := Nat.sub_le s K
    have hnd : n + d = N := Nat.sub_add_cancel (hd.trans hsN)
    have hNk : N - n = d := by omega
    have hram : fourStarRamsey n ≤ N :=
      ramsey_le_iff_no_obstruction.mpr (hNk.symm ▸ hno)
    have hpoly : (s - 1)^2 + s ≤ s^2 := by
      let t := s - 1
      have hst : s = t + 1 := by dsimp [t]; omega
      change t^2 + s ≤ s^2
      rw [hst]
      nlinarith
    have hsq : (s - 1)^2 ≤ n := by omega
    have hsqrt : s - 1 ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hsq
    refine ⟨n, ?_, by have := Nat.sqrt_le_self n; omega⟩
    change (fourStarRamsey n : ℝ) ≤ (n : ℝ) + Real.sqrt n - c
    have hramR : (fourStarRamsey n : ℝ) ≤ (n : ℝ) + (d : ℝ) := by
      exact_mod_cast (hnd.symm ▸ hram : fourStarRamsey n ≤ n + d)
    have hdR : (d : ℝ) + (K : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
      exact_mod_cast (show d + K ≤ Nat.sqrt n + 1 by dsimp [d]; omega)
    linarith [Real.nat_sqrt_le_real_sqrt (a := n)]
  · intro target K B
    have hpos : 0 < (K : ℝ) + 2 := by positivity
    obtain ⟨n, hn, hB⟩ := (Set.infinite_iff_exists_gt.mp (target _ hpos)) (max B ((K+1)^2))
    have hKn : K + 1 ≤ Nat.sqrt n := Nat.le_sqrt'.mpr (le_of_lt ((le_max_right _ _).trans_lt hB))
    let d := Nat.sqrt n - (K + 1)
    let N := n + d
    have hnat : fourStarRamsey n + (K + 1) ≤ n + Nat.sqrt n := by
      change (fourStarRamsey n : ℝ) ≤ (n : ℝ) + Real.sqrt n - ((K : ℝ) + 2) at hn
      have hreal : (fourStarRamsey n : ℝ) + ((K : ℝ) + 1) ≤ (n : ℝ) + (Nat.sqrt n : ℝ) := by
        linarith [Real.real_sqrt_lt_nat_sqrt_succ (a := n)]
      exact_mod_cast hreal
    have hram : fourStarRamsey n ≤ N := by dsimp [N, d]; omega
    refine ⟨N, (le_max_left _ _).trans_lt (hB.trans_le (Nat.le_add_right n d)), ?_⟩
    have hsub : N - n = d := by simp [N]
    have hno : ¬ DegreeObstruction N d := hsub ▸ ramsey_le_iff_no_obstruction.mp hram
    have hmon : Nat.sqrt n ≤ Nat.sqrt N := Nat.sqrt_le_sqrt (Nat.le_add_right n d)
    have hdom : d ≤ Nat.sqrt N - K :=
      (Nat.sub_le_sub_right hmon (K + 1)).trans
        (Nat.sub_le_sub_left (Nat.le_succ K) (Nat.sqrt N))
    rintro ⟨G, hfree, hmin⟩
    exact hno ⟨G, hfree, fun v => hdom.trans (hmin v)⟩

/-- Any obstruction at a sufficiently large order has all its degrees in a fixed-width interval. -/
theorem degree_range {N K : ℕ} (hlarge : (K + 4) * (K + 1) ≤ Nat.sqrt N)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hfree : ¬ (cycleGraph 4).IsContained G)
    (hmin : ∀ v, Nat.sqrt N - K ≤ G.degree v) (v : Fin N) :
    Nat.sqrt N - K ≤ G.degree v ∧ G.degree v ≤ Nat.sqrt N + K + 3 := by
  refine ⟨hmin v, ?_⟩
  let s := Nat.sqrt N
  let t := s - (K + 1)
  have hlarge' : (K + 4) * (K + 1) ≤ s := hlarge
  have hKs : K + 1 ≤ s := by nlinarith only [hlarge']
  have hst : s = t + (K + 1) := by dsimp [t]; omega
  have hcount := degree_mul_sub_one_le G hfree hmin v
  have hcount' : G.degree v * t ≤ N - 1 := by
    rwa [show Nat.sqrt N - K - 1 = t by dsimp [t, s]; omega] at hcount
  have hN : N < (s + 1)^2 := Nat.lt_succ_sqrt' N
  have hNpos : 0 < N := Nat.zero_lt_of_lt v.isLt
  have hpred : N - 1 + 1 = N := by omega
  have hupper : N - 1 < s^2 + 2 * s := by nlinarith only [hN, hpred]
  have hprod : (s + K + 4) * t + (K + 4) * (K + 1) = s^2 + 3 * s := by
    have hmul := congrArg (fun x : ℕ => (s + K + 4) * x) hst
    nlinarith only [hmul]
  by_contra h
  have hdeg : s + K + 4 ≤ G.degree v := by omega
  have hmul := Nat.mul_le_mul_right t hdeg
  nlinarith only [hcount', hmul, hupper, hprod, hlarge']

/-- Deleting a vertex and some of its neighbors costs each survivor at most two neighbors. -/
theorem DegreeObstruction.shrink_once {M d r : ℕ} (hrM : r ≤ M) (hrd : r ≤ d + 1)
    (h : DegreeObstruction M d) : DegreeObstruction (M - r) (d - 2) := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨G, hfree, hmin⟩ := h
    exact ⟨G, hfree, fun v => (Nat.sub_le _ _).trans (hmin v)⟩
  obtain ⟨G, hfree, hmin⟩ := h
  let v : Fin M := ⟨0, hr.trans_le hrM⟩
  obtain ⟨T, hT, hcardT⟩ := Finset.exists_subset_card_eq
    (s := G.neighborFinset v) (n := r - 1) (by
      rw [card_neighborFinset_eq_degree]
      exact (show r - 1 ≤ d by omega).trans (hmin v))
  let D := insert v T
  have hvT : v ∉ T := fun hv => G.irrefl ((G.mem_neighborFinset v v).mp (hT hv))
  have hcardD : D.card = r := by
    dsimp [D]
    rw [Finset.card_insert_of_notMem hvT, hcardT]
    omega
  let e : Fin (M - r) ≃ ↥(Dᶜ) := (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hcardD])).symm
  let f : Fin (M - r) ↪ Fin M := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hf (w : Fin (M - r)) : f w ∉ D := Finset.mem_compl.mp (e w).property
  let H := G.comap f
  refine ⟨H, fun hc => hfree (hc.trans ⟨(SimpleGraph.Embedding.comap f G).toCopy⟩), ?_⟩
  intro w
  have hwv : f w ≠ v := fun heq => hf w (Finset.mem_insert.mpr (Or.inl heq))
  have hone : (G.neighborFinset (f w) ∩ T).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    obtain ⟨hwa, hva⟩ := Finset.mem_inter.mp ha
    obtain ⟨hwb, hvb⟩ := Finset.mem_inter.mp hb
    exact common_neighbor_unique G hfree hwv ((G.mem_neighborFinset _ _).mp hwa)
      ((G.mem_neighborFinset _ _).mp (hT hva)).symm
      ((G.mem_neighborFinset _ _).mp hwb)
      ((G.mem_neighborFinset _ _).mp (hT hvb)).symm
  have htwo : (G.neighborFinset (f w) ∩ D).card ≤ 2 := by
    have hsub : G.neighborFinset (f w) ∩ D ⊆ insert v (G.neighborFinset (f w) ∩ T) := by
      intro a ha
      obtain ⟨hwa, haD⟩ := Finset.mem_inter.mp ha
      rcases Finset.mem_insert.mp haD with rfl | haT
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hwa, haT⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))
  have hcard : (G.neighborFinset (f w) \ D).card = H.degree w := by
    rw [← card_neighborFinset_eq_degree]
    symm
    refine Finset.card_bij (fun x _ => f x) ?_ (fun _ _ _ _ heq => f.injective heq) ?_
    · intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨(G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp hx), hf x⟩
    · intro y hy
      obtain ⟨hyadj, hyD⟩ := Finset.mem_sdiff.mp hy
      let y' : ↥(Dᶜ) := ⟨y, Finset.mem_compl.mpr hyD⟩
      let x := e.symm y'
      have heq : f x = y := congrArg Subtype.val (e.apply_symm_apply y')
      refine ⟨x, (H.mem_neighborFinset _ _).mpr ?_, heq⟩
      change G.Adj (f w) (f x)
      rw [heq]
      exact (G.mem_neighborFinset _ _).mp hyadj
  have hpartition := Finset.card_sdiff_add_card_inter (G.neighborFinset (f w)) D
  rw [hcard, card_neighborFinset_eq_degree] at hpartition
  have hw := hmin (f w)
  have hlower : d - 2 ≤ H.degree w := by omega
  exact hlower

/-- Obstructions can be transferred to nearby smaller orders with bounded degree loss. -/
theorem DegreeObstruction.shrink {N M d steps : ℕ} (hNM : N ≤ M)
    (hgap : M - N ≤ steps * (d + 1))
    (h : DegreeObstruction M (d + 2 * steps)) : DegreeObstruction N d := by
  induction steps generalizing M with
  | zero =>
    have heq : M = N := by simpa using (Nat.sub_eq_zero_iff_le.mp (by simpa using hgap)).antisymm hNM
    simpa [heq] using h
  | succ steps ih =>
    let r := min (M - N) (d + 1)
    have hrM : r ≤ M := (min_le_left _ _).trans (Nat.sub_le _ _)
    have hrd : r ≤ d + 2 * (steps + 1) + 1 := by
      have := min_le_right (M - N) (d + 1)
      omega
    have hremain : M - r - N ≤ steps * (d + 1) := by
      rw [Nat.succ_mul] at hgap
      dsimp [r]
      omega
    have hsub : N ≤ M - r := by
      have := min_le_left (M - N) (d + 1)
      omega
    apply ih hsub hremain
    have hdegree := h.shrink_once hrM hrd
    rwa [show d + 2 * (steps + 1) - 2 = d + 2 * steps by omega] at hdegree

/-- It is enough to test a set of orders with gaps bounded on the square-root scale. -/
theorem sampled_degree_criterion_iff {S : Set ℕ} {C A : ℕ}
    (hcover : ∀ N : ℕ, A ≤ N → ∃ M ∈ S, N ≤ M ∧ M ≤ N + C * (Nat.sqrt N + 1)) :
    DegreeCriterion ↔
      ∀ K B : ℕ, ∃ M : ℕ, B < M ∧ M ∈ S ∧ ¬ DegreeObstruction M (Nat.sqrt M - K) := by
  constructor
  · intro h K B
    obtain ⟨N, hN, hno⟩ := h (K + 4 * C) (max B (max A ((2 * (K + 4 * C)) ^ 2)))
    have hbase : max A ((2 * (K + 4 * C)) ^ 2) ≤ N := (le_max_right _ _).trans hN.le
    obtain ⟨M, hMS, hNM, hgap⟩ := hcover N ((le_max_left _ _).trans hbase)
    refine ⟨M, ((le_max_left _ _).trans_lt hN).trans_le hNM, hMS, ?_⟩
    intro hM
    let d := Nat.sqrt N - (K + 4 * C)
    have hlarge : 2 * (K + 4 * C) ≤ Nat.sqrt N :=
      Nat.le_sqrt'.mpr ((le_max_right _ _).trans hbase)
    have hd : Nat.sqrt N + 1 ≤ 2 * (d + 1) := by dsimp [d]; omega
    have hsteps : M - N ≤ (2 * C) * (d + 1) := calc
      M - N ≤ C * (Nat.sqrt N + 1) := by omega
      _ ≤ C * (2 * (d + 1)) := Nat.mul_le_mul_left C hd
      _ = (2 * C) * (d + 1) := by ring
    have hthreshold : d + 2 * (2 * C) ≤ Nat.sqrt M - K := by
      have hs := Nat.sqrt_le_sqrt hNM
      dsimp [d]
      omega
    obtain ⟨G, hfree, hmin⟩ := hM
    have hstrong : DegreeObstruction M (d + 2 * (2 * C)) :=
      ⟨G, hfree, fun v => hthreshold.trans (hmin v)⟩
    exact hno (hstrong.shrink hNM hsteps)
  · intro h K B
    obtain ⟨M, hM, _, hno⟩ := h K B
    exact ⟨M, hM, hno⟩

/-- The obstruction criterion can be restricted to perfect-square graph orders. -/
theorem square_degree_criterion_iff :
    DegreeCriterion ↔
      ∀ K B : ℕ, ∃ s : ℕ, B < s ∧ ¬ DegreeObstruction (s ^ 2) (s - K) := by
  rw [sampled_degree_criterion_iff (S := Set.range fun s : ℕ => s ^ 2) (C := 2) (A := 0)]
  · constructor
    · intro h K B
      obtain ⟨N, hN, ⟨s, rfl⟩, hno⟩ := h K (B ^ 2)
      refine ⟨s, ?_, ?_⟩
      · by_contra! hs
        exact (not_le_of_gt hN) (Nat.pow_le_pow_left hs 2)
      · simpa only [Nat.sqrt_eq'] using hno
    · intro h K B
      obtain ⟨s, hs, hno⟩ := h K B
      refine ⟨s ^ 2, ?_, ⟨s, rfl⟩, ?_⟩
      · nlinarith
      · simpa only [Nat.sqrt_eq'] using hno
  · intro N _
    let s := Nat.sqrt N
    have hlow : s ^ 2 ≤ N := Nat.sqrt_le' N
    have hhigh : N < (s + 1) ^ 2 := Nat.lt_succ_sqrt' N
    exact ⟨(s + 1) ^ 2, ⟨s + 1, rfl⟩, hhigh.le, by nlinarith⟩

private theorem square_star_bound_iff {s K : ℕ} (hKs : K ≤ s) :
    fourStarRamsey (s ^ 2) + K ≤ s ^ 2 + s ↔
      ¬ DegreeObstruction (s ^ 2 + s - K) (Nat.sqrt (s ^ 2 + s - K) - K) := by
  have hsqrt : Nat.sqrt (s ^ 2 + s - K) = s := by
    apply le_antisymm
    · by_contra! h
      have hsq := Nat.le_sqrt'.mp (show s + 1 ≤ Nat.sqrt (s ^ 2 + s - K) by omega)
      have hle := Nat.sub_le (s ^ 2 + s) K
      nlinarith
    · exact Nat.le_sqrt'.mpr (by omega)
  have hgap : s ^ 2 + s - K - s ^ 2 = s - K := by omega
  rw [hsqrt, ← hgap, ← ramsey_le_iff_no_obstruction]
  omega

/-- It suffices to prove the Ramsey deficit along perfect-square star sizes. -/
theorem square_star_criterion_iff :
    DegreeCriterion ↔
      ∀ K B : ℕ, ∃ s : ℕ, B < s ∧ fourStarRamsey (s ^ 2) + K ≤ s ^ 2 + s := by
  constructor
  · intro h K B
    let S : Set ℕ := Set.range fun s : ℕ => s ^ 2 + s - K
    have hcover (N : ℕ) (hN : K ^ 2 ≤ N) :
        ∃ M ∈ S, N ≤ M ∧ M ≤ N + 3 * (Nat.sqrt N + 1) := by
      let s := Nat.sqrt N + 1
      have hKs : K ≤ s := (Nat.le_sqrt'.mpr hN).trans (Nat.le_succ _)
      have hhigh : N < s ^ 2 := Nat.lt_succ_sqrt' N
      have hlow : (Nat.sqrt N) ^ 2 ≤ N := Nat.sqrt_le' N
      refine ⟨s ^ 2 + s - K, ⟨s, rfl⟩, by omega, ?_⟩
      apply (Nat.sub_le _ _).trans
      dsimp [s]
      nlinarith
    obtain ⟨N, hN, ⟨s, rfl⟩, hno⟩ :=
      (sampled_degree_criterion_iff hcover).mp h K ((max K B) ^ 2 + max K B)
    change (max K B) ^ 2 + max K B < s ^ 2 + s - K at hN
    have hlarge : max K B < s := by
      by_contra! hs
      have hsq := Nat.pow_le_pow_left hs 2
      omega
    exact ⟨s, (le_max_right _ _).trans_lt hlarge,
      (square_star_bound_iff ((le_max_left _ _).trans hlarge.le)).mpr hno⟩
  · intro h K B
    obtain ⟨s, hs, hram⟩ := h K (max K B)
    have hKs : K ≤ s := (le_max_left _ _).trans hs.le
    have hB : B < s := (le_max_right _ _).trans_lt hs
    have hsquare : s ≤ s ^ 2 := by nlinarith
    exact ⟨s ^ 2 + s - K, by omega, (square_star_bound_iff hKs).mp hram⟩

end OMA.Erdos552Helpers

/-- The remaining Ramsey inequality is restricted to perfect-square star sizes. -/
theorem OMA.degree_criterion_core : OMA.Erdos552Helpers.DegreeCriterion := by
  apply OMA.Erdos552Helpers.square_star_criterion_iff.mpr
  sorry

theorem OMA.solution : type_of% @Erdos552.erdos_552.parts.ii := by
  exact OMA.Erdos552Helpers.degree_criterion_iff.mp OMA.degree_criterion_core
