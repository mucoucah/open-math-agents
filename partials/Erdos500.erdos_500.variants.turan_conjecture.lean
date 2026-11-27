import FormalConjectures.ErdosProblems.«500»

/-!
Partial proof of Erdős Problem 500 (Turán's tetrahedron conjecture):
proves Katona-Nemetz-Simonovits monotonicity of the Turán density, Turán's 3-partite
lower bound construction, and existence of the Turán density limit in [5/9, 22/35].
The matching upper bound is the remaining gap.
-/

-- Problem: Erdős Problem 500 — turan conjecture
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/500.lean:76 (declaration Erdos500.erdos_500.variants.turan_conjecture)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics Topology
open scoped Classical

/-- Generic reduction: a ratio limit gives asymptotic equivalence. -/
theorem OMA.isEquivalent_of_ratio (f : ℕ → ℝ)
    (h : Tendsto (fun n : ℕ => f n / (n.choose 3 : ℝ)) atTop (𝓝 (5 / 9))) :
    f ~[atTop] fun n => 5 / 9 * (n.choose 3 : ℝ) := by
  have hne : ∀ᶠ n : ℕ in atTop, (5 / 9 * (n.choose 3 : ℝ)) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have : (0 : ℝ) < n.choose 3 := by exact_mod_cast Nat.choose_pos hn
    positivity
  refine (isEquivalent_iff_tendsto_one hne).2 ?_
  have h2 : Tendsto (fun n : ℕ => f n / (n.choose 3 : ℝ) * (9 / 5)) atTop (𝓝 (5 / 9 * (9 / 5))) :=
    h.mul_const _
  rw [show (5 / 9 * (9 / 5) : ℝ) = 1 by norm_num] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have : (0 : ℝ) < n.choose 3 := by exact_mod_cast Nat.choose_pos hn
  simp only [Pi.div_apply]
  field_simp

/-- The finite Turan density ex_3(n, K_4^3) / choose(n, 3). -/
noncomputable def OMA.turanDensity (n : ℕ) : ℝ :=
  (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) / (n.choose 3 : ℝ)

private lemma OMA.two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add, ih]
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      ring

private lemma OMA.six_mul_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, mul_add, ih]
    have h2 : 6 * k.choose 2 = 3 * (k * (k - 1)) := by
      have := OMA.two_mul_choose_two k
      omega
    rw [h2]
    rcases k with _ | _ | m
    · simp
    · simp
    · rw [show m + 1 + 1 - 1 = m + 1 by omega, show m + 1 + 1 - 2 = m by omega,
          show m + 1 + 1 + 1 - 1 = m + 2 by omega, show m + 1 + 1 + 1 - 2 = m + 1 by omega]
      ring

private lemma OMA.choose_three_step (n : ℕ) (hn : 3 ≤ n) :
    (n - 2) * (n + 1).choose 3 = (n + 1) * n.choose 3 := by
  have h1 := OMA.six_mul_choose_three (n + 1)
  have h2 := OMA.six_mul_choose_three n
  have h3 : 6 * ((n - 2) * (n + 1).choose 3) = 6 * ((n + 1) * n.choose 3) := by
    calc 6 * ((n - 2) * (n + 1).choose 3)
        = (n - 2) * (6 * (n + 1).choose 3) := by ring
      _ = (n - 2) * ((n + 1) * n * (n - 1)) := by
          rw [h1]
          have : n + 1 - 1 = n := by omega
          have : n + 1 - 2 = n - 1 := by omega
          simp_all
      _ = (n + 1) * (n * (n - 1) * (n - 2)) := by ring
      _ = (n + 1) * (6 * n.choose 3) := by rw [h2]
      _ = 6 * ((n + 1) * n.choose 3) := by ring
  omega

/-- Any K_4^3-free 3-uniform hypergraph on Fin n has at most cliqueExtremalNumber n 3 4 edges. -/
theorem OMA.cliqueExtremalNumber_ge_card {n : ℕ} (H : Finset (Finset (Fin n)))
    (hunif : ∀ e ∈ H, e.card = 3) (hfree : ¬ H.ContainsCompleteHypergraph 3 4) :
    H.card ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply Finset.le_sup (f := Finset.card)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, hfree⟩
  intro e he
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ e, hunif e he⟩

/-- There exists an extremal K_4^3-free 3-uniform hypergraph on Fin n. -/
theorem OMA.exists_extremal_hypergraph (n : ℕ) :
    ∃ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) ∧
      ¬ H.ContainsCompleteHypergraph 3 4 ∧
      H.card = Hypergraph.cliqueExtremalNumber n 3 4 := by
  let F : Finset (Finset (Finset (Fin n))) :=
    ((Finset.univ : Finset (Fin n)).powersetCard 3).powerset.filter
      (fun H => ¬ H.ContainsCompleteHypergraph 3 4)
  have hempty : (∅ : Finset (Finset (Fin n))) ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_⟩
    rintro ⟨S, hScard, hSsub⟩
    have hcard : (S.powersetCard 3).card = 0 := by
      rw [Finset.subset_empty.mp hSsub]
      simp
    rw [Finset.card_powersetCard, hScard] at hcard
    norm_num at hcard
  obtain ⟨H, hHF, hHsup⟩ := Finset.exists_mem_eq_sup F ⟨∅, hempty⟩ Finset.card
  simp only [F, Finset.mem_filter, Finset.mem_powerset] at hHF
  refine ⟨H, ?_, hHF.2, ?_⟩
  · intro e he
    exact (Finset.mem_powersetCard.mp (hHF.1 he)).2
  · unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
    convert hHsup.symm

/-- Katona-Nemetz-Simonovits averaging step for K_4^3-free 3-graphs. -/
theorem OMA.cliqueExtremalNumber_step (n : ℕ) (hn : 3 ≤ n) :
    (n - 2) * Hypergraph.cliqueExtremalNumber (n + 1) 3 4 ≤
      (n + 1) * Hypergraph.cliqueExtremalNumber n 3 4 := by
  classical
  obtain ⟨H, hunif, hfree, hcard⟩ := OMA.exists_extremal_hypergraph (n + 1)
  have hbound : ∀ v : Fin (n + 1),
      (H.filter (fun e => v ∉ e)).card ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
    intro v
    let emb : Fin n ↪ Fin (n + 1) := ⟨v.succAbove, Fin.succAbove_right_injective⟩
    let Hv : Finset (Finset (Fin n)) :=
      ((Finset.univ : Finset (Fin n)).powersetCard 3).filter (fun e => e.map emb ∈ H)
    have hHv_unif : ∀ e ∈ Hv, e.card = 3 := by
      intro e he
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
    have hHv_free : ¬ Hv.ContainsCompleteHypergraph 3 4 := by
      rintro ⟨S, hScard, hSsub⟩
      apply hfree
      refine ⟨S.map emb, by simpa using hScard, ?_⟩
      intro e' he'
      rw [Finset.mem_powersetCard] at he'
      let e : Finset (Fin n) := S.filter (fun y => emb y ∈ e')
      have he_map : e.map emb = e' := by
        ext x
        simp only [Finset.mem_map, e, Finset.mem_filter]
        constructor
        · rintro ⟨y, ⟨_, hy⟩, rfl⟩
          exact hy
        · intro hx
          obtain ⟨y, hyS, rfl⟩ := Finset.mem_map.mp (he'.1 hx)
          exact ⟨y, ⟨hyS, hx⟩, rfl⟩
      have he_card : e.card = 3 := by
        have := congrArg Finset.card he_map
        simpa [he'.2] using this
      have he_in : e ∈ Hv := hSsub (Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, he_card⟩)
      rw [← he_map]
      exact (Finset.mem_filter.mp he_in).2
    have hcard_eq : (H.filter (fun e => v ∉ e)).card = Hv.card := by
      let mapEmb : Finset (Fin n) ↪ Finset (Fin (n + 1)) :=
        ⟨fun e => e.map emb, Finset.map_injective emb⟩
      have himg : Hv.map mapEmb = H.filter (fun e => v ∉ e) := by
        ext e'
        simp only [Finset.mem_map, mapEmb, Function.Embedding.coeFn_mk, Finset.mem_filter, Hv,
          Finset.mem_powersetCard]
        constructor
        · rintro ⟨e, ⟨⟨_, _⟩, heH⟩, rfl⟩
          refine ⟨heH, ?_⟩
          intro hv
          obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hv
          exact Fin.succAbove_ne v y hy
        · rintro ⟨he'H, hvnot⟩
          let e : Finset (Fin n) := Finset.univ.filter (fun y => emb y ∈ e')
          have he_map : e.map emb = e' := by
            ext x
            simp only [Finset.mem_map, e, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨y, hy, rfl⟩
              exact hy
            · intro hx
              have hne : x ≠ v := fun h => hvnot (h ▸ hx)
              obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq hne
              exact ⟨y, by simpa [emb, hy] using hx, hy⟩
          have he_card : e.card = 3 := by
            have := congrArg Finset.card he_map
            simpa [hunif e' he'H] using this
          exact ⟨e, ⟨⟨Finset.subset_univ _, he_card⟩, by simpa [he_map] using he'H⟩, he_map⟩
      rw [← himg, Finset.card_map]
    rw [hcard_eq]
    exact OMA.cliqueExtremalNumber_ge_card Hv hHv_unif hHv_free
  have hsum_le : ∑ v : Fin (n + 1), (H.filter (fun e => v ∉ e)).card ≤
      (n + 1) * Hypergraph.cliqueExtremalNumber n 3 4 := by
    calc ∑ v : Fin (n + 1), (H.filter (fun e => v ∉ e)).card
        ≤ ∑ _v : Fin (n + 1), Hypergraph.cliqueExtremalNumber n 3 4 :=
          Finset.sum_le_sum (fun v _ => hbound v)
      _ = (n + 1) * Hypergraph.cliqueExtremalNumber n 3 4 := by
          simp
  have hsum_eq : ∑ v : Fin (n + 1), (H.filter (fun e => v ∉ e)).card = (n - 2) * H.card := by
    calc ∑ v : Fin (n + 1), (H.filter (fun e => v ∉ e)).card
        = ∑ v : Fin (n + 1), ∑ e ∈ H, if v ∉ e then 1 else 0 := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.card_filter]
      _ = ∑ e ∈ H, ∑ v : Fin (n + 1), if v ∉ e then 1 else 0 := Finset.sum_comm
      _ = ∑ e ∈ H, (n - 2) := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          rw [← Finset.card_filter]
          have hcompl : (Finset.univ.filter (fun v : Fin (n + 1) => v ∉ e)) = eᶜ := by
            ext v
            simp
          rw [hcompl, Finset.card_compl, Fintype.card_fin, hunif e he]
          omega
      _ = H.card * (n - 2) := by simp
      _ = (n - 2) * H.card := Nat.mul_comm _ _
  rw [← hcard, ← hsum_eq]
  exact hsum_le

/-- The Turan density sequence is non-increasing from n = 3 onwards. -/
theorem OMA.turanDensity_succ_le (n : ℕ) (hn : 3 ≤ n) :
    OMA.turanDensity (n + 1) ≤ OMA.turanDensity n := by
  unfold OMA.turanDensity
  have hpos1 : (0 : ℝ) < (n.choose 3 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hpos2 : (0 : ℝ) < ((n + 1).choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ n + 1)
  rw [div_le_div_iff₀ hpos2 hpos1]
  have hstep : ((n - 2 : ℕ) : ℝ) * (Hypergraph.cliqueExtremalNumber (n + 1) 3 4 : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
    exact_mod_cast OMA.cliqueExtremalNumber_step n hn
  have hch : ((n - 2 : ℕ) : ℝ) * ((n + 1).choose 3 : ℝ) =
      ((n + 1 : ℕ) : ℝ) * (n.choose 3 : ℝ) := by
    exact_mod_cast OMA.choose_three_step n hn
  have hnp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hmul : ((n + 1 : ℕ) : ℝ) *
      ((Hypergraph.cliqueExtremalNumber (n + 1) 3 4 : ℝ) * (n.choose 3 : ℝ)) ≤
      ((n + 1 : ℕ) : ℝ) *
      ((Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) * ((n + 1).choose 3 : ℝ)) := by
    calc ((n + 1 : ℕ) : ℝ) *
          ((Hypergraph.cliqueExtremalNumber (n + 1) 3 4 : ℝ) * (n.choose 3 : ℝ))
        = (Hypergraph.cliqueExtremalNumber (n + 1) 3 4 : ℝ) *
          (((n + 1 : ℕ) : ℝ) * (n.choose 3 : ℝ)) := by ring
      _ = (Hypergraph.cliqueExtremalNumber (n + 1) 3 4 : ℝ) *
          (((n - 2 : ℕ) : ℝ) * ((n + 1).choose 3 : ℝ)) := by rw [hch]
      _ = (((n - 2 : ℕ) : ℝ) * (Hypergraph.cliqueExtremalNumber (n + 1) 3 4 : ℝ)) *
          ((n + 1).choose 3 : ℝ) := by ring
      _ ≤ (((n + 1 : ℕ) : ℝ) * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ)) *
          ((n + 1).choose 3 : ℝ) := by
            exact mul_le_mul_of_nonneg_right hstep (le_of_lt hpos2)
      _ = ((n + 1 : ℕ) : ℝ) *
          ((Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) * ((n + 1).choose 3 : ℝ)) := by ring
  exact le_of_mul_le_mul_left hmul hnp

/-- Monotonicity of Turan density for all 3 <= m <= n. -/
theorem OMA.turanDensity_antitone {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) :
    OMA.turanDensity n ≤ OMA.turanDensity m := by
  induction hmn with
  | refl => exact le_rfl
  | @step k hmk ih =>
    exact (OMA.turanDensity_succ_le k (le_trans hm hmk)).trans ih

/-- Number of vertices in S with residue r mod 3. -/
def OMA.colorCount {n : ℕ} (S : Finset (Fin n)) (r : ℕ) : ℕ :=
  (S.filter (fun v => v.val % 3 = r)).card

private lemma OMA.colorCount_sum {n : ℕ} (S : Finset (Fin n)) :
    OMA.colorCount S 0 + OMA.colorCount S 1 + OMA.colorCount S 2 = S.card := by
  unfold OMA.colorCount
  have hd01 : Disjoint (S.filter (fun v => v.val % 3 = 0)) (S.filter (fun v => v.val % 3 = 1)) := by
    rw [Finset.disjoint_filter]
    intro v _ h0 h1
    omega
  have hd012 : Disjoint (S.filter (fun v => v.val % 3 = 0) ∪ S.filter (fun v => v.val % 3 = 1))
      (S.filter (fun v => v.val % 3 = 2)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_union, Finset.mem_filter] at hv1 hv2
    omega
  rw [← Finset.card_union_of_disjoint hd01, ← Finset.card_union_of_disjoint hd012]
  congr 1
  ext v
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ((⟨hv, _⟩ | ⟨hv, _⟩) | ⟨hv, _⟩) <;> exact hv
  · intro hv
    have hmod : v.val % 3 = 0 ∨ v.val % 3 = 1 ∨ v.val % 3 = 2 := by omega
    rcases hmod with h | h | h
    · exact Or.inl (Or.inl ⟨hv, h⟩)
    · exact Or.inl (Or.inr ⟨hv, h⟩)
    · exact Or.inr ⟨hv, h⟩

private lemma OMA.colorCount_erase {n : ℕ} (S : Finset (Fin n)) (v : Fin n) (hv : v ∈ S) (r : ℕ) :
    OMA.colorCount (S.erase v) r =
      if v.val % 3 = r then OMA.colorCount S r - 1 else OMA.colorCount S r := by
  unfold OMA.colorCount
  by_cases hr : v.val % 3 = r
  · rw [if_pos hr]
    have heq : (S.erase v).filter (fun x => x.val % 3 = r) =
        (S.filter (fun x => x.val % 3 = r)).erase v := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [heq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hv, hr⟩)]
  · rw [if_neg hr]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hxS⟩, hxr⟩
      exact ⟨hxS, hxr⟩
    · rintro ⟨hxS, hxr⟩
      exact ⟨⟨fun h => hr (h ▸ hxr), hxS⟩, hxr⟩

/-- Predicate for edges of Turan's 3-partite construction. -/
def OMA.isTuranEdge {n : ℕ} (e : Finset (Fin n)) : Prop :=
  (OMA.colorCount e 0 = 1 ∧ OMA.colorCount e 1 = 1 ∧ OMA.colorCount e 2 = 1) ∨
  (OMA.colorCount e 0 = 2 ∧ OMA.colorCount e 1 = 1 ∧ OMA.colorCount e 2 = 0) ∨
  (OMA.colorCount e 0 = 0 ∧ OMA.colorCount e 1 = 2 ∧ OMA.colorCount e 2 = 1) ∨
  (OMA.colorCount e 0 = 1 ∧ OMA.colorCount e 1 = 0 ∧ OMA.colorCount e 2 = 2)

instance {n : ℕ} (e : Finset (Fin n)) : Decidable (OMA.isTuranEdge e) := by
  unfold OMA.isTuranEdge
  infer_instance

/-- Turan's balanced 3-partite K_4^3-free 3-uniform hypergraph on Fin n. -/
def OMA.turanGraph (n : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard 3).filter OMA.isTuranEdge

/-- Turan's construction contains no complete 3-graph on 4 vertices. -/
theorem OMA.turanGraph_no_K4 (n : ℕ) : ¬ (OMA.turanGraph n).ContainsCompleteHypergraph 3 4 := by
  rintro ⟨S, hScard, hSsub⟩
  have hsum : OMA.colorCount S 0 + OMA.colorCount S 1 + OMA.colorCount S 2 = 4 := by
    rw [OMA.colorCount_sum, hScard]
  have herase : ∀ v ∈ S, OMA.isTuranEdge (S.erase v) := by
    intro v hv
    have hmem : S.erase v ∈ S.powersetCard 3 := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.erase_subset v S, by rw [Finset.card_erase_of_mem hv, hScard]⟩
    exact (Finset.mem_filter.mp (hSsub hmem)).2
  have hstep : ∀ r : ℕ, 0 < OMA.colorCount S r →
      ∃ v ∈ S, v.val % 3 = r ∧ OMA.isTuranEdge (S.erase v) := by
    intro r hr
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hr
    rw [Finset.mem_filter] at hv
    exact ⟨v, hv.1, hv.2, herase v hv.1⟩
  have h0 : 0 < OMA.colorCount S 0 →
      (OMA.colorCount S 0 = 2 ∧ OMA.colorCount S 1 = 1 ∧ OMA.colorCount S 2 = 1) ∨
      (OMA.colorCount S 0 = 3 ∧ OMA.colorCount S 1 = 1 ∧ OMA.colorCount S 2 = 0) ∨
      (OMA.colorCount S 0 = 1 ∧ OMA.colorCount S 1 = 2 ∧ OMA.colorCount S 2 = 1) ∨
      (OMA.colorCount S 0 = 2 ∧ OMA.colorCount S 1 = 0 ∧ OMA.colorCount S 2 = 2) := by
    intro hr
    obtain ⟨v, hv, hvr, hedge⟩ := hstep 0 hr
    unfold OMA.isTuranEdge at hedge
    rw [OMA.colorCount_erase S v hv 0, OMA.colorCount_erase S v hv 1,
      OMA.colorCount_erase S v hv 2] at hedge
    simp only [hvr, ↓reduceIte, show (0 : ℕ) ≠ 1 by decide, show (0 : ℕ) ≠ 2 by decide] at hedge
    omega
  have h1 : 0 < OMA.colorCount S 1 →
      (OMA.colorCount S 0 = 1 ∧ OMA.colorCount S 1 = 2 ∧ OMA.colorCount S 2 = 1) ∨
      (OMA.colorCount S 0 = 2 ∧ OMA.colorCount S 1 = 2 ∧ OMA.colorCount S 2 = 0) ∨
      (OMA.colorCount S 0 = 0 ∧ OMA.colorCount S 1 = 3 ∧ OMA.colorCount S 2 = 1) ∨
      (OMA.colorCount S 0 = 1 ∧ OMA.colorCount S 1 = 1 ∧ OMA.colorCount S 2 = 2) := by
    intro hr
    obtain ⟨v, hv, hvr, hedge⟩ := hstep 1 hr
    unfold OMA.isTuranEdge at hedge
    rw [OMA.colorCount_erase S v hv 0, OMA.colorCount_erase S v hv 1,
      OMA.colorCount_erase S v hv 2] at hedge
    simp only [hvr, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) ≠ 2 by decide] at hedge
    omega
  have h2 : 0 < OMA.colorCount S 2 →
      (OMA.colorCount S 0 = 1 ∧ OMA.colorCount S 1 = 1 ∧ OMA.colorCount S 2 = 2) ∨
      (OMA.colorCount S 0 = 2 ∧ OMA.colorCount S 1 = 1 ∧ OMA.colorCount S 2 = 1) ∨
      (OMA.colorCount S 0 = 0 ∧ OMA.colorCount S 1 = 2 ∧ OMA.colorCount S 2 = 2) ∨
      (OMA.colorCount S 0 = 1 ∧ OMA.colorCount S 1 = 0 ∧ OMA.colorCount S 2 = 3) := by
    intro hr
    obtain ⟨v, hv, hvr, hedge⟩ := hstep 2 hr
    unfold OMA.isTuranEdge at hedge
    rw [OMA.colorCount_erase S v hv 0, OMA.colorCount_erase S v hv 1,
      OMA.colorCount_erase S v hv 2] at hedge
    simp only [hvr, ↓reduceIte, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide] at hedge
    omega
  omega

/-- Vertex class of residue r mod 3 in Fin n. -/
def OMA.colorClass (n r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val % 3 = r)

private lemma OMA.div_three_le_card_colorClass (n r : ℕ) (hr : r < 3) :
    n / 3 ≤ (OMA.colorClass n r).card := by
  let emb : Fin (n / 3) ↪ Fin n :=
    ⟨fun k => ⟨3 * k.val + r, by omega⟩, by
      intro a b h
      ext
      have := congrArg Fin.val h
      dsimp at this
      omega⟩
  have hsub : (Finset.univ : Finset (Fin (n / 3))).map emb ⊆ OMA.colorClass n r := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hx
    rw [OMA.colorClass, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by change (3 * k.val + r) % 3 = r; omega⟩
  have := Finset.card_le_card hsub
  simpa using this

private lemma OMA.card_turanGraph_ge (n : ℕ) :
    (n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3)) ≤ (OMA.turanGraph n).card := by
  classical
  let V0 := OMA.colorClass n 0
  let V1 := OMA.colorClass n 1
  let V2 := OMA.colorClass n 2
  let E_rain : Finset (Finset (Fin n)) :=
    (V0 ×ˢ (V1 ×ˢ V2)).image (fun t => {t.1, t.2.1, t.2.2})
  let E_01 : Finset (Finset (Fin n)) :=
    (V0.powersetCard 2 ×ˢ V1).image (fun t => insert t.2 t.1)
  let E_12 : Finset (Finset (Fin n)) :=
    (V1.powersetCard 2 ×ˢ V2).image (fun t => insert t.2 t.1)
  let E_20 : Finset (Finset (Fin n)) :=
    (V2.powersetCard 2 ×ˢ V0).image (fun t => insert t.2 t.1)
  have hfilter_triple : ∀ a ∈ V0, ∀ b ∈ V1, ∀ c ∈ V2,
      ({a, b, c} : Finset (Fin n)).filter (fun v => v.val % 3 = 0) = {a} ∧
      ({a, b, c} : Finset (Fin n)).filter (fun v => v.val % 3 = 1) = {b} ∧
      ({a, b, c} : Finset (Fin n)).filter (fun v => v.val % 3 = 2) = {c} := by
    intro a ha b hb c hc
    have ha0 : a.val % 3 = 0 := (Finset.mem_filter.mp ha).2
    have hb1 : b.val % 3 = 1 := (Finset.mem_filter.mp hb).2
    have hc2 : c.val % 3 = 2 := (Finset.mem_filter.mp hc).2
    refine ⟨?_, ?_, ?_⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hx⟩ <;> omega
      · rintro rfl; exact ⟨Or.inl rfl, ha0⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hx⟩ <;> omega
      · rintro rfl; exact ⟨Or.inr (Or.inl rfl), hb1⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hx⟩ <;> omega
      · rintro rfl; exact ⟨Or.inr (Or.inr rfl), hc2⟩
  have hfilter_pair : ∀ (r1 r2 : ℕ), r1 ≠ r2 → ∀ p ∈ (OMA.colorClass n r1).powersetCard 2,
      ∀ c ∈ OMA.colorClass n r2,
      (insert c p).filter (fun v => v.val % 3 = r1) = p ∧
      (insert c p).filter (fun v => v.val % 3 = r2) = {c} ∧
      (∀ r3, r3 ≠ r1 → r3 ≠ r2 → (insert c p).filter (fun v => v.val % 3 = r3) = ∅) ∧
      (insert c p).card = 3 := by
    intro r1 r2 hne p hp c hc
    rw [Finset.mem_powersetCard] at hp
    have hc_mod : c.val % 3 = r2 := (Finset.mem_filter.mp hc).2
    have hp_mod : ∀ x ∈ p, x.val % 3 = r1 := fun x hx => (Finset.mem_filter.mp (hp.1 hx)).2
    have hc_not : c ∉ p := fun h => hne ((hp_mod c h).symm.trans hc_mod)
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hxp, hx⟩
        · exact absurd (hc_mod.symm.trans hx) hne.symm
        · exact hxp
      · intro hxp
        exact ⟨Or.inr hxp, hp_mod x hxp⟩
    · ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | hxp, hx⟩
        · rfl
        · exact absurd ((hp_mod x hxp).symm.trans hx) hne
      · rintro rfl
        exact ⟨Or.inl rfl, hc_mod⟩
    · intro r3 h31 h32
      ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false]
      rintro ⟨rfl | hxp, hx⟩
      · exact h32 (hx.symm.trans hc_mod)
      · exact h31 (hx.symm.trans (hp_mod x hxp))
    · rw [Finset.card_insert_of_notMem hc_not, hp.2]
  have hrain_counts : ∀ e ∈ E_rain,
      OMA.colorCount e 0 = 1 ∧ OMA.colorCount e 1 = 1 ∧ OMA.colorCount e 2 = 1 ∧ e.card = 3 := by
    intro e he
    obtain ⟨⟨a, b, c⟩, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨f0, f1, f2⟩ := hfilter_triple a ht.1 b ht.2.1 c ht.2.2
    have c0 : OMA.colorCount {a, b, c} 0 = 1 := by unfold OMA.colorCount; rw [f0]; simp
    have c1 : OMA.colorCount {a, b, c} 1 = 1 := by unfold OMA.colorCount; rw [f1]; simp
    have c2 : OMA.colorCount {a, b, c} 2 = 1 := by unfold OMA.colorCount; rw [f2]; simp
    have hsum := OMA.colorCount_sum ({a, b, c} : Finset (Fin n))
    dsimp only
    exact ⟨c0, c1, c2, by omega⟩
  have h01_counts : ∀ e ∈ E_01,
      OMA.colorCount e 0 = 2 ∧ OMA.colorCount e 1 = 1 ∧ OMA.colorCount e 2 = 0 ∧ e.card = 3 := by
    intro e he
    obtain ⟨⟨p, c⟩, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product] at ht
    obtain ⟨f0, f1, f2, hcard⟩ := hfilter_pair 0 1 (by decide) p ht.1 c ht.2
    refine ⟨?_, ?_, ?_, hcard⟩
    · unfold OMA.colorCount; rw [f0]; exact (Finset.mem_powersetCard.mp ht.1).2
    · unfold OMA.colorCount; rw [f1]; simp
    · unfold OMA.colorCount; rw [f2 2 (by decide) (by decide)]; simp
  have h12_counts : ∀ e ∈ E_12,
      OMA.colorCount e 0 = 0 ∧ OMA.colorCount e 1 = 2 ∧ OMA.colorCount e 2 = 1 ∧ e.card = 3 := by
    intro e he
    obtain ⟨⟨p, c⟩, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product] at ht
    obtain ⟨f1, f2, f0, hcard⟩ := hfilter_pair 1 2 (by decide) p ht.1 c ht.2
    refine ⟨?_, ?_, ?_, hcard⟩
    · unfold OMA.colorCount; rw [f0 0 (by decide) (by decide)]; simp
    · unfold OMA.colorCount; rw [f1]; exact (Finset.mem_powersetCard.mp ht.1).2
    · unfold OMA.colorCount; rw [f2]; simp
  have h20_counts : ∀ e ∈ E_20,
      OMA.colorCount e 0 = 1 ∧ OMA.colorCount e 1 = 0 ∧ OMA.colorCount e 2 = 2 ∧ e.card = 3 := by
    intro e he
    obtain ⟨⟨p, c⟩, ht, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product] at ht
    obtain ⟨f2, f0, f1, hcard⟩ := hfilter_pair 2 0 (by decide) p ht.1 c ht.2
    refine ⟨?_, ?_, ?_, hcard⟩
    · unfold OMA.colorCount; rw [f0]; simp
    · unfold OMA.colorCount; rw [f1 1 (by decide) (by decide)]; simp
    · unfold OMA.colorCount; rw [f2]; exact (Finset.mem_powersetCard.mp ht.1).2
  have hcard_rain : E_rain.card = V0.card * (V1.card * V2.card) := by
    rw [Finset.card_image_of_injOn]
    · simp [Finset.card_product]
    · rintro ⟨a1, b1, c1⟩ h1 ⟨a2, b2, c2⟩ h2 heq
      dsimp only at heq
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product] at h1 h2
      obtain ⟨f10, f11, f12⟩ := hfilter_triple a1 h1.1 b1 h1.2.1 c1 h1.2.2
      obtain ⟨f20, f21, f22⟩ := hfilter_triple a2 h2.1 b2 h2.2.1 c2 h2.2.2
      have ha : ({a1} : Finset (Fin n)) = {a2} := by rw [← f10, heq, f20]
      have hb : ({b1} : Finset (Fin n)) = {b2} := by rw [← f11, heq, f21]
      have hc : ({c1} : Finset (Fin n)) = {c2} := by rw [← f12, heq, f22]
      simp only [Finset.singleton_inj] at ha hb hc
      simp [ha, hb, hc]
  have hcard_pair : ∀ (r1 r2 : ℕ), r1 ≠ r2 →
      (((OMA.colorClass n r1).powersetCard 2 ×ˢ OMA.colorClass n r2).image
        (fun t => insert t.2 t.1)).card =
      (OMA.colorClass n r1).card.choose 2 * (OMA.colorClass n r2).card := by
    intro r1 r2 hne
    rw [Finset.card_image_of_injOn]
    · simp [Finset.card_product, Finset.card_powersetCard]
    · rintro ⟨p1, c1⟩ h1 ⟨p2, c2⟩ h2 heq
      dsimp only at heq
      rw [Finset.mem_coe, Finset.mem_product] at h1 h2
      obtain ⟨fp1, fc1, _, _⟩ := hfilter_pair r1 r2 hne p1 h1.1 c1 h1.2
      obtain ⟨fp2, fc2, _, _⟩ := hfilter_pair r1 r2 hne p2 h2.1 c2 h2.2
      have hp : p1 = p2 := by rw [← fp1, heq, fp2]
      have hc : ({c1} : Finset (Fin n)) = {c2} := by rw [← fc1, heq, fc2]
      simp only [Finset.singleton_inj] at hc
      simp [hp, hc]
  have hcard_01 : E_01.card = V0.card.choose 2 * V1.card := hcard_pair 0 1 (by decide)
  have hcard_12 : E_12.card = V1.card.choose 2 * V2.card := hcard_pair 1 2 (by decide)
  have hcard_20 : E_20.card = V2.card.choose 2 * V0.card := hcard_pair 2 0 (by decide)
  have hd_r_01 : Disjoint E_rain E_01 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    have := hrain_counts e h1
    have := h01_counts e h2
    omega
  have hd_r01_12 : Disjoint (E_rain ∪ E_01) E_12 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    have := h12_counts e h2
    rcases Finset.mem_union.mp h1 with hr | h01
    · have := hrain_counts e hr; omega
    · have := h01_counts e h01; omega
  have hd_all_20 : Disjoint (E_rain ∪ E_01 ∪ E_12) E_20 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    have := h20_counts e h2
    rcases Finset.mem_union.mp h1 with h1' | h12
    · rcases Finset.mem_union.mp h1' with hr | h01
      · have := hrain_counts e hr; omega
      · have := h01_counts e h01; omega
    · have := h12_counts e h12; omega
  have hsub : E_rain ∪ E_01 ∪ E_12 ∪ E_20 ⊆ OMA.turanGraph n := by
    intro e he
    rw [OMA.turanGraph, Finset.mem_filter, Finset.mem_powersetCard]
    rcases Finset.mem_union.mp he with h1 | h20
    · rcases Finset.mem_union.mp h1 with h2 | h12
      · rcases Finset.mem_union.mp h2 with hr | h01
        · obtain ⟨c0, c1, c2, hc⟩ := hrain_counts e hr
          exact ⟨⟨Finset.subset_univ _, hc⟩, Or.inl ⟨c0, c1, c2⟩⟩
        · obtain ⟨c0, c1, c2, hc⟩ := h01_counts e h01
          exact ⟨⟨Finset.subset_univ _, hc⟩, Or.inr (Or.inl ⟨c0, c1, c2⟩)⟩
      · obtain ⟨c0, c1, c2, hc⟩ := h12_counts e h12
        exact ⟨⟨Finset.subset_univ _, hc⟩, Or.inr (Or.inr (Or.inl ⟨c0, c1, c2⟩))⟩
    · obtain ⟨c0, c1, c2, hc⟩ := h20_counts e h20
      exact ⟨⟨Finset.subset_univ _, hc⟩, Or.inr (Or.inr (Or.inr ⟨c0, c1, c2⟩))⟩
  have hle_total : E_rain.card + E_01.card + E_12.card + E_20.card ≤ (OMA.turanGraph n).card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd_all_20, Finset.card_union_of_disjoint hd_r01_12,
      Finset.card_union_of_disjoint hd_r_01] at this
    exact this
  have hV0 : n / 3 ≤ V0.card := OMA.div_three_le_card_colorClass n 0 (by decide)
  have hV1 : n / 3 ≤ V1.card := OMA.div_three_le_card_colorClass n 1 (by decide)
  have hV2 : n / 3 ≤ V2.card := OMA.div_three_le_card_colorClass n 2 (by decide)
  have hr_ge : (n / 3) ^ 3 ≤ E_rain.card := by
    rw [hcard_rain, pow_three]
    exact Nat.mul_le_mul hV0 (Nat.mul_le_mul hV1 hV2)
  have h01_ge : (n / 3).choose 2 * (n / 3) ≤ E_01.card := by
    rw [hcard_01]
    exact Nat.mul_le_mul (Nat.choose_le_choose 2 hV0) hV1
  have h12_ge : (n / 3).choose 2 * (n / 3) ≤ E_12.card := by
    rw [hcard_12]
    exact Nat.mul_le_mul (Nat.choose_le_choose 2 hV1) hV2
  have h20_ge : (n / 3).choose 2 * (n / 3) ≤ E_20.card := by
    rw [hcard_20]
    exact Nat.mul_le_mul (Nat.choose_le_choose 2 hV2) hV0
  omega

/-- Explicit Turan lower bound: cliqueExtremalNumber n 3 4 >= q^3 + 3 * choose(q, 2) * q. -/
theorem OMA.turan_extremal_lower_nat (n : ℕ) :
    (n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3)) ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  have hunif : ∀ e ∈ OMA.turanGraph n, e.card = 3 := fun e he =>
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
  exact (OMA.card_turanGraph_ge n).trans
    (OMA.cliqueExtremalNumber_ge_card (OMA.turanGraph n) hunif (OMA.turanGraph_no_K4 n))

/-- Explicit density lower bound 5/9 - 5/n <= turanDensity n for all n >= 3. -/
theorem OMA.five_ninths_sub_le_turanDensity (n : ℕ) (hn : 3 ≤ n) :
    5 / 9 - 5 / (n : ℝ) ≤ OMA.turanDensity n := by
  unfold OMA.turanDensity
  have hCpos : (0 : ℝ) < (n.choose 3 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  by_cases h9 : n < 9
  · have hnonpos : 5 / 9 - 5 / (n : ℝ) ≤ 0 := by
      rw [sub_nonpos, div_le_div_iff₀ (by norm_num) hn_pos]
      have hn_le : (n : ℝ) ≤ 9 := by exact_mod_cast (by omega : n ≤ 9)
      linarith
    exact hnonpos.trans (div_nonneg (Nat.cast_nonneg _) (le_of_lt hCpos))
  · push Not at h9
    have hnat : 2 * ((n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3))) ≤
        2 * Hypergraph.cliqueExtremalNumber n 3 4 :=
      Nat.mul_le_mul_left 2 (OMA.turan_extremal_lower_nat n)
    have h2ch : 2 * (n / 3).choose 2 = (n / 3) * (n / 3 - 1) := OMA.two_mul_choose_two (n / 3)
    have hq_pos : 1 ≤ n / 3 := by omega
    have hq_real : (5 : ℝ) * ((n / 3 : ℕ) : ℝ) ^ 3 - 3 * ((n / 3 : ℕ) : ℝ) ^ 2 ≤
        2 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
      have hnat2 : 2 * (n / 3) ^ 3 + 3 * ((n / 3) * (n / 3 - 1) * (n / 3)) ≤
          2 * Hypergraph.cliqueExtremalNumber n 3 4 := by
        calc 2 * (n / 3) ^ 3 + 3 * ((n / 3) * (n / 3 - 1) * (n / 3))
            = 2 * (n / 3) ^ 3 + 3 * (2 * (n / 3).choose 2 * (n / 3)) := by rw [h2ch]
          _ = 2 * ((n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3))) := by ring
          _ ≤ 2 * Hypergraph.cliqueExtremalNumber n 3 4 := hnat
      have hcast : (2 : ℝ) * ((n / 3 : ℕ) : ℝ) ^ 3 +
          3 * (((n / 3 : ℕ) : ℝ) * ((n / 3 - 1 : ℕ) : ℝ) * ((n / 3 : ℕ) : ℝ)) ≤
          2 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
        exact_mod_cast hnat2
      have hsub : ((n / 3 - 1 : ℕ) : ℝ) = ((n / 3 : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub hq_pos, Nat.cast_one]
      rw [hsub] at hcast
      linarith
    have hq_lo : (n : ℝ) - 2 ≤ 3 * ((n / 3 : ℕ) : ℝ) := by
      have : n ≤ 3 * (n / 3) + 2 := by omega
      have : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast this
      linarith
    have hq_hi : 3 * ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : 3 * (n / 3) ≤ n := by omega
      exact_mod_cast this
    have hq_nonneg : (0 : ℝ) ≤ ((n / 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn_ge9 : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h9
    have hcube : ((n : ℝ) - 2) ^ 3 ≤ (3 * ((n / 3 : ℕ) : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hq_lo 3
    have hsq : (3 * ((n / 3 : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
      nlinarith
    have hex_ge : 5 / 9 * (n : ℝ) ^ 3 - 5 * (n : ℝ) ^ 2 ≤
        6 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
      nlinarith
    have hchoose_le : 6 * (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have h6 := OMA.six_mul_choose_three n
      have hle_nat : 6 * n.choose 3 ≤ n ^ 3 := by
        rw [h6, pow_three, ← mul_assoc]
        exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.sub_le n 1)) (Nat.sub_le n 2)
      exact_mod_cast hle_nat
    have hcoeff_nonneg : 0 ≤ 5 / 9 - 5 / (n : ℝ) := by
      rw [sub_nonneg, div_le_div_iff₀ hn_pos (by norm_num)]
      linarith
    rw [le_div_iff₀ hCpos]
    have hmul6 : (5 / 9 - 5 / (n : ℝ)) * (6 * (n.choose 3 : ℝ)) ≤
        6 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
      calc (5 / 9 - 5 / (n : ℝ)) * (6 * (n.choose 3 : ℝ))
          ≤ (5 / 9 - 5 / (n : ℝ)) * (n : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_left hchoose_le hcoeff_nonneg
        _ = 5 / 9 * (n : ℝ) ^ 3 - 5 * (n : ℝ) ^ 2 := by field_simp
        _ ≤ 6 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := hex_ge
    linarith

/-- Combining KNS monotonicity and Turan's construction: turanDensity n >= 5/9 for every n >= 3. -/
theorem OMA.five_ninths_le_turanDensity (n : ℕ) (hn : 3 ≤ n) :
    5 / 9 ≤ OMA.turanDensity n := by
  by_contra hlt
  push Not at hlt
  set δ : ℝ := 5 / 9 - OMA.turanDensity n with hδ_def
  have hδ : 0 < δ := by linarith
  let N : ℕ := max n (Nat.ceil (5 / δ) + 1)
  have hN_ge_n : n ≤ N := le_max_left _ _
  have hN_ge_3 : 3 ≤ N := le_trans hn hN_ge_n
  have hN_gt : 5 / δ < (N : ℝ) := by
    have h1 : 5 / δ ≤ (Nat.ceil (5 / δ) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (5 / δ) + 1 : ℕ) ≤ N := le_max_right _ _
    have h3 : ((Nat.ceil (5 / δ) : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h5N : 5 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hN_pos]
    have := (div_lt_iff₀ hδ).mp hN_gt
    linarith
  have hlo : 5 / 9 - 5 / (N : ℝ) ≤ OMA.turanDensity N :=
    OMA.five_ninths_sub_le_turanDensity N hN_ge_3
  have hanti : OMA.turanDensity N ≤ OMA.turanDensity n :=
    OMA.turanDensity_antitone hn hN_ge_n
  linarith

/-- Double-counting on 5 vertices shows ex_3(5, K_4^3) <= 7. -/
theorem OMA.cliqueExtremalNumber_five_le : Hypergraph.cliqueExtremalNumber 5 3 4 ≤ 7 := by
  obtain ⟨H, hunif, hfree, hcard⟩ := OMA.exists_extremal_hypergraph 5
  let U3 : Finset (Finset (Fin 5)) := (Finset.univ : Finset (Fin 5)).powersetCard 3
  let U4 : Finset (Finset (Fin 5)) := (Finset.univ : Finset (Fin 5)).powersetCard 4
  have hHsub : H ⊆ U3 := by
    intro e he
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hunif e he⟩
  let M : Finset (Finset (Fin 5)) := U3 \ H
  have hHM : H.card + M.card = 10 := by
    have h1 : M.card + H.card = U3.card := Finset.card_sdiff_add_card_eq_card hHsub
    have h2 : U3.card = 10 := by
      simpa [U3, Finset.card_powersetCard] using (show (5 : ℕ).choose 3 = 10 by decide)
    omega
  have hhit : ∀ S ∈ U4, 1 ≤ (M.filter (fun e => e ⊆ S)).card := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hnot : ¬ S.powersetCard 3 ⊆ H := fun h => hfree ⟨S, hS.2, h⟩
    rw [Finset.not_subset] at hnot
    obtain ⟨e, heS, heH⟩ := hnot
    rw [Finset.mem_powersetCard] at heS
    refine Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨?_, heS.1⟩⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, heS.2⟩, heH⟩
  have hdeg : ∀ e ∈ M, (U4.filter (fun S => e ⊆ S)).card ≤ 2 := by
    intro e he
    have he3 : e.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1).2
    have hsub : U4.filter (fun S => e ⊆ S) ⊆ eᶜ.image (fun v => insert v e) := by
      intro S hS
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
      have hne : (S \ e).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hSeq : S = e := Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hemp) hS.2
        have := congrArg Finset.card hSeq
        omega
      obtain ⟨v, hv⟩ := hne
      rw [Finset.mem_sdiff] at hv
      refine Finset.mem_image.mpr ⟨v, Finset.mem_compl.mpr hv.2, ?_⟩
      have hsub1 : insert v e ⊆ S := Finset.insert_subset hv.1 hS.2
      have hcard1 : (insert v e).card = S.card := by
        rw [Finset.card_insert_of_notMem hv.2, he3, hS.1.2]
      exact Finset.eq_of_subset_of_card_le hsub1 (le_of_eq hcard1.symm)
    calc (U4.filter (fun S => e ⊆ S)).card
        ≤ (eᶜ.image (fun v => insert v e)).card := Finset.card_le_card hsub
      _ ≤ eᶜ.card := Finset.card_image_le
      _ = 2 := by rw [Finset.card_compl, Fintype.card_fin, he3]
  have hsum_lo : 5 ≤ ∑ S ∈ U4, (M.filter (fun e => e ⊆ S)).card := by
    calc 5 = U4.card := by simp [U4, Finset.card_powersetCard]
      _ = ∑ _S ∈ U4, 1 := by simp
      _ ≤ ∑ S ∈ U4, (M.filter (fun e => e ⊆ S)).card :=
          Finset.sum_le_sum (fun S hS => hhit S hS)
  have hsum_eq : ∑ S ∈ U4, (M.filter (fun e => e ⊆ S)).card =
      ∑ e ∈ M, (U4.filter (fun S => e ⊆ S)).card := by
    calc ∑ S ∈ U4, (M.filter (fun e => e ⊆ S)).card
        = ∑ S ∈ U4, ∑ e ∈ M, if e ⊆ S then 1 else 0 := by
          refine Finset.sum_congr rfl (fun S _ => Finset.card_filter _ _)
      _ = ∑ e ∈ M, ∑ S ∈ U4, if e ⊆ S then 1 else 0 := Finset.sum_comm
      _ = ∑ e ∈ M, (U4.filter (fun S => e ⊆ S)).card := by
          refine Finset.sum_congr rfl (fun e _ => (Finset.card_filter _ _).symm)
  have hsum_hi : ∑ e ∈ M, (U4.filter (fun S => e ⊆ S)).card ≤ 2 * M.card := by
    calc ∑ e ∈ M, (U4.filter (fun S => e ⊆ S)).card
        ≤ ∑ _e ∈ M, 2 := Finset.sum_le_sum (fun e he => hdeg e he)
      _ = 2 * M.card := by simp [mul_comm]
  omega

/-- By KNS monotonicity and ex_3(5, K_4^3) <= 7, turanDensity n <= 7/10 for all n >= 5. -/
theorem OMA.turanDensity_le_seven_tenths (n : ℕ) (hn : 5 ≤ n) :
    OMA.turanDensity n ≤ 7 / 10 := by
  have h5 : OMA.turanDensity 5 ≤ 7 / 10 := by
    unfold OMA.turanDensity
    have hex : (Hypergraph.cliqueExtremalNumber 5 3 4 : ℝ) ≤ 7 := by
      exact_mod_cast OMA.cliqueExtremalNumber_five_le
    have hch : ((5 : ℕ).choose 3 : ℝ) = 10 := by
      rw [show (5 : ℕ).choose 3 = 10 by decide, Nat.cast_ofNat]
    rw [hch]
    linarith
  exact (OMA.turanDensity_antitone (by omega) hn).trans h5

private def OMA.CoversFourSets {α : Type*} [DecidableEq α]
    (U : Finset α) (M : Finset (Finset α)) : Prop :=
  (∀ e ∈ M, e ⊆ U ∧ e.card = 3) ∧
    ∀ S ∈ U.powersetCard 4, ∃ e ∈ M, e ⊆ S

private def OMA.avoidVertex {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) (v : α) : Finset (Finset α) :=
  M.filter (fun e => v ∉ e)

private theorem OMA.coversFourSets_erase {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (v : α) :
    OMA.CoversFourSets (U.erase v) (OMA.avoidVertex M v) := by
  constructor
  · intro e he
    have ⟨heM, hev⟩ := Finset.mem_filter.mp he
    have ⟨heU, he3⟩ := h.1 e heM
    exact ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => hev (h ▸ hx), heU hx⟩, he3⟩
  · intro S hS
    have ⟨hSU, hS4⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨e, heM, heS⟩ := h.2 S
      (Finset.mem_powersetCard.mpr ⟨hSU.trans (Finset.erase_subset _ _), hS4⟩)
    exact ⟨e, Finset.mem_filter.mpr ⟨heM, fun hv => Finset.notMem_erase v U (hSU (heS hv))⟩, heS⟩

private theorem OMA.sum_card_avoidVertex {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : ∀ e ∈ M, e ⊆ U ∧ e.card = 3) :
    ∑ v ∈ U, (OMA.avoidVertex M v).card = M.card * (U.card - 3) := by
  calc
    ∑ v ∈ U, (OMA.avoidVertex M v).card =
        ∑ v ∈ U, ∑ e ∈ M, if v ∉ e then 1 else 0 := by
      simp only [OMA.avoidVertex, Finset.card_filter]
    _ = ∑ e ∈ M, ∑ v ∈ U, if v ∉ e then 1 else 0 := Finset.sum_comm
    _ = ∑ _e ∈ M, (U.card - 3) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.card_filter]
      have heq : U.filter (fun v => v ∉ e) = U \ e := by ext v; simp
      rw [heq, Finset.card_sdiff_of_subset (h e he).1, (h e he).2]
    _ = _ := by simp

private theorem OMA.card_cover_five {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (hU : U.card = 5) :
    3 ≤ M.card := by
  have hlocal : ∀ v ∈ U, 1 ≤ (OMA.avoidVertex M v).card := by
    intro v hv
    have h4 : (U.erase v).card = 4 := by rw [Finset.card_erase_of_mem hv, hU]
    obtain ⟨e, he, _⟩ := (OMA.coversFourSets_erase h v).2 (U.erase v)
      (Finset.mem_powersetCard.mpr ⟨Finset.Subset.rfl, h4⟩)
    exact Finset.card_pos.mpr ⟨e, he⟩
  have hs := OMA.sum_card_avoidVertex h.1
  rw [hU] at hs
  have hl : ∑ v ∈ U, (1 : ℕ) ≤ ∑ v ∈ U, (OMA.avoidVertex M v).card :=
    Finset.sum_le_sum hlocal
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hU] at hl
  omega

private theorem OMA.card_cover_six {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (hU : U.card = 6) :
    6 ≤ M.card ∧ (M.card = 6 → ∀ v ∈ U, (OMA.avoidVertex M v).card = 3) := by
  have hlocal : ∀ v ∈ U, 3 ≤ (OMA.avoidVertex M v).card := by
    intro v hv
    apply OMA.card_cover_five (OMA.coversFourSets_erase h v)
    rw [Finset.card_erase_of_mem hv, hU]
  have hs := OMA.sum_card_avoidVertex h.1
  rw [hU] at hs
  have hl : ∑ v ∈ U, (3 : ℕ) ≤ ∑ v ∈ U, (OMA.avoidVertex M v).card :=
    Finset.sum_le_sum hlocal
  simp only [Finset.sum_const, nsmul_eq_mul, hU] at hl
  refine ⟨by omega, ?_⟩
  intro hM v hv
  have hr : ∑ w ∈ U.erase v, (3 : ℕ) ≤ ∑ w ∈ U.erase v, (OMA.avoidVertex M w).card :=
    Finset.sum_le_sum (fun w hw => hlocal w (Finset.mem_of_mem_erase hw))
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hv, hU] at hr
  rw [← Finset.sum_erase_add _ _ hv] at hs
  have := hlocal v hv
  omega

private def OMA.vertexDegree {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) (v : α) : ℕ :=
  (M.filter (fun e => v ∈ e)).card

private def OMA.throughPair {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) (v w : α) : Finset (Finset α) :=
  M.filter (fun e => v ∈ e ∧ w ∈ e)

private theorem OMA.vertexDegree_add_avoid {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) (v : α) :
    OMA.vertexDegree M v + (OMA.avoidVertex M v).card = M.card :=
  Finset.card_filter_add_card_filter_not (fun e => v ∈ e)

private theorem OMA.vertexDegree_erase_add {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) (v w : α) :
    (OMA.throughPair M v w).card + OMA.vertexDegree (OMA.avoidVertex M w) v =
      OMA.vertexDegree M v := by
  simpa only [OMA.throughPair, OMA.vertexDegree, OMA.avoidVertex, Finset.filter_filter, and_comm]
    using (Finset.card_filter_add_card_filter_not (s := M.filter (fun e => v ∈ e)) (fun e => w ∈ e))

private theorem OMA.pair_card_cover_six {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M)
    (hU : U.card = 6) (hM : M.card = 6) {v w : α} (hv : v ∈ U) (hw : w ∈ U)
    (hne : v ≠ w) : (OMA.throughPair M v w).card ≤ 2 := by
  have hav := (OMA.card_cover_six h hU).2 hM
  have hvw := OMA.vertexDegree_erase_add M v w
  have hvdeg := OMA.vertexDegree_add_avoid M v
  rw [hav v hv, hM] at hvdeg
  by_contra! hlarge
  have hzero : OMA.vertexDegree (OMA.avoidVertex M w) v = 0 := by omega
  have hnone : ∀ e ∈ OMA.avoidVertex M w, v ∉ e := by
    intro e he hv'
    have hpos : 0 < OMA.vertexDegree (OMA.avoidVertex M w) v :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hv'⟩⟩
    omega
  let W := (U.erase w).erase v
  have hW : W.card = 4 := by
    dsimp [W]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, hv⟩),
      Finset.card_erase_of_mem hw, hU]
  have hsub : W.powersetCard 3 ⊆ OMA.avoidVertex M w := by
    intro e he
    obtain ⟨heW, he3⟩ := Finset.mem_powersetCard.mp he
    have hev : v ∉ e := fun hv' => Finset.notMem_erase _ _ (heW hv')
    have hin : insert v e ∈ (U.erase w).powersetCard 4 :=
      Finset.mem_powersetCard.mpr
        ⟨Finset.insert_subset (Finset.mem_erase.mpr ⟨hne, hv⟩)
            (heW.trans (Finset.erase_subset _ _)), by rw [Finset.card_insert_of_notMem hev, he3]⟩
    obtain ⟨f, hf, hfe⟩ := (OMA.coversFourSets_erase h w).2 _ hin
    have hfv := hnone f hf
    have hsub : f ⊆ e := by
      intro x hx
      rcases Finset.mem_insert.mp (hfe hx) with rfl | hxe
      · exact (hfv hx).elim
      · exact hxe
    have hfeq : f = e := Finset.eq_of_subset_of_card_le hsub
      (by rw [((OMA.coversFourSets_erase h w).1 f hf).2, he3])
    exact hfeq ▸ hf
  have hle := Finset.card_le_card hsub
  rw [Finset.card_powersetCard, hW, hav w hw] at hle
  exact (by decide : ¬ (4 : ℕ).choose 3 ≤ 3) hle

private theorem OMA.sum_card_throughPair {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (v : α) :
    ∑ w ∈ U.erase v, (OMA.throughPair M v w).card = 2 * OMA.vertexDegree M v := by
  let D := M.filter (fun e => v ∈ e)
  have hpair (w : α) : OMA.throughPair M v w = D.filter (fun e => w ∈ e) := by
    ext e
    simp [D, OMA.throughPair, and_assoc]
  calc
    ∑ w ∈ U.erase v, (OMA.throughPair M v w).card =
        ∑ w ∈ U.erase v, ∑ e ∈ D, if w ∈ e then 1 else 0 := by
      simp only [hpair, Finset.card_filter]
    _ = ∑ e ∈ D, ∑ w ∈ U.erase v, if w ∈ e then 1 else 0 := Finset.sum_comm
    _ = ∑ _e ∈ D, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨heM, hv⟩ := Finset.mem_filter.mp he
      obtain ⟨heU, he3⟩ := h.1 e heM
      rw [← Finset.card_filter]
      have hfilter : (U.erase v).filter (fun w => w ∈ e) = e.erase v := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, heU h.2⟩, h.2⟩⟩
      rw [hfilter, Finset.card_erase_of_mem hv, he3]
    _ = _ := by simp [D, OMA.vertexDegree, mul_comm]

private theorem OMA.card_cover_seven {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (hU : U.card = 7) :
    12 ≤ M.card := by
  let a := fun v => (OMA.avoidVertex M v).card
  have hlocal (v : α) (hv : v ∈ U) : 6 ≤ a v :=
    (OMA.card_cover_six (OMA.coversFourSets_erase h v)
      (by rw [Finset.card_erase_of_mem hv, hU])).1
  have hs : ∑ v ∈ U, a v = M.card * 4 := by
    simpa [a, hU] using OMA.sum_card_avoidVertex h.1
  have hl : ∑ v ∈ U, (6 : ℕ) ≤ ∑ v ∈ U, a v := Finset.sum_le_sum hlocal
  simp only [Finset.sum_const, nsmul_eq_mul, hU] at hl
  by_contra! hsmall
  have hM : M.card = 11 := by omega
  let L := U.filter (fun v => 6 < a v)
  let G := U \ L
  have hLU : L ⊆ U := Finset.filter_subset _ _
  have hGU : G ⊆ U := Finset.sdiff_subset
  have hlow (v : α) (hv : v ∈ L) : 6 < a v := (Finset.mem_filter.mp hv).2
  have hhigh (v : α) (hv : v ∈ G) : a v = 6 := by
    have hv' := Finset.mem_sdiff.mp hv
    have hlt : ¬ 6 < a v := fun hp => hv'.2 (Finset.mem_filter.mpr ⟨hv'.1, hp⟩)
    exact le_antisymm (Nat.le_of_not_gt hlt) (hlocal v hv'.1)
  have hexcess : ∑ v ∈ L, (a v - 6) = 2 := by
    have hsplit : ∑ v ∈ U, a v = (∑ v ∈ U, (a v - 6)) + ∑ v ∈ U, 6 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v hv => (Nat.sub_add_cancel (hlocal v hv)).symm)
    simp only [Finset.sum_const, nsmul_eq_mul, hU] at hsplit
    have heq : ∑ v ∈ L, (a v - 6) = ∑ v ∈ U, (a v - 6) := by
      apply Finset.sum_subset hLU
      intro v hvU hv
      exact Nat.sub_eq_zero_of_le (Nat.le_of_not_gt
        (fun hp => hv (Finset.mem_filter.mpr ⟨hvU, hp⟩)))
    rw [heq]
    omega
  have hLle : L.card ≤ 2 := by
    have h := Finset.sum_le_sum (fun v hv => Nat.succ_le_of_lt (Nat.sub_pos_of_lt (hlow v hv)))
    change (∑ v ∈ L, (1 : ℕ)) ≤ ∑ v ∈ L, (a v - 6) at h
    simpa [hexcess] using h
  have hLpos : 0 < L.card := by
    apply Finset.card_pos.mpr
    by_contra! he
    rw [he, Finset.sum_empty] at hexcess
    omega
  have hpair (v z : α) (hz : z ∈ G) (hv : v ∈ U) (hne : v ≠ z) :
      (OMA.throughPair M v z).card + 3 = OMA.vertexDegree M v := by
    have hU6 : (U.erase z).card = 6 := by rw [Finset.card_erase_of_mem (hGU hz), hU]
    have havo := (OMA.card_cover_six (OMA.coversFourSets_erase h z) hU6).2
      (hhigh z hz) v (Finset.mem_erase.mpr ⟨hne, hv⟩)
    have hd := OMA.vertexDegree_add_avoid (OMA.avoidVertex M z) v
    rw [havo] at hd
    change OMA.vertexDegree (OMA.avoidVertex M z) v + 3 = a z at hd
    rw [hhigh z hz] at hd
    have hd3 : OMA.vertexDegree (OMA.avoidVertex M z) v = 3 := by omega
    rw [← hd3]
    exact OMA.vertexDegree_erase_add M v z
  rcases (show L.card = 1 ∨ L.card = 2 by omega) with hL | hL
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hL
    have hxL : x ∈ L := by simp [hx]
    have hxv := OMA.vertexDegree_add_avoid M x
    simp only [hx, Finset.sum_singleton] at hexcess
    have hd3 : OMA.vertexDegree M x = 3 := by change OMA.vertexDegree M x + a x = M.card at hxv; omega
    have hz (z : α) (hz : z ∈ U.erase x) : (OMA.throughPair M x z).card = 0 := by
      obtain ⟨hne, hzU⟩ := Finset.mem_erase.mp hz
      have hzG : z ∈ G := by simp [G, hx, hzU, hne]
      have hc := hpair x z hzG (hLU hxL) hne.symm
      omega
    have hh := OMA.sum_card_throughPair h x
    rw [Finset.sum_eq_zero hz, hd3] at hh
    omega
  · obtain ⟨x, y, hxy, hLxy⟩ := Finset.card_eq_two.mp hL
    have hxL : x ∈ L := by simp [hLxy]
    have hyL : y ∈ L := by simp [hLxy]
    have hyG : y ∉ G := fun hy => (Finset.mem_sdiff.mp hy).2 hyL
    have hain : a x - 6 + (a y - 6) = 2 := by
      simpa [hLxy, Finset.sum_insert, hxy] using hexcess
    have hxlt := hlow x hxL
    have hylt := hlow y hyL
    have hxv := OMA.vertexDegree_add_avoid M x
    change OMA.vertexDegree M x + a x = M.card at hxv
    have hd4 : OMA.vertexDegree M x = 4 := by omega
    have hG5 : G.card = 5 := by
      change (U \ L).card = 5
      rw [Finset.card_sdiff_of_subset hLU, hU, hL]
    have hone (z : α) (hz : z ∈ G) : (OMA.throughPair M x z).card = 1 := by
      have hne : x ≠ z := fun he => (Finset.mem_sdiff.mp hz).2 (he ▸ hxL)
      have hc := hpair x z hz (hLU hxL) hne
      omega
    have hsplit : insert y G = U.erase x := by
      ext z
      simp only [G, hLxy, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_erase]
      have hyU := hLU hyL
      grind
    have hsum := OMA.sum_card_throughPair h x
    rw [← hsplit, Finset.sum_insert hyG, hd4] at hsum
    simp only [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one, hG5] at hsum
    have hthree : (OMA.throughPair M x y).card = 3 := by omega
    have hsumavoid := OMA.sum_card_avoidVertex
      (M := OMA.throughPair M x y)
      (fun e he => h.1 e (Finset.mem_filter.mp he).1)
    rw [hthree, hU] at hsumavoid
    have hrestrict :
        ∑ z ∈ G, (OMA.avoidVertex (OMA.throughPair M x y) z).card =
          ∑ z ∈ U, (OMA.avoidVertex (OMA.throughPair M x y) z).card := by
      apply Finset.sum_subset hGU
      intro z hz hzG
      have hzL : z ∈ L := by
        by_contra hnot
        exact hzG (Finset.mem_sdiff.mpr ⟨hz, hnot⟩)
      have hzero : OMA.avoidVertex (OMA.throughPair M x y) z = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        have ⟨hep, hze⟩ := Finset.mem_filter.mp he
        have hep' := (Finset.mem_filter.mp hep).2
        rw [hLxy, Finset.mem_insert, Finset.mem_singleton] at hzL
        rcases hzL with rfl | rfl
        · exact hze hep'.1
        · exact hze hep'.2
      rw [hzero, Finset.card_empty]
    have hbound : ∑ z ∈ G, (OMA.avoidVertex (OMA.throughPair M x y) z).card ≤ ∑ z ∈ G, 2 := by
      apply Finset.sum_le_sum
      intro z hz
      have hzx : x ≠ z := fun he => (Finset.mem_sdiff.mp hz).2 (he ▸ hxL)
      have hzy : y ≠ z := fun he => (Finset.mem_sdiff.mp hz).2 (he ▸ hyL)
      have hU6 : (U.erase z).card = 6 := by rw [Finset.card_erase_of_mem (hGU hz), hU]
      have hp := OMA.pair_card_cover_six (OMA.coversFourSets_erase h z) hU6 (hhigh z hz)
        (Finset.mem_erase.mpr ⟨hzx, hLU hxL⟩) (Finset.mem_erase.mpr ⟨hzy, hLU hyL⟩) hxy
      simpa only [OMA.avoidVertex, OMA.throughPair, Finset.filter_filter, and_comm] using hp
    rw [hrestrict] at hbound
    simp only [Finset.sum_const, nsmul_eq_mul, hG5] at hbound
    omega

private theorem OMA.exists_extremal_cover (n : ℕ) :
    ∃ M : Finset (Finset (Fin n)), OMA.CoversFourSets Finset.univ M ∧
      M.card + Hypergraph.cliqueExtremalNumber n 3 4 = n.choose 3 := by
  obtain ⟨H, hunif, hfree, hcard⟩ := OMA.exists_extremal_hypergraph n
  let U : Finset (Fin n) := Finset.univ
  let T := U.powersetCard 3
  have hsub : H ⊆ T := fun e he =>
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hunif e he⟩
  refine ⟨T \ H, ⟨?_, ?_⟩, ?_⟩
  · intro e he
    exact Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1
  · intro S hS
    have h4 := (Finset.mem_powersetCard.mp hS).2
    have hnot : ¬ S.powersetCard 3 ⊆ H := fun h => hfree ⟨S, h4, h⟩
    obtain ⟨e, he, hne⟩ := Finset.not_subset.mp hnot
    obtain ⟨heS, he3⟩ := Finset.mem_powersetCard.mp he
    exact ⟨e, Finset.mem_sdiff.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, he3⟩, hne⟩, heS⟩
  · rw [← hcard, Finset.card_sdiff_add_card_eq_card hsub]
    simp [T, U, Finset.card_powersetCard]

/-- Every cover of the four-sets on six vertices needs at least six missing triples. -/
theorem OMA.cliqueExtremalNumber_six_le : Hypergraph.cliqueExtremalNumber 6 3 4 ≤ 14 := by
  obtain ⟨M, hcover, hM⟩ := OMA.exists_extremal_cover 6
  have hl := (OMA.card_cover_six hcover (by simp)).1
  rw [show (6 : ℕ).choose 3 = 20 by decide] at hM
  omega

/-- A seven-vertex cover needs at least twelve missing triples. -/
theorem OMA.cliqueExtremalNumber_seven_le : Hypergraph.cliqueExtremalNumber 7 3 4 ≤ 23 := by
  obtain ⟨M, hcover, hM⟩ := OMA.exists_extremal_cover 7
  have hl := OMA.card_cover_seven hcover (by simp)
  rw [show (7 : ℕ).choose 3 = 35 by decide] at hM
  omega

/-- Integer upper bounds obtained by iterating the vertex-deletion inequality from seven. -/
private def OMA.extremalCap : ℕ → ℕ
  | 0 => 23
  | k + 1 => (k + 8) * OMA.extremalCap k / (k + 5)

private theorem OMA.cliqueExtremalNumber_le_cap (k : ℕ) :
    Hypergraph.cliqueExtremalNumber (k + 7) 3 4 ≤ OMA.extremalCap k := by
  induction k with
  | zero => exact OMA.cliqueExtremalNumber_seven_le
  | succ k ih =>
    change Hypergraph.cliqueExtremalNumber (k + 8) 3 4 ≤ (k + 8) * OMA.extremalCap k / (k + 5)
    apply (Nat.le_div_iff_mul_le (by omega : 0 < k + 5)).2
    have hs := OMA.cliqueExtremalNumber_step (k + 7) (by omega)
    rw [show k + 7 - 2 = k + 5 by omega] at hs
    simpa only [Nat.mul_comm (Hypergraph.cliqueExtremalNumber (k + 8) 3 4) (k + 5)]
      using hs.trans (Nat.mul_le_mul_left (k + 8) ih)

/-- Turán's construction attains the deletion upper bound on nine vertices. -/
theorem OMA.cliqueExtremalNumber_nine :
    Hypergraph.cliqueExtremalNumber 9 3 4 = 54 := by
  apply le_antisymm
  · exact OMA.cliqueExtremalNumber_le_cap 2
  · exact OMA.turan_extremal_lower_nat 9

/-- The seven-vertex covering bound and vertex-deletion recurrence give a uniform upper bound. -/
theorem OMA.turanDensity_le_twenty_two_thirty_fifths (n : ℕ) (hn : 21 ≤ n) :
    OMA.turanDensity n ≤ 22 / 35 := by
  have h21 : OMA.turanDensity 21 ≤ 22 / 35 := by
    have hb : Hypergraph.cliqueExtremalNumber 21 3 4 ≤ 836 := OMA.cliqueExtremalNumber_le_cap 14
    have hc : (Hypergraph.cliqueExtremalNumber 21 3 4 : ℝ) ≤ 836 := by exact_mod_cast hb
    rw [OMA.turanDensity, show (21 : ℕ).choose 3 = 1330 by decide, Nat.cast_ofNat]
    linarith
  exact (OMA.turanDensity_antitone (by omega) hn).trans h21

/-- Existence of the Turan density limit pi(K_4^3) in [5/9, 7/10]. -/
theorem OMA.exists_turanDensity_limit :
    ∃ L : ℝ, 5 / 9 ≤ L ∧ L ≤ 7 / 10 ∧ Tendsto OMA.turanDensity atTop (𝓝 L) := by
  let g : ℕ → ℝ := fun k => OMA.turanDensity (k + 3)
  have hg_anti : Antitone g := fun a b hab =>
    OMA.turanDensity_antitone (by omega) (by omega)
  have hg_bdd : BddBelow (Set.range g) := by
    refine ⟨5 / 9, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact OMA.five_ninths_le_turanDensity (k + 3) (by omega)
  refine ⟨⨅ k, g k, ?_, ?_, ?_⟩
  · exact le_ciInf (fun k => OMA.five_ninths_le_turanDensity (k + 3) (by omega))
  · exact (ciInf_le hg_bdd 2).trans (OMA.turanDensity_le_seven_tenths 5 le_rfl)
  · have htend : Tendsto g atTop (𝓝 (⨅ k, g k)) := tendsto_atTop_ciInf hg_anti hg_bdd
    exact (tendsto_add_atTop_iff_nat 3).mp htend

/-- The Turán density limit lies between the construction and the deletion upper bound. -/
theorem OMA.exists_turanDensity_limit_le_twenty_two_thirty_fifths :
    ∃ L : ℝ, 5 / 9 ≤ L ∧ L ≤ 22 / 35 ∧ Tendsto OMA.turanDensity atTop (𝓝 L) := by
  obtain ⟨L, hlo, _, ht⟩ := OMA.exists_turanDensity_limit
  refine ⟨L, hlo, le_of_tendsto ht ?_, ht⟩
  exact (eventually_ge_atTop 21).mono (fun n hn => OMA.turanDensity_le_twenty_two_thirty_fifths n hn)

/-- Open upper bound half of Turan's tetrahedron conjecture (OPEN since 1941):
by KNS monotonicity, it suffices to find for each eps > 0 some n >= 3 with density <= 5/9 + eps. -/
theorem OMA.turan_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 3 ≤ n ∧ OMA.turanDensity n ≤ 5 / 9 + ε := by
  sorry

/-- Turan tetrahedron conjecture in density form (reduced to OMA.turan_upper_bound). -/
theorem OMA.turan_density :
    Tendsto (fun n : ℕ => (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) / (n.choose 3 : ℝ))
      atTop (𝓝 (5 / 9)) := by
  change Tendsto OMA.turanDensity atTop (𝓝 (5 / 9))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN3, hNle⟩ := OMA.turan_upper_bound (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hlo : 5 / 9 ≤ OMA.turanDensity n := OMA.five_ninths_le_turanDensity n (le_trans hN3 hn)
  have hhi : OMA.turanDensity n ≤ 5 / 9 + ε / 2 :=
    (OMA.turanDensity_antitone hN3 hn).trans hNle
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem OMA.solution : type_of% @Erdos500.erdos_500.variants.turan_conjecture := by
  exact OMA.isEquivalent_of_ratio _ OMA.turan_density
