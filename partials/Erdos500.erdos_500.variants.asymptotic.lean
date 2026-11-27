import FormalConjectures.ErdosProblems.«500»

-- Problem: Erdős Problem 500 — asymptotic (it asks for a value)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/500.lean:112 (declaration Erdos500.erdos_500.variants.asymptotic; placeholder Erdos500.erdos_500.variants.asymptotic.answer := sorry)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Give the value explicitly as OMA.answer (same type as the placeholder; not built from Erdos500.…,
-- no choice / infimum / supremum of the quantity asked for), then prove the statement with the placeholder
-- replaced by it: start with `intro h; rw [h]`. No sorry, no axiom, no native_decide. A person checks the answer.

/-!
Partial proof of Erdős Problem 500 (asymptotic Turán density of the tetrahedron K_4^3):
- Sets the conjectured explicit value `OMA.answer : ℝ := 5 / 9`.
- Proves Katona-Nemetz-Simonovits monotonicity of the Turán density and existence of the limit.
- Proves Turán's 3-partite construction lower bound `5 / 9 ≤ L`.
- Determines the exact extremal numbers `ex_3(n, K_4^3)` for `n = 4, 5, 6, 7, 8, 9` (3, 7, 14, 23, 36, 54),
  proves `ex_3(10, K_4^3) ≤ 76`, and iterates KNS to prove `L ≤ 5 / 8` and `L ≤ 99481 / 161700` (< 0.6153).
- Proves the blow-up lower bound and the finite cubic equivalence:
  `L = 5 / 9 ↔ ∀ n > 0, 54 * ex_3(n, K_4^3) ≤ 5 * n ^ 3`.
- Improves the 39-vertex deletion bound to 5628 edges and verifies the target cubic inequality through 29 vertices.
- A five-vertex sum-of-squares certificate gives the sharper bound `L ≤ 23 / 40`.
- Reduces `OMA.solution` to the single open conjecture `OMA.turan_upper_bound`.
-/

open Filter Asymptotics Topology
open scoped Classical

/-- Conjectured Turan density of K_4^3 (Turan 1941). -/
noncomputable def OMA.answer : ℝ := 5 / 9

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

private lemma OMA.card_turanGraph_ge_parts (n : ℕ) :
    (OMA.colorClass n 0).card * ((OMA.colorClass n 1).card * (OMA.colorClass n 2).card) +
      (OMA.colorClass n 0).card.choose 2 * (OMA.colorClass n 1).card +
      (OMA.colorClass n 1).card.choose 2 * (OMA.colorClass n 2).card +
      (OMA.colorClass n 2).card.choose 2 * (OMA.colorClass n 0).card ≤
      (OMA.turanGraph n).card := by
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
  rw [hcard_rain, hcard_01, hcard_12, hcard_20] at hle_total
  exact hle_total

private lemma OMA.card_turanGraph_ge (n : ℕ) :
    (n / 3) ^ 3 + 3 * ((n / 3).choose 2 * (n / 3)) ≤ (OMA.turanGraph n).card := by
  have hparts := OMA.card_turanGraph_ge_parts n
  have hV0 : n / 3 ≤ (OMA.colorClass n 0).card := OMA.div_three_le_card_colorClass n 0 (by decide)
  have hV1 : n / 3 ≤ (OMA.colorClass n 1).card := OMA.div_three_le_card_colorClass n 1 (by decide)
  have hV2 : n / 3 ≤ (OMA.colorClass n 2).card := OMA.div_three_le_card_colorClass n 2 (by decide)
  have hr_ge : (n / 3) ^ 3 ≤
      (OMA.colorClass n 0).card * ((OMA.colorClass n 1).card * (OMA.colorClass n 2).card) := by
    rw [pow_three]
    exact Nat.mul_le_mul hV0 (Nat.mul_le_mul hV1 hV2)
  have h01_ge : (n / 3).choose 2 * (n / 3) ≤
      (OMA.colorClass n 0).card.choose 2 * (OMA.colorClass n 1).card :=
    Nat.mul_le_mul (Nat.choose_le_choose 2 hV0) hV1
  have h12_ge : (n / 3).choose 2 * (n / 3) ≤
      (OMA.colorClass n 1).card.choose 2 * (OMA.colorClass n 2).card :=
    Nat.mul_le_mul (Nat.choose_le_choose 2 hV1) hV2
  have h20_ge : (n / 3).choose 2 * (n / 3) ≤
      (OMA.colorClass n 2).card.choose 2 * (OMA.colorClass n 0).card :=
    Nat.mul_le_mul (Nat.choose_le_choose 2 hV2) hV0
  omega

/-- Turan lower bound via exact class sizes. -/
theorem OMA.turan_extremal_lower_parts (n : ℕ) :
    (OMA.colorClass n 0).card * ((OMA.colorClass n 1).card * (OMA.colorClass n 2).card) +
      (OMA.colorClass n 0).card.choose 2 * (OMA.colorClass n 1).card +
      (OMA.colorClass n 1).card.choose 2 * (OMA.colorClass n 2).card +
      (OMA.colorClass n 2).card.choose 2 * (OMA.colorClass n 0).card ≤
      Hypergraph.cliqueExtremalNumber n 3 4 := by
  have hunif : ∀ e ∈ OMA.turanGraph n, e.card = 3 := fun e he =>
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
  exact (OMA.card_turanGraph_ge_parts n).trans
    (OMA.cliqueExtremalNumber_ge_card (OMA.turanGraph n) hunif (OMA.turanGraph_no_K4 n))

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

private theorem OMA.card_cover_four {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (hU : U.card = 4) :
    1 ≤ M.card := by
  obtain ⟨e, he, _⟩ := h.2 U (Finset.mem_powersetCard.mpr ⟨Finset.Subset.rfl, hU⟩)
  exact Finset.card_pos.mpr ⟨e, he⟩

private theorem OMA.card_cover_five {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (hU : U.card = 5) :
    3 ≤ M.card := by
  have hlocal : ∀ v ∈ U, 1 ≤ (OMA.avoidVertex M v).card := by
    intro v hv
    exact OMA.card_cover_four (OMA.coversFourSets_erase h v)
      (by rw [Finset.card_erase_of_mem hv, hU])
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

/-- Exact extremal number on 4 vertices: ex_3(4, K_4^3) = 3. -/
theorem OMA.cliqueExtremalNumber_four : Hypergraph.cliqueExtremalNumber 4 3 4 = 3 := by
  apply le_antisymm
  · obtain ⟨M, hcover, hM⟩ := OMA.exists_extremal_cover 4
    have hl := OMA.card_cover_four hcover (by simp)
    rw [show (4 : ℕ).choose 3 = 4 by decide] at hM
    omega
  · have h := OMA.turan_extremal_lower_parts 4
    have c0 : (OMA.colorClass 4 0).card = 2 := by decide
    have c1 : (OMA.colorClass 4 1).card = 1 := by decide
    have c2 : (OMA.colorClass 4 2).card = 1 := by decide
    rw [c0, c1, c2] at h
    exact le_trans (by decide) h

/-- Exact extremal number on 5 vertices: ex_3(5, K_4^3) = 7. -/
theorem OMA.cliqueExtremalNumber_five : Hypergraph.cliqueExtremalNumber 5 3 4 = 7 := by
  apply le_antisymm
  · obtain ⟨M, hcover, hM⟩ := OMA.exists_extremal_cover 5
    have hl := OMA.card_cover_five hcover (by simp)
    rw [show (5 : ℕ).choose 3 = 10 by decide] at hM
    omega
  · have h := OMA.turan_extremal_lower_parts 5
    have c0 : (OMA.colorClass 5 0).card = 2 := by decide
    have c1 : (OMA.colorClass 5 1).card = 2 := by decide
    have c2 : (OMA.colorClass 5 2).card = 1 := by decide
    rw [c0, c1, c2] at h
    exact le_trans (by decide) h

/-- Exact extremal number on 6 vertices: ex_3(6, K_4^3) = 14. -/
theorem OMA.cliqueExtremalNumber_six : Hypergraph.cliqueExtremalNumber 6 3 4 = 14 := by
  apply le_antisymm
  · obtain ⟨M, hcover, hM⟩ := OMA.exists_extremal_cover 6
    have hl := (OMA.card_cover_six hcover (by simp)).1
    rw [show (6 : ℕ).choose 3 = 20 by decide] at hM
    omega
  · have h := OMA.turan_extremal_lower_parts 6
    have c0 : (OMA.colorClass 6 0).card = 2 := by decide
    have c1 : (OMA.colorClass 6 1).card = 2 := by decide
    have c2 : (OMA.colorClass 6 2).card = 2 := by decide
    rw [c0, c1, c2] at h
    exact le_trans (by decide) h

/-- Exact extremal number on 7 vertices: ex_3(7, K_4^3) = 23. -/
theorem OMA.cliqueExtremalNumber_seven : Hypergraph.cliqueExtremalNumber 7 3 4 = 23 := by
  apply le_antisymm
  · obtain ⟨M, hcover, hM⟩ := OMA.exists_extremal_cover 7
    have hl := OMA.card_cover_seven hcover (by simp)
    rw [show (7 : ℕ).choose 3 = 35 by decide] at hM
    omega
  · have h := OMA.turan_extremal_lower_parts 7
    have c0 : (OMA.colorClass 7 0).card = 3 := by decide
    have c1 : (OMA.colorClass 7 1).card = 2 := by decide
    have c2 : (OMA.colorClass 7 2).card = 2 := by decide
    rw [c0, c1, c2] at h
    exact le_trans (by decide) h

/-- Integer upper bounds obtained by iterating the vertex-deletion inequality from seven. -/
private def OMA.extremalCap : ℕ → ℕ
  | 0 => 23
  | k + 1 => (k + 8) * OMA.extremalCap k / (k + 5)

private theorem OMA.cliqueExtremalNumber_le_cap (k : ℕ) :
    Hypergraph.cliqueExtremalNumber (k + 7) 3 4 ≤ OMA.extremalCap k := by
  induction k with
  | zero => exact OMA.cliqueExtremalNumber_seven.le
  | succ k ih =>
    change Hypergraph.cliqueExtremalNumber (k + 8) 3 4 ≤ (k + 8) * OMA.extremalCap k / (k + 5)
    apply (Nat.le_div_iff_mul_le (by omega : 0 < k + 5)).2
    have hs := OMA.cliqueExtremalNumber_step (k + 7) (by omega)
    rw [show k + 7 - 2 = k + 5 by omega] at hs
    simpa only [Nat.mul_comm (Hypergraph.cliqueExtremalNumber (k + 8) 3 4) (k + 5)]
      using hs.trans (Nat.mul_le_mul_left (k + 8) ih)

/-- Exact extremal number on 8 vertices: ex_3(8, K_4^3) = 36. -/
theorem OMA.cliqueExtremalNumber_eight : Hypergraph.cliqueExtremalNumber 8 3 4 = 36 := by
  apply le_antisymm
  · exact OMA.cliqueExtremalNumber_le_cap 1
  · have h := OMA.turan_extremal_lower_parts 8
    have c0 : (OMA.colorClass 8 0).card = 3 := by decide
    have c1 : (OMA.colorClass 8 1).card = 3 := by decide
    have c2 : (OMA.colorClass 8 2).card = 2 := by decide
    rw [c0, c1, c2] at h
    exact le_trans (by decide) h

/-- Exact extremal number on 9 vertices: ex_3(9, K_4^3) = 54. -/
theorem OMA.cliqueExtremalNumber_nine : Hypergraph.cliqueExtremalNumber 9 3 4 = 54 := by
  apply le_antisymm
  · exact OMA.cliqueExtremalNumber_le_cap 2
  · exact OMA.turan_extremal_lower_nat 9

private theorem OMA.card_cover_eight {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (hU : U.card = 8) :
    20 ≤ M.card := by
  have hlocal : ∀ v ∈ U, 12 ≤ (OMA.avoidVertex M v).card := by
    intro v hv
    exact OMA.card_cover_seven (OMA.coversFourSets_erase h v)
      (by rw [Finset.card_erase_of_mem hv, hU])
  have hs := OMA.sum_card_avoidVertex h.1
  rw [hU] at hs
  have hl : ∑ v ∈ U, (12 : ℕ) ≤ ∑ v ∈ U, (OMA.avoidVertex M v).card :=
    Finset.sum_le_sum hlocal
  simp only [Finset.sum_const, nsmul_eq_mul, hU] at hl
  omega

private theorem OMA.card_cover_nine {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (hU : U.card = 9) :
    30 ≤ M.card ∧ (M.card = 30 → ∀ v ∈ U, (OMA.avoidVertex M v).card = 20) := by
  have hlocal : ∀ v ∈ U, 20 ≤ (OMA.avoidVertex M v).card := by
    intro v hv
    exact OMA.card_cover_eight (OMA.coversFourSets_erase h v)
      (by rw [Finset.card_erase_of_mem hv, hU])
  have hs := OMA.sum_card_avoidVertex h.1
  rw [hU] at hs
  have hl : ∑ v ∈ U, (20 : ℕ) ≤ ∑ v ∈ U, (OMA.avoidVertex M v).card :=
    Finset.sum_le_sum hlocal
  simp only [Finset.sum_const, nsmul_eq_mul, hU] at hl
  refine ⟨by omega, ?_⟩
  intro hM v hv
  have hr : ∑ w ∈ U.erase v, (20 : ℕ) ≤ ∑ w ∈ U.erase v, (OMA.avoidVertex M w).card :=
    Finset.sum_le_sum (fun w hw => hlocal w (Finset.mem_of_mem_erase hw))
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hv, hU] at hr
  rw [← Finset.sum_erase_add _ _ hv] at hs
  have := hlocal v hv
  omega

/-- A ten-vertex cover of four-sets needs at least 44 triples:
a 43-triple cover would have total deletion excess 1, forcing one vertex of degree 12
and nine vertices of degree 13 whose deletions are tight 30-triple covers on 9 vertices
(all 10-regular), forcing every pair through the degree-12 vertex to have codegree 2,
which gives sum 18 != 24. -/
private theorem OMA.card_cover_ten {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M) (hU : U.card = 10) :
    44 ≤ M.card := by
  let a := fun v => (OMA.avoidVertex M v).card
  have hlocal (v : α) (hv : v ∈ U) : 30 ≤ a v :=
    (OMA.card_cover_nine (OMA.coversFourSets_erase h v)
      (by rw [Finset.card_erase_of_mem hv, hU])).1
  have hs : ∑ v ∈ U, a v = M.card * 7 := by
    simpa [a, hU] using OMA.sum_card_avoidVertex h.1
  have hl : ∑ v ∈ U, (30 : ℕ) ≤ ∑ v ∈ U, a v := Finset.sum_le_sum hlocal
  simp only [Finset.sum_const, nsmul_eq_mul, hU] at hl
  by_contra! hsmall
  have hM : M.card = 43 := by omega
  let L := U.filter (fun v => 30 < a v)
  have hLU : L ⊆ U := Finset.filter_subset _ _
  have hlow (v : α) (hv : v ∈ L) : 30 < a v := (Finset.mem_filter.mp hv).2
  have hexcess : ∑ v ∈ L, (a v - 30) = 1 := by
    have hsplit : ∑ v ∈ U, a v = (∑ v ∈ U, (a v - 30)) + ∑ v ∈ U, 30 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v hv => (Nat.sub_add_cancel (hlocal v hv)).symm)
    simp only [Finset.sum_const, nsmul_eq_mul, hU] at hsplit
    have heq : ∑ v ∈ L, (a v - 30) = ∑ v ∈ U, (a v - 30) := by
      apply Finset.sum_subset hLU
      intro v hvU hv
      exact Nat.sub_eq_zero_of_le (Nat.le_of_not_gt
        (fun hp => hv (Finset.mem_filter.mpr ⟨hvU, hp⟩)))
    rw [heq]
    omega
  have hLle : L.card ≤ 1 := by
    have h1 := Finset.sum_le_sum (fun v hv => Nat.succ_le_of_lt (Nat.sub_pos_of_lt (hlow v hv)))
    change (∑ v ∈ L, (1 : ℕ)) ≤ ∑ v ∈ L, (a v - 30) at h1
    simpa [hexcess] using h1
  have hLpos : 0 < L.card := by
    apply Finset.card_pos.mpr
    by_contra! he
    rw [he, Finset.sum_empty] at hexcess
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by omega : L.card = 1)
  have hxL : x ∈ L := by simp [hx]
  have hxU : x ∈ U := hLU hxL
  simp only [hx, Finset.sum_singleton] at hexcess
  have hax : a x = 31 := by have := hlow x hxL; omega
  have hxv := OMA.vertexDegree_add_avoid M x
  have hdx : OMA.vertexDegree M x = 12 := by
    change OMA.vertexDegree M x + a x = M.card at hxv
    omega
  have hpair (z : α) (hz : z ∈ U.erase x) : (OMA.throughPair M x z).card = 2 := by
    obtain ⟨hne, hzU⟩ := Finset.mem_erase.mp hz
    have hznotL : z ∉ L := by simp [hx, hne]
    have haz : a z = 30 := by
      have hnot : ¬ 30 < a z := fun hp => hznotL (Finset.mem_filter.mpr ⟨hzU, hp⟩)
      have hge := hlocal z hzU
      omega
    have hU9 : (U.erase z).card = 9 := by rw [Finset.card_erase_of_mem hzU, hU]
    have havo := (OMA.card_cover_nine (OMA.coversFourSets_erase h z) hU9).2
      haz x (Finset.mem_erase.mpr ⟨hne.symm, hxU⟩)
    have hd := OMA.vertexDegree_add_avoid (OMA.avoidVertex M z) x
    rw [havo] at hd
    change OMA.vertexDegree (OMA.avoidVertex M z) x + 20 = a z at hd
    have hd10 : OMA.vertexDegree (OMA.avoidVertex M z) x = 10 := by omega
    have hrel := OMA.vertexDegree_erase_add M x z
    omega
  have hsum := OMA.sum_card_throughPair h x
  rw [Finset.sum_congr rfl hpair, hdx] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hxU, hU] at hsum
  omega

private theorem OMA.throughPair_comm {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) (v w : α) :
    OMA.throughPair M v w = OMA.throughPair M w v := by
  ext e
  simp only [OMA.throughPair, Finset.mem_filter]
  exact and_congr_right (fun _ => and_comm)

private theorem OMA.degree_cover_nine {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M)
    (hU : U.card = 9) (hM : M.card = 30) {v : α} (hv : v ∈ U) :
    OMA.vertexDegree M v = 10 := by
  have hd := OMA.vertexDegree_add_avoid M v
  rw [(OMA.card_cover_nine h hU).2 hM v hv, hM] at hd
  omega

/-- Every pair in an optimal nine-vertex cover lies in at least two covering triples. -/
private theorem OMA.pair_degree_cover_nine {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M)
    (hU : U.card = 9) (hM : M.card = 30) {v w : α}
    (hv : v ∈ U) (hw : w ∈ U) (hvw : v ≠ w) :
    2 ≤ (OMA.throughPair M v w).card := by
  have hvw' : v ∈ U.erase w := Finset.mem_erase.mpr ⟨hvw, hv⟩
  have hUw : (U.erase w).card = 8 := by rw [Finset.card_erase_of_mem hw, hU]
  have hUwv : ((U.erase w).erase v).card = 7 := by
    rw [Finset.card_erase_of_mem hvw', hUw]
  have hsmall := OMA.card_cover_seven
    (OMA.coversFourSets_erase (OMA.coversFourSets_erase h w) v) hUwv
  have hsum₁ := OMA.vertexDegree_add_avoid M w
  have hsum₂ := OMA.vertexDegree_add_avoid (OMA.avoidVertex M w) v
  have hsum₃ := OMA.vertexDegree_erase_add M v w
  rw [OMA.degree_cover_nine h hU hM hw, hM] at hsum₁
  rw [OMA.degree_cover_nine h hU hM hv] at hsum₃
  omega

/-- A 44-triple ten-vertex cover has at least two vertices whose deletion is optimal. -/
private theorem OMA.tight_vertices_cover_ten {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M)
    (hU : U.card = 10) (hM : M.card = 44) :
    2 ≤ (U.filter (fun v => (OMA.avoidVertex M v).card = 30)).card := by
  let L := U.filter (fun v => (OMA.avoidVertex M v).card = 30)
  let B := U \ L
  have hL : L ⊆ U := Finset.filter_subset _ _
  have hB : B.card = U.card - L.card := Finset.card_sdiff_of_subset hL
  have hlocal (v : α) (hv : v ∈ U) : 30 ≤ (OMA.avoidVertex M v).card :=
    (OMA.card_cover_nine (OMA.coversFourSets_erase h v)
      (by rw [Finset.card_erase_of_mem hv, hU])).1
  have hlB : ∑ v ∈ B, (31 : ℕ) ≤ ∑ v ∈ B, (OMA.avoidVertex M v).card := by
    apply Finset.sum_le_sum
    intro v hv
    obtain ⟨hvU, hvL⟩ := Finset.mem_sdiff.mp hv
    have hne : (OMA.avoidVertex M v).card ≠ 30 :=
      fun he => hvL (Finset.mem_filter.mpr ⟨hvU, he⟩)
    have := hlocal v hvU
    omega
  have hlL : ∑ v ∈ L, (OMA.avoidVertex M v).card = ∑ v ∈ L, (30 : ℕ) :=
    Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
  have hs := OMA.sum_card_avoidVertex h.1
  rw [← Finset.sum_sdiff hL, hlL, hU, hM] at hs
  change (∑ v ∈ B, (OMA.avoidVertex M v).card) + ∑ v ∈ L, (30 : ℕ) = _ at hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hlB hs
  rw [hU] at hB
  change B.card * 31 ≤ ∑ v ∈ B, (OMA.avoidVertex M v).card at hlB
  change (∑ v ∈ B, (OMA.avoidVertex M v).card) + L.card * 30 = 308 at hs
  have hcard : 2 ≤ L.card := by omega
  exact hcard

/-- Every vertex of a 44-triple ten-vertex cover has degree at least twelve.
A vertex of degree twelve cannot form a triple with two optimal deletion vertices. -/
private theorem OMA.degree_and_triple_cover_ten {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} (h : OMA.CoversFourSets U M)
    (hU : U.card = 10) (hM : M.card = 44) {v : α} (hv : v ∈ U) :
    12 ≤ OMA.vertexDegree M v ∧
      (OMA.vertexDegree M v = 12 → ∀ x ∈ U, ∀ y ∈ U, x ≠ y →
        (OMA.avoidVertex M x).card = 30 → (OMA.avoidVertex M y).card = 30 →
        ({v, x, y} : Finset α) ∉ M) := by
  have pair (x y : α) (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y)
      (hvx : v ≠ x) (hvy : v ≠ y) (hax : (OMA.avoidVertex M x).card = 30)
      (hay : (OMA.avoidVertex M y).card = 30) :
      2 ≤ (OMA.throughPair (OMA.avoidVertex M x) v y).card ∧
      (OMA.throughPair M v y).card + 10 = OMA.vertexDegree M v := by
    have hx9 : (U.erase x).card = 9 := by rw [Finset.card_erase_of_mem hx, hU]
    have hy9 : (U.erase y).card = 9 := by rw [Finset.card_erase_of_mem hy, hU]
    refine ⟨OMA.pair_degree_cover_nine (OMA.coversFourSets_erase h x) hx9 hax
      (Finset.mem_erase.mpr ⟨hvx, hv⟩) (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩) hvy, ?_⟩
    rw [← OMA.degree_cover_nine (OMA.coversFourSets_erase h y) hy9 hay
      (Finset.mem_erase.mpr ⟨hvy, hv⟩)]
    exact OMA.vertexDegree_erase_add M v y
  have sub (x y : α) : OMA.throughPair (OMA.avoidVertex M x) v y ⊆ OMA.throughPair M v y := by
    intro e he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,
      (Finset.mem_filter.mp he).2⟩
  constructor
  · by_cases ht : (OMA.avoidVertex M v).card = 30
    · have hd := OMA.vertexDegree_add_avoid M v
      omega
    · let L := U.filter (fun w => (OMA.avoidVertex M w).card = 30)
      have hL : 1 < L.card := OMA.tight_vertices_cover_ten h hU hM
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hL
      obtain ⟨hxU, hax⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyU, hay⟩ := Finset.mem_filter.mp hy
      have hp := pair x y hxU hyU hxy (by rintro rfl; exact ht hax)
        (by rintro rfl; exact ht hay) hax hay
      have := Finset.card_le_card (sub x y)
      omega
  · intro hd x hx y hy hxy hax hay he
    have hb := OMA.vertexDegree_add_avoid M v
    have hvx : v ≠ x := by rintro rfl; omega
    have hvy : v ≠ y := by rintro rfl; omega
    have hp := pair x y hx hy hxy hvx hvy hax hay
    have hstrict : OMA.throughPair (OMA.avoidVertex M x) v y ⊂ OMA.throughPair M v y := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨sub x y, ?_⟩
      intro heq
      have hin : ({v, x, y} : Finset α) ∈ OMA.throughPair M v y := by
        simp [OMA.throughPair, he]
      rw [← heq] at hin
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hin).1).2 (by simp)
    have := Finset.card_lt_card hstrict
    omega

/-- Upper bound on 10 vertices: ex_3(10, K_4^3) <= 76. -/
theorem OMA.cliqueExtremalNumber_ten_le : Hypergraph.cliqueExtremalNumber 10 3 4 ≤ 76 := by
  obtain ⟨M, hcover, hM⟩ := OMA.exists_extremal_cover 10
  have hl := OMA.card_cover_ten hcover (by simp)
  have hch : (10 : ℕ).choose 3 = 120 := by
    have h6 := OMA.six_mul_choose_three 10
    omega
  rw [hch] at hM
  omega

/-- General tail-recursive KNS vertex-deletion upper bound iterator. -/
private def OMA.knsIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, c => c
  | k + 1, n, c => OMA.knsIter k (n + 1) ((n + 1) * c / (n - 2))

private theorem OMA.cliqueExtremalNumber_le_knsIter (k : ℕ) :
    ∀ n c, 3 ≤ n → Hypergraph.cliqueExtremalNumber n 3 4 ≤ c →
      Hypergraph.cliqueExtremalNumber (n + k) 3 4 ≤ OMA.knsIter k n c := by
  induction k with
  | zero =>
    intro n c _ h
    simpa [OMA.knsIter] using h
  | succ k ih =>
    intro n c hn h
    have hstep : Hypergraph.cliqueExtremalNumber (n + 1) 3 4 ≤ (n + 1) * c / (n - 2) := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < n - 2)).2
      have hs := OMA.cliqueExtremalNumber_step n hn
      simpa only [Nat.mul_comm (Hypergraph.cliqueExtremalNumber (n + 1) 3 4) (n - 2)]
        using hs.trans (Nat.mul_le_mul_left (n + 1) h)
    have hrec := ih (n + 1) ((n + 1) * c / (n - 2)) (by omega) hstep
    simpa only [OMA.knsIter, show n + (k + 1) = n + 1 + k by omega] using hrec

/-- The seven-vertex covering bound and vertex-deletion recurrence give a uniform upper bound. -/
theorem OMA.turanDensity_le_twenty_two_thirty_fifths (n : ℕ) (hn : 21 ≤ n) :
    OMA.turanDensity n ≤ 22 / 35 := by
  have h21 : OMA.turanDensity 21 ≤ 22 / 35 := by
    have hb : Hypergraph.cliqueExtremalNumber 21 3 4 ≤ 836 := OMA.cliqueExtremalNumber_le_cap 14
    have hc : (Hypergraph.cliqueExtremalNumber 21 3 4 : ℝ) ≤ 836 := by exact_mod_cast hb
    rw [OMA.turanDensity, show (21 : ℕ).choose 3 = 1330 by decide, Nat.cast_ofNat]
    linarith
  exact (OMA.turanDensity_antitone (by omega) hn).trans h21

/-- Iterating KNS from ex_3(10, K_4^3) <= 76 beats 5/8 = 0.625 by n = 14 (227/364 < 5/8). -/
theorem OMA.turanDensity_le_five_eighths (n : ℕ) (hn : 14 ≤ n) :
    OMA.turanDensity n ≤ 5 / 8 := by
  have h14 : OMA.turanDensity 14 ≤ 5 / 8 := by
    have hb : Hypergraph.cliqueExtremalNumber 14 3 4 ≤ 227 :=
      OMA.cliqueExtremalNumber_le_knsIter 4 10 76 (by omega) OMA.cliqueExtremalNumber_ten_le
    have hc : (Hypergraph.cliqueExtremalNumber 14 3 4 : ℝ) ≤ 227 := by exact_mod_cast hb
    have hch : (14 : ℕ).choose 3 = 364 := by
      have h6 := OMA.six_mul_choose_three 14
      omega
    rw [OMA.turanDensity, hch, Nat.cast_ofNat]
    linarith
  exact (OMA.turanDensity_antitone (by omega) hn).trans h14

/-- Iterating KNS from ex_3(10, K_4^3) <= 76 to n = 100 yields turanDensity n <= 99481/161700 (< 0.6153). -/
theorem OMA.turanDensity_le_of_ten (n : ℕ) (hn : 100 ≤ n) :
    OMA.turanDensity n ≤ 99481 / 161700 := by
  have h100 : OMA.turanDensity 100 ≤ 99481 / 161700 := by
    have h25 : Hypergraph.cliqueExtremalNumber 25 3 4 ≤ 1419 :=
      OMA.cliqueExtremalNumber_le_knsIter 15 10 76 (by omega) OMA.cliqueExtremalNumber_ten_le
    have h40 : Hypergraph.cliqueExtremalNumber 40 3 4 ≤ 6085 :=
      OMA.cliqueExtremalNumber_le_knsIter 15 25 1419 (by omega) h25
    have h55 : Hypergraph.cliqueExtremalNumber 55 3 4 ≤ 16149 :=
      OMA.cliqueExtremalNumber_le_knsIter 15 40 6085 (by omega) h40
    have h70 : Hypergraph.cliqueExtremalNumber 70 3 4 ≤ 33685 :=
      OMA.cliqueExtremalNumber_le_knsIter 15 55 16149 (by omega) h55
    have h85 : Hypergraph.cliqueExtremalNumber 85 3 4 ≤ 60770 :=
      OMA.cliqueExtremalNumber_le_knsIter 15 70 33685 (by omega) h70
    have hb : Hypergraph.cliqueExtremalNumber 100 3 4 ≤ 99481 :=
      OMA.cliqueExtremalNumber_le_knsIter 15 85 60770 (by omega) h85
    have hc : (Hypergraph.cliqueExtremalNumber 100 3 4 : ℝ) ≤ 99481 := by exact_mod_cast hb
    have hch : (100 : ℕ).choose 3 = 161700 := by
      have h6 := OMA.six_mul_choose_three 100
      omega
    rw [OMA.turanDensity, hch, Nat.cast_ofNat]
    linarith
  exact (OMA.turanDensity_antitone (by omega) hn).trans h100

/-- Rounded lower bounds on the number of triples needed to cover all four-sets. -/
private def OMA.coverIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, c => c
  | k + 1, n, c => OMA.coverIter k (n + 1) (((n + 1) * c + (n - 3)) / (n - 2))

private theorem OMA.card_cover_ge_iter {α : Type*} [DecidableEq α] (k : ℕ) :
    ∀ {U : Finset α} {M : Finset (Finset α)} {n c : ℕ},
      OMA.CoversFourSets U M → U.card = n + k → 3 ≤ n →
      (∀ (V : Finset α) (N : Finset (Finset α)),
        OMA.CoversFourSets V N → V.card = n → c ≤ N.card) →
      OMA.coverIter k n c ≤ M.card := by
  induction k with
  | zero =>
    intro U M n c h hU _ hbase
    exact hbase U M h (by simpa using hU)
  | succ k ih =>
    intro U M n c h hU hn hbase
    have hstep (V : Finset α) (N : Finset (Finset α))
        (hN : OMA.CoversFourSets V N) (hV : V.card = n + 1) :
        ((n + 1) * c + (n - 3)) / (n - 2) ≤ N.card := by
      have hs : ∑ x ∈ V, c ≤ ∑ x ∈ V, (OMA.avoidVertex N x).card :=
        Finset.sum_le_sum fun x hx =>
          hbase _ _ (OMA.coversFourSets_erase hN x)
            (by rw [Finset.card_erase_of_mem hx, hV]; omega)
      rw [OMA.sum_card_avoidVertex hN.1] at hs
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, hV] at hs
      rw [show n + 1 - 3 = n - 2 by omega] at hs
      apply (Nat.div_le_iff_le_mul_add_pred (by omega : 0 < n - 2)).2
      rw [show n - 2 - 1 = n - 3 by omega, Nat.mul_comm (n - 2) N.card]
      exact Nat.add_le_add_right hs _
    exact ih h (by omega) (by omega) hstep

/-- The total excess over the deletion floor bounds the count of nonoptimal deletions. -/
private theorem OMA.card_bad_deletions_le {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} {c : ℕ}
    (h : OMA.CoversFourSets U M)
    (hc : ∀ x ∈ U, c ≤ (OMA.avoidVertex M x).card) :
    (U.filter (fun x => c < (OMA.avoidVertex M x).card)).card + U.card * c ≤
      M.card * (U.card - 3) := by
  let f (x : α) := (OMA.avoidVertex M x).card - c
  let B := U.filter (fun x => c < (OMA.avoidVertex M x).card)
  have hB : B ⊆ U := Finset.filter_subset _ _
  have hle : B.card ≤ ∑ x ∈ U, f x := by
    calc
      B.card = ∑ x ∈ B, (1 : ℕ) := by simp
      _ ≤ ∑ x ∈ B, f x := by
        apply Finset.sum_le_sum
        intro x hx
        have := (Finset.mem_filter.mp hx).2
        dsimp [f]
        omega
      _ ≤ ∑ x ∈ U, f x := Finset.sum_le_sum_of_subset hB
  have hsum : (∑ x ∈ U, f x) + U.card * c = M.card * (U.card - 3) := by
    rw [← OMA.sum_card_avoidVertex h.1]
    have hconst : U.card * c = ∑ _x ∈ U, c := by simp
    rw [hconst, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x hx => Nat.sub_add_cancel (hc x hx)
  exact (Nat.add_le_add_right hle _).trans hsum.le

private theorem OMA.avoidPair_comm {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) (x y : α) :
    OMA.avoidVertex (OMA.avoidVertex M x) y =
      OMA.avoidVertex (OMA.avoidVertex M y) x := by
  ext e
  simp only [OMA.avoidVertex, Finset.filter_filter, Finset.mem_filter]
  exact and_congr_right (fun _ => and_comm)

private theorem OMA.exists_subset_avoiding_pairs {α : Type*} [DecidableEq α]
    (S : Finset α) (bad : α → Finset α) {k : ℕ}
    (hself : ∀ x ∈ S, x ∈ bad x)
    (hsym : ∀ x ∈ S, ∀ y ∈ S, y ∈ bad x ↔ x ∈ bad y)
    (hbad : ∀ x ∈ S, (bad x).card ≤ k) (m : ℕ)
    (hS : ∀ j < m, j * k < S.card) :
    ∃ T ⊆ S, T.card = m ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → y ∉ bad x := by
  induction m with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ m ih =>
    obtain ⟨T, hTS, hT, hgood⟩ := ih (fun j hj => hS j (by omega))
    have hcap : (T.biUnion bad).card ≤ m * k := by
      calc
        (T.biUnion bad).card ≤ ∑ x ∈ T, (bad x).card := Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ T, k := Finset.sum_le_sum (fun x hx => hbad x (hTS hx))
        _ = m * k := by simp [hT]
    have hnsub : ¬ S ⊆ T.biUnion bad :=
      fun h => (Nat.not_le_of_gt (hS m (by omega))) ((Finset.card_le_card h).trans hcap)
    obtain ⟨x, hx, hxf⟩ := Finset.not_subset.mp hnsub
    have hxt : x ∉ T :=
      fun ht => hxf (Finset.mem_biUnion.mpr ⟨x, ht, hself x hx⟩)
    have hxgood (y : α) (hy : y ∈ T) : x ∉ bad y :=
      fun hf => hxf (Finset.mem_biUnion.mpr ⟨y, hy, hf⟩)
    refine ⟨insert x T, Finset.insert_subset hx hTS,
      by rw [Finset.card_insert_of_notMem hxt, hT], ?_⟩
    intro y hy z hz hyz
    rcases Finset.mem_insert.mp hy with rfl | hyT
    · have hzT := (Finset.mem_insert.mp hz).resolve_left hyz.symm
      exact fun hf => hxgood z hzT ((hsym y hx z (hTS hzT)).mp hf)
    · rcases Finset.mem_insert.mp hz with rfl | hzT
      · exact hxgood y hyT
      · exact hgood y hyT z hzT hyz

private theorem OMA.avoid_three_inclusion_exclusion {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) (x y z : α) :
    M.card + (OMA.avoidVertex (OMA.avoidVertex M x) y).card +
        (OMA.avoidVertex (OMA.avoidVertex M x) z).card +
        (OMA.avoidVertex (OMA.avoidVertex M y) z).card =
      (OMA.avoidVertex M x).card + (OMA.avoidVertex M y).card + (OMA.avoidVertex M z).card +
        (OMA.avoidVertex (OMA.avoidVertex (OMA.avoidVertex M x) y) z).card +
        (M.filter fun e => x ∈ e ∧ y ∈ e ∧ z ∈ e).card := by
  have hcard : (∑ _e ∈ M, (1 : ℕ)) = M.card := by simp
  conv_lhs => lhs; lhs; lhs; rw [← hcard]
  simp only [OMA.avoidVertex, Finset.filter_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hx : x ∈ e <;> by_cases hy : y ∈ e <;> by_cases hz : z ∈ e <;>
    simp [hx, hy, hz]

/-- Simultaneous optimal deletions rule out equality in the rounded covering bound. -/
private theorem OMA.card_cover_ne_of_deletions {α : Type*} [DecidableEq α]
    {U : Finset α} {M : Finset (Finset α)} {n p a b c : ℕ}
    (h : OMA.CoversFourSets U M) (hU : U.card = n) (hp : M.card = p)
    (ha : ∀ (V : Finset α) (N : Finset (Finset α)), OMA.CoversFourSets V N → V.card = n - 1 → a ≤ N.card)
    (hb : ∀ (V : Finset α) (N : Finset (Finset α)), OMA.CoversFourSets V N → V.card = n - 2 → b ≤ N.card)
    (hc : ∀ (V : Finset α) (N : Finset (Finset α)), OMA.CoversFourSets V N → V.card = n - 3 → c ≤ N.card)
    (hspace : p * (n - 3) - n * a + 3 * (a * (n - 4) - (n - 1) * b + 1) < n)
    (hgap : p + 3 * b ≤ 3 * a + c) : False := by
  let S := U.filter (fun x => (OMA.avoidVertex M x).card = a)
  let k := a * (n - 4) - (n - 1) * b + 1
  let bad (x : α) := insert x ((U.erase x).filter
    (fun y => b < (OMA.avoidVertex (OMA.avoidVertex M x) y).card))
  have hav (x : α) (hx : x ∈ U) : a ≤ (OMA.avoidVertex M x).card :=
    ha _ _ (OMA.coversFourSets_erase h x) (by rw [Finset.card_erase_of_mem hx, hU])
  have hSS : S ⊆ U := Finset.filter_subset _ _
  have hSc : 3 * k < S.card := by
    have hcnt := OMA.card_bad_deletions_le h hav
    have heq : U \ S = U.filter (fun x => a < (OMA.avoidVertex M x).card) := by
      ext x
      simp only [S, Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro ⟨hx, hn⟩
        exact ⟨hx, lt_of_le_of_ne (hav x hx) (fun he => hn ⟨hx, he.symm⟩)⟩
      · rintro ⟨hx, hl⟩
        exact ⟨hx, fun he => (Nat.ne_of_gt hl) he.2⟩
    rw [← heq, Finset.card_sdiff_of_subset hSS, hp, hU] at hcnt
    change n - S.card + n * a ≤ p * (n - 3) at hcnt
    have hSk : p * (n - 3) - n * a + 3 * k < n := hspace
    omega
  have hdouble (x y : α) (hx : x ∈ U) (hy : y ∈ U.erase x) :
      b ≤ (OMA.avoidVertex (OMA.avoidVertex M x) y).card :=
    hb _ _ (OMA.coversFourSets_erase (OMA.coversFourSets_erase h x) y)
      (by rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx, hU]; omega)
  have hbad (x : α) (hx : x ∈ S) : (bad x).card ≤ k := by
    have ⟨hxU, hxa⟩ := Finset.mem_filter.mp hx
    have hcnt := OMA.card_bad_deletions_le (OMA.coversFourSets_erase h x) (hdouble x · hxU)
    rw [hxa, Finset.card_erase_of_mem hxU, hU, show n - 1 - 3 = n - 4 by omega] at hcnt
    dsimp [bad]
    rw [Finset.card_insert_of_notMem (by simp)]
    change _ + 1 ≤ a * (n - 4) - (n - 1) * b + 1
    omega
  have hsym (x : α) (hx : x ∈ S) (y : α) (hy : y ∈ S) : y ∈ bad x ↔ x ∈ bad y := by
    by_cases he : x = y
    · subst y; rfl
    · simp [bad, he, Ne.symm he, hSS hx, hSS hy, OMA.avoidPair_comm M x y]
  obtain ⟨T, hTS, hTc, hT⟩ :=
    OMA.exists_subset_avoiding_pairs S bad (by intro x hx; simp [bad]) hsym hbad 4
      (fun j hj => (Nat.mul_le_mul_right k (by omega : j ≤ 3)).trans_lt hSc)
  have hTU : T ⊆ U := hTS.trans hSS
  obtain ⟨e, he, heT⟩ := h.2 T (Finset.mem_powersetCard.mpr ⟨hTU, hTc⟩)
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp (h.1 e he).2
  have hxT : x ∈ T := heT (by simp)
  have hyT : y ∈ T := heT (by simp)
  have hzT : z ∈ T := heT (by simp)
  have eq₁ (v : α) (hv : v ∈ T) : (OMA.avoidVertex M v).card = a :=
    (Finset.mem_filter.mp (hTS hv)).2
  have eq₂ (v w : α) (hv : v ∈ T) (hw : w ∈ T) (hne : v ≠ w) :
      (OMA.avoidVertex (OMA.avoidVertex M v) w).card = b := by
    have hwer : w ∈ U.erase v := Finset.mem_erase.mpr ⟨hne.symm, hTU hw⟩
    apply le_antisymm _ (hdouble v w (hTU hv) hwer)
    exact Nat.le_of_not_gt (fun hl => hT v hv w hw hne
      (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hwer, hl⟩)))
  have hxyz : z ∈ (U.erase x).erase y :=
    Finset.mem_erase.mpr ⟨hyz.symm, Finset.mem_erase.mpr ⟨hxz.symm, hTU hzT⟩⟩
  have htriple := hc _ _
    (OMA.coversFourSets_erase (OMA.coversFourSets_erase (OMA.coversFourSets_erase h x) y) z)
    (by rw [Finset.card_erase_of_mem hxyz,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hTU hyT⟩),
      Finset.card_erase_of_mem (hTU hxT), hU]; omega)
  have hpos : 0 < (M.filter fun e => x ∈ e ∧ y ∈ e ∧ z ∈ e).card := by
    exact Finset.card_pos.mpr ⟨{x, y, z}, by simp [he]⟩
  have hsum := OMA.avoid_three_inclusion_exclusion M x y z
  rw [hp, eq₁ x hxT, eq₁ y hyT, eq₁ z hzT, eq₂ x y hxT hyT hxy,
    eq₂ x z hxT hzT hxz, eq₂ y z hyT hzT hyz] at hsum
  omega

/-- The rounded vertex-deletion bound of 5629 on 39 vertices cannot be attained. -/
theorem OMA.cliqueExtremalNumber_thirty_nine_le :
    Hypergraph.cliqueExtremalNumber 39 3 4 ≤ 5628 := by
  obtain ⟨M, hcover, hsum⟩ := OMA.exists_extremal_cover 39
  have hU : (Finset.univ : Finset (Fin 39)).card = 39 := by simp
  have hchoose : (39 : ℕ).choose 3 = 9139 := by decide
  rw [hchoose] at hsum
  have hfloor : 3510 ≤ M.card :=
    OMA.card_cover_ge_iter 29 hcover hU (n := 10) (c := 44) (by decide)
      (fun _ _ h hV => OMA.card_cover_ten h hV)
  by_contra! hlarge
  have hp : M.card = 3510 := by omega
  exact OMA.card_cover_ne_of_deletions (a := 3240) (b := 2984) (c := 2742) hcover hU hp
    (fun _ _ h hV => OMA.card_cover_ge_iter 28 h hV (n := 10) (c := 44) (by decide)
      (fun _ _ h' hV' => OMA.card_cover_ten h' hV'))
    (fun _ _ h hV => OMA.card_cover_ge_iter 27 h hV (n := 10) (c := 44) (by decide)
      (fun _ _ h' hV' => OMA.card_cover_ten h' hV'))
    (fun _ _ h hV => OMA.card_cover_ge_iter 26 h hV (n := 10) (c := 44) (by decide)
      (fun _ _ h' hV' => OMA.card_cover_ten h' hV'))
    (by decide) (by decide)

/-- Starting the deletion recurrence from the improved 39-vertex cap sharpens the density bound. -/
theorem OMA.turanDensity_le_of_thirty_nine (n : ℕ) (hn : 100 ≤ n) :
    OMA.turanDensity n ≤ 99451 / 161700 := by
  refine (OMA.turanDensity_antitone (by omega) hn).trans ?_
  have h54 : Hypergraph.cliqueExtremalNumber 54 3 4 ≤ 15264 :=
    OMA.cliqueExtremalNumber_le_knsIter 15 39 5628 (by decide) OMA.cliqueExtremalNumber_thirty_nine_le
  have h69 : Hypergraph.cliqueExtremalNumber 69 3 4 ≤ 32232 :=
    OMA.cliqueExtremalNumber_le_knsIter 15 54 15264 (by decide) h54
  have h84 : Hypergraph.cliqueExtremalNumber 84 3 4 ≤ 58608 :=
    OMA.cliqueExtremalNumber_le_knsIter 15 69 32232 (by decide) h69
  have h99 : Hypergraph.cliqueExtremalNumber 99 3 4 ≤ 96468 :=
    OMA.cliqueExtremalNumber_le_knsIter 15 84 58608 (by decide) h84
  have h100 : Hypergraph.cliqueExtremalNumber 100 3 4 ≤ 99451 :=
    OMA.cliqueExtremalNumber_le_knsIter 1 99 96468 (by decide) h99
  have hr : (Hypergraph.cliqueExtremalNumber 100 3 4 : ℝ) ≤ 99451 := by exact_mod_cast h100
  rw [OMA.turanDensity, show (100 : ℕ).choose 3 = 161700 by decide, Nat.cast_ofNat]
  linarith

/-- Existence of the Turan density limit pi(K_4^3) in [5/9, 99481/161700]. -/
theorem OMA.exists_turanDensity_limit :
    ∃ L : ℝ, 5 / 9 ≤ L ∧ L ≤ 99481 / 161700 ∧ Tendsto OMA.turanDensity atTop (𝓝 L) := by
  let g : ℕ → ℝ := fun k => OMA.turanDensity (k + 3)
  have hg_anti : Antitone g := fun a b hab =>
    OMA.turanDensity_antitone (by omega) (by omega)
  have hg_bdd : BddBelow (Set.range g) := by
    refine ⟨5 / 9, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact OMA.five_ninths_le_turanDensity (k + 3) (by omega)
  have htend : Tendsto OMA.turanDensity atTop (𝓝 (⨅ k, g k)) :=
    (tendsto_add_atTop_iff_nat 3).mp (tendsto_atTop_ciInf hg_anti hg_bdd)
  refine ⟨⨅ k, g k, ?_, ?_, htend⟩
  · exact le_ciInf (fun k => OMA.five_ninths_le_turanDensity (k + 3) (by omega))
  · exact le_of_tendsto htend
      ((eventually_ge_atTop 100).mono (fun n hn => OMA.turanDensity_le_of_ten n hn))

private abbrev OMA.BlowupChoices {n : ℕ} (H : Finset (Finset (Fin n))) (m : ℕ) :=
  (e : ↥H) × (↥e.val → Fin m)

private def OMA.blowupProjection {n m : ℕ} (x : Fin (n * m)) : Fin n :=
  (finProdFinEquiv.symm x).1

private def OMA.blowupEdge {n m : ℕ} {H : Finset (Finset (Fin n))}
    (c : OMA.BlowupChoices H m) : Finset (Fin (n * m)) :=
  Finset.univ.map ⟨fun x => finProdFinEquiv (x.val, c.2 x), by
    intro x y h
    exact Subtype.ext (congrArg Prod.fst (finProdFinEquiv.injective h))⟩

private theorem OMA.image_blowupEdge {n m : ℕ} {H : Finset (Finset (Fin n))}
    (c : OMA.BlowupChoices H m) : (OMA.blowupEdge c).image OMA.blowupProjection = c.1.val := by
  ext v
  simp only [Finset.mem_image, OMA.blowupEdge, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, hv⟩
    change OMA.blowupProjection (finProdFinEquiv (x.val, c.2 x)) = v at hv
    have he : (x : Fin n) = v := by simpa [OMA.blowupProjection] using hv
    exact he ▸ x.property
  · intro hv
    let x : ↥c.1.val := ⟨v, hv⟩
    exact ⟨finProdFinEquiv (v, c.2 x), ⟨x, rfl⟩, by simp [OMA.blowupProjection]⟩

private theorem OMA.blowupEdge_injective {n m : ℕ} {H : Finset (Finset (Fin n))} :
    Function.Injective (@OMA.blowupEdge n m H) := by
  rintro ⟨e, f⟩ ⟨e', g⟩ h
  have he : e = e' := by
    apply Subtype.ext
    simpa only [OMA.image_blowupEdge] using congrArg (fun s => s.image OMA.blowupProjection) h
  subst e'
  congr 1
  funext x
  have hx : finProdFinEquiv (x.val, f x) ∈ OMA.blowupEdge (m := m) ⟨e, g⟩ := by
    rw [← h]
    exact Finset.mem_map.mpr ⟨x, Finset.mem_univ _, rfl⟩
  obtain ⟨y, -, hy⟩ := Finset.mem_map.mp hx
  change finProdFinEquiv (y.val, g y) = finProdFinEquiv (x.val, f x) at hy
  have hp := finProdFinEquiv.injective hy
  have hyx : y = x := Subtype.ext (congrArg Prod.fst hp)
  subst y
  exact (congrArg Prod.snd hp).symm

private theorem OMA.cliqueFree_of_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) {H : Finset (Finset β)} (hH : ∀ e ∈ H, e.card = 3)
    (hfree : ¬ H.ContainsCompleteHypergraph 3 4)
    {G : Finset (Finset α)} (hG : ∀ e ∈ G, e.image f ∈ H) :
    ¬ G.ContainsCompleteHypergraph 3 4 := by
  rintro ⟨s, hs, hsub⟩
  have hinj : Set.InjOn f (s : Set (α)) := by
    intro a ha b hb hab
    by_contra hne
    have hp : ({a, b} : Finset (α)) ⊆ s :=
      Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
    have h2 : ({a, b} : Finset (α)).card ≤ 3 := by
      rw [Finset.card_pair hne]
      decide
    obtain ⟨e, he, hes, hcard⟩ := Finset.exists_subsuperset_card_eq hp h2 (by omega)
    have heG := hsub (Finset.mem_powersetCard.mpr ⟨hes, hcard⟩)
    have heinj := Finset.injOn_of_card_image_eq ((hH _ (hG _ heG)).trans hcard.symm)
    exact hne (heinj (he (by simp)) (he (by simp)) hab)
  apply hfree
  refine ⟨s.image f, (Finset.card_image_of_injOn hinj).trans hs, ?_⟩
  intro e he
  obtain ⟨hes, her⟩ := Finset.mem_powersetCard.mp he
  let t := s.filter fun x => f x ∈ e
  have hts : t ⊆ s := Finset.filter_subset _ _
  have himage : t.image f = e := by
    ext v
    constructor
    · rintro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hx).2
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hes hv)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hv⟩, rfl⟩
  have hti := Set.InjOn.mono (Finset.coe_subset.mpr hts) hinj
  have htc : t.card = 3 := by
    rw [← Finset.card_image_of_injOn hti, himage, her]
  have htG := hsub (Finset.mem_powersetCard.mpr ⟨hts, htc⟩)
  exact himage ▸ hG _ htG

private theorem OMA.cliqueFree_of_image {n m : ℕ}
    {H : Finset (Finset (Fin n))} (hH : ∀ e ∈ H, e.card = 3)
    (hfree : ¬ H.ContainsCompleteHypergraph 3 4)
    {G : Finset (Finset (Fin (n * m)))}
    (hG : ∀ e ∈ G, e.image OMA.blowupProjection ∈ H) :
    ¬ G.ContainsCompleteHypergraph 3 4 :=
  OMA.cliqueFree_of_map OMA.blowupProjection hH hfree hG

/-- Balanced m-fold blow-up gives ex_3(n, K_4^3) * m^3 <= ex_3(n * m, K_4^3). -/
theorem OMA.extremal_blowup_lower (n m : ℕ) :
    Hypergraph.cliqueExtremalNumber n 3 4 * m ^ 3 ≤
      Hypergraph.cliqueExtremalNumber (n * m) 3 4 := by
  classical
  obtain ⟨H, hunif, hfree, hcard⟩ := OMA.exists_extremal_hypergraph n
  let G := Finset.univ.image (@OMA.blowupEdge n m H)
  have hGc : G.card = H.card * m ^ 3 := by
    change (Finset.univ.image (@OMA.blowupEdge n m H)).card = _
    rw [Finset.card_image_of_injective _ OMA.blowupEdge_injective, Finset.card_univ, Fintype.card_sigma]
    have hc (e : ↥H) : Fintype.card (↥e.val → Fin m) = m ^ 3 := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hunif e.val e.property]
    simp [hc]
  have hproj : ∀ e ∈ G, e.image OMA.blowupProjection ∈ H := by
    intro e he
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp he
    rw [OMA.image_blowupEdge]
    exact c.1.property
  have hGunif : ∀ e ∈ G, e.card = 3 := by
    intro e he
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp he
    simp [OMA.blowupEdge, hunif _ c.1.property]
  rw [← hcard, ← hGc]
  exact OMA.cliqueExtremalNumber_ge_card G hGunif (OMA.cliqueFree_of_image hunif hfree hproj)

private theorem OMA.choose_three_scaled_tendsto :
    Tendsto (fun n : ℕ => (6 : ℝ) * (n.choose 3 : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) * (1 - 2 * (n : ℝ)⁻¹)) atTop (𝓝 ((1 - 0) * (1 - 2 * 0))) :=
    ((tendsto_const_nhds.sub hinv).mul (tendsto_const_nhds.sub (hinv.const_mul 2)))
  rw [show ((1 - 0) * (1 - 2 * 0) : ℝ) = 1 by norm_num] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h6 : (6 : ℝ) * (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    have hnat := OMA.six_mul_choose_three n
    have hcast : (6 : ℝ) * (n.choose 3 : ℝ) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n)] at hcast
    simpa using hcast
  rw [h6]
  field_simp

/-- The normalized extremal count 6 * ex_3(n, K_4^3) / n^3. -/
noncomputable def OMA.scaledExtremal (n : ℕ) : ℝ :=
  6 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) / (n : ℝ) ^ 3

theorem OMA.scaledExtremal_tendsto {d : ℝ} (h : Tendsto OMA.turanDensity atTop (𝓝 d)) :
    Tendsto OMA.scaledExtremal atTop (𝓝 d) := by
  have hmul := h.mul OMA.choose_three_scaled_tendsto
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hc : (n.choose 3 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  unfold OMA.turanDensity OMA.scaledExtremal
  field_simp

theorem OMA.scaledExtremal_le_blowup {n m : ℕ} (hm : 0 < m) :
    OMA.scaledExtremal n ≤ OMA.scaledExtremal (n * m) := by
  have hmz : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) * (m : ℝ) ^ 3 ≤
      (Hypergraph.cliqueExtremalNumber (n * m) 3 4 : ℝ) := by
    exact_mod_cast OMA.extremal_blowup_lower n m
  unfold OMA.scaledExtremal
  rw [Nat.cast_mul, mul_pow, ← mul_div_mul_right _ _ (pow_ne_zero 3 hmz), mul_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcast (by positivity)) (by positivity)

/-- Blow-up characterization: the Turan density limit is <= C iff 6 * ex_3(n, K_4^3) / n^3 <= C for all n > 0. -/
theorem OMA.density_le_iff_finite {d C : ℝ} (h : Tendsto OMA.turanDensity atTop (𝓝 d)) :
    d ≤ C ↔ ∀ n : ℕ, 0 < n → OMA.scaledExtremal n ≤ C := by
  have hscale := OMA.scaledExtremal_tendsto h
  constructor
  · intro hd n hn
    have hseq : Tendsto (fun m : ℕ => n * m) atTop atTop :=
      tendsto_atTop_mono (fun m => show m ≤ n * m by
        simpa using Nat.mul_le_mul_right m (show 1 ≤ n from hn)) tendsto_id
    refine (le_of_tendsto_of_tendsto tendsto_const_nhds (hscale.comp hseq) ?_).trans hd
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact OMA.scaledExtremal_le_blowup hm
  · intro hC
    refine le_of_tendsto_of_tendsto hscale tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hC n hn

/-- Finite cubic equivalence for Turan's tetrahedron conjecture:
pi(K_4^3) = 5/9 iff 54 * ex_3(n, K_4^3) <= 5 * n^3 for every n > 0. -/
theorem OMA.tetrahedron_density_eq_iff_finite {d : ℝ} (h : Tendsto OMA.turanDensity atTop (𝓝 d)) :
    d = 5 / 9 ↔ ∀ n : ℕ, 0 < n → 54 * Hypergraph.cliqueExtremalNumber n 3 4 ≤ 5 * n ^ 3 := by
  have hlo : 5 / 9 ≤ d := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds h ?_
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact OMA.five_ninths_le_turanDensity n hn
  have hcd : d ≤ 5 / 9 ↔ d = 5 / 9 := ⟨fun hle => le_antisymm hle hlo, fun he => he.le⟩
  rw [← hcd, OMA.density_le_iff_finite h]
  constructor
  · intro hbound n hn
    have hp : (0 : ℝ) < (n : ℝ) ^ 3 := pow_pos (by exact_mod_cast hn) _
    have hb := (div_le_iff₀ hp).mp (hbound n hn)
    have hr : 54 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) ≤ 5 * (n : ℝ) ^ 3 := by linarith
    exact_mod_cast hr
  · intro hbound n hn
    have hp : (0 : ℝ) < (n : ℝ) ^ 3 := pow_pos (by exact_mod_cast hn) _
    apply (div_le_iff₀ hp).mpr
    have hb : 54 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) ≤ 5 * (n : ℝ) ^ 3 := by
      exact_mod_cast hbound n hn
    linarith

/-- The finite cubic inequality holds on at most 29 vertices. -/
theorem OMA.tetrahedron_cubic_le_twenty_nine (n : ℕ) (hn : n ≤ 29) :
    54 * Hypergraph.cliqueExtremalNumber n 3 4 ≤ 5 * n ^ 3 := by
  by_cases hsmall : n < 10
  · obtain ⟨M, _, he⟩ := OMA.exists_extremal_cover n
    have hc : Hypergraph.cliqueExtremalNumber n 3 4 ≤ n.choose 3 := by omega
    interval_cases n
    all_goals first
      | exact (Nat.mul_le_mul_left 54 hc).trans (by decide)
      | simp only [OMA.cliqueExtremalNumber_seven,
          OMA.cliqueExtremalNumber_eight, OMA.cliqueExtremalNumber_nine]
        decide
  · have h10 : 10 ≤ n := by omega
    have he := OMA.cliqueExtremalNumber_le_knsIter (n - 10) 10 76
      (by decide) OMA.cliqueExtremalNumber_ten_le
    rw [Nat.add_sub_of_le h10] at he
    refine (Nat.mul_le_mul_left 54 he).trans ?_
    interval_cases n <;> decide

/-- The ten rooted triples on five labels, followed by their two complementary labels. -/
private def OMA.flagSlots : Fin 10 → Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4], ![0, 1, 3, 2, 4], ![0, 1, 4, 2, 3],
    ![0, 2, 3, 1, 4], ![0, 2, 4, 1, 3], ![0, 3, 4, 1, 2],
    ![1, 2, 3, 0, 4], ![1, 2, 4, 0, 3], ![1, 3, 4, 0, 2],
    ![2, 3, 4, 0, 1]]

/-- Extending one of the three pairs in a rooted triple by a complementary label gives these indices. -/
private def OMA.flagIndices : Fin 10 → Fin 2 → Fin 3 → Fin 10 :=
  ![![![1, 3, 6], ![2, 4, 7]],
    ![![0, 3, 6], ![2, 5, 8]],
    ![![0, 4, 7], ![1, 5, 8]],
    ![![0, 1, 6], ![4, 5, 9]],
    ![![0, 2, 7], ![3, 5, 9]],
    ![![1, 2, 8], ![3, 4, 9]],
    ![![0, 1, 3], ![7, 8, 9]],
    ![![0, 2, 4], ![6, 8, 9]],
    ![![1, 2, 5], ![6, 7, 9]],
    ![![3, 4, 5], ![6, 7, 8]]]

private def OMA.flagTetrahedra : Fin 5 → Fin 4 → Fin 10 :=
  ![![6, 7, 8, 9], ![3, 4, 5, 9], ![1, 2, 5, 8], ![0, 2, 4, 7], ![0, 1, 3, 6]]

private def OMA.flagPattern (p : Fin 3 → Bool) : Fin 8 :=
  Fin.ofNat 8 ((if p 0 then 1 else 0) + (if p 1 then 2 else 0) + (if p 2 then 4 else 0))

/-- Integer coefficients for the five products in the local sum-of-squares certificate. -/
private def OMA.flagCoefficients (edge : Bool) : Fin 5 → Fin 8 → ℤ :=
  if edge then
    ![![137, -15, -15, 4, -15, 4, 4, 0],
      ![0, 140, -70, 46, -70, 46, -92, 0],
      ![0, -70, 140, 46, -70, -92, 46, 0],
      ![0, -70, -70, -92, 140, 46, 46, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]]
  else
    ![![-115, -138, -138, 96, -138, 96, 96, 24],
      ![-98, 40, 40, -108, 40, -108, -108, 192],
      ![0, 82, -41, 16, -41, 16, -32, 0],
      ![0, -41, 82, 16, -41, -32, 16, 0],
      ![0, -41, -41, -32, 82, 16, 16, 0]]

private def OMA.flagScore (edge : Bool) (a b : Fin 8) : ℤ :=
  (if edge then 40000 else 0) +
    ∑ k : Fin 5, OMA.flagCoefficients edge k a * OMA.flagCoefficients edge k b

private def OMA.flagCertificate (E : Fin 10 → Bool) : Prop :=
  (∀ q : Fin 5, ∃ j : Fin 4, E (OMA.flagTetrahedra q j) = false) →
    ∑ j : Fin 10, OMA.flagScore (E j)
      (OMA.flagPattern (fun k => E (OMA.flagIndices j 0 k)))
      (OMA.flagPattern (fun k => E (OMA.flagIndices j 1 k))) ≤ 230000

/-- A dot-product table speeds up the finite verification. Its entries are checked below. -/
private def OMA.flagDot (edge : Bool) : Fin 8 → Fin 8 → ℤ :=
  if edge then
    ![![18769, -2055, -2055, 548, -2055, 548, 548, 0],
      ![-2055, 29625, -14475, 9600, -14475, 9600, -19380, 0],
      ![-2055, -14475, 29625, 9600, -14475, -19380, 9600, 0],
      ![548, 9600, 9600, 12712, -19380, -6332, -6332, 0],
      ![-2055, -14475, -14475, -19380, 29625, 9600, 9600, 0],
      ![548, 9600, -19380, -6332, 9600, 12712, -6332, 0],
      ![548, -19380, 9600, -6332, 9600, -6332, 12712, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]]
  else
    ![![22829, 11950, 11950, -456, 11950, -456, -456, -21576],
      ![11950, 30730, 15601, -15600, 15601, -15600, -21504, 4368],
      ![11950, 15601, 30730, -15600, 15601, -21504, -15600, 4368],
      ![-456, -15600, -15600, 22416, -21504, 20112, 20112, -18432],
      ![11950, 15601, 15601, -21504, 30730, -15600, -15600, 4368],
      ![-456, -15600, -21504, 20112, -15600, 22416, 20112, -18432],
      ![-456, -21504, -15600, 20112, -15600, 20112, 22416, -18432],
      ![-21576, 4368, 4368, -18432, 4368, -18432, -18432, 37440]]

private def OMA.flagScoreFast (edge : Bool) (a b : Fin 8) : ℤ :=
  (if edge then 40000 else 0) + OMA.flagDot edge a b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem OMA.flagScoreFast_eq :
    ∀ t a b, OMA.flagScoreFast t a b = OMA.flagScore t a b := by
  decide +kernel

private def OMA.flagCheck (m : ℕ) : Prop :=
  (∀ q : Fin 5, ∃ j : Fin 4, m.testBit (OMA.flagTetrahedra q j) = false) →
    ∑ j : Fin 10, OMA.flagScoreFast (m.testBit j)
      (OMA.flagPattern (fun k => m.testBit (OMA.flagIndices j 0 k)))
      (OMA.flagPattern (fun k => m.testBit (OMA.flagIndices j 1 k))) ≤ 230000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Check the 1024 assignments of the ten possible edges in blocks of 32. -/
private theorem OMA.flagCheck_chunks (hi : Fin 32) : ∀ lo : Fin 32,
    OMA.flagCheck (32 * hi.val + lo.val) := by
  unfold OMA.flagCheck
  fin_cases hi <;> decide +kernel

private theorem OMA.flagCertificate_valid : ∀ E, OMA.flagCertificate E := by
  intro E
  let b := BitVec.ofBoolListLE (List.ofFn E)
  have hbn : b.toNat < 1024 := by
    simpa [b, List.length_ofFn] using b.isLt
  have hbit (i : Fin 10) : b.toNat.testBit i = E i := by
    change b.getLsbD i = E i
    dsimp [b]
    rw [BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  let hi : Fin 32 := ⟨b.toNat / 32, by omega⟩
  let lo : Fin 32 := ⟨b.toNat % 32, by omega⟩
  have heq : 32 * hi.val + lo.val = b.toNat := by
    dsimp [hi, lo]
    omega
  have hc := OMA.flagCheck_chunks hi
  have hs := hc lo
  rw [heq] at hs
  unfold OMA.flagCheck at hs
  simpa only [OMA.flagCertificate, hbit, OMA.flagScoreFast_eq] using hs
private def OMA.flagPairs : Fin 3 → Fin 2 → Fin 3 :=
  ![![0, 1], ![0, 2], ![1, 2]]

private def OMA.flagRoot (i : Fin 10) : Finset (Fin 5) :=
  {OMA.flagSlots i 0, OMA.flagSlots i 1, OMA.flagSlots i 2}

private theorem OMA.flag_indices_correct :
    ∀ (i : Fin 10) (w : Fin 2) (k : Fin 3),
      OMA.flagRoot (OMA.flagIndices i w k) =
        {OMA.flagSlots i (Fin.castAdd 2 (OMA.flagPairs k 0)),
         OMA.flagSlots i (Fin.castAdd 2 (OMA.flagPairs k 1)),
         OMA.flagSlots i (Fin.natAdd 3 w)} := by
  decide

private theorem OMA.flag_tetrahedra_correct :
    ∀ q : Fin 5, ((Finset.univ.erase q).powersetCard 3) =
      (Finset.univ : Finset (Fin 4)).image (fun j => OMA.flagRoot (OMA.flagTetrahedra q j)) := by
  decide

private theorem OMA.flag_slots_bijective :
    ∀ i : Fin 10, Function.Bijective (OMA.flagSlots i) := by
  have h : ∀ (i : Fin 10) (a b : Fin 5), OMA.flagSlots i a = OMA.flagSlots i b → a = b := by
    decide
  intro i
  exact ⟨h i, Finite.surjective_of_injective (h i)⟩

private def OMA.flagEdge {α : Type*} [DecidableEq α] (H : Finset (Finset α))
    (a b c : α) : Bool := decide (({a, b, c} : Finset α) ∈ H)

private def OMA.flagMask {α : Type*} [DecidableEq α] (H : Finset (Finset α))
    (r : Fin 3 → α) (x : α) : Fin 8 :=
  OMA.flagPattern (fun k => OMA.flagEdge H (r (OMA.flagPairs k 0)) (r (OMA.flagPairs k 1)) x)

private def OMA.flagTerm {α : Type*} [DecidableEq α] (H : Finset (Finset α))
    (v : Fin 5 → α) : ℤ :=
  let r := v ∘ Fin.castAdd 2
  OMA.flagScore (OMA.flagEdge H (r 0) (r 1) (r 2))
    (OMA.flagMask H r (v (Fin.natAdd 3 (0 : Fin 2)))) (OMA.flagMask H r (v (Fin.natAdd 3 (1 : Fin 2))))

private theorem OMA.flagScore_local {n : ℕ} (H : Finset (Finset (Fin n)))
    (hunif : ∀ e ∈ H, e.card = 3) (hfree : ¬ H.ContainsCompleteHypergraph 3 4)
    (v : Fin 5 → Fin n) :
    ∑ i : Fin 10, OMA.flagTerm H (v ∘ OMA.flagSlots i) ≤ 230000 := by
  let G := ((Finset.univ : Finset (Fin 5)).powersetCard 3).filter (fun e => e.image v ∈ H)
  have hgfree : ¬ G.ContainsCompleteHypergraph 3 4 :=
    OMA.cliqueFree_of_map v hunif hfree (fun e he => (Finset.mem_filter.mp he).2)
  let E (i : Fin 10) : Bool := decide ((OMA.flagRoot i).image v ∈ H)
  have hE (q : Fin 5) : ∃ j : Fin 4, E (OMA.flagTetrahedra q j) = false := by
    by_contra! hh
    apply hgfree
    refine ⟨Finset.univ.erase q, by simp, ?_⟩
    intro e he
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp he).2⟩
    · rw [OMA.flag_tetrahedra_correct] at he
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
      have hj : E (OMA.flagTetrahedra q j) = true := by
        cases heq : E (OMA.flagTetrahedra q j)
        · exact (hh j heq).elim
        · rfl
      exact of_decide_eq_true hj
  have hs := OMA.flagCertificate_valid E hE
  refine le_trans (le_of_eq (Finset.sum_congr rfl ?_)) hs
  intro i _
  let r := (v ∘ OMA.flagSlots i) ∘ Fin.castAdd 2
  have hroot : OMA.flagEdge H (r 0) (r 1) (r 2) = E i := by
    simp [r, E, OMA.flagEdge, OMA.flagRoot, Function.comp_def]
  have hmask (w : Fin 2) :
      OMA.flagMask H r ((v ∘ OMA.flagSlots i) (Fin.natAdd 3 w)) =
        OMA.flagPattern (fun k => E (OMA.flagIndices i w k)) := by
    unfold OMA.flagMask
    apply congrArg OMA.flagPattern
    funext k
    unfold E
    rw [OMA.flag_indices_correct]
    simp [r, OMA.flagEdge, Function.comp_def]
  change OMA.flagScore (OMA.flagEdge H (r 0) (r 1) (r 2)) _ _ = _
  rw [hroot, hmask, hmask]

private theorem OMA.flagScore_sum {n : ℕ} (H : Finset (Finset (Fin n)))
    (hunif : ∀ e ∈ H, e.card = 3) (hfree : ¬ H.ContainsCompleteHypergraph 3 4) :
    10 * (∑ v : Fin 5 → Fin n, OMA.flagTerm H v) ≤ 230000 * (n : ℤ) ^ 5 := by
  calc
    _ = ∑ _ : Fin 10, ∑ v : Fin 5 → Fin n, OMA.flagTerm H v := by simp
    _ = ∑ i : Fin 10, ∑ v : Fin 5 → Fin n, OMA.flagTerm H (v ∘ OMA.flagSlots i) := by
      apply Finset.sum_congr rfl
      intro i _
      let e := Equiv.ofBijective (OMA.flagSlots i) (OMA.flag_slots_bijective i)
      exact ((Equiv.piCongrLeft' (fun _ : Fin 5 => Fin n) e.symm).sum_comp (OMA.flagTerm H)).symm
    _ = ∑ v : Fin 5 → Fin n, ∑ i : Fin 10, OMA.flagTerm H (v ∘ OMA.flagSlots i) :=
      Finset.sum_comm
    _ ≤ ∑ _ : Fin 5 → Fin n, (230000 : ℤ) :=
      Finset.sum_le_sum (fun v _ => OMA.flagScore_local H hunif hfree v)
    _ = _ := by simp [mul_comm]

private theorem OMA.sum_flagScore_nonnegative {α : Type*} [Fintype α] (t : Bool)
    (p : α → Fin 8) :
    (Fintype.card α : ℤ) ^ 2 * (if t then 40000 else 0) ≤
      ∑ x : α, ∑ y : α, OMA.flagScore t (p x) (p y) := by
  let f (k : Fin 5) (x : α) := OMA.flagCoefficients t k (p x)
  have hs : ∑ x : α, ∑ y : α, ∑ k : Fin 5, f k x * f k y =
      ∑ k : Fin 5, (∑ x : α, f k x) ^ 2 := by
    calc
      _ = ∑ x : α, ∑ k : Fin 5, ∑ y : α, f k x * f k y := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
      _ = ∑ k : Fin 5, ∑ x : α, ∑ y : α, f k x * f k y := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_two, Finset.sum_mul_sum]
  unfold OMA.flagScore
  simp only [Finset.sum_add_distrib]
  change _ ≤ (∑ _x : α, ∑ _y : α, (if t then (40000 : ℤ) else 0)) +
    ∑ x : α, ∑ y : α, ∑ k : Fin 5, f k x * f k y
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, ← pow_two]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => sq_nonneg _))

private theorem OMA.flagTerm_sum_lower {n : ℕ} (H : Finset (Finset (Fin n))) :
    (n : ℤ) ^ 2 * (∑ r : Fin 3 → Fin n,
      if OMA.flagEdge H (r 0) (r 1) (r 2) then (40000 : ℤ) else 0) ≤
      ∑ v : Fin 5 → Fin n, OMA.flagTerm H v := by
  rw [← (Fin.appendEquiv (α := Fin n) 3 2).sum_comp (OMA.flagTerm H),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  rw [← (piFinTwoEquiv (fun _ : Fin 2 => Fin n)).symm.sum_comp
    (fun s => OMA.flagTerm H (Fin.appendEquiv 3 2 (r, s))), Fintype.sum_prod_type]
  have happ (s : Fin 2 → Fin n) :
      OMA.flagTerm H (Fin.appendEquiv 3 2 (r, s)) =
        OMA.flagScore (OMA.flagEdge H (r 0) (r 1) (r 2))
          (OMA.flagMask H r (s 0)) (OMA.flagMask H r (s 1)) := by
    have hr : (Fin.append r s) ∘ Fin.castAdd 2 = r := by
      funext i
      simp
    change OMA.flagTerm H (Fin.append r s) = _
    simp only [OMA.flagTerm, hr, Fin.append_right]
  simpa [happ, piFinTwoEquiv] using
    OMA.sum_flagScore_nonnegative (OMA.flagEdge H (r 0) (r 1) (r 2)) (OMA.flagMask H r)

private theorem OMA.card_ordered_edges {n : ℕ} (H : Finset (Finset (Fin n)))
    (hunif : ∀ e ∈ H, e.card = 3) :
    6 * H.card ≤ (Finset.univ.filter (fun r : Fin 3 → Fin n =>
      ({r 0, r 1, r 2} : Finset (Fin n)) ∈ H)).card := by
  classical
  let S := Finset.univ.filter (fun r : Fin 3 → Fin n =>
    ({r 0, r 1, r 2} : Finset (Fin n)) ∈ H)
  let base (e : ↥H) : Fin 3 ≃ ↥e.val := (e.val.equivFinOfCardEq (hunif e e.property)).symm
  let f (a : ↥H × Equiv.Perm (Fin 3)) (i : Fin 3) : Fin n := base a.1 (a.2 i)
  have hf (a : ↥H × Equiv.Perm (Fin 3)) :
      ({f a 0, f a 1, f a 2} : Finset (Fin n)) = a.1.val := by
    ext x
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl) <;> exact (base a.1 (a.2 _)).property
    · intro hx
      obtain ⟨i, hi⟩ := ((a.2.trans (base a.1)).surjective) ⟨x, hx⟩
      have hxi : f a i = x := congrArg Subtype.val hi
      rw [← hxi]
      fin_cases i <;> simp
  let g (a : ↥H × Equiv.Perm (Fin 3)) : ↥S :=
    ⟨f a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hf]; exact a.1.property⟩⟩
  have hg : Function.Injective g := by
    rintro ⟨e, p⟩ ⟨e', p'⟩ h
    have hfe : f (e, p) = f (e', p') := congrArg Subtype.val h
    have he : e = e' := Subtype.ext ((hf (e, p)).symm.trans (hfe ▸ hf (e', p')))
    subst e'
    refine Prod.ext rfl (Equiv.ext ?_)
    intro i
    exact (base e).injective (Subtype.ext (congrFun hfe i))
  have h := Fintype.card_le_of_injective g hg
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_perm, Fintype.card_fin, Fintype.card_coe] at h
  change H.card * 6 ≤ S.card at h
  simpa only [Nat.mul_comm] using h

/-- A five-vertex sum-of-squares certificate gives an exact finite bound on the scaled density. -/
theorem OMA.tetrahedron_cubic_upper_flag (n : ℕ) :
    240 * Hypergraph.cliqueExtremalNumber n 3 4 ≤ 23 * n ^ 3 := by
  obtain ⟨H, hunif, hfree, hcard⟩ := OMA.exists_extremal_hypergraph n
  have hhi := OMA.flagScore_sum H hunif hfree
  have hlo := OMA.flagTerm_sum_lower H
  have hc : (∑ r : Fin 3 → Fin n, if OMA.flagEdge H (r 0) (r 1) (r 2) then (40000 : ℤ) else 0) =
      ((Finset.univ.filter (fun r : Fin 3 → Fin n =>
        ({r 0, r 1, r 2} : Finset (Fin n)) ∈ H)).card : ℤ) * 40000 := by
    simp [OMA.flagEdge, ← Finset.sum_filter]
  rw [hc] at hlo
  have hcount := OMA.card_ordered_edges H hunif
  have hcountZ : (6 : ℤ) * H.card ≤
      ((Finset.univ.filter (fun r : Fin 3 → Fin n =>
        ({r 0, r 1, r 2} : Finset (Fin n)) ∈ H)).card : ℤ) := by exact_mod_cast hcount
  have hpos : (0 : ℤ) ≤ (n : ℤ) ^ 2 := sq_nonneg _
  have hmix := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcountZ
    (by decide : (0 : ℤ) ≤ 40000)) hpos
  have hsum := mul_le_mul_of_nonneg_left (hmix.trans hlo) (by decide : (0 : ℤ) ≤ 10)
  have hscaled : (n : ℤ) ^ 2 * (240 * (H.card : ℤ)) ≤ (n : ℤ) ^ 2 * (23 * (n : ℤ) ^ 3) := by
    nlinarith only [hsum.trans hhi]
  by_cases hn : n = 0
  · have hH : H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hmax := Finset.card_le_univ e
      rw [hunif e he, Fintype.card_fin, hn] at hmax
      omega
    simp [← hcard, hH]
  · have hnZ : (0 : ℤ) < (n : ℤ) := by omega
    have hfinal := (mul_le_mul_iff_of_pos_left (pow_pos hnZ 2)).mp hscaled
    rw [hcard] at hfinal
    exact_mod_cast hfinal

theorem OMA.tetrahedron_density_le_flag {d : ℝ} (hd : Tendsto OMA.turanDensity atTop (𝓝 d)) :
    d ≤ 23 / 40 := by
  apply (OMA.density_le_iff_finite hd).mpr
  intro n hn
  have h := OMA.tetrahedron_cubic_upper_flag n
  have hR : 240 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) ≤ 23 * (n : ℝ) ^ 3 := by
    exact_mod_cast h
  rw [OMA.scaledExtremal, div_le_iff₀ (pow_pos (by exact_mod_cast hn : (0 : ℝ) < n) _)]
  nlinarith only [hR]

/-- Open upper bound half of Turan's tetrahedron conjecture (OPEN since 1941):
by KNS monotonicity, it suffices to find for each eps > 0 some n >= 3 with density <= 5/9 + eps,
or equivalently to prove 54 * ex_3(n, K_4^3) <= 5 * n^3 for all n > 0. -/
theorem OMA.turan_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 3 ≤ n ∧ OMA.turanDensity n ≤ 5 / 9 + ε := by
  intro ε hε
  by_cases hgap : (7 : ℝ) / 360 < ε
  · obtain ⟨d, _, _, hd⟩ := OMA.exists_turanDensity_limit
    have hbound := OMA.tetrahedron_density_le_flag hd
    have hlt : d < 5 / 9 + ε := by linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hd.eventually (gt_mem_nhds hlt))
    exact ⟨max 3 N, le_max_left _ _, (hN _ (le_max_right _ _)).le⟩
  · have hεle : ε ≤ 7 / 360 := le_of_not_gt hgap
    sorry

theorem OMA.solution : Erdos500.erdos_500.variants.asymptotic.answer = OMA.answer → type_of% @Erdos500.erdos_500.variants.asymptotic := by
  intro h
  rw [h]
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
