import FormalConjectures.ErdosProblems.«161»

-- Problem: Erdős Problem 161 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/161.lean:62 (declaration Erdos161.erdos_161.parts.ii)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Density comparisons for balanced coloring thresholds. -/

open Filter Asymptotics Finset
open scoped BigOperators Function

private def HasBalancedColoring (n t : ℕ) (α : ℝ) (m : ℕ) : Prop :=
  ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
      0 < count ∧ α * (X.card.choose t : ℝ) ≤ (count : ℝ)

private lemma threshold_feasible (n t : ℕ) (α : ℝ) :
    HasBalancedColoring n t α (Hypergraph.balancedColoringThreshold n t α) := by
  change sInf {m | HasBalancedColoring n t α m} ∈ {m | HasBalancedColoring n t α m}
  apply Nat.sInf_mem
  refine ⟨n + 1, fun _ ↦ false, fun X hX ↦ ?_⟩
  have hcard : X.card ≤ n := by simpa using Finset.card_le_univ X
  omega

private lemma threshold_le_of_feasible {n t m : ℕ} {α : ℝ}
    (h : HasBalancedColoring n t α m) : Hypergraph.balancedColoringThreshold n t α ≤ m :=
  Nat.sInf_le (s := {k | HasBalancedColoring n t α k}) h

private lemma threshold_mono_density (n t : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    Hypergraph.balancedColoringThreshold n t α ≤ Hypergraph.balancedColoringThreshold n t β := by
  apply threshold_le_of_feasible
  obtain ⟨col, hcol⟩ := threshold_feasible n t β
  refine ⟨col, fun X hm b ↦ ?_⟩
  obtain ⟨hpos, hβ⟩ := hcol X hm b
  exact ⟨hpos, (mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg _)).trans hβ⟩

private lemma threshold_mono_vertices {n N : ℕ} (hnN : n ≤ N) (t : ℕ) (α : ℝ) :
    Hypergraph.balancedColoringThreshold n t α ≤ Hypergraph.balancedColoringThreshold N t α := by
  apply threshold_le_of_feasible
  obtain ⟨col, hcol⟩ := threshold_feasible N t α
  let f := Fin.castLEEmb hnN
  refine ⟨fun e ↦ col (e.map f), fun X hm b ↦ ?_⟩
  have hm' : Hypergraph.balancedColoringThreshold N t α ≤ (X.map f).card := by simpa
  have h := hcol (X.map f) hm' b
  simp only [Finset.powersetCard_map, Finset.filter_map, Finset.card_map, Function.comp_def] at h
  convert! h using 1

private noncomputable abbrev threshold (t : ℕ) (density : ℝ) (n : ℕ) : ℝ :=
  Hypergraph.balancedColoringThreshold n t density

private lemma threshold_bigO_of_density_le (t : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    threshold t α =O[atTop] threshold t β := by
  apply IsBigO.of_bound 1
  filter_upwards with n
  simpa only [threshold, Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul] using
    (show threshold t α n ≤ threshold t β n by exact_mod_cast threshold_mono_density n t hαβ)

/-- Isolate the edges meeting every part by removing subfamilies of parts. -/
private lemma sum_transversals {n t q : ℕ} (X : Finset (Fin n))
    (P : Fin q → Finset (Fin n)) (w : Finset (Fin n) → ℝ) :
    ∑ e ∈ (X.powersetCard t).filter (fun e ↦ ∀ i, ¬ Disjoint e (P i)), w e =
      ∑ s ∈ (univ : Finset (Fin q)).powerset,
        (-1 : ℝ) ^ s.card * ∑ e ∈ (X \ s.biUnion P).powersetCard t, w e := by
  classical
  let E := X.powersetCard t
  let S (i : Fin q) : Finset (Finset (Fin n)) := univ.filter (fun e ↦ Disjoint e (P i))
  let f (e : Finset (Fin n)) := if e ∈ E then w e else 0
  have h := inclusion_exclusion_sum_inf_compl (univ : Finset (Fin q)) S f
  have left :
      ((univ : Finset (Fin q)).inf fun i ↦ (S i)ᶜ).filter (· ∈ E) =
        E.filter (fun e ↦ ∀ i, ¬ Disjoint e (P i)) := by
    ext e
    simp [S, and_comm, mem_inf]
  have right (s : Finset (Fin q)) :
      (s.inf S).filter (· ∈ E) = (X \ s.biUnion P).powersetCard t := by
    ext e
    simp only [mem_filter, mem_inf, S, mem_univ, true_and, E, mem_powersetCard]
    constructor
    · rintro ⟨hd, hx, ht⟩
      refine ⟨fun a ha ↦ mem_sdiff.mpr ⟨hx ha, ?_⟩, ht⟩
      rintro hm
      obtain ⟨i, hi, hai⟩ := mem_biUnion.mp hm
      exact disjoint_left.mp (hd i hi) ha hai
    · rintro ⟨hs, ht⟩
      refine ⟨fun i hi ↦ disjoint_left.mpr ?_, hs.trans sdiff_subset, ht⟩
      intro a ha hai
      exact (mem_sdiff.mp (hs ha)).2 (mem_biUnion.mpr ⟨i, hi, hai⟩)
  simp only [f, ← sum_filter, left, right, ← Int.cast_smul_eq_zsmul ℝ,
    Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul] at h
  exact h

private lemma abs_sum_transversals_le {n t q m : ℕ} (ht : 0 < t)
    (P : Fin q → Finset (Fin n)) (hdisj : Pairwise (Disjoint on P))
    (hm : ∀ i, m ≤ (P i).card) (w : Finset (Fin n) → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ Y ⊆ univ.biUnion P, m ≤ Y.card →
      |∑ e ∈ Y.powersetCard t, w e| ≤ M) :
    |∑ e ∈ ((univ.biUnion P).powersetCard t).filter (fun e ↦ ∀ i, ¬ Disjoint e (P i)),
      w e| ≤ (2 : ℝ) ^ q * M := by
  classical
  rw [sum_transversals]
  calc
    _ ≤ ∑ s ∈ (univ : Finset (Fin q)).powerset,
        |(-1 : ℝ) ^ s.card * ∑ e ∈ (univ.biUnion P \ s.biUnion P).powersetCard t, w e| :=
          abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ (univ : Finset (Fin q)).powerset, M := by
      apply sum_le_sum
      intro s _
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      by_cases hs : s = univ
      · have hempty : (∅ : Finset (Fin n)).powersetCard t = ∅ :=
          powersetCard_eq_empty.mpr (by simpa using ht)
        simpa [hs, hempty] using hM
      · obtain ⟨i, hi⟩ : ∃ i, i ∉ s := by
          by_contra! hall
          exact hs (eq_univ_of_forall hall)
        apply hbound _ sdiff_subset (hm i |>.trans (card_le_card ?_))
        intro a ha
        refine mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨i, mem_univ _, ha⟩, ?_⟩
        intro has
        obtain ⟨j, hj, haj⟩ := mem_biUnion.mp has
        exact disjoint_left.mp (hdisj (show i ≠ j from fun h ↦ hi (h ▸ hj))) ha haj
    _ = _ := by simp [nsmul_eq_mul]

private lemma card_transversals_ge {n t s : ℕ}
    (P : Fin t → Finset (Fin n)) (hdisj : Pairwise (Disjoint on P))
    (hs : ∀ i, (P i).card = s) :
    s ^ t ≤ (((univ.biUnion P).powersetCard t).filter
      (fun e ↦ ∀ i, ¬ Disjoint e (P i))).card := by
  classical
  let edge (f : ∀ i, ↥(P i)) := univ.image (fun i ↦ (f i).val)
  have hmatch {f g : ∀ i, ↥(P i)} {i j : Fin t} (he : (f i).val = (g j).val) : i = j := by
    by_contra hne
    exact disjoint_left.mp (hdisj hne) (f i).property (he.symm ▸ (g j).property)
  have hinj : Function.Injective edge := by
    intro f g hfg
    funext i
    apply Subtype.ext
    have hfi : (f i).val ∈ edge f := mem_image_of_mem _ (mem_univ i)
    rw [hfg] at hfi
    obtain ⟨j, _, hj⟩ := mem_image.mp hfi
    obtain rfl := hmatch hj.symm
    exact hj.symm
  have hsub : (univ.image edge) ⊆ ((univ.biUnion P).powersetCard t).filter
      (fun e ↦ ∀ i, ¬ Disjoint e (P i)) := by
    intro e he
    obtain ⟨f, _, rfl⟩ := mem_image.mp he
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro a ha
      obtain ⟨i, _, rfl⟩ := mem_image.mp ha
      exact mem_biUnion.mpr ⟨i, mem_univ _, (f i).property⟩
    · rw [show (edge f).card = (univ : Finset (Fin t)).card from
        card_image_of_injective _ (fun _ _ h ↦ hmatch h)]
      simp
    · intro i hd
      exact disjoint_left.mp hd (mem_image_of_mem _ (mem_univ i)) (f i).property
  have h := card_le_card hsub
  rw [card_image_of_injective _ hinj] at h
  simpa [Fintype.card_pi, hs] using h

/-- A monochromatic box forces an induced discrepancy on a union of its parts. -/
private lemma threshold_gt_of_monochromatic_transversals {n t s : ℕ} {α : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hα : α ≤ 1 / 2)
    (hαclose : ((2 : ℝ) * t) ^ t * (1 - 2 * α) < 1)
    (hbox : ∀ col : Finset (Fin n) → Bool, ∃ (P : Fin t → Finset (Fin n)) (b : Bool),
      Pairwise (Disjoint on P) ∧ (∀ i, (P i).card = s) ∧
        ∀ e ∈ ((univ.biUnion P).powersetCard t).filter (fun e ↦ ∀ i, ¬ Disjoint e (P i)),
          col e = b) :
    s < Hypergraph.balancedColoringThreshold n t α := by
  classical
  by_contra! h
  obtain ⟨col, hcol⟩ := threshold_feasible n t α
  obtain ⟨P, b, hdisj, hsize, hmono⟩ := hbox col
  let X := univ.biUnion P
  let W (e : Finset (Fin n)) : ℝ := (if col e = b then 2 else 0) - 1
  have hε : 0 ≤ 1 - 2 * α := by linarith
  have hbound (Y : Finset (Fin n)) (hYX : Y ⊆ X) (hY : s ≤ Y.card) :
      |∑ e ∈ Y.powersetCard t, W e| ≤ (1 - 2 * α) * (X.card.choose t : ℝ) := by
    let C := (Y.powersetCard t).filter (fun e ↦ col e = b)
    let D := (Y.powersetCard t).filter (fun e ↦ col e = !b)
    have hsum : ∑ e ∈ Y.powersetCard t, W e = 2 * (C.card : ℝ) - (Y.card.choose t : ℝ) := by
      simp [W, C, sum_sub_distrib, ← sum_filter, nsmul_eq_mul, mul_comm]
    have hD : D = (Y.powersetCard t).filter (fun e ↦ ¬ col e = b) := by
      ext e
      cases b <;> cases col e <;> simp_all [D]
    have hCD : (C.card : ℝ) + (D.card : ℝ) = (Y.card.choose t : ℝ) := by
      exact_mod_cast (show C.card + D.card = Y.card.choose t by
        rw [hD, ← card_powersetCard]
        exact card_filter_add_card_filter_not ..)
    have hb : α * (Y.card.choose t : ℝ) ≤ (C.card : ℝ) := (hcol Y (h.trans hY) b).2
    have hb' : α * (Y.card.choose t : ℝ) ≤ (D.card : ℝ) := (hcol Y (h.trans hY) (!b)).2
    calc
      _ ≤ (1 - 2 * α) * (Y.card.choose t : ℝ) := by
        rw [hsum, abs_le]
        constructor <;> linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        exact_mod_cast Nat.choose_le_choose t (card_le_card hYX)) hε
  let E := (X.powersetCard t).filter (fun e ↦ ∀ i, ¬ Disjoint e (P i))
  have hsum : ∑ e ∈ E, W e = (E.card : ℝ) := by
    calc
      _ = ∑ _e ∈ E, (1 : ℝ) := by
        apply sum_congr rfl
        intro e he
        norm_num [W, hmono e he]
      _ = _ := by simp
  have hupper := abs_sum_transversals_le ht P hdisj
    (fun i ↦ (hsize i).ge) W (mul_nonneg hε (Nat.cast_nonneg _)) hbound
  change |∑ e ∈ E, W e| ≤ (2 : ℝ) ^ t * ((1 - 2 * α) * (X.card.choose t : ℝ)) at hupper
  rw [hsum, abs_of_nonneg (Nat.cast_nonneg _)] at hupper
  have hX : X.card = t * s := by
    rw [show X = univ.biUnion P from rfl, card_biUnion (fun _ _ _ _ hij ↦ hdisj hij)]
    simp [hsize]
  have hc : (X.card.choose t : ℝ) ≤ ((t : ℝ) * s) ^ t := by
    rw [hX]
    exact_mod_cast Nat.choose_le_pow (t * s) t
  have hlower : (s : ℝ) ^ t ≤ (E.card : ℝ) := by
    exact_mod_cast card_transversals_ge P hdisj hsize
  have hlt : ((2 : ℝ) * t) ^ t * (1 - 2 * α) * (s : ℝ) ^ t < (s : ℝ) ^ t := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hαclose (show 0 < (s : ℝ) ^ t by positivity)
  apply hlt.not_ge
  calc
    (s : ℝ) ^ t ≤ (E.card : ℝ) := hlower
    _ ≤ (2 : ℝ) ^ t * ((1 - 2 * α) * (X.card.choose t : ℝ)) := hupper
    _ ≤ (2 : ℝ) ^ t * ((1 - 2 * α) * ((t : ℝ) * s) ^ t) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hε) (by positivity)
    _ = _ := by rw [mul_pow, mul_pow]; ring

open scoped Classical in
/-- Choose an s-set with a large common fiber by counting incidences with rich fibers. -/
private lemma exists_large_common_fiber {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) (s : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hs : 4 * (s : ℝ) ≤ δ * Fintype.card A)
    (hdense : δ * Fintype.card A * Fintype.card B ≤
      ∑ y : B, ((univ.filter fun x ↦ R x y).card : ℝ)) :
    ∃ Q : Finset A, Q.card = s ∧
      (δ / 4) ^ (s + 1) * Fintype.card B ≤
        ((univ.filter fun y : B ↦ ∀ x ∈ Q, R x y).card : ℝ) := by
  classical
  let N : ℝ := Fintype.card A
  let K : ℝ := Fintype.card B
  let F (y : B) : Finset A := univ.filter fun x ↦ R x y
  let G : Finset B := univ.filter fun y ↦ δ * N / 2 ≤ (F y).card
  let Qs := (univ : Finset A).powersetCard s
  let C (Q : Finset A) : Finset B := univ.filter fun y ↦ Q ⊆ F y
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := A)
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hG : δ / 2 * K ≤ (G.card : ℝ) := by
    have hsum : ∑ y : B, ((F y).card : ℝ) ≤ (G.card : ℝ) * N + K * (δ * N / 2) := by
      calc
        _ ≤ ∑ y : B, ((if y ∈ G then N else 0) + δ * N / 2) := by
          apply sum_le_sum
          intro y _
          split_ifs with hy
          · have hle : ((F y).card : ℝ) ≤ N := by
              dsimp [N]
              exact_mod_cast card_le_univ (F y)
            linarith [mul_nonneg hδ hN.le]
          · have hlt : (F y).card < δ * N / 2 := by simpa [G] using hy
            simpa using hlt.le
        _ = _ := by simp [K, sum_add_distrib, nsmul_eq_mul]
    apply (le_of_mul_le_mul_right ?_ hN)
    change δ * N * K ≤ ∑ y : B, ((F y).card : ℝ) at hdense
    linarith [hdense.trans hsum]
  have hsN : s ≤ Fintype.card A := by
    have h : (s : ℝ) ≤ N := by
      have h' : δ * N ≤ N := by simpa using mul_le_mul_of_nonneg_right hδ1 hN.le
      linarith
    exact_mod_cast (show (s : ℝ) ≤ Fintype.card A from h)
  have hchoose (y : B) (hy : y ∈ G) :
      (δ / 4) ^ s * ((Fintype.card A).choose s : ℝ) ≤ ((F y).card.choose s : ℝ) := by
    have hy' : δ * N / 2 ≤ ((F y).card : ℝ) := (mem_filter.mp hy).2
    have hsF : s ≤ (F y).card := by
      have h : (s : ℝ) ≤ ((F y).card : ℝ) := by linarith
      exact_mod_cast h
    have hbase : δ / 4 * N ≤ ((F y).card + 1 - s : ℕ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      linarith
    calc
      _ ≤ (δ / 4) ^ s * (N ^ s / (s.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (Nat.choose_le_pow_div s (Fintype.card A)) (by positivity)
      _ = (δ / 4 * N) ^ s / (s.factorial : ℝ) := by rw [mul_pow, mul_div_assoc]
      _ ≤ ((↑((F y).card + 1 - s) : ℝ) ^ s) / (s.factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase _) (Nat.cast_nonneg _)
      _ ≤ _ := Nat.pow_le_choose s (F y).card
  have hswap : ∑ Q ∈ Qs, ((C Q).card : ℝ) = ∑ y : B, ((F y).card.choose s : ℝ) := by
    suffices hswap' : ∑ Q ∈ Qs, (C Q).card = ∑ y : B, (F y).card.choose s by exact_mod_cast hswap'
    calc
      _ = ∑ Q ∈ Qs, ∑ y : B, if Q ⊆ F y then 1 else 0 := by simp [C]
      _ = ∑ y : B, ∑ Q ∈ Qs, if Q ⊆ F y then 1 else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro y _
        rw [sum_boole, ← card_powersetCard]
        apply congrArg Finset.card
        ext Q
        simp [Qs, mem_powersetCard, and_comm]
  have hQs : (Qs.card : ℝ) = (Fintype.card A).choose s := by simp [Qs]
  have hsum : ∑ Q ∈ Qs, ((δ / 4) ^ (s + 1) * K) ≤ ∑ Q ∈ Qs, ((C Q).card : ℝ) := by
    rw [hswap]
    calc
      _ = (δ / 4 * K) * ((δ / 4) ^ s * ((Fintype.card A).choose s : ℝ)) := by
        simp only [sum_const, nsmul_eq_mul, hQs, pow_succ]
        ring
      _ ≤ (G.card : ℝ) * ((δ / 4) ^ s * ((Fintype.card A).choose s : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (mul_le_mul_of_nonneg_right (by linarith) hK : δ / 4 * K ≤ δ / 2 * K).trans hG
      _ = ∑ _y ∈ G, (δ / 4) ^ s * ((Fintype.card A).choose s : ℝ) := by
        simp [nsmul_eq_mul]
      _ ≤ ∑ y ∈ G, ((F y).card.choose s : ℝ) := sum_le_sum hchoose
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ G) (fun _ _ _ ↦ by positivity)
  obtain ⟨Q, hQ, hC⟩ := exists_le_of_sum_le
    (show Qs.Nonempty by simpa [Qs, ← card_pos] using Nat.choose_pos hsN) hsum
  refine ⟨Q, (mem_powersetCard.mp hQ).2, ?_⟩
  have hCeq : (univ.filter fun y : B ↦ ∀ x ∈ Q, R x y) = C Q := by
    ext y
    simp only [mem_filter, mem_univ, true_and, C, Finset.subset_iff, F]
  rw [hCeq]
  exact hC

open scoped Classical in
private lemma card_relation_eq_sum_fibers {A : Type*} [Fintype A] {d : ℕ}
    (R : (Fin (d + 1) → A) → Prop) :
    ((univ.filter R).card : ℝ) =
      ∑ y : Fin d → A, ((univ.filter fun x ↦ R (Fin.cons x y)).card : ℝ) := by
  classical
  let F (y : Fin d → A) : Finset A := univ.filter fun x ↦ R (Fin.cons x y)
  have h : ((univ : Finset (Fin d → A)).sigma F).card = (univ.filter R).card := by
    refine card_bij (fun p _ ↦ Fin.cons p.2 p.1) ?_ ?_ ?_
    · intro p hp
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (mem_sigma.mp hp).2).2⟩
    · rintro ⟨y, x⟩ _ ⟨y', x'⟩ _ he
      have hy : y = y' := by simpa using congrArg Fin.tail he
      have hx : x = x' := by simpa using congrFun he 0
      subst y'
      subst x'
      rfl
    · intro p hp
      refine ⟨⟨Fin.tail p, p 0⟩, mem_sigma.mpr ⟨mem_univ _, ?_⟩, Fin.cons_self_tail p⟩
      exact mem_filter.mpr ⟨mem_univ _, by simpa using (mem_filter.mp hp).2⟩
  rw [card_sigma] at h
  exact_mod_cast h.symm

open scoped Classical in
private lemma exists_cartesian_box_of_density {N s d : ℕ} (hN : 0 < N)
    (δ : ℕ → ℝ)
    (hδ : ∀ j ≤ d, 0 ≤ δ j ∧ δ j ≤ 1 ∧ 4 * (s : ℝ) ≤ δ j * N)
    (hstep : ∀ j < d, δ (j + 1) ≤ (δ j / 4) ^ (s + 1))
    (R : (Fin (d + 1) → Fin N) → Prop)
    (hR : δ 0 * (N : ℝ) ^ (d + 1) ≤ ((univ.filter R).card : ℝ)) :
    ∃ P : Fin (d + 1) → Finset (Fin N), (∀ i, (P i).card = s) ∧
      ∀ p : Fin (d + 1) → Fin N, (∀ i, p i ∈ P i) → R p := by
  classical
  induction d generalizing δ with
  | zero =>
    let F : Finset (Fin N) := univ.filter fun x ↦ R (fun _ ↦ x)
    have hcard : (univ.filter R).card = F.card := by
      refine card_bij (fun p _ ↦ p 0) ?_ ?_ ?_
      · intro p hp
        have he : (fun _ : Fin 1 ↦ p 0) = p := by funext i; fin_cases i; rfl
        exact mem_filter.mpr ⟨mem_univ _, he.symm ▸ (mem_filter.mp hp).2⟩
      · intro p _ q _ h
        funext i
        fin_cases i
        exact h
      · intro x hx
        exact ⟨fun _ ↦ x, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩, rfl⟩
    rw [hcard, pow_one] at hR
    have hs : s ≤ F.card := by
      have h := (hδ 0 le_rfl).2.2.trans hR
      exact_mod_cast (show (s : ℝ) ≤ F.card from by linarith)
    obtain ⟨Q, hQ, hQs⟩ := exists_subset_card_eq hs
    refine ⟨fun _ ↦ Q, fun _ ↦ hQs, fun p hp ↦ ?_⟩
    have he : (fun _ : Fin 1 ↦ p 0) = p := by funext i; fin_cases i; rfl
    exact he ▸ (mem_filter.mp (hQ (hp 0))).2
  | succ d ih =>
    let R' (x : Fin N) (y : Fin (d + 1) → Fin N) := R (Fin.cons x y)
    have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    have hdense : δ 0 * Fintype.card (Fin N) * Fintype.card (Fin (d + 1) → Fin N) ≤
        ∑ y : Fin (d + 1) → Fin N, ((univ.filter fun x ↦ R' x y).card : ℝ) := by
      rw [← card_relation_eq_sum_fibers R]
      simpa [Fintype.card_pi_const, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hR
    have h0 := hδ 0 (Nat.zero_le _)
    obtain ⟨Q, hQs, hQ⟩ := exists_large_common_fiber R' s h0.1 h0.2.1
      (by simpa using h0.2.2) hdense
    let R'' (y : Fin (d + 1) → Fin N) := ∀ x ∈ Q, R' x y
    let : DecidablePred R'' := fun y ↦ Classical.propDecidable (R'' y)
    have hR'' : δ (0 + 1) * (N : ℝ) ^ (d + 1) ≤ ((univ.filter R'').card : ℝ) := by
      refine (mul_le_mul_of_nonneg_right (hstep 0 (Nat.zero_lt_succ _)) (by positivity)).trans ?_
      simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow] at hQ
      convert! hQ using 4
    obtain ⟨P, hPs, hP⟩ := ih (fun j ↦ δ (j + 1))
      (fun j hj ↦ hδ _ (Nat.succ_le_succ hj))
      (fun j hj ↦ hstep _ (Nat.succ_lt_succ hj)) R'' hR''
    refine ⟨Fin.cons Q P, fun i ↦ Fin.cases (by simpa) (fun j ↦ by simpa using hPs j) i,
      fun p hp ↦ ?_⟩
    have hy : R'' (Fin.tail p) := hP _ (fun i ↦ by simpa [Fin.tail] using hp i.succ)
    simpa [R', Fin.cons_self_tail] using hy (p 0) (by simpa using hp 0)

private lemma exists_monochromatic_transversals {n d N s : ℕ}
    (hs : 0 < s) (hN : s * 32 ^ ((s + 1) ^ d) ≤ N) (hn : (d + 1) * N ≤ n)
    (col : Finset (Fin n) → Bool) :
    ∃ (P : Fin (d + 1) → Finset (Fin n)) (b : Bool),
      Pairwise (Disjoint on P) ∧ (∀ i, (P i).card = s) ∧
        ∀ e ∈ ((univ.biUnion P).powersetCard (d + 1)).filter (fun e ↦ ∀ i, ¬ Disjoint e (P i)),
          col e = b := by
  classical
  let g (i : Fin (d + 1)) : Fin N ↪ Fin n :=
    ⟨fun x ↦ Fin.castLEEmb hn (finProdFinEquiv (i, x)), fun a b h ↦
      congrArg Prod.snd (finProdFinEquiv.injective (Fin.castLEEmb hn |>.injective h))⟩
  have hg {i j : Fin (d + 1)} {x y : Fin N} (h : g i x = g j y) : i = j :=
    congrArg Prod.fst (finProdFinEquiv.injective (Fin.castLEEmb hn |>.injective h))
  let edge (p : Fin (d + 1) → Fin N) : Finset (Fin n) := univ.image (fun i ↦ g i (p i))
  have hedge (p) : (edge p).card = d + 1 := by
    rw [show (edge p).card = (univ : Finset (Fin (d + 1))).card from
      card_image_of_injective _ (fun _ _ h ↦ hg h)]
    simp
  let F (b : Bool) := univ.filter fun p ↦ col (edge p) = b
  have hsum : (F true).card + (F false).card = N ^ (d + 1) := by
    have hfalse : F false = univ.filter (fun p ↦ ¬ col (edge p) = true) := by
      ext p
      cases col (edge p) <;> simp_all [F]
    rw [hfalse, show N ^ (d + 1) = (univ : Finset (Fin (d + 1) → Fin N)).card by
      simp]
    exact card_filter_add_card_filter_not ..
  obtain ⟨b, hb⟩ : ∃ b, (1 / 2 : ℝ) * (N : ℝ) ^ (d + 1) ≤ ((F b).card : ℝ) := by
    by_contra! h
    have hsum' : ((F true).card : ℝ) + ((F false).card : ℝ) = (N : ℝ) ^ (d + 1) := by
      exact_mod_cast hsum
    linarith [h true, h false]
  -- This density sequence leaves enough room for the loss from choosing each new part.
  let δ (j : ℕ) : ℝ := 16 / (32 : ℝ) ^ ((s + 1) ^ j)
  have hδ (j : ℕ) (hj : j ≤ d) : 0 ≤ δ j ∧ δ j ≤ 1 ∧ 4 * (s : ℝ) ≤ δ j * N := by
    have he : 1 ≤ (s + 1) ^ j := one_le_pow₀ (by omega : 1 ≤ s + 1)
    have h₁ : (32 : ℝ) ≤ 32 ^ ((s + 1) ^ j) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 32) he
    have h₂ : (32 : ℝ) ^ ((s + 1) ^ j) ≤ 32 ^ ((s + 1) ^ d) := by
      exact pow_le_pow_right₀ (by norm_num) (pow_le_pow_right₀ (by omega) hj)
    have hN' : (s : ℝ) * 32 ^ ((s + 1) ^ d) ≤ N := by exact_mod_cast hN
    refine ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith), ?_⟩
    dsimp [δ]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h₃ := (mul_le_mul_of_nonneg_left h₂ (show (0 : ℝ) ≤ s by positivity)).trans hN'
    linarith
  have hstep (j : ℕ) : δ (j + 1) ≤ (δ j / 4) ^ (s + 1) := by
    have hdiv : δ j / 4 = 4 / (32 : ℝ) ^ ((s + 1) ^ j) := by
      dsimp [δ]
      field_simp
      norm_num
    rw [hdiv, div_pow, ← pow_mul, ← pow_succ]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [show (4 : ℝ) ^ 2 = 16 by norm_num] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (show 2 ≤ s + 1 by omega)
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.mul_pos hs (by positivity)) hN
  obtain ⟨Q, hQ, hmono⟩ := exists_cartesian_box_of_density hNpos δ hδ
    (fun j _ ↦ hstep j) (fun p ↦ col (edge p) = b) (by
      have hδ₀ : δ 0 = (1 / 2 : ℝ) := by norm_num [δ]
      rw [hδ₀]
      convert! hb using 4)
  refine ⟨fun i ↦ (Q i).map (g i), b, ?_, fun i ↦ by simpa using hQ i, ?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨x, _, hx⟩ := mem_map.mp hzi
    obtain ⟨y, _, hy⟩ := mem_map.mp hzj
    exact hij (hg (hx.trans hy.symm))
  · intro e he
    obtain ⟨⟨_, hecard⟩, heparts⟩ := (mem_filter.mp he).imp_left mem_powersetCard.mp
    have hhit (i : Fin (d + 1)) : ∃ x ∈ Q i, g i x ∈ e := by
      by_contra! hm
      apply heparts i
      apply disjoint_left.mpr
      intro z hz hzi
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hzi
      exact hm x hx hz
    choose p hp hpe using hhit
    have hsub : edge p ⊆ e := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      exact hpe i
    have heq : edge p = e := eq_of_subset_of_card_le hsub (by rw [hecard, hedge])
    exact heq ▸ hmono p hp

private lemma threshold_pos_of_pos_uniformity (n d : ℕ) (α : ℝ) :
    0 < Hypergraph.balancedColoringThreshold n (d + 1) α := by
  by_contra! h
  obtain ⟨col, hcol⟩ := threshold_feasible n (d + 1) α
  have hempty : (∅ : Finset (Fin n)).powersetCard (d + 1) = ∅ :=
    powersetCard_eq_empty.mpr (by simp)
  have hpos := (hcol ∅ (by simpa using h) false).1
  simp [hempty] at hpos

private lemma log_le_threshold_pow_near_half (n d : ℕ) (hd : 0 < d) {α : ℝ}
    (hα : α ≤ 1 / 2) (hclose : ((2 : ℝ) * (d + 1)) ^ (d + 1) * (1 - 2 * α) < 1) :
    Real.log n ≤ ((d : ℝ) + 2 + 2 ^ d * Real.log 32) * (threshold (d + 1) α n) ^ d := by
  let m := Hypergraph.balancedColoringThreshold n (d + 1) α
  have hm : 0 < m := threshold_pos_of_pos_uniformity n d α
  have hN : n < (d + 1) * (m * 32 ^ ((m + 1) ^ d)) := by
    by_contra! hn
    have hw := threshold_gt_of_monochromatic_transversals (Nat.succ_pos d) hm hα
      (by simpa only [Nat.cast_succ] using hclose) (exists_monochromatic_transversals hm le_rfl hn)
    exact lt_irrefl m hw
  have hlog32 : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm_d : (m : ℝ) ≤ (m : ℝ) ^ d := by
    simpa only [pow_one] using pow_le_pow_right₀ hmone hd
  have hm_d_one : (1 : ℝ) ≤ (m : ℝ) ^ d := hmone.trans hm_d
  change Real.log n ≤ ((d : ℝ) + 2 + 2 ^ d * Real.log 32) * (m : ℝ) ^ d
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.cast_zero, Real.log_zero]
    positivity
  have hN' : (n : ℝ) ≤ ((d : ℝ) + 1) * ((m : ℝ) * 32 ^ ((m + 1) ^ d)) := by
    exact_mod_cast hN.le
  have hpow : ((m : ℝ) + 1) ^ d ≤ 2 ^ d * (m : ℝ) ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc
    Real.log n ≤ Real.log (((d : ℝ) + 1) * ((m : ℝ) * 32 ^ ((m + 1) ^ d))) :=
      Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hN'
    _ = Real.log ((d : ℝ) + 1) + Real.log (m : ℝ) +
          ((m : ℝ) + 1) ^ d * Real.log 32 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
      push_cast
      ring
    _ ≤ ((d : ℝ) + 1) * (m : ℝ) ^ d + (m : ℝ) ^ d +
          (2 ^ d * (m : ℝ) ^ d) * Real.log 32 := by
      have hd' : Real.log ((d : ℝ) + 1) ≤ ((d : ℝ) + 1) * (m : ℝ) ^ d :=
        (Real.log_le_self (by positivity)).trans (le_mul_of_one_le_right (by positivity) hm_d_one)
      have hm' : Real.log (m : ℝ) ≤ (m : ℝ) ^ d :=
        (Real.log_le_self (by positivity)).trans hm_d
      exact add_le_add (add_le_add hd' hm') (mul_le_mul_of_nonneg_right hpow hlog32)
    _ = _ := by ring

private noncomputable abbrev logScale (d : ℕ) (n : ℕ) : ℝ :=
  Real.log n ^ ((d : ℝ)⁻¹)

private lemma logScale_bigO_threshold_near_half (d : ℕ) (hd : 0 < d) {α : ℝ}
    (hα : α ≤ 1 / 2) (hclose : ((2 : ℝ) * (d + 1)) ^ (d + 1) * (1 - 2 * α) < 1) :
    logScale d =O[atTop] threshold (d + 1) α := by
  let C : ℝ := d + 2 + 2 ^ d * Real.log 32
  have hC : 0 ≤ C := by
    have hlog : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
    dsimp [C]
    positivity
  apply IsBigO.of_bound (C ^ ((d : ℝ)⁻¹))
  filter_upwards with n
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have hm : 0 ≤ threshold (d + 1) α n := Nat.cast_nonneg _
  have hroot := Real.rpow_le_rpow hlog (log_le_threshold_pow_near_half n d hd hα hclose)
    (inv_nonneg.mpr (Nat.cast_nonneg d))
  have hpow : ((threshold (d + 1) α n) ^ d) ^ ((d : ℝ)⁻¹) = threshold (d + 1) α n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm, mul_inv_cancel₀ (by exact_mod_cast hd.ne'),
      Real.rpow_one]
  rw [Real.mul_rpow hC (pow_nonneg hm d), hpow] at hroot
  simpa only [logScale, Real.norm_of_nonneg (Real.rpow_nonneg hlog _), Real.norm_of_nonneg hm]
    using hroot

private noncomputable abbrev endpointGap (k : ℕ) : ℝ := 1 / ((k : ℝ) + 4)

private lemma theta_of_reciprocal_comparisons (t : ℕ)
    (h : ∀ k : ℕ, threshold t (1 / 2 - endpointGap k) =O[atTop] threshold t (endpointGap k))
    {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1 / 2) :
    threshold t α =Θ[atTop] threshold t β := by
  let ε := min (min α β) (min (1 / 2 - α) (1 / 2 - β))
  have hε : 0 < ε := lt_min (lt_min hα0 hβ0) (lt_min (sub_pos.mpr hα1) (sub_pos.mpr hβ1))
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hgap : endpointGap k ≤ ε := by
    apply le_trans _ hk.le
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hloα : endpointGap k ≤ α := hgap.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hloβ : endpointGap k ≤ β := hgap.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhiα : α ≤ 1 / 2 - endpointGap k :=
    le_sub_comm.mp (hgap.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhiβ : β ≤ 1 / 2 - endpointGap k :=
    le_sub_comm.mp (hgap.trans ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨(threshold_bigO_of_density_le t hhiα).trans ((h k).trans (threshold_bigO_of_density_le t hloβ)),
    (threshold_bigO_of_density_le t hhiβ).trans ((h k).trans (threshold_bigO_of_density_le t hloα))⟩

private lemma exists_density_with_logScale_lower (d : ℕ) (hd : 0 < d) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ logScale d =O[atTop] threshold (d + 1) γ := by
  let A : ℝ := (2 * ((d : ℝ) + 1)) ^ (d + 1)
  let ε : ℝ := (4 * A)⁻¹
  have hA : 1 ≤ A := by
    apply one_le_pow₀
    have hn : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hε : 0 < ε := by positivity
  have hε' : ε ≤ 1 / 4 := by
    dsimp [ε]
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    linarith
  refine ⟨1 / 2 - ε, by linarith, by linarith, logScale_bigO_threshold_near_half d hd (by linarith) ?_⟩
  change A * (1 - 2 * (1 / 2 - ε)) < 1
  have h : A * (1 - 2 * (1 / 2 - ε)) = 1 / 2 := by
    dsimp [ε]
    field_simp [hApos.ne']
    ring
  rw [h]
  norm_num

/-- Given the logarithmic upper bound, the comparisons are equivalent to its matching lower bound. -/
private lemma reciprocal_comparisons_iff_lower_logScale {d : ℕ} (hd : 0 < d)
    (hupper : ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 →
      threshold (d + 1) ρ =O[atTop] logScale d) :
    (∀ k, threshold (d + 1) (1 / 2 - endpointGap k) =O[atTop]
      threshold (d + 1) (endpointGap k)) ↔
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 → logScale d =O[atTop] threshold (d + 1) ρ := by
  constructor
  · intro h ρ hρ hρ'
    obtain ⟨γ, hγ, hγ', hlog⟩ := exists_density_with_logScale_lower d hd
    exact hlog.trans (theta_of_reciprocal_comparisons (d + 1) h hγ hγ' hρ hρ').isBigO
  · intro hlower k
    have hgap : 0 < endpointGap k := by positivity
    have hgap' : endpointGap k < 1 / 2 := by
      unfold endpointGap
      rw [div_lt_iff₀ (by positivity)]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
    exact (hupper _ (sub_pos.mpr hgap') (sub_lt_self _ hgap)).trans (hlower _ hgap hgap')

theorem OMA.solution : type_of% @Erdos161.erdos_161.parts.ii := by
  intro t ht α β hα0 hα1 hβ0 hβ1
  apply theta_of_reciprocal_comparisons t ?_ hα0 hα1 hβ0 hβ1
  intro k
  cases k with
  | zero =>
    have h : (1 : ℝ) / 2 - endpointGap 0 = endpointGap 0 := by norm_num [endpointGap]
    rw [h]
  | succ k =>
    sorry
