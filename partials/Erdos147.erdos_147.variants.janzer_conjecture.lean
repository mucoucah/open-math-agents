import FormalConjectures.ErdosProblems.«147»

/-! Bounds and reductions for the regular-graph extremal problem. -/

-- Problem: Erdős Problem 147 — janzer conjecture
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/147.lean:107 (declaration Erdos147.erdos_147.variants.janzer_conjecture)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics SimpleGraph Finset
open scoped Classical

namespace JanzerRelay

/-- A degree threshold for a copy in every nonempty host gives an extremal bound. -/
theorem extremal_of_degree_threshold {W : Type} (H : SimpleGraph W) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (force : ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      (∀ v, C * (Fintype.card V : ℝ) ^ a < (G.degree v : ℝ)) → H ⊑ G) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (a + 1) := by
  classical
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have bound : ∀ (m : ℕ) (V : Type) [Fintype V], Fintype.card V = m → m ≤ n →
      ∀ (G : SimpleGraph V), H.Free G →
        (G.edgeFinset.card : ℝ) ≤ (m : ℝ) * (C * (n : ℝ) ^ a) := by
    intro m
    induction m with
    | zero =>
      intro V _ hV _ G _
      have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      have : G = ⊥ := Subsingleton.elim _ _
      simp [this]
    | succ m ih =>
      intro V _ hV hmn G hfree
      have : Nonempty V := Fintype.card_pos_iff.mp (hV.symm ▸ m.succ_pos)
      obtain ⟨v, hv⟩ : ∃ v, (G.degree v : ℝ) ≤ C * (n : ℝ) ^ a := by
        by_contra! hf
        apply hfree (force V G ?_)
        intro v
        have hc : (Fintype.card V : ℝ) ≤ n := by exact_mod_cast (hV.trans_le hmn)
        exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hc ha) hC).trans_lt (hf v)
      let T : Set V := {v}ᶜ
      have hT : Fintype.card T = m := by
        change Fintype.card (({v} : Set V)ᶜ : Set V) = m
        rw [Fintype.card_compl_set, hV, @Fintype.card_unique ({v} : Set V), Nat.add_sub_cancel]
      have hfreeT : H.Free (G.induce T) := fun hc => hfree (hc.trans ⟨Copy.induce G T⟩)
      have hrest := ih T hT (by omega) (G.induce T) hfreeT
      have hsplit : (G.induce T).edgeFinset.card + G.degree v = G.edgeFinset.card := by
        simp only [T, card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]
        exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)
      have hsplitR : ((G.induce T).edgeFinset.card : ℝ) + G.degree v = G.edgeFinset.card := by
        exact_mod_cast hsplit
      rw [← hsplitR, Nat.cast_succ, add_mul, one_mul]
      exact add_le_add hrest hv
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg hnR.le _)]
  have hrewrite : C * (n : ℝ) ^ (a + 1) = (n : ℝ) * (C * (n : ℝ) ^ a) := by
    rw [Real.rpow_add hnR, Real.rpow_one]
    ring
  rw [hrewrite, ← Fintype.card_fin n]
  apply (extremalNumber_le_iff_of_nonneg (V := Fin n) H (by positivity)).2
  intro G _ hfree
  have h := bound n (Fin n) (Fintype.card_fin n) le_rfl G hfree
  rw [Fintype.card_fin]
  convert! h

/-- Count pairs consisting of a vertex and an r-subset of its neighborhood. -/
theorem sum_choose_degrees_le_of_free {V : Type} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free G) :
    (∑ v : V, (G.degree v).choose r) ≤ (Fintype.card V).choose r * (r - 1) := by
  classical
  let S := (univ : Finset V).powersetCard r
  let common (s : Finset V) := univ.filter fun v => ∀ u ∈ s, G.Adj u v
  have hcommon (s : Finset V) (hs : s ∈ S) : (common s).card ≤ r - 1 := by
    by_contra! h
    have hr : r ≤ (common s).card := by omega
    obtain ⟨t, hts, htc⟩ := exists_subset_card_eq hr
    apply hfree (completeBipartiteGraph_isContained_iff.mpr ?_)
    refine ⟨s, t, ?_, by simpa using htc, ?_⟩
    · simpa using (mem_powersetCard.mp hs).2
    · intro u hu v hv
      exact (mem_filter.mp (hts hv)).2 u hu
  have hcount (v : V) :
      (∑ s ∈ S, if s ⊆ G.neighborFinset v then 1 else 0) = (G.degree v).choose r := by
    rw [← card_filter]
    have hsets : S.filter (· ⊆ G.neighborFinset v) = (G.neighborFinset v).powersetCard r := by
      ext s
      simp [S, mem_powersetCard, and_comm]
    rw [hsets, card_powersetCard, card_neighborFinset_eq_degree]
  calc
    _ = ∑ v : V, ∑ s ∈ S, if s ⊆ G.neighborFinset v then 1 else 0 :=
      sum_congr rfl fun v _ => (hcount v).symm
    _ = ∑ s ∈ S, ∑ v : V, if s ⊆ G.neighborFinset v then 1 else 0 := sum_comm
    _ = ∑ s ∈ S, (common s).card := by
      apply sum_congr rfl
      intro s _
      rw [← card_filter]
      congr 1
      ext v
      simp only [mem_filter, mem_univ, true_and, common, subset_iff, mem_neighborFinset]
      exact ⟨fun h u hu => (h hu).symm, fun h u hu => (h u hu).symm⟩
    _ ≤ ∑ _s ∈ S, (r - 1) := sum_le_sum hcommon
    _ = _ := by simp [S]

/-- The complete bipartite graph occurs at the classical degree threshold. -/
theorem contains_balanced_biclique {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) {r : ℕ} (hr : 1 ≤ r)
    (hd : ∀ v, (2 * r : ℝ) * (Fintype.card V : ℝ) ^ (1 - 1 / (r : ℝ)) <
      (G.degree v : ℝ)) :
    completeBipartiteGraph (Fin r) (Fin r) ⊑ G := by
  classical
  by_contra hf
  let n : ℝ := Fintype.card V
  let a : ℝ := 1 - 1 / (r : ℝ)
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (show 1 ≤ Fintype.card V from Fintype.card_pos (α := V))
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hde : 0 ≤ a := sub_nonneg.mpr ((div_le_one (by positivity)).2 hrR)
  have hp : 1 ≤ n ^ a := Real.one_le_rpow hn hde
  have hfac : 0 < (r.factorial : ℝ) := by positivity
  have hpower : (n ^ a) ^ r = n ^ (r : ℝ) / n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have he : a * (r : ℝ) = (r : ℝ) - 1 := by
      dsimp [a]
      field_simp
    rw [he, Real.rpow_sub (by positivity), Real.rpow_one]
  have hlower (v : V) : (r : ℝ) * (n ^ (r : ℝ) / n) / r.factorial <
      ((G.degree v).choose r : ℝ) := by
    have hcast : (r : ℝ) + n ^ a < (G.degree v : ℝ) := by
      have h1 : (r : ℝ) + n ^ a ≤ 2 * (r : ℝ) * n ^ a := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (sub_nonneg.mpr hp)]
      exact h1.trans_lt (hd v)
    have hsub : r ≤ G.degree v + 1 := by
      have : (r : ℝ) ≤ (G.degree v : ℝ) := by linarith
      exact (Nat.cast_le.mp this).trans (Nat.le_succ _)
    have hshift : (r : ℝ) * n ^ a < (↑(G.degree v + 1 - r) : ℝ) := by
      rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
      have hh := hd v
      change (2 * (r : ℝ)) * n ^ a < (G.degree v : ℝ) at hh
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by positivity) (sub_nonneg.mpr hp)]
    have hpow := pow_lt_pow_left₀ hshift (by positivity : 0 ≤ (r : ℝ) * n ^ a) (by omega : r ≠ 0)
    have hrpow : (r : ℝ) ≤ (r : ℝ) ^ r := le_self_pow₀ hrR (by omega)
    calc
      _ ≤ ((r : ℝ) * n ^ a) ^ r / r.factorial := by
        rw [mul_pow, hpower]
        gcongr
      _ < (↑(G.degree v + 1 - r) : ℝ) ^ r / r.factorial :=
        div_lt_div_of_pos_right hpow hfac
      _ ≤ _ := Nat.pow_le_choose r (G.degree v)
  have hsumLower := sum_lt_sum_of_nonempty (s := (univ : Finset V)) univ_nonempty
    (fun v _ => hlower v)
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsumLower
  have hu : (∑ v : V, ((G.degree v).choose r : ℝ)) ≤
      ((Fintype.card V).choose r : ℝ) * ((r : ℝ) - 1) := by
    have h := sum_choose_degrees_le_of_free G r hf
    exact_mod_cast h
  have hchoose : ((Fintype.card V).choose r : ℝ) ≤ n ^ (r : ℝ) / r.factorial := by
    rw [Real.rpow_natCast]
    exact Nat.choose_le_pow_div r (Fintype.card V)
  have htop := hu.trans (mul_le_mul_of_nonneg_right hchoose (sub_nonneg.mpr hrR))
  change n * ((r : ℝ) * (n ^ (r : ℝ) / n) / r.factorial) < _ at hsumLower
  have hcancel : n * ((r : ℝ) * (n ^ (r : ℝ) / n) / r.factorial) =
      (n ^ (r : ℝ) / r.factorial) * (r : ℝ) := by
    have hn0 : n ≠ 0 := by linarith
    field_simp
  rw [hcancel] at hsumLower
  nlinarith [hsumLower.trans_le htop, show 0 ≤ n ^ (r : ℝ) / r.factorial by positivity]

theorem balanced_biclique_regular (r : ℕ) :
    (completeBipartiteGraph (Fin r) (Fin r)).IsRegularOfDegree r := by
  classical
  let B := completeBipartiteGraph (Fin r) (Fin r)
  have left (u : Fin r) : B.neighborSet (Sum.inl u) ≃ Fin r := {
    toFun := fun x => match x with
      | ⟨.inl _, h⟩ => False.elim (by simp [B] at h)
      | ⟨.inr v, _⟩ => v
    invFun := fun v => ⟨Sum.inr v, by simp [B]⟩
    left_inv := by
      rintro ⟨x, hx⟩
      cases x with
      | inl x => exact False.elim (by simp [B] at hx)
      | inr x => rfl
    right_inv := fun _ => rfl }
  have right (u : Fin r) : B.neighborSet (Sum.inr u) ≃ Fin r := {
    toFun := fun x => match x with
      | ⟨.inl v, _⟩ => v
      | ⟨.inr _, h⟩ => False.elim (by simp [B] at h)
    invFun := fun v => ⟨Sum.inl v, by simp [B]⟩
    left_inv := by
      rintro ⟨x, hx⟩
      cases x with
      | inl x => rfl
      | inr x => exact False.elim (by simp [B] at hx)
    right_inv := fun _ => rfl }
  change B.IsRegularOfDegree r
  intro v
  rw [← card_neighborSet_eq_degree]
  cases v with
  | inl u => simpa only [Fintype.card_fin] using Fintype.card_congr (left u)
  | inr u => simpa only [Fintype.card_fin] using Fintype.card_congr (right u)

/-- The conjectured inequality holds when the allowed error is at least 1/r. -/
theorem large_error (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 1 / (r : ℝ) ≤ ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε) := by
  classical
  let B := completeBipartiteGraph (Fin r) (Fin r)
  let e : Fin r ⊕ Fin r ≃ Fin (r + r) := finSumFinEquiv
  let H := B.map e
  let iso : B ≃g H := Iso.map e B
  refine ⟨r + r, H, by omega, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ : ∃ u, iso u = v := iso.toEquiv.surjective v
    rw [← hu]
    have hcard : H.degree (iso u) = B.degree u := by
      rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
      convert! (Fintype.card_congr (iso.mapNeighborSet u)).symm
    convert! hcard.trans (balanced_biclique_regular r u)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : 0 ≤ 1 - 1 / (r : ℝ) := sub_nonneg.mpr ((div_le_one (by positivity)).2 hrR)
  have hB := extremal_of_degree_threshold B ha (by positivity : 0 ≤ 2 * (r : ℝ))
    (fun _ _ _ G hG => contains_balanced_biclique G hr hG)
  have hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 - 1 / (r : ℝ) + 1) := by
    simpa only [extremalNumber_congr rfl iso.symm] using hB
  apply hH.trans
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  apply Real.rpow_le_rpow_of_exponent_le hnR
  have htwo : 2 / (r : ℝ) = 2 * (1 / (r : ℝ)) := by ring
  linarith

/-- An edge-maximal cut preserves at least half the degree of every vertex. -/
theorem exists_bipartite_half_degrees {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ B : SimpleGraph V, B ≤ G ∧ B.IsBipartite ∧ ∀ v, G.degree v ≤ 2 * B.degree v := by
  classical
  let side (c : V → Bool) : Set V := {v | c v = true}
  let cut (c : V → Bool) := G.between (side c) (side c)ᶜ
  have hcut (c : V → Bool) (u w : V) : (cut c).Adj u w ↔ G.Adj u w ∧ c u ≠ c w := by
    simp only [cut, between_adj, side, Set.mem_ofPred_eq, Set.mem_compl_iff]
    cases c u <;> cases c w <;> simp
  obtain ⟨c, hc⟩ := Finite.exists_max (fun c : V → Bool => (cut c).edgeFinset.card)
  refine ⟨cut c, between_le, between_isBipartite disjoint_compl_right, ?_⟩
  intro v
  let flip : V → Bool := fun w => if w = v then !(c w) else c w
  have hsplit (B : SimpleGraph V) :
      (B.deleteIncidenceSet v).edgeFinset.card + B.degree v = B.edgeFinset.card := by
    rw [card_edgeFinset_deleteIncidenceSet, Nat.sub_add_cancel (B.degree_le_card_edgeFinset v)]
  have hrest : (cut flip).deleteIncidenceSet v = (cut c).deleteIncidenceSet v := by
    ext a b
    simp only [deleteIncidenceSet_adj, hcut]
    by_cases ha : a = v
    · simp [ha]
    by_cases hb : b = v
    · simp [hb]
    simp [flip, ha, hb]
  have hdr : (cut flip).degree v ≤ (cut c).degree v := by
    have hrc : ((cut flip).deleteIncidenceSet v).edgeFinset.card =
        ((cut c).deleteIncidenceSet v).edgeFinset.card := by
      convert! congrArg (fun B : SimpleGraph V => B.edgeFinset.card) hrest
    have hm : ((cut flip).deleteIncidenceSet v).edgeFinset.card + (cut flip).degree v ≤
        ((cut c).deleteIncidenceSet v).edgeFinset.card + (cut c).degree v := by
      calc
        _ = (cut flip).edgeFinset.card := by convert! hsplit (cut flip)
        _ ≤ (cut c).edgeFinset.card := by convert! hc flip
        _ = _ := by convert! (hsplit (cut c)).symm
    omega
  have hfirst : (cut c).neighborFinset v = (G.neighborFinset v).filter (fun w => c v ≠ c w) := by
    ext w
    simp only [mem_neighborFinset, mem_filter, hcut]
  have hsecond :
      (cut flip).neighborFinset v = (G.neighborFinset v).filter (fun w => ¬c v ≠ c w) := by
    ext w
    simp only [mem_neighborFinset, mem_filter, hcut]
    by_cases hw : G.Adj v w
    · simp only [hw, true_and, flip, if_pos rfl, if_neg hw.ne.symm]
      cases c v <;> cases c w <;> simp
    · simp [hw]
  have hsum : (cut c).degree v + (cut flip).degree v = G.degree v := by
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      ← card_neighborFinset_eq_degree, hfirst, hsecond, card_filter_add_card_filter_not]
  have hfinal := hsum.symm.trans_le (Nat.add_le_add_left hdr ((cut c).degree v))
  rw [← two_mul] at hfinal
  convert! hfinal

/-- In an extremal application it suffices to find the copy in bipartite hosts. -/
theorem extremal_of_bipartite_degree_threshold {W : Type} (H : SimpleGraph W) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (force : ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V), G.IsBipartite →
      (∀ v, C * (Fintype.card V : ℝ) ^ a < (G.degree v : ℝ)) → H ⊑ G) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (a + 1) := by
  classical
  apply extremal_of_degree_threshold H ha (C := 2 * C) (by positivity)
  intro V _ _ G hd
  obtain ⟨B, hle, hb, hhalf⟩ := exists_bipartite_half_degrees G
  refine (force V B hb ?_).trans (.of_le hle)
  intro v
  have hhalfR : (G.degree v : ℝ) ≤ 2 * (B.degree v : ℝ) := by exact_mod_cast hhalf v
  have h := (hd v).trans_le hhalfR
  linarith

/-- Common neighbors of a finite set in a bipartite relation. -/
noncomputable def relationCommon {A B : Type} [Fintype B] (R : A → B → Prop)
    (s : Finset A) : Finset B :=
  univ.filter fun b => ∀ a ∈ s, R a b

/-- Count incidences between k-subsets on one side and their common neighbors. -/
theorem sum_card_relationCommon {A B : Type} [Fintype A] [Fintype B]
    (R : A → B → Prop) (k : ℕ) :
    (∑ s ∈ (univ : Finset A).powersetCard k, (relationCommon R s).card) =
      ∑ b : B, ((univ.filter fun a => R a b).card).choose k := by
  classical
  let sets := (univ : Finset A).powersetCard k
  let nb (b : B) := univ.filter fun a => R a b
  calc
    _ = ∑ s ∈ sets, ∑ b : B, if s ⊆ nb b then 1 else 0 := by
      apply sum_congr rfl
      intro s _
      rw [← card_filter]
      congr 1
      ext b
      simp [relationCommon, nb, subset_iff]
    _ = ∑ b : B, ∑ s ∈ sets, if s ⊆ nb b then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro b _
      rw [← card_filter]
      have h : sets.filter (· ⊆ nb b) = (nb b).powersetCard k := by
        ext s
        simp [sets, mem_powersetCard, and_comm]
      rw [h, card_powersetCard]

private theorem choose_two_real (n : ℕ) :
    2 * (n.choose 2 : ℝ) = (n : ℝ) ^ 2 - n := by
  have hN : 2 * n.choose 2 = n * (n - 1) := by
    simpa [Nat.descFactorial_succ, Nat.factorial_succ, Nat.mul_comm] using
      (Nat.descFactorial_eq_factorial_mul_choose n 2).symm
  cases n with
  | zero => norm_num
  | succ n =>
    simp only [Nat.add_sub_cancel] at hN
    have hR : 2 * ((n + 1).choose 2 : ℝ) = ((n : ℝ) + 1) * n := by
      exact_mod_cast hN
    rw [hR, Nat.cast_succ]
    ring

/-- When the average is at least two, distinct pairs retain a fixed fraction of the second moment. -/
theorem sum_choose_two_lower {A : Type} (s : Finset A) (hs : s.Nonempty) (d : A → ℕ)
    (hm : 2 * (s.card : ℝ) ≤ ∑ a ∈ s, (d a : ℝ)) :
    (∑ a ∈ s, (d a : ℝ)) ^ 2 / (4 * s.card) ≤
      ∑ a ∈ s, ((d a).choose 2 : ℝ) := by
  have hsR : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr hs
  have hcs := sum_mul_sq_le_sq_mul_sq s (fun a => (d a : ℝ)) (fun _ => (1 : ℝ))
  simp only [one_pow, sum_const, nsmul_eq_mul, mul_comm _ (1 : ℝ), one_mul] at hcs
  have hchoose : 2 * (∑ a ∈ s, ((d a).choose 2 : ℝ)) =
      (∑ a ∈ s, (d a : ℝ) ^ 2) - ∑ a ∈ s, (d a : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun a _ => choose_two_real (d a)
  rw [div_le_iff₀ (by positivity)]
  have hdiff : 0 ≤ (∑ a ∈ s, (d a : ℝ)) * ((∑ a ∈ s, (d a : ℝ)) - 2 * s.card) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hm)
  nlinarith only [hcs, hdiff, congrArg (fun x : ℝ => (s.card : ℝ) * x) hchoose]

/-- A lower bound for the number of rectangles with distinct corners on each side. -/
theorem rectangles_lower_bound {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (R : A → B → Prop) (hA : 2 ≤ Fintype.card A)
    (m : ℝ) (hm : m = ∑ b : B, ((univ.filter fun a => R a b).card : ℝ))
    (hB : 2 * (Fintype.card B : ℝ) ≤ m)
    (hdense : 8 * (Fintype.card A : ℝ) ^ 2 * Fintype.card B ≤ m ^ 2) :
    m ^ 4 / (64 * (Fintype.card A : ℝ) ^ 2 * (Fintype.card B : ℝ) ^ 2) ≤
      ∑ s ∈ (univ : Finset A).powersetCard 2, (((relationCommon R s).card).choose 2 : ℝ) := by
  classical
  let S := (univ : Finset A).powersetCard 2
  let p : ℝ := Fintype.card A
  let q : ℝ := Fintype.card B
  let k : ℝ := S.card
  let u : ℝ := ∑ s ∈ S, ((relationCommon R s).card : ℝ)
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := B)
  have hp : 0 < p := by
    dsimp [p]
    exact_mod_cast (show 0 < Fintype.card A by omega)
  have hS : S.Nonempty := by
    rw [← card_pos, card_powersetCard, card_univ]
    exact Nat.choose_pos hA
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hS.card_pos
  have hkp : k ≤ p ^ 2 := by
    dsimp [k, p, S]
    rw [card_powersetCard, card_univ]
    exact_mod_cast Nat.choose_le_pow (Fintype.card A) 2
  have hsum : u = ∑ b : B, (((univ.filter fun a => R a b).card).choose 2 : ℝ) := by
    dsimp [u, S]
    exact_mod_cast sum_card_relationCommon R 2
  have hb : m ^ 2 / (4 * q) ≤ u := by
    rw [hsum, hm]
    exact sum_choose_two_lower univ univ_nonempty _ (by simpa [hm] using hB)
  have hku : 2 * k ≤ u := by
    apply le_trans _ hb
    rw [le_div_iff₀ (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hkp (show 0 ≤ q by positivity)
    change 8 * p ^ 2 * q ≤ m ^ 2 at hdense
    nlinarith only [hdense, hmul]
  have hc := sum_choose_two_lower S hS (fun s => (relationCommon R s).card) hku
  change u ^ 2 / (4 * k) ≤ _ at hc
  apply le_trans _ hc
  calc
    m ^ 4 / (64 * p ^ 2 * q ^ 2) = (m ^ 2 / (4 * q)) ^ 2 / (4 * p ^ 2) := by
      ring
    _ ≤ u ^ 2 / (4 * p ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hb 2
    _ ≤ u ^ 2 / (4 * k) :=
      div_le_div_of_nonneg_left (sq_nonneg u) (by positivity)
        (mul_le_mul_of_nonneg_left hkp (by norm_num))

theorem mem_relationCommon {A B : Type} [Fintype B] {R : A → B → Prop}
    {s : Finset A} {b : B} :
    b ∈ relationCommon R s ↔ ∀ a ∈ s, R a b := by
  classical
  simp [relationCommon]

/-- Edges of a bipartite relation, with the left endpoint first. -/
abbrev RelationEdge {A B : Type} (R : A → B → Prop) :=
  {p : A × B // R p.1 p.2}

/-- Two edges are adjacent when they are opposite edges of a rectangle with distinct corners. -/
def rectangleGraph {A B : Type} (R : A → B → Prop) : SimpleGraph (RelationEdge R) where
  Adj e f := e.val.1 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2 ∧ R e.val.1 f.val.2 ∧ R f.val.1 e.val.2
  symm.symm := fun _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.2.2, h.2.2.1⟩
  loopless.irrefl := fun _ h => h.1 rfl

/-- Every distinct rectangle contributes an ordered adjacent pair in the edge graph. -/
theorem sum_rectangleGraph_degree_ge {A B : Type} [Fintype A] [Fintype B]
    (R : A → B → Prop) :
    (∑ s ∈ (univ : Finset A).powersetCard 2, ((relationCommon R s).card).choose 2) ≤
      ∑ e : RelationEdge R, (rectangleGraph R).degree e := by
  classical
  let S := (univ : Finset A).powersetCard 2
  let T (s : Finset A) := (relationCommon R s).powersetCard 2
  let E := RelationEdge R
  let Q := rectangleGraph R
  let target := Σ e : E, Q.neighborSet e
  have cardT : (S.sigma T).card = ∑ s ∈ S, ((relationCommon R s).card).choose 2 := by
    rw [card_sigma]
    exact sum_congr rfl fun s _ => card_powersetCard _ _
  have locate (x : ↥(S.sigma T)) : ∃ y : target,
      {y.1.val.1, y.2.val.val.1} = x.val.1 ∧ {y.1.val.2, y.2.val.val.2} = x.val.2 := by
    obtain ⟨⟨s, t⟩, hmem⟩ := x
    have hst := mem_sigma.mp hmem
    have hs : s.card = 2 := (mem_powersetCard.mp hst.1).2
    have ht : t.card = 2 := (mem_powersetCard.mp hst.2).2
    have hct : t ⊆ relationCommon R s := (mem_powersetCard.mp hst.2).1
    obtain ⟨a, a', hAA, rfl⟩ := card_eq_two.mp hs
    obtain ⟨b, b', hBB, rfl⟩ := card_eq_two.mp ht
    have hab (u : A) (hu : u ∈ ({a, a'} : Finset A))
        (w : B) (hw : w ∈ ({b, b'} : Finset B)) : R u w :=
      (mem_relationCommon.mp (hct hw)) u hu
    let e : E := ⟨(a, b), hab a (by simp) b (by simp)⟩
    let f : E := ⟨(a', b'), hab a' (by simp) b' (by simp)⟩
    have hef : Q.Adj e f :=
      ⟨hAA, hBB, hab a (by simp) b' (by simp), hab a' (by simp) b (by simp)⟩
    refine ⟨⟨e, ⟨f, hef⟩⟩, ?_, ?_⟩
    · rfl
    · rfl
  choose f h₁ h₂ using locate
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    have hx₁ := (h₁ x).symm.trans ((congrArg (fun z : target => {z.1.val.1, z.2.val.val.1}) he).trans (h₁ y))
    have hx₂ := (h₂ x).symm.trans ((congrArg (fun z : target => {z.1.val.2, z.2.val.val.2}) he).trans (h₂ y))
    exact Sigma.ext hx₁ (heq_of_eq hx₂)
  have hcard := Fintype.card_le_of_injective _ hf
  rw [Fintype.card_coe, cardT, Fintype.card_sigma] at hcard
  simpa only [card_neighborSet_eq_degree] using hcard

/-- Ordered tuples from a finite set with no conflicting pair. -/
noncomputable def packedTuples {E : Type} [Fintype E] (s : Finset E)
    (conflict : E → E → Prop) (t : ℕ) : Finset (Fin t → E) :=
  (Fintype.piFinset (fun _ : Fin t => s)).filter fun x =>
    ∀ i j, i < j → ¬ conflict (x i) (x j)

theorem mem_packedTuples {E : Type} [Fintype E] {s : Finset E}
    {conflict : E → E → Prop} {t : ℕ} {x : Fin t → E} :
    x ∈ packedTuples s conflict t ↔ (∀ i, x i ∈ s) ∧
       (∀ i j, i < j → ¬ conflict (x i) (x j)) := by
  classical
  simp [packedTuples]

private noncomputable def compatibleHeads {E : Type} (s : Finset E)
    (conflict : E → E → Prop) {t : ℕ} (x : Fin t → E) : Finset E :=
  s.filter fun a => ∀ i, ¬ conflict a (x i)

private theorem sigma_subtype_ext {A B : Type} {P : A → B → Prop}
    {x y : Σ a : A, {b : B // P a b}} (h : x.1 = y.1) (h' : x.2.val = y.2.val) :
    x = y := by
  rcases x with ⟨x, ⟨a, ha⟩⟩
  rcases y with ⟨y, ⟨b, hb⟩⟩
  change x = y at h
  change a = b at h'
  subst y
  subst b
  rfl

private theorem card_packedTuples_succ {E : Type} [Fintype E] (s : Finset E)
    (conflict : E → E → Prop) (t : ℕ) :
    (packedTuples s conflict (t + 1)).card =
      ∑ x ∈ packedTuples s conflict t, (compatibleHeads s conflict x).card := by
  classical
  let long := ↥(packedTuples s conflict (t + 1))
  let short := ↥(packedTuples s conflict t)
  let e : long ≃ Σ x : short, ↥(compatibleHeads s conflict x.val) := by
    refine {
      toFun := fun x => ⟨⟨Fin.tail x.val, ?_⟩, ⟨x.val 0, ?_⟩⟩
      invFun := fun y => ⟨Fin.cons y.2.val y.1.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · have h := mem_packedTuples.mp x.prop
      exact mem_packedTuples.mpr
        ⟨fun i => h.1 i.succ, fun i j hij => h.2 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)⟩
    · have h := mem_packedTuples.mp x.prop
      apply mem_filter.mpr
      exact ⟨h.1 0, fun i => h.2 0 i.succ (Fin.succ_pos i)⟩
    · have hx := mem_packedTuples.mp y.1.prop
      have hy := mem_filter.mp y.2.prop
      apply mem_packedTuples.mpr
      constructor
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hy.1
        · simpa using hx.1 j
      · intro i j hij
        revert hij
        refine Fin.cases (fun j hj => ?_) (fun i j hj => ?_) i j
        · revert hj
          refine Fin.cases ?_ (fun j hj => ?_) j
          · simp
          · simpa using hy.2 j
        · revert hj
          refine Fin.cases ?_ (fun j hj => ?_) j
          · simp
          · simpa using hx.2 i j (Fin.succ_lt_succ_iff.mp hj)
    · intro x
      apply Subtype.ext
      simp
    · rintro ⟨x, a⟩
      apply sigma_subtype_ext
      · apply Subtype.ext
        simp
      · simp
  have hc := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_sigma] at hc
  calc
    _ = ∑ x : short, (compatibleHeads s conflict x.val).card := by
      simpa only [Fintype.card_coe] using hc
    _ = _ := by
      exact Finset.sum_coe_sort
        (f := fun (x : Fin t → E) => (compatibleHeads s conflict x).card)
        (s := packedTuples s conflict t)

/-- If each element conflicts with at most B choices, greedy packing retains a power lower bound. -/
theorem card_packedTuples_lower {E : Type} [Fintype E] (s : Finset E)
    (conflict : E → E → Prop) (B t : ℕ)
    (hB : ∀ b ∈ s, (s.filter fun a => conflict a b).card ≤ B) :
    (s.card - t * B) ^ t ≤ (packedTuples s conflict t).card := by
  classical
  induction t with
  | zero =>
    simp [packedTuples]
  | succ t ih =>
    let lower := s.card - (t + 1) * B
    have hshift : lower ≤ s.card - t * B := by
      dsimp [lower]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
    have hheads (x : Fin t → E) (hx : x ∈ packedTuples s conflict t) :
        lower ≤ (compatibleHeads s conflict x).card := by
      have hxs := (mem_packedTuples.mp hx).1
      let bad := (univ : Finset (Fin t)).biUnion (fun i => s.filter fun a => conflict a (x i))
      have hbad : bad.card ≤ t * B := by
        apply card_biUnion_le.trans
        calc
          _ ≤ ∑ _i : Fin t, B := sum_le_sum fun i _ => hB _ (hxs i)
          _ = _ := by simp
      have hbadId : bad = s.filter (fun a => ¬ ∀ i, ¬ conflict a (x i)) := by
        ext a
        simp [bad, mem_biUnion, mem_filter, exists_and_left]
      have hsplit : (compatibleHeads s conflict x).card + bad.card = s.card := by
        rw [hbadId, compatibleHeads, card_filter_add_card_filter_not]
      dsimp [lower]
      omega
    rw [card_packedTuples_succ, pow_succ]
    calc
      lower ^ t * lower ≤ (packedTuples s conflict t).card * lower :=
        Nat.mul_le_mul_right _ ((Nat.pow_le_pow_left hshift t).trans ih)
      _ = ∑ _x ∈ packedTuples s conflict t, lower := by simp
      _ ≤ _ := sum_le_sum hheads

/-- A packing that is compatible with a fixed element can be counted in either order. -/
theorem sum_card_packed_neighborhoods {E : Type} [Fintype E]
    (s : Finset E) (R conflict : E → E → Prop) (t : ℕ) :
    (∑ e ∈ s, (packedTuples (s.filter fun f => R f e) conflict t).card) =
      ∑ x ∈ packedTuples s conflict t, (s.filter fun e => ∀ i, R (x i) e).card := by
  classical
  let P := packedTuples s conflict t
  have hfilter (e : E) : packedTuples (s.filter fun f => R f e) conflict t =
      P.filter fun x => ∀ i, R (x i) e := by
    ext x
    simp only [P, mem_packedTuples, mem_filter]
    constructor
    · rintro ⟨hm, hc⟩
      exact ⟨⟨fun i => (hm i).1, hc⟩, fun i => (hm i).2⟩
    · rintro ⟨⟨hm, hc⟩, hr⟩
      exact ⟨fun i => ⟨hm i, hr i⟩, hc⟩
  calc
    _ = ∑ e ∈ s, ∑ x ∈ P, if ∀ i, R (x i) e then 1 else 0 := by
      apply sum_congr rfl
      intro e _
      rw [hfilter, card_filter]
    _ = ∑ x ∈ P, ∑ e ∈ s, if ∀ i, R (x i) e then 1 else 0 := sum_comm
    _ = _ := by simp only [card_filter, P]

private theorem power_mean_le {I : Type} (T : Finset I) (hT : T.Nonempty)
    (f : I → ℝ) (hf : ∀ i ∈ T, 0 ≤ f i) (t : ℕ) :
    (T.card : ℝ) * ((∑ i ∈ T, f i) / T.card) ^ t ≤ ∑ i ∈ T, f i ^ t := by
  let k : ℝ := T.card
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hT.card_pos
  let w : I → ℝ := fun _ => k⁻¹
  have hw : ∑ i ∈ T, w i = 1 := by
    simp only [w, sum_const, nsmul_eq_mul]
    change k * k⁻¹ = 1
    exact mul_inv_cancel₀ hk.ne'
  have h := (convexOn_pow (𝕜 := ℝ) t).map_sum_le (t := T)
    (w := w) (p := f) (fun _ _ => inv_nonneg.mpr hk.le) hw hf
  simp only [w, smul_eq_mul, ← mul_sum] at h
  rw [← div_eq_inv_mul, ← div_eq_inv_mul] at h
  simpa only [mul_comm _ k] using (le_div_iff₀ hk).mp h

/-- An average neighborhood size yields a lower bound for the total number of packings. -/
theorem sum_card_packed_lower {I E : Type} [Fintype E] (T : Finset I) (hT : T.Nonempty)
    (s : I → Finset E) (conflict : E → E → Prop) (B t : ℕ) (d : ℝ)
    (hd : (t : ℝ) * B ≤ d)
    (hmean : (T.card : ℝ) * d ≤ ∑ i ∈ T, ((s i).card : ℝ))
    (hB : ∀ i ∈ T, ∀ b ∈ s i, ((s i).filter fun a => conflict a b).card ≤ B) :
    (T.card : ℝ) * (d - (t : ℝ) * B) ^ t ≤
      ∑ i ∈ T, ((packedTuples (s i) conflict t).card : ℝ) := by
  let f : I → ℝ := fun i => ↑((s i).card - t * B)
  have hTpos : 0 < (T.card : ℝ) := by exact_mod_cast hT.card_pos
  have hf (i : I) : (s i).card - (t : ℝ) * B ≤ f i := by
    dsimp [f]
    rw [← Nat.cast_mul]
    by_cases h : t * B ≤ (s i).card
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), Nat.cast_zero]
      exact sub_nonpos.mpr (by exact_mod_cast le_of_not_ge h)
  have hsum := sum_le_sum (fun i hi => hf i : ∀ i ∈ T, _)
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
  have hmean' : d - (t : ℝ) * B ≤ (∑ i ∈ T, f i) / T.card := by
    apply (le_div_iff₀ hTpos).2
    linarith only [hsum, hmean]
  calc
    _ ≤ (T.card : ℝ) * ((∑ i ∈ T, f i) / T.card) ^ t :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr hd) hmean' t) hTpos.le
    _ ≤ ∑ i ∈ T, f i ^ t := power_mean_le T hT f (fun _ _ => by positivity) t
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      dsimp [f]
      exact_mod_cast card_packedTuples_lower (s i) conflict B t (hB i hi)

/-- Marking one coordinate of a packing costs at most its unrestricted coordinate count. -/
theorem card_packedTuples_filter_hit_le {E : Type} [Fintype E] (s : Finset E)
    (conflict : E → E → Prop) (t : ℕ) (P : E → Prop) :
    ((packedTuples s conflict t).filter fun x => ∃ i, P (x i)).card ≤
      t * (s.filter P).card * s.card ^ (t - 1) := by
  classical
  let U (i : Fin t) := Fintype.piFinset (Function.update (fun _ : Fin t => s) i (s.filter P))
  have hsub : (packedTuples s conflict t).filter (fun x => ∃ i, P (x i)) ⊆ univ.biUnion U := by
    intro x hx
    obtain ⟨hx, i, hi⟩ := mem_filter.mp hx
    have hxs := (mem_packedTuples.mp hx).1
    refine mem_biUnion.mpr ⟨i, mem_univ i, Fintype.mem_piFinset.mpr fun j => ?_⟩
    obtain rfl | hji := eq_or_ne j i
    · simp [hxs, hi]
    · simp [Function.update_of_ne hji, hxs]
  have hcard (i : Fin t) : (U i).card = (s.filter P).card * s.card ^ (t - 1) := by
    dsimp [U]
    rw [Fintype.card_piFinset]
    calc
      _ = ∏ j : Fin t, Function.update (fun _ : Fin t => s.card) i (s.filter P).card j := by
        apply Fintype.prod_congr
        intro j
        obtain rfl | hji := eq_or_ne j i <;> simp [*]
      _ = _ := by
        rw [prod_update_of_mem (mem_univ i)]
        simp only [sdiff_singleton_eq_erase, prod_const, card_erase_of_mem (mem_univ i),
          card_univ, Fintype.card_fin]
  calc
    _ ≤ (univ.biUnion U).card := card_le_card hsub
    _ ≤ ∑ i : Fin t, (U i).card := card_biUnion_le
    _ = _ := by simp [hcard, mul_assoc]

/-- Two oriented edges conflict if they use the same vertex on either side. -/
def edgeConflict {A B : Type} {R : A → B → Prop} (e f : RelationEdge R) : Prop :=
  e.val.1 = f.val.1 ∨ e.val.2 = f.val.2

/-- Edges lying opposite every edge in a tuple of rectangles. -/
noncomputable def commonRectangleEdges {A B : Type} [Fintype A] [Fintype B]
    (R : A → B → Prop) {t : ℕ} (x : Fin t → RelationEdge R) : Finset (RelationEdge R) :=
  univ.filter fun e => ∀ i, (rectangleGraph R).Adj (x i) e

theorem mem_commonRectangleEdges {A B : Type} [Fintype A] [Fintype B]
    {R : A → B → Prop} {t : ℕ} {x : Fin t → RelationEdge R} {e : RelationEdge R} :
    e ∈ commonRectangleEdges R x ↔ ∀ i, (rectangleGraph R).Adj (x i) e := by
  classical
  simp [commonRectangleEdges]

private theorem card_endpoint_fiber_le {A B E : Type} [Fintype B]
    (R : A → B → Prop) (left : E → A) (right : E → B)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (s : Finset E) {t L : ℕ} (x : Fin t → A) (hx : Function.Injective x)
    (hs : ∀ e ∈ s, R (left e) (right e) ∧ ∀ i, x i ≠ left e ∧ R (x i) (right e))
    (hcodeg : ∀ u : Finset A, u.card = t + 1 → (relationCommon R u).card ≤ L)
    (z : A) :
    (s.filter fun e => left e = z).card ≤ L := by
  classical
  let u := (univ : Finset (Fin t)).image x
  by_cases hz : z ∈ u
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hz
    have hempty : s.filter (fun e => left e = x i) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨hm, hl⟩ := mem_filter.mp he
      exact ((hs e hm).2 i).1 hl.symm
    simp [hempty]
  · have hu : (insert z u).card = t + 1 := by
      rw [card_insert_of_notMem hz, card_image_of_injective _ hx, card_univ, Fintype.card_fin]
    apply le_trans _ (hcodeg (insert z u) hu)
    apply card_le_card_of_injOn right
    · intro e he
      obtain ⟨hm, hl⟩ := mem_filter.mp (Finset.mem_coe.mp he)
      apply Finset.mem_coe.mpr
      refine mem_relationCommon.mpr fun a ha => ?_
      rcases mem_insert.mp ha with rfl | ha
      · rw [← hl]
        exact (hs e hm).1
      · obtain ⟨i, _, rfl⟩ := mem_image.mp ha
        exact ((hs e hm).2 i).2
    · intro e he f hf h
      have he' := (mem_filter.mp (Finset.mem_coe.mp he)).2
      have hf' := (mem_filter.mp (Finset.mem_coe.mp hf)).2
      exact hinj (Prod.ext (he'.trans hf'.symm) h)

/-- In the bounded-codegree regime each original vertex is incident to few common rectangle edges. -/
theorem commonRectangleEdges_conflict_le {A B : Type} [Fintype A] [Fintype B]
    (R : A → B → Prop) {t L : ℕ} (x : Fin t → RelationEdge R)
    (hxA : Function.Injective fun i => (x i).val.1)
    (hxB : Function.Injective fun i => (x i).val.2)
    (hA : ∀ u : Finset A, u.card = t + 1 → (relationCommon R u).card ≤ L)
    (hB : ∀ u : Finset B, u.card = t + 1 → (relationCommon (Function.swap R) u).card ≤ L)
    (f : RelationEdge R) :
    ((commonRectangleEdges R x).filter fun e => edgeConflict e f).card ≤ 2 * L := by
  classical
  let S := commonRectangleEdges R x
  have hLeft : (S.filter fun e => e.val.1 = f.val.1).card ≤ L := by
    apply card_endpoint_fiber_le R (fun e => e.val.1) (fun e => e.val.2)
      Subtype.val_injective S (fun i => (x i).val.1) hxA _ hA
    intro e he
    refine ⟨e.property, fun i => ?_⟩
    have h := mem_commonRectangleEdges.mp he i
    exact ⟨h.1, h.2.2.1⟩
  have hRight : (S.filter fun e => e.val.2 = f.val.2).card ≤ L := by
    apply card_endpoint_fiber_le (Function.swap R) (fun e => e.val.2) (fun e => e.val.1)
      (Prod.swap_injective.comp Subtype.val_injective) S (fun i => (x i).val.2) hxB _ hB
    intro e he
    refine ⟨e.property, fun i => ?_⟩
    have h := mem_commonRectangleEdges.mp he i
    exact ⟨h.2.1, h.2.2.2⟩
  have hEq : (S.filter fun e => edgeConflict e f) =
      (S.filter fun e => e.val.1 = f.val.1) ∪ (S.filter fun e => e.val.2 = f.val.2) := by
    unfold edgeConflict
    convert! (Finset.filter_or (p := fun e : RelationEdge R => e.val.1 = f.val.1)
      (q := fun e => e.val.2 = f.val.2) S)
  change (S.filter fun e => edgeConflict e f).card ≤ 2 * L
  rw [hEq]
  exact (card_union_le _ _).trans (by omega)

/-- Prune a finite relation to a nonempty set on which every vertex meets its own degree threshold. -/
theorem exists_degree_core {E : Type} (S : Finset E) (R : E → E → Prop) (w : E → ℝ)
    (hsym : ∀ ⦃x y⦄, R x y → R y x) (hirr : ∀ x, ¬ R x x)
    (hdense : 2 * ∑ x ∈ S, w x < ∑ x ∈ S, ((S.filter (R x)).card : ℝ)) :
    ∃ T ⊆ S, T.Nonempty ∧ ∀ x ∈ T, w x ≤ ((T.filter (R x)).card : ℝ) := by
  classical
  let d (T : Finset E) (x : E) : ℝ := ∑ y ∈ T, if R x y then 1 else 0
  have hd (T : Finset E) (x : E) : d T x = (T.filter (R x)).card := by
    simp only [d, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  let score (T : Finset E) := (∑ x ∈ T, d T x) - 2 * ∑ x ∈ T, w x
  obtain ⟨T, hTS, hmax⟩ := exists_max_image S.powerset score
    ⟨∅, mem_powerset.mpr (empty_subset _)⟩
  have hsub := mem_powerset.mp hTS
  have hpos : 0 < score T := by
    apply lt_of_lt_of_le _ (hmax S (mem_powerset.mpr le_rfl))
    dsimp [score]
    simp_rw [hd]
    linarith only [hdense]
  have hne : T.Nonempty := by
    by_contra! h
    simp [score, h] at hpos
  refine ⟨T, hsub, hne, ?_⟩
  intro x hx
  let U := T.erase x
  have hUS : U ∈ S.powerset := mem_powerset.mpr ((erase_subset x T).trans hsub)
  have hw : ∑ y ∈ U, w y = (∑ y ∈ T, w y) - w x := by
    exact eq_sub_of_add_eq (sum_erase_add _ _ hx)
  have hds (y : E) : d T y = d U y + (if R y x then 1 else 0) := by
    exact (sum_erase_add _ _ hx).symm
  have hflip : (∑ y ∈ U, if R y x then (1 : ℝ) else 0) = d T x := by
    calc
      _ = d U x := by
        apply sum_congr rfl
        intro y _
        have hiff : R y x ↔ R x y := ⟨fun h => hsym h, fun h => hsym h⟩
        rw [hiff]
      _ = d T x := by simpa [hirr x] using (hds x).symm
  have hdsum : (∑ y ∈ U, d T y) = (∑ y ∈ U, d U y) + d T x := by
    rw [← hflip, ← sum_add_distrib]
    exact sum_congr rfl (fun y _ => hds y)
  have hsum : ∑ y ∈ T, d T y = (∑ y ∈ U, d U y) + 2 * d T x := by
    calc
      _ = (∑ y ∈ U, d T y) + d T x := (sum_erase_add _ _ hx).symm
      _ = _ := by rw [hdsum]; ring
  have hless := hmax U hUS
  change (∑ y ∈ U, d U y) - 2 * ∑ y ∈ U, w y ≤
    (∑ y ∈ T, d T y) - 2 * ∑ y ∈ T, w y at hless
  rw [hw, hsum] at hless
  rw [← hd]
  linarith only [hless]

/-- The common neighborhood for simultaneous adjacency of two oriented matchings. -/
def simultaneousRectangles {A B : Type} (R : A → B → Prop) {t : ℕ}
    (x y : Fin t → RelationEdge R) : Prop :=
  ∀ i j, (rectangleGraph R).Adj (x i) (y j)

theorem packed_neighbors_eq {A B : Type} [Fintype A] [Fintype B] (R : A → B → Prop)
    {t : ℕ} (x : Fin t → RelationEdge R) :
    let P := packedTuples (univ : Finset (RelationEdge R)) edgeConflict t
    P.filter (simultaneousRectangles R x) =
      packedTuples (commonRectangleEdges R x) edgeConflict t := by
  classical
  intro P
  ext y
  simp only [P, mem_filter, mem_packedTuples, mem_univ, implies_true, true_and,
    mem_commonRectangleEdges, simultaneousRectangles]
  tauto

theorem packed_endpoints_injective {A B : Type} [Fintype A] [Fintype B] (R : A → B → Prop)
    {t : ℕ} {x : Fin t → RelationEdge R}
    (hx : x ∈ packedTuples univ edgeConflict t) :
    (Function.Injective fun i => (x i).val.1) ∧ (Function.Injective fun i => (x i).val.2) := by
  have sep (i j : Fin t) (h : i ≠ j) : ¬ edgeConflict (x i) (x j) := by
    rcases lt_or_gt_of_ne h with hij | hji
    · exact (mem_packedTuples.mp hx).2 i j hij
    · intro hc
      exact (mem_packedTuples.mp hx).2 j i hji (hc.elim (Or.inl ∘ Eq.symm) (Or.inr ∘ Eq.symm))
  exact ⟨fun _ _ h => by_contra fun h' => sep _ _ h' (.inl h),
    fun _ _ h => by_contra fun h' => sep _ _ h' (.inr h)⟩

/-- Overlap of oriented matchings means overlap in at least one original vertex. -/
def packedOverlap {A B : Type} {R : A → B → Prop} {t : ℕ}
    (x y : Fin t → RelationEdge R) : Prop :=
  ∃ i j, edgeConflict (y j) (x i)

private theorem packed_size_le {E : Type} [Fintype E] (s : Finset E)
    (conflict : E → E → Prop) (t : ℕ) :
    (packedTuples s conflict t).card ≤ s.card ^ t := by
  classical
  unfold packedTuples
  refine (card_filter_le _ _).trans ?_
  rw [Fintype.card_piFinset_const]

/-- A degree sum in the rectangle graph supplies many common rectangle edges of disjoint tuples. -/
theorem sum_commonRectangleEdges_lower {A B : Type} [Fintype A] [Fintype B]
    (R : A → B → Prop) [Nonempty (RelationEdge R)] (t B₀ : ℕ) (d : ℝ)
    (hd : (t : ℝ) * B₀ ≤ d)
    (hmean : (Fintype.card (RelationEdge R) : ℝ) * d ≤
      ∑ e : RelationEdge R, ((rectangleGraph R).degree e : ℝ))
    (hconf : ∀ e f : RelationEdge R,
      (((rectangleGraph R).neighborFinset e).filter fun g => edgeConflict g f).card ≤ B₀) :
    (Fintype.card (RelationEdge R) : ℝ) * (d - (t : ℝ) * B₀) ^ t ≤
      ∑ x ∈ packedTuples univ edgeConflict t, ((commonRectangleEdges R x).card : ℝ) := by
  classical
  let Q := rectangleGraph R
  let nbh (e : RelationEdge R) := univ.filter fun f => Q.Adj f e
  have hnbh (e : RelationEdge R) : nbh e = Q.neighborFinset e := by
    ext f
    simp [nbh, mem_neighborFinset, adj_comm]
  have h := sum_card_packed_lower univ univ_nonempty nbh edgeConflict B₀ t d hd
    (by simpa only [card_univ, hnbh, card_neighborFinset_eq_degree] using hmean)
    (fun e _ f _ => by simpa only [hnbh] using hconf e f)
  have hcast : (∑ e : RelationEdge R, ((packedTuples (nbh e) edgeConflict t).card : ℝ)) =
      ∑ x ∈ packedTuples univ edgeConflict t, ((commonRectangleEdges R x).card : ℝ) := by
    exact_mod_cast sum_card_packed_neighborhoods (univ : Finset (RelationEdge R)) Q.Adj edgeConflict t
  simpa only [card_univ, hcast] using h

/-- Two tuples overlap if some pair of entries conflicts. -/
def tupleOverlap {E : Type} (C : E → E → Prop) {t : ℕ}
    (x y : Fin t → E) : Prop :=
  ∃ i j, C (y j) (x i)

/-- Pack neighborhoods and prune to a core with few neighbors hitting any given tuple. -/
theorem exists_sparse_tuple_core {E : Type} [Fintype E]
    (C : E → E → Prop) (t L θ : ℕ) (ht : 0 < t) (hθ : 0 < θ) (hθL : 4 * t * L ≤ θ)
    (Q : (Fin t → E) → (Fin t → E) → Prop) (common : (Fin t → E) → Finset E)
    (hsym : ∀ ⦃x y⦄, Q x y → Q y x) (hirr : ∀ x, ¬ Q x x)
    (hneighbor : ∀ x, (packedTuples univ C t).filter (Q x) = packedTuples (common x) C t)
    (hcap : ∀ x ∈ packedTuples univ C t, ∀ f, ((common x).filter fun e => C e f).card ≤ 2 * L)
    (hsum : let P := packedTuples (univ : Finset E) C t
      4 * (P.card : ℝ) * ((θ : ℝ) ^ t + 1) <
        ∑ x ∈ P, ((packedTuples (common x) C t).card : ℝ)) :
    ∃ U : Finset (Fin t → E), U ⊆ packedTuples univ C t ∧ U.Nonempty ∧
      ∀ x ∈ U, 0 < (U.filter (Q x)).card ∧
        ∀ f : Fin t → E, θ * (U.filter fun y => Q x y ∧ tupleOverlap C f y).card ≤
          (8 * 2 ^ t * t ^ 2 * L) * (U.filter (Q x)).card := by
  classical
  let P := packedTuples (univ : Finset (E)) C t
  let D (x : Fin t → E) := (P.filter (Q x)).card
  have hD (x : Fin t → E) : D x =
      (packedTuples (common x) C t).card :=
    congrArg Finset.card (hneighbor x)
  let M (x : Fin t → E) := (common x).card
  let w (x : Fin t → E) : ℝ :=
    if θ ≤ M x then (D x : ℝ) / 4 else (D x : ℝ) + 1
  have hw (x : Fin t → E) :
      w x ≤ (D x : ℝ) / 4 + ((θ : ℝ) ^ t + 1) := by
    unfold w
    split_ifs with hx
    · exact le_add_of_nonneg_right (by positivity)
    · have hD' : (D x : ℝ) ≤ (θ : ℝ) ^ t := by
        have h := (hD x).le.trans (packed_size_le (common x) C t)
        exact_mod_cast h.trans (Nat.pow_le_pow_left (le_of_lt (lt_of_not_ge hx)) _)
      have hnonneg : 0 ≤ (D x : ℝ) / 4 := by positivity
      linarith only [hD', hnonneg]
  have hsum' : 4 * (P.card : ℝ) * ((θ : ℝ) ^ t + 1) < ∑ x ∈ P, (D x : ℝ) := by
    simpa only [hD] using hsum
  have hds : 2 * ∑ x ∈ P, w x < ∑ x ∈ P, (D x : ℝ) := by
    have h := sum_le_sum (fun x (_ : x ∈ P) => hw x)
    rw [sum_add_distrib, ← sum_div, sum_const, nsmul_eq_mul] at h
    linarith only [hsum', h]
  obtain ⟨U, hUP, hUne, hU⟩ := exists_degree_core P Q w hsym hirr hds
  refine ⟨U, hUP, hUne, fun x hx => ?_⟩
  let deg := (U.filter (Q x)).card
  have hless : deg ≤ D x := card_le_card (filter_subset_filter _ hUP)
  have hlarge : θ ≤ M x := by
    by_contra! hn
    have h := hU x hx
    change w x ≤ (deg : ℝ) at h
    rw [show w x = (D x : ℝ) + 1 by simp only [w, if_neg (not_le.mpr hn)]] at h
    have h' : (deg : ℝ) ≤ D x := by exact_mod_cast hless
    linarith only [h, h']
  have hquarter : D x ≤ 4 * deg := by
    have h := hU x hx
    change w x ≤ (deg : ℝ) at h
    simp only [w, if_pos hlarge] at h
    exact_mod_cast (show (D x : ℝ) ≤ 4 * deg by linarith only [h])
  let S := common x
  have hBc (f : E) : (S.filter fun e => C e f).card ≤ 2 * L :=
    hcap x (hUP hx) f
  have hfull : (M x - t * (2 * L)) ^ t ≤ D x := by
    rw [hD]
    exact card_packedTuples_lower S C (2 * L) t (fun b _ => hBc b)
  have hshift : M x ≤ 2 * (M x - t * (2 * L)) := by
    have hm : 2 * (t * (2 * L)) ≤ M x := by
      calc
        _ = 4 * t * L := by ring
        _ ≤ _ := hθL.trans hlarge
    omega
  have hpower : (M x) ^ t ≤ 2 ^ t * D x := by
    calc
      _ ≤ (2 * (M x - t * (2 * L))) ^ t := Nat.pow_le_pow_left hshift _
      _ = _ := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ hfull
  have hpos : 0 < deg := by
    have hm : 0 < (M x) ^ t := Nat.pow_pos (hθ.trans_le hlarge)
    by_contra! hz
    have : D x = 0 := by omega
    simp [this] at hpower
    omega
  refine ⟨hpos, fun f => ?_⟩
  let hits (i : Fin t) := (packedTuples S C t).filter fun y => ∃ j, C (y j) (f i)
  have hsub : (U.filter fun y => Q x y ∧ tupleOverlap C f y) ⊆ univ.biUnion hits := by
    intro y hy
    obtain ⟨hyU, hyQ, i, j, hc⟩ := mem_filter.mp hy
    refine mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨?_, ⟨j, hc⟩⟩⟩
    have h : y ∈ P.filter (Q x) := mem_filter.mpr ⟨hUP hyU, hyQ⟩
    rw [hneighbor x] at h
    exact h
  have hhits (i : Fin t) : (hits i).card ≤ t * (2 * L) * (M x) ^ (t - 1) := by
    exact (card_packedTuples_filter_hit_le S C t _).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hBc (f i))))
  have total : (U.filter fun y => Q x y ∧ tupleOverlap C f y).card ≤
      t * (t * (2 * L) * (M x) ^ (t - 1)) := by
    calc
      _ ≤ (univ.biUnion hits).card := card_le_card hsub
      _ ≤ ∑ i : Fin t, (hits i).card := card_biUnion_le
      _ ≤ _ := by simpa using sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin t))) => hhits i)
  calc
    _ ≤ M x * (t * (t * (2 * L) * (M x) ^ (t - 1))) :=
      Nat.mul_le_mul hlarge total
    _ = (2 * t ^ 2 * L) * (M x) ^ t := by
      have hmPow : (M x) ^ t = (M x) ^ (t - 1) * M x :=
        (congrArg (fun k : ℕ => (M x) ^ k) (show t = (t - 1) + 1 by omega)).trans
          (pow_succ _ _)
      rw [hmPow]
      ring
    _ ≤ (2 * t ^ 2 * L) * (2 ^ t * (4 * deg)) :=
      Nat.mul_le_mul_left _ (hpower.trans (Nat.mul_le_mul_left _ hquarter))
    _ = _ := by ring

/-- A rich rectangle graph with bounded codegrees has a core whose local overlaps are sparse. -/
theorem exists_packed_rectangle_core {A B : Type} [Fintype A] [Fintype B] (R : A → B → Prop)
    (t L θ : ℕ) (ht : 0 < t) (hθ : 0 < θ) (hθL : 4 * t * L ≤ θ)
    (hA : ∀ u : Finset A, u.card = t + 1 → (relationCommon R u).card ≤ L)
    (hB : ∀ u : Finset B, u.card = t + 1 → (relationCommon (Function.swap R) u).card ≤ L)
    (hsum : let P := packedTuples (univ : Finset (RelationEdge R)) edgeConflict t
      4 * (P.card : ℝ) * ((θ : ℝ) ^ t + 1) <
        ∑ x ∈ P, ((packedTuples (commonRectangleEdges R x) edgeConflict t).card : ℝ)) :
    ∃ U : Finset (Fin t → RelationEdge R),
      U ⊆ packedTuples univ edgeConflict t ∧ U.Nonempty ∧
      ∀ x ∈ U,
        0 < (U.filter (simultaneousRectangles R x)).card ∧
        ∀ f : Fin t → RelationEdge R,
        θ * (U.filter fun y => simultaneousRectangles R x y ∧ packedOverlap f y).card ≤
          (8 * 2 ^ t * t ^ 2 * L) * (U.filter (simultaneousRectangles R x)).card := by
  classical
  apply exists_sparse_tuple_core edgeConflict t L θ ht hθ hθL
    (simultaneousRectangles R) (commonRectangleEdges R)
    (fun {_ _} h i j => (h j i).symm) (fun x h => (rectangleGraph R).irrefl (h ⟨0, ht⟩ ⟨0, ht⟩))
    (packed_neighbors_eq R) ?_ hsum
  intro x hx f
  obtain ⟨ha, hb⟩ := packed_endpoints_injective R hx
  exact commonRectangleEdges_conflict_le R x ha hb hA hB f

/-- A lower bound on the mean common degree supplies the required packing degree sum. -/
theorem sum_packing_degrees_of_average {E : Type} [Fintype E]
    (P : Finset (Fin t → E)) (hPpos : P.Nonempty)
    (S : (Fin t → E) → Finset E) (C : E → E → Prop) (L θ : ℕ)
    (ht : 0 < t) (hθ : 0 < θ) (hθL : 4 * t * L ≤ θ)
    (hS : (P.card : ℝ) * (10 * θ) ≤ ∑ x ∈ P, ((S x).card : ℝ))
    (hcap : ∀ x ∈ P, ∀ b, ((S x).filter fun a => C a b).card ≤ 2 * L) :
    4 * (P.card : ℝ) * ((θ : ℝ) ^ t + 1) <
      ∑ x ∈ P, ((packedTuples (S x) C t).card : ℝ) := by
  have hθR : (1 : ℝ) ≤ θ := by exact_mod_cast (show 1 ≤ θ from hθ)
  have hcodegR : (t : ℝ) * (2 * L : ℕ) ≤ θ := by
    exact_mod_cast (show t * (2 * L) ≤ θ from
      (show t * (2 * L) ≤ 4 * t * L from calc
        _ ≤ 2 * (t * (2 * L)) := by omega
        _ = _ := by ring).trans hθL)
  have hd' : (t : ℝ) * (2 * L : ℕ) ≤ 10 * θ := by linarith
  have hord := sum_card_packed_lower P hPpos S C (2 * L) t (10 * θ) hd' hS
    (fun x hx b _ => hcap x hx b)
  have hsharp : 4 * ((θ : ℝ) ^ t + 1) < (10 * (θ : ℝ) - (t : ℝ) * (2 * L : ℕ)) ^ t := by
    have hbase : 9 * (θ : ℝ) ≤ 10 * (θ : ℝ) - (t : ℝ) * (2 * L : ℕ) := by linarith
    have h₉ : (9 : ℝ) ≤ (9 : ℝ) ^ t := le_self_pow₀ (by norm_num) (by omega)
    have hθt : 1 ≤ (θ : ℝ) ^ t := one_le_pow₀ hθR
    calc
      _ < 9 * (θ : ℝ) ^ t := by linarith
      _ ≤ (9 * (θ : ℝ)) ^ t := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right h₉ (by positivity)
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase _
  have hp : 0 < (P.card : ℝ) := by exact_mod_cast hPpos.card_pos
  change 4 * (P.card : ℝ) * ((θ : ℝ) ^ t + 1) <
    ∑ x ∈ P, ((packedTuples (S x) C t).card : ℝ)
  rw [mul_comm (4 : ℝ), mul_assoc]
  exact (mul_lt_mul_of_pos_left hsharp hp).trans_le hord

/-- A first-moment condition in the rectangle graph implies the overlap-core criterion. -/
theorem rectangle_core_of_degree_sum {A B : Type} [Fintype A] [Fintype B] (R : A → B → Prop)
    [Nonempty (RelationEdge R)]
    (t L θ B₀ : ℕ) (ht : 0 < t) (hθ : 0 < θ) (hθL : 4 * t * L ≤ θ)
    (d : ℝ) (hd : (t : ℝ) * B₀ ≤ d)
    (hmean : (Fintype.card (RelationEdge R) : ℝ) * d ≤
      ∑ e : RelationEdge R, ((rectangleGraph R).degree e : ℝ))
    (hconf : ∀ e f : RelationEdge R,
      (((rectangleGraph R).neighborFinset e).filter fun g => edgeConflict g f).card ≤ B₀)
    (hpower : 10 * (θ : ℝ) * (Fintype.card (RelationEdge R) : ℝ) ^ (t - 1) ≤
      (d - (t : ℝ) * B₀) ^ t)
    (hA : ∀ u : Finset A, u.card = t + 1 → (relationCommon R u).card ≤ L)
    (hB : ∀ u : Finset B, u.card = t + 1 → (relationCommon (Function.swap R) u).card ≤ L) :
    ∃ U : Finset (Fin t → RelationEdge R),
      U ⊆ packedTuples univ edgeConflict t ∧ U.Nonempty ∧
      ∀ x ∈ U,
        0 < (U.filter (simultaneousRectangles R x)).card ∧
        ∀ f : Fin t → RelationEdge R,
        θ * (U.filter fun y => simultaneousRectangles R x y ∧ packedOverlap f y).card ≤
          (8 * 2 ^ t * t ^ 2 * L) * (U.filter (simultaneousRectangles R x)).card := by
  classical
  apply exists_packed_rectangle_core R t L θ ht hθ hθL hA hB
  let P := packedTuples (univ : Finset (RelationEdge R)) edgeConflict t
  let m : ℝ := Fintype.card (RelationEdge R)
  let S (x : Fin t → RelationEdge R) := commonRectangleEdges R x
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos (α := RelationEdge R)
  have hmpow : m ^ t = m ^ (t - 1) * m :=
    (congrArg (fun k : ℕ => m ^ k) (show t = (t - 1) + 1 by omega)).trans (pow_succ _ _)
  have havg := sum_commonRectangleEdges_lower R t B₀ d hd hmean hconf
  change m * (d - (t : ℝ) * B₀) ^ t ≤ ∑ x ∈ P, ((S x).card : ℝ) at havg
  have hPpos : P.Nonempty := by
    by_contra! h
    rw [h, sum_empty] at havg
    have hh : 0 < (d - (t : ℝ) * B₀) ^ t :=
      (show 0 < 10 * (θ : ℝ) * m ^ (t - 1) by positivity).trans_le hpower
    exact (not_lt_of_ge havg) (mul_pos hm hh)
  have hP : (P.card : ℝ) ≤ m ^ t := by
    have h := packed_size_le (univ : Finset (RelationEdge R)) edgeConflict t
    rw [card_univ] at h
    dsimp [m]
    exact_mod_cast h
  have hS : (P.card : ℝ) * (10 * θ) ≤ ∑ x ∈ P, ((S x).card : ℝ) := by
    calc
      _ ≤ m ^ t * (10 * θ) := mul_le_mul_of_nonneg_right hP (by positivity)
      _ = m * (10 * θ * m ^ (t - 1)) := by rw [hmpow]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hpower hm.le).trans havg
  apply sum_packing_degrees_of_average P hPpos S edgeConflict L θ ht hθ hθL hS
  intro x hx b
  obtain ⟨ha, hb⟩ := packed_endpoints_injective R hx
  exact commonRectangleEdges_conflict_le R x ha hb hA hB b

/-- The number of oriented edges is the sum of row degrees. -/
theorem card_relationEdge {A B : Type} [Fintype A] [Fintype B] (R : A → B → Prop) :
    Fintype.card (RelationEdge R) = ∑ b : B, (univ.filter fun a => R a b).card := by
  classical
  let e : RelationEdge R ≃ Σ b : B, {a : A // R a b} :=
    { toFun := fun x => ⟨x.val.2, ⟨x.val.1, x.property⟩⟩
      invFun := fun x => ⟨(x.2.val, x.1), x.2.property⟩
      left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
      right_inv := by rintro ⟨b, a, h⟩; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  apply sum_congr rfl
  intro b _
  exact Fintype.card_of_subtype (univ.filter fun a => R a b) (by simp)

private theorem card_relationCommon_singleton {A B : Type} [Fintype B]
    (R : A → B → Prop) (a : A) :
    (relationCommon R ({a} : Finset A)).card = (univ.filter fun b => R a b).card := by
  classical
  congr 1
  ext b
  simp [mem_relationCommon]

/-- Bounding the ordinary degrees bounds each original vertex's contribution to rectangle degrees. -/
theorem rectangleGraph_conflict_le_of_degree_max {A B : Type} [Fintype A] [Fintype B]
    (R : A → B → Prop) (D : ℕ)
    (hA : ∀ a : A, ((univ : Finset B).filter fun b => R a b).card ≤ D)
    (hB : ∀ b : B, ((univ : Finset A).filter fun a => R a b).card ≤ D)
    (e f : RelationEdge R) :
    (((rectangleGraph R).neighborFinset e).filter fun g => edgeConflict g f).card ≤ 2 * D := by
  classical
  let x : Fin 0 → RelationEdge R := Fin.elim0
  have hzero : commonRectangleEdges R x = univ := by
    ext g
    simp [mem_commonRectangleEdges]
  have hc := commonRectangleEdges_conflict_le R (L := D) x
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (fun u hu => by
      obtain ⟨a, rfl⟩ := card_eq_one.mp hu
      simpa only [card_relationCommon_singleton] using hA a)
    (fun u hu => by
      obtain ⟨b, rfl⟩ := card_eq_one.mp hu
      simpa only [card_relationCommon_singleton] using hB b) f
  rw [hzero] at hc
  exact (card_le_card (filter_subset_filter _ (subset_univ _))).trans hc

/-- A dense bipartite relation with bounded codegrees has a sparse-overlap rectangle core. -/
theorem rectangle_core_of_density {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (R : A → B → Prop) [Nonempty (RelationEdge R)]
    (t L θ D : ℕ) (ht : 0 < t) (hθ : 0 < θ) (hθL : 4 * t * L ≤ θ)
    (hA : 2 ≤ Fintype.card A)
    (hm₁ : 2 * (Fintype.card B : ℝ) ≤ (Fintype.card (RelationEdge R) : ℝ))
    (hm₂ : 8 * (Fintype.card A : ℝ) ^ 2 * (Fintype.card B : ℝ) ≤
      (Fintype.card (RelationEdge R) : ℝ) ^ 2)
    (hD₁ : ∀ a : A, ((univ : Finset B).filter fun b => R a b).card ≤ D)
    (hD₂ : ∀ b : B, ((univ : Finset A).filter fun a => R a b).card ≤ D)
    (hL₁ : ∀ u : Finset A, u.card = t + 1 → (relationCommon R u).card ≤ L)
    (hL₂ : ∀ u : Finset B, u.card = t + 1 → (relationCommon (Function.swap R) u).card ≤ L)
    (hd : (t : ℝ) * (2 * D : ℕ) ≤
      (Fintype.card (RelationEdge R) : ℝ) ^ 3 /
        (64 * (Fintype.card A : ℝ) ^ 2 * (Fintype.card B : ℝ) ^ 2))
    (hpower : 10 * (θ : ℝ) * (Fintype.card (RelationEdge R) : ℝ) ^ (t - 1) ≤
      ((Fintype.card (RelationEdge R) : ℝ) ^ 3 /
        (64 * (Fintype.card A : ℝ) ^ 2 * (Fintype.card B : ℝ) ^ 2) - (t : ℝ) * (2 * D : ℕ)) ^ t) :
    ∃ U : Finset (Fin t → RelationEdge R),
      U ⊆ packedTuples univ edgeConflict t ∧ U.Nonempty ∧
      ∀ x ∈ U,
        0 < (U.filter (simultaneousRectangles R x)).card ∧
        ∀ f : Fin t → RelationEdge R,
        θ * (U.filter fun y => simultaneousRectangles R x y ∧ packedOverlap f y).card ≤
          (8 * 2 ^ t * t ^ 2 * L) * (U.filter (simultaneousRectangles R x)).card := by
  classical
  let m : ℝ := Fintype.card (RelationEdge R)
  let denom : ℝ := 64 * (Fintype.card A : ℝ) ^ 2 * (Fintype.card B : ℝ) ^ 2
  apply rectangle_core_of_degree_sum R t L θ (2 * D) ht hθ hθL (m ^ 3 / denom) hd
    _ (rectangleGraph_conflict_le_of_degree_max R D hD₁ hD₂) hpower hL₁ hL₂
  have hm : m = ∑ b : B, (((univ : Finset A).filter fun a => R a b).card : ℝ) := by
    dsimp [m]
    exact_mod_cast card_relationEdge R
  have h₁ := rectangles_lower_bound R hA m hm hm₁ hm₂
  have h₂ : (∑ s ∈ (univ : Finset A).powersetCard 2, (((relationCommon R s).card).choose 2 : ℝ)) ≤
      ∑ e : RelationEdge R, ((rectangleGraph R).degree e : ℝ) := by
    exact_mod_cast sum_rectangleGraph_degree_ge R
  calc
    m * (m ^ 3 / denom) = m ^ 4 / denom := by ring
    _ ≤ _ := h₁.trans h₂

/-- Replace each vertex by t independent vertices and each edge by a complete link. -/
def independentBlowup {V : Type} (G : SimpleGraph V) (t : ℕ) :
    SimpleGraph (V × Fin t) :=
  G.comap Prod.fst

theorem degree_independentBlowup {V : Type} [Fintype V] (G : SimpleGraph V)
    (t : ℕ) (v : V × Fin t) :
    (independentBlowup G t).degree v = G.degree v.1 * t := by
  classical
  have h :
      (independentBlowup G t).neighborFinset v = G.neighborFinset v.1 ×ˢ (univ : Finset (Fin t)) := by
    ext w
    rw [mem_neighborFinset, mem_product, mem_neighborFinset]
    simp [independentBlowup]
  rw [← card_neighborFinset_eq_degree, h, card_product, card_univ,
    Fintype.card_fin, card_neighborFinset_eq_degree]

/-- Two blow-ups of the same cycle, joined by a matching between corresponding vertices. -/
def cycleWithMatching (l t : ℕ) : SimpleGraph ((Fin l × Fin t) × Fin 2) :=
  (independentBlowup (cycleGraph l) t).boxProd ⊤

theorem cycleWithMatching_regular (l t : ℕ) (hl : 3 ≤ l) :
    (cycleWithMatching l t).IsRegularOfDegree (2 * t + 1) := by
  classical
  have hlen : l = (l - 3) + 3 := (Nat.sub_add_cancel hl).symm
  generalize l - 3 = k at hlen
  subst l
  intro v
  unfold cycleWithMatching
  rw [degree_boxProd, degree_independentBlowup]
  have hcycle : (cycleGraph (k + 3)).degree v.1.1 = 2 := cycleGraph_degree_three_le
  have htop : (⊤ : SimpleGraph (Fin 2)).degree v.2 = 1 := by
    simp
  convert! congrArg₂ (· + ·) (congrArg (· * t) hcycle) htop

/-- An ordered matching of t edges, with a choice of sides. -/
structure MatchingTuple {V : Type} (G : SimpleGraph V) (t : ℕ) where
  point : Fin t × Fin 2 → V
  injective : Function.Injective point
  paired : ∀ i b c, b ≠ c → G.Adj (point (i, b)) (point (i, c))

/-- Two matchings are adjacent when their corresponding sides are completely joined. -/
def matchingAux {V : Type} (G : SimpleGraph V) (t : ℕ) :
    SimpleGraph (MatchingTuple G t) :=
  SimpleGraph.fromRel fun x y => ∀ i j b, G.Adj (x.point (i, b)) (y.point (j, b))

/-- An auxiliary cycle lifts when the matchings at distinct positions have disjoint vertices. -/
theorem cycleWithMatching_isContained {V : Type} (G : SimpleGraph V) (l t : ℕ)
    (f : cycleGraph l →g matchingAux G t)
    (hdisj : ∀ i j, i ≠ j → ∀ a b, (f i).point a ≠ (f j).point b) :
    cycleWithMatching l t ⊑ G := by
  let liftPoint : (Fin l × Fin t) × Fin 2 → V :=
    fun u => (f u.1.1).point (u.1.2, u.2)
  refine ⟨⟨⟨liftPoint, ?_⟩, ?_⟩⟩
  · rintro ⟨⟨i, a⟩, b⟩ ⟨⟨j, c⟩, d⟩ hadj
    change ((cycleGraph l).Adj i j ∧ b = d) ∨ ((⊤ : SimpleGraph (Fin 2)).Adj b d ∧
      (i, a) = (j, c)) at hadj
    rcases hadj with ⟨hij, rfl⟩ | ⟨hbd, hpair⟩
    · change G.Adj ((f i).point (a, b)) ((f j).point (c, b))
      have hf := (fromRel_adj _ _ _).mp (f.map_adj hij)
      rcases hf.2 with h | h
      · exact h a c b
      · exact (h c a b).symm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      exact (f i).paired a b d (by simpa using hbd)
  · rintro ⟨⟨i, a⟩, b⟩ ⟨⟨j, c⟩, d⟩ h
    change (f i).point (a, b) = (f j).point (c, d) at h
    have hij : i = j := by
      by_contra hne
      exact hdisj i j hne _ _ h
    subst j
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((f i).injective h)
    rfl

/-- The auxiliary cycle criterion for the odd-degree bound. -/
theorem odd_degree_from_matching_cycles (t : ℕ) (ht : 1 ≤ t) (ε : ℝ) (hε : 0 ≤ ε)
    (l : ℕ) (hl : 3 ≤ l) (C : ℝ) (hC : 0 ≤ C)
    (force : ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V), G.IsBipartite →
      (∀ v, C * (Fintype.card V : ℝ) ^ (1 - 2 / ((2 * t + 1 : ℕ) : ℝ) + ε) <
        (G.degree v : ℝ)) →
      ∃ f : cycleGraph l →g matchingAux G t,
        ∀ i j, i ≠ j → ∀ a b, (f i).point a ≠ (f j).point b) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree (2 * t + 1) ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / ((2 * t + 1 : ℕ) : ℝ) + ε) := by
  classical
  let W := cycleWithMatching l t
  let e : ((Fin l × Fin t) × Fin 2) ≃ Fin ((l * t) * 2) :=
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv
  let H := W.map e
  let iso : W ≃g H := Iso.map e W
  refine ⟨(l * t) * 2, H, by positivity, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ : ∃ u, iso u = v := iso.toEquiv.surjective v
    rw [← hu]
    have hcard : H.degree (iso u) = W.degree u := by
      rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
      convert! (Fintype.card_congr (iso.mapNeighborSet u)).symm
    convert! hcard.trans (cycleWithMatching_regular l t hl u)
  have hr : (2 : ℝ) ≤ ((2 * t + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ 2 * t + 1 by omega)
  have hfrac := (div_le_one (by positivity : 0 < ((2 * t + 1 : ℕ) : ℝ))).2 hr
  let a := 1 - 2 / ((2 * t + 1 : ℕ) : ℝ) + ε
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hw := extremal_of_bipartite_degree_threshold W ha hC (fun V _ _ G hb hdeg => by
    obtain ⟨f, hdisj⟩ := force V G hb hdeg
    exact cycleWithMatching_isContained G l t f hdisj)
  have hexp : a + 1 = 2 - 2 / ((2 * t + 1 : ℕ) : ℝ) + ε := by dsimp [a]; ring
  simpa only [extremalNumber_congr rfl iso.symm, hexp] using hw

/-- A relation viewed as a simple graph on the disjoint union of its sides. -/
def relationGraph {A B : Type} (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj u v := match u, v with
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | _, _ => False
  symm.symm := by rintro (a | b) (c | d) h <;> exact h
  loopless.irrefl := by rintro (a | b) <;> simp

private def orientedPoint {A B : Type} {R : A → B → Prop} {t : ℕ}
    (x : Fin t → RelationEdge R) (flip : Bool) (w : Fin t × Fin 2) : A ⊕ B :=
  if (w.2 = 0) ↔ flip = true then Sum.inl (x w.1).val.1 else Sum.inr (x w.1).val.2

private theorem orientedPoint_injective {A B : Type} {R : A → B → Prop} {t : ℕ}
    (x : Fin t → RelationEdge R) (flip : Bool)
    (hA : Function.Injective fun i => (x i).val.1)
    (hB : Function.Injective fun i => (x i).val.2) :
    Function.Injective (orientedPoint x flip) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  fin_cases b <;> fin_cases c <;> cases flip <;>
    simp [orientedPoint, hA.eq_iff, hB.eq_iff] at h ⊢ <;> exact h

private theorem orientedPoint_paired {A B : Type} {R : A → B → Prop} {t : ℕ}
    (x : Fin t → RelationEdge R) (flip : Bool) (i : Fin t) (b c : Fin 2) (h : b ≠ c) :
    (relationGraph R).Adj (orientedPoint x flip (i, b)) (orientedPoint x flip (i, c)) := by
  fin_cases b <;> fin_cases c <;> cases flip <;> simp_all [orientedPoint, relationGraph]
  all_goals exact (x i).property

private theorem orientedPoint_adj {A B : Type} {R : A → B → Prop} {t : ℕ}
    (x y : Fin t → RelationEdge R) (hx hy : Bool) (hcolor : hx ≠ hy)
    (hxy : simultaneousRectangles R x y) (i j : Fin t) (b : Fin 2) :
    (relationGraph R).Adj (orientedPoint x hx (i, b)) (orientedPoint y hy (j, b)) := by
  have h₁ := (hxy i j).2.2.1
  have h₂ := (hxy i j).2.2.2
  fin_cases b <;> cases hx <;> cases hy <;> simp_all [orientedPoint, relationGraph]

private theorem orientedPoint_disjoint {A B : Type} {R : A → B → Prop} {t : ℕ}
    (x y : Fin t → RelationEdge R) (hx hy : Bool) (hxy : ¬ packedOverlap x y)
    (a b : Fin t × Fin 2) :
    orientedPoint x hx a ≠ orientedPoint y hy b := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  have h₁ : (x i).val.1 ≠ (y j).val.1 := fun h => hxy ⟨i, j, .inl h.symm⟩
  have h₂ : (x i).val.2 ≠ (y j).val.2 := fun h => hxy ⟨i, j, .inr h.symm⟩
  fin_cases a <;> fin_cases b <;> cases hx <;> cases hy <;> simp [orientedPoint, h₁, h₂]

/-- A vertex-disjoint even cycle of compatible oriented matchings yields the odd-regular witness. -/
theorem cycleWithMatching_of_rectangles {A B : Type} [Fintype A] [Fintype B]
    (R : A → B → Prop) (l t : ℕ) (hl : Even l) (ht : 0 < t)
    (x : Fin l → Fin t → RelationEdge R)
    (hx : ∀ i, x i ∈ packedTuples univ edgeConflict t)
    (hstep : ∀ i j, (cycleGraph l).Adj i j → simultaneousRectangles R (x i) (x j))
    (hdisj : ∀ i j, i ≠ j → ¬ packedOverlap (x i) (x j)) :
    cycleWithMatching l t ⊑ relationGraph R := by
  classical
  let color := cycleGraph.bicoloring_of_even l hl
  let pack (i : Fin l) : MatchingTuple (relationGraph R) t :=
    { point := orientedPoint (x i) (color i)
      injective := orientedPoint_injective (x i) (color i)
        (packed_endpoints_injective R (hx i)).1 (packed_endpoints_injective R (hx i)).2
      paired := orientedPoint_paired (x i) (color i) }
  have hne (i j : Fin l) (hij : (cycleGraph l).Adj i j) : pack i ≠ pack j := by
    intro he
    let a : Fin t × Fin 2 := (⟨0, ht⟩, 0)
    apply orientedPoint_disjoint (x i) (x j) (color i) (color j)
      (hdisj i j hij.ne) a a
    exact congrArg (fun p : MatchingTuple (relationGraph R) t => p.point a) he
  let f : cycleGraph l →g matchingAux (relationGraph R) t :=
    ⟨pack, fun {i j} hij => (fromRel_adj _ _ _).mpr
      ⟨hne i j hij, .inl (orientedPoint_adj (x i) (x j) (color i) (color j)
        (color.valid hij) (hstep i j hij))⟩⟩
  apply cycleWithMatching_isContained _ _ _ f
  intro i j hij a b
  exact orientedPoint_disjoint (x i) (x j) (color i) (color j) (hdisj i j hij) a b

/-- A finite cycle guarantee phrased using the local proportion of conflicting neighbors. -/
def SparseConflictCycles (N b c l : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W], Fintype.card W ≤ N →
    ∀ (G : SimpleGraph W) (conflict : W → W → Prop),
      (∀ ⦃x y⦄, conflict x y → conflict y x) → G.edgeFinset.Nonempty →
      (∀ u v, b * ((G.neighborFinset v).filter (conflict u)).card ≤ c * G.degree v) →
      ∃ f : cycleGraph l →g G, ∀ i j, i ≠ j → ¬ conflict (f i) (f j)

/-- A sparse-overlap tuple core gives a cycle of compatible disjoint tuples. -/
theorem exists_cycle_of_sparse_tuple_core {E : Type} [Fintype E]
    (C : E → E → Prop) (t l b c : ℕ)
    (Q : (Fin t → E) → (Fin t → E) → Prop)
    (hC : ∀ ⦃u v⦄, C u v → C v u)
    (hQ : ∀ ⦃x y⦄, Q x y → Q y x) (hQirr : ∀ x, ¬ Q x x)
    (findCycle : SparseConflictCycles (Fintype.card E ^ t) b c l)
    (U : Finset (Fin t → E)) (hU : U ⊆ packedTuples univ C t)
    (hUne : U.Nonempty)
    (hd : ∀ x ∈ U, 0 < (U.filter (Q x)).card)
    (hover : ∀ x ∈ U, ∀ f : Fin t → E,
      b * (U.filter fun y => Q x y ∧ tupleOverlap C f y).card ≤ c * (U.filter (Q x)).card) :
    ∃ x : Fin l → Fin t → E,
      (∀ i, x i ∈ packedTuples univ C t) ∧
      (∀ i j, (cycleGraph l).Adj i j → Q (x i) (x j)) ∧
      ∀ i j, i ≠ j → ¬ tupleOverlap C (x i) (x j) := by
  classical
  let W := ↥U
  let G : SimpleGraph W :=
    { Adj := fun x y => Q x.val y.val
      symm.symm := fun _ _ h => hQ h
      loopless.irrefl := fun x h => hQirr x.val h }
  let conflict (x y : W) := tupleOverlap C x.val y.val
  have hc ⦃x y : W⦄ (h : conflict x y) : conflict y x := by
    obtain ⟨i, j, h⟩ := h
    exact ⟨j, i, hC h⟩
  have hcard : Fintype.card W ≤ Fintype.card (E) ^ t := by
    rw [show Fintype.card W = U.card from Fintype.card_coe U]
    exact (card_le_card hU).trans (by
      simpa only [card_univ] using packed_size_le (univ : Finset (E)) C t)
  have hfiber (v : W) (P : (Fin t → E) → Prop) :
      (((G.neighborFinset v).filter fun u => P u.val).map (Function.Embedding.subtype _)) =
        U.filter (fun u => Q v.val u ∧ P u) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      have hy' := mem_filter.mp hy
      exact mem_filter.mpr ⟨y.property, (mem_neighborFinset _ _ _).mp hy'.1, hy'.2⟩
    · intro hx
      obtain ⟨hu, ha, hp⟩ := mem_filter.mp hx
      let y : W := ⟨x, hu⟩
      exact mem_map.mpr ⟨y, mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr ha, hp⟩, rfl⟩
  have hdeg (v : W) : G.degree v = (U.filter (Q v.val)).card := by
    have h := congrArg Finset.card (hfiber v (fun _ => True))
    simpa [card_map, card_neighborFinset_eq_degree] using h
  have he : G.edgeFinset.Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    let v : W := ⟨x, hx⟩
    have hp := hd x hx
    have hp' : 0 < (G.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree, hdeg]
      exact hp
    obtain ⟨y, hy⟩ := card_pos.mp hp'
    exact ⟨s(v, y), by simpa using (mem_neighborFinset _ _ _).mp hy⟩
  have hlocal (u v : W) :
      b * ((G.neighborFinset v).filter (conflict u)).card ≤ c * G.degree v := by
    have h := congrArg Finset.card (hfiber v (tupleOverlap C u.val))
    have h' : ((G.neighborFinset v).filter (conflict u)).card =
        (U.filter fun y => Q v.val y ∧ tupleOverlap C u.val y).card := by
      simpa only [card_map, conflict] using h
    rw [h', hdeg]
    exact hover v.val v.property u.val
  obtain ⟨f, hdisj⟩ := findCycle W hcard G conflict hc he hlocal
  exact ⟨fun i => (f i).val, fun i => hU (f i).property,
    fun _ _ hij => f.map_adj hij, hdisj⟩

/-- The overlap bound on a rectangle core suffices for embedding via a sparse-conflict cycle lemma. -/
theorem cycleWithMatching_of_rectangle_core {A B : Type} [Fintype A] [Fintype B]
    (R : A → B → Prop) (t l b c : ℕ) (ht : 0 < t) (hl : Even l)
    (findCycle : SparseConflictCycles (Fintype.card (RelationEdge R) ^ t) b c l)
    (U : Finset (Fin t → RelationEdge R)) (hU : U ⊆ packedTuples univ edgeConflict t)
    (hUne : U.Nonempty)
    (hd : ∀ x ∈ U, 0 < (U.filter (simultaneousRectangles R x)).card)
    (hover : ∀ x ∈ U, ∀ f : Fin t → RelationEdge R,
      b * (U.filter fun y => simultaneousRectangles R x y ∧ packedOverlap f y).card ≤
        c * (U.filter (simultaneousRectangles R x)).card) :
    cycleWithMatching l t ⊑ relationGraph R := by
  classical
  obtain ⟨x, hx, hstep, hdisj⟩ := exists_cycle_of_sparse_tuple_core edgeConflict t l b c
    (simultaneousRectangles R) (fun {_ _} h =>
      h.elim (Or.inl ∘ Eq.symm) (Or.inr ∘ Eq.symm))
    (fun {_ _} h i j => (h j i).symm)
    (fun x h => (rectangleGraph R).irrefl (h ⟨0, ht⟩ ⟨0, ht⟩))
    findCycle U hU hUne hd hover
  exact cycleWithMatching_of_rectangles R l t hl ht x hx hstep hdisj

noncomputable def pathWeight {V : Type} (M : Matrix V V ℝ) :
    (n : ℕ) → V → (Fin n → V) → V → ℝ
  | 0, a, _, b => M a b
  | n + 1, a, x, b => M a (x 0) * pathWeight M n (x 0) (Fin.tail x) b

theorem pathWeight_cons {V : Type} (M : Matrix V V ℝ) {n : ℕ} (a w b : V)
    (x : Fin n → V) :
    pathWeight M (n + 1) a (Fin.cons w x) b = M a w * pathWeight M n w x b := by
  simp [pathWeight]

theorem pathWeight_nonneg {V : Type} (M : Matrix V V ℝ) (hM : ∀ a b, 0 ≤ M a b) :
    ∀ n a x b, 0 ≤ pathWeight M n a x b := by
  intro n
  induction n with
  | zero => exact fun a _ b => hM a b
  | succ n ih =>
    intro a x b
    exact mul_nonneg (hM a (x 0)) (ih (x 0) (Fin.tail x) b)

theorem sum_pathWeight_eq_pow {V : Type} [Fintype V] (M : Matrix V V ℝ) :
    ∀ n a b, (∑ x : Fin n → V, pathWeight M n a x b) = (M ^ (n + 1)) a b := by
  classical
  intro n
  induction n with
  | zero =>
    intro a b
    simp [pathWeight]
  | succ n ih =>
    intro a b
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => V)
    calc
      _ = ∑ z : V × (Fin n → V), pathWeight M (n + 1) a (e z) b :=
        (Fintype.sum_equiv e (fun z => pathWeight M (n + 1) a (e z) b)
          (fun x => pathWeight M (n + 1) a x b) (fun _ => rfl)).symm
      _ = ∑ w : V, M a w * (M ^ (n + 1)) w b := by
        rw [Fintype.sum_prod_type]
        apply sum_congr rfl
        intro w _
        change (∑ x : Fin n → V, pathWeight M (n + 1) a (Fin.cons w x) b) = _
        simp only [pathWeight_cons, ← mul_sum, ih]
      _ = _ := by
        rw [show M ^ (n + 1 + 1) = M * M ^ (n + 1) from pow_succ' _ _, Matrix.mul_apply]

private theorem pathWeight_cast {V : Type} (M : Matrix V V ℝ) {n m : ℕ}
    (h : n = m) (x : Fin m → V) (a b : V) :
    pathWeight M n a (x ∘ Fin.cast h) b = pathWeight M m a x b := by
  subst m
  rfl

theorem pathWeight_append_cons {V : Type} (M : Matrix V V ℝ) {m n : ℕ}
    (a c b : V) (x : Fin m → V) (y : Fin n → V) :
    pathWeight M (m + (n + 1)) a (Fin.append x (Fin.cons c y)) b =
      pathWeight M m a x c * pathWeight M n c y b := by
  induction m generalizing a with
  | zero =>
    have hx : Fin.append x (Fin.cons c y) =
        Fin.cons c y ∘ Fin.cast (Nat.zero_add (n + 1)) := by
      exact Fin.append_left_nil _ _ rfl
    rw [hx, pathWeight_cast, pathWeight_cons]
    rfl
  | succ m ih =>
    let z := x 0
    let u := Fin.tail x
    have hx : x = Fin.cons z u := (Fin.cons_self_tail x).symm
    rw [hx, Fin.append_cons]
    have he : m + 1 + (n + 1) = (m + (n + 1)) + 1 := Nat.add_right_comm m 1 (n + 1)
    rw [pathWeight_cast M he, pathWeight_cons, pathWeight_cons, ih]
    ring

/-- Path weights also read as a product of consecutive matrix entries. -/
theorem pathWeight_eq_prod {V : Type} (M : Matrix V V ℝ) :
    ∀ n (a : V) (x : Fin n → V) (b : V),
      let y : Fin (n + 2) → V := Fin.cons a (Fin.snoc x b)
      pathWeight M n a x b =
        ∏ i : Fin (n + 1), M (y i.castSucc) (y i.succ) := by
  intro n
  induction n with
  | zero =>
    intro a x b
    simp [pathWeight, Fin.snoc]
  | succ n ih =>
    intro a x b y
    rw [Fin.prod_univ_succ]
    have h0 : y ((0 : Fin (n + 2)).castSucc) = a := by simp [y]
    have h1 : y ((0 : Fin (n + 2)).succ) = x 0 := by
      simp only [y, Fin.cons_succ]
      exact Fin.snoc_castSucc (α := fun _ => V) b x (0 : Fin (n + 1))
    have hy : Fin.tail y = Fin.cons (x 0) (Fin.snoc (Fin.tail x) b) := by
      simp only [y, Fin.tail_cons]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Fin.snoc_castSucc (α := fun _ => V) b x (0 : Fin (n + 1))
      · simp only [Fin.cons_succ]
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simp
        · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          rfl
    rw [h0, h1]
    rw [show pathWeight M (n + 1) a x b = M a (x 0) *
      pathWeight M n (x 0) (Fin.tail x) b from rfl, ih]
    congr 1
    apply Fintype.prod_congr
    intro i
    simp only [← hy, Fin.tail, Fin.succ_castSucc]

/-- Detailed balance survives taking a power of a transition matrix. -/
theorem pow_detailedBalance {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (w : V → ℝ) (h : ∀ a b, w a * M a b = w b * M b a) :
    ∀ n a b, w a * (M ^ n) a b = w b * (M ^ n) b a := by
  classical
  intro n
  induction n with
  | zero =>
    intro a b
    by_cases hab : a = b
    · subst b
      rfl
    · simp [hab, Ne.symm hab]
  | succ n ih =>
    intro a b
    calc
      _ = ∑ x : V, (w a * M a x) * (M ^ n) x b := by
        rw [pow_succ', Matrix.mul_apply, mul_sum]
        exact sum_congr rfl (fun x _ => by ring)
      _ = ∑ x : V, (w b * (M ^ n) b x) * M x a := by
        apply sum_congr rfl
        intro x _
        rw [h a x, mul_assoc, mul_comm (M x a), ← mul_assoc, ih x b]
      _ = _ := by
        rw [pow_succ, Matrix.mul_apply, mul_sum]
        exact sum_congr rfl (fun x _ => by ring)

/-- Powers of a row-stochastic matrix remain row-stochastic. -/
theorem pow_rows_eq_one {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (h : ∀ a, ∑ b : V, M a b = 1) :
    ∀ n a, ∑ b : V, (M ^ n) a b = 1 := by
  classical
  intro n
  induction n with
  | zero => intro a; simp [Matrix.one_apply]
  | succ n ih =>
    intro a
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [sum_comm]
    simp_rw [← mul_sum, ih, mul_one]
    exact h a

private theorem trace_pow_split {V : Type} [Fintype V] (M : Matrix V V ℝ) (a b : ℕ) :
    Matrix.trace (M ^ (a + b)) = ∑ x : V × V, (M ^ a) x.1 x.2 * (M ^ b) x.2 x.1 := by
  rw [pow_add, Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply]

/-- Even return traces of a reversible stochastic matrix are at least one. -/
theorem one_le_even_trace {V : Type} [Fintype V] [Nonempty V]
    (M : Matrix V V ℝ) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hbal : ∀ a b, w a * M a b = w b * M b a)
    (hrow : ∀ a, ∑ b : V, M a b = 1) (n : ℕ) :
    1 ≤ Matrix.trace (M ^ (n + n)) := by
  classical
  let W := ∑ v : V, w v
  have hW : 0 < W := sum_pos (fun v _ => hw v) univ_nonempty
  have rowBound (a : V) :
      w a / W ≤ ∑ b : V, (M ^ n) a b * (M ^ n) b a := by
    have hc := sq_sum_div_le_sum_sq_div univ (fun b => (M ^ n) a b)
      (g := w) (fun b _ => hw b)
    rw [pow_rows_eq_one M hrow n a, one_pow] at hc
    calc
      _ = w a * (1 / W) := by ring
      _ ≤ w a * ∑ b : V, ((M ^ n) a b) ^ 2 / w b :=
        mul_le_mul_of_nonneg_left hc (hw a).le
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro b _
        have hb := pow_detailedBalance M w hbal n a b
        have hb' : (M ^ n) b a = w a * (M ^ n) a b / w b :=
          (eq_div_iff (hw b).ne').2 (by rw [mul_comm, hb])
        rw [hb']
        ring
  have h := sum_le_sum (fun a (_ : a ∈ (univ : Finset V)) => rowBound a)
  rw [← sum_div, div_self hW.ne', ← Fintype.sum_prod_type'] at h
  simpa only [trace_pow_split] using h

/-- Even return traces of a reversible matrix form a log-convex sequence. -/
theorem even_trace_logConvex {V : Type} [Fintype V]
    (M : Matrix V V ℝ) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hbal : ∀ a b, w a * M a b = w b * M b a) (j : ℕ) :
    (Matrix.trace (M ^ ((j + 1) + (j + 1)))) ^ 2 ≤
      Matrix.trace (M ^ (j + j)) * Matrix.trace (M ^ ((j + 2) + (j + 2))) := by
  classical
  let f (k : ℕ) (p : V × V) := Real.sqrt (w p.1 / w p.2) * (M ^ k) p.1 p.2
  have hprod (a b : ℕ) :
      (∑ p : V × V, f a p * f b p) = Matrix.trace (M ^ (a + b)) := by
    rw [trace_pow_split]
    apply sum_congr rfl
    intro p _
    have hroot : Real.sqrt (w p.1 / w p.2) ^ 2 = w p.1 / w p.2 :=
      Real.sq_sqrt (by positivity [hw p.1, hw p.2])
    have hbal' := pow_detailedBalance M w hbal b p.1 p.2
    calc
      _ = Real.sqrt (w p.1 / w p.2) ^ 2 * ((M ^ a) p.1 p.2 * (M ^ b) p.1 p.2) := by
        dsimp [f]
        ring
      _ = _ := by
        rw [hroot]
        have hb' : (M ^ b) p.2 p.1 = w p.1 * (M ^ b) p.1 p.2 / w p.2 :=
          (eq_div_iff (hw p.2).ne').2 (by rw [mul_comm, hbal'])
        rw [hb']
        ring
  have h := sum_mul_sq_le_sq_mul_sq univ (f j) (f (j + 2))
  simp only [sq, hprod] at h ⊢
  simpa only [show j + (j + 2) = (j + 1) + (j + 1) by omega] using h

/-- A positive log-convex sequence obeys the interpolation bound between its first and last terms. -/
theorem logConvex_nat_interpolation (T : ℕ → ℝ) (hp : ∀ n, 0 < T n)
    (hcv : ∀ n, (T (n + 1)) ^ 2 ≤ T n * T (n + 2)) {n : ℕ} (hn : 0 < n) :
    (T (n - 1)) ^ n ≤ T 0 * (T n) ^ (n - 1) := by
  let r (k : ℕ) := T (k + 1) / T k
  have hstep (k : ℕ) : r k ≤ r (k + 1) := by
    dsimp [r]
    rw [div_le_div_iff₀ (hp k) (hp (k + 1))]
    simpa only [sq, mul_comm] using hcv k
  have hr : Monotone r := monotone_nat_of_le_succ hstep
  have hprod (m : ℕ) : T 0 * ∏ k ∈ range m, r k = T m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [prod_range_succ, ← mul_assoc, ih]
      exact mul_div_cancel₀ _ (hp _).ne'
  have hbound : (∏ k ∈ range (n - 1), r k) ≤ (r (n - 1)) ^ (n - 1) := by
    calc
      _ ≤ ∏ _k ∈ range (n - 1), r (n - 1) :=
        prod_le_prod (fun k _ => div_nonneg (hp _).le (hp _).le)
          (fun k hk => hr (by have := mem_range.mp hk; omega))
      _ = _ := by simp
  have ht := mul_le_mul_of_nonneg_left hbound (hp 0).le
  rw [hprod] at ht
  have hrn : r (n - 1) = T n / T (n - 1) := by
    dsimp [r]
    rw [Nat.sub_add_cancel (show 1 ≤ n from hn)]
  rw [hrn, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos (hp _) _)] at ht
  calc
    _ = T (n - 1) * T (n - 1) ^ (n - 1) := by
      exact (congrArg (fun k : ℕ => (T (n - 1)) ^ k)
        (Nat.sub_add_cancel (show 1 ≤ n from hn)).symm).trans (pow_succ' _ _)
    _ ≤ _ := ht

/-- A truncated prefix weight counts paths having a conflict with the preceding vertex. -/
noncomputable def badPrefixWeight {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (conflict : V → V → Prop) (n : ℕ) (a b c : V) : ℝ :=
  ∑ x : Fin (n + 1) → V,
    if ∃ i : Fin (n + 2), conflict a (Fin.cons (α := fun _ => V) b x i)
    then pathWeight M (n + 1) b x c else 0

theorem badPrefixWeight_nonneg {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (hM : ∀ u v, 0 ≤ M u v) (conflict : V → V → Prop) (n : ℕ) (a b c : V) :
    0 ≤ badPrefixWeight M conflict n a b c := by
  unfold badPrefixWeight
  exact sum_nonneg fun x _ => by split <;> first | exact pathWeight_nonneg M hM _ _ _ _ | rfl

theorem badPrefixWeight_le_pow {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (hM : ∀ u v, 0 ≤ M u v) (conflict : V → V → Prop) (n : ℕ) (a b c : V) :
    badPrefixWeight M conflict n a b c ≤ (M ^ (n + 2)) b c := by
  classical
  rw [← sum_pathWeight_eq_pow M (n + 1), badPrefixWeight]
  exact sum_le_sum fun x _ => by split <;> first | exact le_rfl | exact pathWeight_nonneg M hM _ _ _ _

private theorem sum_mass_ratio_square {I : Type} [Fintype I] (T X Y : I → ℝ)
    (hT : ∀ i, 0 ≤ T i) (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (hs : ∀ i, T i ≠ 0 → X i ≠ 0 ∧ Y i ≠ 0) :
    (∑ i, T i) ^ 2 ≤ (∑ i, T i * (X i / Y i)) * (∑ i, T i * (Y i / X i)) := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => mul_nonneg (hT i) (div_nonneg (hX i) (hY i)))
    (fun i _ => mul_nonneg (hT i) (div_nonneg (hY i) (hX i)))
  intro i _
  by_cases h : T i = 0
  · simp [h]
  · obtain ⟨hx, hy⟩ := hs i h
    exact le_of_eq (by field_simp)

private theorem sum_badPrefixWeight_row {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (hM : ∀ u v, 0 ≤ M u v) (conflict : V → V → Prop)
    (α : ℝ) (hloc : ∀ u v, ∑ a : V, (if conflict a u then M v a else 0) ≤ α)
    (n : ℕ) (b c : V) :
    (∑ a : V, M b a * badPrefixWeight M conflict n a b c) ≤
      ((n + 2 : ℕ) : ℝ) * α * (M ^ (n + 2)) b c := by
  classical
  let k : ℝ := (n + 2 : ℕ)
  let w (x : Fin (n + 1) → V) := pathWeight M (n + 1) b x c
  let bad (x : Fin (n + 1) → V) (a : V) := ∃ i : Fin (n + 2), conflict a (Fin.cons (α := fun _ => V) b x i)
  have hweight (x : Fin (n + 1) → V) :
      (∑ a : V, if bad x a then M b a else 0) ≤ k * α := by
    calc
      _ ≤ ∑ a : V, ∑ i : Fin (n + 2), if conflict a (Fin.cons (α := fun _ => V) b x i) then M b a else 0 := by
        apply sum_le_sum
        intro a _
        by_cases hb : bad x a
        · obtain ⟨i, hi⟩ := hb
          simpa only [if_pos (show bad x a from ⟨i, hi⟩), if_pos hi] using
            (Finset.single_le_sum
              (f := fun j : Fin (n + 2) => if conflict a (Fin.cons (α := fun _ => V) b x j) then M b a else 0)
              (fun j _ => by split <;> first | exact hM b a | rfl) (mem_univ i))
        · simpa only [if_neg hb] using sum_nonneg (fun i (_ : i ∈ (univ : Finset (Fin (n + 2)))) =>
            by split <;> first | exact hM b a | rfl)
      _ = ∑ i : Fin (n + 2), ∑ a : V, if conflict a (Fin.cons (α := fun _ => V) b x i) then M b a else 0 := sum_comm
      _ ≤ ∑ _i : Fin (n + 2), α := sum_le_sum fun i _ => hloc (Fin.cons (α := fun _ => V) b x i) b
      _ = _ := by simp [k]
  calc
    _ = ∑ a : V, ∑ x : Fin (n + 1) → V, (if bad x a then M b a else 0) * w x := by
      apply sum_congr rfl
      intro a _
      rw [badPrefixWeight, mul_sum]
      apply sum_congr rfl
      intro x _
      by_cases hx : bad x a <;> simp [bad, w] at hx ⊢
    _ = ∑ x : Fin (n + 1) → V, (∑ a : V, if bad x a then M b a else 0) * w x := by
      rw [sum_comm]
      simp only [sum_mul]
    _ ≤ ∑ x : Fin (n + 1) → V, (k * α) * w x := by
      exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hweight x) (pathWeight_nonneg M hM _ _ _ _)
    _ = _ := by rw [← mul_sum]; congr 1; exact sum_pathWeight_eq_pow M (n + 1) b c

/-- The mass of closed walks having a conflict in their first half is bounded by two return traces. -/
theorem badHalfWalk_mass_square {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hM : ∀ u v, 0 ≤ M u v) (hrow : ∀ a, ∑ b : V, M a b = 1)
    (hbal : ∀ a b, w a * M a b = w b * M b a)
    (conflict : V → V → Prop) (α : ℝ) (_hα : 0 ≤ α)
    (hloc : ∀ u v, ∑ a : V, (if conflict a u then M v a else 0) ≤ α)
    (n : ℕ) :
    (∑ a : V, ∑ b : V, ∑ c : V,
      M a b * badPrefixWeight M conflict n a b c * (M ^ (n + 1)) c a) ^ 2 ≤
      ((n + 2 : ℕ) : ℝ) * α * Matrix.trace (M ^ ((n + 1) + (n + 1))) *
        Matrix.trace (M ^ ((n + 2) + (n + 2))) := by
  classical
  let U := badPrefixWeight M conflict n
  let A₂ (a c : V) := (M ^ (n + 1)) a c
  let B₂ (a c : V) := (M ^ (n + 2)) a c
  let T (p : V × V × V) := M p.1 p.2.1 * U p.1 p.2.1 p.2.2 * A₂ p.2.2 p.1
  let X (p : V × V × V) := A₂ p.1 p.2.2
  let Y (p : V × V × V) := B₂ p.2.1 p.2.2
  have hA (a c : V) : 0 ≤ A₂ a c := Matrix.pow_apply_nonneg hM _ a c
  have hB (a c : V) : 0 ≤ B₂ a c := Matrix.pow_apply_nonneg hM _ a c
  have hU (a b c : V) : 0 ≤ U a b c := badPrefixWeight_nonneg M hM conflict n a b c
  have hUB (a b c : V) : U a b c ≤ B₂ b c := badPrefixWeight_le_pow M hM conflict n a b c
  have hT (p : V × V × V) : 0 ≤ T p := mul_nonneg (mul_nonneg (hM _ _) (hU _ _ _)) (hA _ _)
  have hs (p : V × V × V) (hp : T p ≠ 0) : X p ≠ 0 ∧ Y p ≠ 0 := by
    obtain ⟨a, b, c⟩ := p
    change M a b * U a b c * A₂ c a ≠ 0 at hp
    refine ⟨?_, (lt_of_lt_of_le (lt_of_le_of_ne (hU a b c) ?_) (hUB a b c)).ne'⟩
    · change A₂ a c ≠ 0
      intro hx
      have hb := pow_detailedBalance M w hbal (n + 1) a c
      change w a * A₂ a c = w c * A₂ c a at hb
      rw [hx, mul_zero] at hb
      have hc : A₂ c a = 0 := (mul_eq_zero.mp hb.symm).resolve_left (hw c).ne'
      simp [hc] at hp
    · exact Ne.symm (fun h => hp (by simp [h]))
  have hratio₁ (a b c : V) : T (a, b, c) * (X (a, b, c) / Y (a, b, c)) ≤
      M a b * (A₂ a c * A₂ c a) := by
    have hu : U a b c * (A₂ a c / B₂ b c) ≤ A₂ a c := by
      by_cases h : B₂ b c = 0
      · simpa [h] using hA a c
      · calc
          _ ≤ B₂ b c * (A₂ a c / B₂ b c) :=
            mul_le_mul_of_nonneg_right (hUB a b c) (div_nonneg (hA a c) (hB b c))
          _ = _ := by field_simp
    dsimp [T, X, Y]
    calc
      _ = M a b * (U a b c * (A₂ a c / B₂ b c)) * A₂ c a := by ring
      _ ≤ M a b * A₂ a c * A₂ c a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (hM a b)) (hA c a)
      _ = _ := by ring
  have hratio₂ (a b c : V) : T (a, b, c) * (Y (a, b, c) / X (a, b, c)) ≤
      B₂ c b * (M b a * U a b c) := by
    by_cases hx : A₂ a c = 0
    · simpa [T, X, Y, hx] using mul_nonneg (hB c b) (mul_nonneg (hM b a) (hU a b c))
    have ha := pow_detailedBalance M w hbal (n + 1) a c
    have hb := pow_detailedBalance M w hbal (n + 2) b c
    change w a * A₂ a c = w c * A₂ c a at ha
    change w b * B₂ b c = w c * B₂ c b at hb
    have hret : A₂ c a / A₂ a c = w a / w c := by
      apply (div_eq_div_iff hx (hw c).ne').2
      linarith only [ha]
    have hret' : w b * B₂ b c / w c = B₂ c b := (div_eq_iff (hw c).ne').2 (by simpa only [mul_comm (w c)] using hb)
    apply le_of_eq
    dsimp [T, X, Y]
    calc
      _ = U a b c * (M a b * ((A₂ c a / A₂ a c) * B₂ b c)) := by ring
      _ = U a b c * ((w a * M a b) * B₂ b c / w c) := by rw [hret]; ring
      _ = U a b c * (M b a * (w b * B₂ b c / w c)) := by rw [hbal]; ring
      _ = _ := by rw [hret']; ring
  have h₁ : (∑ p : V × V × V, T p * (X p / Y p)) ≤ Matrix.trace (M ^ ((n + 1) + (n + 1))) := by
    calc
      _ ≤ ∑ a : V, ∑ b : V, ∑ c : V, M a b * (A₂ a c * A₂ c a) := by
        simp only [Fintype.sum_prod_type]
        exact sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ => hratio₁ a b c
      _ = ∑ a : V, ∑ c : V, A₂ a c * A₂ c a := by
        apply sum_congr rfl
        intro a _
        rw [sum_comm]
        simp only [← sum_mul, hrow, one_mul]
      _ = _ := by rw [trace_pow_split, Fintype.sum_prod_type]
  have h₂ : (∑ p : V × V × V, T p * (Y p / X p)) ≤
      ((n + 2 : ℕ) : ℝ) * α * Matrix.trace (M ^ ((n + 2) + (n + 2))) := by
    calc
      _ ≤ ∑ a : V, ∑ b : V, ∑ c : V, B₂ c b * (M b a * U a b c) := by
        simp only [Fintype.sum_prod_type]
        exact sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ => hratio₂ a b c
      _ = ∑ b : V, ∑ c : V, B₂ c b * ∑ a : V, M b a * U a b c := by
        rw [sum_comm]
        apply sum_congr rfl
        intro b _
        rw [sum_comm]
        simp only [← mul_sum]
      _ ≤ ∑ b : V, ∑ c : V, B₂ c b * (((n + 2 : ℕ) : ℝ) * α * B₂ b c) := by
        exact sum_le_sum fun b _ => sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (sum_badPrefixWeight_row M hM conflict α hloc n b c) (hB c b)
      _ = _ := by
        rw [trace_pow_split, Fintype.sum_prod_type]
        have h (b c : V) : B₂ c b * (((n + 2 : ℕ) : ℝ) * α * B₂ b c) =
            ((n + 2 : ℕ) : ℝ) * α * (B₂ b c * B₂ c b) := by ring
        simp only [h, ← mul_sum, B₂]
  have hT₂ : 0 ≤ ∑ p : V × V × V, T p * (Y p / X p) :=
    sum_nonneg fun p _ => mul_nonneg (hT p) (div_nonneg (hB _ _) (hA _ _))
  have htr₁ : 0 ≤ Matrix.trace (M ^ ((n + 1) + (n + 1))) := by
    rw [trace_pow_split]
    exact sum_nonneg fun p _ => mul_nonneg (hA _ _) (hA _ _)
  calc
    _ = (∑ p : V × V × V, T p) ^ 2 := by simp only [Fintype.sum_prod_type, T, U, A₂]
    _ ≤ (∑ p : V × V × V, T p * (X p / Y p)) * ∑ p : V × V × V, T p * (Y p / X p) :=
      sum_mass_ratio_square T X Y hT (fun _ => hA _ _) (fun _ => hB _ _) hs
    _ ≤ Matrix.trace (M ^ ((n + 1) + (n + 1))) *
        (((n + 2 : ℕ) : ℝ) * α * Matrix.trace (M ^ ((n + 2) + (n + 2)))) :=
      mul_le_mul h₁ h₂ hT₂ htr₁
    _ = _ := by ring

noncomputable def closedWeight {V : Type} (M : Matrix V V ℝ) {n : ℕ} (x : Fin (n + 1) → V) : ℝ :=
  pathWeight M n (x 0) (Fin.tail x) (x 0)

theorem closedWeight_eq_prod {V : Type} (M : Matrix V V ℝ) {n : ℕ}
    (x : Fin (n + 2) → V) :
    closedWeight M x = ∏ i : Fin (n + 2), M (x i) (x (i + 1)) := by
  unfold closedWeight
  rw [pathWeight_eq_prod]
  have hy : (Fin.cons (α := fun _ => V) (x 0) (Fin.snoc (Fin.tail x) (x 0))) =
      Fin.snoc x (x 0) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last, Fin.succ_last, Fin.snoc_last]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · rw [Fin.castSucc_succ, Fin.cons_succ, Fin.snoc_castSucc, ← Fin.castSucc_succ, Fin.snoc_castSucc]
        rfl
  simp only [hy]
  apply Fintype.prod_congr
  intro i
  rw [Fin.snoc_castSucc]
  congr 1
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.succ_last, Fin.snoc_last]
    congr 1
    apply Fin.ext
    have h1 : ((1 : Fin (n + 2)) : ℕ) = 1 := by simp
    rw [Fin.val_add, Fin.val_last, h1, Fin.val_zero, Nat.mod_self]
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    congr 1
    apply Fin.ext
    have h1 : ((1 : Fin (n + 2)) : ℕ) = 1 := by simp
    rw [Fin.val_add, Fin.val_castSucc, h1, Fin.val_succ]
    exact (Nat.mod_eq_of_lt (show j.val + 1 < n + 2 from j.succ.isLt)).symm

private def cyclePrefixIndex (n : ℕ) (i : Fin (n + 2)) :
    Fin (((n + 1) + (n + 1)) + 2) :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

private def packClosedCycle {V : Type} (n : ℕ) (a b : V) (x : Fin (n + 1) → V)
    (c : V) (y : Fin n → V) : Fin (((n + 1) + (n + 1)) + 2) → V :=
  Fin.cons a (Fin.cons b (Fin.append x (Fin.cons c y)))

private theorem packClosedCycle_zero {V : Type} (n : ℕ) (a b : V) (x : Fin (n + 1) → V)
    (c : V) (y : Fin n → V) : packClosedCycle n a b x c y 0 = a :=
  Fin.cons_zero _ _

private theorem packClosedCycle_prefix {V : Type} (n : ℕ) (a b : V) (x : Fin (n + 1) → V)
    (c : V) (y : Fin n → V) (i : Fin (n + 2)) :
    packClosedCycle n a b x c y (cyclePrefixIndex n i) = Fin.cons (α := fun _ => V) b x i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change Fin.cons (α := fun _ => V) a
        (Fin.cons b (Fin.append x (Fin.cons c y))) (Fin.succ 0) = _
    simp
  · change Fin.cons (α := fun _ => V) a
        (Fin.cons b (Fin.append x (Fin.cons c y))) ((Fin.castAdd (n + 1) j).succ.succ) = _
    simp only [Fin.cons_succ, Fin.append_left]

private theorem closedWeight_pack {V : Type} (M : Matrix V V ℝ) (n : ℕ) (a b : V)
    (x : Fin (n + 1) → V) (c : V) (y : Fin n → V) :
    closedWeight M (packClosedCycle n a b x c y) =
      M a b * pathWeight M (n + 1) b x c * pathWeight M n c y a := by
  simp only [closedWeight, packClosedCycle, Fin.cons_zero, Fin.tail_cons,
    pathWeight_cons, pathWeight_append_cons, mul_assoc]

private theorem sum_over_packClosedCycle {V : Type} [Fintype V] (n : ℕ)
    (F : (Fin (((n + 1) + (n + 1)) + 2) → V) → ℝ) :
    (∑ z, F z) = ∑ a, ∑ b, ∑ x, ∑ c, ∑ y, F (packClosedCycle n a b x c y) := by
  let e₀ : V × (Fin n → V) ≃ (Fin (n + 1) → V) := Fin.consEquiv (fun _ : Fin (n + 1) => V)
  let e₁ : (Fin (n + 1) → V) × V × (Fin n → V) ≃
      (Fin ((n + 1) + (n + 1)) → V) :=
    (Equiv.prodCongr (Equiv.refl _) e₀).trans (Fin.appendEquiv _ _)
  let e₂ : V × (Fin (n + 1) → V) × V × (Fin n → V) ≃
      (Fin (((n + 1) + (n + 1)) + 1) → V) :=
    (Equiv.prodCongr (Equiv.refl _) e₁).trans (Fin.consEquiv (fun _ : Fin (((n + 1) + (n + 1)) + 1) => V))
  let e : V × V × (Fin (n + 1) → V) × V × (Fin n → V) ≃
      (Fin (((n + 1) + (n + 1)) + 2) → V) :=
    (Equiv.prodCongr (Equiv.refl _) e₂).trans (Fin.consEquiv (fun _ : Fin (((n + 1) + (n + 1)) + 2) => V))
  have h := (Fintype.sum_equiv e (fun p => F (packClosedCycle n p.1 p.2.1 p.2.2.1
    p.2.2.2.1 p.2.2.2.2)) F (fun _ => rfl)).symm
  simpa only [Fintype.sum_prod_type] using h

/-- Summing over closed walks with a restriction on the first half factors the return path. -/
theorem sum_closedWeight_prefix {V : Type} [Fintype V] (M : Matrix V V ℝ) (n : ℕ)
    (P : V → (Fin (n + 2) → V) → Prop) :
    (∑ z : Fin (((n + 1) + (n + 1)) + 2) → V,
      if P (z 0) (fun i => z (cyclePrefixIndex n i)) then closedWeight M z else 0) =
    ∑ a : V, ∑ b : V, ∑ c : V, M a b *
      (∑ x : Fin (n + 1) → V, if P a (Fin.cons (α := fun _ => V) b x)
        then pathWeight M (n + 1) b x c else 0) * (M ^ (n + 1)) c a := by
  classical
  rw [sum_over_packClosedCycle]
  simp only [packClosedCycle_zero, packClosedCycle_prefix, closedWeight_pack]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro x _
  by_cases hx : P a (Fin.cons (α := fun _ => V) b x)
  · simp only [hx, if_true, ← mul_sum, sum_pathWeight_eq_pow]
  · simp [hx]

theorem sum_closedWeight_eq_trace {V : Type} [Fintype V] (M : Matrix V V ℝ) (n : ℕ) :
    (∑ z : Fin (((n + 1) + (n + 1)) + 2) → V, closedWeight M z) =
      Matrix.trace (M ^ ((n + 2) + (n + 2))) := by
  have h := sum_closedWeight_prefix M n (fun _ _ => True)
  simp only [if_true, sum_pathWeight_eq_pow] at h
  rw [h, show (n + 2) + (n + 2) = (n + 3) + (n + 1) by omega,
    trace_pow_split, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  calc
    _ = (∑ b : V, M a b * (M ^ (n + 2)) b c) * (M ^ (n + 1)) c a := by rw [sum_mul]
    _ = (M ^ (n + 3)) a c * (M ^ (n + 1)) c a := by
      rw [show M ^ (n + 3) = M * M ^ (n + 2) from pow_succ' _ _, Matrix.mul_apply]

private def translateWord {V : Type} {n : ℕ} (j : Fin (n + 2)) :
    (Fin (n + 2) → V) ≃ (Fin (n + 2) → V) where
  toFun x i := x (i + j)
  invFun x i := x (i - j)
  left_inv x := funext fun _ => by simp
  right_inv x := funext fun _ => by simp

private theorem closedWeight_translate {V : Type} (M : Matrix V V ℝ) {n : ℕ}
    (j : Fin (n + 2)) (x : Fin (n + 2) → V) :
    closedWeight M (translateWord j x) = closedWeight M x := by
  rw [closedWeight_eq_prod, closedWeight_eq_prod]
  let e : Fin (n + 2) ≃ Fin (n + 2) :=
    ⟨fun i => i + j, fun i => i - j, fun _ => by simp, fun _ => by simp⟩
  apply Fintype.prod_equiv e
  intro i
  change M (x (i + j)) (x ((i + 1) + j)) = M (x (i + j)) (x ((i + j) + 1))
  rw [add_right_comm]

private theorem conflict_detected_by_translation {V : Type} (conflict : V → V → Prop)
    (hsym : ∀ ⦃u v⦄, conflict u v → conflict v u)
    (n : ℕ) (z : Fin (((n + 1) + (n + 1)) + 2) → V)
    (hb : ∃ i j, i ≠ j ∧ conflict (z i) (z j)) :
    ∃ j : Fin (((n + 1) + (n + 1)) + 2), ∃ i : Fin (n + 2),
      conflict ((translateWord j z) 0) ((translateWord j z) (cyclePrefixIndex n i)) := by
  let L := ((n + 1) + (n + 1)) + 2
  have detect (i j : Fin L) (hij : i < j) (h : conflict (z i) (z j)) :
      ∃ j' : Fin L, ∃ p : Fin (n + 2),
        conflict ((translateWord j' z) 0) ((translateWord j' z) (cyclePrefixIndex n p)) := by
    have hlt : i.val < j.val := hij
    by_cases hp : j.val - i.val ≤ n + 2
    · let p : Fin (n + 2) := ⟨j.val - i.val - 1, by omega⟩
      have he : cyclePrefixIndex n p + i = j := by
        apply Fin.ext
        rw [Fin.val_add]
        have hw : (cyclePrefixIndex n p).val + i.val = j.val := by
          change j.val - i.val - 1 + 1 + i.val = j.val
          omega
        rw [hw, Nat.mod_eq_of_lt j.isLt]
      refine ⟨i, p, ?_⟩
      change conflict (z (0 + i)) (z (cyclePrefixIndex n p + i))
      simpa only [zero_add, he] using h
    · have hgap : 0 < L - (j.val - i.val) := by
        have hj := j.isLt
        omega
      let p : Fin (n + 2) := ⟨L - (j.val - i.val) - 1, by dsimp [L] at *; omega⟩
      have he : cyclePrefixIndex n p + j = i := by
        apply Fin.ext
        rw [Fin.val_add]
        have hw : (cyclePrefixIndex n p).val + j.val = L + i.val := by
          change L - (j.val - i.val) - 1 + 1 + j.val = L + i.val
          have hj := j.isLt
          omega
        change ((cyclePrefixIndex n p).val + j.val) % L = i.val
        rw [hw, Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
      refine ⟨j, p, ?_⟩
      change conflict (z (0 + j)) (z (cyclePrefixIndex n p + j))
      simpa only [zero_add, he] using hsym h
  obtain ⟨i, j, hij, h⟩ := hb
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact detect i j hij h
  · exact detect j i hij (hsym h)

private theorem sum_badClosed_le_prefix {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (hM : ∀ a b, 0 ≤ M a b) (conflict : V → V → Prop)
    (hsym : ∀ ⦃u v⦄, conflict u v → conflict v u) (n : ℕ) :
    let L := ((n + 1) + (n + 1)) + 2
    (∑ z : Fin L → V,
      if ∃ i j, i ≠ j ∧ conflict (z i) (z j) then closedWeight M z else 0) ≤
    (L : ℝ) * ∑ a : V, ∑ b : V, ∑ c : V,
      M a b * badPrefixWeight M conflict n a b c * (M ^ (n + 1)) c a := by
  classical
  intro L
  let front : (Fin L → V) → Prop :=
    fun z => ∃ i : Fin (n + 2), conflict (z 0) (z (cyclePrefixIndex n i))
  let w : (Fin L → V) → ℝ := closedWeight M
  have hw (z : Fin L → V) : 0 ≤ w z := pathWeight_nonneg M hM _ _ _ _
  have hfront :
      (∑ z : Fin L → V, if front z then w z else 0) =
        ∑ a : V, ∑ b : V, ∑ c : V,
          M a b * badPrefixWeight M conflict n a b c * (M ^ (n + 1)) c a := by
    convert! sum_closedWeight_prefix M n (fun a x => ∃ i, conflict a (x i))
    unfold badPrefixWeight
    apply sum_congr rfl
    intro z _
    split_ifs <;> rfl
  calc
    _ ≤ ∑ z : Fin L → V, ∑ j : Fin L, if front (translateWord j z) then w z else 0 := by
      apply sum_le_sum
      intro z _
      by_cases hb : ∃ i j, i ≠ j ∧ conflict (z i) (z j)
      · obtain ⟨j, hj⟩ := conflict_detected_by_translation conflict hsym n z hb
        have h : front (translateWord j z) := hj
        simp only [if_pos hb]
        exact (le_of_eq (if_pos h).symm).trans
          (single_le_sum (f := fun j : Fin L => if front (translateWord j z) then w z else 0)
            (fun k _ => by split <;> first | exact hw z | rfl) (mem_univ j))
      · simp only [if_neg hb]
        exact sum_nonneg fun j _ => by split <;> first | exact hw z | rfl
    _ = ∑ j : Fin L, ∑ z : Fin L → V, if front (translateWord j z) then w z else 0 := sum_comm
    _ = ∑ _j : Fin L, ∑ z : Fin L → V, if front z then w z else 0 := by
      apply sum_congr rfl
      intro j _
      apply Fintype.sum_equiv (translateWord j)
      intro z
      rw [show w (translateWord j z) = w z from closedWeight_translate M j z]
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hfront]

/-- A reversible kernel with small local conflicts has a conflict-free closed walk of the given length. -/
theorem exists_conflict_free_kernel_cycle {V : Type} [Fintype V] [Nonempty V]
    (M : Matrix V V ℝ) (w : V → ℝ) (hw : ∀ a, 0 < w a)
    (hM : ∀ u v, 0 ≤ M u v) (hrow : ∀ a, ∑ b : V, M a b = 1)
    (hbal : ∀ a b, w a * M a b = w b * M b a)
    (conflict : V → V → Prop) (hsym : ∀ ⦃u v⦄, conflict u v → conflict v u)
    (α : ℝ) (hα : 0 ≤ α)
    (hloc : ∀ u v, ∑ a : V, (if conflict a u then M v a else 0) ≤ α)
    (n : ℕ)
    (hsmall : (Fintype.card V : ℝ) * (4 * ((n + 2 : ℕ) : ℝ) ^ 3 * α) ^ (n + 2) < 1) :
    let L := ((n + 1) + (n + 1)) + 2
    ∃ x : Fin L → V, (∀ i, 0 < M (x i) (x (i + 1))) ∧
      ∀ i j, i ≠ j → ¬ conflict (x i) (x j) := by
  classical
  intro L
  let k := n + 2
  let T (j : ℕ) := Matrix.trace (M ^ (j + j))
  let K : ℝ := k
  let β := 4 * K ^ 3 * α
  let bad (x : Fin L → V) : Prop := ∃ i j, i ≠ j ∧ conflict (x i) (x j)
  let S := ∑ x : Fin L → V, if bad x then closedWeight M x else 0
  let U := ∑ a : V, ∑ b : V, ∑ c : V,
    M a b * badPrefixWeight M conflict n a b c * (M ^ (n + 1)) c a
  have ht (j : ℕ) : 1 ≤ T j := one_le_even_trace M w hw hbal hrow j
  have htpos (j : ℕ) : 0 < T j := zero_lt_one.trans_le (ht j)
  have hcv (j : ℕ) : (T (j + 1)) ^ 2 ≤ T j * T (j + 2) := even_trace_logConvex M w hw hbal j
  have hk : 0 < k := by dsimp [k]; omega
  have hprev : k - 1 = n + 1 := rfl
  have hinterp := logConvex_nat_interpolation T htpos hcv hk
  have hzero : T 0 = (Fintype.card V : ℝ) := by simp [T, Matrix.trace_one]
  rw [hzero] at hinterp
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hβlt : β * T (k - 1) < T k := by
    have hp : (β * T (k - 1)) ^ k < (T k) ^ k := by
      calc
        _ = β ^ k * (T (k - 1)) ^ k := mul_pow _ _ _
        _ ≤ β ^ k * ((Fintype.card V : ℝ) * (T k) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left hinterp (by positivity)
        _ = (Fintype.card V : ℝ) * β ^ k * (T k) ^ (k - 1) := by ring
        _ < 1 * (T k) ^ (k - 1) :=
          mul_lt_mul_of_pos_right hsmall (pow_pos (htpos k) _)
        _ ≤ _ := by
          rw [one_mul]
          exact pow_le_pow_right₀ (ht k) (Nat.sub_le _ _)
    by_contra! h
    exact (not_le_of_gt hp) (pow_le_pow_left₀ (htpos k).le h k)
  have hS : S ≤ (L : ℝ) * U := sum_badClosed_le_prefix M hM conflict hsym n
  have hS0 : 0 ≤ S := by
    apply sum_nonneg
    intro x _
    split <;> first | exact pathWeight_nonneg M hM _ _ _ _ | rfl
  have hU : U ^ 2 ≤ K * α * T (k - 1) * T k := by
    rw [hprev]
    exact badHalfWalk_mass_square M w hw hM hrow hbal conflict α hα hloc n
  have hL : (L : ℝ) = 2 * K := by
    change (L : ℝ) = 2 * (k : ℝ)
    exact_mod_cast (show L = 2 * k by dsimp [L, k]; omega)
  have hSq : S ^ 2 < (T k) ^ 2 := by
    calc
      _ ≤ ((L : ℝ) * U) ^ 2 := pow_le_pow_left₀ hS0 hS 2
      _ = (L : ℝ) ^ 2 * U ^ 2 := mul_pow _ _ _
      _ ≤ (L : ℝ) ^ 2 * (K * α * T (k - 1) * T k) :=
        mul_le_mul_of_nonneg_left hU (sq_nonneg _)
      _ = (β * T (k - 1)) * T k := by rw [hL]; dsimp [β]; ring
      _ < _ := by simpa only [pow_two] using mul_lt_mul_of_pos_right hβlt (htpos k)
  have hbad : S < T k := by
    by_contra! h
    exact (not_le_of_gt hSq) (pow_le_pow_left₀ (htpos k).le h 2)
  have hsum : ∑ x : Fin L → V, closedWeight M x = T k := sum_closedWeight_eq_trace M n
  obtain ⟨x, hx, hxb⟩ : ∃ x : Fin L → V, closedWeight M x ≠ 0 ∧ ¬ bad x := by
    by_contra! h
    apply (not_le_of_gt hbad)
    rw [← hsum]
    apply sum_le_sum
    intro x _
    by_cases hb : bad x
    · exact le_of_eq (if_pos hb).symm
    · have hx : closedWeight M x = 0 := by
        by_contra hn
        exact hb (h x hn)
      simp [hx]
  refine ⟨x, fun i => ?_, fun i j hij hc => hxb ⟨i, j, hij, hc⟩⟩
  by_contra! hi
  have hz : M (x i) (x (i + 1)) = 0 := le_antisymm hi (hM _ _)
  apply hx
  rw [closedWeight_eq_prod]
  exact Finset.prod_eq_zero (mem_univ i) hz

/-- A cycle without conflicts in a finite graph from its local neighbor proportion. -/
theorem conflict_free_cycle_of_ratio {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hdegree : ∀ v, 0 < G.degree v)
    (conflict : V → V → Prop) (hsym : ∀ ⦃u v⦄, conflict u v → conflict v u)
    (α : ℝ) (hα : 0 ≤ α)
    (hloc : ∀ u v, (((G.neighborFinset v).filter (conflict u)).card : ℝ) ≤ α * G.degree v)
    (n : ℕ)
    (hsmall : (Fintype.card V : ℝ) * (4 * ((n + 2 : ℕ) : ℝ) ^ 3 * α) ^ (n + 2) < 1) :
    let L := ((n + 1) + (n + 1)) + 2
    ∃ f : cycleGraph L →g G, ∀ i j, i ≠ j → ¬ conflict (f i) (f j) := by
  classical
  intro L
  let w (v : V) : ℝ := G.degree v
  let M : Matrix V V ℝ := fun u v => if G.Adj u v then (w u)⁻¹ else 0
  have hw (v : V) : 0 < w v := by
    dsimp [w]
    exact_mod_cast hdegree v
  have hM (u v : V) : 0 ≤ M u v := by
    change 0 ≤ if G.Adj u v then (w u)⁻¹ else 0
    split <;> positivity
  have hrow (u : V) : ∑ v : V, M u v = 1 := by
    calc
      _ = ∑ _v ∈ G.neighborFinset u, (w u)⁻¹ := by
        have hf : G.neighborFinset u = univ.filter (G.Adj u) := by
          ext v
          simp [mem_neighborFinset]
        rw [hf, sum_filter]
      _ = _ := by
        rw [sum_const, nsmul_eq_mul, card_neighborFinset_eq_degree]
        exact mul_inv_cancel₀ (hw u).ne'
  have hbal (u v : V) : w u * M u v = w v * M v u := by
    by_cases h : G.Adj u v
    · simp only [M, if_pos h, if_pos h.symm, mul_inv_cancel₀ (hw u).ne', mul_inv_cancel₀ (hw v).ne']
    · have h' : ¬ G.Adj v u := fun hv => h hv.symm
      simp [M, h, h']
  have hlocM (u v : V) : ∑ a : V, (if conflict a u then M v a else 0) ≤ α := by
    let S := (G.neighborFinset v).filter (conflict u)
    have hS : S = univ.filter (fun a => G.Adj v a ∧ conflict u a) := by
      ext a
      simp [S, mem_neighborFinset]
    have hnum : (S.card : ℝ) ≤ α * w v := hloc u v
    calc
      _ = ∑ _a ∈ S, (w v)⁻¹ := by
        rw [hS, sum_filter]
        apply sum_congr rfl
        intro a _
        by_cases hv : G.Adj v a <;> by_cases hu : conflict u a
        · simp [M, hv, hu, hsym hu]
        · have h' : ¬ conflict a u := fun hc => hu (hsym hc)
          simp [M, hv, hu, h']
        · simp [M, hv]
        · simp [M, hv]
      _ ≤ α := by
        rw [sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
        exact (div_le_iff₀ (hw v)).2 hnum
  obtain ⟨x, hpos, hdisj⟩ := exists_conflict_free_kernel_cycle M w hw hM hrow hbal
    conflict hsym α hα hlocM n hsmall
  have hpath (i : Fin L) : G.Adj (x i) (x (i + 1)) := by
    by_contra hi
    simpa only [M, if_neg hi, lt_self_iff_false] using hpos i
  refine ⟨⟨x, fun {i j} hij => ?_⟩, hdisj⟩
  rcases cycleGraph_adj.mp hij with h | h
  · have he : i = j + 1 := sub_eq_iff_eq_add'.mp h
    rw [he]
    exact (hpath j).symm
  · have he : j = i + 1 := sub_eq_iff_eq_add'.mp h
    rw [he]
    exact hpath i

/-- The finite conflict-cycle principle follows from a power bound on the local overlap. -/
theorem sparseConflictCycles_of_ratio (N b c n : ℕ) (hb : 0 < b)
    (hsmall : (N : ℝ) * (4 * ((n + 2 : ℕ) : ℝ) ^ 3 * (c : ℝ) / b) ^ (n + 2) < 1) :
    SparseConflictCycles N b c (((n + 1) + (n + 1)) + 2) := by
  classical
  intro V _ hcard G conflict hsym he hloc
  let S := G.support
  let B := G.induce S
  let conflictS (u v : S) := conflict u.val v.val
  have hne : Nonempty S := by
    obtain ⟨e, he⟩ := he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have h : G.Adj a b := by simpa using he
      exact ⟨⟨a, h.mem_support_left⟩⟩
  have hfilter (v : S) (P : V → Prop) :
      (((B.neighborFinset v).filter fun u => P u.val).map (Function.Embedding.subtype _)) =
        (G.neighborFinset v.val).filter P := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      obtain ⟨hd, hp⟩ := mem_filter.mp hy
      have hBy : B.Adj v y := (mem_neighborFinset B v y).mp hd
      exact mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hBy, hp⟩
    · intro hx
      obtain ⟨hd, hp⟩ := mem_filter.mp hx
      have ha : G.Adj v.val x := (mem_neighborFinset _ _ _).mp hd
      let y : S := ⟨x, ha.mem_support_right⟩
      exact mem_map.mpr ⟨y, mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr ha, hp⟩, rfl⟩
  have hdeg (v : S) : B.degree v = G.degree v.val := by
    have h := congrArg Finset.card (hfilter v (fun _ => True))
    simpa [card_map, card_neighborFinset_eq_degree] using h
  have hdegree (v : S) : 0 < B.degree v := by
    rw [hdeg]
    exact (G.degree_pos_iff_mem_support v.val).mpr v.property
  have hlocS (u v : S) :
      (((B.neighborFinset v).filter (conflictS u)).card : ℝ) ≤ ((c : ℝ) / b) * B.degree v := by
    have h := congrArg Finset.card (hfilter v (conflict u.val))
    have h' : ((B.neighborFinset v).filter (conflictS u)).card =
        ((G.neighborFinset v.val).filter (conflict u.val)).card := by
      simpa only [card_map, conflictS] using h
    rw [h', hdeg, div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hb)]
    have hh : (b : ℝ) * ((G.neighborFinset v.val).filter (conflict u.val)).card ≤
        (c : ℝ) * G.degree v.val := by
      exact_mod_cast hloc u.val v.val
    simpa only [mul_comm (b : ℝ)] using hh
  have hS : (Fintype.card S : ℝ) ≤ N := by
    exact_mod_cast (Fintype.card_le_of_injective (fun u : S => (u : V)) Subtype.val_injective).trans hcard
  have hsmall' : (Fintype.card S : ℝ) * (4 * ((n + 2 : ℕ) : ℝ) ^ 3 *
      ((c : ℝ) / b)) ^ (n + 2) < 1 := by
    rw [← mul_div_assoc]
    exact (mul_le_mul_of_nonneg_right hS (by positivity)).trans_lt hsmall
  obtain ⟨f, hf⟩ := conflict_free_cycle_of_ratio B hdegree conflictS
    (fun {u v} h => hsym h) ((c : ℝ) / b) (by positivity) hlocS n hsmall'
  exact ⟨(Copy.induce G S).toHom.comp f, hf⟩

private theorem card_filter_eq_le_one {V : Type} (s : Finset V) (b : V) :
    (s.filter (· = b)).card ≤ 1 := by
  classical
  have hs : s.filter (· = b) ⊆ {b} := by
    intro x hx
    exact mem_singleton.mpr (mem_filter.mp hx).2
  simpa using card_le_card hs

private theorem injective_of_packed_eq {V : Type} [Fintype V] {t : ℕ} {x : Fin t → V}
    (hx : x ∈ packedTuples univ Eq t) : Function.Injective x := by
  intro i j he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (mem_packedTuples.mp hx).2 i j h he
  · exact (mem_packedTuples.mp hx).2 j i h he.symm

/-- The complete-link tuple construction for an even regular witness. -/
theorem contains_even_cycle_blowup {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (t l θ : ℕ) (ht : 0 < t) (hθ : 0 < θ) (hθt : 4 * t ≤ θ) (d : ℝ)
    (hd : (t : ℝ) ≤ d) (hdeg : ∀ v, d ≤ (G.degree v : ℝ))
    (hpow : 10 * (θ : ℝ) * (Fintype.card V : ℝ) ^ (t - 1) ≤ (d - t) ^ t)
    (findCycle : SparseConflictCycles (Fintype.card V ^ t) θ (8 * 2 ^ t * t ^ 2 * 1) l) :
    independentBlowup (cycleGraph l) t ⊑ G := by
  classical
  let P := packedTuples (univ : Finset V) Eq t
  let Q (x y : Fin t → V) := ∀ i j, G.Adj (x i) (y j)
  let common (x : Fin t → V) := (univ : Finset V).filter fun v => ∀ i, G.Adj (x i) v
  let m : ℝ := Fintype.card V
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos (α := V)
  let nh (v : V) := (univ : Finset V).filter fun f => G.Adj f v
  have hnh (v : V) : nh v = G.neighborFinset v := by
    ext f
    simp [nh, mem_neighborFinset, adj_comm]
  have hsum := sum_card_packed_lower univ univ_nonempty nh Eq 1 t d (by simpa using hd)
    (by
      calc
        _ = ∑ _v : V, d := by simp [sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum (fun v _ => by
          simpa only [hnh, card_neighborFinset_eq_degree] using hdeg v))
    (fun v _ b _ => card_filter_eq_le_one (nh v) b)
  have hcount : (∑ v : V, ((packedTuples (nh v) Eq t).card : ℝ)) =
      ∑ x ∈ P, ((common x).card : ℝ) := by
    exact_mod_cast sum_card_packed_neighborhoods (univ : Finset V) G.Adj Eq t
  have havg : m * (d - t) ^ t ≤ ∑ x ∈ P, ((common x).card : ℝ) := by
    simpa only [card_univ, Nat.cast_one, mul_one, hcount] using hsum
  have hPne : P.Nonempty := by
    by_contra! h
    rw [h, sum_empty] at havg
    have hp := (show 0 < 10 * (θ : ℝ) * m ^ (t - 1) by positivity).trans_le hpow
    exact (not_lt_of_ge havg) (mul_pos hm hp)
  have hP : (P.card : ℝ) ≤ m ^ t := by
    have h := packed_size_le (univ : Finset V) Eq t
    rw [card_univ] at h
    dsimp [m]
    exact_mod_cast h
  have hmPow : m ^ t = m ^ (t - 1) * m :=
    (congrArg (fun k : ℕ => m ^ k) (show t = (t - 1) + 1 by omega)).trans (pow_succ _ _)
  have hmean : (P.card : ℝ) * (10 * θ) ≤ ∑ x ∈ P, ((common x).card : ℝ) := by
    calc
      _ ≤ m ^ t * (10 * θ) := mul_le_mul_of_nonneg_right hP (by positivity)
      _ = m * (10 * θ * m ^ (t - 1)) := by rw [hmPow]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hpow hm.le).trans havg
  have hcap (x : Fin t → V) (_ : x ∈ P) (b : V) :
      ((common x).filter fun a => a = b).card ≤ 2 * 1 :=
    (card_filter_eq_le_one (common x) b).trans (by norm_num)
  have hs := sum_packing_degrees_of_average P hPne common Eq 1 θ ht hθ
    (by simpa using hθt) hmean hcap
  have hneigh (x : Fin t → V) : P.filter (Q x) = packedTuples (common x) Eq t := by
    ext y
    simp only [P, Q, common, mem_filter, mem_packedTuples, mem_univ, true_and]
    tauto
  have hsym ⦃x y⦄ (h : Q x y) : Q y x := fun i j => (h j i).symm
  have hirr : ∀ x, ¬ Q x x := by
    intro x h
    exact G.irrefl (h ⟨0, ht⟩ ⟨0, ht⟩)
  obtain ⟨U, hu, hne, hU⟩ := exists_sparse_tuple_core Eq t 1 θ ht hθ
    (by simpa using hθt) Q common hsym hirr (fun x => by convert! hneigh x) hcap hs
  obtain ⟨x, hx, hstep, hdisj⟩ := exists_cycle_of_sparse_tuple_core Eq t l θ _
    Q (fun {_ _} h => h.symm) hsym hirr findCycle U hu hne
    (fun z hz => (hU z hz).1) (fun z hz => (hU z hz).2)
  refine ⟨⟨⟨fun p => x p.1 p.2, ?_⟩, ?_⟩⟩
  · rintro ⟨i, a⟩ ⟨j, b⟩ hij
    exact hstep i j hij a b
  · rintro ⟨i, a⟩ ⟨j, b⟩ he
    have he' : x i a = x j b := he
    have hij : i = j := by
      by_contra hne
      exact hdisj i j hne ⟨a, b, he'.symm⟩
    subst j
    exact Prod.ext rfl (injective_of_packed_eq (hx i) he')

private theorem eventually_even_scales (t : ℕ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    let a := 1 - 1 / (t : ℝ) + ε
    let c : ℕ := 8 * 2 ^ t * t ^ 2 * 1
    ∃ k : ℕ, ∀ᶠ m : ℕ in atTop, ∃ θ : ℕ,
      0 < θ ∧ 4 * t ≤ θ ∧ (t : ℝ) ≤ 20 * t * (m : ℝ) ^ a ∧
      10 * (θ : ℝ) * (m : ℝ) ^ (t - 1) ≤ (20 * (t : ℝ) * (m : ℝ) ^ a - t) ^ t ∧
      ((m ^ t : ℕ) : ℝ) * (4 * ((k + 2 : ℕ) : ℝ) ^ 3 * (c : ℝ) / θ) ^ (k + 2) < 1 := by
  intro a c
  let δ := (t : ℝ) * ε / 2
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t from ht)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ha : 0 ≤ a := by
    have hh := (div_le_one htR).2 ht1
    dsimp [a]
    linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((t : ℝ) / δ)
  let j := k + 2
  let K : ℝ := j
  let η := δ * K - t
  have hη : 0 < η := by
    have hh := (div_lt_iff₀ hδ).mp hk
    dsimp [η, K, j]
    rw [Nat.cast_add]
    nlinarith only [hh, hδ]
  let B := 8 * K ^ 3 * (c : ℝ)
  have hlimδ : Tendsto (fun m : ℕ => (m : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hlimη : Tendsto (fun m : ℕ => (m : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  refine ⟨k, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hlimδ.eventually_ge_atTop (8 * (t : ℝ) + 2),
    hlimη.eventually_gt_atTop (B ^ j)] with m hm hδm hηm
  let θ := ⌊(m : ℝ) ^ δ⌋₊
  let mR : ℝ := m
  have hmR : 1 ≤ mR := by dsimp [mR]; exact_mod_cast hm
  have hmpos : 0 < mR := zero_lt_one.trans_le hmR
  have hθupper : (θ : ℝ) ≤ mR ^ δ := Nat.floor_le (by positivity)
  have hθlower : mR ^ δ / 2 ≤ θ := by
    have hf := Nat.lt_floor_add_one (mR ^ δ)
    change mR ^ δ < (θ : ℝ) + 1 at hf
    change 8 * (t : ℝ) + 2 ≤ mR ^ δ at hδm
    linarith
  have hθt : 4 * t ≤ θ := by
    have h : 4 * (t : ℝ) ≤ θ := by
      change 8 * (t : ℝ) + 2 ≤ mR ^ δ at hδm
      linarith only [hδm, hθlower]
    exact_mod_cast h
  have hθ : 0 < θ := by omega
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  let d := 20 * (t : ℝ) * mR ^ a
  have hd : 2 * (t : ℝ) ≤ d := by
    have h := mul_le_mul_of_nonneg_left (Real.one_le_rpow hmR ha) (by positivity : 0 ≤ 20 * (t : ℝ))
    dsimp [d]
    linarith only [h, htR]
  have hpower : 10 * (θ : ℝ) * mR ^ (t - 1) ≤ (d - t) ^ t := by
    have hconst : (10 : ℝ) ≤ (10 * (t : ℝ)) ^ t :=
      (show (10 : ℝ) ≤ 10 * (t : ℝ) by linarith only [ht1]).trans
        (le_self_pow₀ (by linarith only [ht1]) (by omega))
    have hθeps : (θ : ℝ) ≤ mR ^ ((t : ℝ) * ε) :=
      hθupper.trans (Real.rpow_le_rpow_of_exponent_le hmR (by dsimp [δ]; nlinarith only [mul_pos htR hε]))
    have hpow : (mR ^ a) ^ t = mR ^ (a * (t : ℝ)) := by
      rw [Real.rpow_mul hmpos.le, Real.rpow_natCast]
    have hexp : a * (t : ℝ) = ((t - 1 : ℕ) : ℝ) + (t : ℝ) * ε := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      dsimp [a]
      field_simp [htR.ne']
    calc
      _ ≤ (10 * (t : ℝ)) ^ t * mR ^ ((t : ℝ) * ε) * mR ^ (t - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hconst hθeps hθR.le (by positivity)) (by positivity)
      _ = (d / 2) ^ t := by
        have hd' : d / 2 = (10 * (t : ℝ)) * mR ^ a := by dsimp [d]; ring
        rw [hd', mul_pow (10 * (t : ℝ)) (mR ^ a), hpow, hexp, Real.rpow_add hmpos,
          Real.rpow_natCast]
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith only [hd]) _
  refine ⟨θ, hθ, hθt, by exact le_trans (by linarith only [htR]) hd, hpower, ?_⟩
  have hratio : 4 * K ^ 3 * (c : ℝ) / θ ≤ B / mR ^ δ := by
    have hdv : (1 : ℝ) / θ ≤ 2 / mR ^ δ := by
      rw [div_le_div_iff₀ hθR (Real.rpow_pos_of_pos hmpos _)]
      linarith only [hθlower]
    calc
      _ = (4 * K ^ 3 * (c : ℝ)) * (1 / θ) := by ring
      _ ≤ (4 * K ^ 3 * (c : ℝ)) * (2 / mR ^ δ) :=
        mul_le_mul_of_nonneg_left hdv (by positivity)
      _ = _ := by dsimp [B]; ring
  have hmδ : (mR ^ δ) ^ j = mR ^ (δ * K) := by
    rw [show K = (j : ℝ) from rfl, Real.rpow_mul hmpos.le, Real.rpow_natCast]
  have hfinal : mR ^ t * (B / mR ^ δ) ^ j < 1 := by
    have he : mR ^ t / (mR ^ δ) ^ j = (mR ^ η)⁻¹ := by
      rw [hmδ, ← Real.rpow_natCast, ← Real.rpow_sub hmpos, ← Real.rpow_neg hmpos.le]
      congr 1
      dsimp [η]
      ring
    calc
      _ = B ^ j * (mR ^ t / (mR ^ δ) ^ j) := by rw [div_pow]; ring
      _ = B ^ j / mR ^ η := by rw [he, div_eq_mul_inv]
      _ < _ := (div_lt_one (Real.rpow_pos_of_pos hmpos _)).2 hηm
  rw [Nat.cast_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio j) (by positivity)).trans_lt hfinal

/-- Even-degree cycle blow-ups have the conjectured extremal bound. -/
theorem even_cycle_blowup_bound (t : ℕ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    ∃ l : ℕ, 4 ≤ l ∧ Even l ∧
      (fun m : ℕ => (extremalNumber m (independentBlowup (cycleGraph l) t) : ℝ)) =O[atTop]
        fun m : ℕ => (m : ℝ) ^ (2 - 1 / (t : ℝ) + ε) := by
  classical
  let a := 1 - 1 / (t : ℝ) + ε
  let c : ℕ := 8 * 2 ^ t * t ^ 2 * 1
  obtain ⟨k, he⟩ := eventually_even_scales t ht ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let l := ((k + 1) + (k + 1)) + 2
  refine ⟨l, by dsimp [l]; omega, ⟨k + 2, by dsimp [l]; omega⟩, ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t from ht)
  have ha : 0 ≤ a := by
    have hh := (div_le_one (by positivity : 0 < (t : ℝ))).2 ht1
    dsimp [a]
    linarith
  let C : ℝ := N + 20 * t
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb := extremal_of_degree_threshold (independentBlowup (cycleGraph l) t) ha hC (by
    intro V _ _ G hd
    let m := Fintype.card V
    have hm : 1 ≤ m := Fintype.card_pos (α := V)
    have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    by_cases hmN : N ≤ m
    · obtain ⟨θ, hθ, hθt, hdeg, hp, hsmall⟩ := hN m hmN
      have hdeg' (v : V) : 20 * (t : ℝ) * (m : ℝ) ^ a ≤ (G.degree v : ℝ) := by
        apply le_of_lt
        exact (mul_le_mul_of_nonneg_right (by dsimp [C]; exact le_add_of_nonneg_left (by positivity) : 20 * (t : ℝ) ≤ C)
          (by positivity)).trans_lt (hd v)
      exact contains_even_cycle_blowup G t l θ ht hθ hθt _ hdeg hdeg' hp
        (sparseConflictCycles_of_ratio (m ^ t) θ c k hθ hsmall)
    · obtain ⟨v⟩ := (inferInstance : Nonempty V)
      have hc : (N : ℝ) ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
      have hpow : 1 ≤ (m : ℝ) ^ a := Real.one_le_rpow hmR ha
      have hn : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by omega)
      have hv : (G.degree v : ℝ) < m := by exact_mod_cast G.degree_lt_card_verts v
      have hcontra : (m : ℝ) ≤ C * (m : ℝ) ^ a :=
        (hn.trans hc).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hC)
      exact (not_lt_of_ge hcontra) ((hd v).trans hv) |>.elim)
  have hExp : a + 1 = 2 - 1 / (t : ℝ) + ε := by dsimp [a]; ring
  simpa only [hExp] using hb

private theorem regular_witness_on_fin {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (r : ℕ) (hr : G.IsRegularOfDegree r) (f : ℕ → ℝ)
    (hG : (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] f) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] f := by
  classical
  let q := Fintype.card V
  let e : V ≃ Fin q := Fintype.equivFin V
  let H := G.map e
  let iso : G ≃g H := Iso.map e G
  refine ⟨q, H, Fintype.card_pos, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ : ∃ u, iso u = v := iso.toEquiv.surjective v
    rw [← hu]
    have he : H.degree (iso u) = G.degree u := by
      rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
      convert! (Fintype.card_congr (iso.mapNeighborSet u)).symm
    convert! he.trans (hr u)
  simpa only [extremalNumber_congr rfl iso.symm] using hG

private theorem cycle_degree_const {l : ℕ} (hl : 3 ≤ l) (v : Fin l) :
    (cycleGraph l).degree v = 2 := by
  have hlen : l = (l - 3) + 3 := (Nat.sub_add_cancel hl).symm
  generalize l - 3 = k at hlen
  subst l
  convert! cycleGraph_degree_three_le (v := v)

/-- Removing the edges paired by an involution decreases the degree by one. -/
def deletePairedEdges {V : Type} (G : SimpleGraph V) (f : V → V)
    (hf : Function.Involutive f) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ v ≠ f u
  symm.symm := by
    intro u v h
    refine ⟨h.1.symm, fun he => h.2 ?_⟩
    rw [he, hf v]
  loopless.irrefl := fun _ h => G.irrefl h.1

theorem degree_deletePairedEdges {V : Type} [Fintype V] (G : SimpleGraph V) (f : V → V)
    (hf : Function.Involutive f) (hadj : ∀ u, G.Adj u (f u)) (v : V) :
    (deletePairedEdges G f hf).degree v = G.degree v - 1 := by
  classical
  have hn : (deletePairedEdges G f hf).neighborFinset v = (G.neighborFinset v).erase (f v) := by
    ext u
    rw [mem_neighborFinset, mem_erase, mem_neighborFinset]
    exact and_comm
  rw [← card_neighborFinset_eq_degree, hn,
    card_erase_of_mem ((mem_neighborFinset _ _ _).mpr (hadj v)), card_neighborFinset_eq_degree]

private def pairedCyclePos {k : ℕ} (i : Fin (2 * k)) : Fin (2 * k) :=
  ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
    have hi := i.isLt
    split_ifs <;> omega⟩

private theorem pairedCyclePos_involutive (k : ℕ) :
    Function.Involutive (pairedCyclePos (k := k)) := by
  intro i
  apply Fin.ext
  simp only [pairedCyclePos]
  split_ifs <;> omega

private theorem pairedCyclePos_adj (k : ℕ) (i : Fin (2 * k)) :
    (cycleGraph (2 * k)).Adj i (pairedCyclePos i) := by
  rw [cycleGraph_adj']
  by_cases hi : i.val % 2 = 0
  · right
    have hle : i ≤ pairedCyclePos i := by
      change i.val ≤ (if i.val % 2 = 0 then i.val + 1 else i.val - 1)
      simp [hi]
    rw [Fin.coe_sub_iff_le.mpr hle]
    simp [pairedCyclePos, hi]
  · left
    have hle : pairedCyclePos i ≤ i := by
      change (if i.val % 2 = 0 then i.val + 1 else i.val - 1) ≤ i.val
      simp [hi]
    rw [Fin.coe_sub_iff_le.mpr hle]
    simp only [pairedCyclePos, if_neg hi]
    omega

/-- Both the even blow-up and its matching-deleted graph inherit the extremal estimate. -/
theorem adjacent_degrees_bound (t : ℕ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    ∀ r, (r = 2 * t ∨ r = 2 * t - 1) →
      ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
        (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
          fun n : ℕ => (n : ℝ) ^ (2 - 1 / (t : ℝ) + ε) := by
  classical
  obtain ⟨l, hl, he, hbound⟩ := even_cycle_blowup_bound t ht ε hε
  obtain ⟨k, hk⟩ := he
  have hlen : l = 2 * k := by omega
  clear hk
  subst l
  let G := independentBlowup (cycleGraph (2 * k)) t
  have hin : Nonempty (Fin (2 * k) × Fin t) :=
    ⟨(⟨0, by omega⟩, ⟨0, ht⟩)⟩
  have hreg : G.IsRegularOfDegree (2 * t) := by
    intro v
    calc
      _ = (cycleGraph (2 * k)).degree v.1 * t := by
        convert! degree_independentBlowup (cycleGraph (2 * k)) t v
      _ = _ := by rw [cycle_degree_const (by omega)]
  intro r hr
  rcases hr with rfl | rfl
  · exact regular_witness_on_fin G _ hreg _ hbound
  let f (v : Fin (2 * k) × Fin t) := (pairedCyclePos v.1, v.2)
  have hf : Function.Involutive f := by
    intro v
    exact Prod.ext (pairedCyclePos_involutive k v.1) rfl
  have hpair (v : Fin (2 * k) × Fin t) : G.Adj v (f v) := pairedCyclePos_adj k v.1
  let G' := deletePairedEdges G f hf
  have hreg' : G'.IsRegularOfDegree (2 * t - 1) := by
    intro v
    calc
      _ = G.degree v - 1 := by convert! degree_deletePairedEdges G f hf hpair v
      _ = _ := by rw [hreg v]
  have hle : G' ≤ G := fun _ _ h => h.1
  have hO : (fun n : ℕ => (extremalNumber n G' : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 - 1 / (t : ℝ) + ε) := by
    apply IsBigO.trans _ hbound
    refine isBigO_of_le _ fun n => ?_
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast (IsContained.of_le hle).extremalNumber_le (n := n)
  exact regular_witness_on_fin G' _ hreg' _ hO

/-- The exact target holds in every even degree. -/
theorem even_degree_case (r : ℕ) (hr : 3 ≤ r) (he : Even r) (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε) := by
  obtain ⟨t, ht⟩ := he
  have heq : r = 2 * t := by omega
  have htpos : 0 < t := by omega
  obtain ⟨q, H, hq, hreg, hO⟩ := adjacent_degrees_bound t htpos ε hε r (Or.inl heq)
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have hdiv : 2 / (r : ℝ) = 1 / (t : ℝ) := by
    rw [heq, Nat.cast_mul, Nat.cast_two]
    field_simp
  exact ⟨q, H, hq, hreg, by simpa only [hdiv] using hO⟩

/-- The matching-deleted blow-up gives the target when the odd-degree exponent loss fits in ε. -/
theorem odd_degree_with_error (r : ℕ) (hr : 3 ≤ r) (ho : Odd r) (ε : ℝ)
    (hε : 2 / ((r : ℝ) * ((r : ℝ) + 1)) < ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε) := by
  obtain ⟨t₀, ht₀⟩ := ho
  let t := t₀ + 1
  have ht : 0 < t := Nat.succ_pos _
  have heq : r + 1 = 2 * t := by dsimp [t]; omega
  have hr' : r = 2 * t - 1 := by omega
  let η := ε - 2 / ((r : ℝ) * ((r : ℝ) + 1))
  have hη : 0 < η := sub_pos.mpr hε
  obtain ⟨q, H, hq, hreg, hO⟩ := adjacent_degrees_bound t ht η hη r (Or.inr hr')
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have heR : (r : ℝ) + 1 = 2 * (t : ℝ) := by exact_mod_cast heq
  have hdiv : 1 / (t : ℝ) = 2 / ((r : ℝ) + 1) := by
    rw [heR]
    field_simp
  have hgap : 2 / (r : ℝ) - 2 / ((r : ℝ) + 1) = 2 / ((r : ℝ) * ((r : ℝ) + 1)) := by
    have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hrR.ne', hr1]
    ring
  have hexp : 2 - 1 / (t : ℝ) + η = 2 - 2 / (r : ℝ) + ε := by
    rw [hdiv]
    dsimp [η]
    linarith only [hgap]
  exact ⟨q, H, hq, hreg, by simpa only [hexp] using hO⟩

/-- Quantitative embedding of the odd witness when the rectangle codegrees are bounded. -/
theorem contains_odd_cycle_with_matching {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (R : A → B → Prop) [Nonempty (RelationEdge R)]
    (t L θ D k : ℕ) (ht : 0 < t) (hθ : 0 < θ) (hθL : 4 * t * L ≤ θ)
    (hA : 2 ≤ Fintype.card A)
    (hm₁ : 2 * (Fintype.card B : ℝ) ≤ (Fintype.card (RelationEdge R) : ℝ))
    (hm₂ : 8 * (Fintype.card A : ℝ) ^ 2 * (Fintype.card B : ℝ) ≤
      (Fintype.card (RelationEdge R) : ℝ) ^ 2)
    (hD₁ : ∀ a : A, ((univ : Finset B).filter fun b => R a b).card ≤ D)
    (hD₂ : ∀ b : B, ((univ : Finset A).filter fun a => R a b).card ≤ D)
    (hL₁ : ∀ u : Finset A, u.card = t + 1 → (relationCommon R u).card ≤ L)
    (hL₂ : ∀ u : Finset B, u.card = t + 1 → (relationCommon (Function.swap R) u).card ≤ L)
    (hd : 256 * (t : ℝ) * D * (Fintype.card A : ℝ) ^ 2 * (Fintype.card B : ℝ) ^ 2 ≤
      (Fintype.card (RelationEdge R) : ℝ) ^ 3)
    (hpower : 10 * (θ : ℝ) * (128 * (Fintype.card A : ℝ) ^ 2 * (Fintype.card B : ℝ) ^ 2) ^ t ≤
      (Fintype.card (RelationEdge R) : ℝ) ^ (2 * t + 1))
    (hsmall : ((Fintype.card (RelationEdge R) ^ t : ℕ) : ℝ) *
      (4 * ((k + 2 : ℕ) : ℝ) ^ 3 * ((8 * 2 ^ t * t ^ 2 * L : ℕ) : ℝ) / θ) ^ (k + 2) < 1) :
    cycleWithMatching (((k + 1) + (k + 1)) + 2) t ⊑ relationGraph R := by
  classical
  let m : ℝ := Fintype.card (RelationEdge R)
  let a : ℝ := Fintype.card A
  let b : ℝ := Fintype.card B
  let den := 64 * a ^ 2 * b ^ 2
  let d := m ^ 3 / den
  have ha : 0 < a := by dsimp [a]; exact_mod_cast (show 0 < Fintype.card A by omega)
  have hb : 0 < b := by dsimp [b]; exact_mod_cast Fintype.card_pos (α := B)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos (α := RelationEdge R)
  have hden : 0 < den := by dsimp [den]; positivity
  have hd' : 2 * ((t : ℝ) * (2 * D : ℕ)) ≤ d := by
    apply (le_div_iff₀ hden).mpr
    push_cast
    calc
      _ = 256 * (t : ℝ) * D * a ^ 2 * b ^ 2 := by dsimp [den]; ring
      _ ≤ _ := hd
  have hhalf : d / 2 ≤ d - (t : ℝ) * (2 * D : ℕ) := by linarith only [hd']
  have hdnon : 0 ≤ d / 2 := by dsimp [d]; positivity
  have hd₀ : (t : ℝ) * (2 * D : ℕ) ≤ d := by
    have h : 0 ≤ (t : ℝ) * (2 * D : ℕ) := by positivity
    linarith only [hd', h]
  have hpow' : 10 * (θ : ℝ) * m ^ (t - 1) ≤ (d - (t : ℝ) * (2 * D : ℕ)) ^ t := by
    calc
      _ ≤ (d / 2) ^ t := by
        have hD : d / 2 = m ^ 3 / (128 * a ^ 2 * b ^ 2) := by
          dsimp [d, den]
          ring
        rw [hD, div_pow, ← pow_mul]
        apply (le_div_iff₀ (by positivity)).2
        have hExp : (2 * t + 1) + (t - 1) = 3 * t := by omega
        calc
          _ = (10 * (θ : ℝ) * (128 * a ^ 2 * b ^ 2) ^ t) * m ^ (t - 1) := by ring
          _ ≤ m ^ (2 * t + 1) * m ^ (t - 1) :=
            mul_le_mul_of_nonneg_right hpower (by positivity)
          _ = _ := by rw [← pow_add, hExp]
      _ ≤ _ := pow_le_pow_left₀ hdnon hhalf _
  obtain ⟨U, hU, hne, hc⟩ := rectangle_core_of_density R t L θ D ht hθ hθL hA
    hm₁ hm₂ hD₁ hD₂ hL₁ hL₂ hd₀ hpow'
  exact cycleWithMatching_of_rectangle_core R t _ θ _ ht ⟨k + 2, by omega⟩
    (sparseConflictCycles_of_ratio _ _ _ k hθ hsmall) U hU hne
    (fun x hx => (hc x hx).1) (fun x hx => (hc x hx).2)

/-- Partition a finite type into bounded fibers using an embedding into a rectangular grid. -/
theorem exists_small_fibers {V : Type} [Fintype V] (j b : ℕ)
    (h : Fintype.card V ≤ j * b) :
    ∃ f : V → Fin j, ∀ i, (univ.filter fun v => f v = i).card ≤ b := by
  classical
  let e (v : V) : Fin j × Fin b :=
    finProdFinEquiv.symm (Fin.castLEEmb h (Fintype.equivFin V v))
  have he : Function.Injective e :=
    finProdFinEquiv.symm.injective.comp ((Fin.castLEEmb h).injective.comp (Fintype.equivFin V).injective)
  refine ⟨fun v => (e v).1, fun i => ?_⟩
  have hb := card_le_card_of_injOn (fun v => (e v).2)
    (s := univ.filter fun v : V => (e v).1 = i) (t := (univ : Finset (Fin b)))
    (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
  · simpa only [card_univ, Fintype.card_fin] using hb
  intro u hu v hv huv
  have h₁ := (mem_filter.mp (mem_coe.mp hu)).2
  have h₂ := (mem_filter.mp (mem_coe.mp hv)).2
  exact he (Prod.ext (h₁.trans h₂.symm) huv)

private noncomputable def edgesInside {V : Type} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => e.toFinset ⊆ s

private theorem card_edgesInside {V : Type} [Fintype V] (G : SimpleGraph V) (s : Finset V) :
    (edgesInside G s).card = (G.induce (s : Set V)).edgeFinset.card := by
  classical
  convert! G.card_filter_edgeFinset_toFinset_subset s

private theorem mem_edgesInside {V : Type} [Fintype V] (G : SimpleGraph V)
    (s : Finset V) (e : Sym2 V) :
    e ∈ edgesInside G s ↔ e ∈ G.edgeFinset ∧ e.toFinset ⊆ s := by
  classical
  unfold edgesInside
  exact mem_filter

/-- In a graph maximizing normalized induced density, high degrees account for few edges. -/
theorem trim_high_degrees {V : Type} [Fintype V] (G : SimpleGraph V) (a : ℝ) (ha : 0 ≤ a)
    (j : ℕ) (hj : 0 < j) (hmj : j ≤ Fintype.card V) (he : 0 < G.edgeFinset.card)
    (hJ : (j : ℝ) * (3 / (j : ℝ)) ^ a ≤ 1 / 4)
    (hmax : ∀ s : Finset V, ((G.induce (s : Set V)).edgeFinset.card : ℝ) ≤
      (G.edgeFinset.card : ℝ) * ((s.card : ℝ) / Fintype.card V) ^ a) :
    ∃ s : Finset V, 3 * (G.edgeFinset.card : ℝ) / 4 ≤ ((G.induce (s : Set V)).edgeFinset.card : ℝ) ∧
      ∀ v : (s : Set V), ((G.induce (s : Set V)).degree v : ℝ) ≤
        2 * (j : ℝ) * G.edgeFinset.card / Fintype.card V := by
  classical
  let m := Fintype.card V
  let mR : ℝ := m
  let J : ℝ := j
  let E : ℝ := G.edgeFinset.card
  let cap := 2 * J * E / mR
  have hm : 0 < m := lt_of_lt_of_le hj hmj
  have hmR : 0 < mR := by dsimp [mR]; exact_mod_cast hm
  have hJR : 0 < J := by dsimp [J]; exact_mod_cast hj
  have hE : 0 < E := by dsimp [E]; exact_mod_cast he
  have hcap : 0 ≤ cap := by dsimp [cap]; positivity
  let H := univ.filter fun v => cap < (G.degree v : ℝ)
  let S := univ.filter fun v => ¬ cap < (G.degree v : ℝ)
  have hHsum : (H.card : ℝ) * cap ≤ 2 * E := by
    calc
      _ = ∑ _v ∈ H, cap := by simp
      _ ≤ ∑ v ∈ H, (G.degree v : ℝ) := by
        apply sum_le_sum
        intro v hv
        exact (mem_filter.mp hv).2.le
      _ ≤ ∑ v : V, (G.degree v : ℝ) := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by
        intro v _ _
        positivity)
      _ = _ := by
        dsimp [E]
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hHC : (H.card : ℝ) ≤ mR / J := by
    rw [le_div_iff₀ hJR]
    change (H.card : ℝ) * (2 * J * E / mR) ≤ 2 * E at hHsum
    have hmul : (H.card : ℝ) * J * (2 * E) ≤ mR * (2 * E) := by
      rw [← mul_div_assoc, div_le_iff₀ hmR] at hHsum
      nlinarith only [hHsum]
    exact le_of_mul_le_mul_right hmul (by positivity)
  let b := m / j + 1
  have hgrid : m ≤ j * b := by
    have hsplit := Nat.mod_add_div m j
    have hmod := Nat.mod_lt m hj
    dsimp [b]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  obtain ⟨f, hf⟩ := exists_small_fibers (V := V) j b hgrid
  let B (i : Fin j) := univ.filter fun v => f v = i
  let U (i : Fin j) := H ∪ B i
  have hb : (b : ℝ) ≤ 2 * mR / J := by
    have hd : ((m / j : ℕ) : ℝ) * J ≤ mR := by
      dsimp [J, mR]
      exact_mod_cast Nat.div_mul_le_self m j
    have hJm : J ≤ mR := by dsimp [J, mR, m]; exact_mod_cast hmj
    rw [le_div_iff₀ hJR]
    dsimp only [b]
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith only [hd, hJm]
  have hU (i : Fin j) : ((U i).card : ℝ) / mR ≤ 3 / J := by
    have hsum : ((U i).card : ℝ) ≤ (H.card : ℝ) + (B i).card := by
      exact_mod_cast card_union_le H (B i)
    have hB : ((B i).card : ℝ) ≤ b := by exact_mod_cast hf i
    apply (div_le_iff₀ hmR).mpr
    have heq : 3 / J * mR = mR / J + 2 * mR / J := by ring
    rw [heq]
    linarith only [hsum, hB, hb, hHC]
  let bad := G.edgeFinset.filter fun e => ¬ e.toFinset ⊆ S
  have cover : bad ⊆ (univ : Finset (Fin j)).biUnion (fun i => edgesInside G (U i)) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      obtain ⟨hg, hbad⟩ := mem_filter.mp he
      have hpair : u ∉ S ∨ v ∉ S := by
        have hh : ¬(u ∈ S ∧ v ∈ S) := by
          rw [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff] at hbad
          exact hbad
        exact not_and_or.mp hh
      rcases hpair with hu | hv
      · refine mem_biUnion.mpr ⟨f v, mem_univ _, (mem_edgesInside _ _ _).mpr ⟨hg, ?_⟩⟩
        rw [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff]
        have uH : u ∈ H := by simpa [H, S] using hu
        exact ⟨mem_union_left _ uH, mem_union_right _ (mem_filter.mpr ⟨mem_univ _, rfl⟩)⟩
      · refine mem_biUnion.mpr ⟨f u, mem_univ _, (mem_edgesInside _ _ _).mpr ⟨hg, ?_⟩⟩
        rw [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff]
        have vH : v ∈ H := by simpa [H, S] using hv
        exact ⟨mem_union_right _ (mem_filter.mpr ⟨mem_univ _, rfl⟩), mem_union_left _ vH⟩
  have hbad : (bad.card : ℝ) ≤ E / 4 := by
    have hnat := (card_le_card cover).trans card_biUnion_le
    calc
      _ ≤ ∑ i : Fin j, ((edgesInside G (U i)).card : ℝ) := by exact_mod_cast hnat
      _ ≤ ∑ _i : Fin j, E * (3 / J) ^ a := by
        apply sum_le_sum
        intro i _
        rw [card_edgesInside]
        exact (hmax (U i)).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (hU i) ha) hE.le)
      _ = E * (J * (3 / J) ^ a) := by simp [J, mul_left_comm]
      _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hJ hE.le
  refine ⟨S, ?_, ?_⟩
  · have hsum : ((edgesInside G S).card : ℝ) + bad.card = E := by
      dsimp [E]
      exact_mod_cast (show (edgesInside G S).card + bad.card = G.edgeFinset.card from
        card_filter_add_card_filter_not _)
    rw [← card_edgesInside]
    linarith only [hsum, hbad]
  · intro v
    have hv := (mem_filter.mp (mem_coe.mp v.property)).2
    have hdeg : ((G.induce (S : Set V)).degree v : ℝ) ≤ G.degree v.val := by
      exact_mod_cast (Copy.induce G (S : Set V)).degree_le v
    exact hdeg.trans (not_lt.mp hv)

/-- Iteratively removing low-degree vertices loses at most the degree threshold times the order. -/
theorem min_degree_core_preserves_edges (d : ℝ) (hd : 0 ≤ d) :
    ∀ (m : ℕ) (V : Type) [Fintype V], Fintype.card V = m →
      ∀ (G : SimpleGraph V), d * m < (G.edgeFinset.card : ℝ) →
        ∃ (W : Type) (iW : Fintype W) (F : SimpleGraph W),
          0 < @Fintype.card W iW ∧ @Fintype.card W iW ≤ m ∧ F ⊑ G ∧
          (G.edgeFinset.card : ℝ) - d * m ≤ (F.edgeFinset.card : ℝ) ∧
          ∀ v : W, d ≤ (F.degree v : ℝ) := by
  classical
  intro m
  induction m with
  | zero =>
    intro V _ hV G hG
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    have hbot : G = ⊥ := Subsingleton.elim _ _
    simp [hbot] at hG
  | succ m ih =>
    intro V _ hV G hG
    by_cases h : ∀ v, d ≤ (G.degree v : ℝ)
    · refine ⟨V, inferInstance, G, by omega, hV.le, IsContained.rfl, ?_, h⟩
      exact sub_le_self _ (by positivity)
    · push Not at h
      obtain ⟨v, hv⟩ := h
      let T : Set V := {v}ᶜ
      let B := G.induce T
      have hT : Fintype.card T = m := by
        change Fintype.card (({v} : Set V)ᶜ : Set V) = m
        rw [Fintype.card_compl_set, hV, @Fintype.card_unique ({v} : Set V), Nat.add_sub_cancel]
      have hsplit : B.edgeFinset.card + G.degree v = G.edgeFinset.card := by
        simp only [B, T, card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]
        exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)
      have hsplitR : (B.edgeFinset.card : ℝ) + G.degree v = (G.edgeFinset.card : ℝ) := by
        exact_mod_cast hsplit
      have hB : d * m < (B.edgeFinset.card : ℝ) := by
        rw [Nat.cast_succ, mul_add, mul_one] at hG
        linarith only [hG, hsplitR, hv]
      obtain ⟨W, iW, F, hn, hle, hc, hE, hD⟩ := ih T hT B hB
      refine ⟨W, iW, F, hn, hle.trans (Nat.le_succ m), hc.trans ⟨Copy.induce G T⟩, ?_, hD⟩
      calc
        _ ≤ (B.edgeFinset.card : ℝ) - d * m := by
          rw [Nat.cast_succ, mul_add, mul_one]
          linarith only [hsplitR, hv]
        _ ≤ _ := by convert! hE

/-- A dense graph admits an almost-regular copy retaining at least half its normalized density. -/
theorem exists_almost_regular_subcopy {V : Type} [Fintype V] (G : SimpleGraph V)
    (a : ℝ) (ha : 0 ≤ a) (j : ℕ) (hj : 0 < j)
    (hJ : (j : ℝ) * (3 / (j : ℝ)) ^ a ≤ 1 / 4)
    (hdense : (j : ℝ) ^ 2 <
      (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ a) :
    ∃ (W : Type) (iW : Fintype W) (F : SimpleGraph W),
      0 < @Fintype.card W iW ∧ F ⊑ G ∧
      (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ a / 2 ≤
        (F.edgeFinset.card : ℝ) / (@Fintype.card W iW : ℝ) ^ a ∧
      ∃ d : ℝ, 0 < d ∧ ∀ v : W, d ≤ (F.degree v : ℝ) ∧ (F.degree v : ℝ) ≤ 8 * (j : ℝ) * d := by
  classical
  let score (s : Finset V) := ((edgesInside G s).card : ℝ) / (s.card : ℝ) ^ a
  obtain ⟨T, -, hmax⟩ := exists_max_image (univ : Finset V).powerset score
    ⟨∅, mem_powerset.mpr (empty_subset _)⟩
  have hmax' (s : Finset V) : score s ≤ score T := hmax s (mem_powerset.mpr (subset_univ _))
  have hscore : (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ a ≤ score T := by
    simpa [score, edgesInside, filter_eq_self.mpr] using hmax' univ
  have hscore' : (j : ℝ) ^ 2 < score T := hdense.trans_le hscore
  let B := G.induce (T : Set V)
  let M : ℕ := Fintype.card (T : Set V)
  let E : ℝ := B.edgeFinset.card
  have hM : M = T.card := Fintype.card_coe T
  have hBpos : 0 < B.edgeFinset.card := by
    have hp : 0 < score T := (sq_nonneg _).trans_lt hscore'
    have hne : (edgesInside G T).card ≠ 0 := by
      intro hz
      simp [score, hz] at hp
    rw [← card_edgesInside]
    exact Nat.pos_of_ne_zero hne
  have hE : 0 < E := by dsimp [E]; exact_mod_cast hBpos
  have hEbound : B.edgeFinset.card ≤ M ^ 2 :=
    (B.card_edgeFinset_le_card_choose_two).trans (Nat.choose_le_pow _ _)
  have hMpos : 0 < M := by
    by_contra! h
    have hz : M = 0 := Nat.eq_zero_of_le_zero h
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hEbound
    exact (not_le_of_gt hBpos) hEbound
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M from hMpos)
  have hmR : (0 : ℝ) < M := zero_lt_one.trans_le hM1
  have hscoreB : score T = E / (M : ℝ) ^ a := by
    dsimp [score, E]
    rw [card_edgesInside, hM]
  have hMJ : j ≤ M := by
    by_contra! h
    have hR : (M : ℝ) ≤ j := by exact_mod_cast h.le
    have haM := Real.one_le_rpow hM1 ha
    have hE' : E ≤ (M : ℝ) ^ 2 := by dsimp [E]; exact_mod_cast hEbound
    have hle : score T ≤ (j : ℝ) ^ 2 := by
      rw [hscoreB]
      calc
        _ ≤ E / 1 := div_le_div_of_nonneg_left hE.le (by norm_num) haM
        _ ≤ _ := by rw [div_one]; exact hE'.trans (pow_le_pow_left₀ hmR.le hR _)
    exact (not_le_of_gt hscore') hle
  have hnorm (s : Finset (T : Set V)) :
      (((B.induce (s : Set (T : Set V))).edgeFinset.card : ℝ)) ≤
        E * ((s.card : ℝ) / M) ^ a := by
    let e : (T : Set V) ↪ V := Function.Embedding.subtype _
    let U := s.map e
    let iso : B.induce (s : Set (T : Set V)) ≃g G.induce (U : Set V) :=
      { toEquiv := Finset.equivMap e s
        map_rel_iff' := by intro u v; rfl }
    have hEdge : (B.induce (s : Set (T : Set V))).edgeFinset.card = (edgesInside G U).card := by
      rw [card_edgesInside]
      exact iso.card_edgeFinset_eq
    have hcard : U.card = s.card := card_map _
    by_cases hs : s.Nonempty
    · have hsR : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
      have h := hmax' U
      change ((edgesInside G U).card : ℝ) / (U.card : ℝ) ^ a ≤ score T at h
      rw [hcard, hscoreB] at h
      rw [hEdge]
      calc
        _ ≤ (E / (M : ℝ) ^ a) * (s.card : ℝ) ^ a :=
          (div_le_iff₀ (Real.rpow_pos_of_pos hsR _)).mp h
        _ = _ := by rw [Real.div_rpow hsR.le hmR.le]; ring
    · have hs' := not_nonempty_iff_eq_empty.mp hs
      have hzero : (B.induce (s : Set (T : Set V))).edgeFinset.card = 0 := by
        rw [hEdge]
        simp [U, hs', edgesInside, Finset.subset_empty]
      rw [hzero, Nat.cast_zero]
      positivity
  obtain ⟨S, hSedges, hSdeg⟩ := trim_high_degrees B a ha j hj hMJ hBpos hJ hnorm
  let C := B.induce (S : Set (T : Set V))
  let d := E / (4 * (M : ℝ))
  have hd : 0 < d := by dsimp [d]; positivity
  have hcardS : Fintype.card (S : Set (T : Set V)) ≤ M :=
    Fintype.card_le_of_injective _ Subtype.val_injective
  have hsplit : d * (M : ℝ) = E / 4 := by
    dsimp [d]
    field_simp
  have hThin : d * (Fintype.card (S : Set (T : Set V)) : ℝ) ≤ E / 4 := by
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcardS) hd.le).trans_eq hsplit
  have hC : d * (Fintype.card (S : Set (T : Set V)) : ℝ) < C.edgeFinset.card := by
    change 3 * E / 4 ≤ (C.edgeFinset.card : ℝ) at hSedges
    linarith only [hE, hThin, hSedges]
  obtain ⟨W, iW, F, hWpos, hWcard, hFc, hFedges, hFdeg⟩ := min_degree_core_preserves_edges d hd.le
    _ (S : Set (T : Set V)) rfl C hC
  let : Fintype W := iW
  have hFG : F ⊑ G := hFc.trans (show C ⊑ B from ⟨Copy.induce B _⟩) |>.trans ⟨Copy.induce G _⟩
  have hFbound : E / 2 ≤ (F.edgeFinset.card : ℝ) := by
    have he' : (C.edgeFinset.card : ℝ) - d * Fintype.card (S : Set (T : Set V)) ≤ F.edgeFinset.card := by
      convert! hFedges
    change 3 * E / 4 ≤ (C.edgeFinset.card : ℝ) at hSedges
    linarith only [hSedges, hThin, he']
  have hWm : (Fintype.card W : ℝ) ≤ M := by exact_mod_cast hWcard.trans hcardS
  have hW0 : (0 : ℝ) < Fintype.card W := by exact_mod_cast hWpos
  refine ⟨W, iW, F, hWpos, hFG, ?_, d, hd, fun v => ⟨hFdeg v, ?_⟩⟩
  · calc
      _ ≤ score T / 2 := div_le_div_of_nonneg_right hscore (by norm_num)
      _ = (E / 2) / (M : ℝ) ^ a := by rw [hscoreB]; ring
      _ ≤ (E / 2) / (Fintype.card W : ℝ) ^ a :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hW0 _)
          (Real.rpow_le_rpow hW0.le hWm ha)
      _ ≤ _ := div_le_div_of_nonneg_right hFbound (by positivity)
  obtain ⟨c⟩ := hFc
  have hD : (F.degree v : ℝ) ≤ C.degree (c v) := by exact_mod_cast c.degree_le v
  apply hD.trans
  calc
    _ ≤ 2 * (j : ℝ) * E / M := hSdeg (c v)
    _ = _ := by dsimp [d]; ring

private theorem exists_bipartite_half_edges {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ B : SimpleGraph V, B ≤ G ∧ B.IsBipartite ∧ G.edgeFinset.card ≤ 2 * B.edgeFinset.card := by
  classical
  obtain ⟨B, hBG, hb, hd⟩ := exists_bipartite_half_degrees G
  refine ⟨B, hBG, hb, ?_⟩
  have hs := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hd v)
  rw [← mul_sum, G.sum_degrees_eq_twice_card_edges, B.sum_degrees_eq_twice_card_edges] at hs
  omega

/-- Embedding in sufficiently large almost-regular bipartite graphs suffices up to an exponent loss. -/
theorem extremal_of_almost_regular_bipartite_test {W : Type} (H : SimpleGraph W)
    (a η : ℝ) (ha : 1 < a) (hη : 0 < η)
    (force : ∀ K : ℝ, ∃ N : ℕ, ∀ (V : Type) [Fintype V] [Nonempty V] (F : SimpleGraph V),
      N ≤ Fintype.card V → F.IsBipartite →
      (∃ d : ℝ, 0 < d ∧ ∀ v : V, d ≤ (F.degree v : ℝ) ∧ (F.degree v : ℝ) ≤ K * d) →
      (Fintype.card V : ℝ) ^ a ≤ F.edgeFinset.card → H ⊑ F) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a + η)) := by
  classical
  have ha₀ : 0 ≤ a := by linarith
  have hlim : Tendsto (fun j : ℕ => (j : ℝ) ^ (a - 1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
  obtain ⟨j, hj, hjpow⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (hlim.eventually_gt_atTop (4 * (3 : ℝ) ^ a))).exists
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j from hj)
  have hJ : (j : ℝ) * (3 / (j : ℝ)) ^ a ≤ 1 / 4 := by
    have hform : (j : ℝ) * (3 / (j : ℝ)) ^ a = (3 : ℝ) ^ a / (j : ℝ) ^ (a - 1) := by
      rw [Real.div_rpow (by positivity) hjR.le, Real.rpow_sub hjR, Real.rpow_one]
      field_simp [hjR.ne', (Real.rpow_pos_of_pos hjR a).ne']
    rw [hform, div_le_iff₀ (Real.rpow_pos_of_pos hjR _)]
    change 4 * (3 : ℝ) ^ a < (j : ℝ) ^ (a - 1) at hjpow
    linarith only [hjpow]
  obtain ⟨N, hN⟩ := force (8 * (j : ℝ))
  let Bnd := max (2 * (j : ℝ) ^ 2) (4 * (max ((N : ℝ) ^ 2) 1))
  have hlimη : Tendsto (fun n : ℕ => (n : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlimη.eventually_gt_atTop Bnd] with n hn hbig
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  nth_rw 1 [← Fintype.card_fin n]
  apply (extremalNumber_le_iff_of_nonneg (V := Fin n) H (by positivity)).2
  intro G _ hf
  by_contra! hG
  obtain ⟨B, hBG, hb, hhalf⟩ := exists_bipartite_half_edges G
  have hhalfR : (G.edgeFinset.card : ℝ) ≤ 2 * B.edgeFinset.card := by
    exact_mod_cast (show G.edgeFinset.card ≤ 2 * B.edgeFinset.card from by convert! hhalf)
  have hscore : (n : ℝ) ^ η / 2 < (B.edgeFinset.card : ℝ) / (Fintype.card (Fin n) : ℝ) ^ a := by
    rw [Fintype.card_fin, lt_div_iff₀ (Real.rpow_pos_of_pos hnR _)]
    rw [Real.rpow_add hnR] at hG
    nlinarith only [hG, hhalfR]
  have hDense : (j : ℝ) ^ 2 < (B.edgeFinset.card : ℝ) / (Fintype.card (Fin n) : ℝ) ^ a := by
    apply lt_trans _ hscore
    have h := (le_max_left (2 * (j : ℝ) ^ 2) (4 * (max ((N : ℝ) ^ 2) 1))).trans_lt hbig
    linarith only [h]
  obtain ⟨V, iV, F, hVpos, hFB, hFscore, hReg⟩ :=
    exists_almost_regular_subcopy B a ha₀ j hj hJ hDense
  let : Fintype V := iV
  have : Nonempty V := Fintype.card_pos_iff.mp hVpos
  have hvR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast (show 1 ≤ Fintype.card V from hVpos)
  have hFlarge : max ((N : ℝ) ^ 2) 1 <
      (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ a := by
    have hb := (le_max_right (2 * (j : ℝ) ^ 2) (4 * (max ((N : ℝ) ^ 2) 1))).trans_lt hbig
    linarith only [hb, hscore, hFscore]
  have hFpos : 0 < (Fintype.card V : ℝ) ^ a :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hvR) _
  have hFden := Real.one_le_rpow hvR ha₀
  have hForder : N ≤ Fintype.card V := by
    by_contra! ht
    have ht' : (Fintype.card V : ℝ) ≤ N := by exact_mod_cast ht.le
    have hE : (F.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
      exact_mod_cast F.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)
    have hEst := (div_le_self (by positivity : 0 ≤ (F.edgeFinset.card : ℝ)) hFden).trans
      (hE.trans (pow_le_pow_left₀ (by positivity) ht' _))
    exact (not_le_of_gt ((le_max_left _ _).trans_lt hFlarge)) hEst
  have hFedges : (Fintype.card V : ℝ) ^ a ≤ F.edgeFinset.card := by
    have h := (le_max_right ((N : ℝ) ^ 2) 1).trans_lt hFlarge
    exact le_of_lt (by simpa only [one_mul] using (lt_div_iff₀ hFpos).mp h)
  obtain ⟨f⟩ := hFB
  have hFbip : F.IsBipartite := Colorable.of_hom f.toHom hb
  exact hf ((hN V F hForder hFbip hReg hFedges).trans ((show F ⊑ B from ⟨f⟩).trans (.of_le hBG)))

/-- The odd-degree witness occurs at the conjectured density in almost-regular relations
with polynomially bounded higher codegrees. -/
theorem uniform_bounded_codegree_odd_witness_of_exponent (t : ℕ) (ht : 2 ≤ t)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hδgap : δ < (((2 * t + 1 : ℕ) : ℝ)) * ε) :
    let r : ℝ := (2 * t + 1 : ℕ)
    let a := 2 - 2 / r + ε
    ∃ k : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ᶠ N : ℕ in atTop,
      ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
        Fintype.card A + Fintype.card B = N →
        (N : ℝ) ^ a ≤ (Fintype.card (RelationEdge R) : ℝ) →
        ∀ D L : ℕ, (D : ℝ) ≤ K * (Fintype.card (RelationEdge R) : ℝ) / N →
        (L : ℝ) ≤ (N : ℝ) ^ δ →
        (∀ x : A, ((univ : Finset B).filter fun y => R x y).card ≤ D) →
        (∀ y : B, ((univ : Finset A).filter fun x => R x y).card ≤ D) →
        (∀ u : Finset A, u.card = t + 1 → (relationCommon R u).card ≤ L) →
        (∀ u : Finset B, u.card = t + 1 → (relationCommon (Function.swap R) u).card ≤ L) →
        cycleWithMatching (((k + 1) + (k + 1)) + 2) t ⊑ relationGraph R := by
  classical
  intro r a
  have hr5 : (5 : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast (show 5 ≤ 2 * t + 1 by omega)
  have hr : 0 < r := by linarith
  let ρ := (r * ε - δ) / 2
  let σ := δ + ρ
  have hρ : 0 < ρ := half_pos (sub_pos.mpr hδgap)
  have hσ : 0 < σ := add_pos_of_nonneg_of_pos hδ hρ
  have ha : 0 < 2 * a - 3 := by
    have hd : 2 / r ≤ (2 : ℝ) / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr5
    dsimp [a]
    linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((2 * (t : ℝ)) / ρ)
  let j := k + 2
  let J : ℝ := j
  let η := ρ * J - 2 * t
  have hη : 0 < η := by
    have h := (div_lt_iff₀ hρ).mp hk
    dsimp [η, J, j]
    rw [Nat.cast_add]
    nlinarith only [h, hρ]
  let C := (8 : ℝ) * J ^ 3 * (8 * 2 ^ t * (t : ℝ) ^ 2)
  have hlim (s : ℝ) (hs : 0 < s) : Tendsto (fun n : ℕ => (n : ℝ) ^ s) atTop atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  refine ⟨k, ?_⟩
  intro K hK
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (hlim (2 * a - 3) ha).eventually_ge_atTop (max 8 (256 * (t : ℝ) * K)),
    (hlim ρ hρ).eventually_ge_atTop (max (8 * (t : ℝ)) 2),
    (hlim ρ hρ).eventually_ge_atTop (10 * (128 : ℝ) ^ t),
    (hlim η hη).eventually_gt_atTop (C ^ j)] with N hN hscale hρN hlarge hcycle
  intro A B _ _ R hAB hR D L hD hL hD₁ hD₂ hL₁ hL₂
  let n : ℝ := N
  let m : ℝ := Fintype.card (RelationEdge R)
  let A₀ : ℝ := Fintype.card A
  let B₀ : ℝ := Fintype.card B
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast hN
  have hn : 0 < n := zero_lt_one.trans_le hn1
  have hApos : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hBpos : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have hparts : A₀ + B₀ = n := by dsimp [A₀, B₀, n]; exact_mod_cast hAB
  have hAn : A₀ ≤ n := by linarith only [hparts, hBpos]
  have hBn : B₀ ≤ n := by linarith only [hparts, hApos]
  have hm : 0 < m := (Real.rpow_pos_of_pos hn _).trans_le hR
  have hE : Nonempty (RelationEdge R) := by
    apply Fintype.card_pos_iff.mp
    dsimp [m] at hm
    exact_mod_cast hm
  have : Nonempty B := ⟨(Classical.choice hE).val.2⟩
  have hmAB : m ≤ A₀ * B₀ := by
    have h := Fintype.card_le_of_injective (fun e : RelationEdge R => e.val) Subtype.val_injective
    rw [Fintype.card_prod] at h
    dsimp [m, A₀, B₀]
    exact_mod_cast h
  have hpartsProd : A₀ * B₀ ≤ n ^ 2 := by
    simpa only [pow_two] using mul_le_mul hAn hBn hBpos hn.le
  have hSq : n ^ (2 * a - 3) * n ^ (3 : ℕ) ≤ m ^ 2 := by
    have he : n ^ (2 * a - 3) * n ^ (3 : ℕ) = (n ^ a) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast n (3 : ℕ), ← Real.rpow_add hn,
        ← Real.rpow_natCast (n ^ a) (2 : ℕ), ← Real.rpow_mul hn.le]
      congr 1
      norm_num
      ring
    rw [he]
    exact pow_le_pow_left₀ (by positivity) hR _
  have hSq₁ : 8 * n ^ (3 : ℕ) ≤ m ^ 2 :=
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hscale) (by positivity)).trans hSq
  have hSq₂ : (256 * (t : ℝ) * K) * n ^ (3 : ℕ) ≤ m ^ 2 :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hscale) (by positivity)).trans hSq
  have htwoN : 2 * n ≤ m := by
    by_contra! h
    have h' := pow_lt_pow_left₀ h (by positivity : 0 ≤ m) (by decide : (2 : ℕ) ≠ 0)
    nlinarith only [h', hSq₁, show 4 * n ^ 2 ≤ 8 * n ^ 3 by nlinarith [mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hn1)]]
  have hA2 : 2 ≤ Fintype.card A := by
    by_contra! h
    have h' : A₀ ≤ 1 := by dsimp [A₀]; exact_mod_cast (show Fintype.card A ≤ 1 by omega)
    have hn' := hmAB.trans ((mul_le_mul_of_nonneg_right h' hBpos).trans (by simpa using hBn))
    linarith only [hn', htwoN, hn]
  have hD' : (D : ℝ) * n ≤ K * m := (le_div_iff₀ hn).mp hD
  have hDscale : 256 * (t : ℝ) * D * A₀ ^ 2 * B₀ ^ 2 ≤ m ^ 3 := by
    have hpartsPow : A₀ ^ 2 * B₀ ^ 2 ≤ n ^ (4 : ℕ) := by
      rw [← mul_pow, show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hpartsProd _
    calc
      _ ≤ (256 * (t : ℝ) * D) * n ^ (4 : ℕ) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpartsPow (by positivity : 0 ≤ 256 * (t : ℝ) * D)
      _ = (256 * (t : ℝ)) * ((D : ℝ) * n) * n ^ (3 : ℕ) := by ring
      _ ≤ (256 * (t : ℝ) * K * n ^ (3 : ℕ)) * m := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD' (by positivity : 0 ≤ 256 * (t : ℝ))) (by positivity : 0 ≤ n ^ (3 : ℕ))
        simpa only [mul_assoc, mul_comm m] using h
      _ ≤ m ^ 2 * m := mul_le_mul_of_nonneg_right hSq₂ hm.le
      _ = _ := by ring
  let θ := ⌊n ^ σ⌋₊
  have hnδ : n ^ δ * n ^ ρ = n ^ σ := (Real.rpow_add hn _ _).symm
  have hlargeρ : (8 * (t : ℝ)) ≤ n ^ ρ := (le_max_left _ _).trans hρN
  have hρ₂ : (2 : ℝ) ≤ n ^ ρ := (le_max_right _ _).trans hρN
  have hθup : (θ : ℝ) ≤ n ^ σ := Nat.floor_le (by positivity)
  have hθlow : n ^ σ / 2 ≤ θ := by
    have hδ₁ := Real.one_le_rpow hn1 hδ
    have hσ₂ : 2 ≤ n ^ σ := by
      rw [← hnδ]
      calc
        _ ≤ n ^ ρ := hρ₂
        _ = 1 * n ^ ρ := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hδ₁ (by positivity)
    have hf := Nat.lt_floor_add_one (n ^ σ)
    change n ^ σ < (θ : ℝ) + 1 at hf
    linarith only [hf, hσ₂]
  have hθ : 0 < θ := by
    have h := (show 0 < n ^ σ / 2 by positivity).trans_le hθlow
    exact_mod_cast h
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hθL : 4 * t * L ≤ θ := by
    have h : 4 * (t : ℝ) * L ≤ (θ : ℝ) := by
      calc
        _ ≤ 4 * (t : ℝ) * n ^ δ := mul_le_mul_of_nonneg_left hL (by positivity)
        _ ≤ n ^ σ / 2 := by
          rw [← hnδ]
          nlinarith only [mul_le_mul_of_nonneg_left hlargeρ (by positivity : 0 ≤ n ^ δ)]
        _ ≤ _ := hθlow
    exact_mod_cast h
  have hθscale : 10 * (θ : ℝ) * (128 * A₀ ^ 2 * B₀ ^ 2) ^ t ≤ m ^ (2 * t + 1) := by
    have hratio : (128 * A₀ ^ 2 * B₀ ^ 2) ^ t ≤ (128 : ℝ) ^ t * n ^ (4 * t : ℕ) := by
      have hpart : A₀ ^ 2 * B₀ ^ 2 ≤ n ^ (4 : ℕ) := by
        rw [← mul_pow, show (4 : ℕ) = 2 * 2 by decide, pow_mul]
        exact pow_le_pow_left₀ (by positivity) hpartsProd _
      rw [show (128 : ℝ) * A₀ ^ 2 * B₀ ^ 2 = 128 * (A₀ ^ 2 * B₀ ^ 2) by ring,
        mul_pow, pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpart _) (by positivity)
    have hl : a * (2 * t + 1 : ℕ) = ((4 * t : ℕ) : ℝ) + (ρ + σ) := by
      change a * r = _ + _
      dsimp [a, σ, ρ]
      have hrEq : 2 * r - 2 = ((4 * t : ℕ) : ℝ) := by dsimp [r]; push_cast; ring
      rw [← hrEq]
      field_simp [hr.ne']
      ring
    calc
      _ ≤ 10 * (n ^ σ) * ((128 : ℝ) ^ t * n ^ (4 * t : ℕ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hθup (by norm_num)) hratio (by positivity) (by positivity)
      _ = (10 * (128 : ℝ) ^ t) * (n ^ σ * n ^ (4 * t : ℕ)) := by ring
      _ ≤ n ^ ρ * (n ^ σ * n ^ (4 * t : ℕ)) :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = (n ^ a) ^ (2 * t + 1) := by
        rw [← Real.rpow_natCast n (4 * t : ℕ), ← Real.rpow_natCast (n ^ a) (2 * t + 1 : ℕ),
          ← Real.rpow_mul hn.le, hl, ← Real.rpow_add hn, ← Real.rpow_add hn]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hR _
  have hsmall : ((Fintype.card (RelationEdge R) ^ t : ℕ) : ℝ) *
      (4 * ((k + 2 : ℕ) : ℝ) ^ 3 * ((8 * 2 ^ t * t ^ 2 * L : ℕ) : ℝ) / θ) ^ (k + 2) < 1 := by
    have hLratio : (L : ℝ) / θ ≤ 2 / n ^ ρ := by
      rw [div_le_div_iff₀ hθR (Real.rpow_pos_of_pos hn _)]
      have h₁ := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ n ^ ρ)
      have h₂ := hθlow
      rw [← hnδ] at h₂
      linarith only [h₁, h₂]
    have hratio : (4 * J ^ 3 * ((8 * 2 ^ t * t ^ 2 * L : ℕ) : ℝ)) / θ ≤ C / n ^ ρ := by
      push_cast
      calc
        _ = (4 * J ^ 3 * (8 * 2 ^ t * (t : ℝ) ^ 2)) * ((L : ℝ) / θ) := by ring
        _ ≤ (4 * J ^ 3 * (8 * 2 ^ t * (t : ℝ) ^ 2)) * (2 / n ^ ρ) :=
          mul_le_mul_of_nonneg_left hLratio (by positivity)
        _ = _ := by dsimp [C]; ring
    have hp : m ^ t ≤ n ^ (2 * t : ℕ) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ hm.le (hmAB.trans hpartsProd) _
    have hf : n ^ (2 * t : ℕ) * (C / n ^ ρ) ^ j < 1 := by
      have hpow : (n ^ ρ) ^ j = n ^ (ρ * J) := by rw [Real.rpow_mul hn.le, Real.rpow_natCast]
      have he : n ^ (2 * t : ℕ) / (n ^ ρ) ^ j = (n ^ η)⁻¹ := by
        rw [hpow, ← Real.rpow_natCast n (2 * t : ℕ), ← Real.rpow_sub hn, ← Real.rpow_neg hn.le]
        congr 1
        dsimp [η]
        push_cast
        ring
      calc
        _ = C ^ j * (n ^ (2 * t : ℕ) / (n ^ ρ) ^ j) := by rw [div_pow]; ring
        _ = C ^ j / n ^ η := by rw [he, div_eq_mul_inv]
        _ < _ := (div_lt_one (Real.rpow_pos_of_pos hn _)).2 hcycle
    rw [Nat.cast_pow]
    exact (mul_le_mul hp (pow_le_pow_left₀ (by positivity) hratio j) (by positivity) (by positivity)).trans_lt hf
  apply contains_odd_cycle_with_matching R t L θ D k (by omega) hθ hθL hA2 _ _ hD₁ hD₂ hL₁ hL₂
    hDscale hθscale hsmall
  · exact (mul_le_mul_of_nonneg_left hBn (by norm_num)).trans htwoN
  · exact (show 8 * A₀ ^ 2 * B₀ ≤ 8 * n ^ (3 : ℕ) by
      have hh := mul_le_mul (pow_le_pow_left₀ hApos hAn 2) hBn hBpos (by positivity)
      simpa only [mul_assoc, ← pow_succ] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 8)).trans hSq₁

theorem uniform_bounded_codegree_odd_witness (t : ℕ) (ht : 2 ≤ t)
    (ε : ℝ) (hε : 0 < ε) :
    let r : ℝ := (2 * t + 1 : ℕ)
    let a := 2 - 2 / r + ε
    let δ := r * ε / 4
    ∃ k : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ᶠ N : ℕ in atTop,
      ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
        Fintype.card A + Fintype.card B = N →
        (N : ℝ) ^ a ≤ (Fintype.card (RelationEdge R) : ℝ) →
        ∀ D L : ℕ, (D : ℝ) ≤ K * (Fintype.card (RelationEdge R) : ℝ) / N →
        (L : ℝ) ≤ (N : ℝ) ^ δ →
        (∀ x : A, ((univ : Finset B).filter fun y => R x y).card ≤ D) →
        (∀ y : B, ((univ : Finset A).filter fun x => R x y).card ≤ D) →
        (∀ u : Finset A, u.card = t + 1 → (relationCommon R u).card ≤ L) →
        (∀ u : Finset B, u.card = t + 1 → (relationCommon (Function.swap R) u).card ≤ L) →
        cycleWithMatching (((k + 1) + (k + 1)) + 2) t ⊑ relationGraph R := by
  intro r a δ
  have hr : 0 < r := by dsimp [r]; positivity
  have hprod : 0 < r * ε := mul_pos hr hε
  exact uniform_bounded_codegree_odd_witness_of_exponent t ht ε δ hε
    (by dsimp [δ]; positivity) (by change r * ε / 4 < r * ε; linarith)

theorem eventually_bounded_codegree_odd_witness (t : ℕ) (ht : 2 ≤ t)
    (ε K : ℝ) (hε : 0 < ε) (hK : 0 ≤ K) :
    let r : ℝ := (2 * t + 1 : ℕ)
    let a := 2 - 2 / r + ε
    let δ := r * ε / 4
    ∃ k : ℕ, ∀ᶠ N : ℕ in atTop,
      ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
        Fintype.card A + Fintype.card B = N →
        (N : ℝ) ^ a ≤ (Fintype.card (RelationEdge R) : ℝ) →
        ∀ D L : ℕ, (D : ℝ) ≤ K * (Fintype.card (RelationEdge R) : ℝ) / N →
        (L : ℝ) ≤ (N : ℝ) ^ δ →
        (∀ x : A, ((univ : Finset B).filter fun y => R x y).card ≤ D) →
        (∀ y : B, ((univ : Finset A).filter fun x => R x y).card ≤ D) →
        (∀ u : Finset A, u.card = t + 1 → (relationCommon R u).card ≤ L) →
        (∀ u : Finset B, u.card = t + 1 → (relationCommon (Function.swap R) u).card ≤ L) →
        cycleWithMatching (((k + 1) + (k + 1)) + 2) t ⊑ relationGraph R := by
  obtain ⟨k, h⟩ := uniform_bounded_codegree_odd_witness t ht ε hε
  exact ⟨k, h K hK⟩

private theorem card_filter_subtype_eq {V : Type} [Fintype V] (s : Finset V)
    (P : V → Prop) (hs : ∀ v, P v → v ∈ s) :
    ((univ : Finset ↥s).filter fun v => P v.val).card = ((univ : Finset V).filter P).card := by
  classical
  let e : ↥s ↪ V := Function.Embedding.subtype _
  rw [← card_map e]
  congr 1
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hv
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hu).2⟩
  · intro hv
    have hp := (mem_filter.mp hv).2
    exact mem_map.mpr ⟨⟨v, hs v hp⟩, mem_filter.mpr ⟨mem_univ _, hp⟩, rfl⟩

private theorem card_relation_row {V : Type} [Fintype V] (G : SimpleGraph V)
    (s t : Finset V) (h : G.IsBipartiteWith s t) (v : s) :
    ((univ : Finset ↥t).filter fun w => G.Adj v.val w.val).card = G.degree v.val := by
  classical
  rw [card_filter_subtype_eq t _ (fun w hw => h.mem_of_mem_adj v.property hw)]
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_neighborFinset]

private theorem card_relation_col {V : Type} [Fintype V] (G : SimpleGraph V)
    (s t : Finset V) (h : G.IsBipartiteWith s t) (w : t) :
    ((univ : Finset ↥s).filter fun v => G.Adj v.val w.val).card = G.degree w.val := by
  classical
  calc
    _ = ((univ : Finset ↥s).filter fun v => G.Adj w.val v.val).card := by
      congr 1
      ext v
      simp only [mem_filter, mem_univ, true_and, G.adj_comm v.val w.val]
    _ = _ := card_relation_row G t s h.symm w

private theorem relationGraph_contained {V : Type} (G : SimpleGraph V)
    (s t : Finset V) (h : G.IsBipartiteWith s t) :
    relationGraph (fun (u : s) (v : t) => G.Adj u.val v.val) ⊑ G := by
  let f : s ⊕ t → V := Sum.elim Subtype.val Subtype.val
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · rintro (u | u) (v | v) hu
    · exact False.elim hu
    · exact hu
    · change G.Adj v.val u.val at hu
      exact hu.symm
    · exact False.elim hu
  · rintro (u | u) (v | v) he
    · exact congrArg Sum.inl (Subtype.ext he)
    · have ht : u.val ∈ (t : Set V) := by
        change u.val = v.val at he
        rw [he]
        exact v.property
      exact False.elim (Set.disjoint_left.mp h.disjoint u.property ht)
    · have hs : u.val ∈ (s : Set V) := by
        change u.val = v.val at he
        rw [he]
        exact v.property
      exact False.elim (Set.disjoint_left.mp h.disjoint hs u.property)
    · exact congrArg Sum.inr (Subtype.ext he)

private theorem common_subtype_le {V : Type} [Fintype V] (G : SimpleGraph V)
    (s t : Finset V) (u : Finset ↥s) :
    (relationCommon (fun (a : s) (b : t) => G.Adj a.val b.val) u).card ≤
      (relationCommon G.Adj (u.map (Function.Embedding.subtype _))).card := by
  classical
  apply card_le_card_of_injOn (fun v : ↥t => v.val) _ (fun _ _ _ _ h => Subtype.ext h)
  intro v hv
  apply mem_coe.mpr
  apply mem_relationCommon.mpr
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  exact (mem_relationCommon.mp (mem_coe.mp hv)) y hy

set_option maxHeartbeats 1000000 in
/-- The bounded-codegree odd witness for almost-regular bipartite simple graphs. -/
theorem uniform_bounded_codegree_bipartite_odd_witness_of_exponent (t : ℕ) (ht : 2 ≤ t)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hδgap : δ < (((2 * t + 1 : ℕ) : ℝ)) * ε) :
    let r : ℝ := (2 * t + 1 : ℕ)
    let a := 2 - 2 / r + ε
    ∃ k : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
        Fintype.card V = n → G.IsBipartite →
        (∃ d : ℝ, 0 < d ∧ ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ K * d) →
        (n : ℝ) ^ a ≤ (G.edgeFinset.card : ℝ) →
        ∀ L : ℕ, (L : ℝ) ≤ (n : ℝ) ^ δ →
        (∀ u : Finset V, u.card = t + 1 → (relationCommon G.Adj u).card ≤ L) →
        cycleWithMatching (((k + 1) + (k + 1)) + 2) t ⊑ G := by
  classical
  intro r a
  obtain ⟨k, h⟩ := uniform_bounded_codegree_odd_witness_of_exponent t ht ε δ hε hδ hδgap
  refine ⟨k, ?_⟩
  intro K hK
  filter_upwards [h (2 * K) (by positivity)] with n hn
  intro V _ _ G hV hb hreg hE L hL hcodeg
  obtain ⟨d, hd, hreg⟩ := hreg
  obtain ⟨s, w, hsw⟩ := isBipartite_iff_exists_isBipartiteWith.mp hb
  let S := s.toFinset
  let T := w.toFinset
  have hs : (S : Set V) = s := Set.coe_toFinset s
  have ht' : (T : Set V) = w := Set.coe_toFinset w
  have hST : G.IsBipartiteWith S T := by rw [hs, ht']; exact hsw
  let R (u : S) (v : T) := G.Adj u.val v.val
  have hpos (v : V) : 0 < G.degree v := by
    have hv : (0 : ℝ) < G.degree v := hd.trans_le (hreg v).1
    exact_mod_cast hv
  have hcover : S ∪ T = univ := by
    apply eq_univ_of_forall
    intro v
    obtain ⟨y, hy⟩ := (G.degree_pos_iff_exists_adj v).1 (hpos v)
    rcases hST.mem_of_adj hy with h | h
    · exact mem_union_left _ h.1
    · exact mem_union_right _ h.1
  have hcount : Fintype.card ↥S + Fintype.card ↥T = n := by
    rw [Fintype.card_coe, Fintype.card_coe,
      ← card_union_of_disjoint (disjoint_coe.mp hST.disjoint), hcover, card_univ, hV]
  have hm : Fintype.card (RelationEdge R) = G.edgeFinset.card := by
    rw [card_relationEdge]
    calc
      _ = ∑ v : T, G.degree v.val :=
        sum_congr rfl (fun v _ => card_relation_col G S T hST v)
      _ = ∑ v ∈ T, G.degree v := Finset.sum_coe_sort (s := T) (f := fun (v : V) => G.degree v)
      _ = _ := isBipartiteWith_sum_degrees_eq_card_edges' hST
  let D := G.maxDegree
  have hD : (D : ℝ) ≤ 2 * K * (Fintype.card (RelationEdge R) : ℝ) / n := by
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    have hnpos : (0 : ℝ) < n := by rw [← hV]; exact_mod_cast Fintype.card_pos (α := V)
    have hs : (n : ℝ) * d ≤ 2 * G.edgeFinset.card := by
      rw [← hV]
      calc
        _ = ∑ _v : V, d := by simp
        _ ≤ ∑ v : V, ((G.degree v : ℕ) : ℝ) := sum_le_sum fun v _ => (hreg v).1
        _ = _ := by exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hD₁ : (D : ℝ) ≤ K * d := by rw [show D = G.degree v from hv]; exact (hreg v).2
    rw [hm, le_div_iff₀ hnpos]
    calc
      _ ≤ (K * d) * n := mul_le_mul_of_nonneg_right hD₁ hnpos.le
      _ = K * ((n : ℝ) * d) := by ring
      _ ≤ _ := by simpa only [mul_assoc, mul_left_comm K] using mul_le_mul_of_nonneg_left hs hK
  have hR₁ (u : S) : ((univ : Finset ↥T).filter (R u)).card ≤ D :=
    (card_relation_row G S T hST u).le.trans (G.degree_le_maxDegree u.val)
  have hR₂ (v : T) : ((univ : Finset ↥S).filter (fun u => R u v)).card ≤ D :=
    (card_relation_col G S T hST v).le.trans (G.degree_le_maxDegree v.val)
  have hL₁ (u : Finset ↥S) (hu : u.card = t + 1) : (relationCommon R u).card ≤ L :=
    (common_subtype_le G S T u).trans (hcodeg (u.map (Function.Embedding.subtype _)) (by simp [hu]))
  have hL₂ (u : Finset ↥T) (hu : u.card = t + 1) :
      (relationCommon (Function.swap R) u).card ≤ L := by
    have he :
        relationCommon (Function.swap R) u =
          relationCommon (fun (a : T) (b : S) => G.Adj a.val b.val) u := by
      ext v
      simp only [mem_relationCommon, Function.swap, R]
      exact ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
    rw [he]
    exact (common_subtype_le G T S u).trans (hcodeg (u.map (Function.Embedding.subtype _)) (by simp [hu]))
  have hrel : cycleWithMatching (((k + 1) + (k + 1)) + 2) t ⊑ relationGraph R :=
    hn ↥S ↥T R hcount (by rw [hm]; exact hE) D L hD hL hR₁ hR₂ hL₁ hL₂
  exact hrel.trans (relationGraph_contained G S T hST)

theorem uniform_bounded_codegree_bipartite_odd_witness (t : ℕ) (ht : 2 ≤ t)
    (ε : ℝ) (hε : 0 < ε) :
    let r : ℝ := (2 * t + 1 : ℕ)
    let a := 2 - 2 / r + ε
    let δ := r * ε / 4
    ∃ k : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
        Fintype.card V = n → G.IsBipartite →
        (∃ d : ℝ, 0 < d ∧ ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ K * d) →
        (n : ℝ) ^ a ≤ (G.edgeFinset.card : ℝ) →
        ∀ L : ℕ, (L : ℝ) ≤ (n : ℝ) ^ δ →
        (∀ u : Finset V, u.card = t + 1 → (relationCommon G.Adj u).card ≤ L) →
        cycleWithMatching (((k + 1) + (k + 1)) + 2) t ⊑ G := by
  intro r a δ
  have hr : 0 < r := by dsimp [r]; positivity
  have hprod : 0 < r * ε := mul_pos hr hε
  exact uniform_bounded_codegree_bipartite_odd_witness_of_exponent t ht ε δ hε
    (by dsimp [δ]; positivity) (by change r * ε / 4 < r * ε; linarith)

theorem eventually_bounded_codegree_bipartite_odd_witness (t : ℕ) (ht : 2 ≤ t)
    (ε K : ℝ) (hε : 0 < ε) (hK : 0 ≤ K) :
    let r : ℝ := (2 * t + 1 : ℕ)
    let a := 2 - 2 / r + ε
    let δ := r * ε / 4
    ∃ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
        Fintype.card V = n → G.IsBipartite →
        (∃ d : ℝ, 0 < d ∧ ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ K * d) →
        (n : ℝ) ^ a ≤ (G.edgeFinset.card : ℝ) →
        ∀ L : ℕ, (L : ℝ) ≤ (n : ℝ) ^ δ →
        (∀ u : Finset V, u.card = t + 1 → (relationCommon G.Adj u).card ≤ L) →
        cycleWithMatching (((k + 1) + (k + 1)) + 2) t ⊑ G := by
  obtain ⟨k, h⟩ := uniform_bounded_codegree_bipartite_odd_witness t ht ε hε
  exact ⟨k, h K hK⟩

/-- At odd degrees at least five, only the large-codegree regime remains for the chosen witness. -/
theorem odd_degree_reduction_to_high_codegrees_at_exponent (t : ℕ) (ht : 2 ≤ t) (ε η δ : ℝ)
    (hη : 0 < η) (hηε : η < ε) (hδ : 0 ≤ δ)
    (hδgap : δ < (((2 * t + 1 : ℕ) : ℝ)) * (ε - η)) :
    let r : ℝ := (2 * t + 1 : ℕ)
    let a := 2 - 2 / r + (ε - η)
    ∃ l : ℕ, 4 ≤ l ∧ Even l ∧
      ((∀ K : ℝ, 0 ≤ K → ∀ᶠ n : ℕ in atTop,
        ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
          Fintype.card V = n → G.IsBipartite →
          (∃ d : ℝ, 0 < d ∧ ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ K * d) →
          (n : ℝ) ^ a ≤ (G.edgeFinset.card : ℝ) →
          (∃ u : Finset V, u.card = t + 1 ∧ (n : ℝ) ^ δ < (relationCommon G.Adj u).card) →
          cycleWithMatching l t ⊑ G) →
      ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree (2 * t + 1) ∧
        (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
          fun n : ℕ => (n : ℝ) ^ (2 - 2 / r + ε)) := by
  classical
  intro r a
  have heta : 0 < ε - η := sub_pos.mpr hηε
  obtain ⟨k, hlow⟩ :=
    uniform_bounded_codegree_bipartite_odd_witness_of_exponent t ht (ε - η) δ heta hδ hδgap
  let l := ((k + 1) + (k + 1)) + 2
  have hl : 4 ≤ l := by dsimp [l]; omega
  refine ⟨l, hl, ⟨k + 2, by dsimp [l]; omega⟩, ?_⟩
  intro hhigh
  have hr5 : (5 : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast (show 5 ≤ 2 * t + 1 by omega)
  have ha : 1 < a := by
    have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) < 5 by norm_num) hr5
    dsimp [a]
    linarith only [h, heta]
  let W := cycleWithMatching l t
  have hW := extremal_of_almost_regular_bipartite_test W a η ha hη (by
    intro K
    let K' := max K 0
    have hK' : 0 ≤ K' := le_max_right _ _
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlow K' hK').and (hhigh K' hK'))
    refine ⟨N, ?_⟩
    intro V _ _ G hVN hb hreg he
    have hboth := hN (Fintype.card V) hVN
    have hreg' : ∃ d : ℝ, 0 < d ∧ ∀ v : V,
        d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ K' * d := by
      obtain ⟨d, hd, hdeg⟩ := hreg
      exact ⟨d, hd, fun v => ⟨(hdeg v).1,
        (hdeg v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd.le)⟩⟩
    by_cases hlarge : ∃ u : Finset V, u.card = t + 1 ∧
        (Fintype.card V : ℝ) ^ δ < (relationCommon G.Adj u).card
    · exact hboth.2 V G rfl hb hreg' he hlarge
    · let L := ⌊(Fintype.card V : ℝ) ^ δ⌋₊
      have hnon : 0 ≤ (Fintype.card V : ℝ) ^ δ := by positivity
      have hL : (L : ℝ) ≤ (Fintype.card V : ℝ) ^ δ := Nat.floor_le hnon
      have hc (u : Finset V) (hu : u.card = t + 1) : (relationCommon G.Adj u).card ≤ L := by
        apply (Nat.le_floor_iff hnon).2
        exact le_of_not_gt (fun h => hlarge ⟨u, hu, h⟩)
      exact hboth.1 V G rfl hb hreg' he L hL hc)
  have : Nonempty ((Fin l × Fin t) × Fin 2) :=
    ⟨((⟨0, by omega⟩, ⟨0, by omega⟩), 0)⟩
  have hExp : a + η = 2 - 2 / r + ε := by dsimp [a]; ring
  exact regular_witness_on_fin W (2 * t + 1) (cycleWithMatching_regular l t (by omega)) _
    (by simpa only [hExp] using hW)

theorem odd_degree_reduction_to_high_codegrees (t : ℕ) (ht : 2 ≤ t) (ε : ℝ) (hε : 0 < ε) :
    let r : ℝ := (2 * t + 1 : ℕ)
    let a := 2 - 2 / r + ε / 2
    let δ := r * (ε / 2) / 4
    ∃ l : ℕ, 4 ≤ l ∧ Even l ∧
      ((∀ K : ℝ, 0 ≤ K → ∀ᶠ n : ℕ in atTop,
        ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
          Fintype.card V = n → G.IsBipartite →
          (∃ d : ℝ, 0 < d ∧ ∀ v, d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ K * d) →
          (n : ℝ) ^ a ≤ (G.edgeFinset.card : ℝ) →
          (∃ u : Finset V, u.card = t + 1 ∧ (n : ℝ) ^ δ < (relationCommon G.Adj u).card) →
          cycleWithMatching l t ⊑ G) →
      ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree (2 * t + 1) ∧
        (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
          fun n : ℕ => (n : ℝ) ^ (2 - 2 / r + ε)) := by
  intro r a δ
  have hη : 0 < ε / 2 := by positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hδgap : δ < r * (ε - ε / 2) := by
    dsimp [δ]
    nlinarith only [mul_pos hr hε]
  have h := odd_degree_reduction_to_high_codegrees_at_exponent t ht ε (ε / 2) δ hη
    (by linarith) (by dsimp [δ]; positivity) hδgap
  rw [show ε - ε / 2 = ε / 2 by ring] at h
  exact h

end JanzerRelay

theorem OMA.solution : type_of% @Erdos147.erdos_147.variants.janzer_conjecture := by
  intro r hr ε hε
  by_cases he : Even r
  · exact JanzerRelay.even_degree_case r hr he ε hε
  have ho : Odd r := Nat.not_even_iff_odd.mp he
  by_cases hlarge : 2 / ((r : ℝ) * ((r : ℝ) + 1)) < ε
  · exact JanzerRelay.odd_degree_with_error r hr ho ε hlarge
  · sorry

