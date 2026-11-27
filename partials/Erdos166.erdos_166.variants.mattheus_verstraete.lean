import FormalConjectures.ErdosProblems.«166»

-- Problem: Erdős Problem 166 — mattheus verstraete
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/166.lean:65 (declaration Erdos166.erdos_166.variants.mattheus_verstraete)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

namespace OMA

/-- A graph on `Fin n` with no copy of `K_a` and whose complement has no copy of `K_b`
shows `n < R(a, b)`. -/
theorem lt_classicalRamsey_of_graph (a b n : ℕ) (G : SimpleGraph (Fin n))
    (h1 : ¬ (SimpleGraph.completeGraph (Fin a)).IsContained G)
    (h2 : ¬ (SimpleGraph.completeGraph (Fin b)).IsContained Gᶜ) :
    n < SimpleGraph.classicalRamsey a b ∨ SimpleGraph.classicalRamsey a b = 0 := by
  unfold SimpleGraph.classicalRamsey SimpleGraph.graphRamsey
  set S := { m : ℕ | ∀ (C : SimpleGraph (Fin m)),
    (SimpleGraph.completeGraph (Fin a)).IsContained C ∨
      (SimpleGraph.completeGraph (Fin b)).IsContained Cᶜ } with hS
  rcases S.eq_empty_or_nonempty with he | hne
  · right; rw [he, Nat.sInf_empty]
  left
  by_contra hlt
  push Not at hlt
  have hmem := Nat.sInf_mem hne
  let f : Fin (sInf S) ↪ Fin n := Fin.castLEEmb hlt
  have hf : Function.Injective f := f.injective
  rcases hmem (G.comap f) with h | h
  · exact h1 (h.trans ⟨⟨⟨f, fun hab => hab⟩, hf⟩⟩)
  · apply h2
    refine h.trans ⟨⟨⟨f, ?_⟩, hf⟩⟩
    intro x y hxy
    simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj] at hxy ⊢
    exact ⟨fun e => hxy.1 (hf e), hxy.2⟩

section Greedy

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Delete a vertex and all its neighbors in the current set. -/
def mvDelete (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => w ≠ v ∧ ¬ G.Adj v w

/-- Follow the greedy order until the prescribed vertex is reached. -/
def mvPeel (pick : Finset V → V) : ℕ → Finset V → V → Finset V
  | 0, _, _ => ∅
  | fuel + 1, S, v =>
    if pick S = v then mvDelete G S v
    else mvPeel pick fuel (S.erase (pick S)) v

theorem mv_peel_step (pick : Finset V → V) (R : ℕ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hmem : ∀ S : Finset V, S.Nonempty → pick S ∈ S)
    (hshrink : ∀ S : Finset V, R < S.card →
      ((mvDelete G S (pick S)).card : ℝ) ≤ β * S.card)
    (fuel : ℕ) (S I : Finset V) (hfuel : S.card ≤ fuel)
    (hIS : I ⊆ S) (hI : I.Nonempty) (hind : G.IsIndepSet (I : Set V)) :
    ∃ v ∈ I, I.erase v ⊆ mvPeel G pick fuel S v ∧
      ((mvPeel G pick fuel S v).card : ℝ) ≤ max (R : ℝ) (β * S.card) := by
  induction fuel generalizing S with
  | zero =>
    have hpos := Finset.card_pos.mpr (hI.mono hIS)
    omega
  | succ fuel ih =>
    have h₁ : pick S ∈ S := hmem S (hI.mono hIS)
    by_cases h₂ : pick S ∈ I
    · refine ⟨pick S, h₂, ?_⟩
      simp only [mvPeel]
      constructor
      · intro w hw
        rw [Finset.mem_erase] at hw
        exact Finset.mem_filter.mpr ⟨hIS hw.2, hw.1,
          hind h₂ hw.2 (Ne.symm hw.1)⟩
      · by_cases hR : R < S.card
        · exact (hshrink S hR).trans (le_max_right _ _)
        · have hle : (mvDelete G S (pick S)).card ≤ R :=
            (Finset.card_le_card (Finset.filter_subset _ _)).trans (Nat.le_of_not_gt hR)
          exact (Nat.cast_le.mpr hle).trans (le_max_left _ _)
    · have hIS' : I ⊆ S.erase (pick S) := by
        intro w hw
        refine Finset.mem_erase.mpr ⟨?_, hIS hw⟩
        rintro rfl
        exact h₂ hw
      have hfuel' : (S.erase (pick S)).card ≤ fuel := by
        rw [Finset.card_erase_of_mem h₁]
        omega
      obtain ⟨v, hv, htail, hsize⟩ := ih _ hfuel' hIS'
      have hne : pick S ≠ v := fun e => h₂ (e ▸ hv)
      refine ⟨v, hv, ?_⟩
      simp only [mvPeel, if_neg hne]
      refine ⟨htail, hsize.trans (max_le_max le_rfl (mul_le_mul_of_nonneg_left ?_ hβ))⟩
      exact Nat.cast_le.mpr (Finset.card_le_card (Finset.erase_subset _ _))

/-- Reconstruct the residual set after successive greedy choices. -/
def mvReplay (pick : Finset V → V) : Finset V → List V → Finset V
  | S, [] => S
  | S, v :: l => mvReplay pick (mvPeel G pick S.card S v) l

theorem mv_independent_encoding (pick : Finset V → V) (R : ℕ) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hmem : ∀ S : Finset V, S.Nonempty → pick S ∈ S)
    (hshrink : ∀ S : Finset V, R < S.card →
      ((mvDelete G S (pick S)).card : ℝ) ≤ β * S.card)
    (r : ℕ) (S I : Finset V) (hIS : I ⊆ S) (hr : r ≤ I.card)
    (hind : G.IsIndepSet (I : Set V)) :
    ∃ (l : List V) (T : Finset V), l.length = r ∧
      T ⊆ mvReplay G pick S l ∧ I = l.toFinset ∪ T ∧ T.card + r = I.card ∧
      ((mvReplay G pick S l).card : ℝ) ≤ max (R : ℝ) (β ^ r * S.card) := by
  induction r generalizing I S with
  | zero =>
    refine ⟨[], I, rfl, hIS, by simp, by simp, ?_⟩
    simpa [mvReplay] using le_max_right (R : ℝ) (S.card : ℝ)
  | succ r ih =>
    have hI : I.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv, hs, hb⟩ := mv_peel_step G pick R β hβ hmem hshrink S.card S I le_rfl hIS hI hind
    have hcard := Finset.card_erase_of_mem hv
    have hsub : G.IsIndepSet (↑(I.erase v) : Set V) :=
      hind.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
    obtain ⟨l, T, hl, hT, he, hcard', hb'⟩ := ih _ _ hs (by omega) hsub
    refine ⟨v :: l, T, by simp [hl], hT, ?_, by omega, ?_⟩
    · simpa [List.toFinset_cons, Finset.insert_union, ← he] using (Finset.insert_erase hv).symm
    · change ((mvReplay G pick (mvPeel G pick S.card S v) l).card : ℝ) ≤
        max (R : ℝ) (β ^ (r + 1) * S.card)
      apply hb'.trans
      refine max_le (le_max_left _ _) ?_
      have hp : 0 ≤ β ^ r := pow_nonneg hβ _
      apply (mul_le_mul_of_nonneg_left hb hp).trans
      rw [mul_max_of_nonneg _ _ hp]
      apply max_le
      · apply le_max_of_le_left
        calc
          β ^ r * (R : ℝ) ≤ 1 * (R : ℝ) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hβ hβ') (Nat.cast_nonneg _)
          _ = R := one_mul _
      · rw [← mul_assoc, ← pow_succ]
        exact le_max_right _ _

/-- Independent subsets of a prescribed size. -/
noncomputable def mvIndependents (S : Finset V) (t : ℕ) : Finset (Finset V) := by
  classical
  exact (S.powersetCard t).filter fun T => G.IsIndepSet (T : Set V)

@[simp] theorem mv_mem_independents {S I : Finset V} {t : ℕ} :
    I ∈ mvIndependents G S t ↔ I ⊆ S ∧ I.card = t ∧ G.IsIndepSet (I : Set V) := by
  classical
  simp [mvIndependents, and_assoc]

theorem mv_card_independents_le [Fintype V] (pick : Finset V → V) (R : ℕ) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hmem : ∀ S : Finset V, S.Nonempty → pick S ∈ S)
    (hshrink : ∀ S : Finset V, R < S.card →
      ((mvDelete G S (pick S)).card : ℝ) ≤ β * S.card)
    (S : Finset V) (r t : ℕ) (hrt : r ≤ t) (hsmall : β ^ r * S.card ≤ R) :
    (mvIndependents G S t).card ≤ Fintype.card V ^ r * R.choose (t - r) := by
  classical
  let rest (f : Fin r → V) : Finset V := mvReplay G pick S (List.ofFn f)
  let tails (f : Fin r → V) : Finset (Finset V) :=
    if (rest f).card ≤ R then
      ((rest f).powersetCard (t - r)).image fun T => (List.ofFn f).toFinset ∪ T
    else ∅
  have hcover : mvIndependents G S t ⊆ (Finset.univ : Finset (Fin r → V)).biUnion tails := by
    intro I hI
    obtain ⟨hIS, hcard, hind⟩ := (mv_mem_independents G).mp hI
    obtain ⟨l, T, hl, hT, he, hcard', hbound⟩ :=
      mv_independent_encoding G pick R β hβ hβ' hmem hshrink r S I hIS
        (hcard ▸ hrt) hind
    rw [max_eq_left hsmall] at hbound
    let f (i : Fin r) : V := l.get (Fin.cast hl.symm i)
    have hf : List.ofFn f = l := by
      subst r
      exact List.ofFn_get l
    have hrest : (rest f).card ≤ R := by simpa [rest, hf] using hbound
    refine Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _, ?_⟩
    change I ∈ (if _ then _ else _)
    rw [if_pos hrest]
    refine Finset.mem_image.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨?_, by omega⟩, ?_⟩
    · simpa [rest, hf] using hT
    · rw [hf, ← he]
  have htails (f : Fin r → V) : (tails f).card ≤ R.choose (t - r) := by
    by_cases h : (rest f).card ≤ R
    · unfold tails
      rw [if_pos h]
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_choose _ h
    · simp [tails, h]
  calc
    (mvIndependents G S t).card ≤ ((Finset.univ : Finset (Fin r → V)).biUnion tails).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ f : Fin r → V, (tails f).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin r → V, R.choose (t - r) := Finset.sum_le_sum fun f _ => htails f
    _ = _ := by simp

end Greedy

section Sampling

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The color-zero class of a labeling. -/
def mvSample {d : ℕ} (c : V → Fin (d + 1)) : Finset V :=
  Finset.univ.filter fun v => c v = 0

theorem mv_card_labelings_containing (d : ℕ) (T : Finset V) :
    ((Finset.univ : Finset (V → Fin (d + 1))).filter
      (fun c => T ⊆ mvSample c)).card = (d + 1) ^ (Fintype.card V - T.card) := by
  classical
  let e : {c : V → Fin (d + 1) // T ⊆ mvSample c} ≃
      ({v : V // v ∉ T} → Fin (d + 1)) :=
    { toFun := fun c v => c.1 v.1
      invFun := fun f => ⟨fun v => if h : v ∈ T then 0 else f ⟨v, h⟩, by
        intro v hv
        simp [mvSample, hv]⟩
      left_inv := by
        intro c
        apply Subtype.ext
        funext v
        by_cases hv : v ∈ T
        · exact (dif_pos hv).trans (Finset.mem_filter.mp (c.2 hv)).2.symm
        · exact dif_neg hv
      right_inv := by
        intro f
        funext v
        exact dif_neg v.2 }
  have h := Fintype.card_congr e
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl,
    Fintype.card_subtype, Fintype.card_subtype] at h
  simpa using h

private theorem mv_sum_card_filter_swap {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (t : Finset B) (p : A → B → Prop) [DecidableRel p] :
    ∑ a ∈ s, (t.filter (p a)).card = ∑ b ∈ t, (s.filter (fun a => p a b)).card := by
  calc
    _ = ∑ a ∈ s, ∑ b ∈ t, if p a b then 1 else 0 :=
      Finset.sum_congr rfl fun a _ => (Finset.sum_boole (p a) t).symm
    _ = ∑ b ∈ t, ∑ a ∈ s, if p a b then 1 else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun b _ => Finset.sum_boole (fun a => p a b) s

theorem mv_sample_avoids_independents (G : SimpleGraph V) [DecidableRel G.Adj] (d t m : ℕ) (ht : 0 < t)
    (hsize : m * (d + 1) ^ Fintype.card V +
        (mvIndependents G Finset.univ t).card * (d + 1) ^ (Fintype.card V - t) ≤
      Fintype.card V * (d + 1) ^ (Fintype.card V - 1)) :
    ∃ S : Finset V, m ≤ S.card ∧ mvIndependents G S t = ∅ := by
  classical
  let labels : Finset (V → Fin (d + 1)) := Finset.univ
  let family := mvIndependents G Finset.univ t
  let bad (c : V → Fin (d + 1)) := family.filter (· ⊆ mvSample c)
  let pick (T : Finset V) (h : T.Nonempty) : V := h.choose
  let drop (c : V → Fin (d + 1)) := (bad c).attach.image fun T =>
    pick T.1 (Finset.card_pos.mp (by
      have hcard := ((mv_mem_independents G).mp (Finset.mem_filter.mp T.2).1).2.1
      omega))
  let keep (c : V → Fin (d + 1)) := mvSample c \ drop c
  have havoid (c : V → Fin (d + 1)) : mvIndependents G (keep c) t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    obtain ⟨hsub, hcard, hind⟩ := (mv_mem_independents G).mp hT
    have hb : T ∈ bad c := Finset.mem_filter.mpr
      ⟨(mv_mem_independents G).mpr ⟨Finset.subset_univ _, hcard, hind⟩,
        hsub.trans Finset.sdiff_subset⟩
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    have hp : pick T hne ∈ T := hne.choose_spec
    have hd : pick T hne ∈ drop c :=
      Finset.mem_image.mpr ⟨⟨T, hb⟩, Finset.mem_attach _ _, rfl⟩
    exact (Finset.mem_sdiff.mp (hsub hp)).2 hd
  have hpoint (c : V → Fin (d + 1)) :
      (mvSample c).card ≤ (keep c).card + (bad c).card :=
    Finset.card_le_card_sdiff_add_card.trans
      (Nat.add_le_add_left (Finset.card_image_le.trans_eq Finset.card_attach) _)
  have hsample : ∑ c ∈ labels, (mvSample c).card =
      Fintype.card V * (d + 1) ^ (Fintype.card V - 1) := by
    unfold mvSample
    rw [mv_sum_card_filter_swap labels Finset.univ (fun c v => c v = 0)]
    calc
      _ = ∑ _v : V, (d + 1) ^ (Fintype.card V - 1) := by
        apply Finset.sum_congr rfl
        intro v _
        simpa [labels, mvSample] using mv_card_labelings_containing d ({v} : Finset V)
      _ = _ := by simp
  have hbad : ∑ c ∈ labels, (bad c).card =
      family.card * (d + 1) ^ (Fintype.card V - t) := by
    unfold bad
    rw [mv_sum_card_filter_swap labels family (fun c T => T ⊆ mvSample c)]
    calc
      _ = ∑ _T ∈ family, (d + 1) ^ (Fintype.card V - t) := by
        apply Finset.sum_congr rfl
        intro T hT
        have hcard := ((mv_mem_independents G).mp hT).2.1
        simpa [labels, hcard] using mv_card_labelings_containing d T
      _ = _ := by simp
  have hsum : (∑ c ∈ labels, m) ≤ ∑ c ∈ labels, (keep c).card := by
    have hb := Finset.sum_le_sum fun c (_ : c ∈ labels) => hpoint c
    rw [hsample, Finset.sum_add_distrib, hbad] at hb
    change m * (d + 1) ^ Fintype.card V +
      family.card * (d + 1) ^ (Fintype.card V - t) ≤ _ at hsize
    simpa [labels, Nat.mul_comm] using Nat.le_of_add_le_add_right (hsize.trans hb)
  have hlabels : labels.Nonempty := ⟨fun _ => 0, Finset.mem_univ _⟩
  by_contra h
  push Not at h
  have hlt := Finset.sum_lt_sum_of_nonempty hlabels
    (fun c (_ : c ∈ labels) => lt_of_not_ge (fun hm => (h (keep c) hm).ne_empty (havoid c)))
  exact (not_lt_of_ge hsum) hlt

theorem mv_sample_of_count_le (G : SimpleGraph V) [DecidableRel G.Adj] (d t m : ℕ)
    (ht : 0 < t) (hcount : (mvIndependents G Finset.univ t).card ≤ (d + 1) ^ t)
    (hm : (m + 1) * (d + 1) ≤ Fintype.card V) :
    ∃ S : Finset V, m ≤ S.card ∧ mvIndependents G S t = ∅ := by
  apply mv_sample_avoids_independents G d t m ht
  let N := Fintype.card V
  change m * (d + 1) ^ N + _ ≤ N * (d + 1) ^ (N - 1)
  have hN : 0 < N := (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)).trans_le hm
  have he : (d + 1) ^ N = (d + 1) * (d + 1) ^ (N - 1) := by
    conv_lhs => rw [show N = N - 1 + 1 by omega, pow_succ, Nat.mul_comm]
  calc
    _ ≤ (m + 1) * (d + 1) ^ N := by
      rw [Nat.add_mul, Nat.one_mul]
      apply Nat.add_le_add_left
      by_cases htN : t ≤ N
      · refine (Nat.mul_le_mul_right _ hcount).trans_eq ?_
        rw [← pow_add, Nat.add_sub_cancel' htN]
      · have hE : mvIndependents G Finset.univ t = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro T hT
          have hTcard := ((mv_mem_independents G).mp hT).2.1
          exact htN (hTcard ▸ Finset.card_le_univ T)
        simp [hE]
    _ = ((m + 1) * (d + 1)) * (d + 1) ^ (N - 1) := by rw [he, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ hm

end Sampling

section Ramsey

private theorem mv_finite_ramsey {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (a b : ℕ) (S : Finset V) (hS : 2 ^ (a + b) ≤ S.card) :
    (∃ T ⊆ S, G.IsNClique a T) ∨ (∃ T ⊆ S, Gᶜ.IsNClique b T) := by
  classical
  induction a generalizing b S with
  | zero =>
    exact Or.inl ⟨∅, Finset.empty_subset _, by simp [SimpleGraph.isNClique_iff]⟩
  | succ a iha =>
    induction b generalizing S with
    | zero =>
      exact Or.inr ⟨∅, Finset.empty_subset _, by simp [SimpleGraph.isNClique_iff]⟩
    | succ b ihb =>
      obtain ⟨v, hv⟩ := Finset.card_pos.mp ((pow_pos (by decide : 0 < (2 : ℕ)) _).trans_le hS)
      let A := (S.erase v).filter (G.Adj v)
      let B := (S.erase v).filter (fun w => ¬G.Adj v w)
      have hab : A.card + B.card = S.card - 1 := by
        exact (Finset.card_filter_add_card_filter_not (G.Adj v)).trans
          (Finset.card_erase_of_mem hv)
      have hsplit : 2 * 2 ^ (a + b + 1) ≤ S.card := by
        rw [← pow_succ']
        convert hS using 2
        omega
      have hAs : A ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hBs : B ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      by_cases hA : 2 ^ (a + b + 1) ≤ A.card
      · obtain ⟨T, hT, hcl⟩ | ⟨T, hT, hcl⟩ := iha (b + 1) A hA
        · refine Or.inl ⟨insert v T, Finset.insert_subset_iff.mpr ⟨hv, hT.trans hAs⟩, ?_⟩
          have hnv : v ∉ T := fun h => (Finset.mem_erase.mp ((Finset.mem_filter.mp (hT h)).1)).1 rfl
          rw [SimpleGraph.isNClique_iff, Finset.coe_insert, Finset.card_insert_of_notMem hnv,
            hcl.card_eq]
          exact ⟨hcl.isClique.insert fun w hw _ => (Finset.mem_filter.mp (hT hw)).2, rfl⟩
        · exact Or.inr ⟨T, hT.trans hAs, hcl⟩
      · have hB : 2 ^ (a + 1 + b) ≤ B.card := by
          rw [show a + 1 + b = a + b + 1 by omega]
          omega
        obtain ⟨T, hT, hcl⟩ | ⟨T, hT, hcl⟩ := ihb B hB
        · exact Or.inl ⟨T, hT.trans hBs, hcl⟩
        · refine Or.inr ⟨insert v T, Finset.insert_subset_iff.mpr ⟨hv, hT.trans hBs⟩, ?_⟩
          have hnv : v ∉ T := fun h => (Finset.mem_erase.mp ((Finset.mem_filter.mp (hT h)).1)).1 rfl
          rw [SimpleGraph.isNClique_iff, Finset.coe_insert, Finset.card_insert_of_notMem hnv,
            hcl.card_eq]
          exact ⟨hcl.isClique.insert fun w hw hn =>
            (SimpleGraph.compl_adj _ _ _).mpr ⟨hn, (Finset.mem_filter.mp (hT hw)).2⟩, rfl⟩

theorem mv_classicalRamsey_pos (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    0 < SimpleGraph.classicalRamsey a b := by
  classical
  unfold SimpleGraph.classicalRamsey SimpleGraph.graphRamsey
  let S := { n : ℕ | ∀ C : SimpleGraph (Fin n),
    (SimpleGraph.completeGraph (Fin a)).IsContained C ∨
    (SimpleGraph.completeGraph (Fin b)).IsContained Cᶜ }
  change 0 < sInf S
  have hS : S.Nonempty := by
    refine ⟨2 ^ (a + b), fun C => ?_⟩
    obtain ⟨T, _, hT⟩ | ⟨T, _, hT⟩ :=
      mv_finite_ramsey C a b Finset.univ (by simp)
    · exact Or.inl ((SimpleGraph.not_cliqueFree_iff_top_isContained a).mp hT.not_cliqueFree)
    · exact Or.inr ((SimpleGraph.not_cliqueFree_iff_top_isContained b).mp hT.not_cliqueFree)
  by_contra! h
  have h0 : sInf S = 0 := by omega
  have hm := Nat.sInf_mem hS
  rw [h0] at hm
  obtain hC | hC := hm (⊥ : SimpleGraph (Fin 0))
  · have hle := Fintype.card_le_of_injective _ hC.some.injective
    simpa [Nat.ne_of_gt ha] using hle
  · have hle := Fintype.card_le_of_injective _ hC.some.injective
    simpa [Nat.ne_of_gt hb] using hle

theorem mv_ramsey_of_sample {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.completeGraph (Fin 4)).IsContained G)
    (S : Finset V) {t k : ℕ} (ht : 0 < t) (htk : t ≤ k)
    (hS : mvIndependents G S t = ∅) : S.card < SimpleGraph.classicalRamsey 4 k := by
  classical
  let f : Fin S.card ↪ V :=
    (Finset.equivFin S).symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  let H := G.comap f
  have hH : ¬ (SimpleGraph.completeGraph (Fin 4)).IsContained H := by
    intro h
    apply hG
    exact h.trans ⟨⟨⟨f, fun h => h⟩, f.injective⟩⟩
  have hH' : ¬ (SimpleGraph.completeGraph (Fin k)).IsContained Hᶜ := by
    intro h
    let g : Fin t ↪ V := (Fin.castLEEmb htk).trans (h.some.toEmbedding.trans f)
    let T : Finset V := Finset.univ.map g
    have hTS : T ⊆ S := by
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
      exact ((Finset.equivFin S).symm (h.some (Fin.castLEEmb htk i))).2
    have hTcard : T.card = t := by simp [T]
    have hTi : G.IsIndepSet (T : Set V) := by
      intro v hv w hw hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hw
      have hij : i ≠ j := fun he => hne (congrArg g he)
      have hC := h.some.toHom.map_adj (show (SimpleGraph.completeGraph (Fin k)).Adj
        (Fin.castLEEmb htk i) (Fin.castLEEmb htk j) from fun he => hij ((Fin.castLEEmb htk).injective he))
      exact ((SimpleGraph.compl_adj _ _ _).mp hC).2
    have hm := (mv_mem_independents G).mpr ⟨hTS, hTcard, hTi⟩
    simpa [hS] using hm
  exact (lt_classicalRamsey_of_graph 4 k _ H hH hH').resolve_right
    (Nat.ne_of_gt (mv_classicalRamsey_pos 4 k (by decide) (ht.trans_le htk)))

end Ramsey

section Estimates

private theorem mv_choose_mul_pow_le (R s D : ℕ) (hs : 0 < s)
    (h : 6 * R ≤ D * s) : 2 ^ s * R.choose s ≤ D ^ s := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have he : (s : ℝ) ^ s / s.factorial ≤ (3 : ℝ) ^ s := by
    refine (Real.pow_div_factorial_le_exp (s : ℝ) hs'.le s).trans ?_
    rw [show (s : ℝ) = (s : ℝ) * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have hc : (R.choose s : ℝ) ≤ (3 * (R : ℝ) / s) ^ s := by
    calc
      _ ≤ (R : ℝ) ^ s / s.factorial := Nat.choose_le_pow_div s R
      _ = ((R : ℝ) / s) ^ s * ((s : ℝ) ^ s / s.factorial) := by
        rw [div_pow, div_mul_div_comm]
        field_simp
      _ ≤ ((R : ℝ) / s) ^ s * (3 : ℝ) ^ s :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; ring
  have h' : 6 * (R : ℝ) ≤ (D : ℝ) * s := by exact_mod_cast h
  have hb : 2 * (3 * (R : ℝ) / s) ≤ D := by
    rw [← mul_div_assoc, div_le_iff₀ hs']
    linarith
  have hl : (2 : ℝ) ^ s * (R.choose s : ℝ) ≤ (D : ℝ) ^ s := by
    refine (mul_le_mul_of_nonneg_left hc (by positivity)).trans ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hb _
  exact_mod_cast hl

theorem mv_ramsey_of_dense_graph {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ¬ (SimpleGraph.completeGraph (Fin 4)).IsContained G)
    (R M r s d m k : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hdeg : ∀ S : Finset V, R < S.card →
      ∃ v ∈ S, ((mvDelete G S v).card : ℝ) ≤ β * S.card)
    (hN : Fintype.card V ≤ 2 ^ M) (hsmall : β ^ r * Fintype.card V ≤ R)
    (hs : 0 < s) (hrs : M * r ≤ s) (hR : 6 * R ≤ (d + 1) * s)
    (hm : (m + 1) * (d + 1) ≤ Fintype.card V) (hk : r + s ≤ k) :
    m < SimpleGraph.classicalRamsey 4 k := by
  classical
  have hV : Nonempty V := Fintype.card_pos_iff.mp
    ((Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)).trans_le hm)
  have hex (S : Finset V) (hS : S.Nonempty) :
      ∃ v ∈ S, R < S.card → ((mvDelete G S v).card : ℝ) ≤ β * S.card := by
    by_cases h : R < S.card
    · obtain ⟨v, hv, hb⟩ := hdeg S h
      exact ⟨v, hv, fun _ => hb⟩
    · obtain ⟨v, hv⟩ := hS
      exact ⟨v, hv, fun hp => (h hp).elim⟩
  let pick (S : Finset V) : V := if h : S.Nonempty then (hex S h).choose else hV.some
  have hp (S : Finset V) (hS : S.Nonempty) :
      pick S ∈ S ∧ (R < S.card → ((mvDelete G S (pick S)).card : ℝ) ≤ β * S.card) := by
    simpa [pick, hS] using (hex S hS).choose_spec
  have hcount := mv_card_independents_le G pick R β hβ hβ'
    (fun S hS => (hp S hS).1)
    (fun S hS => (hp S (Finset.card_pos.mp (Nat.zero_lt_of_lt hS))).2 hS)
    Finset.univ r (r + s) (Nat.le_add_right _ _) (by simpa using hsmall)
  rw [Nat.add_sub_cancel_left] at hcount
  have hsample : (mvIndependents G Finset.univ (r + s)).card ≤ (d + 1) ^ (r + s) := by
    calc
      _ ≤ Fintype.card V ^ r * R.choose s := hcount
      _ ≤ (2 ^ M) ^ r * R.choose s := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN _)
      _ = 2 ^ (M * r) * R.choose s := by rw [pow_mul]
      _ ≤ 2 ^ s * R.choose s := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hrs)
      _ ≤ (d + 1) ^ s := mv_choose_mul_pow_le R s (d + 1) hs hR
      _ ≤ _ := Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _)
  have ht : 0 < r + s := by omega
  obtain ⟨S, hSm, hSi⟩ := mv_sample_of_count_le G d (r + s) m ht hsample hm
  exact hSm.trans_lt (mv_ramsey_of_sample G hG S ht hk hSi)

end Estimates

theorem mv_bound_of_dyadic (L : ℕ) (hL : 0 < L)
    (h : ∀ᶠ j : ℕ in atTop, ∀ k : ℕ, L * 2 ^ j * j ^ 2 ≤ k →
      ((2 : ℝ) ^ j) ^ 3 * (j : ℝ) ^ 2 / 16 ≤ (SimpleGraph.classicalRamsey 4 k : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      (SimpleGraph.classicalRamsey 4 k : ℝ) ≥ C * (k : ℝ) ^ 3 / (Real.log k) ^ 4 := by
  classical
  obtain ⟨J, hJ⟩ := eventually_atTop.mp h
  let j₀ := max 1 J
  let T (j : ℕ) := L * 2 ^ j * j ^ 2
  let C := (Real.log 2) ^ 4 / (16 * (8 * (L : ℝ)) ^ 3)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
  have hC : 0 < C := by dsimp [C]; positivity
  have hjT (j : ℕ) : j ≤ T j := by
    calc
      j = 1 * j := (one_mul _).symm
      _ ≤ (L * 2 ^ j) * j ^ 2 := by
        apply Nat.mul_le_mul (Nat.mul_pos hL (by positivity))
        rw [pow_two]
        exact Nat.le_mul_self j
  refine ⟨C, hC, eventually_atTop.mpr ⟨T j₀, ?_⟩⟩
  intro k hk
  let j := Nat.findGreatest (fun i : ℕ => T i ≤ k) k
  have hj₀ : j₀ ≤ j := Nat.le_findGreatest ((hjT j₀).trans hk) hk
  have hj₁ : 1 ≤ j := (le_max_left _ _).trans hj₀
  have hjJ : J ≤ j := (le_max_right _ _).trans hj₀
  have hjk : T j ≤ k := Nat.findGreatest_spec (P := fun i : ℕ => T i ≤ k) ((hjT j₀).trans hk) hk
  have hnext : k < T (j + 1) := by
    apply lt_of_not_ge
    intro h'
    have hh : j + 1 ≤ j := Nat.le_findGreatest ((hjT _).trans h') h'
    omega
  have hj : 0 < (j : ℝ) := by exact_mod_cast hj₁
  have hqn : 2 ^ j ≤ T j := by
    calc
      2 ^ j = (1 * 2 ^ j) * 1 := by simp
      _ ≤ T j := Nat.mul_le_mul (Nat.mul_le_mul_right _ hL) (Nat.pow_pos hj₁)
  have hqk : (2 : ℝ) ^ j ≤ k := by exact_mod_cast hqn.trans hjk
  have hlogk : (j : ℝ) * Real.log 2 ≤ Real.log k := by
    have hh := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ j) hqk
    rwa [Real.log_pow] at hh
  have hnext' : (k : ℝ) ≤ (L : ℝ) * (2 : ℝ) ^ (j + 1) * ((j : ℝ) + 1) ^ 2 := by
    have hh : (k : ℝ) ≤ (T (j + 1) : ℝ) := by exact_mod_cast hnext.le
    simpa [T] using hh
  have hk' : (k : ℝ) ≤ 8 * (L : ℝ) * (2 : ℝ) ^ j * (j : ℝ) ^ 2 := by
    refine hnext'.trans ?_
    calc
      _ ≤ (L : ℝ) * (2 : ℝ) ^ (j + 1) * (2 * (j : ℝ)) ^ 2 := by
        have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj₁
        gcongr <;> linarith
      _ = _ := by rw [pow_succ (2 : ℝ) j]; ring
  have hp : 0 < (j : ℝ) * Real.log 2 := by positivity
  calc
    _ ≤ C * (8 * (L : ℝ) * (2 : ℝ) ^ j * (j : ℝ) ^ 2) ^ 3 /
        ((j : ℝ) * Real.log 2) ^ 4 := by gcongr
    _ = ((2 : ℝ) ^ j) ^ 3 * (j : ℝ) ^ 2 / 16 := by
      dsimp [C]
      field_simp [ne_of_gt hL', ne_of_gt hj, ne_of_gt hlog2]
      <;> ring
    _ ≤ _ := hJ j hjJ k hjk

section SplitGraph

/-- Split each block of an incidence relation into two parts and keep the crossing pairs. -/
def mvSplitGraph {P V : Type*} (on : P → V → Prop) (side : P → V → Bool) : SimpleGraph V where
  Adj u v := ∃ p, on p u ∧ on p v ∧ side p u ≠ side p v
  symm := ⟨by
    rintro u v ⟨p, hu, hv, h⟩
    exact ⟨p, hv, hu, h.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨_, _, _, h⟩
    exact h rfl⟩

theorem mv_split_graph_k4_free {P V : Type*} (on : P → V → Prop) (side : P → V → Bool)
    (hlinear : ∀ p q u v, u ≠ v → on p u → on p v → on q u → on q v → p = q)
    (htriple : ∀ f : Fin 4 ↪ V,
      (∀ i j, i ≠ j → ∃ p, on p (f i) ∧ on p (f j)) →
      ∃ p i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ on p (f i) ∧ on p (f j) ∧ on p (f k)) :
    ¬ (SimpleGraph.completeGraph (Fin 4)).IsContained (mvSplitGraph on side) := by
  intro h
  let f := h.some.toEmbedding
  have hpair (i j : Fin 4) (hij : i ≠ j) :
      ∃ p, on p (f i) ∧ on p (f j) ∧ side p (f i) ≠ side p (f j) :=
    h.some.toHom.map_adj hij
  obtain ⟨p, i, j, k, hij, hik, hjk, hi, hj, hk⟩ :=
    htriple f fun i j e => by
      obtain ⟨p, hp, hq, _⟩ := hpair i j e
      exact ⟨p, hp, hq⟩
  have hs (u v : Fin 4) (hne : u ≠ v) (hu : on p (f u)) (hv : on p (f v)) :
      side p (f u) ≠ side p (f v) := by
    obtain ⟨q, hqu, hqv, hn⟩ := hpair u v hne
    have e := hlinear q p _ _ (fun e => hne (f.injective e)) hqu hqv hu hv
    exact e ▸ hn
  have h₁ := hs i j hij hi hj
  have h₂ := hs i k hik hi hk
  have h₃ := hs j k hjk hj hk
  exact (by decide : ∀ a b c : Bool, a ≠ b → a ≠ c → b ≠ c → False) _ _ _ h₁ h₂ h₃

end SplitGraph

section BalancedSplits

variable {P V : Type*} [Fintype V]

/-- Vertices on a prescribed side of a split block. -/
noncomputable def mvBlockSide (on : P → V → Prop) (side : P → V → Bool)
    (p : P) (b : Bool) : Finset V := by
  classical
  exact Finset.univ.filter fun v => on p v ∧ side p v = b

theorem mv_split_pair_count (on : P → V → Prop) (side : P → V → Bool)
    (B : Finset P) [DecidableRel (mvSplitGraph on side).Adj]
    (hlinear : ∀ p q u v, u ≠ v → on p u → on p v → on q u → on q v → p = q) :
    ∑ p : ↥B, (mvBlockSide on side p false).card * (mvBlockSide on side p true).card ≤
      2 * (mvSplitGraph on side).edgeFinset.card := by
  classical
  let G := mvSplitGraph on side
  let X (p : ↥B) := mvBlockSide on side (p : P) false
  let Y (p : ↥B) := mvBlockSide on side (p : P) true
  have hX (p : ↥B) (u : X p) : on p u ∧ side p u = false := (Finset.mem_filter.mp u.2).2
  have hY (p : ↥B) (v : Y p) : on p v ∧ side p v = true := (Finset.mem_filter.mp v.2).2
  let f : (Σ p : ↥B, ↥(X p) × ↥(Y p)) → G.Dart :=
    fun ⟨p, u, v⟩ => ⟨⟨u, v⟩, ⟨p, (hX p u).1, (hY p v).1,
      by rw [(hX p u).2, (hY p v).2]; decide⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨p, u, v⟩ ⟨q, x, y⟩ h
    have hu : (u : V) = x := congrArg (fun d : G.Dart => d.fst) h
    have hv : (v : V) = y := congrArg (fun d : G.Dart => d.snd) h
    have hn : (u : V) ≠ v := (f ⟨p, u, v⟩).fst_ne_snd
    have hpq : (p : P) = q := hlinear p q u v hn (hX p u).1 (hY p v).1
      (hu ▸ (hX q x).1) (hv ▸ (hY q y).1)
    have hh : p = q := Subtype.ext hpq
    subst q
    have hux : u = x := Subtype.ext hu
    have hvy : v = y := Subtype.ext hv
    subst x
    subst y
    rfl
  have hc := Fintype.card_le_of_injective f hf
  rw [G.dart_card_eq_twice_card_edges] at hc
  simpa [G, X, Y] using hc

theorem mv_density_of_balanced_stars (on : P → V → Prop) (side : P → V → Bool)
    (B : Finset P) [DecidableRel (mvSplitGraph on side).Adj]
    (hlinear : ∀ p q u v, u ≠ v → on p u → on p v → on q u → on q v → p = q)
    (q : ℝ) (hq : 0 < q) (hB : (B.card : ℝ) ≤ 2 * q ^ 3)
    (hbalanced : ∀ p : ↥B, let a := ((mvBlockSide on side p false).card : ℝ)
      let b := ((mvBlockSide on side p true).card : ℝ)
      a + b ≤ 4 * a ∧ a + b ≤ 4 * b)
    (hmass : q * Fintype.card V ≤ 2 * ∑ p : ↥B,
      (((mvBlockSide on side p false).card : ℝ) + (mvBlockSide on side p true).card)) :
    (Fintype.card V : ℝ) ^ 2 ≤ 256 * q * ((mvSplitGraph on side).edgeFinset.card : ℝ) := by
  classical
  let a (p : ↥B) := ((mvBlockSide on side p false).card : ℝ)
  let b (p : ↥B) := ((mvBlockSide on side p true).card : ℝ)
  let e := ((mvSplitGraph on side).edgeFinset.card : ℝ)
  let W := ∑ p : ↥B, (a p + b p)
  have hpair : (∑ p : ↥B, a p * b p) ≤ 2 * e := by
    dsimp [a, b, e]
    exact_mod_cast mv_split_pair_count on side B hlinear
  have hsq : W ^ 2 ≤ (B.card : ℝ) * ∑ p : ↥B, (a p + b p) ^ 2 := by
    simpa [W] using Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset ↥B) (fun _ => (1 : ℝ)) (fun p => a p + b p)
  have hb : (∑ p : ↥B, (a p + b p) ^ 2) ≤ 16 * ∑ p : ↥B, a p * b p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    obtain ⟨ha, hb⟩ := hbalanced p
    nlinarith [mul_le_mul ha hb (by positivity : 0 ≤ a p + b p) (by positivity : 0 ≤ 4 * a p)]
  have hsq' : W ^ 2 ≤ (B.card : ℝ) * (16 * (2 * e)) := by
    refine hsq.trans (mul_le_mul_of_nonneg_left (hb.trans ?_) (by positivity))
    exact mul_le_mul_of_nonneg_left hpair (by norm_num)
  have hh : q ^ 2 * (Fintype.card V : ℝ) ^ 2 ≤ q ^ 2 * (256 * q * e) := by
    calc
      _ = (q * Fintype.card V) ^ 2 := by ring
      _ ≤ (2 * W) ^ 2 := pow_le_pow_left₀ (by positivity) hmass _
      _ = 4 * W ^ 2 := by ring
      _ ≤ 4 * ((B.card : ℝ) * (16 * (2 * e))) :=
        mul_le_mul_of_nonneg_left hsq' (by norm_num)
      _ ≤ 4 * ((2 * q ^ 3) * (16 * (2 * e))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB (by positivity)) (by norm_num)
      _ = _ := by ring
  exact le_of_mul_le_mul_left hh (by positivity)

end BalancedSplits

section Density

theorem mv_pivot_of_edge_density {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hS : S.Nonempty)
    (C : ℝ) (hC : 0 < C)
    (hedges : (S.card : ℝ) ^ 2 ≤ 2 * C * ((G.induce (S : Set V)).edgeFinset.card : ℝ)) :
    ∃ v ∈ S, ((mvDelete G S v).card : ℝ) ≤ (1 - 1 / C) * S.card := by
  classical
  let H := G.induce (S : Set V)
  have huniv : (Finset.univ : Finset ↥(S : Set V)).Nonempty := by
    obtain ⟨v, hv⟩ := hS
    exact ⟨⟨v, hv⟩, Finset.mem_univ _⟩
  have hsum : ∑ v : ↥(S : Set V), (H.degree v : ℝ) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  have hdeg : ∃ v : ↥(S : Set V), (S.card : ℝ) / C ≤ H.degree v := by
    by_contra! h
    have hs := Finset.sum_lt_sum_of_nonempty huniv
      (fun v (_ : v ∈ Finset.univ) => h v)
    rw [hsum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hs
    change (S.card : ℝ) ^ 2 ≤ 2 * C * (H.edgeFinset.card : ℝ) at hedges
    have hcard : Fintype.card ↥(S : Set V) = S.card := Fintype.card_coe S
    rw [hcard, ← mul_div_assoc, ← pow_two, lt_div_iff₀ hC] at hs
    nlinarith
  obtain ⟨v, hv⟩ := hdeg
  refine ⟨v, v.2, ?_⟩
  let near := S.filter (G.Adj (v : V))
  let far := S.filter (fun w => ¬ G.Adj (v : V) w)
  have hpart : (near.card : ℝ) + far.card = S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S) (G.Adj (v : V))
  have hnear : H.degree v = near.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_map (f := Function.Embedding.subtype
      (fun w : V => w ∈ (S : Set V)))]
    congr 1
    ext w
    constructor
    · intro hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
      exact Finset.mem_filter.mpr ⟨u.2, (H.mem_neighborFinset v u).mp hu⟩
    · intro hw
      obtain ⟨hwS, hwa⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_map.mpr ⟨⟨w, hwS⟩, (H.mem_neighborFinset v ⟨w, hwS⟩).mpr hwa, rfl⟩
  have hfar : (mvDelete G S v).card ≤ far.card := by
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwS, _, hn⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwS, hn⟩
  rw [hnear] at hv
  have hfar' : ((mvDelete G S v).card : ℝ) ≤ far.card := by exact_mod_cast hfar
  rw [show (1 - 1 / C) * (S.card : ℝ) = S.card - (S.card : ℝ) / C by
    simp only [div_eq_mul_inv]; ring]
  linarith

end Density

/-- The six isotropic points of a quadrilateral force a singular form in normalized coordinates. -/
theorem mv_quadrilateral_det_zero {F : Type*} [Field F] (σ : F →+* F)
    (M : Matrix (Fin 3) (Fin 3) F) (w : Fin 3 → F) (hw : ∀ i, w i ≠ 0)
    (hdiag : ∀ i, M i i = 0)
    (hpair : ∀ i j, i ≠ j →
      σ (w i) * M i j * w j + σ (w j) * M j i * w i = 0) :
    M.det = 0 := by
  let D₁ := Matrix.diagonal (fun i => σ (w i))
  let D₂ := Matrix.diagonal w
  let B := D₁ * M * D₂
  have hentry (i j : Fin 3) : B i j = σ (w i) * M i j * w j := by
    simp [B, D₁, D₂, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hBdiag (i : Fin 3) : B i i = 0 := by simp [hentry, hdiag]
  have hBpair (i j : Fin 3) (hij : i ≠ j) : B j i = - B i j := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [hentry] using hpair j i hij.symm
  have hB : B.det = 0 := by
    rw [Matrix.det_fin_three, hBdiag 0, hBdiag 1, hBdiag 2,
      hBpair 0 1 (by decide), hBpair 0 2 (by decide), hBpair 1 2 (by decide)]
    ring
  have hD₁ : D₁.det ≠ 0 := by
    dsimp [D₁]
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero σ).mpr (hw i)
  have hD₂ : D₂.det ≠ 0 := by
    dsimp [D₂]
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hw i
  dsimp [B] at hB
  rw [Matrix.det_mul, Matrix.det_mul] at hB
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hB).resolve_right hD₂)).resolve_left hD₁

/-- The finite host graph needed for the sampling argument at the dyadic scale. -/
noncomputable def mvHost (A D j : ℕ) : Prop := by
  classical
  let q : ℕ := 2 ^ j
  exact ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
    q ^ 4 ≤ 2 * n ∧ n ≤ q ^ 4 ∧
    ¬ (SimpleGraph.completeGraph (Fin 4)).IsContained G ∧
    ∀ S : Finset (Fin n), D * q ^ 2 < S.card →
      ∃ v ∈ S, ((mvDelete G S v).card : ℝ) ≤
        (1 - 1 / ((A : ℝ) * q)) * S.card

private theorem mv_square_le_pow_two (j : ℕ) (hj : 4 ≤ j) : j ^ 2 ≤ 2 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : 4 ≤ j
    · have hstep : (j + 1) ^ 2 ≤ 2 * j ^ 2 := by
        have h' : (4 : ℤ) ≤ (j : ℤ) := by exact_mod_cast h
        have h'' : ((j : ℤ) + 1) ^ 2 ≤ 2 * (j : ℤ) ^ 2 := by
          nlinarith [mul_nonneg (by omega : (j : ℤ) - 4 ≥ 0) (by omega : (j : ℤ) + 2 ≥ 0)]
        exact_mod_cast h''
      rw [pow_succ' (2 : ℕ) j]
      exact hstep.trans (Nat.mul_le_mul_left _ (ih h))
    · have hj' : j = 3 := by omega
      subst j
      decide

theorem mv_bound_from_hosts (A D : ℕ) (hA : 0 < A) (hD : 0 < D)
    (h : ∀ᶠ j : ℕ in atTop, mvHost A D j) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      (SimpleGraph.classicalRamsey 4 k : ℝ) ≥ C * (k : ℝ) ^ 3 / (Real.log k) ^ 4 := by
  classical
  let K := 16 * A + 6 * D
  let L := 4 * A + K
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  apply mv_bound_of_dyadic L hL
  filter_upwards [h, eventually_ge_atTop (4 : ℕ)] with j hj hj4
  intro k hk
  let q : ℕ := 2 ^ j
  let r := 4 * A * q * j
  let s := K * q * j ^ 2
  let d := q / j ^ 2
  let m := (q ^ 3 / 8) * j ^ 2
  let β : ℝ := 1 - 1 / ((A : ℝ) * q)
  obtain ⟨n, G, hn, hn', hG, hdeg⟩ := hj
  change q ^ 4 ≤ 2 * n at hn
  change n ≤ q ^ 4 at hn'
  have hj0 : 0 < j := by omega
  have hjsq : 0 < j ^ 2 := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hqj : j ^ 2 ≤ q := mv_square_le_pow_two j hj4
  have hq8 : 8 ≤ q ^ 3 := by
    have h2q : 2 ≤ q := by
      exact (show 2 ^ (1 : ℕ) ≤ 2 ^ j from Nat.pow_le_pow_right (by decide) hj0)
    exact Nat.pow_le_pow_left h2q 3
  have hAq : (1 : ℝ) ≤ (A : ℝ) * q := by
    exact_mod_cast Nat.mul_pos hA hq
  have hAqpos : 0 < (A : ℝ) * q := by linarith
  have hβ : 0 ≤ β := sub_nonneg.mpr ((div_le_iff₀ hAqpos).mpr (by simpa using hAq))
  have hβ' : β ≤ 1 := sub_le_self _ (by positivity)
  have hsmall : β ^ r * (n : ℝ) ≤ (D * q ^ 2 : ℕ) := by
    have hb : β ^ r ≤ Real.exp (-(4 * (j : ℝ))) := by
      calc
        _ ≤ Real.exp (-(1 / ((A : ℝ) * q))) ^ r :=
          pow_le_pow_left₀ hβ (Real.one_sub_le_exp_neg _) _
        _ = _ := by
          rw [← Real.exp_nat_mul]
          congr 1
          dsimp [r]
          push_cast
          field_simp
          <;> ring
    have hqe : (q : ℝ) ≤ Real.exp (j : ℝ) := by
      calc
        _ = (2 : ℝ) ^ j := by simp [q]
        _ ≤ Real.exp 1 ^ j := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
        _ = _ := by rw [← Real.exp_nat_mul, mul_one]
    have hne : (n : ℝ) ≤ Real.exp (4 * (j : ℝ)) := by
      calc
        _ ≤ (q : ℝ) ^ 4 := by exact_mod_cast hn'
        _ ≤ Real.exp (j : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hqe _
        _ = _ := by rw [← Real.exp_nat_mul]; norm_num
    calc
      _ ≤ Real.exp (-(4 * (j : ℝ))) * Real.exp (4 * (j : ℝ)) :=
        mul_le_mul hb hne (by positivity) (by positivity)
      _ = 1 := by rw [← Real.exp_add]; simp
      _ ≤ _ := by exact_mod_cast Nat.mul_pos hD (pow_pos hq 2)
  have hN : n ≤ 2 ^ (4 * j) := by
    simpa only [q, ← pow_mul, Nat.mul_comm j 4] using hn'
  have hrs : (4 * j) * r ≤ s := by
    calc
      _ = (16 * A) * q * j ^ 2 := by dsimp [r]; ring
      _ ≤ s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  have hd : q ≤ (d + 1) * j ^ 2 := by
    simpa [d, Nat.mul_comm] using (Nat.lt_mul_div_succ q hjsq).le
  have hR : 6 * (D * q ^ 2) ≤ (d + 1) * s := by
    calc
      _ = (6 * D * q) * q := by ring
      _ ≤ (K * q) * ((d + 1) * j ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)) hd
      _ = _ := by dsimp [s]; ring
  have hdiv : q ^ 3 / 8 > 0 := (Nat.le_div_iff_mul_le (by decide)).mpr (by simpa using hq8)
  have hm0 : 0 < m := Nat.mul_pos hdiv hjsq
  have hdu : (d + 1) * j ^ 2 ≤ 2 * q := by
    rw [Nat.add_mul, Nat.one_mul]
    exact (Nat.add_le_add (Nat.div_mul_le_self _ _) hqj).trans_eq (by ring)
  have hm : (m + 1) * (d + 1) ≤ n := by
    have hm' : m + 1 ≤ 2 * m := by omega
    have hnd : (q ^ 3 / 8) * 8 ≤ q ^ 3 := Nat.div_mul_le_self _ _
    have hh : 2 * ((m + 1) * (d + 1)) ≤ q ^ 4 := by
      calc
        _ ≤ 2 * ((2 * m) * (d + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm')
        _ = 4 * (q ^ 3 / 8) * ((d + 1) * j ^ 2) := by dsimp [m]; ring
        _ ≤ 4 * (q ^ 3 / 8) * (2 * q) := Nat.mul_le_mul_left _ hdu
        _ = ((q ^ 3 / 8) * 8) * q := by ring
        _ ≤ q ^ 3 * q := Nat.mul_le_mul_right _ hnd
        _ = _ := by ring
    omega
  have hk' : r + s ≤ k := by
    apply le_trans _ hk
    have hjj : j ≤ j ^ 2 := by rw [pow_two]; exact Nat.le_mul_self _
    calc
      _ ≤ 4 * A * q * j ^ 2 + K * q * j ^ 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hjj) _
      _ = L * 2 ^ j * j ^ 2 := by dsimp [L, q]; ring
  have hRam : m < SimpleGraph.classicalRamsey 4 k :=
    mv_ramsey_of_dense_graph G hG (D * q ^ 2) (4 * j) r s d m k β hβ hβ' hdeg
      (by simpa using hN) (by simpa using hsmall)
      (Nat.mul_pos (Nat.mul_pos hK hq) hjsq) hrs hR (by simpa using hm) hk'
  have hmu : q ^ 3 * j ^ 2 ≤ 16 * m := by
    have hqd : q ^ 3 ≤ 16 * (q ^ 3 / 8) := by omega
    exact (Nat.mul_le_mul_right _ hqd).trans_eq (by dsimp [m]; ring)
  have hmu' : ((q : ℝ) ^ 3 * (j : ℝ) ^ 2) ≤ 16 * (m : ℝ) := by exact_mod_cast hmu
  have hmr : ((q : ℝ) ^ 3 * (j : ℝ) ^ 2) / 16 ≤ m :=
    (div_le_iff₀ (by norm_num : 0 < (16 : ℝ))).mpr (by linarith)
  exact (by simpa [q] using hmr : ((2 : ℝ) ^ j) ^ 3 * (j : ℝ) ^ 2 / 16 ≤ (m : ℝ)).trans
    (by exact_mod_cast hRam.le)


/-- Count the subsets putting at most a quarter of the vertices on one side. -/
theorem mv_small_side_count {V : Type*} (S : Finset V) :
    (((S.powerset.filter fun T => 4 * T.card ≤ S.card).card : ℝ)) ≤
      ((9 : ℝ) / 5) ^ S.card := by
  classical
  let b : ℝ := 4 / 5
  let U := S.powerset.filter fun T => 4 * T.card ≤ S.card
  have hb : 0 < b := by norm_num [b]
  have hU : (U.card : ℝ) * b ^ S.card ≤ (1 + b ^ 4) ^ S.card := by
    calc
      _ = ∑ _T ∈ U, b ^ S.card := by simp
      _ ≤ ∑ T ∈ U, b ^ (4 * T.card) := by
        apply Finset.sum_le_sum
        intro T hT
        exact pow_le_pow_of_le_one hb.le (by norm_num [b]) (Finset.mem_filter.mp hT).2
      _ ≤ ∑ T ∈ S.powerset, b ^ (4 * T.card) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
      _ = _ := by
        simp only [pow_mul, Finset.sum_powerset_apply_card, nsmul_eq_mul]
        rw [add_comm (1 : ℝ) (b ^ 4), add_pow]
        simp [mul_comm]
  have hpow : (1 + b ^ 4) ^ S.card ≤ (((9 : ℝ) / 5) * b) ^ S.card :=
    pow_le_pow_left₀ (by positivity) (by norm_num [b]) _
  rw [mul_pow] at hpow
  exact le_of_mul_le_mul_right (hU.trans hpow) (pow_pos hb _)

theorem mv_unbalanced_split_count {V : Type*} [DecidableEq V] (S : Finset V) :
    ((S.powerset.filter fun T => 4 * T.card ≤ S.card ∨ 4 * (S \ T).card ≤ S.card).card : ℝ)
      ≤ 2 * ((9 : ℝ) / 5) ^ S.card := by
  classical
  let U := S.powerset.filter fun T => 4 * T.card ≤ S.card
  let W := S.powerset.filter fun T => 4 * (S \ T).card ≤ S.card
  have hWU : W.card ≤ U.card := by
    apply Finset.card_le_card_of_injOn (fun T => S \ T)
    · intro T hT
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset,
        (Finset.mem_filter.mp hT).2⟩
    · intro T hT R hR h
      have hTS := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hRS := Finset.mem_powerset.mp (Finset.mem_filter.mp hR).1
      have hh := congrArg (fun Q => S \ Q) h
      simpa only [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hTS,
        Finset.inter_eq_right.mpr hRS] using hh
  rw [Finset.filter_or]
  change ((U ∪ W).card : ℝ) ≤ _
  have hu := mv_small_side_count S
  change (U.card : ℝ) ≤ _ at hu
  have h₁ : ((U ∪ W).card : ℝ) ≤ (U.card : ℝ) + W.card := by
    exact_mod_cast Finset.card_union_le U W
  have h₂ : (W.card : ℝ) ≤ U.card := by exact_mod_cast hWU
  linarith

/-- A counting bound obtained from a product of nonnegative weights on independent choices. -/
theorem mv_product_weight_count {P : Type*} [DecidableEq P] [Fintype P] {X : P → Type*} [∀ p, Fintype (X p)]
    (W : Finset (∀ p, X p)) (score : ∀ p, X p → ℝ) (threshold C : ℝ)
    (hscore : ∀ p x, 0 ≤ score p x)
    (havg : ∀ p, ∑ x : X p, score p x ≤ C * Fintype.card (X p))
    (hW : ∀ f ∈ W, threshold ≤ ∏ p, score p (f p)) :
    (W.card : ℝ) * threshold ≤ C ^ Fintype.card P * Fintype.card (∀ p, X p) := by
  classical
  calc
    _ = ∑ _f ∈ W, threshold := by simp
    _ ≤ ∑ f ∈ W, ∏ p, score p (f p) := Finset.sum_le_sum hW
    _ ≤ ∑ f : ∀ p, X p, ∏ p, score p (f p) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun f _ _ => Finset.prod_nonneg fun p _ => hscore p (f p))
    _ = ∏ p, ∑ x : X p, score p x := (Fintype.prod_sum score).symm
    _ ≤ ∏ p, C * Fintype.card (X p) :=
      Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun x _ => hscore p x)
        (fun p _ => havg p)
    _ = _ := by simp [Finset.prod_mul_distrib, Fintype.card_pi]

theorem mv_split_weight_sum {V : Type*} [DecidableEq V] (S : Finset V) :
    (∑ T ∈ S.powerset, if 4 * T.card ≤ S.card ∨ 4 * (S \ T).card ≤ S.card
      then ((10 : ℝ) / 9) ^ S.card else 1) ≤ 3 * (2 : ℝ) ^ S.card := by
  classical
  let bad (T : Finset V) := 4 * T.card ≤ S.card ∨ 4 * (S \ T).card ≤ S.card
  let w := ((10 : ℝ) / 9) ^ S.card
  have hcount := mv_unbalanced_split_count S
  change (((S.powerset.filter bad).card : ℝ)) ≤ _ at hcount
  have hmul : ((S.powerset.filter bad).card : ℝ) * w ≤ 2 * (2 : ℝ) ^ S.card := by
    calc
      _ ≤ (2 * ((9 : ℝ) / 5) ^ S.card) * w := mul_le_mul_of_nonneg_right hcount (by dsimp [w]; positivity)
      _ = _ := by dsimp [w]; rw [mul_assoc, ← mul_pow]; norm_num
  change (∑ T ∈ S.powerset, if bad T then w else 1) ≤ _
  calc
    _ ≤ ∑ T ∈ S.powerset, (1 + if bad T then w else 0) := by
      apply Finset.sum_le_sum
      intro T _
      split_ifs <;> linarith
    _ = (2 : ℝ) ^ S.card + ((S.powerset.filter bad).card : ℝ) * w := by
      rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero]
      simp [Finset.card_powerset, nsmul_eq_mul]
    _ ≤ _ := by linarith

/-- A split restricted to a vertex set can be extended independently on its complement. -/
def mv_split_restrict_equiv {V : Type*} [DecidableEq V] {S T : Finset V} (hTS : T ⊆ S) :
    ↥S.powerset ≃ ↥T.powerset × ↥(S \ T).powerset where
  toFun U :=
    (⟨U.1 ∩ T, Finset.mem_powerset.mpr Finset.inter_subset_right⟩,
      ⟨U.1 \ T, Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff_left T (Finset.mem_powerset.mp U.2))⟩)
  invFun U := ⟨U.1.1 ∪ U.2.1, Finset.mem_powerset.mpr
    (Finset.union_subset ((Finset.mem_powerset.mp U.1.2).trans hTS)
      ((Finset.mem_powerset.mp U.2.2).trans Finset.sdiff_subset))⟩
  left_inv U := by
    apply Subtype.ext
    ext v
    change v ∈ (U.1 ∩ T) ∪ (U.1 \ T) ↔ v ∈ U.1
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  right_inv := by
    rintro ⟨U, W⟩
    have hUT := Finset.mem_powerset.mp U.2
    have hWT := Finset.mem_powerset.mp W.2
    apply Prod.ext <;> apply Subtype.ext <;> ext v
    · change v ∈ (U.1 ∪ W.1) ∩ T ↔ v ∈ U.1
      simp only [Finset.mem_inter, Finset.mem_union]
      have h (hv : v ∈ W.1) := (Finset.mem_sdiff.mp (hWT hv)).2
      aesop
    · change v ∈ (U.1 ∪ W.1) \ T ↔ v ∈ W.1
      simp only [Finset.mem_sdiff, Finset.mem_union]
      have h (hv : v ∈ W.1) := (Finset.mem_sdiff.mp (hWT hv)).2
      have h' (hv : v ∈ U.1) : v ∈ T := hUT hv
      tauto

/-- The total block size over blocks with a side of size at most one quarter. -/
def mvBadMass {P V : Type*} [Fintype P] [DecidableEq V]
    (S : P → Finset V) (f : ∀ p, ↥((S p).powerset)) : ℕ :=
  ∑ p, if 4 * (f p).val.card ≤ (S p).card ∨ 4 * (S p \ (f p).val).card ≤ (S p).card
    then (S p).card else 0

theorem mv_split_bad_mass_count {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (S : P → Finset V) (r : ℕ) :
    let F := ∀ p, ↥((S p).powerset)
    (((Finset.univ : Finset F).filter (fun f => r ≤ mvBadMass S f)).card : ℝ) *
      ((10 : ℝ) / 9) ^ r ≤ 3 ^ Fintype.card P * Fintype.card F := by
  classical
  let mass (p : P) (T : Finset V) : ℕ :=
    if 4 * T.card ≤ (S p).card ∨ 4 * (S p \ T).card ≤ (S p).card then (S p).card else 0
  let score (p : P) (T : ↥((S p).powerset)) := ((10 : ℝ) / 9) ^ (mass p T)
  apply mv_product_weight_count _ score _ 3
  · intro p T
    dsimp [score]
    positivity
  · intro p
    rw [Fintype.card_coe, Finset.card_powerset]
    push_cast
    change (∑ T : ↥((S p).powerset), ((10 : ℝ) / 9) ^ mass p T) ≤ _
    rw [Finset.sum_coe_sort ((S p).powerset) (fun T => ((10 : ℝ) / 9) ^ mass p T)]
    simpa only [mass, apply_ite, pow_zero] using mv_split_weight_sum (S p)
  · intro f hf
    have h := (Finset.mem_filter.mp hf).2
    change r ≤ ∑ p, mass p (f p) at h
    simp only [score, Finset.prod_pow_eq_pow_sum]
    exact pow_le_pow_right₀ (by norm_num) h

/-- An incidence structure with a two-coloring of each point star. Any four pairwise
intersecting secants have a concurrent triple. For each large set of secants, balanced
stars account for at least half of the required incidence mass. -/
noncomputable def mvIncidenceHost (D j : ℕ) : Prop := by
  classical
  let q : ℕ := 2 ^ j
  exact ∃ n p : ℕ, ∃ on : Fin p → Fin n → Prop,
    q ^ 4 ≤ 2 * n ∧ n ≤ q ^ 4 ∧ p ≤ 2 * q ^ 3 ∧
    (∀ a b u v, u ≠ v → on a u → on a v → on b u → on b v → a = b) ∧
    (∀ f : Fin 4 ↪ Fin n,
      (∀ i j, i ≠ j → ∃ a, on a (f i) ∧ on a (f j)) →
      ∃ a i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ on a (f i) ∧ on a (f j) ∧ on a (f k)) ∧
    ∃ side : Fin p → Fin n → Bool, ∀ S : Finset (Fin n), D * q ^ 2 < S.card →
      ∃ B : Finset (Fin p),
        let left (a : Fin p) := (mvBlockSide (fun a (v : ↥(S : Set (Fin n))) => on a v)
          (fun a (v : ↥(S : Set (Fin n))) => side a v) a false).card
        let right (a : Fin p) := (mvBlockSide (fun a (v : ↥(S : Set (Fin n))) => on a v)
          (fun a (v : ↥(S : Set (Fin n))) => side a v) a true).card
        (∀ a ∈ B, left a + right a ≤ 4 * left a ∧ left a + right a ≤ 4 * right a) ∧
        q * S.card ≤ 2 * ∑ a : ↥B, (left a + right a)

theorem mv_incidence_host_construction : ∃ D : ℕ, 0 < D ∧
    ∀ᶠ j : ℕ in atTop, mvIncidenceHost D j := by
  sorry

/-- The pseudorandom K₄-free graph furnished by the Hermitian-unital construction. -/
theorem mv_host_edge_construction : ∃ A D : ℕ, 0 < A ∧ 0 < D ∧
    ∀ᶠ j : ℕ in atTop, by
      classical
      let q : ℕ := 2 ^ j
      exact ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        q ^ 4 ≤ 2 * n ∧ n ≤ q ^ 4 ∧
        ¬ (SimpleGraph.completeGraph (Fin 4)).IsContained G ∧
        ∀ S : Finset (Fin n), D * q ^ 2 < S.card →
          (S.card : ℝ) ^ 2 ≤ 2 * (A : ℝ) * q *
            ((G.induce (S : Set (Fin n))).edgeFinset.card : ℝ) := by
  classical
  obtain ⟨D, hD, h⟩ := mv_incidence_host_construction
  refine ⟨128, D, by decide, hD, h.mono fun j hj => ?_⟩
  let q : ℕ := 2 ^ j
  obtain ⟨n, p, on, hn, hn', hp, hlinear, htriple, side, hside⟩ := hj
  let G := mvSplitGraph on side
  refine ⟨n, G, hn, hn', mv_split_graph_k4_free on side hlinear htriple, ?_⟩
  intro S hS
  obtain ⟨B, hB, hmass⟩ := hside S hS
  let on' (a : Fin p) (v : ↥(S : Set (Fin n))) := on a v
  let side' (a : Fin p) (v : ↥(S : Set (Fin n))) := side a v
  have hlin (a b : Fin p) (u v : ↥(S : Set (Fin n))) (huv : u ≠ v) :
      on' a u → on' a v → on' b u → on' b v → a = b :=
    hlinear a b u v (fun h => huv (Subtype.ext h))
  have hBcard : (B.card : ℝ) ≤ 2 * (q : ℝ) ^ 3 := by
    exact_mod_cast (Finset.card_le_univ B).trans (by simpa using hp)
  have hq : (0 : ℝ) < q := by dsimp [q]; positivity
  have hcard : Fintype.card ↥(S : Set (Fin n)) = S.card := Fintype.card_coe S
  have hd := mv_density_of_balanced_stars on' side' B hlin (q : ℝ) hq hBcard
    (fun a => ⟨by exact_mod_cast (hB a a.2).1, by exact_mod_cast (hB a a.2).2⟩)
    (by
      rw [hcard]
      exact_mod_cast hmass)
  rw [hcard] at hd
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 128 = 256 by norm_num]
  exact hd

theorem mv_host_construction : ∃ A D : ℕ, 0 < A ∧ 0 < D ∧
    ∀ᶠ j : ℕ in atTop, mvHost A D j := by
  classical
  obtain ⟨A, D, hA, hD, h⟩ := mv_host_edge_construction
  refine ⟨A, D, hA, hD, h.mono fun j hj => ?_⟩
  obtain ⟨n, G, hn, hn', hK, hE⟩ := hj
  refine ⟨n, G, hn, hn', hK, fun S hS => ?_⟩
  have hC : 0 < (A : ℝ) * ((2 ^ j : ℕ) : ℝ) := by positivity
  exact mv_pivot_of_edge_density G S (Finset.card_pos.mp (Nat.zero_lt_of_lt hS)) _ hC
    (by simpa only [← mul_assoc] using hE S hS)

theorem mv_construction : ∃ C : ℝ, 0 < C ∧ ∀ᶠ (k : ℕ) in atTop,
    (SimpleGraph.classicalRamsey 4 k : ℝ) ≥ C * (k : ℝ) ^ 3 / (Real.log k) ^ 4 := by
  obtain ⟨A, D, hA, hD, h⟩ := mv_host_construction
  exact mv_bound_from_hosts A D hA hD h

end OMA

theorem OMA.solution : type_of% @Erdos166.erdos_166.variants.mattheus_verstraete := by
  exact OMA.mv_construction
