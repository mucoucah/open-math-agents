import FormalConjectures.ErdosProblems.«590»

-- Problem: Erdős Problem 590 — finite cardinal
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/590.lean:70 (declaration Erdos590.erdos_590.variants.finite_cardinal)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Cardinal Ordinal

theorem OMA.typeLT_univ_toType.{v} (α : Ordinal.{v}) :
    typeLT (Set.univ : Set α.ToType) = α := by
  conv_rhs => rw [← Ordinal.type_toType α]
  exact (OrderIso.Set.univ (α := α.ToType)).toRelIsoLT.ordinalType_congr

/-- The cases m at most 2: either a blue edge, or red is complete. -/
theorem OMA.small_m.{v} (α : Ordinal.{v}) (m : ℕ) (hm : m ≤ 2) :
    OrdinalCardinalRamsey α α m := by
  intro red blue hc
  by_cases hb : ∃ x y, blue.Adj x y
  · right
    obtain ⟨x, y, hxy⟩ := hb
    have hne : x ≠ y := hxy.ne
    interval_cases m
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{x}, by simp, by simp⟩
    · refine ⟨{x, y}, ?_, ?_⟩
      · exact (SimpleGraph.isClique_pair).mpr (fun _ => hxy)
      · simp [hne]
  · left
    refine ⟨Set.univ, ?_, OMA.typeLT_univ_toType α⟩
    intro x _ y _ hxy
    push_neg at hb
    have h := congrArg (fun G => G.Adj x y) hc.sup_eq_top
    simp only [SimpleGraph.sup_adj, SimpleGraph.top_adj] at h
    exact (h.mpr hxy).resolve_right (hb x y)

private theorem OMA.ramsey_on.{v} {V : Type v} [LinearOrder V] [WellFoundedLT V]
    {α β : Ordinal.{v}} {c : Cardinal.{v}} (h : OrdinalCardinalRamsey α β c)
    (red blue : SimpleGraph V) (hc : IsCompl red blue) (s : Set V) (hs : α ≤ typeLT s) :
    (∃ t ⊆ s, red.IsClique t ∧ typeLT t = β) ∨
      (∃ t ⊆ s, blue.IsClique t ∧ #t = c) := by
  have hs' : typeLT α.ToType ≤ typeLT s := by rwa [Ordinal.type_toType]
  obtain ⟨e⟩ := Ordinal.type_le_iff'.mp hs'
  let f : α.ToType → V := fun x => (e x).val
  have hf : StrictMono f := fun _ _ hab => e.map_rel_iff.mpr hab
  have hcompl : IsCompl (red.comap f) (blue.comap f) := by
    rw [← eq_compl_iff_isCompl]
    apply SimpleGraph.ext
    funext x y
    apply propext
    rw [SimpleGraph.compl_adj, SimpleGraph.comap_adj, SimpleGraph.comap_adj,
      hc.eq_compl, SimpleGraph.compl_adj]
    exact and_congr_left' hf.injective.ne_iff
  have himage {G : SimpleGraph V} {t : Set α.ToType} (ht : (G.comap f).IsClique t) :
      G.IsClique (f '' t) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    exact ht hx hy (fun he => hxy (congrArg f he))
  have hsub (t : Set α.ToType) : f '' t ⊆ s := by
    rintro _ ⟨x, _, rfl⟩
    exact (e x).property
  rcases h _ _ hcompl with ⟨t, ht, htype⟩ | ⟨t, ht, hcard⟩
  · left
    refine ⟨f '' t, hsub t, himage ht, ?_⟩
    rw [← ((hf.strictMonoOn t).orderIso f t).toRelIsoLT.ordinalType_congr, htype]
  · right
    exact ⟨f '' t, hsub t, himage ht, (Cardinal.mk_congr (Equiv.Set.image f t hf.injective)).symm.trans hcard⟩

/-- Without the desired cliques, the preceding Ramsey case bounds every blue neighborhood. -/
private theorem OMA.neighbor_type_lt.{v} {V : Type v} [LinearOrder V] [WellFoundedLT V]
    {α β : Ordinal.{v}} {m : ℕ} (h : OrdinalCardinalRamsey α β m)
    {red blue : SimpleGraph V} (hc : IsCompl red blue)
    (hr : ¬ ∃ t, red.IsClique t ∧ typeLT t = β)
    (hb : ¬ ∃ t, blue.IsClique t ∧ #t = ((m + 1 : ℕ) : Cardinal.{v}))
    (x : V) : typeLT (blue.neighborSet x) < α := by
  by_contra! hx
  rcases OMA.ramsey_on h red blue hc (blue.neighborSet x) hx with
    ⟨t, _, ht, heq⟩ | ⟨t, hsub, ht, heq⟩
  · exact hr ⟨t, ht, heq⟩
  · have hnot : x ∉ t := fun hxt => blue.irrefl (hsub hxt)
    refine hb ⟨insert x t, ht.insert (fun y hy _ => hsub hy), ?_⟩
    rw [Cardinal.mk_insert hnot, heq, Nat.cast_add, Nat.cast_one]

private theorem OMA.strictMono_of_type_le.{v} {A B : Type v} [LinearOrder A] [LinearOrder B]
    [WellFoundedLT A] [WellFoundedLT B] (h : typeLT A ≤ typeLT B) :
    ∃ f : A → B, StrictMono f := by
  obtain ⟨f⟩ := Ordinal.type_le_iff'.mp h
  exact ⟨f, fun _ _ hab => f.map_rel_iff.mpr hab⟩

private theorem OMA.type_range.{v} {A B : Type v} [LinearOrder A] [LinearOrder B]
    [WellFoundedLT A] [WellFoundedLT B] {f : A → B} (hf : StrictMono f) :
    typeLT (Set.range f) = typeLT A :=
  (hf.orderIso f).toRelIsoLT.ordinalType_congr.symm

private theorem OMA.lex_type.{v} (a b : Ordinal.{v}) :
    typeLT (Lex (b.ToType × a.ToType)) = a * b := by
  change type (Prod.Lex (α := b.ToType) (β := a.ToType) (· < ·) (· < ·)) = a * b
  rw [Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_toType]

private theorem OMA.ordered_blocks.{v} {V : Type v} [LinearOrder V] [WellFoundedLT V]
    (a b : Ordinal.{v}) (s : Set V) (h : a * b ≤ typeLT s) :
    ∃ S : b.ToType → Set V, (∀ i, S i ⊆ s ∧ typeLT (S i) = a) ∧
      ∀ ⦃i j⦄, i < j → ∀ ⦃x y⦄, x ∈ S i → y ∈ S j → x < y := by
  obtain ⟨f, hf⟩ := OMA.strictMono_of_type_le (by rwa [OMA.lex_type] :
    typeLT (Lex (b.ToType × a.ToType)) ≤ typeLT s)
  let g (i : b.ToType) (x : a.ToType) : V := (f (toLex (i, x))).val
  refine ⟨fun i => Set.range (g i), ?_, ?_⟩
  · intro i
    constructor
    · rintro _ ⟨x, rfl⟩
      exact (f (toLex (i, x))).property
    · have hg : StrictMono (g i) := fun _ _ hxy =>
        hf (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hxy⟩))
      rw [OMA.type_range hg, Ordinal.type_toType]
  · rintro i j hij _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact hf (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hij))

private theorem OMA.type_le_of_blocks.{v} {I V : Type v}
    [LinearOrder I] [WellFoundedLT I] [LinearOrder V] [WellFoundedLT V]
    (a : Ordinal.{v}) (s : Set V) (S : I → Set V)
    (hlarge : ∀ i, a ≤ typeLT (S i)) (hsub : ∀ i, S i ⊆ s)
    (horder : ∀ ⦃i j⦄, i < j → ∀ ⦃x y⦄, x ∈ S i → y ∈ S j → x < y) :
    a * typeLT I ≤ typeLT s := by
  have he (i : I) : ∃ f : a.ToType → S i, StrictMono f :=
    OMA.strictMono_of_type_le (by simpa only [Ordinal.type_toType] using hlarge i)
  choose f hf using he
  let g (z : Lex (I × a.ToType)) : s :=
    ⟨f (ofLex z).1 (ofLex z).2, hsub _ (f (ofLex z).1 (ofLex z).2).property⟩
  have hg : StrictMono g := by
    intro x y hxy
    rcases Prod.Lex.lt_iff.mp hxy with h | ⟨h, h'⟩
    · exact horder h (f _ _).property (f _ _).property
    · change (f (ofLex x).1 (ofLex x).2).val < (f (ofLex y).1 (ofLex y).2).val
      rw [← h]
      exact hf _ h'
  have heq : typeLT (Lex (I × a.ToType)) = a * typeLT I := by
    change type (Prod.Lex (α := I) (β := a.ToType) (· < ·) (· < ·)) = a * typeLT I
    rw [Ordinal.type_prod_lex, Ordinal.type_toType]
  rw [← heq, ← OMA.type_range hg]
  exact Ordinal.type_set_le _

private theorem OMA.omega_le_of_infinite.{v} {I : Type v} [LinearOrder I] [WellFoundedLT I]
    [Infinite I] : (ω : Ordinal.{v}) ≤ typeLT I := by
  by_contra! h
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp h
  have hcard : #I < ℵ₀ := by
    rw [← Ordinal.card_type (α := I) (· < ·), hn, Ordinal.card_nat]
    exact Cardinal.natCast_lt_aleph0
  exact Infinite.not_finite (Cardinal.lt_aleph0_iff_finite.mp hcard)

/-- A partition of a copy of omega to a finite power has a part of that order type. -/
private theorem OMA.power_le_union.{v} {V : Type v} [LinearOrder V] [WellFoundedLT V]
    (n : ℕ) (s t : Set V) (h : (ω : Ordinal.{v}) ^ (n : Ordinal.{v}) ≤ typeLT (s ∪ t : Set V)) :
    (ω : Ordinal.{v}) ^ (n : Ordinal.{v}) ≤ typeLT s ∨
      (ω : Ordinal.{v}) ^ (n : Ordinal.{v}) ≤ typeLT t := by
  induction n generalizing s t with
  | zero =>
    simp only [Nat.cast_zero, opow_zero] at h ⊢
    by_contra! hn
    have hs : typeLT s = 0 := Order.lt_one_iff.mp hn.1
    have ht : typeLT t = 0 := Order.lt_one_iff.mp hn.2
    have : IsEmpty s := Ordinal.type_eq_zero_iff_isEmpty.mp hs
    have : IsEmpty t := Ordinal.type_eq_zero_iff_isEmpty.mp ht
    have he : IsEmpty (↑(s ∪ t) : Type v) := ⟨fun x => x.property.elim
      (fun hx => isEmptyElim (⟨x.val, hx⟩ : s)) (fun hx => isEmptyElim (⟨x.val, hx⟩ : t))⟩
    rw [Ordinal.type_eq_zero_iff_isEmpty.mpr he] at h
    exact not_le.mpr zero_lt_one h
  | succ n ih =>
    simp only [Nat.cast_succ, Ordinal.opow_add_one] at h ⊢
    let a : Ordinal.{v} := ω ^ (n : Ordinal.{v})
    obtain ⟨S, hS, ho⟩ := OMA.ordered_blocks a ω (s ∪ t) h
    have hparts (i) : a ≤ typeLT (S i ∩ s : Set V) ∨ a ≤ typeLT (S i ∩ t : Set V) := by
      apply ih
      change a ≤ _
      rw [← (hS i).2]
      apply Ordinal.type_mono
      intro x hx
      exact ((hS i).1 hx).elim (fun hxs => Or.inl ⟨hx, hxs⟩) (fun hxt => Or.inr ⟨hx, hxt⟩)
    let J : Set (ω : Ordinal.{v}).ToType := {i | a ≤ typeLT (S i ∩ s : Set V)}
    have hJ : J.Infinite ∨ Jᶜ.Infinite := by
      apply Set.infinite_union.mp
      rw [Set.union_compl_self]
      apply Set.infinite_univ_iff.mpr
      rw [← Cardinal.aleph0_le_mk_iff, Cardinal.mk_toType, Ordinal.card_omega0]
    rcases hJ with hJ | hJ
    · left
      have : Infinite J := hJ.to_subtype
      refine (mul_le_mul_right (OMA.omega_le_of_infinite (I := J)) a).trans ?_
      exact OMA.type_le_of_blocks a s (fun i : J => S i.val ∩ s) (fun i => i.property)
        (fun _ _ hx => hx.2) (by intro i j hij x y hx hy; exact ho hij hx.1 hy.1)
    · right
      have : Infinite ↑Jᶜ := hJ.to_subtype
      refine (mul_le_mul_right (OMA.omega_le_of_infinite (I := ↑Jᶜ)) a).trans ?_
      exact OMA.type_le_of_blocks a t (fun i : ↑Jᶜ => S i.val ∩ t)
        (fun i => (hparts i.val).resolve_left i.property) (fun _ _ hx => hx.2)
        (by intro i j hij x y hx hy; exact ho hij hx.1 hy.1)

private theorem OMA.clique_choice.{v} {I V : Type v} [Countable I] [Nonempty I]
    (red : SimpleGraph V) (S : I → Set V)
    (h : ∀ i (t : Finset V), ∃ x ∈ S i, ∀ y ∈ t, red.Adj y x) :
    ∃ f : I → V, (∀ i, f i ∈ S i) ∧ ∀ ⦃i j⦄, i ≠ j → red.Adj (f i) (f j) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat I
  let step (n : ℕ) (prev : ∀ m < n, S (e m)) : S (e n) :=
    let t := Finset.univ.image (fun i : Fin n => (prev i.val i.isLt).val)
    ⟨(h (e n) t).choose, (h (e n) t).choose_spec.1⟩
  let f₀ (n : ℕ) : S (e n) := Nat.strongRec step n
  have hpair {m n} (hmn : m < n) : red.Adj (f₀ m).val (f₀ n).val := by
    change red.Adj (f₀ m).val (Nat.strongRec (motive := fun n => S (e n)) step n).val
    rw [Nat.strongRec_eq]
    let t := Finset.univ.image (fun i : Fin n => (f₀ i.val).val)
    have ht : (f₀ m).val ∈ t := Finset.mem_image.mpr ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩
    exact (h (e n) t).choose_spec.2 _ ht
  let g (i : I) : ℕ := (he i).choose
  have hg (i : I) : e (g i) = i := (he i).choose_spec
  let f (i : I) : V := (f₀ (g i)).val
  refine ⟨f, ?_, ?_⟩
  · intro i
    have hmem : f i ∈ S (e (g i)) := (f₀ (g i)).property
    rwa [hg i] at hmem
  ·
    intro i j hij
    have hne : g i ≠ g j := fun h => hij ((hg i).symm.trans ((congrArg e h).trans (hg j)))
    exact (lt_or_gt_of_ne hne).elim (fun hlt => hpair hlt) (fun hgt => (hpair hgt).symm)

private theorem OMA.type_biUnion_finset_lt.{v} {I : Type*} {V : Type v}
    [LinearOrder V] [WellFoundedLT V] (k : ℕ) (t : Finset I) (S : I → Set V)
    (h : ∀ i ∈ t, typeLT (S i) < (ω : Ordinal.{v}) ^ (k : Ordinal.{v})) :
    typeLT (⋃ i ∈ t, S i : Set V) < (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have he : (⋃ i ∈ (∅ : Finset I), S i) = ∅ := by simp
    rw [he, Ordinal.type_eq_zero_iff_isEmpty.mpr (by infer_instance)]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  | @insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    by_contra! hb
    rcases OMA.power_le_union k _ _ hb with hb | hb
    · exact (h i (Finset.mem_insert_self i t)).not_ge hb
    · exact (ih fun j hj => h j (Finset.mem_insert_of_mem hj)).not_ge hb

private theorem OMA.clique_of_uniform_bound.{v} {V : Type v} [LinearOrder V] [WellFoundedLT V]
    (red blue : SimpleGraph V) (hc : IsCompl red blue) (s : Set V)
    (β : Ordinal.{v}) [Countable β.ToType] [Nonempty β.ToType] (k : ℕ) (hk : 0 < k)
    (hs : (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) * β ≤ typeLT s)
    (hblue : ∀ x, typeLT (blue.neighborSet x ∩ s : Set V) < (ω : Ordinal.{v}) ^ (k : Ordinal.{v})) :
    ∃ t ⊆ s, red.IsClique t ∧ typeLT t = β := by
  classical
  let a : Ordinal.{v} := ω ^ (k : Ordinal.{v})
  obtain ⟨S, hS, horder⟩ := OMA.ordered_blocks a β s hs
  have hchoice (i : β.ToType) (t : Finset V) : ∃ x ∈ S i, ∀ y ∈ t, red.Adj y x := by
    let F (y : V) : Set V := {y} ∪ (blue.neighborSet y ∩ s)
    have hsmall (y : V) : typeLT (F y) < a := by
      by_contra! hlarge
      rcases OMA.power_le_union k _ _ hlarge with hlarge | hlarge
      · have hsingle : typeLT ({y} : Set V) = 1 := by simp
        rw [hsingle] at hlarge
        have hk' : (0 : Ordinal.{v}) < (k : Ordinal.{v}) := by exact_mod_cast hk
        have ha : (1 : Ordinal.{v}) < a := by
          simpa only [Ordinal.opow_zero] using
            (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hk'
        exact ha.not_ge hlarge
      · exact (hblue y).not_ge hlarge
    have hsmall' : typeLT (⋃ y ∈ t, F y : Set V) < a :=
      OMA.type_biUnion_finset_lt k t F (fun y _ => hsmall y)
    have hnot : ¬ S i ⊆ (⋃ y ∈ t, F y : Set V) := by
      intro hsub
      exact hsmall'.not_ge ((hS i).2 ▸ Ordinal.type_mono hsub)
    obtain ⟨x, hx, hxf⟩ := Set.not_subset.mp hnot
    refine ⟨x, hx, fun y hy => ?_⟩
    have hxf' : x ∉ F y := fun hc' => hxf (Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, hc'⟩⟩)
    rw [hc.eq_compl, SimpleGraph.compl_adj]
    exact ⟨fun h => hxf' (Or.inl (by simp [h])), fun h => hxf' (Or.inr ⟨h, (hS i).1 hx⟩)⟩
  obtain ⟨f, hf, hpair⟩ := OMA.clique_choice red S hchoice
  have hf' : StrictMono f := fun _ _ hij => horder hij (hf _) (hf _)
  refine ⟨Set.range f, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (hS i).1 (hf i)
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hpair fun heq => hij (congrArg f heq)
  · rw [OMA.type_range hf', Ordinal.type_toType]

private theorem OMA.countable_power.{v} (a : Ordinal.{v}) (ha : a ≤ ω) :
    Countable ((ω : Ordinal.{v}) ^ a).ToType := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType]
  apply (Ordinal.card_opow_le_of_omega0_le_left (le_refl ω) a).trans
  rw [Ordinal.card_omega0]
  exact max_le le_rfl ((Ordinal.card_le_card ha).trans_eq Ordinal.card_omega0)

private theorem OMA.nonempty_power.{v} (a : Ordinal.{v}) :
    Nonempty ((ω : Ordinal.{v}) ^ a).ToType := by
  by_contra! h
  have hz : typeLT ((ω : Ordinal.{v}) ^ a).ToType = 0 :=
    Ordinal.type_eq_zero_iff_isEmpty.mpr h
  rw [Ordinal.type_toType] at hz
  exact (Ordinal.opow_pos a Ordinal.omega0_pos).ne' hz

/-- A sufficiently high finite power suffices when the desired red order type is a finite power. -/
private theorem OMA.finite_power_ramsey.{v} (n m : ℕ) :
    OrdinalCardinalRamsey.{v} (ω ^ (((m + 1) * n + 1 : ℕ) : Ordinal.{v}))
      (ω ^ (n : Ordinal.{v})) m := by
  induction m with
  | zero =>
    intro red blue hc
    exact Or.inr ⟨∅, by simp, by simp⟩
  | succ m ih =>
    intro red blue hc
    by_cases hr : ∃ t, red.IsClique t ∧ typeLT t = (ω : Ordinal.{v}) ^ (n : Ordinal.{v})
    · exact Or.inl hr
    by_cases hb : ∃ t, blue.IsClique t ∧ #t = ((m + 1 : ℕ) : Cardinal.{v})
    · exact Or.inr hb
    let k : ℕ := (m + 1) * n + 1
    have hk : 0 < k := Nat.succ_pos _
    have hcount := OMA.countable_power (n : Ordinal.{v}) (Ordinal.natCast_lt_omega0 n).le
    have hnonempty := OMA.nonempty_power (n : Ordinal.{v})
    have hsize : (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) * (ω ^ (n : Ordinal.{v})) ≤
        typeLT (Set.univ : Set ((ω : Ordinal.{v}) ^ (((m + 1 + 1) * n + 1 : ℕ) : Ordinal.{v})).ToType) := by
      rw [OMA.typeLT_univ_toType, ← Ordinal.opow_add, ← Nat.cast_add]
      have heq : k + n = (m + 1 + 1) * n + 1 := by dsimp [k]; ring
      rw [heq]
    have hlocal x := OMA.neighbor_type_lt ih hc hr hb x
    obtain ⟨t, _, ht, heq⟩ := OMA.clique_of_uniform_bound red blue hc Set.univ
      ((ω : Ordinal.{v}) ^ (n : Ordinal.{v})) k hk hsize
      (fun x => (Ordinal.type_mono Set.inter_subset_left).trans_lt (hlocal x))
    exact Or.inl ⟨t, ht, heq⟩

private theorem OMA.uniform_omega_power.{v}
    (red blue : SimpleGraph ((ω : Ordinal.{v}) ^ (ω : Ordinal.{v})).ToType)
    (hc : IsCompl red blue) (k : ℕ) (hk : 0 < k)
    (hbound : ∀ x, typeLT (blue.neighborSet x) < (ω : Ordinal.{v}) ^ (k : Ordinal.{v})) :
    ∃ t, red.IsClique t ∧ typeLT t = (ω : Ordinal.{v}) ^ (ω : Ordinal.{v}) := by
  have hcount := OMA.countable_power (ω : Ordinal.{v}) le_rfl
  have hnonempty := OMA.nonempty_power (ω : Ordinal.{v})
  have hsize : (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) * (ω ^ ω) ≤
      typeLT (Set.univ : Set ((ω : Ordinal.{v}) ^ (ω : Ordinal.{v})).ToType) := by
    rw [OMA.typeLT_univ_toType, ← Ordinal.opow_add, Ordinal.add_omega0 (Ordinal.natCast_lt_omega0 k)]
  obtain ⟨t, _, ht, heq⟩ := OMA.clique_of_uniform_bound red blue hc Set.univ (ω ^ ω) k hk hsize
    (fun x => (Ordinal.type_mono Set.inter_subset_left).trans_lt (hbound x))
  exact ⟨t, ht, heq⟩

private theorem OMA.lt_some_power.{v} {a : Ordinal.{v}} (ha : a < (ω : Ordinal.{v}) ^ ω) :
    ∃ k : ℕ, a < (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) := by
  by_contra! h
  apply ha.not_ge
  apply (Ordinal.opow_le_of_isSuccLimit Ordinal.omega0_ne_zero Ordinal.isSuccLimit_omega0).mpr
  intro b hb
  obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hb
  exact h k

private theorem OMA.red_block_after.{v}
    {red blue : SimpleGraph ((ω : Ordinal.{v}) ^ ω).ToType} (hc : IsCompl red blue) (m n : ℕ)
    (hlocal : ∀ x, typeLT (blue.neighborSet x) < (ω : Ordinal.{v}) ^ ω)
    (hb : ¬ ∃ t, blue.IsClique t ∧ #t = (m : Cardinal.{v}))
    (z : ((ω : Ordinal.{v}) ^ ω).ToType) (P : Finset ((ω : Ordinal.{v}) ^ ω).ToType) :
    ∃ u B, red.IsClique B ∧ typeLT B = (ω : Ordinal.{v}) ^ (n : Ordinal.{v}) ∧
      ∀ x ∈ B, (z < x ∧ x < u) ∧ ∀ y ∈ P, red.Adj y x := by
  classical
  let α : Ordinal.{v} := ω ^ ω
  let d : ℕ := (m + 1) * n + 1
  let F (y : α.ToType) : Set α.ToType := {y} ∪ blue.neighborSet y
  let E := Ordinal.ToType.mk (o := α)
  have hzα : (E.symm z).val < (ω : Ordinal.{v}) ^ ω := (E.symm z).property
  obtain ⟨k₀, hk₀⟩ := OMA.lt_some_power hzα
  choose p hp using fun x => OMA.lt_some_power (hlocal x)
  let k := max d (max k₀ (P.sup p))
  have hdk : d ≤ k := le_max_left _ _
  have hpos : 0 < k := (Nat.succ_pos ((m + 1) * n)).trans_le hdk
  let a : Ordinal.{v} := ω ^ (k : Ordinal.{v})
  have hpow {i : ℕ} (hi : i ≤ k) : (ω : Ordinal.{v}) ^ (i : Ordinal.{v}) ≤ a :=
    Ordinal.opow_le_opow_right Ordinal.omega0_pos (by exact_mod_cast hi)
  have hz : (E.symm z).val < a := hk₀.trans_le (hpow ((le_max_left _ _).trans (le_max_right _ _)))
  have ha' : a + a < α := by
    rw [← Ordinal.mul_two]
    exact Ordinal.opow_mul_lt_opow (by simpa using Ordinal.natCast_lt_omega0 2)
      (Ordinal.natCast_lt_omega0 k)
  let u := E ⟨a + a, ha'⟩
  have h1 : (1 : Ordinal.{v}) < a := by
    have hkpos : (0 : Ordinal.{v}) < (k : Ordinal.{v}) := by exact_mod_cast hpos
    simpa only [Ordinal.opow_zero] using
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hkpos
  have hF : typeLT (⋃ y ∈ P, F y : Set α.ToType) < a := by
    apply OMA.type_biUnion_finset_lt
    intro y hy
    by_contra! hFy
    rcases OMA.power_le_union k _ _ hFy with hFy | hFy
    · have ht : typeLT ({y} : Set α.ToType) = 1 := by simp
      rw [ht] at hFy
      exact h1.not_ge hFy
    · have hpk : p y ≤ k := ((Finset.le_sup (f := p) hy).trans (le_max_right _ _)).trans (le_max_right _ _)
      exact ((hp y).trans_le (hpow hpk)).not_ge hFy
  let f (x : a.ToType) : α.ToType :=
    E ⟨a + (Ordinal.ToType.mk.symm x).val,
      ((Ordinal.isNormal_add_right a).strictMono
        (show (Ordinal.ToType.mk.symm x).val < a from (Ordinal.ToType.mk.symm x).property)).trans ha'⟩
  have hf : StrictMono f := by
    intro x y hxy
    apply E.strictMono
    exact (Ordinal.isNormal_add_right a).strictMono (Ordinal.ToType.mk.symm.strictMono hxy)
  let T := Set.range f
  let Bad : Set α.ToType := ⋃ y ∈ P, F y
  have hT : typeLT T = a := (OMA.type_range hf).trans (Ordinal.type_toType a)
  have hgood : a ≤ typeLT (T \ Bad : Set α.ToType) := by
    have hsub : T ⊆ (T \ Bad) ∪ Bad := by
      intro x hx
      by_cases h : x ∈ Bad
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    have hl : a ≤ typeLT ((T \ Bad) ∪ Bad : Set α.ToType) := hT.ge.trans (Ordinal.type_mono hsub)
    exact (OMA.power_le_union k _ _ hl).resolve_right hF.not_ge
  rcases OMA.ramsey_on (OMA.finite_power_ramsey n m) red blue hc (T \ Bad)
      ((hpow hdk).trans hgood) with ⟨B, hsub, hclique, htype⟩ | ⟨B, _, hclique, hcard⟩
  · refine ⟨u, B, hclique, htype, ?_⟩
    intro x hx
    obtain ⟨w, rfl⟩ := (hsub hx).1
    have hxBad : f w ∉ Bad := (hsub hx).2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← E.apply_symm_apply z]
      exact E.strictMono (hz.trans_le le_self_add)
    · exact E.strictMono ((Ordinal.isNormal_add_right a).strictMono
        (show (Ordinal.ToType.mk.symm w).val < a from (Ordinal.ToType.mk.symm w).property))
    · intro y hy
      have hnot : f w ∉ F y := fun hw => hxBad (Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, hw⟩⟩)
      rw [hc.eq_compl, SimpleGraph.compl_adj]
      exact ⟨fun he => hnot (Or.inl (by simp [he])), fun he => hnot (Or.inr he)⟩
  · exact (hb ⟨B, hclique, hcard⟩).elim

/-- Local bounds allow one to make each vertex red to all sufficiently late blocks. -/
private theorem OMA.diagonal_red_blocks.{v} {m : ℕ}
    {red blue : SimpleGraph ((ω : Ordinal.{v}) ^ ω).ToType} (hc : IsCompl red blue)
    (hlocal : ∀ x, typeLT (blue.neighborSet x) < (ω : Ordinal.{v}) ^ ω)
    (hb : ¬ ∃ t, blue.IsClique t ∧ #t = (m : Cardinal.{v})) :
    ∃ B : ℕ → Set ((ω : Ordinal.{v}) ^ ω).ToType,
      (∀ n, red.IsClique (B n) ∧ typeLT (B n) = (ω : Ordinal.{v}) ^ (n : Ordinal.{v})) ∧
      (∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) ∧
      ∀ x, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ B n, red.Adj x y := by
  classical
  let α : Ordinal.{v} := ω ^ ω
  have hcount := OMA.countable_power (ω : Ordinal.{v}) le_rfl
  have hnonempty := OMA.nonempty_power (ω : Ordinal.{v})
  obtain ⟨e, he⟩ := exists_surjective_nat α.ToType
  let P (n : ℕ) := (Finset.range (n + 1)).image e
  choose next block hcl htype hspec using fun n z => OMA.red_block_after hc m n hlocal hb z (P n)
  let u : ℕ → α.ToType := Nat.rec (e 0) (fun n z => next n z)
  let B (n : ℕ) := block n (u n)
  have hs (n : ℕ) (x : α.ToType) (hx : x ∈ B n) := hspec n (u n) x hx
  have hstep (n) : u n < u (n + 1) := by
    have hB : typeLT (B n) = (ω : Ordinal.{v}) ^ (n : Ordinal.{v}) := htype n (u n)
    have hne : Nonempty (B n) := Ordinal.type_ne_zero_iff_nonempty.mp (by
      rw [hB]
      exact (Ordinal.opow_pos _ Ordinal.omega0_pos).ne')
    obtain ⟨x⟩ := hne
    exact (hs n x.val x.property).1.1.trans (hs n x.val x.property).1.2
  have hmono := monotone_nat_of_le_succ (fun n => (hstep n).le)
  refine ⟨B, fun n => ⟨hcl n (u n), htype n (u n)⟩, ?_, ?_⟩
  · intro i j hij x hx y hy
    exact ((hs i x hx).1.2.trans_le (hmono (Nat.succ_le_of_lt hij))).trans (hs j y hy).1.1
  · intro x
    obtain ⟨N, rfl⟩ := he x
    exact ⟨N, fun n hn y hy => (hs n y hy).2 (e N) (Finset.mem_image_of_mem e (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))⟩

/-- Red subblocks of unbounded order type give a clique once their cross-edges are red. -/
private theorem OMA.clique_of_subblocks.{v}
    {red : SimpleGraph ((ω : Ordinal.{v}) ^ ω).ToType}
    (D : ℕ → Set ((ω : Ordinal.{v}) ^ ω).ToType)
    (hD : ∀ n, red.IsClique (D n))
    (hcross : ∀ i j, i < j → ∀ x ∈ D i, ∀ y ∈ D j, red.Adj x y)
    (hsize : ∀ k : ℕ, ∃ n, (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) ≤ typeLT (D n)) :
    ∃ t, red.IsClique t ∧ typeLT t = (ω : Ordinal.{v}) ^ ω := by
  refine ⟨⋃ n, D n, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hcross i j hij x hi y hj
    · exact hD i hi hj hxy
    · exact (hcross j i hji y hj x hi).symm
  · apply le_antisymm
    · exact (Ordinal.type_set_le _).trans_eq (Ordinal.type_toType _)
    · apply (Ordinal.opow_le_of_isSuccLimit Ordinal.omega0_ne_zero Ordinal.isSuccLimit_omega0).mpr
      intro b hb
      obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hb
      obtain ⟨n, hn⟩ := hsize k
      exact hn.trans (Ordinal.type_mono (Set.subset_iUnion D n))

/-- Thin the red blocks to keep unbounded order types with all cross-edges red. -/
private theorem OMA.thin_diagonal_red_blocks.{v} (m : ℕ)
    (red blue : SimpleGraph ((ω : Ordinal.{v}) ^ ω).ToType)
    (hc : IsCompl red blue)
    (hlocal : ∀ x, typeLT (blue.neighborSet x) < (ω : Ordinal.{v}) ^ ω)
    (hunbounded : ∀ k : ℕ, 0 < k → ∃ x,
      (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) ≤ typeLT (blue.neighborSet x))
    (hb : ¬ ∃ t, blue.IsClique t ∧ #t = (m : Cardinal.{v}))
    (B : ℕ → Set ((ω : Ordinal.{v}) ^ ω).ToType)
    (hB : ∀ n, red.IsClique (B n) ∧ typeLT (B n) = (ω : Ordinal.{v}) ^ (n : Ordinal.{v}))
    (horder : ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y)
    (hdiag : ∀ x, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ B n, red.Adj x y) :
    ∃ D : ℕ → Set ((ω : Ordinal.{v}) ^ ω).ToType,
      (∀ n, D n ⊆ B n) ∧
      (∀ i j, i < j → ∀ x ∈ D i, ∀ y ∈ D j, red.Adj x y) ∧
      ∀ k : ℕ, ∃ n, (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) ≤ typeLT (D n) := by
  sorry

private theorem OMA.unbounded_neighbors.{v} (m : ℕ)
    (red blue : SimpleGraph ((ω : Ordinal.{v}) ^ ω).ToType)
    (hc : IsCompl red blue)
    (hlocal : ∀ x, typeLT (blue.neighborSet x) < (ω : Ordinal.{v}) ^ ω)
    (hunbounded : ∀ k : ℕ, 0 < k → ∃ x,
      (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) ≤ typeLT (blue.neighborSet x))
    (hb : ¬ ∃ t, blue.IsClique t ∧ #t = (m : Cardinal.{v})) :
    ∃ t, red.IsClique t ∧ typeLT t = (ω : Ordinal.{v}) ^ ω := by
  obtain ⟨B, hB, horder, hdiag⟩ := OMA.diagonal_red_blocks hc hlocal hb
  obtain ⟨D, hsub, hcross, hsize⟩ :=
    OMA.thin_diagonal_red_blocks m red blue hc hlocal hunbounded hb B hB horder hdiag
  exact OMA.clique_of_subblocks D (fun n => (hB n).1.subset (hsub n)) hcross hsize

/-- Milner's Ramsey relation for all finite blue clique sizes. -/
theorem OMA.milnor.{v} (m : ℕ) (hm : 3 ≤ m) :
    OrdinalCardinalRamsey.{v} (ω ^ ω) (ω ^ ω) m := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hp : OrdinalCardinalRamsey.{v} (ω ^ ω) (ω ^ ω) m := by
      by_cases h : m ≤ 2
      · exact OMA.small_m _ m h
      · exact ih (by omega)
    intro red blue hc
    by_cases hr : ∃ t, red.IsClique t ∧ typeLT t = (ω : Ordinal.{v}) ^ (ω : Ordinal.{v})
    · exact Or.inl hr
    by_cases hb : ∃ t, blue.IsClique t ∧ #t = ((m + 1 : ℕ) : Cardinal.{v})
    · exact Or.inr hb
    have hlocal := OMA.neighbor_type_lt hp hc hr hb
    by_cases hu : ∀ k : ℕ, 0 < k → ∃ x,
        (ω : Ordinal.{v}) ^ (k : Ordinal.{v}) ≤ typeLT (blue.neighborSet x)
    · exact Or.inl (OMA.unbounded_neighbors (m + 1) red blue hc hlocal hu hb)
    · push Not at hu
      obtain ⟨k, hk, hbound⟩ := hu
      exact Or.inl (OMA.uniform_omega_power red blue hc k hk hbound)

theorem OMA.solution : type_of% @Erdos590.erdos_590.variants.finite_cardinal := by
  intro m
  rcases le_or_gt m 2 with h | h
  · exact OMA.small_m _ m h
  · exact OMA.milnor m h
