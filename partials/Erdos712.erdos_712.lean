import FormalConjectures.ErdosProblems.«712»

/-! Turán’s three-part construction for the tetrahedron case. -/

-- Problem: Erdős Problem 712 (it asks for a value)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/712.lean:46 (declaration Erdos712.erdos_712; placeholder Erdos712.erdos_712.answer := sorry)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Give the value explicitly as OMA.answer (same type as the placeholder; not built from Erdos712.…,
-- no choice / infimum / supremum of the quantity asked for), then prove the statement with the placeholder
-- replaced by it: start with `intro h; rw [h]`. No sorry, no axiom, no native_decide. A person checks the answer.

namespace Erdos712Turan

open Finset

private def Good (a b c : Fin 3) : Prop :=
  (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∨
  (a = b ∧ c = a + 1) ∨ (a = c ∧ b = a + 1) ∨ (b = c ∧ a = b + 1)
deriving Decidable

private theorem good_permutations :
    ∀ a b c : Fin 3, Good a b c →
      Good a c b ∧ Good b a c ∧ Good b c a ∧ Good c a b ∧ Good c b a := by
  decide

private theorem missing_triple :
    ∀ a b c d : Fin 3, ¬ (Good a b c ∧ Good a b d ∧ Good a c d ∧ Good b c d) := by
  decide

private def Allowed {V : Type*} (color : V → Fin 3) (e : Finset V) : Prop :=
  ∀ a ∈ e, ∀ b ∈ e, ∀ c ∈ e, a ≠ b → a ≠ c → b ≠ c →
    Good (color a) (color b) (color c)

private theorem allowed_triple {V : Type*} [DecidableEq V] {color : V → Fin 3}
    {x y z : V} (h : Good (color x) (color y) (color z)) :
    Allowed color {x, y, z} := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := good_permutations _ _ _ h
  intro a ha b hb c hc hab hac hbc
  simp only [mem_insert, mem_singleton] at ha hb hc
  rcases ha with (rfl | rfl | rfl) <;>
    rcases hb with (rfl | rfl | rfl) <;>
    rcases hc with (rfl | rfl | rfl) <;>
    first | contradiction | exact h | exact h₁ | exact h₂ | exact h₃ | exact h₄ | exact h₅

private noncomputable def family {V : Type*} [Fintype V] [DecidableEq V]
    (color : V → Fin 3) : Finset (Finset V) := by
  classical
  exact univ.powersetCard 3 |>.filter (Allowed color)

private theorem mem_family {V : Type*} [Fintype V] [DecidableEq V]
    {color : V → Fin 3} {e : Finset V} :
    e ∈ family color ↔ e.card = 3 ∧ Allowed color e := by
  classical
  simp [family, mem_powersetCard]

private theorem cliqueFree {V : Type*} [Fintype V] [DecidableEq V]
    (color : V → Fin 3) :
    ¬ (family color).ContainsCompleteHypergraph 3 4 := by
  rintro ⟨s, hs, hsub⟩
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := card_eq_four.mp hs
  have allowed_subset {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
      (hxs : x ∈ ({a, b, c, d} : Finset V)) (hys : y ∈ ({a, b, c, d} : Finset V))
      (hzs : z ∈ ({a, b, c, d} : Finset V)) : Good (color x) (color y) (color z) := by
    have hmem : ({x, y, z} : Finset V) ∈ ({a, b, c, d} : Finset V).powersetCard 3 := by
      rw [mem_powersetCard]
      exact ⟨by
        intro v hv
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with (rfl | rfl | rfl)
        · exact hxs
        · exact hys
        · exact hzs,
        card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩⟩
    exact (mem_family.mp (hsub hmem)).2 x (by simp) y (by simp) z (by simp) hxy hxz hyz
  exact missing_triple (color a) (color b) (color c) (color d)
    ⟨allowed_subset hab hac hbc (by simp) (by simp) (by simp),
      allowed_subset hab had hbd (by simp) (by simp) (by simp),
      allowed_subset hac had hcd (by simp) (by simp) (by simp),
      allowed_subset hbc hbd hcd (by simp) (by simp) (by simp)⟩

private def rainbow {m : ℕ} (x : Fin 3 → Fin m) : Finset (Fin 3 × Fin m) :=
  univ.map ⟨fun i => (i, x i), fun _ _ h => congrArg Prod.fst h⟩

private def doubled {m : ℕ} (i : Fin 3) (p : Finset (Fin m)) (z : Fin m) :
    Finset (Fin 3 × Fin m) :=
  insert (i + 1, z) (p.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩)

private theorem mem_rainbow {m : ℕ} {x : Fin 3 → Fin m} {i : Fin 3} {v : Fin m} :
    (i, v) ∈ rainbow x ↔ v = x i := by
  simp only [rainbow, mem_map, mem_univ, true_and]
  change (∃ j, (j, x j) = (i, v)) ↔ v = x i
  simp [Prod.mk.injEq, eq_comm]

private theorem mem_doubled {m : ℕ} {i j : Fin 3} {p : Finset (Fin m)} {z v : Fin m} :
    (j, v) ∈ doubled i p z ↔ (j = i + 1 ∧ v = z) ∨ (j = i ∧ v ∈ p) := by
  simp only [doubled, mem_insert, Prod.mk.injEq, mem_map]
  constructor
  · rintro (h | ⟨u, hu, he⟩)
    · exact Or.inl h
    · change (i, u) = (j, v) at he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact Or.inr ⟨rfl, hu⟩
  · rintro (h | ⟨rfl, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, rfl⟩

private theorem next_ne : ∀ i : Fin 3, i + 1 ≠ i := by decide

private theorem rainbow_mem {m : ℕ} (x : Fin 3 → Fin m) :
    rainbow x ∈ family Prod.fst := by
  refine mem_family.mpr ⟨by simp [rainbow], ?_⟩
  intro a ha b hb c hc hab hac hbc
  have determined {v : Fin 3 × Fin m} (hv : v ∈ rainbow x) : v.2 = x v.1 :=
    mem_rainbow.mp hv
  have distinct {v w : Fin 3 × Fin m} (hv : v ∈ rainbow x) (hw : w ∈ rainbow x)
      (hne : v ≠ w) : v.1 ≠ w.1 := by
    intro h
    exact hne (Prod.ext h (by rw [determined hv, determined hw, h]))
  exact Or.inl ⟨distinct ha hb hab, distinct ha hc hac, distinct hb hc hbc⟩

private theorem doubled_mem {m : ℕ} (i : Fin 3) {p : Finset (Fin m)} (hp : p.card = 2)
    (z : Fin m) : doubled i p z ∈ family Prod.fst := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hp
  have hzi : (i + 1, z) ≠ (i, u) := fun h => next_ne i (congrArg Prod.fst h)
  have hzi' : (i + 1, z) ≠ (i, v) := fun h => next_ne i (congrArg Prod.fst h)
  have huv' : (i, u) ≠ (i, v) := fun h => huv (congrArg Prod.snd h)
  have he : doubled i {u, v} z = {(i + 1, z), (i, u), (i, v)} := by
    simp only [doubled, map_insert, map_singleton]
    rfl
  rw [he, mem_family]
  exact ⟨card_eq_three.mpr ⟨_, _, _, hzi, hzi', huv', rfl⟩,
    allowed_triple (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩

private def part {m : ℕ} (i : Fin 3) (e : Finset (Fin 3 × Fin m)) : Finset (Fin m) :=
  (e.filter fun v => v.1 = i).image Prod.snd

private theorem mem_part {m : ℕ} {i : Fin 3} {e : Finset (Fin 3 × Fin m)} {v : Fin m} :
    v ∈ part i e ↔ (i, v) ∈ e := by
  simp only [part, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨j, w⟩, ⟨hw, rfl⟩, rfl⟩
    exact hw
  · intro hv
    exact ⟨(i, v), ⟨hv, rfl⟩, rfl⟩

private theorem part_rainbow {m : ℕ} (i : Fin 3) (x : Fin 3 → Fin m) :
    part i (rainbow x) = {x i} := by
  ext v
  rw [mem_part, mem_rainbow, mem_singleton]

private theorem part_doubled {m : ℕ} (i : Fin 3) (p : Finset (Fin m)) (z : Fin m) :
    part i (doubled i p z) = p := by
  ext v
  simp [mem_part, mem_doubled, (next_ne i).symm]

private theorem part_doubled_next {m : ℕ} (i : Fin 3) (p : Finset (Fin m)) (z : Fin m) :
    part (i + 1) (doubled i p z) = {z} := by
  ext v
  simp [mem_part, mem_doubled]

private theorem part_doubled_not_color {m : ℕ} {i j : Fin 3} (h : j ≠ i)
    (p : Finset (Fin m)) (z : Fin m) : (part j (doubled i p z)).card ≤ 1 := by
  apply (card_le_card (t := {z}) ?_).trans (by simp)
  intro v hv
  rcases mem_doubled.mp (mem_part.mp hv) with ⟨_, rfl⟩ | ⟨he, _⟩
  · simp
  · exact (h he).elim

private abbrev Pairs (m : ℕ) := ↥((univ : Finset (Fin m)).powersetCard 2)

private def edge {m : ℕ} :
    (Fin 3 → Fin m) ⊕ (Fin 3 × Pairs m × Fin m) → Finset (Fin 3 × Fin m) :=
  Sum.elim rainbow (fun u => doubled u.1 u.2.1.val u.2.2)

private theorem edge_card_pair {m : ℕ} (p : Pairs m) : p.val.card = 2 :=
  (mem_powersetCard.mp p.property).2

private theorem rainbow_ne_doubled {m : ℕ} (x : Fin 3 → Fin m)
    (i : Fin 3) (p : Pairs m) (z : Fin m) : rainbow x ≠ doubled i p.val z := by
  intro h
  have hc := congrArg (fun e => (part i e).card) h
  change (part i (rainbow x)).card = (part i (doubled i p.val z)).card at hc
  simp [part_rainbow, part_doubled, edge_card_pair] at hc

private theorem edge_injective (m : ℕ) : Function.Injective (@edge m) := by
  intro u v h
  rcases u with x | ⟨i,p,z⟩ <;> rcases v with y | ⟨j,q,w⟩
  · change rainbow x = rainbow y at h
    congr 1
    funext a
    have ha := congrArg (part a) h
    simpa [part_rainbow] using ha
  · exact (rainbow_ne_doubled x j q w h).elim
  · exact (rainbow_ne_doubled y i p z h.symm).elim
  · change doubled i p.val z = doubled j q.val w at h
    have hij : i = j := by
      by_contra hne
      have hc := part_doubled_not_color hne q.val w
      rw [← h, part_doubled, edge_card_pair] at hc
      omega
    subst j
    have hpq : p = q := by
      apply Subtype.ext
      simpa [part_doubled] using congrArg (part i) h
    subst q
    have hzw : z = w := by
      simpa [part_doubled_next] using congrArg (part (i + 1)) h
    subst w
    rfl

private theorem family_card_lower (m : ℕ) :
    m ^ 3 + 3 * (m.choose 2 * m) ≤ (family (V := Fin 3 × Fin m) Prod.fst).card := by
  have hsub : univ.image (@edge m) ⊆ family Prod.fst := by
    intro e he
    obtain ⟨u, -, rfl⟩ := mem_image.mp he
    rcases u with x | ⟨i,p,z⟩
    · exact rainbow_mem x
    · exact doubled_mem i (edge_card_pair p) z
  have h := card_le_card hsub
  rwa [card_image_of_injective _ (edge_injective m), card_univ, Fintype.card_sum,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
    card_powersetCard, card_univ, Fintype.card_fin] at h

/-- A balanced three-part tetrahedron-free hypergraph contains the rainbow triples and the
triples with two vertices in one part and one vertex in the cyclic successor. -/
theorem tetrahedron_extremal_lower (m : ℕ) :
    m ^ 3 + 3 * (m.choose 2 * m) ≤ Hypergraph.cliqueExtremalNumber (3 * m) 3 4 := by
  classical
  let e : Fin 3 × Fin m ≃ Fin (3 * m) := finProdFinEquiv
  let color (v : Fin (3 * m)) := (e.symm v).1
  have hmap :
      (family Prod.fst).map (Finset.mapEmbedding e.toEmbedding).toEmbedding ⊆ family color := by
    intro edge hedge
    obtain ⟨s, hs, rfl⟩ := mem_map.mp hedge
    obtain ⟨hc, ha⟩ := mem_family.mp hs
    refine mem_family.mpr ⟨by simpa using hc, ?_⟩
    change Allowed color (s.map e.toEmbedding)
    intro a ha' b hb' c hc' hab hac hbc
    obtain ⟨a, ha₀, rfl⟩ := mem_map.mp ha'
    obtain ⟨b, hb₀, rfl⟩ := mem_map.mp hb'
    obtain ⟨c, hc₀, rfl⟩ := mem_map.mp hc'
    simpa [color] using ha a ha₀ b hb₀ c hc₀
      (fun h => hab (congrArg e h)) (fun h => hac (congrArg e h)) (fun h => hbc (congrArg e h))
  have hcard := card_le_card hmap
  rw [card_map] at hcard
  refine ((family_card_lower m).trans hcard).trans ?_
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply le_sup
  simp only [mem_filter, mem_powerset]
  refine ⟨?_, cliqueFree color⟩
  intro edge hedge
  exact mem_powersetCard.mpr ⟨subset_univ _, (mem_family.mp hedge).1⟩

private theorem cast_choose_three_mul (m : ℕ) (hm : 1 ≤ m) :
    ((3 * m).choose 3 : ℝ) = (3 * (m : ℝ) - 2) * (3 * m) * (3 * m - 1) / 6 := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.descFactorial_eq_factorial_mul_choose (3 * m) 3)
  rw [Nat.descFactorial_succ (3 * m) 2, Nat.cast_mul, Nat.cast_descFactorial_two,
    Nat.cast_sub (by omega : 2 ≤ 3 * m), Nat.cast_mul] at h
  norm_num [Nat.factorial] at h
  linarith only [h]

/-- The normalized tetrahedron extremal number is at least 5/9 on positive multiples of three. -/
theorem tetrahedron_ratio_lower (m : ℕ) (hm : 1 ≤ m) :
    (5 : ℝ) / 9 ≤ (Hypergraph.cliqueExtremalNumber (3 * m) 3 4 : ℝ) / (3 * m).choose 3 := by
  have hpos : (0 : ℝ) < (3 * m).choose 3 := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ 3 * m)
  apply (le_div_iff₀ hpos).mpr
  have hcount := tetrahedron_extremal_lower m
  have hcount' : (m : ℝ) ^ 3 + 3 * ((m.choose 2 : ℝ) * m) ≤
      Hypergraph.cliqueExtremalNumber (3 * m) 3 4 := by
    exact_mod_cast hcount
  refine le_trans ?_ hcount'
  rw [Nat.cast_choose_two ℝ, cast_choose_three_mul m hm]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hprod : 0 ≤ (m : ℝ) * (9 * m - 5) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith only [hprod]

open Filter Topology in
/-- The positive multiples of three suffice to bound any limiting tetrahedron density. -/
theorem tetrahedron_density_lower {d : ℝ}
    (h : Tendsto (fun n : ℕ => (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) / n.choose 3)
      atTop (𝓝 d)) : (5 : ℝ) / 9 ≤ d := by
  have hseq : Tendsto (fun m : ℕ => 3 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => show m ≤ 3 * m by omega) tendsto_id
  refine le_of_tendsto_of_tendsto tendsto_const_nhds (h.comp hseq) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  exact tetrahedron_ratio_lower m hm

private abbrev BlowupChoices {n : ℕ} (H : Finset (Finset (Fin n))) (m : ℕ) :=
  (e : ↥H) × (↥e.val → Fin m)

private def blowupProjection {n m : ℕ} (x : Fin (n * m)) : Fin n :=
  (finProdFinEquiv.symm x).1

private def blowupEdge {n m : ℕ} {H : Finset (Finset (Fin n))}
    (c : BlowupChoices H m) : Finset (Fin (n * m)) :=
  univ.map ⟨fun x => finProdFinEquiv (x.val, c.2 x), by
    intro x y h
    exact Subtype.ext (congrArg Prod.fst (finProdFinEquiv.injective h))⟩

private theorem image_blowupEdge {n m : ℕ} {H : Finset (Finset (Fin n))}
    (c : BlowupChoices H m) : (blowupEdge c).image blowupProjection = c.1.val := by
  ext v
  simp only [mem_image, blowupEdge, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, hv⟩
    change blowupProjection (finProdFinEquiv (x.val, c.2 x)) = v at hv
    have he : (x : Fin n) = v := by simpa [blowupProjection] using hv
    exact he ▸ x.property
  · intro hv
    let x : ↥c.1.val := ⟨v, hv⟩
    exact ⟨finProdFinEquiv (v, c.2 x), ⟨x, rfl⟩, by simp [blowupProjection]⟩

private theorem blowupEdge_injective {n m : ℕ} {H : Finset (Finset (Fin n))} :
    Function.Injective (@blowupEdge n m H) := by
  rintro ⟨e, f⟩ ⟨e', g⟩ h
  have he : e = e' := by
    apply Subtype.ext
    simpa only [image_blowupEdge] using congrArg (fun s => s.image blowupProjection) h
  subst e'
  congr 1
  funext x
  have hx : finProdFinEquiv (x.val, f x) ∈ blowupEdge (m := m) ⟨e, g⟩ := by
    rw [← h]
    exact mem_map.mpr ⟨x, mem_univ _, rfl⟩
  obtain ⟨y, -, hy⟩ := mem_map.mp hx
  change finProdFinEquiv (y.val, g y) = finProdFinEquiv (x.val, f x) at hy
  have hp := finProdFinEquiv.injective hy
  have hyx : y = x := Subtype.ext (congrArg Prod.fst hp)
  subst y
  exact (congrArg Prod.snd hp).symm

private theorem cliqueFree_of_image {n r k m : ℕ} (hr : 2 ≤ r) (hrk : r ≤ k)
    {H : Finset (Finset (Fin n))} (hH : ∀ e ∈ H, e.card = r)
    (hfree : ¬ H.ContainsCompleteHypergraph r k)
    {G : Finset (Finset (Fin (n * m)))}
    (hG : ∀ e ∈ G, e.image blowupProjection ∈ H) :
    ¬ G.ContainsCompleteHypergraph r k := by
  rintro ⟨s, hs, hsub⟩
  have hinj : Set.InjOn (@blowupProjection n m) (s : Set (Fin (n * m))) := by
    intro a ha b hb hab
    by_contra hne
    have hp : ({a, b} : Finset (Fin (n * m))) ⊆ s :=
      insert_subset ha (singleton_subset_iff.mpr hb)
    have h2 : ({a, b} : Finset (Fin (n * m))).card ≤ r := by
      simpa [hne] using hr
    obtain ⟨e, he, hes, hcard⟩ := exists_subsuperset_card_eq hp h2 (hs ▸ hrk)
    have heG := hsub (mem_powersetCard.mpr ⟨hes, hcard⟩)
    have heinj := injOn_of_card_image_eq ((hH _ (hG _ heG)).trans hcard.symm)
    exact hne (heinj (he (by simp)) (he (by simp)) hab)
  apply hfree
  refine ⟨s.image blowupProjection, (card_image_of_injOn hinj).trans hs, ?_⟩
  intro e he
  obtain ⟨hes, her⟩ := mem_powersetCard.mp he
  let t := s.filter fun x => blowupProjection x ∈ e
  have hts : t ⊆ s := filter_subset _ _
  have himage : t.image blowupProjection = e := by
    ext v
    constructor
    · rintro hv
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hx).2
    · intro hv
      obtain ⟨x, hx, rfl⟩ := mem_image.mp (hes hv)
      exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, hv⟩, rfl⟩
  have hti := Set.InjOn.mono (Finset.coe_subset.mpr hts) hinj
  have htc : t.card = r := by
    rw [← card_image_of_injOn hti, himage, her]
  have htG := hsub (mem_powersetCard.mpr ⟨hts, htc⟩)
  exact himage ▸ hG _ htG

/-- Replacing each vertex by an independent class of size m gives m ^ r copies of each edge. -/
theorem extremal_blowup_lower (n r k m : ℕ) (hr : 2 ≤ r) (hrk : r ≤ k) :
    Hypergraph.cliqueExtremalNumber n r k * m ^ r ≤
      Hypergraph.cliqueExtremalNumber (n * m) r k := by
  classical
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  have hemptyFree : ¬ (∅ : Finset (Finset (Fin n))).ContainsCompleteHypergraph r k := by
    rintro ⟨s, hs, hsub⟩
    obtain ⟨e, _, hes, he⟩ := exists_subsuperset_card_eq
      (empty_subset s) (by simp) (hs ▸ hrk)
    exact notMem_empty e (hsub (mem_powersetCard.mpr ⟨hes, he⟩))
  let P (H : Finset (Finset (Fin n))) := ¬ H.ContainsCompleteHypergraph r k
  let admissible := @Finset.filter _ P (fun H => Classical.propDecidable (P H))
    ((univ : Finset (Fin n)).powersetCard r).powerset
  change admissible.sup card * m ^ r ≤ _
  have hnonempty : admissible.Nonempty := by
    refine ⟨∅, ?_⟩
    simpa only [admissible, P, mem_filter, mem_powerset, empty_subset, true_and] using hemptyFree
  obtain ⟨H, hH, hmax⟩ := exists_mem_eq_sup admissible hnonempty card
  simp only [admissible, P, mem_filter, mem_powerset] at hH
  obtain ⟨hsub, hfree⟩ := hH
  have hcard : ∀ e ∈ H, e.card = r := fun e he =>
    (mem_powersetCard.mp (hsub he)).2
  let G := univ.image (@blowupEdge n m H)
  have hGc : G.card = H.card * m ^ r := by
    change (univ.image (@blowupEdge n m H)).card = _
    rw [card_image_of_injective _ blowupEdge_injective, card_univ, Fintype.card_sigma]
    have hc (e : ↥H) : Fintype.card (↥e.val → Fin m) = m ^ r := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hcard e.val e.property]
    simp [hc]
  have hproj : ∀ e ∈ G, e.image blowupProjection ∈ H := by
    intro e he
    obtain ⟨c, _, rfl⟩ := mem_image.mp he
    rw [image_blowupEdge]
    exact c.1.property
  rw [hmax, ← hGc]
  apply le_sup
  simp only [mem_filter, mem_powerset]
  refine ⟨?_, cliqueFree_of_image hr hrk hcard hfree hproj⟩
  intro e he
  obtain ⟨c, _, rfl⟩ := mem_image.mp he
  exact mem_powersetCard.mpr ⟨subset_univ _, by
    simp [blowupEdge, hcard _ c.1.property]⟩

open Filter Topology

private theorem choose_scaled_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ => (r.factorial : ℝ) * n.choose r / (n : ℝ) ^ r)
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun n : ℕ => ∏ i ∈ range r, (1 - (i : ℝ) / n)) atTop (𝓝 1) := by
    have hterm (i : ℕ) : Tendsto (fun n : ℕ => 1 - (i : ℝ) / n) atTop (𝓝 1) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul (i : ℝ))
    simpa using tendsto_finsetProd (range r) (fun i _ => hterm i)
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (max r 1)] with n hn
  have hnz : (n : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  calc
    (∏ i ∈ range r, (1 - (i : ℝ) / n)) =
        ∏ i ∈ range r, ((n - i : ℕ) : ℝ) / n := by
      apply prod_congr rfl
      intro i hi
      rw [mem_range] at hi
      rw [Nat.cast_sub (by omega : i ≤ n)]
      field_simp
    _ = _ := by
      rw [prod_div_distrib, prod_const, card_range, ← Nat.cast_prod,
        ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]

private noncomputable def scaledExtremal (n r k : ℕ) : ℝ :=
  (r.factorial : ℝ) * (Hypergraph.cliqueExtremalNumber n r k : ℝ) / (n : ℝ) ^ r

private theorem scaledExtremal_tendsto {r k : ℕ} {d : ℝ}
    (h : Tendsto
      (fun n : ℕ => (Hypergraph.cliqueExtremalNumber n r k : ℝ) / n.choose r) atTop (𝓝 d)) :
    Tendsto (fun n => scaledExtremal n r k) atTop (𝓝 d) := by
  have hmul := h.mul (choose_scaled_tendsto r)
  rw [mul_one] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop r] with n hn
  have hc : (n.choose r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  simp only [scaledExtremal]
  field_simp

private theorem scaledExtremal_le_blowup {n r k m : ℕ} (hr : 2 ≤ r) (hrk : r ≤ k)
    (hm : 0 < m) : scaledExtremal n r k ≤ scaledExtremal (n * m) r k := by
  have hmz : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : (Hypergraph.cliqueExtremalNumber n r k : ℝ) * (m : ℝ) ^ r ≤
      (Hypergraph.cliqueExtremalNumber (n * m) r k : ℝ) := by
    exact_mod_cast extremal_blowup_lower n r k m hr hrk
  unfold scaledExtremal
  rw [Nat.cast_mul, mul_pow, ← mul_div_mul_right _ _ (pow_ne_zero r hmz), mul_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcast (by positivity))
    (by positivity)

/-- A bound on the limiting density is equivalent to the corresponding bound on every
finite hypergraph, with n ^ r / r! as the normalization. -/
theorem density_le_iff_finite {r k : ℕ} {d C : ℝ} (hr : 2 ≤ r) (hrk : r ≤ k)
    (h : Tendsto
      (fun n : ℕ => (Hypergraph.cliqueExtremalNumber n r k : ℝ) / n.choose r) atTop (𝓝 d)) :
    d ≤ C ↔ ∀ n : ℕ, 0 < n →
      (r.factorial : ℝ) * (Hypergraph.cliqueExtremalNumber n r k : ℝ) / (n : ℝ) ^ r ≤ C := by
  have hscale := scaledExtremal_tendsto h
  constructor
  · intro hd n hn
    have hseq : Tendsto (fun m : ℕ => n * m) atTop atTop :=
      tendsto_atTop_mono (fun m => show m ≤ n * m by
        simpa using Nat.mul_le_mul_right m (show 1 ≤ n from hn)) tendsto_id
    refine (le_of_tendsto_of_tendsto tendsto_const_nhds (hscale.comp hseq) ?_).trans hd
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact scaledExtremal_le_blowup hr hrk hm
  · intro hC
    refine le_of_tendsto_of_tendsto hscale tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact hC n hn

/-- The three-part lower bound and blow-ups reduce the tetrahedron conjecture to a
finite cubic inequality at every positive order. -/
theorem tetrahedron_density_eq_iff_finite {d : ℝ}
    (h : Tendsto (fun n : ℕ => (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) / n.choose 3)
      atTop (𝓝 d)) :
    d = (5 : ℝ) / 9 ↔ ∀ n : ℕ, 0 < n →
      54 * Hypergraph.cliqueExtremalNumber n 3 4 ≤ 5 * n ^ 3 := by
  have hcd : d ≤ (5 : ℝ) / 9 ↔ d = (5 : ℝ) / 9 :=
    ⟨fun hle => le_antisymm hle (tetrahedron_density_lower h), fun he => he.le⟩
  rw [← hcd, density_le_iff_finite (by decide) (by decide) h]
  constructor
  · intro hbound n hn
    have hp : 0 < (n : ℝ) ^ 3 := pow_pos (by exact_mod_cast hn) _
    have hb := (div_le_iff₀ hp).mp (hbound n hn)
    norm_num [Nat.factorial] at hb
    have hr : 54 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) ≤ 5 * (n : ℝ) ^ 3 := by
      linarith only [hb]
    exact_mod_cast hr
  · intro hbound n hn
    have hp : 0 < (n : ℝ) ^ 3 := pow_pos (by exact_mod_cast hn) _
    apply (div_le_iff₀ hp).mpr
    have hb : 54 * (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) ≤ 5 * (n : ℝ) ^ 3 := by
      exact_mod_cast hbound n hn
    norm_num [Nat.factorial]
    linarith only [hb]

end Erdos712Turan

-- Type copied from the placeholder. The value is still missing: it has to be the Turan density
-- pi(K_k^r) for every k > r > 2, which is not known for any single pair (r = 3, k = 4 is the
-- tetrahedron conjecture 5/9). There is not even an agreed conjectural closed form for r >= 4.
noncomputable def OMA.answer : ℕ → ℕ → ℝ := sorry

theorem OMA.solution : Erdos712.erdos_712.answer = OMA.answer → type_of% @Erdos712.erdos_712 := by
  intro h
  rw [h]
  sorry

