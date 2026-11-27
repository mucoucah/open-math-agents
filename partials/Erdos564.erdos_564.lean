import FormalConjectures.ErdosProblems.«564»

-- Problem: Erdős Problem 564
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/564.lean:41 (declaration Erdos564.erdos_564)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Finite Ramsey forcing and an equivalent Boolean cube formulation. -/

namespace OMA.Erdos564Aux

open Combinatorics Filter

private def Forces (r n : ℕ) (α : Type) : Prop :=
  ∀ c : Finset α → Bool, ∃ S : Finset α, S.card = n ∧
    ∃ b : Bool, ∀ e : Finset α, e ⊆ S → e.card = r → c e = b

private theorem forces_of_embedding {r n : ℕ} {α β : Type} (i : α ↪ β)
    (h : Forces r n α) : Forces r n β := by
  classical
  intro c
  obtain ⟨S, hS, b, hb⟩ := h (fun e ↦ c (e.map i))
  refine ⟨S.map i, by simpa using hS, b, ?_⟩
  intro e he hcard
  obtain ⟨t, ht, rfl⟩ := Finset.subset_map_iff.mp he
  exact hb t ht (by simpa using hcard)

private theorem forces_mono {r n m M : ℕ} (hm : m ≤ M)
    (h : Forces r n (Fin m)) : Forces r n (Fin M) :=
  forces_of_embedding (Fin.castLEEmb hm) h

private theorem below_ramsey_iff_not_forces {r n m : ℕ}
    (hne : ∃ M : ℕ, Forces r n (Fin M)) :
    m < hypergraphRamsey r n ↔ ¬ Forces r n (Fin m) := by
  change m < sInf {M : ℕ | Forces r n (Fin M)} ↔ _
  constructor
  · exact fun h hf ↦ (not_le_of_gt h) (Nat.sInf_le hf)
  · intro h
    by_contra! hle
    exact h (forces_mono hle (Nat.sInf_mem hne))

private theorem exists_eventual_bool (u : Ultrafilter ℕ) (f : ℕ → Bool) :
    ∃ b : Bool, ∀ᶠ x in (u : Filter ℕ), f x = b := by
  have h : ∀ᶠ x in (u : Filter ℕ), f x = false ∨ f x = true :=
    Eventually.of_forall fun x ↦ by cases f x <;> simp
  rcases u.eventually_or.mp h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

private noncomputable def eventualBool (u : Ultrafilter ℕ) (f : ℕ → Bool) : Bool :=
  (exists_eventual_bool u f).choose

private theorem eventually_eq_eventualBool (u : Ultrafilter ℕ) (f : ℕ → Bool) :
    ∀ᶠ x in (u : Filter ℕ), f x = eventualBool u f :=
  (exists_eventual_bool u f).choose_spec

private noncomputable def iteratedColor (u : Ultrafilter ℕ) (c : Finset ℕ → Bool) :
    ℕ → Finset ℕ → Bool
  | 0, e => c e
  | k + 1, e => eventualBool u (fun x ↦ iteratedColor u c k (insert x e))

private theorem forces_nat (r n : ℕ) : Forces r n ℕ := by
  classical
  obtain ⟨u, hu⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  intro c
  let g := iteratedColor u c
  let b := g r ∅
  suffices h : ∃ S : Finset ℕ, S.card = n ∧
      ∀ e ⊆ S, e.card ≤ r → g (r - e.card) e = b by
    obtain ⟨S, hc, hm⟩ := h
    exact ⟨S, hc, b, fun e he her ↦ by simpa [her, g, iteratedColor] using hm e he her.le⟩
  induction n with
  | zero =>
    refine ⟨∅, rfl, ?_⟩
    intro e he _
    have he' : e = ∅ := Finset.subset_empty.mp he
    subst e
    simp [b]
  | succ n ih =>
    obtain ⟨S, hS, hmono⟩ := ih
    have hext : ∀ᶠ x in (u : Filter ℕ),
        ∀ t ∈ S.powerset, t.card < r → g (r - (t.card + 1)) (insert x t) = b := by
      apply (eventually_all_finset S.powerset).mpr
      intro t ht
      by_cases htr : t.card < r
      · have hh := eventually_eq_eventualBool u (fun x ↦ g (r - (t.card + 1)) (insert x t))
        have heq : r - t.card = r - (t.card + 1) + 1 := by omega
        have hold := hmono t (Finset.mem_powerset.mp ht) htr.le
        rw [heq] at hold
        exact hh.mono fun x hx _ ↦ hx.trans hold
      · exact Eventually.of_forall fun _ hlt ↦ (htr hlt).elim
    have hout : ∀ᶠ x in (u : Filter ℕ), x ∉ S := by
      apply hu
      filter_upwards [eventually_gt_atTop (S.sup id)] with x hx hmem
      exact (not_lt_of_ge (Finset.le_sup (f := id) hmem)) hx
    obtain ⟨x, hx, hxS⟩ := (hext.and hout).exists
    refine ⟨insert x S, by rw [Finset.card_insert_of_notMem hxS, hS], ?_⟩
    intro e he her
    by_cases hxe : x ∈ e
    · have hs : e.erase x ⊆ S := by
        intro y hy
        have h := Finset.mem_erase.mp hy
        exact (Finset.mem_insert.mp (he h.2)).resolve_left h.1
      have hcard := Finset.card_erase_add_one hxe
      have hh := hx (e.erase x) (Finset.mem_powerset.mpr hs) (by omega)
      rwa [hcard, Finset.insert_erase hxe] at hh
    · exact hmono e (fun y hy ↦
        (Finset.mem_insert.mp (he hy)).resolve_left (fun h ↦ hxe (h ▸ hy))) her

private noncomputable def extendColor {m : ℕ} (c : Finset (Fin m) → Bool) (e : Finset ℕ) : Bool :=
  if h : ∃ t : Finset (Fin m), t.map Fin.valEmbedding = e then c h.choose else false

private theorem extendColor_map {m : ℕ} (c : Finset (Fin m) → Bool) (t : Finset (Fin m)) :
    extendColor c (t.map Fin.valEmbedding) = c t := by
  classical
  unfold extendColor
  rw [dif_pos ⟨t, rfl⟩]
  congr 1
  exact Finset.map_injective Fin.valEmbedding (Classical.choose_spec (show
    ∃ q : Finset (Fin m), q.map Fin.valEmbedding = t.map Fin.valEmbedding from ⟨t, rfl⟩))

private theorem finite_ramsey (r n : ℕ) : ∃ M : ℕ, Forces r n (Fin M) := by
  classical
  by_contra! h
  have hb (m : ℕ) : ∃ c : Finset (Fin m) → Bool, ¬ (∃ S : Finset (Fin m),
      S.card = n ∧ ∃ b : Bool, ∀ e : Finset (Fin m), e ⊆ S → e.card = r → c e = b) :=
    not_forall.mp (h m)
  choose c hc using hb
  obtain ⟨u, hu⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  let d (e : Finset ℕ) := eventualBool u (fun m ↦ extendColor (c m) e)
  obtain ⟨S, hS, b, hmono⟩ := forces_nat r n d
  have hmatch : ∀ᶠ m in (u : Filter ℕ),
      ∀ e ∈ S.powerset, extendColor (c m) e = d e :=
    (eventually_all_finset S.powerset).mpr fun e _ ↦ eventually_eq_eventualBool u _
  have hlarge : ∀ᶠ m in (u : Filter ℕ), S.sup id < m :=
    hu (eventually_gt_atTop _)
  obtain ⟨m, hm, hmS⟩ := (hmatch.and hlarge).exists
  have hs : S ⊆ Finset.univ.map (Fin.valEmbedding : Fin m ↪ ℕ) := by
    intro x hx
    exact Finset.mem_map.mpr ⟨⟨x, lt_of_le_of_lt (Finset.le_sup (f := id) hx) hmS⟩,
      Finset.mem_univ _, rfl⟩
  obtain ⟨T, _, rfl⟩ := Finset.subset_map_iff.mp hs
  refine hc m ⟨T, by simpa using hS, b, ?_⟩
  intro e he her
  have hsub := (Finset.map_subset_map (f := Fin.valEmbedding)).mpr he
  rw [← extendColor_map (c m) e, hm _ (Finset.mem_powerset.mpr hsub)]
  exact hmono _ hsub (by simpa using her)

private theorem forces_mono_size {r a b : ℕ} {α : Type} (hab : a ≤ b)
    (h : Forces r b α) : Forces r a α := by
  classical
  intro c
  obtain ⟨S, hS, col, hcol⟩ := h c
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (show a ≤ S.card by rwa [hS])
  exact ⟨T, hT, col, fun e he hr ↦ hcol e (he.trans hTS) hr⟩

private noncomputable def cubeEquiv (t : ℕ) :
    (Fin (2 ^ t) → Bool) ≃ Fin (2 ^ (2 ^ t)) :=
  Fintype.equivFinOfCardEq (by simp)

private theorem forces_cube_iff (r n t : ℕ) :
    Forces r n (Fin (2 ^ t) → Bool) ↔ Forces r n (Fin (2 ^ (2 ^ t))) :=
  ⟨forces_of_embedding (cubeEquiv t).toEmbedding, forces_of_embedding (cubeEquiv t).symm.toEmbedding⟩

private theorem cast_nat_tower (t : ℕ) :
    ((2 ^ (2 ^ t) : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℝ) ^ (t : ℝ) := by
  calc
    ((2 ^ (2 ^ t) : ℕ) : ℝ) = (2 : ℝ) ^ ((2 ^ t : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_cast
    _ = (2 : ℝ) ^ (2 : ℝ) ^ (t : ℝ) := by
      congr 1
      rw [Real.rpow_natCast]
      norm_cast

/-- At each sufficiently large scale, a colouring of the Boolean cube of dimension
`2 ^ t` has no monochromatic `k * t`-set. -/
private def CubeWitness : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ᶠ t : ℕ in atTop, ¬ Forces 3 (k * t) (Fin (2 ^ t) → Bool)

private theorem tower_cube_iff :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (2 : ℝ) ^ (c * n) ≤ hypergraphRamsey 3 n) ↔ CubeWitness := by
  have hbase : (1 : ℝ) < 2 := by norm_num
  constructor
  · rintro ⟨c, hc, hbound⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / c)
    have hkR : (0 : ℝ) < k := (by positivity : (0 : ℝ) < 1 / c).trans hk
    have hkN : 0 < k := by exact_mod_cast hkR
    have hck : (1 : ℝ) < c * k := by
      simpa [mul_comm] using (div_lt_iff₀ hc).mp hk
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
    refine ⟨k, hkN, ?_⟩
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (1 : ℕ)] with t ht hpos
    intro hf
    have hle := hN (k * t) (ht.trans (Nat.le_mul_of_pos_left _ hkN))
    have hexp : (t : ℝ) < c * ((k * t : ℕ) : ℝ) := by
      push_cast
      rw [← mul_assoc]
      simpa using mul_lt_mul_of_pos_right hck (by exact_mod_cast hpos : (0 : ℝ) < t)
    have hstrict := Real.rpow_lt_rpow_of_exponent_lt hbase
      (Real.rpow_lt_rpow_of_exponent_lt hbase hexp)
    rw [← cast_nat_tower] at hstrict
    have hn : 2 ^ (2 ^ t) < hypergraphRamsey 3 (k * t) := by
      exact_mod_cast hstrict.trans_le hle
    exact (below_ramsey_iff_not_forces (finite_ramsey _ _)).mp hn
      ((forces_cube_iff 3 (k * t) t).mp hf)
  · rintro ⟨k, hk, havoid⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp havoid
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    refine ⟨1 / (2 * (k : ℝ)), by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (k * N), eventually_ge_atTop k] with n hn hkn
    let t := n / k
    have htN : N ≤ t := (Nat.le_div_iff_mul_le hk).mpr (by simpa [mul_comm] using hn)
    have ht1 : 1 ≤ t := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hkn)
    have hkt : k * t ≤ n := Nat.mul_div_le _ _
    have hr := Nat.mod_add_div n k
    have hrlt := Nat.mod_lt n hk
    have hkk : k ≤ k * t := by simpa using Nat.mul_le_mul_left k ht1
    have hnt : n ≤ 2 * (k * t) := by
      change n % k + k * t = n at hr
      omega
    have hexp : 1 / (2 * (k : ℝ)) * (n : ℝ) ≤ (t : ℝ) := by
      rw [div_mul_eq_mul_div, one_mul]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
      calc
        (n : ℝ) ≤ (2 : ℝ) * ((k : ℝ) * (t : ℝ)) := by exact_mod_cast hnt
        _ = (t : ℝ) * (2 * k) := by ring
    have hbelow : 2 ^ (2 ^ t) < hypergraphRamsey 3 n := by
      apply (below_ramsey_iff_not_forces (finite_ramsey _ _)).mpr
      intro hf
      exact hN t htN ((forces_cube_iff 3 (k * t) t).mpr (forces_mono_size hkt hf))
    calc
      (2 : ℝ) ^ (2 : ℝ) ^ (1 / (2 * (k : ℝ)) * (n : ℝ)) ≤
          (2 : ℝ) ^ (2 : ℝ) ^ (t : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase.le
          (Real.rpow_le_rpow_of_exponent_le hbase.le hexp)
      _ = ((2 ^ (2 ^ t) : ℕ) : ℝ) := (cast_nat_tower t).symm
      _ ≤ (hypergraphRamsey 3 n : ℝ) := by exact_mod_cast hbelow.le

/- Ordered 3-graph formulation, binary-cube delta calculus, and the pure-delta barrier. -/

private def OrderedForces (n : ℕ) (α : Type) [LinearOrder α] : Prop :=
  ∀ c : α → α → α → Bool, ∃ S : Finset α, S.card = n ∧
    ∃ b : Bool, ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → c x y z = b

private theorem triple_sorted {α : Type} [LinearOrder α] {e : Finset α} (h : e.card = 3) :
    ∃ x y z : α, x < y ∧ y < z ∧ e = {x, y, z} := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
  rcases lt_or_gt_of_ne hab with h1 | h1 <;>
  rcases lt_or_gt_of_ne hac with h2 | h2 <;>
  rcases lt_or_gt_of_ne hbc with h3 | h3
  · exact ⟨a, b, c, h1, h3, rfl⟩
  · exact ⟨a, c, b, h2, h3, by ext w; simp; tauto⟩
  · exact (lt_asymm (h1.trans h3) h2).elim
  · exact ⟨c, a, b, h2, h1, by ext w; simp; tauto⟩
  · exact ⟨b, a, c, h1, h2, by ext w; simp; tauto⟩
  · exact (lt_asymm (h3.trans h1) h2).elim
  · exact ⟨b, c, a, h3, h2, by ext w; simp; tauto⟩
  · exact ⟨c, b, a, h3, h1, by ext w; simp; tauto⟩

private theorem triple_sorted_unique {α : Type} [LinearOrder α]
    {x₁ y₁ z₁ x₂ y₂ z₂ : α}
    (h1 : x₁ < y₁) (h2 : y₁ < z₁) (h3 : x₂ < y₂) (h4 : y₂ < z₂)
    (heq : ({x₁, y₁, z₁} : Finset α) = {x₂, y₂, z₂}) :
    x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂ := by
  have hx1 : x₁ ∈ ({x₂, y₂, z₂} : Finset α) := heq ▸ by simp
  have hx2 : x₂ ∈ ({x₁, y₁, z₁} : Finset α) := heq.symm ▸ by simp
  have hz1 : z₁ ∈ ({x₂, y₂, z₂} : Finset α) := heq ▸ by simp
  have hz2 : z₂ ∈ ({x₁, y₁, z₁} : Finset α) := heq.symm ▸ by simp
  have hy1 : y₁ ∈ ({x₂, y₂, z₂} : Finset α) := heq ▸ by simp
  have hxx : x₁ = x₂ := by
    apply le_antisymm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with rfl | rfl | rfl
      · exact le_rfl
      · exact h1.le
      · exact (h1.trans h2).le
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
      rcases hx1 with rfl | rfl | rfl
      · exact le_rfl
      · exact h3.le
      · exact (h3.trans h4).le
  have hzz : z₁ = z₂ := by
    apply le_antisymm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
      rcases hz1 with rfl | rfl | rfl
      · exact (h3.trans h4).le
      · exact h4.le
      · exact le_rfl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hz2
      rcases hz2 with rfl | rfl | rfl
      · exact (h1.trans h2).le
      · exact h2.le
      · exact le_rfl
  subst hxx; subst hzz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy1
  rcases hy1 with rfl | rfl | rfl
  · exact (lt_irrefl _ h1).elim
  · exact ⟨rfl, rfl, rfl⟩
  · exact (lt_irrefl _ h2).elim

private theorem orderedForces_iff_forces {n : ℕ} {α : Type} [LinearOrder α] :
    OrderedForces n α ↔ Forces 3 n α := by
  classical
  constructor
  · intro h c
    obtain ⟨S, hS, b, hb⟩ := h (fun x y z ↦ c {x, y, z})
    refine ⟨S, hS, b, ?_⟩
    intro e he hcard
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := triple_sorted hcard
    exact hb x (he (by simp)) y (he (by simp)) z (he (by simp)) hxy hyz
  · intro h c
    let c' : Finset α → Bool := fun e ↦
      if he : e.card = 3 then
        let h3 := triple_sorted he
        let x := h3.choose
        let y := h3.choose_spec.choose
        let z := h3.choose_spec.choose_spec.choose
        c x y z
      else false
    obtain ⟨S, hS, b, hb⟩ := h c'
    refine ⟨S, hS, b, ?_⟩
    intro x hx y hy z hz hxy hyz
    have hcard : ({x, y, z} : Finset α).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨x, y, z, ne_of_lt hxy, ne_of_lt (hxy.trans hyz), ne_of_lt hyz, rfl⟩
    have hsub : ({x, y, z} : Finset α) ⊆ S := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have hval := hb {x, y, z} hsub hcard
    dsimp only [c'] at hval
    rw [dif_pos hcard] at hval
    have hspec := (triple_sorted hcard).choose_spec.choose_spec.choose_spec
    obtain ⟨hx', hy', hz'⟩ := triple_sorted_unique hspec.1 hspec.2.1 hxy hyz hspec.2.2.symm
    have hceq : c (triple_sorted hcard).choose
        (triple_sorted hcard).choose_spec.choose
        (triple_sorted hcard).choose_spec.choose_spec.choose = c x y z := by
      congr 1
    exact hceq.symm.trans hval

private structure Cube (N : ℕ) where
  bits : Fin N → Bool
  deriving DecidableEq

private instance (N : ℕ) : Fintype (Cube N) :=
  Fintype.ofEquiv (Fin N → Bool)
    { toFun := Cube.mk
      invFun := Cube.bits
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

private theorem forces_cubeStruct_iff (r n N : ℕ) :
    Forces r n (Cube N) ↔ Forces r n (Fin N → Bool) :=
  ⟨forces_of_embedding ⟨Cube.bits, fun _ _ h ↦ by cases ‹Cube N›; cases ‹Cube N›; cases h; rfl⟩,
   forces_of_embedding ⟨Cube.mk, fun _ _ h ↦ congrArg Cube.bits h⟩⟩

private theorem cubeDelta_nonempty {N : ℕ} {x y : Cube N} (h : x ≠ y) :
    (Finset.univ.filter (fun i : Fin N ↦ x.bits i ≠ y.bits i)).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  apply h
  cases x with
  | mk xb =>
    cases y with
    | mk yb =>
      congr 1
      funext i
      by_contra hne'
      have hi : i ∈ Finset.univ.filter (fun j : Fin N ↦ xb j ≠ yb j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne'⟩
      rw [hne] at hi
      exact Finset.notMem_empty i hi

private noncomputable def cubeDelta {N : ℕ} {x y : Cube N} (h : x ≠ y) : Fin N :=
  (Finset.univ.filter (fun i : Fin N ↦ x.bits i ≠ y.bits i)).min' (cubeDelta_nonempty h)

private theorem cubeDelta_spec {N : ℕ} {x y : Cube N} (h : x ≠ y) :
    x.bits (cubeDelta h) ≠ y.bits (cubeDelta h) := by
  have hmem := Finset.min'_mem (Finset.univ.filter (fun i : Fin N ↦ x.bits i ≠ y.bits i))
    (cubeDelta_nonempty h)
  exact (Finset.mem_filter.mp hmem).2

private theorem cubeDelta_eq_of_lt {N : ℕ} {x y : Cube N} (h : x ≠ y)
    {j : Fin N} (hj : j < cubeDelta h) : x.bits j = y.bits j := by
  by_contra hne
  have hle : cubeDelta h ≤ j :=
    Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  exact not_lt_of_ge hle hj

private theorem cubeDelta_eq_iff {N : ℕ} {x y : Cube N} (h : x ≠ y) (i : Fin N) :
    cubeDelta h = i ↔ (∀ j < i, x.bits j = y.bits j) ∧ x.bits i ≠ y.bits i := by
  constructor
  · rintro rfl
    exact ⟨fun j hj ↦ cubeDelta_eq_of_lt h hj, cubeDelta_spec h⟩
  · rintro ⟨hpre, hdiff⟩
    apply le_antisymm
    · exact Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩)
    · by_contra hlt
      push Not at hlt
      exact cubeDelta_spec h (hpre _ hlt)

private theorem cubeDelta_symm {N : ℕ} {x y : Cube N} (h : x ≠ y) :
    cubeDelta h.symm = cubeDelta h := by
  rw [cubeDelta_eq_iff]
  exact ⟨fun j hj ↦ (cubeDelta_eq_of_lt h hj).symm, (cubeDelta_spec h).symm⟩

private def cubeLt {N : ℕ} (x y : Cube N) : Prop :=
  ∃ i : Fin N, (∀ j < i, x.bits j = y.bits j) ∧ x.bits i = false ∧ y.bits i = true

private theorem cubeLt_irrefl {N : ℕ} (x : Cube N) : ¬ cubeLt x x := by
  rintro ⟨i, _, h1, h2⟩
  rw [h1] at h2
  cases h2

private theorem cubeLt_trans {N : ℕ} {x y z : Cube N}
    (hxy : cubeLt x y) (hyz : cubeLt y z) : cubeLt x z := by
  obtain ⟨i, hi, hxi, hyi⟩ := hxy
  obtain ⟨j, hj, hyj, hzj⟩ := hyz
  rcases lt_trichotomy i j with hij | rfl | hji
  · refine ⟨i, fun k hk ↦ (hi k hk).trans (hj k (hk.trans hij)), hxi, ?_⟩
    rw [← hj i hij, hyi]
  · rw [hyi] at hyj; cases hyj
  · refine ⟨j, fun k hk ↦ (hi k (hk.trans hji)).trans (hj k hk), ?_, hzj⟩
    rw [hi j hji, hyj]

private theorem cubeLt_trichotomy {N : ℕ} (x y : Cube N) :
    cubeLt x y ∨ x = y ∨ cubeLt y x := by
  by_cases h : x = y
  · exact Or.inr (Or.inl h)
  · have hne := cubeDelta_spec h
    have hpre : ∀ j < cubeDelta h, x.bits j = y.bits j :=
      fun j hj ↦ cubeDelta_eq_of_lt h hj
    cases hx : x.bits (cubeDelta h) <;> cases hy : y.bits (cubeDelta h)
    · exact (hne (hx.trans hy.symm)).elim
    · exact Or.inl ⟨cubeDelta h, hpre, hx, hy⟩
    · exact Or.inr (Or.inr ⟨cubeDelta h, fun j hj ↦ (hpre j hj).symm, hy, hx⟩)
    · exact (hne (hx.trans hy.symm)).elim

private noncomputable instance (N : ℕ) : LinearOrder (Cube N) where
  le x y := x = y ∨ cubeLt x y
  lt := cubeLt
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | hxy
    · exact hyz
    · rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr (cubeLt_trans hxy hyz)
  lt_iff_le_not_ge x y := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (rfl | hyx)
      · exact cubeLt_irrefl _ h
      · exact cubeLt_irrefl _ (cubeLt_trans h hyx)
    · rintro ⟨rfl | h, hnot⟩
      · exact (hnot (Or.inl rfl)).elim
      · exact h
  le_antisymm x y hxy hyx := by
    rcases hxy with rfl | hxy
    · rfl
    · rcases hyx with rfl | hyx
      · rfl
      · exact (cubeLt_irrefl _ (cubeLt_trans hxy hyx)).elim
  le_total x y := by
    rcases cubeLt_trichotomy x y with h | rfl | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inr h)
  toDecidableLE := Classical.decRel _

private theorem cubeDelta_bits_of_lt {N : ℕ} {x y : Cube N} (h : x < y) :
    x.bits (cubeDelta (ne_of_lt h)) = false ∧ y.bits (cubeDelta (ne_of_lt h)) = true := by
  obtain ⟨i, hpre, hxi, hyi⟩ := h
  have hd : cubeDelta (ne_of_lt (show x < y from ⟨i, hpre, hxi, hyi⟩)) = i := by
    rw [cubeDelta_eq_iff]
    exact ⟨hpre, by rw [hxi, hyi]; decide⟩
  rw [hd]
  exact ⟨hxi, hyi⟩

private theorem cubeDelta_ne_of_lt_lt {N : ℕ} {x y z : Cube N}
    (hxy : x < y) (hyz : y < z) :
    cubeDelta (ne_of_lt hxy) ≠ cubeDelta (ne_of_lt hyz) := by
  intro heq
  have h1 := (cubeDelta_bits_of_lt hxy).2
  have h2 := (cubeDelta_bits_of_lt hyz).1
  rw [heq] at h1
  rw [h1] at h2
  cases h2

private theorem cubeDelta_min_of_lt_lt {N : ℕ} {x y z : Cube N}
    (hxy : x < y) (hyz : y < z) :
    cubeDelta (ne_of_lt (hxy.trans hyz)) =
      min (cubeDelta (ne_of_lt hxy)) (cubeDelta (ne_of_lt hyz)) := by
  set d₁ := cubeDelta (ne_of_lt hxy)
  set d₂ := cubeDelta (ne_of_lt hyz)
  have hne := cubeDelta_ne_of_lt_lt hxy hyz
  have h1 := cubeDelta_bits_of_lt hxy
  have h2 := cubeDelta_bits_of_lt hyz
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [min_eq_left hlt.le, cubeDelta_eq_iff]
    refine ⟨fun j hj ↦ (cubeDelta_eq_of_lt (ne_of_lt hxy) hj).trans
      (cubeDelta_eq_of_lt (ne_of_lt hyz) (hj.trans hlt)), ?_⟩
    rw [h1.1, ← cubeDelta_eq_of_lt (ne_of_lt hyz) hlt, h1.2]
    decide
  · rw [min_eq_right hgt.le, cubeDelta_eq_iff]
    refine ⟨fun j hj ↦ (cubeDelta_eq_of_lt (ne_of_lt hxy) (hj.trans hgt)).trans
      (cubeDelta_eq_of_lt (ne_of_lt hyz) hj), ?_⟩
    rw [cubeDelta_eq_of_lt (ne_of_lt hxy) hgt, h2.1, h2.2]
    decide

private noncomputable def deltaColor {N : ℕ} (φ ψ : Fin N → Fin N → Bool)
    (x y z : Cube N) : Bool :=
  if h : x < y ∧ y < z then
    let d₁ := cubeDelta (ne_of_lt h.1)
    let d₂ := cubeDelta (ne_of_lt h.2)
    if d₁ < d₂ then φ d₁ d₂ else ψ d₂ d₁
  else false

private def DeltaMonoOn {N : ℕ} (φ ψ : Fin N → Fin N → Bool)
    (A : Finset (Fin N)) (b : Bool) (S : Finset (Cube N)) : Prop :=
  S.Nonempty ∧
  (∀ x ∈ S, ∀ y ∈ S, (h : x ≠ y) → cubeDelta h ∈ A) ∧
  (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → deltaColor φ ψ x y z = b)

private theorem deltaMonoOn_singleton {N : ℕ} (φ ψ : Fin N → Fin N → Bool)
    (A : Finset (Fin N)) (b : Bool) :
    DeltaMonoOn φ ψ A b {⟨fun _ ↦ false⟩} := by
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact (hxy (hx.trans hy.symm)).elim
  · intro x hx y hy _ _ hxy _
    simp only [Finset.mem_singleton] at hx hy
    exact (ne_of_lt hxy (hx.trans hy.symm)).elim

private theorem deltaMonoOn_mono {N : ℕ} {φ ψ : Fin N → Fin N → Bool}
    {A B : Finset (Fin N)} {b : Bool} {S : Finset (Cube N)}
    (hAB : A ⊆ B) (hS : DeltaMonoOn φ ψ A b S) : DeltaMonoOn φ ψ B b S :=
  ⟨hS.1, fun x hx y hy hxy ↦ hAB (hS.2.1 x hx y hy hxy), hS.2.2⟩

private def setLeft {N : ℕ} (u : Fin N) (x : Cube N) : Cube N :=
  ⟨fun i ↦ if i ≤ u then false else x.bits i⟩

private def setRight {N : ℕ} (u : Fin N) (x : Cube N) : Cube N :=
  ⟨fun i ↦ if i < u then false else if i = u then true else x.bits i⟩

private theorem setLeft_lt_setRight {N : ℕ} (u : Fin N) (x y : Cube N) :
    setLeft u x < setRight u y := by
  refine ⟨u, ?_, ?_, ?_⟩
  · intro j hj
    simp [setLeft, setRight, hj.le, hj]
  · simp [setLeft]
  · simp [setRight]

private theorem cubeDelta_setLeft_setRight {N : ℕ} (u : Fin N) (x y : Cube N) :
    cubeDelta (ne_of_lt (setLeft_lt_setRight u x y)) = u := by
  rw [cubeDelta_eq_iff]
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · simp [setLeft, setRight, hj.le, hj]
  · simp [setLeft, setRight]

private theorem setLeft_delta_of_gt {N : ℕ} {u : Fin N} {x₁ x₂ : Cube N}
    (h : x₁ ≠ x₂) (hu : u < cubeDelta h) :
    ∃ h' : setLeft u x₁ ≠ setLeft u x₂, cubeDelta h' = cubeDelta h := by
  have hne : setLeft u x₁ ≠ setLeft u x₂ := by
    intro heq
    have hbit := congrArg (fun c : Cube N ↦ c.bits (cubeDelta h)) heq
    simp only [setLeft, not_le.mpr hu, ↓reduceIte] at hbit
    exact cubeDelta_spec h hbit
  refine ⟨hne, ?_⟩
  rw [cubeDelta_eq_iff]
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · by_cases hju : j ≤ u
    · simp [setLeft, hju]
    · simp only [setLeft, hju, ↓reduceIte]
      exact cubeDelta_eq_of_lt h hj
  · simp only [setLeft, not_le.mpr hu, ↓reduceIte]
    exact cubeDelta_spec h

private theorem setRight_delta_of_gt {N : ℕ} {u : Fin N} {x₁ x₂ : Cube N}
    (h : x₁ ≠ x₂) (hu : u < cubeDelta h) :
    ∃ h' : setRight u x₁ ≠ setRight u x₂, cubeDelta h' = cubeDelta h := by
  have hne : setRight u x₁ ≠ setRight u x₂ := by
    intro heq
    have hbit := congrArg (fun c : Cube N ↦ c.bits (cubeDelta h)) heq
    simp only [setRight, not_lt.mpr hu.le, ne_of_gt hu, ↓reduceIte] at hbit
    exact cubeDelta_spec h hbit
  refine ⟨hne, ?_⟩
  rw [cubeDelta_eq_iff]
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · by_cases hju : j < u
    · simp [setRight, hju]
    · by_cases hjeq : j = u
      · simp [setRight, hjeq]
      · simp only [setRight, hju, hjeq, ↓reduceIte]
        exact cubeDelta_eq_of_lt h hj
  · simp only [setRight, not_lt.mpr hu.le, ne_of_gt hu, ↓reduceIte]
    exact cubeDelta_spec h

private theorem setLeft_lt_iff_of_gt {N : ℕ} {u : Fin N} {x₁ x₂ : Cube N}
    (h : x₁ ≠ x₂) (hu : u < cubeDelta h) :
    setLeft u x₁ < setLeft u x₂ ↔ x₁ < x₂ := by
  obtain ⟨h', hd⟩ := setLeft_delta_of_gt h hu
  constructor
  · intro hlt
    have hbits := cubeDelta_bits_of_lt hlt
    rw [hd] at hbits
    simp only [setLeft, not_le.mpr hu, ↓reduceIte] at hbits
    exact ⟨cubeDelta h, fun j hj ↦ cubeDelta_eq_of_lt h hj, hbits.1, hbits.2⟩
  · intro hlt
    have hbits := cubeDelta_bits_of_lt hlt
    refine ⟨cubeDelta h, fun j hj ↦ ?_, ?_, ?_⟩
    · by_cases hju : j ≤ u
      · simp [setLeft, hju]
      · simp only [setLeft, hju, ↓reduceIte]
        exact cubeDelta_eq_of_lt h hj
    · simp only [setLeft, not_le.mpr hu, ↓reduceIte]
      exact hbits.1
    · simp only [setLeft, not_le.mpr hu, ↓reduceIte]
      exact hbits.2

private theorem setRight_lt_iff_of_gt {N : ℕ} {u : Fin N} {x₁ x₂ : Cube N}
    (h : x₁ ≠ x₂) (hu : u < cubeDelta h) :
    setRight u x₁ < setRight u x₂ ↔ x₁ < x₂ := by
  obtain ⟨h', hd⟩ := setRight_delta_of_gt h hu
  constructor
  · intro hlt
    have hbits := cubeDelta_bits_of_lt hlt
    rw [hd] at hbits
    simp only [setRight, not_lt.mpr hu.le, ne_of_gt hu, ↓reduceIte] at hbits
    exact ⟨cubeDelta h, fun j hj ↦ cubeDelta_eq_of_lt h hj, hbits.1, hbits.2⟩
  · intro hlt
    have hbits := cubeDelta_bits_of_lt hlt
    refine ⟨cubeDelta h, fun j hj ↦ ?_, ?_, ?_⟩
    · by_cases hju : j < u
      · simp [setRight, hju]
      · by_cases hjeq : j = u
        · simp [setRight, hjeq]
        · simp only [setRight, hju, hjeq, ↓reduceIte]
          exact cubeDelta_eq_of_lt h hj
    · simp only [setRight, not_lt.mpr hu.le, ne_of_gt hu, ↓reduceIte]
      exact hbits.1
    · simp only [setRight, not_lt.mpr hu.le, ne_of_gt hu, ↓reduceIte]
      exact hbits.2

private theorem deltaMonoOn_glue {N : ℕ} {φ ψ : Fin N → Fin N → Bool}
    {A L R : Finset (Fin N)} {u : Fin N} {b : Bool} {SL SR : Finset (Cube N)}
    (huA : u ∈ A) (humin : ∀ w ∈ A, u ≤ w)
    (hLA : L ⊆ A.erase u) (hRA : R ⊆ A.erase u)
    (hLψ : ∀ w ∈ L, ψ u w = b) (hRφ : ∀ w ∈ R, φ u w = b)
    (hSL : DeltaMonoOn φ ψ L b SL) (hSR : DeltaMonoOn φ ψ R b SR) :
    ∃ S : Finset (Cube N), DeltaMonoOn φ ψ A b S ∧ S.card = SL.card + SR.card := by
  classical
  have huL : ∀ w ∈ L, u < w := fun w hw ↦
    lt_of_le_of_ne (humin w (Finset.mem_of_mem_erase (hLA hw)))
      (Finset.ne_of_mem_erase (hLA hw)).symm
  have huR : ∀ w ∈ R, u < w := fun w hw ↦
    lt_of_le_of_ne (humin w (Finset.mem_of_mem_erase (hRA hw)))
      (Finset.ne_of_mem_erase (hRA hw)).symm
  let SL' := SL.image (setLeft u)
  let SR' := SR.image (setRight u)
  refine ⟨SL' ∪ SR', ?_, ?_⟩
  · refine ⟨(hSL.1.image _).mono Finset.subset_union_left, ?_, ?_⟩
    · intro p hp q hq hpq
      rcases Finset.mem_union.mp hp with hpL | hpR <;>
      rcases Finset.mem_union.mp hq with hqL | hqR
      · obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hpL
        obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hqL
        have hne : x₁ ≠ x₂ := fun h ↦ hpq (by rw [h])
        have hdL := hSL.2.1 x₁ hx₁ x₂ hx₂ hne
        obtain ⟨_, hd⟩ := setLeft_delta_of_gt hne (huL _ hdL)
        exact Finset.mem_of_mem_erase (hLA (hd ▸ hdL))
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hpL
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hqR
        rw [cubeDelta_setLeft_setRight]
        exact huA
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hpR
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hqL
        have hlr : setLeft u x ≠ setRight u y := ne_of_lt (setLeft_lt_setRight u x y)
        rw [show cubeDelta hpq = cubeDelta hlr from cubeDelta_symm hlr,
          cubeDelta_setLeft_setRight]
        exact huA
      · obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.mp hpR
        obtain ⟨y₂, hy₂, rfl⟩ := Finset.mem_image.mp hqR
        have hne : y₁ ≠ y₂ := fun h ↦ hpq (by rw [h])
        have hdR := hSR.2.1 y₁ hy₁ y₂ hy₂ hne
        obtain ⟨_, hd⟩ := setRight_delta_of_gt hne (huR _ hdR)
        exact Finset.mem_of_mem_erase (hRA (hd ▸ hdR))
    · intro p hp q hq r hr hpq hqr
      rcases Finset.mem_union.mp hp with hpL | hpR <;>
      rcases Finset.mem_union.mp hq with hqL | hqR <;>
      rcases Finset.mem_union.mp hr with hrL | hrR
      · obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hpL
        obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hqL
        obtain ⟨x₃, hx₃, rfl⟩ := Finset.mem_image.mp hrL
        have h12ne : x₁ ≠ x₂ := fun h ↦ ne_of_lt hpq (by rw [h])
        have h23ne : x₂ ≠ x₃ := fun h ↦ ne_of_lt hqr (by rw [h])
        have hd12 := hSL.2.1 x₁ hx₁ x₂ hx₂ h12ne
        have hd23 := hSL.2.1 x₂ hx₂ x₃ hx₃ h23ne
        have hx12 : x₁ < x₂ := (setLeft_lt_iff_of_gt h12ne (huL _ hd12)).mp hpq
        have hx23 : x₂ < x₃ := (setLeft_lt_iff_of_gt h23ne (huL _ hd23)).mp hqr
        obtain ⟨_, heq12⟩ := setLeft_delta_of_gt h12ne (huL _ hd12)
        obtain ⟨_, heq23⟩ := setLeft_delta_of_gt h23ne (huL _ hd23)
        have horig := hSL.2.2 x₁ hx₁ x₂ hx₂ x₃ hx₃ hx12 hx23
        simp only [deltaColor, hpq, hqr, hx12, hx23, and_self, ↓reduceDIte] at horig ⊢
        simpa [heq12, heq23] using horig
      · obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hpL
        obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hqL
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hrR
        have h12ne : x₁ ≠ x₂ := fun h ↦ ne_of_lt hpq (by rw [h])
        have hd12 := hSL.2.1 x₁ hx₁ x₂ hx₂ h12ne
        have hu12 := huL _ hd12
        obtain ⟨_, heq12⟩ := setLeft_delta_of_gt h12ne hu12
        have heq23 : cubeDelta (ne_of_lt hqr) = u := cubeDelta_setLeft_setRight u x₂ y
        simp only [deltaColor, hpq, hqr, and_self, ↓reduceDIte, heq12, heq23,
          not_lt.mpr hu12.le, ↓reduceIte]
        exact hLψ _ hd12
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hrL
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hqR
        exact (lt_asymm hqr (setLeft_lt_setRight u x y)).elim
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hpL
        obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.mp hqR
        obtain ⟨y₂, hy₂, rfl⟩ := Finset.mem_image.mp hrR
        have h12ne : y₁ ≠ y₂ := fun h ↦ ne_of_lt hqr (by rw [h])
        have hd12 := hSR.2.1 y₁ hy₁ y₂ hy₂ h12ne
        have hu12 := huR _ hd12
        obtain ⟨_, heq23⟩ := setRight_delta_of_gt h12ne hu12
        have heq12 : cubeDelta (ne_of_lt hpq) = u := cubeDelta_setLeft_setRight u x y₁
        simp only [deltaColor, hpq, hqr, and_self, ↓reduceDIte, heq12, heq23, hu12, ↓reduceIte]
        exact hRφ _ hd12
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hpR
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hqL
        exact (lt_asymm hpq (setLeft_lt_setRight u x y)).elim
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hpR
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hqL
        exact (lt_asymm hpq (setLeft_lt_setRight u x y)).elim
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hqR
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hrL
        exact (lt_asymm hqr (setLeft_lt_setRight u x y)).elim
      · obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.mp hpR
        obtain ⟨y₂, hy₂, rfl⟩ := Finset.mem_image.mp hqR
        obtain ⟨y₃, hy₃, rfl⟩ := Finset.mem_image.mp hrR
        have h12ne : y₁ ≠ y₂ := fun h ↦ ne_of_lt hpq (by rw [h])
        have h23ne : y₂ ≠ y₃ := fun h ↦ ne_of_lt hqr (by rw [h])
        have hd12 := hSR.2.1 y₁ hy₁ y₂ hy₂ h12ne
        have hd23 := hSR.2.1 y₂ hy₂ y₃ hy₃ h23ne
        have hy12 : y₁ < y₂ := (setRight_lt_iff_of_gt h12ne (huR _ hd12)).mp hpq
        have hy23 : y₂ < y₃ := (setRight_lt_iff_of_gt h23ne (huR _ hd23)).mp hqr
        obtain ⟨_, heq12⟩ := setRight_delta_of_gt h12ne (huR _ hd12)
        obtain ⟨_, heq23⟩ := setRight_delta_of_gt h23ne (huR _ hd23)
        have horig := hSR.2.2 y₁ hy₁ y₂ hy₂ y₃ hy₃ hy12 hy23
        simp only [deltaColor, hpq, hqr, hy12, hy23, and_self, ↓reduceDIte] at horig ⊢
        simpa [heq12, heq23] using horig
  · have hdisj : Disjoint SL' SR' := by
      rw [Finset.disjoint_left]
      intro z hzL hzR
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hzL
      obtain ⟨y, _, heq⟩ := Finset.mem_image.mp hzR
      have hlt := setLeft_lt_setRight u x y
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    have hcardL : SL'.card = SL.card := by
      apply Finset.card_image_of_injOn
      intro x₁ hx₁ x₂ hx₂ heq
      by_contra hne
      obtain ⟨h', _⟩ := setLeft_delta_of_gt hne (huL _ (hSL.2.1 x₁ hx₁ x₂ hx₂ hne))
      exact h' heq
    have hcardR : SR'.card = SR.card := by
      apply Finset.card_image_of_injOn
      intro y₁ hy₁ y₂ hy₂ heq
      by_contra hne
      obtain ⟨h', _⟩ := setRight_delta_of_gt hne (huR _ (hSR.2.1 y₁ hy₁ y₂ hy₂ hne))
      exact h' heq
    rw [Finset.card_union_of_disjoint hdisj, hcardL, hcardR]

open Classical in
private noncomputable def maxDeltaMono {N : ℕ} (φ ψ : Fin N → Fin N → Bool)
    (A : Finset (Fin N)) (b : Bool) : ℕ :=
  let C := Finset.univ.filter (fun S : Finset (Cube N) ↦ DeltaMonoOn φ ψ A b S)
  (C.image Finset.card).max' <| by
    refine ⟨1, Finset.mem_image.mpr ⟨{⟨fun _ ↦ false⟩}, ?_, by simp⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, deltaMonoOn_singleton φ ψ A b⟩

open Classical in
private theorem exists_maxDeltaMono {N : ℕ} (φ ψ : Fin N → Fin N → Bool)
    (A : Finset (Fin N)) (b : Bool) :
    ∃ S : Finset (Cube N), DeltaMonoOn φ ψ A b S ∧ S.card = maxDeltaMono φ ψ A b := by
  let C := Finset.univ.filter (fun S : Finset (Cube N) ↦ DeltaMonoOn φ ψ A b S)
  have hmem := Finset.max'_mem (C.image Finset.card) (by
    refine ⟨1, Finset.mem_image.mpr ⟨{⟨fun _ ↦ false⟩}, ?_, by simp⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, deltaMonoOn_singleton φ ψ A b⟩)
  obtain ⟨S, hS, hcard⟩ := Finset.mem_image.mp hmem
  exact ⟨S, (Finset.mem_filter.mp hS).2, hcard⟩

open Classical in
private theorem le_maxDeltaMono {N : ℕ} {φ ψ : Fin N → Fin N → Bool}
    {A : Finset (Fin N)} {b : Bool} {S : Finset (Cube N)}
    (hS : DeltaMonoOn φ ψ A b S) : S.card ≤ maxDeltaMono φ ψ A b := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩, rfl⟩

private theorem one_le_maxDeltaMono {N : ℕ} (φ ψ : Fin N → Fin N → Bool)
    (A : Finset (Fin N)) (b : Bool) : 1 ≤ maxDeltaMono φ ψ A b := by
  have h := le_maxDeltaMono (deltaMonoOn_singleton φ ψ A b)
  simpa using h

private theorem maxDeltaMono_mono {N : ℕ} (φ ψ : Fin N → Fin N → Bool)
    {A B : Finset (Fin N)} (hAB : A ⊆ B) (b : Bool) :
    maxDeltaMono φ ψ A b ≤ maxDeltaMono φ ψ B b := by
  obtain ⟨S, hS, hcard⟩ := exists_maxDeltaMono φ ψ A b
  rw [← hcard]
  exact le_maxDeltaMono (deltaMonoOn_mono hAB hS)

private theorem quad_pair_bound_ordered {a b a₀ a₁ a₂ b₁ b₂ b₃ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (ha20 : 2 * a₀ ≤ a) (ha01 : a₀ + a₁ ≤ a) (ha12 : a₁ + a₂ ≤ a)
    (hb23 : 2 * b₃ ≤ b) (hb31 : b₃ + b₁ ≤ b) (hb12 : b₁ + b₂ ≤ b)
    (hordA : a₂ ≤ a₁) (hordB : b₂ ≤ b₁) :
    a₁ * b₁ + a₂ * b₂ ≤ (a - a₀) * (b - b₃) + a₀ * b₃ := by
  by_cases hA : a₁ ≤ a₀
  · nlinarith
  · push Not at hA
    by_cases hB : b₁ ≤ b₃
    · nlinarith
    · push Not at hB
      have hu : 0 ≤ a - a₀ - a₁ := by linarith
      have hv : 0 ≤ b - b₃ - b₁ := by linarith
      have ha2' : a₂ ≤ a₀ + (a - a₀ - a₁) := by linarith
      have hb2' : b₂ ≤ b₃ + (b - b₃ - b₁) := by linarith
      have hprod : a₂ * b₂ ≤ (a₀ + (a - a₀ - a₁)) * (b₃ + (b - b₃ - b₁)) :=
        mul_le_mul ha2' hb2' hb₂ (by linarith)
      nlinarith

private theorem quad_pair_bound {a b a₀ a₁ a₂ b₁ b₂ b₃ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (ha20 : 2 * a₀ ≤ a) (ha01 : a₀ + a₁ ≤ a) (ha02 : a₀ + a₂ ≤ a) (ha12 : a₁ + a₂ ≤ a)
    (hb23 : 2 * b₃ ≤ b) (hb31 : b₃ + b₁ ≤ b) (hb32 : b₃ + b₂ ≤ b) (hb12 : b₁ + b₂ ≤ b) :
    a₁ * b₁ + a₂ * b₂ ≤ (a - a₀) * (b - b₃) + a₀ * b₃ := by
  rcases le_total a₂ a₁ with hA | hA <;> rcases le_total b₂ b₁ with hB | hB
  · exact quad_pair_bound_ordered ha₀ ha₁ ha₂ hb₁ hb₂ hb₃ ha20 ha01 ha12 hb23 hb31 hb12 hA hB
  · have hrearr : a₁ * b₁ + a₂ * b₂ ≤ a₁ * b₂ + a₂ * b₁ := by nlinarith
    have hbd := quad_pair_bound_ordered ha₀ ha₁ ha₂ hb₂ hb₁ hb₃ ha20 ha01 ha12 hb23 hb32
      (by linarith) hA hB
    linarith
  · have hrearr : a₁ * b₁ + a₂ * b₂ ≤ a₂ * b₁ + a₁ * b₂ := by nlinarith
    have hbd := quad_pair_bound_ordered ha₀ ha₂ ha₁ hb₁ hb₂ hb₃ ha20 ha02 (by linarith)
      hb23 hb31 hb12 hA hB
    linarith
  · have hbd := quad_pair_bound_ordered ha₀ ha₂ ha₁ hb₂ hb₁ hb₃ ha20 ha02 (by linarith)
      hb23 hb32 (by linarith) hA hB
    linarith

private theorem quad_unit_ineq {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    x ^ 2 + y ^ 2 + ((1 - x) * (1 - y) + x * y) ^ 2 ≤ 1 := by
  set s := x + y
  set p := x * y
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hp0 : 0 ≤ p := mul_nonneg hx0 hy0
  have hps : 4 * p ≤ s ^ 2 := by
    have : 0 ≤ (x - y) ^ 2 := sq_nonneg _
    dsimp [s, p]
    nlinarith
  have hdiff : 1 - (x ^ 2 + y ^ 2 + ((1 - x) * (1 - y) + x * y) ^ 2) =
      2 * s * (1 - s) - 2 * p * (1 - 2 * s + 2 * p) := by
    dsimp [s, p]; ring
  suffices h : 0 ≤ 2 * s * (1 - s) - 2 * p * (1 - 2 * s + 2 * p) by linarith
  by_cases hsign : 1 - 2 * s + 2 * p ≤ 0
  · nlinarith
  · push Not at hsign
    have h1 : 2 * p ≤ s ^ 2 / 2 := by linarith
    have h2 : 1 - 2 * s + 2 * p ≤ 1 - 2 * s + s ^ 2 / 2 := by linarith
    have hmul : 2 * p * (1 - 2 * s + 2 * p) ≤ (s ^ 2 / 2) * (1 - 2 * s + s ^ 2 / 2) :=
      mul_le_mul h1 h2 hsign.le (by positivity)
    have hpoly : 2 * s * (1 - s) - (s ^ 2 / 2) * (1 - 2 * s + s ^ 2 / 2) =
        s / 4 * ((1 - s) * (7 + (1 - s) ^ 2 + s ^ 2) + s ^ 3) := by ring
    have hnonneg : 0 ≤ s / 4 * ((1 - s) * (7 + (1 - s) ^ 2 + s ^ 2) + s ^ 3) := by
      have h1s : 0 ≤ 1 - s := by linarith
      positivity
    linarith

private theorem quad_nat_ineq {a b a₀ a₁ a₂ b₁ b₂ b₃ : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha20 : a₀ + a₀ ≤ a) (ha01 : a₀ + a₁ ≤ a) (ha02 : a₀ + a₂ ≤ a) (ha12 : a₁ + a₂ ≤ a)
    (hb23 : b₃ + b₃ ≤ b) (hb31 : b₃ + b₁ ≤ b) (hb32 : b₃ + b₂ ≤ b) (hb12 : b₁ + b₂ ≤ b) :
    a₀ ^ 2 * b ^ 2 + a₁ ^ 2 * b₁ ^ 2 + a₂ ^ 2 * b₂ ^ 2 + a ^ 2 * b₃ ^ 2 ≤ a ^ 2 * b ^ 2 := by
  have hR : ((a₀ : ℝ) ^ 2 * (b : ℝ) ^ 2 + (a₁ : ℝ) ^ 2 * (b₁ : ℝ) ^ 2 +
      (a₂ : ℝ) ^ 2 * (b₂ : ℝ) ^ 2 + (a : ℝ) ^ 2 * (b₃ : ℝ) ^ 2) ≤ (a : ℝ) ^ 2 * (b : ℝ) ^ 2 := by
    have haR : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hpair : (a₁ : ℝ) * b₁ + (a₂ : ℝ) * b₂ ≤
        ((a : ℝ) - a₀) * ((b : ℝ) - b₃) + (a₀ : ℝ) * b₃ :=
      quad_pair_bound (by positivity) (by positivity) (by positivity)
        (by positivity) (by positivity) (by positivity)
        (by exact_mod_cast (by omega : 2 * a₀ ≤ a))
        (by exact_mod_cast ha01) (by exact_mod_cast ha02) (by exact_mod_cast ha12)
        (by exact_mod_cast (by omega : 2 * b₃ ≤ b))
        (by exact_mod_cast hb31) (by exact_mod_cast hb32) (by exact_mod_cast hb12)
    have hsq : (a₁ : ℝ) ^ 2 * (b₁ : ℝ) ^ 2 + (a₂ : ℝ) ^ 2 * (b₂ : ℝ) ^ 2 ≤
        (((a : ℝ) - a₀) * ((b : ℝ) - b₃) + (a₀ : ℝ) * b₃) ^ 2 := by
      have hnonneg : (0 : ℝ) ≤ (a₁ : ℝ) * b₁ + (a₂ : ℝ) * b₂ := by positivity
      have h1 : (a₁ : ℝ) ^ 2 * (b₁ : ℝ) ^ 2 + (a₂ : ℝ) ^ 2 * (b₂ : ℝ) ^ 2 ≤
          ((a₁ : ℝ) * b₁ + (a₂ : ℝ) * b₂) ^ 2 := by
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ a₁ * b₁)
          (by positivity : (0 : ℝ) ≤ a₂ * b₂)]
      have h2 : ((a₁ : ℝ) * b₁ + (a₂ : ℝ) * b₂) ^ 2 ≤
          (((a : ℝ) - a₀) * ((b : ℝ) - b₃) + (a₀ : ℝ) * b₃) ^ 2 := by
        nlinarith
      linarith
    have hx1 : (a₀ : ℝ) / a ≤ 1 / 2 := by
      rw [div_le_div_iff₀ haR (by norm_num : (0 : ℝ) < 2)]
      have h2a : ((a₀ + a₀ : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha20
      push_cast at h2a
      linarith
    have hy1 : (b₃ : ℝ) / b ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hbR (by norm_num : (0 : ℝ) < 2)]
      have h2b : ((b₃ + b₃ : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb23
      push_cast at h2b
      linarith
    have hunit := quad_unit_ineq (div_nonneg (by positivity) haR.le) hx1
      (div_nonneg (by positivity) hbR.le) hy1
    have hscaled : ((a₀ : ℝ) ^ 2 * (b : ℝ) ^ 2 + (a : ℝ) ^ 2 * (b₃ : ℝ) ^ 2 +
        (((a : ℝ) - a₀) * ((b : ℝ) - b₃) + (a₀ : ℝ) * b₃) ^ 2) ≤ (a : ℝ) ^ 2 * (b : ℝ) ^ 2 := by
      have hab2 : (0 : ℝ) < (a : ℝ) ^ 2 * (b : ℝ) ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_right hunit hab2.le
      have heq : (((a₀ : ℝ) / a) ^ 2 + ((b₃ : ℝ) / b) ^ 2 +
          ((1 - (a₀ : ℝ) / a) * (1 - (b₃ : ℝ) / b) + (a₀ : ℝ) / a * ((b₃ : ℝ) / b)) ^ 2) *
          ((a : ℝ) ^ 2 * (b : ℝ) ^ 2) =
          (a₀ : ℝ) ^ 2 * (b : ℝ) ^ 2 + (a : ℝ) ^ 2 * (b₃ : ℝ) ^ 2 +
          (((a : ℝ) - a₀) * ((b : ℝ) - b₃) + (a₀ : ℝ) * b₃) ^ 2 := by
        field_simp [haR.ne', hbR.ne']
      linarith
    linarith
  exact_mod_cast hR

private theorem card_le_maxDeltaMono_sq {N : ℕ} (φ ψ : Fin N → Fin N → Bool) :
    ∀ A : Finset (Fin N),
      A.card + 1 ≤ (maxDeltaMono φ ψ A false) ^ 2 * (maxDeltaMono φ ψ A true) ^ 2 := by
  classical
  intro A
  induction hcard : A.card using Nat.strong_induction_on generalizing A with
  | h m ih =>
    by_cases hne : A.Nonempty
    · let u := A.min' hne
      have huA : u ∈ A := Finset.min'_mem A hne
      have humin : ∀ w ∈ A, u ≤ w := fun w hw ↦ Finset.min'_le A w hw
      let B := A.erase u
      have hBA : B.card + 1 = A.card := Finset.card_erase_add_one huA
      let X00 := B.filter (fun w ↦ ψ u w = false ∧ φ u w = false)
      let X01 := B.filter (fun w ↦ ψ u w = false ∧ φ u w = true)
      let X10 := B.filter (fun w ↦ ψ u w = true ∧ φ u w = false)
      let X11 := B.filter (fun w ↦ ψ u w = true ∧ φ u w = true)
      have hBsplit : X00.card + X01.card + X10.card + X11.card = B.card := by
        have hL := Finset.card_filter_add_card_filter_not (s := B) (p := fun w ↦ ψ u w = false)
        have h0 := Finset.card_filter_add_card_filter_not
          (s := B.filter (fun w ↦ ψ u w = false)) (p := fun w ↦ φ u w = false)
        have h1 := Finset.card_filter_add_card_filter_not
          (s := B.filter (fun w ↦ ¬ ψ u w = false)) (p := fun w ↦ φ u w = false)
        have e00 : (B.filter (fun w ↦ ψ u w = false)).filter (fun w ↦ φ u w = false) = X00 := by
          ext w; simp [X00, and_assoc]
        have e01 : (B.filter (fun w ↦ ψ u w = false)).filter (fun w ↦ ¬ φ u w = false) = X01 := by
          ext w; simp [X01, and_assoc]
        have e10 : (B.filter (fun w ↦ ¬ ψ u w = false)).filter (fun w ↦ φ u w = false) = X10 := by
          ext w; simp [X10, and_assoc]
        have e11 : (B.filter (fun w ↦ ¬ ψ u w = false)).filter (fun w ↦ ¬ φ u w = false) = X11 := by
          ext w; simp [X11, and_assoc]
        rw [e00, e01] at h0
        rw [e10, e11] at h1
        omega
      have hlt (X : Finset (Fin N)) (hXB : X ⊆ B) : X.card < m := by
        have := Finset.card_le_card hXB
        omega
      have ih00 := ih X00.card (hlt X00 (Finset.filter_subset _ _)) X00 rfl
      have ih01 := ih X01.card (hlt X01 (Finset.filter_subset _ _)) X01 rfl
      have ih10 := ih X10.card (hlt X10 (Finset.filter_subset _ _)) X10 rfl
      have ih11 := ih X11.card (hlt X11 (Finset.filter_subset _ _)) X11 rfl
      let L0 := B.filter (fun w ↦ ψ u w = false)
      let R0 := B.filter (fun w ↦ φ u w = false)
      let L1 := B.filter (fun w ↦ ψ u w = true)
      let R1 := B.filter (fun w ↦ φ u w = true)
      have hstep0 : maxDeltaMono φ ψ L0 false + maxDeltaMono φ ψ R0 false ≤
          maxDeltaMono φ ψ A false := by
        obtain ⟨SL, hSL, hcL⟩ := exists_maxDeltaMono φ ψ L0 false
        obtain ⟨SR, hSR, hcR⟩ := exists_maxDeltaMono φ ψ R0 false
        obtain ⟨S, hS, hcS⟩ := deltaMonoOn_glue huA humin
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          (fun w hw ↦ (Finset.mem_filter.mp hw).2) (fun w hw ↦ (Finset.mem_filter.mp hw).2)
          hSL hSR
        have hle := le_maxDeltaMono hS
        omega
      have hstep1 : maxDeltaMono φ ψ L1 true + maxDeltaMono φ ψ R1 true ≤
          maxDeltaMono φ ψ A true := by
        obtain ⟨SL, hSL, hcL⟩ := exists_maxDeltaMono φ ψ L1 true
        obtain ⟨SR, hSR, hcR⟩ := exists_maxDeltaMono φ ψ R1 true
        obtain ⟨S, hS, hcS⟩ := deltaMonoOn_glue huA humin
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          (fun w hw ↦ (Finset.mem_filter.mp hw).2) (fun w hw ↦ (Finset.mem_filter.mp hw).2)
          hSL hSR
        have hle := le_maxDeltaMono hS
        omega
      have sub00L0 : X00 ⊆ L0 := fun w hw ↦ by
        simp only [X00, L0, Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.1⟩
      have sub00R0 : X00 ⊆ R0 := fun w hw ↦ by
        simp only [X00, R0, Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.2⟩
      have sub01L0 : X01 ⊆ L0 := fun w hw ↦ by
        simp only [X01, L0, Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.1⟩
      have sub10R0 : X10 ⊆ R0 := fun w hw ↦ by
        simp only [X10, R0, Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.2⟩
      have sub11L1 : X11 ⊆ L1 := fun w hw ↦ by
        simp only [X11, L1, Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.1⟩
      have sub11R1 : X11 ⊆ R1 := fun w hw ↦ by
        simp only [X11, R1, Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.2⟩
      have sub10L1 : X10 ⊆ L1 := fun w hw ↦ by
        simp only [X10, L1, Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.1⟩
      have sub01R1 : X01 ⊆ R1 := fun w hw ↦ by
        simp only [X01, R1, Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.2⟩
      have sub00A : X00 ⊆ A := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have sub11A : X11 ⊆ A := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have ha0L := maxDeltaMono_mono φ ψ sub00L0 false
      have ha0R := maxDeltaMono_mono φ ψ sub00R0 false
      have ha1L := maxDeltaMono_mono φ ψ sub01L0 false
      have ha2R := maxDeltaMono_mono φ ψ sub10R0 false
      have hb3L := maxDeltaMono_mono φ ψ sub11L1 true
      have hb3R := maxDeltaMono_mono φ ψ sub11R1 true
      have hb2L := maxDeltaMono_mono φ ψ sub10L1 true
      have hb1R := maxDeltaMono_mono φ ψ sub01R1 true
      have hb0A := maxDeltaMono_mono φ ψ sub00A true
      have ha3A := maxDeltaMono_mono φ ψ sub11A false
      have h00' : X00.card + 1 ≤ (maxDeltaMono φ ψ X00 false) ^ 2 * (maxDeltaMono φ ψ A true) ^ 2 :=
        ih00.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb0A 2))
      have h11' : X11.card + 1 ≤ (maxDeltaMono φ ψ A false) ^ 2 * (maxDeltaMono φ ψ X11 true) ^ 2 :=
        ih11.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ha3A 2))
      have hquad := quad_nat_ineq
        (a := maxDeltaMono φ ψ A false) (b := maxDeltaMono φ ψ A true)
        (a₀ := maxDeltaMono φ ψ X00 false) (a₁ := maxDeltaMono φ ψ X01 false)
        (a₂ := maxDeltaMono φ ψ X10 false) (b₁ := maxDeltaMono φ ψ X01 true)
        (b₂ := maxDeltaMono φ ψ X10 true) (b₃ := maxDeltaMono φ ψ X11 true)
        (one_le_maxDeltaMono φ ψ A false) (one_le_maxDeltaMono φ ψ A true)
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp only [Finset.card_empty] at hcard
      subst hcard
      have h0 := one_le_maxDeltaMono φ ψ ∅ false
      have h1 := one_le_maxDeltaMono φ ψ ∅ true
      have hmul : 1 * 1 ≤ (maxDeltaMono φ ψ ∅ false) ^ 2 * (maxDeltaMono φ ψ ∅ true) ^ 2 :=
        Nat.mul_le_mul (by nlinarith) (by nlinarith)
      simpa using hmul

/-- No-go theorem for pure-delta 2-colourings on the N-dimensional binary cube:
every 2-colouring depending only on (delta_1 < delta_2, delta_1, delta_2) admits
a monochromatic set S with N + 1 <= S.card ^ 4. -/
private theorem deltaColor_fourth_power_mono {N : ℕ} (φ ψ : Fin N → Fin N → Bool) :
    ∃ S : Finset (Cube N), N + 1 ≤ S.card ^ 4 ∧
      ∃ b : Bool, ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → deltaColor φ ψ x y z = b := by
  have h := card_le_maxDeltaMono_sq φ ψ Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h
  obtain ⟨S₀, hS₀, hc₀⟩ := exists_maxDeltaMono φ ψ Finset.univ false
  obtain ⟨S₁, hS₁, hc₁⟩ := exists_maxDeltaMono φ ψ Finset.univ true
  rw [← hc₀, ← hc₁] at h
  rcases le_total S₀.card S₁.card with hle | hle
  · refine ⟨S₁, ?_, true, hS₁.2.2⟩
    calc
      N + 1 ≤ S₀.card ^ 2 * S₁.card ^ 2 := h
      _ ≤ S₁.card ^ 2 * S₁.card ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hle 2)
      _ = S₁.card ^ 4 := by ring
  · refine ⟨S₀, ?_, false, hS₀.2.2⟩
    calc
      N + 1 ≤ S₀.card ^ 2 * S₁.card ^ 2 := h
      _ ≤ S₀.card ^ 2 * S₀.card ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle 2)
      _ = S₀.card ^ 4 := by ring

private theorem deltaColor_fails_cubeWitness (k : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ φ ψ : Fin (2 ^ t) → Fin (2 ^ t) → Bool,
      ∃ S : Finset (Cube (2 ^ t)), S.card = k * t ∧
        ∃ b : Bool, ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → deltaColor φ ψ x y z = b := by
  have hgrow : Tendsto (fun t : ℕ ↦ ((k * t : ℕ) : ℝ) ^ 4 / (2 : ℝ) ^ t) atTop (nhds 0) := by
    have hpow : Tendsto (fun t : ℕ ↦ (t : ℝ) ^ 4 / (2 : ℝ) ^ t) atTop (nhds 0) := by
      simpa using tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num : (1 : ℝ) < 2)
    have hconst : Tendsto (fun t : ℕ ↦ ((k : ℝ) ^ 4) * ((t : ℝ) ^ 4 / (2 : ℝ) ^ t))
        atTop (nhds ((k : ℝ) ^ 4 * 0)) := hpow.const_mul ((k : ℝ) ^ 4)
    rw [mul_zero] at hconst
    refine hconst.congr fun t ↦ ?_
    push_cast
    ring
  have hlt : ∀ᶠ t : ℕ in atTop, ((k * t : ℕ) : ℝ) ^ 4 / (2 : ℝ) ^ t < 1 :=
    hgrow.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlt] with t ht φ ψ
  have hpow_lt : (k * t) ^ 4 < 2 ^ t := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
    have hR : ((k * t : ℕ) : ℝ) ^ 4 < (2 : ℝ) ^ t := by
      simpa using (div_lt_one hpos).mp ht
    exact_mod_cast hR
  obtain ⟨S, hS4, b, hb⟩ := deltaColor_fourth_power_mono φ ψ
  have hle : k * t ≤ S.card := by
    by_contra hlt'
    push Not at hlt'
    have h4 : S.card ^ 4 ≤ (k * t) ^ 4 := Nat.pow_le_pow_left hlt'.le 4
    omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hle
  exact ⟨T, hTcard, b, fun x hx y hy z hz hxy hyz ↦ hb x (hTS hx) y (hTS hy) z (hTS hz) hxy hyz⟩

/- General finite counting lower bound (Erdos 1947 graph seed and EHR 1965 baseline). -/

private theorem not_forces_of_count {r n m : ℕ} (hcount : 2 * m.choose n < 2 ^ n.choose r) :
    ¬ Forces r n (Fin m) := by
  classical
  by_cases hmn : m < n
  · intro hf
    obtain ⟨S, hS, _, _⟩ := hf (fun _ ↦ false)
    have hle : S.card ≤ m := by
      simpa using Finset.card_le_univ S
    omega
  · push Not at hmn
    let V : Finset (Fin m) := Finset.univ
    let E := V.powersetCard r
    let F := V.powersetCard n
    let inS (S : Finset (Fin m)) := S.powersetCard r
    let free (S : Finset (Fin m)) := (E \ inS S).powerset
    let bad (S : Finset (Fin m)) := free S ∪ (free S).image (· ∪ inS S)
    have hEcard : E.card = m.choose r := by simp [E, V]
    have hFcard : F.card = m.choose n := by simp [F, V]
    have hnr : n.choose r ≤ E.card := by
      rw [hEcard]
      exact Nat.choose_le_choose r hmn
    have hbad_le (S : Finset (Fin m)) (hS : S ∈ F) :
        (bad S).card ≤ 2 * 2 ^ (E.card - n.choose r) := by
      obtain ⟨hSV, hScard⟩ := Finset.mem_powersetCard.mp hS
      have hsub : inS S ⊆ E := Finset.powersetCard_mono hSV
      have hfree : (free S).card = 2 ^ (E.card - n.choose r) := by
        simp [free, Finset.card_sdiff_of_subset hsub, inS, hScard]
      have hu := Finset.card_union_le (free S) ((free S).image (· ∪ inS S))
      have hi : ((free S).image (· ∪ inS S)).card ≤ (free S).card := Finset.card_image_le
      dsimp only [bad]
      omega
    have htotal : (F.biUnion bad).card < E.powerset.card := by
      calc
        (F.biUnion bad).card ≤ F.card * (2 * 2 ^ (E.card - n.choose r)) :=
          Finset.card_biUnion_le_card_mul F bad _ hbad_le
        _ = (2 * m.choose n) * 2 ^ (E.card - n.choose r) := by rw [hFcard]; ring
        _ < 2 ^ n.choose r * 2 ^ (E.card - n.choose r) :=
          Nat.mul_lt_mul_of_pos_right hcount (by positivity)
        _ = 2 ^ E.card := by rw [← pow_add, Nat.add_sub_of_le hnr]
        _ = E.powerset.card := (Finset.card_powerset E).symm
    obtain ⟨G, hGE, hGnot⟩ := Finset.exists_mem_notMem_of_card_lt_card htotal
    have hGsub : G ⊆ E := Finset.mem_powerset.mp hGE
    intro hf
    obtain ⟨S, hScard, b, hb⟩ := hf (fun e ↦ decide (e ∈ G))
    have hSF : S ∈ F := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩
    apply hGnot
    apply Finset.mem_biUnion.mpr
    refine ⟨S, hSF, ?_⟩
    cases b with
    | false =>
      apply Finset.mem_union_left
      apply Finset.mem_powerset.mpr
      intro e heG
      refine Finset.mem_sdiff.mpr ⟨hGsub heG, ?_⟩
      intro heS
      obtain ⟨heSub, heCard⟩ := Finset.mem_powersetCard.mp heS
      have hval := hb e heSub heCard
      simp [heG] at hval
    | true =>
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨G \ inS S, Finset.mem_powerset.mpr ?_, ?_⟩
      · intro e he
        obtain ⟨heG, heNot⟩ := Finset.mem_sdiff.mp he
        exact Finset.mem_sdiff.mpr ⟨hGsub heG, heNot⟩
      · ext e
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (⟨heG, _⟩ | heS)
          · exact heG
          · obtain ⟨heSub, heCard⟩ := Finset.mem_powersetCard.mp heS
            have hval := hb e heSub heCard
            simpa using hval
        · intro heG
          by_cases heS : e ∈ inS S
          · exact Or.inr heS
          · exact Or.inl ⟨heG, heS⟩

private theorem choose_le_pow_self (m k : ℕ) : m.choose k ≤ m ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmul := Nat.choose_succ_right_eq m k
    have hle : m.choose (k + 1) * (k + 1) ≤ m ^ (k + 1) := by
      calc
        m.choose (k + 1) * (k + 1) = m.choose k * (m - k) := hmul
        _ ≤ m ^ k * m := Nat.mul_le_mul ih (Nat.sub_le m k)
        _ = m ^ (k + 1) := (pow_succ m k).symm
    have h1 : m.choose (k + 1) ≤ m.choose (k + 1) * (k + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
    exact h1.trans hle

private theorem not_forces2_pow {t : ℕ} (ht : 1 ≤ t) : ¬ Forces 2 (4 * t) (Fin (2 ^ t)) := by
  apply not_forces_of_count
  have hch : (2 ^ t).choose (4 * t) ≤ 2 ^ (4 * t ^ 2) := by
    calc
      (2 ^ t).choose (4 * t) ≤ (2 ^ t) ^ (4 * t) := choose_le_pow_self _ _
      _ = 2 ^ (t * (4 * t)) := (pow_mul 2 t (4 * t)).symm
      _ = 2 ^ (4 * t ^ 2) := by ring_nf
  have h2ch : (4 * t).choose 2 = 2 * t * (4 * t - 1) := by
    rw [Nat.choose_two_right]
    have hmul : 4 * t * (4 * t - 1) = 2 * (2 * t * (4 * t - 1)) := by ring
    rw [hmul, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  have hexp : 4 * t ^ 2 + 1 < (4 * t).choose 2 := by
    rw [h2ch]
    have hsub : 4 * t - 1 + 1 = 4 * t := by omega
    nlinarith
  calc
    2 * (2 ^ t).choose (4 * t) ≤ 2 * 2 ^ (4 * t ^ 2) := Nat.mul_le_mul_left 2 hch
    _ = 2 ^ (4 * t ^ 2 + 1) := by rw [← pow_succ']
    _ < 2 ^ (4 * t).choose 2 := Nat.pow_lt_pow_right (by norm_num) hexp

private theorem six_mul_choose_three (n : ℕ) :
    6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.mul_add, ih, Nat.choose_two_right]
    have h2 : 2 ∣ n * (n - 1) := Nat.even_mul_pred_self n |>.two_dvd
    have hdiv : 6 * (n * (n - 1) / 2) = 3 * (n * (n - 1)) := by
      obtain ⟨k, hk⟩ := h2
      rw [hk, Nat.mul_div_right _ (by norm_num : 0 < 2)]
      ring
    rw [hdiv]
    rcases n with _ | _ | n <;> simp <;> ring

private theorem ehr_quadratic_lower {n : ℕ} (hn : 8 ≤ n) :
    2 ^ (n ^ 2 / 32) < hypergraphRamsey 3 n := by
  apply (below_ramsey_iff_not_forces (finite_ramsey 3 n)).mpr
  apply not_forces_of_count
  let e := n ^ 2 / 32
  have he : 32 * e ≤ n ^ 2 := Nat.mul_div_le (n ^ 2) 32
  have hch : (2 ^ e).choose n ≤ 2 ^ (e * n) := by
    calc
      (2 ^ e).choose n ≤ (2 ^ e) ^ n := choose_le_pow_self _ _
      _ = 2 ^ (e * n) := (pow_mul 2 e n).symm
  have hc3 : 6 * n.choose 3 = n * (n - 1) * (n - 2) := six_mul_choose_three n
  have hexp : e * n + 1 < n.choose 3 := by
    have hmul : 6 * (e * n + 1) < 6 * n.choose 3 := by
      rw [hc3]
      have h3 : 32 * (e * n) ≤ n ^ 3 := by
        calc
          32 * (e * n) = (32 * e) * n := by ring
          _ ≤ n ^ 2 * n := Nat.mul_le_mul_right n he
          _ = n ^ 3 := by ring
      have hpoly : n * (n - 1) * (n - 2) + 3 * n ^ 2 = n ^ 3 + 2 * n := by
        have h1 : (n - 1 : ℕ) + 1 = n := by omega
        have h2 : (n - 2 : ℕ) + 2 = n := by omega
        zify [show 1 ≤ n by omega, show 2 ≤ n by omega]
        ring
      have hsq : 64 ≤ n ^ 2 := by nlinarith
      have hcub : 8 * n ^ 2 ≤ n ^ 3 := by nlinarith
      nlinarith
    omega
  calc
    2 * (2 ^ e).choose n ≤ 2 * 2 ^ (e * n) := Nat.mul_le_mul_left 2 hch
    _ = 2 ^ (e * n + 1) := by rw [← pow_succ']
    _ < 2 ^ n.choose 3 := Nat.pow_lt_pow_right (by norm_num) hexp

/- Multi-colour forcing and 4-colour stepping-up on Cube N. -/

private def ForcesK (q r n : ℕ) (α : Type) : Prop :=
  ∀ c : Finset α → Fin q, ∃ S : Finset α, S.card = n ∧
    ∃ b : Fin q, ∀ e : Finset α, e ⊆ S → e.card = r → c e = b

private theorem forcesK_of_embedding {q r n : ℕ} {α β : Type} (i : α ↪ β)
    (h : ForcesK q r n α) : ForcesK q r n β := by
  classical
  intro c
  obtain ⟨S, hS, b, hb⟩ := h (fun e ↦ c (e.map i))
  refine ⟨S.map i, by simpa using hS, b, ?_⟩
  intro e he hcard
  obtain ⟨t, ht, rfl⟩ := Finset.subset_map_iff.mp he
  exact hb t ht (by simpa using hcard)

private theorem forcesK_mono {q r n m M : ℕ} (hm : m ≤ M)
    (h : ForcesK q r n (Fin m)) : ForcesK q r n (Fin M) :=
  forcesK_of_embedding (Fin.castLEEmb hm) h

private theorem forcesK_mono_size {q r a b : ℕ} {α : Type} (hab : a ≤ b)
    (h : ForcesK q r b α) : ForcesK q r a α := by
  classical
  intro c
  obtain ⟨S, hS, col, hcol⟩ := h c
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (show a ≤ S.card by rwa [hS])
  exact ⟨T, hT, col, fun e he hr ↦ hcol e (he.trans hTS) hr⟩

private theorem forcesK_two_iff (r n : ℕ) (α : Type) :
    ForcesK 2 r n α ↔ Forces r n α := by
  constructor
  · intro h c
    obtain ⟨S, hS, b, hb⟩ := h (fun e ↦ if c e then 1 else 0)
    refine ⟨S, hS, decide (b = 1), ?_⟩
    intro e he hcard
    have hval := hb e he hcard
    fin_cases b <;> cases hce : c e <;> simp_all
  · intro h c
    obtain ⟨S, hS, b, hb⟩ := h (fun e ↦ decide (c e = 1))
    refine ⟨S, hS, if b then 1 else 0, ?_⟩
    intro e he hcard
    have hval := hb e he hcard
    have hlt := (c e).isLt
    cases b with
    | false =>
      have hne : c e ≠ 1 := by simpa using hval
      apply Fin.ext
      change (c e).val = 0
      have hne' : (c e).val ≠ 1 := fun h' ↦ hne (Fin.ext h')
      omega
    | true =>
      simpa using hval

private def OrderedForcesK (q n : ℕ) (α : Type) [LinearOrder α] : Prop :=
  ∀ c : α → α → α → Fin q, ∃ S : Finset α, S.card = n ∧
    ∃ b : Fin q, ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → c x y z = b

private theorem orderedForcesK_iff_forcesK {q n : ℕ} {α : Type} [LinearOrder α] (hq : 0 < q) :
    OrderedForcesK q n α ↔ ForcesK q 3 n α := by
  classical
  constructor
  · intro h c
    obtain ⟨S, hS, b, hb⟩ := h (fun x y z ↦ c {x, y, z})
    refine ⟨S, hS, b, ?_⟩
    intro e he hcard
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := triple_sorted hcard
    exact hb x (he (by simp)) y (he (by simp)) z (he (by simp)) hxy hyz
  · intro h c
    let c' : Finset α → Fin q := fun e ↦
      if he : e.card = 3 then
        let h3 := triple_sorted he
        let x := h3.choose
        let y := h3.choose_spec.choose
        let z := h3.choose_spec.choose_spec.choose
        c x y z
      else ⟨0, hq⟩
    obtain ⟨S, hS, b, hb⟩ := h c'
    refine ⟨S, hS, b, ?_⟩
    intro x hx y hy z hz hxy hyz
    have hcard : ({x, y, z} : Finset α).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨x, y, z, ne_of_lt hxy, ne_of_lt (hxy.trans hyz), ne_of_lt hyz, rfl⟩
    have hsub : ({x, y, z} : Finset α) ⊆ S := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have hval := hb {x, y, z} hsub hcard
    dsimp only [c'] at hval
    rw [dif_pos hcard] at hval
    have hspec := (triple_sorted hcard).choose_spec.choose_spec.choose_spec
    obtain ⟨hx', hy', hz'⟩ := triple_sorted_unique hspec.1 hspec.2.1 hxy hyz hspec.2.2.symm
    have hceq : c (triple_sorted hcard).choose
        (triple_sorted hcard).choose_spec.choose
        (triple_sorted hcard).choose_spec.choose_spec.choose = c x y z := by
      congr 1
    exact hceq.symm.trans hval

private theorem cubeDelta_inc_chain {N t : ℕ} (f : Fin (t + 1) ↪o Cube N)
    (d : Fin t → Fin N)
    (hd : ∀ i : Fin t, d i = cubeDelta (ne_of_lt (f.strictMono (Fin.castSucc_lt_succ (i := i)))))
    (hinc : StrictMono d) :
    ∀ (i j : Fin (t + 1)) (hij : i < j),
      cubeDelta (ne_of_lt (f.strictMono hij)) = d ⟨i.val, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩ := by
  suffices h : ∀ (k : ℕ) (i j : Fin (t + 1)) (hij : i < j), j.val - i.val = k →
      cubeDelta (ne_of_lt (f.strictMono hij)) = d ⟨i.val, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩ by
    exact fun i j hij ↦ h _ i j hij rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro i j hij hk
    by_cases hstep : j.val = i.val + 1
    · have hi' : i.val < t := lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)
      let idx : Fin t := ⟨i.val, hi'⟩
      have hi_eq : i = idx.castSucc := Fin.ext rfl
      have hj_eq : j = idx.succ := Fin.ext hstep
      have hrel : cubeDelta (ne_of_lt (f.strictMono hij)) =
          cubeDelta (ne_of_lt (f.strictMono (Fin.castSucc_lt_succ (i := idx)))) := by
        apply (cubeDelta_eq_iff _ _).mpr
        let h := ne_of_lt (f.strictMono (Fin.castSucc_lt_succ (i := idx)))
        exact ⟨fun l hl ↦ by simpa only [hi_eq, hj_eq] using cubeDelta_eq_of_lt h hl,
          by simpa only [hi_eq, hj_eq] using cubeDelta_spec h⟩
      rw [hrel, ← hd idx]
    · have hmid_lt : i.val + 1 < j.val := by omega
      let m : Fin (t + 1) := ⟨j.val - 1, by omega⟩
      have him : i < m := by change i.val < j.val - 1; omega
      have hmj : m < j := by change j.val - 1 < j.val; omega
      have hsub1 : m.val - i.val < k := by change (j.val - 1) - i.val < k; omega
      have hsub2 : j.val - m.val < k := by change j.val - (j.val - 1) < k; omega
      have h1 := ih (m.val - i.val) hsub1 i m him rfl
      have h2 := ih (j.val - m.val) hsub2 m j hmj rfl
      have hmin := cubeDelta_min_of_lt_lt (f.strictMono him) (f.strictMono hmj)
      have hlt_idx : (⟨i.val, lt_of_lt_of_le him (Nat.le_of_lt_succ m.isLt)⟩ : Fin t) <
          ⟨m.val, lt_of_lt_of_le hmj (Nat.le_of_lt_succ j.isLt)⟩ := him
      have hlt_d := hinc hlt_idx
      rw [hmin, h1, h2, min_eq_left hlt_d.le]

private theorem cubeDelta_dec_chain {N t : ℕ} (f : Fin (t + 1) ↪o Cube N)
    (d : Fin t → Fin N)
    (hd : ∀ i : Fin t, d i = cubeDelta (ne_of_lt (f.strictMono (Fin.castSucc_lt_succ (i := i)))))
    (hdec : StrictAnti d) :
    ∀ (i j : Fin (t + 1)) (hij : i < j),
      cubeDelta (ne_of_lt (f.strictMono hij)) = d ⟨j.val - 1, by omega⟩ := by
  suffices h : ∀ (k : ℕ) (i j : Fin (t + 1)) (hij : i < j), j.val - i.val = k →
      cubeDelta (ne_of_lt (f.strictMono hij)) = d ⟨j.val - 1, by omega⟩ by
    exact fun i j hij ↦ h _ i j hij rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro i j hij hk
    by_cases hstep : j.val = i.val + 1
    · let idx : Fin t := ⟨j.val - 1, by omega⟩
      have hi_eq : i = idx.castSucc := Fin.ext (by simp [idx]; omega)
      have hj_eq : j = idx.succ := Fin.ext (by simp [idx]; omega)
      have hrel : cubeDelta (ne_of_lt (f.strictMono hij)) =
          cubeDelta (ne_of_lt (f.strictMono (Fin.castSucc_lt_succ (i := idx)))) := by
        apply (cubeDelta_eq_iff _ _).mpr
        let h := ne_of_lt (f.strictMono (Fin.castSucc_lt_succ (i := idx)))
        exact ⟨fun l hl ↦ by simpa only [hi_eq, hj_eq] using cubeDelta_eq_of_lt h hl,
          by simpa only [hi_eq, hj_eq] using cubeDelta_spec h⟩
      rw [hrel, ← hd idx]
    · let m : Fin (t + 1) := ⟨i.val + 1, by omega⟩
      have him : i < m := by change i.val < i.val + 1; omega
      have hmj : m < j := by change i.val + 1 < j.val; omega
      have hsub1 : m.val - i.val < k := by change (i.val + 1) - i.val < k; omega
      have hsub2 : j.val - m.val < k := by change j.val - (i.val + 1) < k; omega
      have h1 := ih (m.val - i.val) hsub1 i m him rfl
      have h2 := ih (j.val - m.val) hsub2 m j hmj rfl
      have hmin := cubeDelta_min_of_lt_lt (f.strictMono him) (f.strictMono hmj)
      have hlt_idx : (⟨m.val - 1, by omega⟩ : Fin t) < ⟨j.val - 1, by omega⟩ := by
        change (i.val + 1) - 1 < j.val - 1; omega
      have hlt_d := hdec hlt_idx
      rw [hmin, h1, h2, min_eq_right hlt_d.le]

private theorem not_forcesK4_cube_of_not_forces2 {N t : ℕ}
    (hg : ¬ Forces 2 t (Fin N)) : ¬ ForcesK 4 3 (t + 1) (Cube N) := by
  classical
  by_cases ht : t = 0
  · subst t
    exact (hg (fun _ ↦ ⟨∅, rfl, false, fun e he hcard ↦ by simp [Finset.subset_empty.mp he] at hcard⟩)).elim
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
  have hg' : ∃ g : Finset (Fin N) → Bool, ¬ ∃ T : Finset (Fin N), T.card = s + 1 ∧
      ∃ col : Bool, ∀ e : Finset (Fin N), e ⊆ T → e.card = 2 → g e = col := by
    by_contra h
    push Not at h
    exact hg h
  obtain ⟨g, hno⟩ := hg'
  rw [← orderedForcesK_iff_forcesK (by norm_num : 0 < 4)]
  intro hforce
  let c : Cube N → Cube N → Cube N → Fin 4 := fun x y z ↦
    if h : x < y ∧ y < z then
      let d₁ := cubeDelta (ne_of_lt h.1)
      let d₂ := cubeDelta (ne_of_lt h.2)
      if d₁ < d₂ then (if g {d₁, d₂} then 0 else 1) else (if g {d₁, d₂} then 2 else 3)
    else 0
  obtain ⟨S, hScard, b, hb⟩ := hforce c
  let f : Fin (s + 1 + 1) ↪o Cube N := S.orderEmbOfFin hScard
  have hf_mem (i : Fin (s + 1 + 1)) : f i ∈ S := S.orderEmbOfFin_mem hScard i
  let d : Fin (s + 1) → Fin N := fun i ↦ cubeDelta (ne_of_lt (f.strictMono (Fin.castSucc_lt_succ (i := i))))
  have hlt₁ (i : Fin s) : f i.castSucc.castSucc < f i.succ.castSucc :=
    f.strictMono (show i.castSucc.castSucc < i.succ.castSucc from Fin.castSucc_lt_succ)
  have hlt₂ (i : Fin s) : f i.succ.castSucc < f i.succ.succ :=
    f.strictMono Fin.castSucc_lt_succ
  have hstep_val (i : Fin s) :
      (if d i.castSucc < d i.succ then (if g {d i.castSucc, d i.succ} then 0 else 1)
        else (if g {d i.castSucc, d i.succ} then 2 else 3)) = b := by
    have h := hb _ (hf_mem i.castSucc.castSucc) _ (hf_mem i.succ.castSucc)
      _ (hf_mem i.succ.succ) (hlt₁ i) (hlt₂ i)
    simpa only [c, dif_pos (And.intro (hlt₁ i) (hlt₂ i))] using h
  have hpair_inc (col : Bool) (hinc : StrictMono d)
      (hmono : ∀ i j : Fin (s + 1), i < j → g {d i, d j} = col) : False := by
    apply hno
    refine ⟨Finset.univ.image d, ?_, col, ?_⟩
    · rw [Finset.card_image_of_injective _ hinc.injective, Finset.card_univ, Fintype.card_fin]
    · intro e he hcard
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
      have hu : u ∈ Finset.univ.image d := he (by simp)
      have hv : v ∈ Finset.univ.image d := he (by simp)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
      rw [← hi, ← hj] at huv ⊢
      rcases lt_or_gt_of_ne (show i ≠ j from fun hij ↦ huv (congrArg d hij)) with hij | hji
      · exact hmono i j hij
      · rw [Finset.pair_comm]
        exact hmono j i hji
  have hpair_dec (col : Bool) (hdec : StrictAnti d)
      (hmono : ∀ i j : Fin (s + 1), i < j → g {d i, d j} = col) : False := by
    apply hno
    refine ⟨Finset.univ.image d, ?_, col, ?_⟩
    · rw [Finset.card_image_of_injective _ hdec.injective, Finset.card_univ, Fintype.card_fin]
    · intro e he hcard
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
      have hu : u ∈ Finset.univ.image d := he (by simp)
      have hv : v ∈ Finset.univ.image d := he (by simp)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
      rw [← hi, ← hj] at huv ⊢
      rcases lt_or_gt_of_ne (show i ≠ j from fun hij ↦ huv (congrArg d hij)) with hij | hji
      · exact hmono i j hij
      · rw [Finset.pair_comm]
        exact hmono j i hji
  fin_cases b
  · have hinc : StrictMono d := by
      refine (Fin.strictMono_iff_lt_succ (f := d)).mpr fun i ↦ ?_
      have hv := hstep_val i
      by_contra hnot
      simp only [hnot, ↓reduceIte] at hv
      split_ifs at hv <;> simp at hv
    refine hpair_inc true hinc fun i j hij ↦ ?_
    have hij' : i.castSucc < j.castSucc := hij
    have hjj : j.castSucc < j.succ := Fin.castSucc_lt_succ
    have hv := hb _ (hf_mem i.castSucc) _ (hf_mem j.castSucc) _ (hf_mem j.succ)
      (f.strictMono hij') (f.strictMono hjj)
    have hd1 : cubeDelta (ne_of_lt (f.strictMono hij')) = d i :=
      cubeDelta_inc_chain f d (fun _ ↦ rfl) hinc i.castSucc j.castSucc hij'
    have hd2 : cubeDelta (ne_of_lt (f.strictMono hjj)) = d j := rfl
    simp only [c, dif_pos (And.intro (f.strictMono hij') (f.strictMono hjj)), hd1, hd2,
      hinc hij, ↓reduceIte] at hv
    cases hgval : g {d i, d j} <;> simp [hgval] at hv ⊢
  · have hinc : StrictMono d := by
      refine (Fin.strictMono_iff_lt_succ (f := d)).mpr fun i ↦ ?_
      have hv := hstep_val i
      by_contra hnot
      simp only [hnot, ↓reduceIte] at hv
      split_ifs at hv <;> simp at hv
    refine hpair_inc false hinc fun i j hij ↦ ?_
    have hij' : i.castSucc < j.castSucc := hij
    have hjj : j.castSucc < j.succ := Fin.castSucc_lt_succ
    have hv := hb _ (hf_mem i.castSucc) _ (hf_mem j.castSucc) _ (hf_mem j.succ)
      (f.strictMono hij') (f.strictMono hjj)
    have hd1 : cubeDelta (ne_of_lt (f.strictMono hij')) = d i :=
      cubeDelta_inc_chain f d (fun _ ↦ rfl) hinc i.castSucc j.castSucc hij'
    have hd2 : cubeDelta (ne_of_lt (f.strictMono hjj)) = d j := rfl
    simp only [c, dif_pos (And.intro (f.strictMono hij') (f.strictMono hjj)), hd1, hd2,
      hinc hij, ↓reduceIte] at hv
    cases hgval : g {d i, d j} <;> simp [hgval] at hv ⊢
  · have hdec : StrictAnti d := by
      refine (Fin.strictAnti_iff_succ_lt (f := d)).mpr fun i ↦ ?_
      have hv := hstep_val i
      have hne : d i.castSucc ≠ d i.succ := cubeDelta_ne_of_lt_lt (hlt₁ i) (hlt₂ i)
      by_cases hlt : d i.castSucc < d i.succ
      · simp only [hlt, ↓reduceIte] at hv
        split_ifs at hv <;> simp at hv
      · exact lt_of_le_of_ne (not_lt.mp hlt) hne.symm
    refine hpair_dec true hdec fun i j hij ↦ ?_
    have hii : i.castSucc < i.succ := Fin.castSucc_lt_succ
    have hij' : i.succ < j.succ := Fin.succ_lt_succ_iff.mpr hij
    have hv := hb _ (hf_mem i.castSucc) _ (hf_mem i.succ) _ (hf_mem j.succ)
      (f.strictMono hii) (f.strictMono hij')
    have hd1 : cubeDelta (ne_of_lt (f.strictMono hii)) = d i := rfl
    have hd2 : cubeDelta (ne_of_lt (f.strictMono hij')) = d j := by
      simpa using cubeDelta_dec_chain f d (fun _ ↦ rfl) hdec i.succ j.succ hij'
    have hgt : ¬ d i < d j := not_lt.mpr (hdec hij).le
    simp only [c, dif_pos (And.intro (f.strictMono hii) (f.strictMono hij')), hd1, hd2,
      hgt, ↓reduceIte] at hv
    cases hgval : g {d i, d j} <;> simp [hgval] at hv ⊢
  · have hdec : StrictAnti d := by
      refine (Fin.strictAnti_iff_succ_lt (f := d)).mpr fun i ↦ ?_
      have hv := hstep_val i
      have hne : d i.castSucc ≠ d i.succ := cubeDelta_ne_of_lt_lt (hlt₁ i) (hlt₂ i)
      by_cases hlt : d i.castSucc < d i.succ
      · simp only [hlt, ↓reduceIte] at hv
        split_ifs at hv <;> simp at hv
      · exact lt_of_le_of_ne (not_lt.mp hlt) hne.symm
    refine hpair_dec false hdec fun i j hij ↦ ?_
    have hii : i.castSucc < i.succ := Fin.castSucc_lt_succ
    have hij' : i.succ < j.succ := Fin.succ_lt_succ_iff.mpr hij
    have hv := hb _ (hf_mem i.castSucc) _ (hf_mem i.succ) _ (hf_mem j.succ)
      (f.strictMono hii) (f.strictMono hij')
    have hd1 : cubeDelta (ne_of_lt (f.strictMono hii)) = d i := rfl
    have hd2 : cubeDelta (ne_of_lt (f.strictMono hij')) = d j := by
      simpa using cubeDelta_dec_chain f d (fun _ ↦ rfl) hdec i.succ j.succ hij'
    have hgt : ¬ d i < d j := not_lt.mpr (hdec hij).le
    simp only [c, dif_pos (And.intro (f.strictMono hii) (f.strictMono hij')), hd1, hd2,
      hgt, ↓reduceIte] at hv
    cases hgval : g {d i, d j} <;> simp [hgval] at hv ⊢

private theorem not_forcesK4_pow {t : ℕ} (ht : 1 ≤ t) :
    ¬ ForcesK 4 3 (4 * t + 1) (Fin (2 ^ (2 ^ t))) := by
  intro hf
  apply not_forcesK4_cube_of_not_forces2 (not_forces2_pow ht)
  have h1 : ForcesK 4 3 (4 * t + 1) (Fin (2 ^ t) → Bool) :=
    forcesK_of_embedding (cubeEquiv t).symm.toEmbedding hf
  exact forcesK_of_embedding ⟨Cube.mk, fun _ _ h ↦ congrArg Cube.bits h⟩ h1

/-- An Erdős–Rado selection: on the selected vertices the colour of an
`(r+1)`-edge depends only on its first `r` vertices. -/
private theorem stable_last_vertex {α : Type} [LinearOrder α] {q r m B : ℕ}
    (hq : 0 < q) (hr : 0 < r) (c : Finset α → Fin q) (V : Finset α)
    (hB : ∀ i ≤ m, q ^ i.choose (r - 1) ≤ B)
    (hV : (B + 1) ^ m ≤ V.card) :
    ∃ S ⊆ V, S.card = m ∧ ∃ g : Finset α → Fin q,
      ∀ e ⊆ S, e.card = r → ∀ z ∈ S, (∀ y ∈ e, y < z) → c (insert z e) = g e := by
  classical
  have hselect (i : ℕ) (hi : i ≤ m) :
      ∃ S ⊆ V, ∃ T ⊆ V, S.card = i ∧ (B + 1) ^ (m - i) ≤ T.card ∧
        (∀ y ∈ S, ∀ z ∈ T, y < z) ∧ ∃ g : Finset α → Fin q,
          ∀ e ⊆ S, e.card = r → ∀ z ∈ S ∪ T, (∀ y ∈ e, y < z) →
            c (insert z e) = g e := by
    induction i with
    | zero =>
      refine ⟨∅, Finset.empty_subset _, V, Finset.Subset.refl _, rfl, ?_,
        by simp, fun _ ↦ ⟨0, hq⟩, ?_⟩
      · simpa using hV
      · intro e he hecard
        rw [Finset.subset_empty.mp he, Finset.card_empty] at hecard
        exact (hr.ne' hecard.symm).elim
    | succ i ih =>
      have him : i ≤ m := by omega
      obtain ⟨S, hSV, T, hTV, hS, hT, hsep, g, hg⟩ := ih him
      have hpos : 0 < (B + 1) ^ (m - (i + 1)) := pow_pos (by omega) _
      have hT' : B * (B + 1) ^ (m - (i + 1)) + (B + 1) ^ (m - (i + 1)) ≤ T.card := by
        have he : m - i = (m - (i + 1)) + 1 := by omega
        rwa [he, pow_succ', Nat.add_mul, one_mul] at hT
      have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
      let x := T.min' hTne
      have hx : x ∈ T := T.min'_mem hTne
      have hxS : x ∉ S := fun h ↦ (lt_irrefl _) (hsep x h x hx)
      let P := S.powersetCard (r - 1)
      let signature (z : α) (a : P) := c (insert z (insert x a.val))
      have hcount : (Finset.univ : Finset (P → Fin q)).card ≤ B := by
        simpa [P, hS, Fintype.card_fun, Finset.card_powersetCard] using hB i him
      have hbudget : (Finset.univ : Finset (P → Fin q)).card *
          (B + 1) ^ (m - (i + 1)) ≤ (T.erase x).card := by
        have hh := Nat.mul_le_mul_right ((B + 1) ^ (m - (i + 1))) hcount
        rw [Finset.card_erase_of_mem hx]
        omega
      letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
      obtain ⟨p, _, hp⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (f := signature) (fun _ _ ↦ Finset.mem_univ _) Finset.univ_nonempty hbudget
      let U := (T.erase x).filter (fun z ↦ signature z = p)
      have hU (z : α) (hz : z ∈ U) : z ∈ T.erase x ∧ signature z = p :=
        Finset.mem_filter.mp hz
      have hUT : U ⊆ T := fun z hz ↦ Finset.mem_of_mem_erase (hU z hz).1
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < U.card from hpos.trans_le hp)
      let g' (e : Finset α) := if x ∈ e then c (insert w e) else g e
      refine ⟨insert x S, Finset.insert_subset (hTV hx) hSV, U, hUT.trans hTV,
        by rw [Finset.card_insert_of_notMem hxS, hS], hp, ?_, g', ?_⟩
      · intro y hy z hz
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact T.min'_lt_of_mem_erase_min' hTne (hU z hz).1
        · exact hsep y hy z (hUT hz)
      · intro e he hecard z hz hzmax
        by_cases hxe : x ∈ e
        · have hzU : z ∈ U := by
            rcases Finset.mem_union.mp hz with hz | hz
            · exfalso
              rcases Finset.mem_insert.mp hz with rfl | hz
              · exact (lt_irrefl _) (hzmax x hxe)
              · exact (not_lt_of_ge (hsep z hz x hx).le) (hzmax x hxe)
            · exact hz
          have heP : e.erase x ∈ P := by
            apply Finset.mem_powersetCard.mpr
            refine ⟨?_, ?_⟩
            · intro y hy
              have hy' := Finset.mem_erase.mp hy
              exact (Finset.mem_insert.mp (he hy'.2)).resolve_left hy'.1
            · rw [Finset.card_erase_of_mem hxe, hecard]
          have hzsig := (hU z hzU).2.trans (hU w hw).2.symm
          have hsame := congrFun hzsig (⟨e.erase x, heP⟩ : P)
          dsimp only [signature] at hsame
          rw [Finset.insert_erase hxe] at hsame
          simpa only [g', if_pos hxe] using hsame
        · have heS : e ⊆ S := fun y hy ↦
            (Finset.mem_insert.mp (he hy)).resolve_left (fun eq ↦ hxe (eq ▸ hy))
          have hzST : z ∈ S ∪ T := by
            rcases Finset.mem_union.mp hz with hz | hz
            · rcases Finset.mem_insert.mp hz with rfl | hz
              · exact Finset.mem_union_right _ hx
              · exact Finset.mem_union_left _ hz
            · exact Finset.mem_union_right _ (hUT hz)
          simpa only [g', if_neg hxe] using hg e heS hecard z hzST hzmax
  obtain ⟨S, hSV, T, hTV, hS, _, _, g, hg⟩ := hselect m le_rfl
  exact ⟨S, hSV, hS, g, fun e he hc z hz ↦ hg e he hc z (Finset.mem_union_left _ hz)⟩

private theorem forcesK_of_reservoir {q r n m B : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hm : ForcesK q r n (Fin m))
    (hB : ∀ i ≤ m, q ^ i.choose (r - 1) ≤ B) :
    ForcesK q (r + 1) n (Fin ((B + 1) ^ m)) := by
  classical
  intro c
  obtain ⟨S, _, hS, g, hg⟩ := stable_last_vertex hq hr c Finset.univ hB (by simp)
  let f := (S.orderEmbOfFin hS).toEmbedding
  obtain ⟨A, hA, b, hb⟩ := hm (fun e ↦ g (e.map f))
  have hfS : A.map f ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact S.orderEmbOfFin_mem hS i
  refine ⟨A.map f, by simpa using hA, b, ?_⟩
  intro e he hecard
  have hepos : e.Nonempty := Finset.card_pos.mp (by omega)
  let z := e.max' hepos
  have hz : z ∈ e := e.max'_mem hepos
  have he' : e.erase z ⊆ A.map f := (Finset.erase_subset _ _).trans he
  have hc' : (e.erase z).card = r := by simp [Finset.card_erase_of_mem hz, hecard]
  have h := hg (e.erase z) (he'.trans hfS) hc' z (hfS (he hz))
    (fun _ hy ↦ e.lt_max'_of_mem_erase_max' hepos hy)
  obtain ⟨E, hE, hEmap⟩ := Finset.subset_map_iff.mp he'
  have hEcard : E.card = r := by rw [← hc', hEmap, Finset.card_map]
  rw [Finset.insert_erase hz, hEmap] at h
  exact h.trans (hb E hE hEcard)

private theorem forcesK_vertices {q n : ℕ} (hq : 0 < q) : ForcesK q 1 n (Fin (q * n)) := by
  classical
  intro c
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let f (x : Fin (q * n)) := c {x}
  have hbound : (Finset.univ : Finset (Fin q)).card * n ≤
      (Finset.univ : Finset (Fin (q * n))).card := by simp
  obtain ⟨b, _, hb⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (f := f) (fun _ _ ↦ Finset.mem_univ _) Finset.univ_nonempty hbound
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hb
  refine ⟨T, hTcard, b, ?_⟩
  intro e he hecard
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hecard
  exact (Finset.mem_filter.mp (hT (he (by simp)))).2

private theorem forcesK4_graph (n : ℕ) : ForcesK 4 2 n (Fin (2 ^ (12 * n))) := by
  have h : ForcesK 4 (1 + 1) n (Fin ((7 + 1) ^ (4 * n))) :=
    forcesK_of_reservoir (by decide) (by decide) (forcesK_vertices (by decide))
      (fun i _ ↦ by simp)
  have he : (7 + 1) ^ (4 * n) = 2 ^ (12 * n) := by
    rw [show (7 + 1 : ℕ) = 2 ^ 3 by decide, ← pow_mul, ← Nat.mul_assoc]
  simpa only [he] using h

private theorem forcesK4_tower {n : ℕ} (hn : 1 ≤ n) :
    ForcesK 4 3 n (Fin (2 ^ (2 ^ (26 * n)))) := by
  let m : ℕ := 2 ^ (12 * n)
  have hm : 1 ≤ m := pow_pos (by decide : 0 < (2 : ℕ)) _
  have h : ForcesK 4 3 n (Fin ((4 ^ m + 1) ^ m)) := by
    apply forcesK_of_reservoir (q := 4) (B := 4 ^ m) (by decide) (show 0 < 2 by decide) (forcesK4_graph n)
    intro i hi
    simp only [Nat.reduceSub, Nat.choose_one_right]
    exact Nat.pow_le_pow_right (by decide) hi
  have hbase : 4 ^ m + 1 ≤ 2 ^ (3 * m) := by
    have hp : 1 ≤ 4 ^ m := pow_pos (by decide : 0 < (4 : ℕ)) _
    calc
      4 ^ m + 1 ≤ 2 * 4 ^ m := by omega
      _ = 2 ^ (2 * m + 1) := by rw [pow_succ', pow_mul]; rfl
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by decide) (by omega)
  have hexp : 3 * m * m ≤ 2 ^ (26 * n) := by
    calc
      3 * m * m ≤ 4 * m * m :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 3 ≤ 4))
      _ = 2 ^ (2 + 12 * n * 2) := by
        rw [pow_add, pow_mul]
        dsimp [m]
        ring
      _ ≤ 2 ^ (26 * n) := Nat.pow_le_pow_right (by decide) (by omega)
  apply forcesK_mono _ h
  calc
    (4 ^ m + 1) ^ m ≤ (2 ^ (3 * m)) ^ m := Nat.pow_le_pow_left hbase _
    _ = 2 ^ (3 * m * m) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (2 ^ (26 * n)) := Nat.pow_le_pow_right (by decide) hexp

/-- At the two-colour threshold for a linearly larger clique, every four-colouring
already has a monochromatic clique of the requested size. -/
private def TwoVsFourTransfer : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ᶠ t : ℕ in atTop,
    ForcesK 4 3 t (Fin (hypergraphRamsey 3 (k * t)))

private theorem cubeWitness_of_twoVsFourTransfer (h : TwoVsFourTransfer) : CubeWitness := by
  obtain ⟨k, hk, hforce⟩ := h
  obtain ⟨T, hT⟩ := eventually_atTop.mp hforce
  refine ⟨k * 5, Nat.mul_pos hk (by decide), ?_⟩
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (1 : ℕ)] with t ht ht1
  intro hcube
  have hramsey : hypergraphRamsey 3 ((k * 5) * t) ≤ 2 ^ (2 ^ t) := by
    by_contra! hlt
    exact (below_ramsey_iff_not_forces (finite_ramsey _ _)).mp hlt
      ((forces_cube_iff _ _ _).mp hcube)
  have hlarge : T ≤ 5 * t := by omega
  have h4 := forcesK_mono hramsey (by simpa only [Nat.mul_assoc] using hT (5 * t) hlarge)
  exact not_forcesK4_pow ht1 (forcesK_mono_size (show 4 * t + 1 ≤ 5 * t by omega) h4)

private theorem twoVsFourTransfer_of_cubeWitness (h : CubeWitness) : TwoVsFourTransfer := by
  obtain ⟨k, hk, havoid⟩ := h
  obtain ⟨T, hT⟩ := eventually_atTop.mp havoid
  refine ⟨k * 26, Nat.mul_pos hk (by decide), ?_⟩
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (1 : ℕ)] with t ht ht1
  have hlarge : T ≤ 26 * t := by omega
  have hbelow : 2 ^ (2 ^ (26 * t)) < hypergraphRamsey 3 ((k * 26) * t) := by
    apply (below_ramsey_iff_not_forces (finite_ramsey _ _)).mpr
    intro hf
    exact hT (26 * t) hlarge ((forces_cube_iff _ _ _).mpr (by simpa only [Nat.mul_assoc] using hf))
  exact forcesK_mono hbelow.le (forcesK4_tower ht1)

private theorem cubeWitness_iff_twoVsFourTransfer : CubeWitness ↔ TwoVsFourTransfer :=
  ⟨twoVsFourTransfer_of_cubeWitness, cubeWitness_of_twoVsFourTransfer⟩

private theorem forces_at_hypergraphRamsey (r n : ℕ) :
    Forces r n (Fin (hypergraphRamsey r n)) := by
  exact Nat.sInf_mem (finite_ramsey r n)

private theorem hypergraphRamsey_mono_size (r : ℕ) {a b : ℕ} (hab : a ≤ b) :
    hypergraphRamsey r a ≤ hypergraphRamsey r b := by
  exact Nat.sInf_le (forces_mono_size hab (forces_at_hypergraphRamsey r b))

private theorem twoVsFourTransfer_iff_linear_threshold :
    TwoVsFourTransfer ↔ ∃ d : ℝ, 0 < d ∧ ∀ᶠ n : ℕ in atTop,
      ∃ t : ℕ, d * (n : ℝ) ≤ t ∧ ForcesK 4 3 t (Fin (hypergraphRamsey 3 n)) := by
  constructor
  · rintro ⟨k, hk, hf⟩
    obtain ⟨T, hT⟩ := eventually_atTop.mp hf
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    refine ⟨1 / (2 * (k : ℝ)), by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (T * k), eventually_ge_atTop k] with n hn hkn
    let t := n / k
    have ht : T ≤ t := (Nat.le_div_iff_mul_le hk).mpr hn
    have ht1 : 1 ≤ t := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hkn)
    have hkt : k * t ≤ n := Nat.mul_div_le _ _
    have hdouble : n ≤ 2 * (k * t) := by
      have hmod := Nat.mod_lt n hk
      have hdiv : n % k + k * t = n := Nat.mod_add_div n k
      have hle : k ≤ k * t := by simpa using Nat.mul_le_mul_left k ht1
      omega
    refine ⟨t, ?_, forcesK_mono (hypergraphRamsey_mono_size 3 hkt) (hT t ht)⟩
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
    calc
      (n : ℝ) ≤ 2 * ((k : ℝ) * (t : ℝ)) := by exact_mod_cast hdouble
      _ = (t : ℝ) * (2 * k) := by ring
  · rintro ⟨d, hd, hf⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hf
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / d)
    have hkR : (0 : ℝ) < k := (by positivity : (0 : ℝ) < 1 / d).trans hk
    have hkN : 0 < k := by exact_mod_cast hkR
    have hdk : (1 : ℝ) ≤ d * (k : ℝ) := by
      simpa [mul_comm] using ((div_lt_iff₀ hd).mp hk).le
    refine ⟨k, hkN, ?_⟩
    filter_upwards [eventually_ge_atTop N] with t ht
    obtain ⟨j, hj, hforce⟩ := hN (k * t) (ht.trans (Nat.le_mul_of_pos_left _ hkN))
    have htj : t ≤ j := by
      have h : (t : ℝ) ≤ j := by
        calc
          (t : ℝ) = 1 * (t : ℝ) := (one_mul _).symm
          _ ≤ (d * (k : ℝ)) * (t : ℝ) := mul_le_mul_of_nonneg_right hdk (by positivity)
          _ = d * ((k * t : ℕ) : ℝ) := by rw [Nat.cast_mul, mul_assoc]
          _ ≤ j := hj
      exact_mod_cast h
    exact forcesK_mono_size htj hforce

private def cubeCons {N : ℕ} (b : Bool) (x : Cube N) : Cube (N + 1) :=
  ⟨Fin.cases b x.bits⟩

private def cubeHead {N : ℕ} (x : Cube (N + 1)) : Bool := x.bits 0

private def cubeTail {N : ℕ} (x : Cube (N + 1)) : Cube N := ⟨fun i ↦ x.bits i.succ⟩

@[simp] private theorem cubeHead_cons {N : ℕ} (b : Bool) (x : Cube N) :
    cubeHead (cubeCons b x) = b := by simp [cubeHead, cubeCons]

@[simp] private theorem cubeTail_cons {N : ℕ} (b : Bool) (x : Cube N) :
    cubeTail (cubeCons b x) = x := by cases x; simp [cubeTail, cubeCons]

private theorem cubeCons_head_tail {N : ℕ} (x : Cube (N + 1)) :
    cubeCons (cubeHead x) (cubeTail x) = x := by
  cases x
  apply congrArg Cube.mk
  funext i
  exact Fin.cases (by simp [cubeHead]) (fun j ↦ by simp [cubeTail]) i

private def cubeConsEmb {N : ℕ} (b : Bool) : Cube N ↪ Cube (N + 1) :=
  ⟨cubeCons b, fun x y h ↦ by simpa using congrArg cubeTail h⟩

private theorem cubeCons_maps_disjoint {N : ℕ} (A B : Finset (Cube N)) :
    Disjoint (A.map (cubeConsEmb false)) (B.map (cubeConsEmb true)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hv
  obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hv'
  have h : cubeCons false x = cubeCons true y := hx.trans hy.symm
  simpa using congrArg cubeHead h

private theorem cubeCons_lt_delta_same {N : ℕ} {x y : Cube N} (b : Bool) (h : x < y) :
    ∃ h' : cubeCons b x < cubeCons b y,
      cubeDelta (ne_of_lt h') = (cubeDelta (ne_of_lt h)).succ := by
  let d := cubeDelta (ne_of_lt h)
  have hd := cubeDelta_bits_of_lt h
  have hpre (i : Fin (N + 1)) (hi : i < d.succ) :
      (cubeCons b x).bits i = (cubeCons b y).bits i := by
    refine Fin.cases (by simp [cubeCons]) (fun j hj ↦ ?_) i hi
    have hj' : j < d := Fin.succ_lt_succ_iff.mp hj
    simpa [cubeCons] using cubeDelta_eq_of_lt (ne_of_lt h) hj'
  have hx : (cubeCons b x).bits d.succ = false := by simpa [cubeCons, d] using hd.1
  have hy : (cubeCons b y).bits d.succ = true := by simpa [cubeCons, d] using hd.2
  refine ⟨⟨d.succ, hpre, hx, hy⟩, (cubeDelta_eq_iff _ _).mpr ⟨hpre, ?_⟩⟩
  change (cubeCons b x).bits d.succ ≠ (cubeCons b y).bits d.succ
  rw [hx, hy]
  decide

private theorem cubeCons_lt_delta_cross {N : ℕ} (x y : Cube N) :
    ∃ h : cubeCons false x < cubeCons true y, cubeDelta (ne_of_lt h) = 0 := by
  have hpre (i : Fin (N + 1)) (hi : i < 0) :
      (cubeCons false x).bits i = (cubeCons true y).bits i := (Fin.not_lt_zero i hi).elim
  have hx : (cubeCons false x).bits 0 = false := cubeHead_cons _ _
  have hy : (cubeCons true y).bits 0 = true := cubeHead_cons _ _
  refine ⟨⟨0, hpre, hx, hy⟩, (cubeDelta_eq_iff _ _).mpr ⟨hpre, ?_⟩⟩
  rw [hx, hy]
  decide

private theorem cubeCons_lt_same_iff {N : ℕ} {x y : Cube N} (b : Bool) :
    cubeCons b x < cubeCons b y ↔ x < y := by
  refine ⟨fun h ↦ ?_, fun h ↦ (cubeCons_lt_delta_same b h).choose⟩
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact hxy
  · exact (lt_irrefl _ h).elim
  · exact ((cubeCons_lt_delta_same b hyx).choose.not_gt h).elim

private def cubeSection {N : ℕ} (A : Finset (Cube (N + 1))) (b : Bool) : Finset (Cube N) :=
  Finset.univ.filter fun x ↦ cubeCons b x ∈ A

@[simp] private theorem mem_cubeSection {N : ℕ} {A : Finset (Cube (N + 1))} {b : Bool}
    {x : Cube N} : x ∈ cubeSection A b ↔ cubeCons b x ∈ A := by simp [cubeSection]

private theorem card_cubeSections {N : ℕ} (A : Finset (Cube (N + 1))) :
    (cubeSection A false).card + (cubeSection A true).card = A.card := by
  classical
  let A₀ := cubeSection A false
  let A₁ := cubeSection A true
  have hA : A₀.map (cubeConsEmb false) ∪ A₁.map (cubeConsEmb true) = A := by
    ext v
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp h
        exact mem_cubeSection.mp hx
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp h
        exact mem_cubeSection.mp hx
    · intro h
      have hv : cubeCons (cubeHead v) (cubeTail v) = v := cubeCons_head_tail v
      have hm : cubeTail v ∈ cubeSection A (cubeHead v) := mem_cubeSection.mpr (hv ▸ h)
      cases hb : cubeHead v with
      | false =>
        exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨_, hb ▸ hm, hb ▸ hv⟩)
      | true =>
        exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨_, hb ▸ hm, hb ▸ hv⟩)
  calc
    A₀.card + A₁.card = (A₀.map (cubeConsEmb false) ∪ A₁.map (cubeConsEmb true)).card := by
      rw [Finset.card_union_of_disjoint (cubeCons_maps_disjoint _ _), Finset.card_map,
        Finset.card_map]
    _ = A.card := congrArg Finset.card hA

private def CubeSupported {N : ℕ} (p x : Cube N) : Prop :=
  ∀ i, p.bits i = false → x.bits i = false

/-- A profile gives the positions where a binary tree can branch at the same
level on every branch. The embedding can choose the intervening bits. -/
private def CubeProfile {N : ℕ} (A : Finset (Cube N)) (p : Cube N) : Prop :=
  ∃ f : Cube N → Cube N,
    (∀ x, CubeSupported p x → f x ∈ A) ∧
      ∀ x y, CubeSupported p x → CubeSupported p y → ∀ h : x < y,
        ∃ h' : f x < f y, cubeDelta (ne_of_lt h') = cubeDelta (ne_of_lt h)

private def CubeDeltaIs {N : ℕ} (x y : Cube N) (d : Fin N) : Prop :=
  ∃ h : x < y, cubeDelta (ne_of_lt h) = d

private theorem cubeProfile_cons {N : ℕ} {A : Finset (Cube (N + 1))} {p : Cube N}
    {a : Bool} (out : Bool → Bool)
    (hcross : a = true → out false = false ∧ out true = true)
    (hchild : ∀ b, (a = false → b = false) → CubeProfile (cubeSection A (out b)) p) :
    CubeProfile A (cubeCons a p) := by
  classical
  choose f hmem hdelta using hchild
  let F (x : Cube (N + 1)) : Cube (N + 1) :=
    if hx : a = false → cubeHead x = false then
      cubeCons (out (cubeHead x)) (f (cubeHead x) hx (cubeTail x))
    else x
  have hF (b : Bool) (x : Cube N) (h : a = false → b = false) :
      F (cubeCons b x) = cubeCons (out b) (f b h x) := by
    have h' : a = false → cubeHead (cubeCons b x) = false := fun ha ↦ by simpa using h ha
    unfold F
    rw [dif_pos h']
    simp only [cubeHead_cons, cubeTail_cons]
  have hsup {b : Bool} {x : Cube N} (hx : CubeSupported (cubeCons a p) (cubeCons b x)) :
      (a = false → b = false) ∧ CubeSupported p x := by
    refine ⟨fun ha ↦ ?_, fun i hi ↦ ?_⟩
    · simpa [cubeCons] using hx 0 (by simpa [cubeCons] using ha)
    · simpa [cubeCons] using hx i.succ (by simpa [cubeCons] using hi)
  refine ⟨F, ?_, ?_⟩
  · intro x hx
    rw [← cubeCons_head_tail x] at hx ⊢
    obtain ⟨h, ht⟩ := hsup hx
    rw [hF _ _ h]
    exact mem_cubeSection.mp (hmem _ h _ ht)
  · intro x y hx hy hxy
    revert hx hy hxy
    obtain ⟨b, v, rfl⟩ : ∃ b v, cubeCons b v = x := ⟨_, _, cubeCons_head_tail x⟩
    obtain ⟨c, w, rfl⟩ : ∃ c w, cubeCons c w = y := ⟨_, _, cubeCons_head_tail y⟩
    intro hx hy hxy
    obtain ⟨hb, hv⟩ := hsup hx
    obtain ⟨hc, hw⟩ := hsup hy
    change CubeDeltaIs (F (cubeCons b v)) (F (cubeCons c w)) (cubeDelta (ne_of_lt hxy))
    rw [hF _ _ hb, hF _ _ hc]
    by_cases heq : b = c
    · subst c
      have ht := (cubeCons_lt_same_iff b).mp hxy
      obtain ⟨ht', hd⟩ := hdelta b hb v w hv hw ht
      obtain ⟨h₁, hd₁⟩ := cubeCons_lt_delta_same b ht
      obtain ⟨h₂, hd₂⟩ := cubeCons_lt_delta_same (out b) ht'
      exact ⟨h₂, by rw [hd₂, hd, ← hd₁]⟩
    · cases b <;> cases c
      · contradiction
      · have ha : a = true := by cases a <;> simp_all
        obtain ⟨h₁, hd₁⟩ := cubeCons_lt_delta_cross v w
        obtain ⟨h₂, hd₂⟩ := cubeCons_lt_delta_cross (f false hb v) (f true hc w)
        rw [(hcross ha).1, (hcross ha).2]
        exact ⟨h₂, hd₂.trans hd₁.symm⟩
      · exact ((cubeCons_lt_delta_cross w v).choose.not_gt hxy).elim
      · contradiction

private noncomputable def cubeProfiles {N : ℕ} (A : Finset (Cube N)) : Finset (Cube N) :=
  open Classical in Finset.univ.filter (CubeProfile A)

@[simp] private theorem mem_cubeProfiles {N : ℕ} {A : Finset (Cube N)} {p : Cube N} :
    p ∈ cubeProfiles A ↔ CubeProfile A p := by classical simp [cubeProfiles]

private theorem card_le_cubeProfiles {N : ℕ} (A : Finset (Cube N)) :
    A.card ≤ (cubeProfiles A).card := by
  classical
  induction N with
  | zero =>
    by_cases hA : A.Nonempty
    · obtain ⟨v, hv⟩ := hA
      have heq (x y : Cube 0) : x = y := by
        cases x
        cases y
        congr 1
        funext i
        exact i.elim0
      have hA' : A = {v} := by ext w; rw [heq w v]; simp [hv]
      have hcard : A.card = 1 := congrArg Finset.card hA'
      rw [hcard]
      apply Finset.card_pos.mpr
      refine ⟨v, mem_cubeProfiles.mpr ⟨fun _ ↦ v, fun _ _ ↦ hv, ?_⟩⟩
      intro x y _ _ hxy
      exact (ne_of_lt hxy (heq x y)).elim
    · simp [Finset.not_nonempty_iff_eq_empty.mp hA]
  | succ N ih =>
    let P₀ := cubeProfiles (cubeSection A false)
    let P₁ := cubeProfiles (cubeSection A true)
    let U := (P₀ ∪ P₁).map (cubeConsEmb false)
    let I := (P₀ ∩ P₁).map (cubeConsEmb true)
    have hU : U ⊆ cubeProfiles A := by
      intro p hp
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hp
      apply mem_cubeProfiles.mpr
      rcases Finset.mem_union.mp hw with h₀ | h₁
      · exact cubeProfile_cons (fun _ ↦ false) (by simp) (fun _ _ ↦ mem_cubeProfiles.mp h₀)
      · exact cubeProfile_cons (fun _ ↦ true) (by simp) (fun _ _ ↦ mem_cubeProfiles.mp h₁)
    have hI : I ⊆ cubeProfiles A := by
      intro p hp
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨h₀, h₁⟩ := Finset.mem_inter.mp hw
      apply mem_cubeProfiles.mpr
      apply cubeProfile_cons id (by simp)
      intro b _
      cases b
      · exact mem_cubeProfiles.mp h₀
      · exact mem_cubeProfiles.mp h₁
    calc
      A.card = (cubeSection A false).card + (cubeSection A true).card := (card_cubeSections A).symm
      _ ≤ P₀.card + P₁.card := Nat.add_le_add (ih _) (ih _)
      _ = (P₀ ∪ P₁).card + (P₀ ∩ P₁).card := (Finset.card_union_add_card_inter _ _).symm
      _ = (U ∪ I).card := by
        rw [Finset.card_union_of_disjoint (cubeCons_maps_disjoint _ _),
          Finset.card_map, Finset.card_map]
      _ ≤ (cubeProfiles A).card := Finset.card_le_card (Finset.union_subset hU hI)

private def cubeSupport {N : ℕ} (p : Cube N) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ p.bits i = true

private theorem cubeSupport_injective (N : ℕ) : Function.Injective (@cubeSupport N) := by
  intro p q hpq
  cases p with | mk p =>
  cases q with | mk q =>
  apply congrArg Cube.mk
  funext i
  have hm : i ∈ cubeSupport ⟨p⟩ ↔ i ∈ cubeSupport ⟨q⟩ := by rw [hpq]
  have h : p i = true ↔ q i = true := by simpa [cubeSupport] using hm
  cases hp : p i <;> cases hq : q i <;> simp_all

private theorem card_le_of_small_cubeSupports {N D : ℕ} (hD : D ≤ N)
    (P : Finset (Cube N)) (hP : ∀ p ∈ P, (cubeSupport p).card ≤ D) :
    P.card ≤ (N + 1) ^ (D + 1) := by
  classical
  let f : Cube N ↪ Finset (Fin N) := ⟨cubeSupport, cubeSupport_injective N⟩
  let level (j : ℕ) := (Finset.univ : Finset (Fin N)).powersetCard j
  have hsub : P.map f ⊆ (Finset.range (D + 1)).biUnion level := by
    intro A hA
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hA
    have hpD := hP p hp
    exact Finset.mem_biUnion.mpr ⟨(cubeSupport p).card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  have hlevel (j : ℕ) (hj : j ∈ Finset.range (D + 1)) : (level j).card ≤ (N + 1) ^ D := by
    have hjD : j ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    calc
      (level j).card = N.choose j := by simp [level, Finset.card_powersetCard]
      _ ≤ N ^ j := choose_le_pow_self N j
      _ ≤ (N + 1) ^ j := Nat.pow_le_pow_left (by omega) _
      _ ≤ (N + 1) ^ D := Nat.pow_le_pow_right (by omega) hjD
  calc
    P.card = (P.map f).card := (Finset.card_map _).symm
    _ ≤ ((Finset.range (D + 1)).biUnion level).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (D + 1)).card * (N + 1) ^ D :=
      Finset.card_biUnion_le_card_mul _ _ _ hlevel
    _ ≤ (N + 1) ^ (D + 1) := by
      rw [Finset.card_range, pow_succ']
      exact Nat.mul_le_mul_right _ (by omega)

private def cubeMask {N : ℕ} (p x : Cube N) : Cube N :=
  ⟨fun i ↦ if p.bits i then x.bits i else false⟩

private theorem cubeMask_supported {N : ℕ} (p x : Cube N) : CubeSupported p (cubeMask p x) := by
  intro i hi
  simp [cubeMask, hi]

private theorem cubeMask_preserves_delta {N : ℕ} (p : Cube N) {x y : Cube N} (h : x < y)
    (hp : cubeDelta (ne_of_lt h) ∈ cubeSupport p) :
    CubeDeltaIs (cubeMask p x) (cubeMask p y) (cubeDelta (ne_of_lt h)) := by
  let d := cubeDelta (ne_of_lt h)
  have hp' : p.bits d = true := (Finset.mem_filter.mp hp).2
  have hx : (cubeMask p x).bits d = false := by
    simpa [cubeMask, hp'] using (cubeDelta_bits_of_lt h).1
  have hy : (cubeMask p y).bits d = true := by
    simpa [cubeMask, hp'] using (cubeDelta_bits_of_lt h).2
  have hpre (i : Fin N) (hi : i < d) : (cubeMask p x).bits i = (cubeMask p y).bits i := by
    simp only [cubeMask, cubeDelta_eq_of_lt (ne_of_lt h) hi]
  refine ⟨⟨d, hpre, hx, hy⟩, (cubeDelta_eq_iff _ _).mpr ⟨hpre, ?_⟩⟩
  change (cubeMask p x).bits d ≠ (cubeMask p y).bits d
  rw [hx, hy]
  decide

private theorem deltaMono_on_cubeProfile {N : ℕ} {A : Finset (Cube N)} {p : Cube N}
    (hp : CubeProfile A p) (φ ψ : Fin N → Fin N → Bool) :
    ∃ S ⊆ A, (cubeSupport p).card + 1 ≤ S.card ^ 4 ∧ ∃ b : Bool,
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → deltaColor φ ψ x y z = b := by
  classical
  let L := cubeSupport p
  obtain ⟨b, h₀, h₁⟩ : ∃ b : Bool, maxDeltaMono φ ψ L false ≤ maxDeltaMono φ ψ L b ∧
      maxDeltaMono φ ψ L true ≤ maxDeltaMono φ ψ L b := by
    rcases le_total (maxDeltaMono φ ψ L false) (maxDeltaMono φ ψ L true) with h | h
    · exact ⟨true, h, le_rfl⟩
    · exact ⟨false, le_rfl, h⟩
  obtain ⟨T, hT, htcard⟩ := exists_maxDeltaMono φ ψ L b
  have hsize : L.card + 1 ≤ T.card ^ 4 := by
    rw [htcard]
    calc
      L.card + 1 ≤ (maxDeltaMono φ ψ L false) ^ 2 * (maxDeltaMono φ ψ L true) ^ 2 :=
        card_le_maxDeltaMono_sq φ ψ L
      _ ≤ (maxDeltaMono φ ψ L b) ^ 2 * (maxDeltaMono φ ψ L b) ^ 2 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left h₀ _) (Nat.pow_le_pow_left h₁ _)
      _ = (maxDeltaMono φ ψ L b) ^ 4 := by ring
  obtain ⟨f, hm, hd⟩ := hp
  let g (x : Cube N) := f (cubeMask p x)
  have hg {x y : Cube N} (hx : x ∈ T) (hy : y ∈ T) (hxy : x < y) :
      CubeDeltaIs (g x) (g y) (cubeDelta (ne_of_lt hxy)) := by
    obtain ⟨hmask, hdelta⟩ := cubeMask_preserves_delta p hxy (hT.2.1 x hx y hy (ne_of_lt hxy))
    obtain ⟨h', heq⟩ := hd _ _ (cubeMask_supported p x) (cubeMask_supported p y) hmask
    exact ⟨h', heq.trans hdelta⟩
  have hginj : Set.InjOn g (↑T : Set (Cube N)) := by
    intro x hx y hy he
    rcases lt_trichotomy x y with h | h | h
    · exact (ne_of_lt (hg hx hy h).choose he).elim
    · exact h
    · exact (ne_of_lt (hg hy hx h).choose he.symm).elim
  refine ⟨T.image g, ?_, ?_, b, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact hm _ (cubeMask_supported p y)
  · rwa [Finset.card_image_of_injOn hginj]
  · intro x hx y hy z hz hxy hyz
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
    have hglt {u v : Cube N} (hu : u ∈ T) (hv : v ∈ T) (h : g u < g v) : u < v := by
      rcases lt_trichotomy u v with huv | rfl | hvu
      · exact huv
      · exact (lt_irrefl _ h).elim
      · exact ((hg hv hu hvu).choose.not_gt h).elim
    have hxy' := hglt hx' hy' hxy
    have hyz' := hglt hy' hz' hyz
    have h₁ := (hg hx' hy' hxy').choose_spec
    have h₂ := (hg hy' hz' hyz').choose_spec
    have hmono := hT.2.2 _ hx' _ hy' _ hz' hxy' hyz'
    simpa only [deltaColor, dif_pos (And.intro hxy hyz),
      dif_pos (And.intro hxy' hyz'), h₁, h₂] using hmono

private theorem cube_card (N : ℕ) : Fintype.card (Cube N) = 2 ^ N := by
  let e : Cube N ≃ (Fin N → Bool) :=
    ⟨Cube.bits, Cube.mk, fun x ↦ by cases x; rfl, fun _ ↦ rfl⟩
  simpa using Fintype.card_congr e

private noncomputable def labeledDeltaColor {N q : ℕ} (label : Cube N → Fin q)
    (φ ψ : Fin q → Fin q → Fin q → Fin N → Fin N → Bool) (x y z : Cube N) : Bool :=
  deltaColor (φ (label x) (label y) (label z)) (ψ (label x) (label y) (label z)) x y z

/-- Vertex labels can be arbitrary functions on the cube. A sufficiently large
label class contains a profile on which the two-colour delta bound still applies. -/
private theorem labeledDeltaColor_large_mono {N q D : ℕ} (hD : D ≤ N)
    (hcount : q * (N + 1) ^ (D + 1) < 2 ^ N) (label : Cube N → Fin q)
    (φ ψ : Fin q → Fin q → Fin q → Fin N → Fin N → Bool) :
    ∃ S : Finset (Cube N), D + 1 < S.card ^ 4 ∧ ∃ b : Bool,
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → labeledDeltaColor label φ ψ x y z = b := by
  classical
  have hn : (Finset.univ : Finset (Fin q)).card * (N + 1) ^ (D + 1) <
      (Finset.univ : Finset (Cube N)).card := by simpa [cube_card] using hcount
  obtain ⟨a, _, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := label) (fun _ _ ↦ Finset.mem_univ _) hn
  let A := (Finset.univ : Finset (Cube N)).filter (fun x ↦ label x = a)
  have hprof : ∃ p ∈ cubeProfiles A, D < (cubeSupport p).card := by
    by_contra! h
    exact (not_lt_of_ge ((card_le_cubeProfiles A).trans
      (card_le_of_small_cubeSupports hD _ h))) ha
  obtain ⟨p, hp, hbig⟩ := hprof
  obtain ⟨S, hS, hSize, b, hb⟩ :=
    deltaMono_on_cubeProfile (mem_cubeProfiles.mp hp) (φ a a a) (ψ a a a)
  refine ⟨S, by omega, b, ?_⟩
  intro x hx y hy z hz hxy hyz
  have hl (v : Cube N) (hv : v ∈ S) : label v = a := (Finset.mem_filter.mp (hS hv)).2
  simpa only [labeledDeltaColor, hl x hx, hl y hy, hl z hz] using hb x hx y hy z hz hxy hyz

private theorem eventually_cube_label_budget (k p : ℕ) :
    ∀ᶠ t : ℕ in atTop, (k * t) ^ p ≤ 2 ^ t ∧ ∀ q ≤ 2 ^ (2 ^ (t - 1)),
      q * (2 ^ t + 1) ^ ((k * t) ^ p + 1) < 2 ^ (2 ^ t) := by
  let C : ℕ := 4 * (k ^ p + 1)
  have hlim : Tendsto (fun t : ℕ ↦ ((C * t ^ (p + 1) : ℕ) : ℝ) / (2 : ℝ) ^ t) atTop (nhds 0) := by
    have h := (tendsto_pow_const_div_const_pow_of_one_lt (p + 1)
      (by norm_num : (1 : ℝ) < 2)).const_mul (C : ℝ)
    rw [mul_zero] at h
    refine h.congr fun t ↦ ?_
    push_cast
    ring
  have hlarge : ∀ᶠ t : ℕ in atTop, ((C * t ^ (p + 1) : ℕ) : ℝ) / (2 : ℝ) ^ t < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with t ht ht1
  let D := (k * t) ^ p
  have hpoly : C * t ^ (p + 1) < 2 ^ t := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
    have h := (div_lt_one hp).mp ht
    exact_mod_cast h
  have htp : 1 ≤ t ^ p := pow_pos (by omega : 0 < t) _
  have hD' : D + 1 ≤ (k ^ p + 1) * t ^ p := by
    dsimp [D]
    rw [mul_pow, Nat.add_mul, one_mul]
    exact Nat.add_le_add_left htp _
  have hdom : 2 * ((t + 1) * (D + 1)) ≤ C * t ^ (p + 1) := by
    calc
      2 * ((t + 1) * (D + 1)) ≤ 2 * ((2 * t) * ((k ^ p + 1) * t ^ p)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hD')
      _ = C * t ^ (p + 1) := by rw [pow_succ]; dsimp [C]; ring
  have hhalf : 2 ^ t = 2 * 2 ^ (t - 1) := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega, pow_succ']
  have hexp : (t + 1) * (D + 1) < 2 ^ (t - 1) := by omega
  have hD : D ≤ 2 ^ t := by
    have hle : D + 1 ≤ (t + 1) * (D + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hbase : 2 ^ t + 1 ≤ 2 ^ (t + 1) := by
    rw [pow_succ']
    have hp : 0 < 2 ^ t := pow_pos (by decide : 0 < (2 : ℕ)) _
    omega
  refine ⟨hD, fun q hq ↦ ?_⟩
  calc
    q * (2 ^ t + 1) ^ (D + 1) ≤ 2 ^ (2 ^ (t - 1)) * (2 ^ (t + 1)) ^ (D + 1) :=
      Nat.mul_le_mul hq (Nat.pow_le_pow_left hbase _)
    _ = 2 ^ (2 ^ (t - 1) + (t + 1) * (D + 1)) := by
      rw [← pow_mul (2 : ℕ) (t + 1) (D + 1), ← pow_add]
    _ < 2 ^ (2 ^ t) := Nat.pow_lt_pow_right (by decide) (by omega)

private theorem labeledDeltaColor_fails_cubeWitness (k : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ q ≤ 2 ^ (2 ^ (t - 1)), ∀ label : Cube (2 ^ t) → Fin q,
      ∀ φ ψ : Fin q → Fin q → Fin q → Fin (2 ^ t) → Fin (2 ^ t) → Bool,
      ∃ S : Finset (Cube (2 ^ t)), S.card = k * t ∧ ∃ b : Bool,
        ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → labeledDeltaColor label φ ψ x y z = b := by
  filter_upwards [eventually_cube_label_budget k 4] with t ht q hq label φ ψ
  let D := (k * t) ^ 4
  obtain ⟨S, hS, b, hb⟩ := labeledDeltaColor_large_mono ht.1 (ht.2 q hq) label φ ψ
  have hsize : k * t ≤ S.card := by
    by_contra! h
    exact (not_lt_of_ge (Nat.pow_le_pow_left h.le 4)) (by omega : D < S.card ^ 4)
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hsize
  exact ⟨T, hTcard, b, fun x hx y hy z hz ↦ hb x (hT hx) y (hT hy) z (hT hz)⟩

/-- The internal nodes of the full binary tree, indexed by their position. -/
private def CubeNode : ℕ → Type
  | 0 => Empty
  | n + 1 => Option (Bool × CubeNode n)

private def nodeSection {n : ℕ} (A : CubeNode (n + 1) → Prop) (b : Bool) :
    CubeNode n → Prop := fun v ↦ A (some (b, v))

/-- The maximum depth of a full branching subtree using only allowed nodes.
Skipped levels may differ from branch to branch. -/
private noncomputable def nodeRank : (n : ℕ) → (CubeNode n → Prop) → ℕ
  | 0, _ => 0
  | n + 1, A => open Classical in
      let l := nodeRank n (nodeSection A false)
      let r := nodeRank n (nodeSection A true)
      max (max l r) (if A none then min l r + 1 else 0)

private theorem nodeRank_child_le {n : ℕ} (A : CubeNode (n + 1) → Prop) (b : Bool) :
    nodeRank n (nodeSection A b) ≤ nodeRank (n + 1) A := by
  have h₀ := le_max_left (nodeRank n (nodeSection A false)) (nodeRank n (nodeSection A true))
  have h₁ := le_max_right (nodeRank n (nodeSection A false)) (nodeRank n (nodeSection A true))
  cases b
  · exact h₀.trans (le_max_left _ _)
  · exact h₁.trans (le_max_left _ _)

private theorem nodeRank_join_le {n : ℕ} {A : CubeNode (n + 1) → Prop} (h : A none) :
    min (nodeRank n (nodeSection A false)) (nodeRank n (nodeSection A true)) + 1 ≤
      nodeRank (n + 1) A := by
  classical
  rw [nodeRank.eq_2, if_pos h]
  exact le_max_right _ _

private theorem nodeRank_union_le (n : ℕ) (A B : CubeNode n → Prop) :
    nodeRank n (fun v ↦ A v ∨ B v) ≤ nodeRank n A + nodeRank n B := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let a := nodeRank (n + 1) A
    let b := nodeRank (n + 1) B
    let U (v : CubeNode (n + 1)) := A v ∨ B v
    let l := nodeRank n (nodeSection U false)
    let r := nodeRank n (nodeSection U true)
    have hparts (s : Bool) : nodeRank n (nodeSection U s) ≤
        nodeRank n (nodeSection A s) + nodeRank n (nodeSection B s) := ih _ _
    have hcap (s : Bool) : nodeRank n (nodeSection U s) ≤ a + b :=
      (hparts s).trans (Nat.add_le_add (nodeRank_child_le A s) (nodeRank_child_le B s))
    change nodeRank (n + 1) U ≤ a + b
    unfold nodeRank
    apply max_le (max_le (hcap false) (hcap true))
    split_ifs with h
    · change min l r + 1 ≤ a + b
      by_contra! hbad
      have hminl := min_le_left l r
      have hminr := min_le_right l r
      have hl : a + b ≤ l := by omega
      have hr : a + b ≤ r := by omega
      have hl' := hl.trans (hparts false)
      have hr' := hr.trans (hparts true)
      have ha₀ := nodeRank_child_le A false
      have ha₁ := nodeRank_child_le A true
      have hb₀ := nodeRank_child_le B false
      have hb₁ := nodeRank_child_le B true
      change nodeRank n (nodeSection A false) ≤ a at ha₀
      change nodeRank n (nodeSection A true) ≤ a at ha₁
      change nodeRank n (nodeSection B false) ≤ b at hb₀
      change nodeRank n (nodeSection B true) ≤ b at hb₁
      rcases h with hA | hB
      · have hstep := nodeRank_join_le hA
        have hlA : nodeRank n (nodeSection A false) = a := by omega
        have hrA : nodeRank n (nodeSection A true) = a := by omega
        rw [hlA, hrA, min_self] at hstep
        change a + 1 ≤ a at hstep
        omega
      · have hstep := nodeRank_join_le hB
        have hlB : nodeRank n (nodeSection B false) = b := by omega
        have hrB : nodeRank n (nodeSection B true) = b := by omega
        rw [hlB, hrB, min_self] at hstep
        change b + 1 ≤ b at hstep
        omega
    · exact Nat.zero_le _

private theorem nodeRank_full (n : ℕ) : nodeRank n (fun _ ↦ True) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he (s : Bool) : nodeSection (fun _ : CubeNode (n + 1) ↦ True) s = fun _ ↦ True := rfl
    simp only [nodeRank, he, ih, max_self, if_true, min_self, max_eq_right (Nat.le_succ n)]

private def nodeColorSection {n : ℕ} (c : CubeNode (n + 1) → CubeNode (n + 1) → Bool) (s : Bool) :
    CubeNode n → CubeNode n → Bool := fun u v ↦ c (some (s, u)) (some (s, v))

private def nodeColorClass {n : ℕ} (c : CubeNode (n + 1) → CubeNode (n + 1) → Bool)
    (A : CubeNode (n + 1) → Prop) (s b : Bool) : CubeNode n → Prop :=
  fun v ↦ nodeSection A s v ∧ c none (some (s, v)) = b

private noncomputable def nodeMonoSize :
    (n : ℕ) → (CubeNode n → CubeNode n → Bool) → (CubeNode n → Prop) → Bool → ℕ
  | 0, _, _, _ => 1
  | n + 1, c, A, b => open Classical in
      max (max (nodeMonoSize n (nodeColorSection c false) (nodeSection A false) b)
               (nodeMonoSize n (nodeColorSection c true) (nodeSection A true) b))
        (if A none then
          nodeMonoSize n (nodeColorSection c false) (nodeColorClass c A false b) b +
          nodeMonoSize n (nodeColorSection c true) (nodeColorClass c A true b) b
         else 1)

private theorem nodeMonoSize_child_le {n : ℕ}
    (c : CubeNode (n + 1) → CubeNode (n + 1) → Bool) (A : CubeNode (n + 1) → Prop) (s b : Bool) :
    nodeMonoSize n (nodeColorSection c s) (nodeSection A s) b ≤ nodeMonoSize (n + 1) c A b := by
  cases s
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)

private theorem nodeMonoSize_join_le {n : ℕ}
    (c : CubeNode (n + 1) → CubeNode (n + 1) → Bool) {A : CubeNode (n + 1) → Prop}
    (h : A none) (b : Bool) :
    nodeMonoSize n (nodeColorSection c false) (nodeColorClass c A false b) b +
      nodeMonoSize n (nodeColorSection c true) (nodeColorClass c A true b) b ≤
      nodeMonoSize (n + 1) c A b := by
  classical
  rw [nodeMonoSize.eq_2, if_pos h]
  exact le_max_right _ _

private theorem nodeMonoSize_pos (n : ℕ) (c : CubeNode n → CubeNode n → Bool)
    (A : CubeNode n → Prop) (b : Bool) : 1 ≤ nodeMonoSize n c A b := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (ih _ _).trans (nodeMonoSize_child_le c A false b)

private theorem nodeMonoSize_mono (n : ℕ) (c : CubeNode n → CubeNode n → Bool)
    {A B : CubeNode n → Prop} (h : ∀ v, A v → B v) (b : Bool) :
    nodeMonoSize n c A b ≤ nodeMonoSize n c B b := by
  classical
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hsect (s : Bool) : ∀ v, nodeSection A s v → nodeSection B s v := fun _ hv ↦ h _ hv
    have hcolor (s : Bool) : ∀ v, nodeColorClass c A s b v → nodeColorClass c B s b v :=
      fun v hv ↦ ⟨hsect s v hv.1, hv.2⟩
    unfold nodeMonoSize
    apply max_le_max (max_le_max (ih _ (hsect false)) (ih _ (hsect true)))
    by_cases ha : A none
    · rw [if_pos ha, if_pos (h none ha)]
      exact Nat.add_le_add (ih _ (hcolor false)) (ih _ (hcolor true))
    · rw [if_neg ha]
      split_ifs
      · have hp := nodeMonoSize_pos n (nodeColorSection c false) (nodeColorClass c B false b) b
        omega
      · exact le_rfl

private theorem nodeRank_color_partition {n : ℕ}
    (c : CubeNode (n + 1) → CubeNode (n + 1) → Bool) (A : CubeNode (n + 1) → Prop) (s : Bool) :
    nodeRank n (nodeSection A s) ≤
      nodeRank n (nodeColorClass c A s false) + nodeRank n (nodeColorClass c A s true) := by
  have h : nodeSection A s = fun v ↦ nodeColorClass c A s false v ∨ nodeColorClass c A s true v := by
    funext v
    apply propext
    cases h : c none (some (s,v)) <;> simp [nodeColorClass, h]
  exact (congrArg (nodeRank n) h).le.trans (nodeRank_union_le n _ _)

private theorem nodeRank_le_mono_product (n : ℕ)
    (c : CubeNode n → CubeNode n → Bool) (A : CubeNode n → Prop) :
    nodeRank n A ≤ (nodeMonoSize n c A false - 1) * (nodeMonoSize n c A true - 1) := by
  classical
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    let x := nodeMonoSize (n + 1) c A false
    let y := nodeMonoSize (n + 1) c A true
    let r (s : Bool) := nodeRank n (nodeSection A s)
    let u (s : Bool) := nodeMonoSize n (nodeColorSection c s) (nodeColorClass c A s false) false
    let v (s : Bool) := nodeMonoSize n (nodeColorSection c s) (nodeColorClass c A s true) true
    let P := (x - 1) * (y - 1)
    have hlocal (s : Bool) : r s ≤ P := by
      apply (ih (nodeColorSection c s) (nodeSection A s)).trans
      exact Nat.mul_le_mul (Nat.sub_le_sub_right (nodeMonoSize_child_le c A s false) 1)
        (Nat.sub_le_sub_right (nodeMonoSize_child_le c A s true) 1)
    change nodeRank (n + 1) A ≤ P
    unfold nodeRank
    apply max_le (max_le (hlocal false) (hlocal true))
    by_cases ha : A none
    · rw [if_pos ha]
      change min (r false) (r true) + 1 ≤ P
      have hu : u false + u true ≤ x := nodeMonoSize_join_le c ha false
      have hv : v false + v true ≤ y := nodeMonoSize_join_le c ha true
      have hu1 (s : Bool) : 1 ≤ u s := nodeMonoSize_pos _ _ _ _
      have hv1 (s : Bool) : 1 ≤ v s := nodeMonoSize_pos _ _ _ _
      have hx2 : 2 ≤ x := by have := hu1 false; have := hu1 true; omega
      have hy2 : 2 ≤ y := by have := hv1 false; have := hv1 true; omega
      have hcolor (s b d : Bool) :
          nodeMonoSize n (nodeColorSection c s) (nodeColorClass c A s b) d ≤
            nodeMonoSize (n + 1) c A d :=
        (nodeMonoSize_mono n _ (fun _ h ↦ h.1) d).trans (nodeMonoSize_child_le c A s d)
      have hpart (s : Bool) : r s ≤ (u s - 1) * (y - 1) + (x - 1) * (v s - 1) := by
        apply (nodeRank_color_partition c A s).trans
        apply Nat.add_le_add
        · apply (ih (nodeColorSection c s) (nodeColorClass c A s false)).trans
          exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (hcolor s false true) 1)
        · apply (ih (nodeColorSection c s) (nodeColorClass c A s true)).trans
          exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (hcolor s true false) 1)
      have hsum : r false + r true ≤ (x - 2) * (y - 1) + (x - 1) * (y - 2) := by
        have hux : (u false - 1) + (u true - 1) ≤ x - 2 := by
          have hf := hu1 false
          have ht := hu1 true
          omega
        have hvy : (v false - 1) + (v true - 1) ≤ y - 2 := by
          have hf := hv1 false
          have ht := hv1 true
          omega
        calc
          r false + r true ≤
              ((u false - 1) * (y - 1) + (x - 1) * (v false - 1)) +
              ((u true - 1) * (y - 1) + (x - 1) * (v true - 1)) :=
            Nat.add_le_add (hpart false) (hpart true)
          _ = ((u false - 1) + (u true - 1)) * (y - 1) +
              (x - 1) * ((v false - 1) + (v true - 1)) := by ring
          _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_right _ hux) (Nat.mul_le_mul_left _ hvy)
      have hxp : (x - 2) * (y - 1) + (y - 1) = P := by
        have hx : x - 2 + 1 = x - 1 := by omega
        calc
          _ = (x - 2 + 1) * (y - 1) := by rw [Nat.add_mul, one_mul]
          _ = P := by rw [hx]
      have hyp : (x - 1) * (y - 2) + (x - 1) = P := by
        have hy : y - 2 + 1 = y - 1 := by omega
        calc
          _ = (x - 1) * (y - 2 + 1) := by rw [Nat.mul_add, mul_one]
          _ = P := by rw [hy]
      have hl := min_le_left (r false) (r true)
      have hr := min_le_right (r false) (r true)
      omega
    · rw [if_neg ha]
      exact Nat.zero_le _

private theorem nodeMonoProduct_full (N : ℕ) (c : CubeNode N → CubeNode N → Bool) :
    N ≤ (nodeMonoSize N c (fun _ ↦ True) false - 1) *
      (nodeMonoSize N c (fun _ ↦ True) true - 1) := by
  simpa only [nodeRank_full] using nodeRank_le_mono_product N c (fun _ ↦ True)

/-- The first branching node separating two leaves, when the leaves differ. -/
private def cubeSplitNode : (n : ℕ) → Cube n → Cube n → Option (CubeNode n)
  | 0, _, _ => none
  | n + 1, x, y =>
      if cubeHead x = cubeHead y then
        (cubeSplitNode n (cubeTail x) (cubeTail y)).map (fun u ↦ some (cubeHead x, u))
      else some none

/-- A triple obtains its colour from its two branching nodes. The ancestor
comes first and the descendant includes the full prefix where it branches. -/
private def nodeTripleColor :
    (n : ℕ) → (CubeNode n → CubeNode n → Bool) → Cube n → Cube n → Cube n → Bool
  | 0, _, _, _, _ => false
  | n + 1, c, x, y, z =>
      if cubeHead x = cubeHead z then
        nodeTripleColor n (nodeColorSection c (cubeHead x)) (cubeTail x) (cubeTail y) (cubeTail z)
      else if cubeHead x = cubeHead y then
        ((cubeSplitNode n (cubeTail x) (cubeTail y)).map
          (fun u ↦ c none (some (cubeHead x, u)))).getD false
      else
        ((cubeSplitNode n (cubeTail y) (cubeTail z)).map
          (fun u ↦ c none (some (cubeHead y, u)))).getD false

private def NodeMonoOn {n : ℕ} (c : CubeNode n → CubeNode n → Bool)
    (A : CubeNode n → Prop) (b : Bool) (S : Finset (Cube n)) : Prop :=
  S.Nonempty ∧
  (∀ x ∈ S, ∀ y ∈ S, x < y → ∃ u, cubeSplitNode n x y = some u ∧ A u) ∧
  (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → nodeTripleColor n c x y z = b)

private theorem nodeMonoOn_lift {n : ℕ}
    {c : CubeNode (n + 1) → CubeNode (n + 1) → Bool} {A : CubeNode (n + 1) → Prop}
    {s b : Bool} {S : Finset (Cube n)}
    (hS : NodeMonoOn (nodeColorSection c s) (nodeSection A s) b S) :
    NodeMonoOn c A b (S.map (cubeConsEmb s)) := by
  refine ⟨hS.1.map, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    change cubeCons s u < cubeCons s v at hxy
    obtain ⟨p, hp, ha⟩ := hS.2.1 u hu v hv ((cubeCons_lt_same_iff s).mp hxy)
    refine ⟨some (s, p), ?_, ha⟩
    change cubeSplitNode (n + 1) (cubeCons s u) (cubeCons s v) = _
    simp [cubeSplitNode.eq_2, hp]; rfl
  · intro x hx y hy z hz hxy hyz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    change cubeCons s u < cubeCons s v at hxy
    change cubeCons s v < cubeCons s w at hyz
    change nodeTripleColor (n + 1) c (cubeCons s u) (cubeCons s v) (cubeCons s w) = b
    simpa [nodeTripleColor.eq_2] using
      hS.2.2 u hu v hv w hw ((cubeCons_lt_same_iff s).mp hxy) ((cubeCons_lt_same_iff s).mp hyz)

private theorem nodeMonoOn_join {n : ℕ}
    {c : CubeNode (n + 1) → CubeNode (n + 1) → Bool} {A : CubeNode (n + 1) → Prop}
    {b : Bool} {L R : Finset (Cube n)} (hA : A none)
    (hL : NodeMonoOn (nodeColorSection c false) (nodeColorClass c A false b) b L)
    (hR : NodeMonoOn (nodeColorSection c true) (nodeColorClass c A true b) b R) :
    NodeMonoOn c A b (L.map (cubeConsEmb false) ∪ R.map (cubeConsEmb true)) := by
  classical
  let T (s : Bool) := if s then R else L
  have hmono (s : Bool) : NodeMonoOn (nodeColorSection c s) (nodeColorClass c A s b) b (T s) := by
    cases s
    · exact hL
    · exact hR
  have hdecomp (x : Cube (n + 1))
      (hx : x ∈ L.map (cubeConsEmb false) ∪ R.map (cubeConsEmb true)) :
      ∃ s u, u ∈ T s ∧ cubeCons s u = x := by
    rcases Finset.mem_union.mp hx with hl | hr
    · obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hl
      exact ⟨false, u, hu, he⟩
    · obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hr
      exact ⟨true, u, hu, he⟩
  have himpossible (u v : Cube n) :
      ¬ cubeCons true u < cubeCons false v := (cubeCons_lt_delta_cross v u).choose.not_gt
  have hsplit (s : Bool) (u v : Cube n) (hu : u ∈ T s) (hv : v ∈ T s)
      (huv : cubeCons s u < cubeCons s v) :
      ∃ p, cubeSplitNode n u v = some p ∧ nodeColorClass c A s b p :=
    (hmono s).2.1 u hu v hv ((cubeCons_lt_same_iff s).mp huv)
  have hpairs (s : Bool) (u v : Cube n) (hu : u ∈ T s) (hv : v ∈ T s)
      (huv : cubeCons s u < cubeCons s v) :
      ∃ p, cubeSplitNode (n + 1) (cubeCons s u) (cubeCons s v) = some p ∧ A p := by
    obtain ⟨p, hp, ha⟩ := hsplit s u v hu hv huv
    exact ⟨some (s,p), by simp [cubeSplitNode.eq_2, hp]; rfl, ha.1⟩
  have hsame (s : Bool) (u v w : Cube n) (hu : u ∈ T s) (hv : v ∈ T s) (hw : w ∈ T s)
      (huv : cubeCons s u < cubeCons s v) (hvw : cubeCons s v < cubeCons s w) :
      nodeTripleColor (n + 1) c (cubeCons s u) (cubeCons s v) (cubeCons s w) = b := by
    simpa [nodeTripleColor.eq_2] using (hmono s).2.2 _ hu _ hv _ hw
      ((cubeCons_lt_same_iff s).mp huv) ((cubeCons_lt_same_iff s).mp hvw)
  refine ⟨hL.1.map.mono Finset.subset_union_left, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨s, u, hu, rfl⟩ := hdecomp x hx
    obtain ⟨t, v, hv, rfl⟩ := hdecomp y hy
    cases s <;> cases t
    · exact hpairs false u v hu hv hxy
    · exact ⟨none, by simp [cubeSplitNode.eq_2], hA⟩
    · exact (himpossible u v hxy).elim
    · exact hpairs true u v hu hv hxy
  · intro x hx y hy z hz hxy hyz
    obtain ⟨s, u, hu, rfl⟩ := hdecomp x hx
    obtain ⟨t, v, hv, rfl⟩ := hdecomp y hy
    obtain ⟨e, w, hw, rfl⟩ := hdecomp z hz
    cases s <;> cases t <;> cases e
    · exact hsame false u v w hu hv hw hxy hyz
    · obtain ⟨p, hp, ha⟩ := hsplit false u v hu hv hxy
      simpa [nodeTripleColor.eq_2, hp] using ha.2
    · exact (himpossible v w hyz).elim
    · obtain ⟨p, hp, ha⟩ := hsplit true v w hv hw hyz
      simpa [nodeTripleColor.eq_2, hp] using ha.2
    · exact (himpossible u v hxy).elim
    · exact (himpossible u v hxy).elim
    · exact (himpossible v w hyz).elim
    · exact hsame true u v w hu hv hw hxy hyz

/-- A node can branch inside a leaf set when both of its children meet the set. -/
private def cubeLive : (n : ℕ) → Finset (Cube n) → CubeNode n → Prop
  | 0, _, _ => False
  | n + 1, S, u => match (show Option (Bool × CubeNode n) from u) with
    | none => (cubeSection S false).Nonempty ∧ (cubeSection S true).Nonempty
    | some (b, v) => cubeLive n (cubeSection S b) v

private theorem cubeLive_nonempty (n : ℕ) (S : Finset (Cube n)) {u : CubeNode n}
    (h : cubeLive n S u) : S.Nonempty := by
  induction n with
  | zero => exact False.elim h
  | succ n ih =>
    change Option (Bool × CubeNode n) at u
    cases u with
    | none =>
      have hh : (cubeSection S false).Nonempty ∧ (cubeSection S true).Nonempty := h
      obtain ⟨x, hx⟩ := hh.1
      exact ⟨cubeCons false x, mem_cubeSection.mp hx⟩
    | some u =>
      obtain ⟨b, v⟩ := u
      have hh : cubeLive n (cubeSection S b) v := h
      obtain ⟨x, hx⟩ := ih (cubeSection S b) hh
      exact ⟨cubeCons b x, mem_cubeSection.mp hx⟩

private theorem nodeMonoSize_of_empty_nodes (n : ℕ) (c : CubeNode n → CubeNode n → Bool)
    (A : CubeNode n → Prop) (b : Bool) (hA : ∀ u, ¬ A u) : nodeMonoSize n c A b = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h₀ := ih (nodeColorSection c false) (nodeSection A false) (fun u ↦ hA (some (false, u)))
    have h₁ := ih (nodeColorSection c true) (nodeSection A true) (fun u ↦ hA (some (true, u)))
    simp only [nodeMonoSize.eq_2, h₀, h₁, if_neg (hA none), max_self]

private theorem nodeMonoOn_singleton {n : ℕ} (c : CubeNode n → CubeNode n → Bool)
    (A : CubeNode n → Prop) (b : Bool) (x : Cube n) : NodeMonoOn c A b {x} := by
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · intro u hu v hv huv
    simp only [Finset.mem_singleton] at hu hv
    exact (ne_of_lt huv (hu.trans hv.symm)).elim
  · intro u hu v hv _ _ huv _
    simp only [Finset.mem_singleton] at hu hv
    exact (ne_of_lt huv (hu.trans hv.symm)).elim

private theorem exists_nodeMonoSize_in_leaves (n : ℕ) (c : CubeNode n → CubeNode n → Bool)
    (A : CubeNode n → Prop) (b : Bool) (B : Finset (Cube n)) (hB : B.Nonempty)
    (hAB : ∀ u, A u → cubeLive n B u) :
    ∃ S ⊆ B, nodeMonoSize n c A b ≤ S.card ∧ NodeMonoOn c A b S := by
  classical
  induction n with
  | zero =>
    obtain ⟨x, hx⟩ := hB
    exact ⟨{x}, Finset.singleton_subset_iff.mpr hx, by simp [nodeMonoSize], nodeMonoOn_singleton c A b x⟩
  | succ n ih =>
    let x (s : Bool) := nodeMonoSize n (nodeColorSection c s) (nodeSection A s) b
    have hsection (s : Bool) : ∀ u, nodeSection A s u → cubeLive n (cubeSection B s) u :=
      fun u h ↦ hAB (some (s, u)) h
    have hmap (s : Bool) (T : Finset (Cube n)) (hT : T ⊆ cubeSection B s) :
        T.map (cubeConsEmb s) ⊆ B := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact mem_cubeSection.mp (hT hw)
    have hchild (s : Bool) : ∃ S ⊆ B, x s ≤ S.card ∧ NodeMonoOn c A b S := by
      by_cases hs : (cubeSection B s).Nonempty
      · obtain ⟨T, hT, hTcard, hTmono⟩ := ih (nodeColorSection c s) (nodeSection A s)
          (cubeSection B s) hs (hsection s)
        exact ⟨T.map (cubeConsEmb s), hmap s T hT, by simpa using hTcard, nodeMonoOn_lift hTmono⟩
      · have hempty (u : CubeNode n) : ¬ nodeSection A s u := fun h ↦
          hs (cubeLive_nonempty n _ (hsection s u h))
        have hx : x s = 1 := nodeMonoSize_of_empty_nodes n _ _ _ hempty
        obtain ⟨v, hv⟩ := hB
        exact ⟨{v}, Finset.singleton_subset_iff.mpr hv, by simp [hx], nodeMonoOn_singleton c A b v⟩
    obtain ⟨S, hS, hSsize, hSmono⟩ :
        ∃ S ⊆ B, max (x false) (x true) ≤ S.card ∧ NodeMonoOn c A b S := by
      rcases le_total (x false) (x true) with h | h
      · simpa only [max_eq_right h] using hchild true
      · simpa only [max_eq_left h] using hchild false
    by_cases ha : A none
    · let y (s : Bool) := nodeMonoSize n (nodeColorSection c s) (nodeColorClass c A s b) b
      have he : nodeMonoSize (n + 1) c A b = max (max (x false) (x true)) (y false + y true) := by
        rw [nodeMonoSize.eq_2, if_pos ha]
      rcases le_total (max (x false) (x true)) (y false + y true) with h | h
      · have hab : (cubeSection B false).Nonempty ∧ (cubeSection B true).Nonempty := hAB none ha
        obtain ⟨L, hL, hLsize, hLmono⟩ := ih (nodeColorSection c false) (nodeColorClass c A false b)
          (cubeSection B false) hab.1 (fun u hu ↦ hsection false u hu.1)
        obtain ⟨R, hR, hRsize, hRmono⟩ := ih (nodeColorSection c true) (nodeColorClass c A true b)
          (cubeSection B true) hab.2 (fun u hu ↦ hsection true u hu.1)
        refine ⟨L.map (cubeConsEmb false) ∪ R.map (cubeConsEmb true),
          Finset.union_subset (hmap false L hL) (hmap true R hR), ?_, nodeMonoOn_join ha hLmono hRmono⟩
        rw [he, max_eq_right h, Finset.card_union_of_disjoint (cubeCons_maps_disjoint _ _),
          Finset.card_map, Finset.card_map]
        exact Nat.add_le_add hLsize hRsize
      · exact ⟨S, hS, by rwa [he, max_eq_left h], hSmono⟩
    · have hpos : 1 ≤ max (x false) (x true) :=
        (nodeMonoSize_pos n (nodeColorSection c false) (nodeSection A false) b).trans (le_max_left _ _)
      have he : nodeMonoSize (n + 1) c A b = max (x false) (x true) := by
        rw [nodeMonoSize.eq_2, if_neg ha]
        exact max_eq_left hpos
      exact ⟨S, hS, by rwa [he], hSmono⟩

private theorem cubeLive_univ (n : ℕ) (u : CubeNode n) : cubeLive n Finset.univ u := by
  induction n with
  | zero => exact u.elim
  | succ n ih =>
    have hs (s : Bool) : cubeSection (Finset.univ : Finset (Cube (n + 1))) s = Finset.univ := by
      ext x
      simp
    change Option (Bool × CubeNode n) at u
    cases u with
    | none =>
      change (cubeSection (Finset.univ : Finset (Cube (n + 1))) false).Nonempty ∧
        (cubeSection (Finset.univ : Finset (Cube (n + 1))) true).Nonempty
      rw [hs false, hs true]
      exact ⟨⟨⟨fun _ ↦ false⟩, Finset.mem_univ _⟩, ⟨⟨fun _ ↦ false⟩, Finset.mem_univ _⟩⟩
    | some u =>
      obtain ⟨b, v⟩ := u
      change cubeLive n (cubeSection (Finset.univ : Finset (Cube (n + 1))) b) v
      rw [hs]
      exact ih v

private theorem exists_nodeMonoSize (n : ℕ) (c : CubeNode n → CubeNode n → Bool)
    (A : CubeNode n → Prop) (b : Bool) :
    ∃ S : Finset (Cube n), nodeMonoSize n c A b ≤ S.card ∧ NodeMonoOn c A b S := by
  have hn : (Finset.univ : Finset (Cube n)).Nonempty := ⟨⟨fun _ ↦ false⟩, Finset.mem_univ _⟩
  obtain ⟨S, _, hS, hm⟩ := exists_nodeMonoSize_in_leaves n c A b _ hn (fun u _ ↦ cubeLive_univ n u)
  exact ⟨S, hS, hm⟩

/-- Even if both actual branching nodes are used, every binary colouring of
their comparisons admits a monochromatic set of more than square-root size
in the dimension. -/
private theorem nodeTripleColor_square_mono {N : ℕ} (c : CubeNode N → CubeNode N → Bool) :
    ∃ S : Finset (Cube N), N ≤ (S.card - 1) ^ 2 ∧ ∃ b : Bool,
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → nodeTripleColor N c x y z = b := by
  let f (b : Bool) := nodeMonoSize N c (fun _ ↦ True) b
  obtain ⟨b, h₀, h₁⟩ : ∃ b : Bool, f false ≤ f b ∧ f true ≤ f b := by
    rcases le_total (f false) (f true) with h | h
    · exact ⟨true, h, le_rfl⟩
    · exact ⟨false, le_rfl, h⟩
  obtain ⟨S, hS, hmono⟩ := exists_nodeMonoSize N c (fun _ ↦ True) b
  have hs : f b ≤ S.card := hS
  refine ⟨S, ?_, b, hmono.2.2⟩
  rw [pow_two]
  exact (nodeMonoProduct_full N c).trans (Nat.mul_le_mul
    (Nat.sub_le_sub_right (h₀.trans hs) _) (Nat.sub_le_sub_right (h₁.trans hs) _))

private theorem nodeTripleColor_fails_cubeWitness (k : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ c : CubeNode (2 ^ t) → CubeNode (2 ^ t) → Bool,
      ∃ S : Finset (Cube (2 ^ t)), S.card = k * t ∧ ∃ b : Bool,
        ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → nodeTripleColor (2 ^ t) c x y z = b := by
  have hlim : Tendsto (fun t : ℕ ↦ ((k * t : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ t) atTop (nhds 0) := by
    have h := (tendsto_pow_const_div_const_pow_of_one_lt 2
      (by norm_num : (1 : ℝ) < 2)).const_mul ((k : ℝ) ^ 2)
    rw [mul_zero] at h
    refine h.congr fun t ↦ ?_
    push_cast
    ring
  filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht c
  have hlt : (k * t) ^ 2 < 2 ^ t := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
    have h := (div_lt_one hp).mp ht
    exact_mod_cast h
  obtain ⟨S, hS, b, hb⟩ := nodeTripleColor_square_mono c
  have hsize : k * t ≤ S.card := by
    by_contra! hn
    exact (not_lt_of_ge (hS.trans (Nat.pow_le_pow_left (by omega : S.card - 1 ≤ k * t) _))) hlt
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hsize
  exact ⟨T, hTcard, b, fun x hx y hy z hz ↦ hb x (hT hx) y (hT hy) z (hT hz)⟩

private theorem card_le_pow_nodeRank_live (n : ℕ) (S : Finset (Cube n)) :
    S.card ≤ (n + 1) ^ (nodeRank n (cubeLive n S) + 1) := by
  induction n with
  | zero =>
    have h := S.card_le_univ
    simpa [cube_card, nodeRank] using h
  | succ n ih =>
    let r := nodeRank (n + 1) (cubeLive (n + 1) S)
    let f (s : Bool) := nodeRank n (cubeLive n (cubeSection S s))
    have hsection (s : Bool) : nodeSection (cubeLive (n + 1) S) s = cubeLive n (cubeSection S s) := rfl
    have hf (s : Bool) : f s ≤ r := by
      simpa only [hsection] using nodeRank_child_le (cubeLive (n + 1) S) s
    have hbound (s : Bool) : (cubeSection S s).card ≤ (n + 1) ^ (r + 1) :=
      (ih _).trans (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right (hf s) 1))
    have hstep (s : Bool) (hs : f s + 1 ≤ r) : (cubeSection S s).card ≤ (n + 1) ^ r :=
      (ih _).trans (Nat.pow_le_pow_right (by omega) hs)
    have hsum : S.card ≤ (n + 1) ^ r + (n + 1) ^ (r + 1) := by
      rw [← card_cubeSections S]
      by_cases hl : (cubeSection S false).Nonempty
      · by_cases hr : (cubeSection S true).Nonempty
        · have hroot : cubeLive (n + 1) S none := ⟨hl, hr⟩
          have hmin : min (f false) (f true) + 1 ≤ r := by
            simpa only [hsection] using nodeRank_join_le hroot
          rcases le_total (f false) (f true) with h | h
          · rw [min_eq_left h] at hmin
            exact Nat.add_le_add (hstep false hmin) (hbound true)
          · rw [min_eq_right h] at hmin
            simpa only [Nat.add_comm] using Nat.add_le_add (hbound false) (hstep true hmin)
        · rw [Finset.not_nonempty_iff_eq_empty.mp hr, Finset.card_empty, Nat.add_zero]
          exact (hbound false).trans (Nat.le_add_left _ _)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hl, Finset.card_empty, Nat.zero_add]
        exact (hbound true).trans (Nat.le_add_left _ _)
    calc
      S.card ≤ (n + 1) ^ r + (n + 1) ^ (r + 1) := hsum
      _ = (n + 1 + 1) * (n + 1) ^ r := by rw [pow_succ']; ring
      _ ≤ (n + 1 + 1) * (n + 1 + 1) ^ r :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (n + 1 + 1) ^ (r + 1) := (pow_succ' _ _).symm

private noncomputable def labeledNodeTripleColor {N q : ℕ} (label : Cube N → Fin q)
    (c : Fin q → Fin q → Fin q → CubeNode N → CubeNode N → Bool) (x y z : Cube N) : Bool :=
  nodeTripleColor N (c (label x) (label y) (label z)) x y z

private theorem labeledNodeTripleColor_large_mono {N q D : ℕ}
    (hcount : q * (N + 1) ^ (D + 1) < 2 ^ N) (label : Cube N → Fin q)
    (c : Fin q → Fin q → Fin q → CubeNode N → CubeNode N → Bool) :
    ∃ S : Finset (Cube N), D < (S.card - 1) ^ 2 ∧ ∃ b : Bool,
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → labeledNodeTripleColor label c x y z = b := by
  classical
  have hn : (Finset.univ : Finset (Fin q)).card * (N + 1) ^ (D + 1) <
      (Finset.univ : Finset (Cube N)).card := by simpa [cube_card] using hcount
  obtain ⟨v, _, hv⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := label) (fun _ _ ↦ Finset.mem_univ _) hn
  let B := (Finset.univ : Finset (Cube N)).filter (fun x ↦ label x = v)
  have hB : B.Nonempty := Finset.card_pos.mp ((Nat.zero_le _).trans_lt hv)
  let A := cubeLive N B
  let d := c v v v
  have hr : D < nodeRank N A := by
    by_contra! he
    exact (not_lt_of_ge ((card_le_pow_nodeRank_live N B).trans
      (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right he 1)))) hv
  let f (b : Bool) := nodeMonoSize N d A b
  obtain ⟨b, h₀, h₁⟩ : ∃ b : Bool, f false ≤ f b ∧ f true ≤ f b := by
    rcases le_total (f false) (f true) with h | h
    · exact ⟨true, h, le_rfl⟩
    · exact ⟨false, le_rfl, h⟩
  obtain ⟨S, hS, hs, hm⟩ := exists_nodeMonoSize_in_leaves N d A b B hB (fun _ h ↦ h)
  have hsize : D < (S.card - 1) ^ 2 := by
    rw [pow_two]
    exact hr.trans_le ((nodeRank_le_mono_product N d A).trans (Nat.mul_le_mul
      (Nat.sub_le_sub_right (h₀.trans hs) _) (Nat.sub_le_sub_right (h₁.trans hs) _)))
  refine ⟨S, hsize, b, ?_⟩
  intro x hx y hy z hz hxy hyz
  have hl (u : Cube N) (hu : u ∈ S) : label u = v := (Finset.mem_filter.mp (hS hu)).2
  simpa only [labeledNodeTripleColor, hl x hx, hl y hy, hl z hz, d] using
    hm.2.2 x hx y hy z hz hxy hyz

private theorem labeledNodeTripleColor_fails_cubeWitness (k : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ q ≤ 2 ^ (2 ^ (t - 1)), ∀ label : Cube (2 ^ t) → Fin q,
      ∀ c : Fin q → Fin q → Fin q → CubeNode (2 ^ t) → CubeNode (2 ^ t) → Bool,
      ∃ S : Finset (Cube (2 ^ t)), S.card = k * t ∧ ∃ b : Bool,
        ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → labeledNodeTripleColor label c x y z = b := by
  filter_upwards [eventually_cube_label_budget k 2] with t ht q hq label c
  obtain ⟨S, hS, b, hb⟩ := labeledNodeTripleColor_large_mono (ht.2 q hq) label c
  have hsize : k * t ≤ S.card := by
    by_contra! h
    exact (not_lt_of_ge (Nat.pow_le_pow_left (by omega : S.card - 1 ≤ k * t) 2)) hS
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hsize
  exact ⟨T, hTcard, b, fun x hx y hy z hz hxy hyz ↦ hb x (hT hx) y (hT hy) z (hT hz) hxy hyz⟩

end OMA.Erdos564Aux

theorem OMA.solution : type_of% @Erdos564.erdos_564 := by
  apply OMA.Erdos564Aux.tower_cube_iff.mpr
  sorry

