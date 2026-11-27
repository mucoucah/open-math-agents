import FormalConjectures.ErdosProblems.«19»

-- Problem: Erdős Problem 19 — kahn
-- Partial: everything is reduced to ONE sorry, bounded_rank_list_color (Kahn list-colouring nibble).

open Filter

namespace OMA19

open Erdos19 Erdos19.EFLConfig

open scoped Classical in
/-- generalisation of colorable_of_sharedColoring to m >= n colours -/
theorem colorable_of_sharedColoring_le {V : Type*} {n : ℕ} (C : EFLConfig V n) (m : ℕ)
    (hm : n ≤ m) (c : V → Fin m)
    (hc : ∀ i u v, u ∈ C.A i → v ∈ C.A i → C.IsShared u → C.IsShared v → c u = c v → u = v) :
    C.graph.Colorable m := by
  let P : Fin n → Finset V := fun i => (C.A i).filter (fun v => ¬ C.IsShared v)
  let U : Fin n → Finset V := fun i => (C.A i).filter C.IsShared
  let F : Fin n → Finset (Fin m) := fun i => Finset.univ \ (U i).image c
  have hcard : ∀ i, (P i).card ≤ (F i).card := by
    intro i
    have h1 : (U i).card + (P i).card = n := by
      rw [← C.card_eq i]; exact Finset.card_filter_add_card_filter_not _
    have h2 : ((U i).image c).card ≤ (U i).card := Finset.card_image_le
    have h3 : (F i).card = m - ((U i).image c).card := by
      simp [F, Finset.card_sdiff]
    omega
  have hne : ∀ i, Nonempty (P i ↪ F i) := fun i =>
    Function.Embedding.nonempty_of_card_le (by simpa using hcard i)
  let e : ∀ i, P i ↪ F i := fun i => Classical.choice (hne i)
  let idx : V → Fin n := fun v => Classical.choose (C.cover v)
  have hidx : ∀ v, v ∈ C.A (idx v) := fun v => Classical.choose_spec (C.cover v)
  let col : V → Fin m := fun v =>
    if h : C.IsShared v then c v
    else ((e (idx v) ⟨v, Finset.mem_filter.2 ⟨hidx v, h⟩⟩ : F (idx v)) : Fin m)
  have col_priv : ∀ v (hv : ¬ C.IsShared v) j (hj : v ∈ C.A j),
      col v = ((e j ⟨v, Finset.mem_filter.2 ⟨hj, hv⟩⟩ : F j) : Fin m) := by
    intro v hv j hj
    have key : ∀ i (hi : i = j) (p : v ∈ P i), ((e i ⟨v, p⟩ : F i) : Fin m) =
        ((e j ⟨v, Finset.mem_filter.2 ⟨hj, hv⟩⟩ : F j) : Fin m) := by
      rintro i rfl p; rfl
    simp only [col, dif_neg hv]
    exact key _ (C.eq_of_not_shared hv (hidx v) hj) _
  have col_free : ∀ v (hv : ¬ C.IsShared v) j (hj : v ∈ C.A j), col v ∈ F j := by
    intro v hv j hj
    rw [col_priv v hv j hj]; exact Subtype.property _
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  rintro u v ⟨huv, j, hu, hv⟩ heq
  by_cases su : C.IsShared u <;> by_cases sv : C.IsShared v
  · have : col u = c u := dif_pos su
    have : col v = c v := dif_pos sv
    exact huv (hc j u v hu hv su sv (by simp_all))
  · have h1 := col_free v sv j hv
    have : col u = c u := dif_pos su
    simp only [F, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image] at h1
    exact h1 ⟨u, Finset.mem_filter.2 ⟨hu, su⟩, by rw [← this, heq]⟩
  · have h1 := col_free u su j hu
    have : col v = c v := dif_pos sv
    simp only [F, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image] at h1
    exact h1 ⟨v, Finset.mem_filter.2 ⟨hv, sv⟩, by rw [← this, ← heq]⟩
  · rw [col_priv u su j hu, col_priv v sv j hv] at heq
    have := (e j).injective (Subtype.ext heq)
    exact huv (congrArg Subtype.val this)

theorem le_floor_mul (ε : ℝ) (hε : 0 < ε) (n : ℕ) : n ≤ ⌊(1 + ε) * n⌋₊ := by
  apply Nat.le_floor
  have : (0 : ℝ) ≤ ε * n := by positivity
  nlinarith

open Finset
open scoped BigOperators

def Linear {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1

def incident {n : ℕ} (H : Finset (Finset (Fin n))) (i : Fin n) :
    Finset (Finset (Fin n)) :=
  H.filter (fun A => i ∈ A)

def meeting {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  H.filter (fun B => (A ∩ B).Nonempty)

def ProperOn {n : ℕ} {κ : Type*} (H : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → κ) : Prop :=
  ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B

theorem Linear.mono {n : ℕ} {H K : Finset (Finset (Fin n))} (h : Linear H)
    (hKH : K ⊆ H) : Linear K :=
  fun A hA B hB => h A (hKH hA) B (hKH hB)

theorem incident_mul_le {n : ℕ} {H : Finset (Finset (Fin n))} (h : Linear H)
    (r : ℕ) (hr : ∀ A ∈ H, r + 1 ≤ A.card) (i : Fin n) :
    r * (incident H i).card ≤ n := by
  let K := incident H i
  have hd : (K : Set (Finset (Fin n))).PairwiseDisjoint (fun A => A.erase i) := by
    intro A hA B hB hAB
    obtain ⟨hA', hiA⟩ := mem_filter.mp hA
    obtain ⟨hB', hiB⟩ := mem_filter.mp hB
    apply Finset.disjoint_left.mpr
    intro j hjA hjB
    have hji := (Finset.mem_erase.mp hjA).1
    exact hji (Finset.card_le_one.mp (h A hA' B hB' hAB) j
      (mem_inter.mpr ⟨mem_of_mem_erase hjA, mem_of_mem_erase hjB⟩)
      i (mem_inter.mpr ⟨hiA, hiB⟩))
  calc
    r * K.card = ∑ _A ∈ K, r := by simp [Nat.mul_comm]
    _ ≤ ∑ A ∈ K, (A.erase i).card := by
      apply Finset.sum_le_sum
      intro A hA
      obtain ⟨hA', hiA⟩ := mem_filter.mp hA
      rw [Finset.card_erase_of_mem hiA]
      have := hr A hA'
      omega
    _ = (K.biUnion (fun A => A.erase i)).card := (Finset.card_biUnion hd).symm
    _ ≤ n := by simpa using Finset.card_le_univ (K.biUnion (fun A => A.erase i))

theorem meeting_card_le {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (d : ℕ) (hd : ∀ i ∈ A, (incident H i).card ≤ d) :
    (meeting H A).card ≤ A.card * d := by
  have heq : meeting H A = A.biUnion (incident H) := by
    ext B
    simp only [meeting, incident, mem_filter, mem_biUnion, Finset.Nonempty, mem_inter]
    constructor
    · rintro ⟨hB, i, hiA, hiB⟩
      exact ⟨i, hiA, hB, hiB⟩
    · rintro ⟨i, hiA, hB, hiB⟩
      exact ⟨hB, i, hiA, hiB⟩
  calc
    (meeting H A).card = (A.biUnion (incident H)).card := congrArg Finset.card heq
    _ ≤ ∑ i ∈ A, (incident H i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, d := Finset.sum_le_sum hd
    _ = A.card * d := by simp

/-- Color large supports in descending order of size. -/
theorem large_rank_color {n : ℕ} (H : Finset (Finset (Fin n))) (q m : ℕ)
    (hq : 0 < q) (hm : n + n / q < m) (h : Linear H)
    (hsize : ∀ A ∈ H, q + 1 ≤ A.card) :
    ∃ c : Finset (Fin n) → Fin m, ProperOn H c := by
  induction H using Finset.strongInductionOn with
  | _ H ih =>
    by_cases hH : H.Nonempty
    · obtain ⟨A, hA, hmin⟩ := H.exists_min_image Finset.card hH
      let K := H.erase A
      have hKH : K ⊆ H := Finset.erase_subset _ _
      obtain ⟨c, hc⟩ := ih K (Finset.erase_ssubset hA) (h.mono hKH)
        (fun B hB => hsize B (hKH hB))
      let s := A.card - 1
      have hs : A.card = s + 1 := by
        have := hsize A hA
        dsimp [s]
        omega
      have hqs : q ≤ s := by have := hsize A hA; omega
      have hsp : 0 < s := hq.trans_le hqs
      have hmeet : (meeting K A).card ≤ n + n / q := by
        calc
          (meeting K A).card ≤ A.card * (n / s) := by
            apply meeting_card_le
            intro i _
            rw [Nat.le_div_iff_mul_le hsp, Nat.mul_comm]
            exact incident_mul_le (h.mono hKH) s
              (fun B hB => hs ▸ hmin B (hKH hB)) i
          _ = s * (n / s) + n / s := by rw [hs, Nat.add_mul, Nat.one_mul]
          _ ≤ n + n / q := Nat.add_le_add
            (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _)
            ((Nat.le_div_iff_mul_le hq).mpr <|
              (Nat.mul_le_mul_left (n / s) hqs).trans (Nat.div_mul_le_self _ _))
      let blocked := (meeting K A).image c
      have hblocked : blocked.card < m := (Finset.card_image_le.trans hmeet).trans_lt hm
      have hfree : (univ \ blocked).Nonempty := by
        apply Finset.card_pos.mp
        rwa [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin, Nat.sub_pos_iff_lt]
      obtain ⟨w, hw⟩ := hfree
      have hne : ∀ B ∈ K, (A ∩ B).Nonempty → w ≠ c B := by
        intro B hB hi he
        exact (mem_sdiff.mp hw).2 (he ▸ mem_image_of_mem c (mem_filter.mpr ⟨hB, hi⟩))
      refine ⟨fun B => if B = A then w else c B, ?_⟩
      intro B hB D hD hBD hi
      by_cases hBA : B = A
      · subst B
        have hDA := Ne.symm hBD
        simpa only [if_pos rfl, if_true, if_neg hDA] using hne D (mem_erase.mpr ⟨hDA, hD⟩) hi
      by_cases hDA : D = A
      · subst D
        have hi' : (A ∩ B).Nonempty := by simpa only [Finset.inter_comm] using hi
        simpa only [if_pos rfl, if_true, if_neg hBA] using
          (hne B (mem_erase.mpr ⟨hBA, hB⟩) hi').symm
      simpa only [if_neg hBA, if_neg hDA] using
        hc B (mem_erase.mpr ⟨hBA, hB⟩) D (mem_erase.mpr ⟨hDA, hD⟩) hBD hi
    · have : 0 < m := Nat.zero_le _ |>.trans_lt hm
      exact ⟨fun _ => ⟨0, this⟩, fun A hA => (hH ⟨A, hA⟩).elim⟩

open scoped Classical in
noncomputable def support {V : Type*} {n : ℕ} (C : EFLConfig V n) (v : V) :
    Finset (Fin n) :=
  univ.filter (fun i => v ∈ C.A i)

@[simp] theorem mem_support {V : Type*} {n : ℕ} (C : EFLConfig V n) (v : V) (i : Fin n) :
    i ∈ support C v ↔ v ∈ C.A i := by
  simp [support]

theorem support_inter_le {V : Type*} {n : ℕ} (C : EFLConfig V n) {u v : V}
    (huv : u ≠ v) : (support C u ∩ support C v).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra h
  obtain ⟨hiu, hiv⟩ := mem_inter.mp hi
  obtain ⟨hju, hjv⟩ := mem_inter.mp hj
  exact huv (Finset.card_le_one.mp (C.inter_le i j h) u
    (mem_inter.mpr ⟨(mem_support C u i).mp hiu, (mem_support C u j).mp hju⟩) v
    (mem_inter.mpr ⟨(mem_support C v i).mp hiv, (mem_support C v j).mp hjv⟩))

theorem shared_of_linear_color {V : Type*} {n m : ℕ} (C : EFLConfig V n)
    (hcol : ∀ H : Finset (Finset (Fin n)), Linear H → (∀ A ∈ H, 2 ≤ A.card) →
      ∃ c : Finset (Fin n) → Fin m, ProperOn H c) :
    ∃ c : V → Fin m, ∀ i u v, u ∈ C.A i → v ∈ C.A i → C.IsShared u →
      C.IsShared v → c u = c v → u = v := by
  open scoped Classical in
  let H := C.sharedSet.image (support C)
  have mem_shared (v : V) (hv : C.IsShared v) : v ∈ C.sharedSet := by
    obtain ⟨i, hi⟩ := C.cover v
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, mem_univ _, hi⟩, hv⟩
  have size (v : V) (hv : C.IsShared v) : 2 ≤ (support C v).card := by
    obtain ⟨i, j, hij, hi, hj⟩ := hv
    exact Finset.one_lt_card.mpr ⟨i, (mem_support C v i).mpr hi, j,
      (mem_support C v j).mpr hj, hij⟩
  obtain ⟨c, hc⟩ := hcol H (by
    intro A hA B hB hAB
    obtain ⟨u, _, rfl⟩ := mem_image.mp hA
    obtain ⟨v, _, rfl⟩ := mem_image.mp hB
    exact support_inter_le C (fun e => hAB (congrArg (support C) e))) (by
    intro A hA
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hA
    exact size v (mem_filter.mp hv).2)
  refine ⟨c ∘ support C, ?_⟩
  intro i u v hu hv hsu hsv he
  by_contra huv
  have hs : support C u ≠ support C v := by
    intro h
    have hle := support_inter_le C huv
    rw [← h, Finset.inter_self] at hle
    exact (Nat.not_succ_le_self 1) ((size u hsu).trans hle)
  exact hc _ (mem_image_of_mem _ (mem_shared u hsu))
    _ (mem_image_of_mem _ (mem_shared v hsv)) hs
    ⟨i, mem_inter.mpr ⟨(mem_support C u i).mpr hu, (mem_support C v i).mpr hv⟩⟩ he

theorem ProperOn.map {n : ℕ} {κ τ : Type*} {H : Finset (Finset (Fin n))}
    {c : Finset (Fin n) → κ} (hc : ProperOn H c) {f : κ → τ}
    (hf : Function.Injective f) : ProperOn H (f ∘ c) :=
  fun A hA B hB hAB hi he => hc A hA B hB hAB hi (hf he)

theorem ProperOn.piecewise {n : ℕ} {κ : Type*} {H K : Finset (Finset (Fin n))}
    {c d : Finset (Fin n) → κ} (hc : ProperOn H c) (hd : ProperOn K d)
    (hcross : ∀ A ∈ H, ∀ B ∈ K, (A ∩ B).Nonempty → c A ≠ d B) :
    ProperOn (H ∪ K) (fun A => if A ∈ H then c A else d A) := by
  intro A hA B hB hAB hi
  by_cases ha : A ∈ H <;> by_cases hb : B ∈ H
  · simpa only [if_pos ha, if_pos hb] using hc A ha B hb hAB hi
  · simpa only [if_pos ha, if_neg hb] using
      hcross A ha B ((mem_union.mp hB).resolve_left hb) hi
  · have hi' : (B ∩ A).Nonempty := by simpa only [Finset.inter_comm] using hi
    simpa only [if_neg ha, if_pos hb] using
      (hcross B hb A ((mem_union.mp hA).resolve_left ha) hi').symm
  · simpa only [if_neg ha, if_neg hb] using
      hd A ((mem_union.mp hA).resolve_left ha) B ((mem_union.mp hB).resolve_left hb) hAB hi

/-- The bounded-rank asymptotic list edge-coloring theorem for linear families. -/
theorem bounded_rank_list_color :
    ∀ r q : ℕ, 0 < q → ∃ D₀ : ℕ, ∀ n D m : ℕ, D₀ ≤ D → 0 < m →
      ∀ (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
        Linear H → (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r) →
        (∀ i, (incident H i).card ≤ D) → (∀ A ∈ H, D + D / q ≤ (L A).card) →
        ∃ c : Finset (Fin n) → Fin m, ProperOn H c ∧ ∀ A ∈ H, c A ∈ L A := by
  sorry

/-- Use one palette for the large and small supports and a second for the middle ranks. -/
theorem linear_color (q : ℕ) (hq : 0 < q) :
    ∀ᶠ n in atTop, ∀ H : Finset (Finset (Fin n)), Linear H →
      (∀ A ∈ H, 2 ≤ A.card) →
      ∃ c : Finset (Fin n) → Fin ((n + 2 * (n / q) + 1) + (n / q + 1)), ProperOn H c := by
  let lo := 2 * q
  let hi := lo * q
  have hlo : 0 < lo := by dsimp [lo]; omega
  have hlohi : lo ≤ hi := by
    dsimp [hi]
    exact Nat.le_mul_of_pos_right _ hq
  have hqhi : q ≤ hi := by
    dsimp [hi]
    exact Nat.le_mul_of_pos_left _ hlo
  have hhi : 0 < hi := hlo.trans_le hlohi
  obtain ⟨Ds, hs⟩ := bounded_rank_list_color lo q hq
  obtain ⟨Dm, hm⟩ := bounded_rank_list_color hi 1 Nat.one_pos
  filter_upwards [eventually_ge_atTop Ds, eventually_ge_atTop (Dm * lo)] with n hDs hDm H hH hmin
  let S := H.filter (fun A => A.card ≤ lo)
  let M := H.filter (fun A => lo < A.card ∧ A.card ≤ hi)
  let B := H.filter (fun A => hi < A.card)
  have hSH : S ⊆ H := filter_subset _ _
  have hMH : M ⊆ H := filter_subset _ _
  have hBH : B ⊆ H := filter_subset _ _
  let m₁ := n + 2 * (n / q) + 1
  let m₂ := n / q + 1
  obtain ⟨b, hb⟩ := large_rank_color B q m₁ hq (by dsimp [m₁]; omega) (hH.mono hBH)
    (fun A hA => Nat.succ_le_of_lt (hqhi.trans_lt (mem_filter.mp hA).2))
  have hBdeg (i : Fin n) : (incident B i).card ≤ n / hi := by
    rw [Nat.le_div_iff_mul_le hhi, Nat.mul_comm]
    exact incident_mul_le (hH.mono hBH) hi (fun A hA => (mem_filter.mp hA).2) i
  let blocked (A : Finset (Fin n)) := (meeting B A).image b
  have hblocked (A : Finset (Fin n)) (hA : A ∈ S) : (blocked A).card ≤ n / q := by
    calc
      (blocked A).card ≤ (meeting B A).card := Finset.card_image_le
      _ ≤ A.card * (n / hi) := meeting_card_le B A _ (fun i _ => hBdeg i)
      _ ≤ lo * (n / hi) := Nat.mul_le_mul_right _ (mem_filter.mp hA).2
      _ ≤ n / q := (Nat.le_div_iff_mul_le hq).mpr (by
        calc
          lo * (n / hi) * q = (n / hi) * hi := by dsimp [hi]; ac_rfl
          _ ≤ n := Nat.div_mul_le_self _ _)
  obtain ⟨s, hsp, hsl⟩ := hs n n m₁ hDs (by dsimp [m₁]; omega) S
    (fun A => univ \ blocked A) (hH.mono hSH)
    (fun A hA => ⟨hmin A (hSH hA), (mem_filter.mp hA).2⟩) (by
      intro i
      simpa using incident_mul_le (hH.mono hSH) 1 (fun A hA => hmin A (hSH hA)) i) (by
      intro A hA
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have := hblocked A hA
      dsimp [m₁]
      omega)
  obtain ⟨c, hc, _⟩ := hm n (n / lo) m₂ ((Nat.le_div_iff_mul_le hlo).mpr hDm)
    (Nat.succ_pos _) M (fun _ => univ) (hH.mono hMH)
    (fun A hA => ⟨hmin A (hMH hA), (mem_filter.mp hA).2.2⟩) (by
      intro i
      rw [Nat.le_div_iff_mul_le hlo, Nat.mul_comm]
      exact incident_mul_le (hH.mono hMH) lo (fun A hA => (mem_filter.mp hA).2.1) i) (by
      intro A _
      rw [Finset.card_univ, Fintype.card_fin, Nat.div_one, ← two_mul]
      have h : 2 * (n / lo) ≤ n / q := (Nat.le_div_iff_mul_le hq).mpr (by
        calc
          2 * (n / lo) * q = (n / lo) * lo := by dsimp [lo]; ac_rfl
          _ ≤ n := Nat.div_mul_le_self _ _)
      exact h.trans (Nat.le_succ _))
  let first (A : Finset (Fin n)) := if A ∈ S then s A else b A
  have hfirst : ProperOn (S ∪ B) first := hsp.piecewise hb (by
    intro A hA D hD hAD he
    have hmem : b D ∈ blocked A := mem_image_of_mem b (mem_filter.mpr ⟨hD, hAD⟩)
    exact (mem_sdiff.mp (hsl A hA)).2 (he.symm ▸ hmem))
  have hunion : (S ∪ B) ∪ M = H := by
    ext A
    simp only [S, B, M, mem_union, mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hA
      by_cases hsmall : A.card ≤ lo
      · exact Or.inl (Or.inl ⟨hA, hsmall⟩)
      by_cases hlarge : hi < A.card
      · exact Or.inl (Or.inr ⟨hA, hlarge⟩)
      exact Or.inr ⟨hA, Nat.lt_of_not_ge hsmall, Nat.le_of_not_gt hlarge⟩
  have hoff : Function.Injective (@Fin.natAdd m₂ m₁) := by
    intro a b he
    apply Fin.ext
    have he' := congrArg Fin.val he
    change m₁ + a.val = m₁ + b.val at he'
    omega
  have hproper := (hfirst.map (Fin.castAdd_injective m₁ m₂)).piecewise (hc.map hoff) (by
    intro A _ D _ _ he
    have he' := congrArg Fin.val he
    change (first A).val = m₁ + (c D).val at he'
    have hlt := (first A).isLt
    omega)
  rw [hunion] at hproper
  exact ⟨_, hproper⟩

theorem palette_le_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      (n + 2 * (n / q) + 1) + (n / q + 1) ≤ ⌊(1 + ε) * (n : ℝ)⌋₊ := by
  obtain ⟨q, hq⟩ := exists_nat_gt (6 / ε)
  have hεq : (6 : ℝ) < ε * q := by
    rw [mul_comm]
    exact (div_lt_iff₀ hε).mp hq
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hεq
      norm_num at hεq
    · exact h
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
  refine ⟨q, hqpos, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hεn : 4 ≤ ε * (n : ℝ) := by
    have h : (4 : ℝ) < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    have hle : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [mul_comm]
    exact h.le.trans (mul_le_mul_of_nonneg_right hle hε.le)
  have hd : (↑(n / q : ℕ) : ℝ) * q ≤ n := by
    exact_mod_cast Nat.div_mul_le_self n q
  have hbound : 6 * (↑(n / q : ℕ) : ℝ) ≤ ε * n := by
    calc
      _ ≤ (ε * q) * (↑(n / q : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hεq.le (by positivity)
      _ = ε * ((↑(n / q : ℕ) : ℝ) * q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hε.le
  apply Nat.le_floor
  push_cast
  nlinarith

/-- Kahn 1992: the shared vertices (= edges of the dual linear hypergraph on n vertices)
can be properly coloured with floor((1+eps)n) colours for n large. -/
theorem kahn_shared : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ (V : Type) (C : EFLConfig V n),
    ∃ c : V → Fin ⌊(1 + ε) * n⌋₊, ∀ i u v, u ∈ C.A i → v ∈ C.A i → C.IsShared u →
      C.IsShared v → c u = c v → u = v := by
  intro ε hε
  obtain ⟨q, hq, hfloor⟩ := palette_le_floor ε hε
  filter_upwards [linear_color q hq, hfloor] with n hn hf V C
  apply shared_of_linear_color C
  intro H hH hm
  obtain ⟨c, hc⟩ := hn H hH hm
  exact ⟨_, hc.map (Fin.castLE_injective hf)⟩

end OMA19

theorem OMA.solution : type_of% @Erdos19.erdos_19.variants.kahn := by
  intro ε hε
  filter_upwards [OMA19.kahn_shared ε hε] with n hn V C
  obtain ⟨c, hc⟩ := hn V C
  exact OMA19.colorable_of_sharedColoring_le C _ (OMA19.le_floor_mul ε hε n) c hc
