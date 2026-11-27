import OMAReductions.R_Erdos107_variants_su_bound_R1
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds

-- Step Erdos107.variants.su_bound.R1.H1: hypothesis H1 of reduction Erdos107.variants.su_bound.R1
-- Credit: @<handle>
-- H1 := ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop, Even n →     ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧       ∀ X : Finset (ℝ × ℝ), X.card = N →         Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) →         (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 →           (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →         ∃ Y ⊆ X, Y.card = n ∧           ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2  /-- Suk's planar theorem for odd n. -/

open Finset
open scoped Classical

namespace Erdos107Suk

/-- Counting incidences gives a lower density of good k-subsets from a
hitting property on all m-subsets. -/
private theorem dense_subsets {α : Type*} (S : Finset α) {k m : ℕ}
    (hkm : k ≤ m) (hmS : m ≤ S.card) (good : Finset α → Prop) [DecidablePred good]
    (hit : ∀ U ⊆ S, U.card = m → ∃ T ⊆ U, T.card = k ∧ good T) :
    S.card.choose k ≤ ((S.powersetCard k).filter good).card * m.choose k := by
  classical
  let G := (S.powersetCard k).filter good
  have hcount :
      (S.powersetCard m).card * 1 ≤ G.card * (S.card - k).choose (m - k) := by
    apply Finset.card_mul_le_card_mul (fun U T : Finset α => T ⊆ U)
    · intro U hU
      obtain ⟨hUS, hUm⟩ := mem_powersetCard.mp hU
      obtain ⟨T, hTU, hTk, hg⟩ := hit U hUS hUm
      exact card_pos.mpr ⟨T, by
        exact mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_powersetCard.mpr ⟨hTU.trans hUS, hTk⟩, hg⟩, hTU⟩⟩
    · intro T hT
      obtain ⟨hTS, hTk⟩ := mem_powersetCard.mp (mem_filter.mp hT).1
      change ((S.powersetCard m).filter (T ⊆ ·)).card ≤ _
      rw [card_filter_powersetCard_subset T S m hTS (hTk ▸ hkm), hTk]
  rw [card_powersetCard, mul_one] at hcount
  have hp : 0 < (S.card - k).choose (m - k) := Nat.choose_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hp
  calc
    S.card.choose k * (S.card - k).choose (m - k) =
        S.card.choose m * m.choose k := (Nat.choose_mul hkm).symm
    _ ≤ (G.card * (S.card - k).choose (m - k)) * m.choose k :=
      Nat.mul_le_mul_right _ hcount
    _ = (G.card * m.choose k) * (S.card - k).choose (m - k) := by ac_rfl

/-- Longest chains below a point stratify a finite strict partial order into
antichains. -/
private theorem chain_or_antichain {α : Type*} (S : Finset α) (R : α → α → Prop)
    (hir : ∀ x, ¬ R x x) (ht : ∀ {x y z}, R x y → R y z → R x z)
    {a b : ℕ} (ha : 0 < a) (hsize : a * b < S.card) :
    (∃ C ⊆ S, a ≤ C.card ∧ IsChain R (C : Set α)) ∨
      ∃ A ⊆ S, b < A.card ∧ IsAntichain R (A : Set α) := by
  classical
  by_cases hc : ∃ C ⊆ S, a ≤ C.card ∧ IsChain R (C : Set α)
  · exact Or.inl hc
  right
  let below (p : α) := S.powerset.filter fun (C : Finset α) =>
    IsChain R (C : Set α) ∧ ∀ q ∈ C, R q p
  let rank (p : α) := (below p).sup Finset.card
  have extend {C : Finset α} {p : α} (hC : C ∈ below p) (hp : p ∈ S) :
      insert p C ⊆ S ∧ IsChain R ((insert p C : Finset α) : Set α) ∧
        (insert p C).card = C.card + 1 := by
    obtain ⟨hCS, hchain, hrel⟩ := mem_filter.mp hC
    have hpn : p ∉ C := fun h => hir p (hrel p h)
    refine ⟨insert_subset hp (mem_powerset.mp hCS), ?_, card_insert_of_notMem hpn⟩
    rw [coe_insert]
    exact hchain.insert (fun q hq _ => Or.inr (hrel q hq))
  have hlt p (hp : p ∈ S) : rank p < a := by
    change (below p).sup Finset.card < a
    apply (Finset.sup_lt_iff ha).mpr
    intro C hC
    obtain ⟨hsub, hchain, hcard⟩ := extend hC hp
    have hbound : ¬ a ≤ (insert p C).card := fun hle =>
      hc ⟨insert p C, hsub, hle, hchain⟩
    omega
  have hrank {p q} (hp : p ∈ S) (hpq : R p q) : rank p < rank q := by
    have hne : (below p).Nonempty := ⟨∅, by simp [below]⟩
    obtain ⟨C, hC, he⟩ := Finset.exists_mem_eq_sup (below p) hne Finset.card
    obtain ⟨hsub, hchain, hcard⟩ := extend hC hp
    have hm : insert p C ∈ below q := by
      refine mem_filter.mpr ⟨mem_powerset.mpr hsub, hchain, ?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hpq
      · exact ht ((mem_filter.mp hC).2.2 x hx) hpq
    have hbnd : (insert p C).card ≤ rank q := Finset.le_sup hm
    change rank p = C.card at he
    omega
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := Finset.range a) (f := rank)
    (fun p hp => mem_range.mpr (hlt p hp)) (by simpa using hsize)
  refine ⟨S.filter (fun p => rank p = j), filter_subset _ _, hj, ?_⟩
  intro p hp q hq _ hpq
  obtain ⟨hpS, hpj⟩ := mem_filter.mp hp
  obtain ⟨_, hqj⟩ := mem_filter.mp hq
  exact (hrank hpS hpq).ne (hpj.trans hqj.symm)

/-- If good configurations outnumber the capacity of all anchor choices
with a small region, some anchor has large completion regions throughout. -/
private theorem large_completion_regions {α β γ : Type*}
    {k L : ℕ} (S : Finset α) (G : Finset β) (A : Finset γ)
    (anchor : β → γ) (completion : β → Fin k → α) (R : γ → Fin k → Finset α)
    (hA : ∀ g ∈ G, anchor g ∈ A)
    (hR : ∀ a ∈ A, ∀ i, R a i ⊆ S)
    (hmem : ∀ g ∈ G, ∀ i, completion g i ∈ R (anchor g) i)
    (hinj : ∀ g ∈ G, ∀ g' ∈ G, anchor g = anchor g' →
      completion g = completion g' → g = g')
    (hsize : A.card * (L * S.card ^ (k - 1)) < G.card) :
    ∃ a ∈ A, ∀ i, L < (R a i).card := by
  classical
  obtain ⟨a, haA, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hA hsize
  refine ⟨a, haA, fun i => lt_of_not_ge fun hi => ?_⟩
  let F := G.filter fun g => anchor g = a
  have hm : F.card ≤ (Fintype.piFinset (R a)).card := by
    apply Finset.card_le_card_of_injOn completion
    · intro g hg
      obtain ⟨hgG, hga⟩ := mem_filter.mp hg
      exact Fintype.mem_piFinset.mpr fun j => hga ▸ hmem g hgG j
    · intro g hg g' hg' he
      obtain ⟨hgG, hga⟩ := mem_filter.mp hg
      obtain ⟨hg'G, hg'a⟩ := mem_filter.mp hg'
      exact hinj g hgG g' hg'G (hga.trans hg'a.symm) he
  have hp : (Fintype.piFinset (R a)).card ≤ L * S.card ^ (k - 1) := by
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (mem_univ i)]
    refine Nat.mul_le_mul hi ?_
    calc
      ∏ j ∈ univ.erase i, (R a j).card ≤ ∏ _j ∈ univ.erase i, S.card :=
        Finset.prod_le_prod' fun j _ => card_le_card (hR a haA j)
      _ = S.card ^ (k - 1) := by simp [Finset.prod_const, Finset.card_erase_of_mem]
  exact (not_lt_of_ge (hm.trans hp)) ha

private abbrev Point := ℝ × ℝ

private def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

private noncomputable def chart (p : Point) : Point := (p.1 / p.2, (p.1 - 1) / p.2)

private theorem orient_chart {a b c : Point}
    (ha : a.2 ≠ 0) (hb : b.2 ≠ 0) (hc : c.2 ≠ 0) :
    (a.2 * b.2 * c.2) * orient (chart a) (chart b) (chart c) = orient a b c := by
  dsimp [orient, chart]
  field_simp
  ring

private theorem orient_left_anchor {p q : Point} (hp : 0 < p.2) (hq : 0 < q.2) :
    orient (0, 0) p q < 0 ↔ (chart p).1 < (chart q).1 := by
  rw [show (chart p).1 = p.1 / p.2 from rfl, show (chart q).1 = q.1 / q.2 from rfl,
    div_lt_div_iff₀ hp hq]
  dsimp [orient]
  constructor <;> intro h <;> linarith only [h]

private theorem orient_right_anchor {p q : Point} (hp : 0 < p.2) (hq : 0 < q.2) :
    orient (1, 0) p q < 0 ↔ (chart p).2 < (chart q).2 := by
  rw [show (chart p).2 = (p.1 - 1) / p.2 from rfl,
    show (chart q).2 = (q.1 - 1) / q.2 from rfl, div_lt_div_iff₀ hp hq]
  dsimp [orient]
  constructor <;> intro h <;> linarith only [h]

/-- The second point is a strictly positive barycentric combination of
the first point and the base points (0,0) and (1,0). -/
private def Nested (q p : Point) : Prop :=
  ∃ b w : ℝ, 0 < b ∧ 0 < w ∧ b + w < 1 ∧
    p.1 = b + w * q.1 ∧ p.2 = w * q.2

private theorem nested_iff {q p : Point} (hq : 0 < q.2) (hp : 0 < p.2) :
    Nested q p ↔ (chart q).1 < (chart p).1 ∧ (chart p).2 < (chart q).2 := by
  unfold Nested chart
  dsimp only
  rw [div_lt_div_iff₀ hq hp, div_lt_div_iff₀ hp hq]
  constructor
  · rintro ⟨b, w, hb, hw, hbw, h₁, h₂⟩
    rw [h₁, h₂]
    constructor
    · nlinarith only [mul_pos hb hq]
    · have hgap : 0 < (1 - (b + w)) * q.2 := mul_pos (sub_pos.mpr hbw) hq
      nlinarith only [hgap]
  · rintro ⟨h₁, h₂⟩
    let w : ℝ := p.2 / q.2
    let b : ℝ := p.1 - w * q.1
    have hwq : w * q.2 = p.2 := div_mul_cancel₀ _ hq.ne'
    refine ⟨b, w, ?_, div_pos hp hq, ?_, by dsimp [b]; ring, hwq.symm⟩
    · apply (mul_pos_iff_of_pos_right hq).mp
      have heq : b * q.2 = p.1 * q.2 - q.1 * p.2 := by
        dsimp [b]
        linear_combination -q.1 * hwq
      rw [heq]
      exact sub_pos.mpr h₁
    · apply (lt_of_mul_lt_mul_right · hq.le)
      have heq : (b + w) * q.2 = p.1 * q.2 - (q.1 - 1) * p.2 := by
        dsimp [b]
        linear_combination (1 - q.1) * hwq
      rw [heq]
      nlinarith only [h₂]

private theorem nested_trans {a b c : Point} (ha : 0 < a.2) (hb : 0 < b.2)
    (hc : 0 < c.2) (hab : Nested a b) (hbc : Nested b c) : Nested a c := by
  obtain ⟨hl, hr⟩ := (nested_iff ha hb).mp hab
  obtain ⟨hl', hr'⟩ := (nested_iff hb hc).mp hbc
  exact (nested_iff ha hc).mpr ⟨hl.trans hl', hr'.trans hr⟩

private theorem anchors_of_antichain {A : Finset Point}
    (hA : IsAntichain Nested (A : Set Point))
    (hpos : ∀ p ∈ A, 0 < p.2)
    (hinj : Set.InjOn (fun p => (chart p).2) (A : Set Point))
    {p q : Point} (hp : p ∈ A) (hq : q ∈ A) (h : (chart p).1 < (chart q).1) :
    orient (0, 0) p q < 0 ∧ orient (1, 0) p q < 0 := by
  have hne : p ≠ q := fun he => h.ne (congrArg (fun x => (chart x).1) he)
  have hR : (chart p).2 < (chart q).2 := by
    rcases lt_or_gt_of_ne (fun he => hne (hinj hp hq he)) with hlt | hgt
    · exact hlt
    · exact (hA hp hq hne ((nested_iff (hpos p hp) (hpos q hq)).mpr ⟨h, hgt⟩)).elim
  exact ⟨(orient_left_anchor (hpos p hp) (hpos q hq)).mpr h,
    (orient_right_anchor (hpos p hp) (hpos q hq)).mpr hR⟩

private def turn (up : Bool) (a b c : Point) : Prop :=
  if up then 0 < orient a b c else orient a b c < 0

private def turns (up : Bool) : List Point → Prop
  | a :: b :: c :: l => turn up a b c ∧ turns up (b :: c :: l)
  | _ => True

private def IsSeq (up : Bool) (X : Finset Point) (l : List Point) : Prop :=
  (∀ p ∈ l, p ∈ X) ∧ l.Pairwise (fun p q => p.1 < q.1) ∧ turns up l

private def HasSeq (up : Bool) (X : Finset Point) (k : ℕ) : Prop :=
  ∃ l, IsSeq up X l ∧ l.length = k

private theorem isSeq_mono {up : Bool} {X Y : Finset Point} {l : List Point}
    (hl : IsSeq up X l) (hXY : X ⊆ Y) : IsSeq up Y l :=
  ⟨fun p hp => hXY (hl.1 p hp), hl.2⟩

private theorem turns_append {up : Bool} {a b c : Point} (l : List Point)
    (hl : turns up (l ++ [a, b])) (hc : turn up a b c) :
    turns up (l ++ [a, b, c]) := by
  induction l with
  | nil => simpa [turns] using hc
  | cons x l ih =>
    cases l with
    | nil =>
      have h := (show turn up x a b ∧ turns up [a, b] from hl).1
      exact ⟨h, ih (by trivial)⟩
    | cons y l =>
      cases l with
      | nil =>
        exact ⟨(show turn up x y a ∧ turns up [y, a, b] from hl).1,
          ih (show turns up [y, a, b] from hl.2)⟩
      | cons z l =>
        exact ⟨(show turn up x y z ∧ turns up ((y :: z :: l) ++ [a, b]) from hl).1,
          ih (show turns up ((y :: z :: l) ++ [a, b]) from hl.2)⟩

private theorem isSeq_append {up : Bool} {X : Finset Point} {a b c : Point} {l : List Point}
    (hl : IsSeq up X (l ++ [a, b])) (hc : c ∈ X) (hbc : b.1 < c.1) (ht : turn up a b c) :
    IsSeq up X (l ++ [a, b, c]) := by
  rw [show l ++ [a, b, c] = (l ++ [a, b]) ++ [c] by simp]
  refine ⟨?_, List.pairwise_append.2 ⟨hl.2.1, by simp, ?_⟩, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hl.1 p hp
    · simpa using (List.mem_singleton.1 hp ▸ hc)
  · intro p hp q hq
    have hqc := List.mem_singleton.1 hq
    subst q
    rw [show l ++ [a, b] = (l ++ [a]) ++ [b] by simp] at hp
    rcases List.mem_append.1 hp with hp | hp
    · have hsort := hl.2.1
      rw [show l ++ [a,b] = (l ++ [a]) ++ [b] by simp] at hsort
      exact ((List.pairwise_append.1 hsort).2.2 _ hp _ (by simp)).trans hbc
    · simpa [List.mem_singleton.1 hp] using hbc
  · simpa using turns_append l hl.2.2 ht

private theorem exists_suffix_two {l : List Point} (h : 2 ≤ l.length) :
    ∃ pre a b, l = pre ++ [a, b] := by
  have hrevlen : 2 ≤ l.reverse.length := by simpa using h
  cases hr : l.reverse with
  | nil => simp [hr] at hrevlen
  | cons b r =>
    cases r with
    | nil => simp [hr] at hrevlen
    | cons a pre =>
      exact ⟨pre.reverse, a, b, by
        simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hr⟩

private def IsEnd (s : ℕ) (X : Finset Point) (p : Point) : Prop :=
  ∃ pre a, IsSeq true X (pre ++ [a, p]) ∧ pre.length = s

private theorem no_shorter_cup_outside (s : ℕ) (X : Finset Point) :
    ¬ HasSeq true {p ∈ X | ¬ IsEnd s X p} (s + 2) := by
  rintro ⟨l, hl, hlen⟩
  obtain ⟨pre, a, p, rfl⟩ := exists_suffix_two (by omega : 2 ≤ l.length)
  have hp := Finset.mem_filter.1 (hl.1 p (by simp))
  have hpre : pre.length = s := by simpa using hlen
  exact hp.2 ⟨pre, a, isSeq_mono hl (Finset.filter_subset _ _), hpre⟩

private theorem no_shorter_cap_in_ends (s t : ℕ) (X : Finset Point)
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ HasSeq true X (s + 3)) (hd : ¬ HasSeq false X (t + 3)) :
    ¬ HasSeq false {p ∈ X | IsEnd s X p} (t + 2) := by
  rintro ⟨l, hl, hlen⟩
  cases l with
  | nil => simp at hlen
  | cons p l =>
    cases l with
    | nil => simp at hlen
    | cons q tail =>
      obtain ⟨hp, pre, a, hcup, hpre⟩ := Finset.mem_filter.1 (hl.1 p (by simp))
      have hq := (Finset.mem_filter.1 (hl.1 q (by simp))).1
      have ha := hcup.1 a (by simp)
      have hap : a.1 < p.1 :=
        (List.pairwise_cons.1 (List.pairwise_append.1 hcup.2.1).2.1).1 p (by simp)
      have hpq : p.1 < q.1 := (List.pairwise_cons.1 hl.2.1).1 q (by simp)
      by_cases hturn : 0 < orient a p q
      · apply hc
        exact ⟨pre ++ [a, p, q],
          isSeq_append hcup hq hpq (by simpa [turn] using hturn), by simp [hpre]⟩
      · apply hd
        have hneg : orient a p q < 0 :=
          lt_of_le_of_ne (le_of_not_gt hturn) (hgen a ha p hp q hq hap hpq)
        have hlX := isSeq_mono hl (Finset.filter_subset _ _)
        refine ⟨a :: p :: q :: tail,
          ⟨?_, List.pairwise_cons.2 ⟨?_, hlX.2.1⟩, ?_⟩, ?_⟩
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact ha
          · exact hlX.1 b hb
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact hap
          · exact hap.trans ((List.pairwise_cons.1 hlX.2.1).1 _ hb)
        · change turn false a p q ∧ turns false (p :: q :: tail)
          exact ⟨by simpa [turn] using hneg, hlX.2.2⟩
        · simp only [List.length_cons] at hlen ⊢
          omega

private theorem hasSeq_two {X : Finset Point}
    (hx : Set.InjOn Prod.fst (X : Set Point)) (hX : 1 < X.card) (up : Bool) :
    HasSeq up X 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hX
  have hne : a.1 ≠ b.1 := fun he => hab (hx ha hb he)
  have hseq {a b : Point} (ha : a ∈ X) (hb : b ∈ X) (hab : a.1 < b.1) :
      HasSeq up X 2 := by
    refine ⟨[a, b], ⟨?_, ?_, trivial⟩, rfl⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ha
      · exact hb
    · simp [hab]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hseq ha hb h
  · exact hseq hb ha h

private theorem card_le_binomial (s t : ℕ) (X : Finset Point)
    (hx : Set.InjOn Prod.fst (X : Set Point))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ HasSeq true X (s + 2)) (hd : ¬ HasSeq false X (t + 2)) :
    X.card ≤ (s + t).choose s := by
  induction s generalizing t X with
  | zero =>
    simpa using (le_of_not_gt fun h => hc (hasSeq_two hx h true))
  | succ s ih =>
    induction t generalizing X with
    | zero =>
      simpa using (le_of_not_gt fun h => hd (hasSeq_two hx h false))
    | succ t jt =>
      let T := X.filter (IsEnd s X)
      let U := X.filter (fun p => ¬ IsEnd s X p)
      have hTX : T ⊆ X := Finset.filter_subset _ _
      have hUX : U ⊆ X := Finset.filter_subset _ _
      have hT : T.card ≤ (s + 1 + t).choose (s + 1) := by
        apply jt T (hx.mono hTX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hTX ha) b (hTX hb) c (hTX hc) hab hbc
        · rintro ⟨l, hl, hlen⟩
          exact hc ⟨l, isSeq_mono hl hTX, hlen⟩
        · exact no_shorter_cap_in_ends s t X hgen hc hd
      have hU : U.card ≤ (s + (t + 1)).choose s := by
        apply ih (t + 1) U (hx.mono hUX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hUX ha) b (hUX hb) c (hUX hc) hab hbc
        · exact no_shorter_cup_outside s X
        · rintro ⟨l, hl, hlen⟩
          exact hd ⟨l, isSeq_mono hl hUX, hlen⟩
      have hpart : T.card + U.card = X.card :=
        Finset.card_filter_add_card_filter_not (IsEnd s X)
      have hchoose :
          ((s + 1) + (t + 1)).choose (s + 1) =
            (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        rw [show (s + 1) + (t + 1) = (s + (t + 1)) + 1 by omega,
          Nat.choose_succ_succ', show s + (t + 1) = s + 1 + t by omega]
      rw [hchoose, ← hpart]
      exact (Nat.add_le_add hT hU).trans_eq (Nat.add_comm _ _)

private def signedOrient (up : Bool) (a b c : Point) : ℝ :=
  (if up then 1 else -1) * orient a b c

private theorem turn_iff_signed (up : Bool) (a b c : Point) :
    turn up a b c ↔ 0 < signedOrient up a b c := by
  cases up <;> simp [turn, signedOrient]

private theorem turn_quad {up : Bool} {a b c d : Point}
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (h₁ : turn up a b c) (h₂ : turn up b c d) :
    turn up a b d ∧ turn up a c d := by
  rw [turn_iff_signed] at h₁ h₂
  simp only [turn_iff_signed]
  have hleft :
      (c.1 - b.1) * signedOrient up a b d =
        (d.1 - b.1) * signedOrient up a b c + (b.1 - a.1) * signedOrient up b c d := by
    unfold signedOrient orient
    ring
  have hright :
      (c.1 - b.1) * signedOrient up a c d =
        (c.1 - a.1) * signedOrient up b c d + (d.1 - c.1) * signedOrient up a b c := by
    unfold signedOrient orient
    ring
  constructor
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hleft]
    exact add_pos (mul_pos (sub_pos.mpr (hbc.trans hcd)) h₁) (mul_pos (sub_pos.mpr hab) h₂)
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hright]
    exact add_pos (mul_pos (sub_pos.mpr (hab.trans hbc)) h₂) (mul_pos (sub_pos.mpr hcd) h₁)

private theorem turns_tail {up : Bool} {a : Point} {l : List Point}
    (h : turns up (a :: l)) : turns up l := by
  rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
  · trivial
  · trivial
  · exact h.2

private theorem x_lt_next {a b : Point} {l : List Point}
    (h : (a :: b :: l).Pairwise (fun p q => p.1 < q.1)) : a.1 < b.1 :=
  (List.pairwise_cons.1 h).1 b (by simp)

private theorem turns_delete {up : Bool} {p : Point} {l : List Point} (pre : List Point)
    (hs : (pre ++ p :: l).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ p :: l)) : turns up (pre ++ l) := by
  induction pre with
  | nil => exact turns_tail ht
  | cons a pre ih =>
    cases pre with
    | nil =>
      rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
      · trivial
      · trivial
      · have hs' : (a :: p :: b :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
        have ht' : turns up (a :: p :: b :: c :: l) := ht
        have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
          (x_lt_next hs'.tail.tail) ht'.1 ht'.2.1
        exact ⟨hp.2, ht'.2.2⟩
    | cons b pre =>
      cases pre with
      | nil =>
        cases l with
        | nil => trivial
        | cons c l =>
          have hs' : (a :: b :: p :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
          have ht' : turns up (a :: b :: p :: c :: l) := ht
          have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
            (x_lt_next hs'.tail.tail) ht'.1 ht'.2.1
          exact ⟨hp.1, ih hs'.tail ht'.2⟩
      | cons c pre =>
        have ht' : turns up (a :: b :: c :: (pre ++ p :: l)) := ht
        exact ⟨ht'.1, ih hs.tail ht'.2⟩

private theorem turns_sublist_append {up : Bool} {l₁ l₂ : List Point} (h : List.Sublist l₁ l₂)
    (pre : List Point) (hs : (pre ++ l₂).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ l₂)) : turns up (pre ++ l₁) := by
  induction h generalizing pre with
  | slnil => exact ht
  | cons a h ih =>
    apply ih pre
    · apply List.Pairwise.sublist _ hs
      exact (List.Sublist.refl _).append (List.Sublist.cons _ (List.Sublist.refl _))
    · exact turns_delete pre hs ht
  | cons_cons a h ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [a]) (by simpa only [List.append_assoc, List.singleton_append] using hs)
        (by simpa only [List.append_assoc, List.singleton_append] using ht)

private theorem turn_of_mem {up : Bool} {X : Finset Point} {l : List Point}
    (h : IsSeq up X l) {a b c : Point} (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) : turn up a b c := by
  let r : Point → Point → Prop := fun a b => a.1 < b.1
  let : Std.Antisymm r := ⟨fun _ _ h₁ h₂ => (lt_asymm h₁ h₂).elim⟩
  let : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
  have htri : [a, b, c].Pairwise r := by simp [r, hab, hbc, hab.trans hbc]
  have hsub : [a, b, c] ⊆ l := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hsublist : List.Sublist [a, b, c] l :=
    List.sublist_of_subperm_of_pairwise (List.subperm_of_subset htri.nodup hsub) htri h.2.1
  have hh := turns_sublist_append hsublist [] h.2.1 h.2.2
  exact hh.1

private theorem chart_injOn {A : Finset Point} (hpos : ∀ p ∈ A, 0 < p.2) :
    Set.InjOn chart (A : Set Point) := by
  intro p hp q hq he
  have hu := congrArg Prod.fst he
  have hv := congrArg Prod.snd he
  change p.1 / p.2 = q.1 / q.2 at hu
  change (p.1 - 1) / p.2 = (q.1 - 1) / q.2 at hv
  have hy : p.2 = q.2 := by
    have hu' := (div_eq_div_iff (hpos p hp).ne' (hpos q hq).ne').mp hu
    have hv' := (div_eq_div_iff (hpos p hp).ne' (hpos q hq).ne').mp hv
    linarith only [hu', hv']
  exact Prod.ext (by simpa only [hy, div_left_inj' (hpos q hq).ne'] using hu) hy

private def TurnsInChart (up : Bool) (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, (chart p).1 < (chart q).1 → (chart q).1 < (chart r).1 →
    turn up p q r

private theorem cup_or_cap_in_chart {A : Finset Point} {s t : ℕ}
    (hpos : ∀ p ∈ A, 0 < p.2)
    (hinj : Set.InjOn (fun p => (chart p).1) (A : Set Point))
    (hgen : ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A,
      (chart p).1 < (chart q).1 → (chart q).1 < (chart r).1 → orient p q r ≠ 0)
    (hsize : (s + t).choose s < A.card) :
    (∃ Y ⊆ A, Y.card = s + 2 ∧ TurnsInChart true Y) ∨
      ∃ Y ⊆ A, Y.card = t + 2 ∧ TurnsInChart false Y := by
  classical
  let X := A.image chart
  have hX : X.card = A.card := card_image_of_injOn (chart_injOn hpos)
  have hinjX : Set.InjOn Prod.fst (X : Set Point) := by
    intro p hp q hq he
    obtain ⟨p', hp', rfl⟩ := mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := mem_image.mp hq
    exact congrArg chart (hinj hp' hq' he)
  have hgenX : ∀ p ∈ X, ∀ q ∈ X, ∀ r ∈ X,
      p.1 < q.1 → q.1 < r.1 → orient p q r ≠ 0 := by
    intro p hp q hq r hr hpq hqr he
    obtain ⟨p', hp', rfl⟩ := mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := mem_image.mp hq
    obtain ⟨r', hr', rfl⟩ := mem_image.mp hr
    have he' := orient_chart (hpos p' hp').ne' (hpos q' hq').ne' (hpos r' hr').ne'
    rw [he, mul_zero] at he'
    exact hgen p' hp' q' hq' r' hr' hpq hqr he'.symm
  have pull {up : Bool} {m : ℕ} (h : HasSeq up X m) :
      ∃ Y ⊆ A, Y.card = m ∧ TurnsInChart up Y := by
    obtain ⟨l, hl, hlen⟩ := h
    let Y := A.filter fun p => chart p ∈ l.toFinset
    have hYA : Y ⊆ A := filter_subset _ _
    have hYl : Y.image chart = l.toFinset := by
      ext u
      constructor
      · intro hu
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hu
        exact (mem_filter.mp hp).2
      · intro hu
        obtain ⟨p, hp, rfl⟩ := mem_image.mp (hl.1 u (List.mem_toFinset.mp hu))
        exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hu⟩, rfl⟩
    have hnodup : l.Nodup :=
      hl.2.1.imp fun hpq he => hpq.ne (congrArg Prod.fst he)
    have hcard : Y.card = m := by
      rw [← card_image_of_injOn ((chart_injOn hpos).mono hYA), hYl,
        List.toFinset_card_of_nodup hnodup, hlen]
    refine ⟨Y, hYA, hcard, ?_⟩
    intro p hp q hq r hr hpq hqr
    have member {u : Point} (hu : u ∈ Y) : chart u ∈ l :=
      List.mem_toFinset.mp (mem_filter.mp hu).2
    have hturn := turn_of_mem hl (member hp) (member hq) (member hr) hpq hqr
    have hp' := hpos p (hYA hp)
    have hq' := hpos q (hYA hq)
    have hr' := hpos r (hYA hr)
    have hprod : 0 < p.2 * q.2 * r.2 := by positivity
    unfold turn
    rw [← orient_chart hp'.ne' hq'.ne' hr'.ne']
    cases up with
    | false => exact mul_neg_of_pos_of_neg hprod hturn
    | true => exact mul_pos hprod hturn
  by_cases hu : HasSeq true X (s + 2)
  · exact Or.inl (pull hu)
  by_cases hd : HasSeq false X (t + 2)
  · exact Or.inr (pull hd)
  exact (hsize.not_ge (hX ▸ card_le_binomial s t X hinjX hgenX hu hd)).elim

private theorem cup_or_anchored_cap {A : Finset Point} {s t : ℕ}
    (hA : IsAntichain Nested (A : Set Point))
    (hpos : ∀ p ∈ A, 0 < p.2)
    (hleft : Set.InjOn (fun p => (chart p).1) (A : Set Point))
    (hright : Set.InjOn (fun p => (chart p).2) (A : Set Point))
    (hgen : ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A,
      (chart p).1 < (chart q).1 → (chart q).1 < (chart r).1 → orient p q r ≠ 0)
    (hsize : (s + t).choose s < A.card) :
    (∃ Y ⊆ A, Y.card = s + 2 ∧ TurnsInChart true Y) ∨
      ∃ Y ⊆ A, Y.card = t + 2 ∧ TurnsInChart false Y ∧
        ∀ p ∈ Y, ∀ q ∈ Y, (chart p).1 < (chart q).1 →
          orient (0, 0) p q < 0 ∧ orient (1, 0) p q < 0 := by
  rcases cup_or_cap_in_chart hpos hleft hgen hsize with hc | ⟨Y, hYA, hcard, ht⟩
  · exact Or.inl hc
  · exact Or.inr ⟨Y, hYA, hcard, ht, fun p hp q hq hpq =>
      anchors_of_antichain hA hpos hright (hYA hp) (hYA hq) hpq⟩

private def OrderedTurns (up : Bool) {d : ℕ} (e : Fin d → Point) : Prop :=
  StrictMono (fun i => (e i).1) ∧
    ∀ i j k, i < j → j < k → turn up (e i) (e j) (e k)

private theorem ordered_turns_of_hasSeq {S : Finset Point} {d : ℕ} {up : Bool}
    (h : HasSeq up S d) :
    ∃ e : Fin d → Point, (∀ i, e i ∈ S) ∧ OrderedTurns up e := by
  obtain ⟨l, hl, rfl⟩ := h
  let e : Fin l.length → Point := l.get
  have hmono : StrictMono (fun i => (e i).1) := by
    intro i j hij
    exact (List.pairwise_iff_get.mp hl.2.1) i j hij
  exact ⟨e, fun i => hl.1 _ (List.get_mem _ _), hmono,
    fun i j k hij hjk => turn_of_mem hl (List.get_mem _ _) (List.get_mem _ _)
      (List.get_mem _ _) (hmono hij) (hmono hjk)⟩

private def GoodTurns (d : ℕ) (T : Finset Point) : Prop :=
  ∃ (up : Bool) (e : Fin d → Point), (∀ i, e i ∈ T) ∧ OrderedTurns up e

private def evenIndex {k : ℕ} (i : Fin (k + 1)) : Fin (2 * k + 1) :=
  ⟨2 * i.val, by omega⟩

private def oddIndex {k : ℕ} (i : Fin k) : Fin (2 * k + 1) :=
  ⟨2 * i.val + 1, by omega⟩

private def InGap {k : ℕ} (up : Bool) (a : Fin (k + 1) → Point)
    (i : Fin k) (p : Point) : Prop :=
  (a ⟨i, by omega⟩).1 < p.1 ∧ p.1 < (a ⟨i.val + 1, by omega⟩).1 ∧
    ∀ j l : Fin (k + 1), j < l →
      if l.val ≤ i.val then turn up (a j) (a l) p
      else if i.val < j.val then turn up p (a j) (a l)
      else turn up (a j) p (a l)

private theorem inGap_of_orderedTurns {k : ℕ} {up : Bool}
    {e : Fin (2 * k + 1) → Point} (he : OrderedTurns up e) (i : Fin k) :
    InGap up (e ∘ evenIndex) i (e (oddIndex i)) := by
  refine ⟨he.1 (by change 2 * i.val < 2 * i.val + 1; omega),
    he.1 (by change 2 * i.val + 1 < 2 * (i.val + 1); omega), ?_⟩
  intro j l hjl
  have hjl' : evenIndex j < evenIndex l := by
    change 2 * j.val < 2 * l.val
    exact Nat.mul_lt_mul_of_pos_left hjl (by decide)
  by_cases hl : l.val ≤ i.val
  · simp only [if_pos hl, Function.comp_apply]
    exact he.2 _ _ _ hjl' (by change 2 * l.val < 2 * i.val + 1; omega)
  · by_cases hj : i.val < j.val
    · simp only [if_neg hl, if_pos hj, Function.comp_apply]
      exact he.2 _ _ _ (by change 2 * i.val + 1 < 2 * j.val; omega) hjl'
    · simp only [if_neg hl, if_neg hj, Function.comp_apply]
      exact he.2 _ _ _ (by change 2 * j.val < 2 * i.val + 1; omega)
        (by change 2 * i.val + 1 < 2 * l.val; omega)

private theorem even_odd_determine {α : Type*} {k : ℕ} {e f : Fin (2 * k + 1) → α}
    (he : e ∘ evenIndex = f ∘ evenIndex) (ho : e ∘ oddIndex = f ∘ oddIndex) : e = f := by
  funext i
  by_cases h : i.val % 2 = 0
  · let j : Fin (k + 1) := ⟨i.val / 2, by omega⟩
    have hj : evenIndex j = i := by
      apply Fin.ext
      change 2 * (i.val / 2) = i.val
      omega
    simpa only [Function.comp_apply, hj] using congrFun he j
  · let j : Fin k := ⟨i.val / 2, by omega⟩
    have hj : oddIndex j = i := by
      apply Fin.ext
      change 2 * (i.val / 2) + 1 = i.val
      omega
    simpa only [Function.comp_apply, hj] using congrFun ho j

private theorem image_eq_of_orderedTurns {d : ℕ} {up : Bool} {e : Fin d → Point}
    {T : Finset Point} (hTd : T.card = d) (hsub : ∀ i, e i ∈ T)
    (he : OrderedTurns up e) : Finset.univ.image e = T := by
  classical
  have hi : Function.Injective e := fun i j hij => he.1.injective (congrArg Prod.fst hij)
  have hs : Finset.univ.image e ⊆ T := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact hsub i
  apply Finset.eq_of_subset_of_card_le hs
  rw [Finset.card_image_of_injective _ hi, card_univ, Fintype.card_fin, hTd]

private theorem pow_le_mul_choose {N d : ℕ} (h : 2 * (d - 1) ≤ N) :
    N ^ d ≤ (2 ^ d * d.factorial) * N.choose d := by
  have h₁ : N ≤ 2 * (N + 1 - d) := by omega
  calc
    N ^ d ≤ (2 * (N + 1 - d)) ^ d := Nat.pow_le_pow_left h₁ _
    _ = 2 ^ d * (N + 1 - d) ^ d := Nat.mul_pow _ _ _
    _ ≤ 2 ^ d * N.descFactorial d := Nat.mul_le_mul_left _ (N.pow_sub_le_descFactorial d)
    _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_assoc]

private def regionConstant (m k : ℕ) : ℕ :=
  2 * (2 ^ (2 * k + 1) * (2 * k + 1).factorial * m.choose (2 * k + 1))

/-- A weak positive-fraction form of the cup-cap theorem, giving an
ordered chain of anchors with many insertions in every gap. -/
private theorem dense_ordered_regions {k L m : ℕ} (S : Finset Point) (hk : 0 < k)
    (hm : 2 * k + 1 ≤ m) (hmS : m ≤ S.card) (h4k : 4 * k ≤ S.card)
    (hit : ∀ U ⊆ S, U.card = m → ∃ T ⊆ U, T.card = 2 * k + 1 ∧ GoodTurns (2 * k + 1) T)
    (hlarge : regionConstant m k * L < S.card) :
    ∃ (up : Bool) (a : Fin (k + 1) → Point), (∀ i, a i ∈ S) ∧ OrderedTurns up a ∧
      ∀ i : Fin k, L < (S.filter (InGap up a i)).card := by
  classical
  let d := 2 * k + 1
  let G := (S.powersetCard d).filter (GoodTurns d)
  have hgood (T : ↑G) : GoodTurns d T.val := (mem_filter.mp T.property).2
  let up (T : ↑G) := (hgood T).choose
  let e (T : ↑G) := (hgood T).choose_spec.choose
  have he (T : ↑G) : (∀ i, e T i ∈ T.val) ∧ OrderedTurns (up T) (e T) :=
    (hgood T).choose_spec.choose_spec
  have hT (T : ↑G) := mem_powersetCard.mp (mem_filter.mp T.property).1
  let anchor (T : ↑G) := (up T, e T ∘ evenIndex)
  let completion (T : ↑G) := e T ∘ oddIndex
  let A := G.attach.image anchor
  let A₀ := (Finset.univ : Finset Bool) ×ˢ Fintype.piFinset (fun _ : Fin (k + 1) => S)
  let R (a : Bool × (Fin (k + 1) → Point)) (i : Fin k) := S.filter (InGap a.1 a.2 i)
  have hAA₀ : A ⊆ A₀ := by
    intro a ha
    obtain ⟨T, _, rfl⟩ := mem_image.mp ha
    exact mem_product.mpr ⟨mem_univ _, Fintype.mem_piFinset.mpr
      (fun i => (hT T).1 ((he T).1 (evenIndex i)))⟩
  have hAc : A.card ≤ 2 * S.card ^ (k + 1) := by
    simpa [A₀, Fintype.card_piFinset_const] using card_le_card hAA₀
  have hbound : S.card ^ d ≤ G.card * (2 ^ d * d.factorial * m.choose d) := by
    calc
      S.card ^ d ≤ (2 ^ d * d.factorial) * S.card.choose d :=
        pow_le_mul_choose (by dsimp [d]; omega)
      _ ≤ (2 ^ d * d.factorial) * (G.card * m.choose d) :=
        Nat.mul_le_mul_left _ (dense_subsets S hm hmS (GoodTurns d) hit)
      _ = _ := by ac_rfl
  have hexp : k + 1 + (k - 1) = 2 * k := by omega
  have hcount : A.card * (L * S.card ^ (k - 1)) < G.attach.card := by
    rw [card_attach]
    by_contra! hc
    have hab := (Nat.mul_le_mul_right (L * S.card ^ (k - 1)) hAc)
    have hb := hbound.trans (Nat.mul_le_mul_right _ (hc.trans hab))
    exact (lt_irrefl (S.card ^ d)) (calc
      S.card ^ d ≤
          (2 * S.card ^ (k + 1) * (L * S.card ^ (k - 1))) *
            (2 ^ d * d.factorial * m.choose d) := hb
      _ = (regionConstant m k * L) * S.card ^ (2 * k) := by
        unfold regionConstant
        change _ = (2 * (2 ^ d * d.factorial * m.choose d) * L) * S.card ^ (2 * k)
        rw [← hexp, pow_add S.card (k + 1) (k - 1)]
        ac_rfl
      _ < S.card * S.card ^ (2 * k) :=
        Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos (by omega))
      _ = S.card ^ d := by dsimp [d]; rw [pow_succ'])
  obtain ⟨a, ha, hLa⟩ := large_completion_regions S G.attach A anchor completion R
    (fun T hT' => mem_image.mpr ⟨T, hT', rfl⟩)
    (fun _ _ _ => filter_subset _ _)
    (fun T _ i => mem_filter.mpr ⟨(hT T).1 ((he T).1 (oddIndex i)),
      inGap_of_orderedTurns (he T).2 i⟩)
    (fun T _ U _ ha' hc' => by
      have hfun : e T = e U := even_odd_determine (congrArg Prod.snd ha') hc'
      apply Subtype.ext
      rw [← image_eq_of_orderedTurns (hT T).2 (he T).1 (he T).2,
        ← image_eq_of_orderedTurns (hT U).2 (he U).1 (he U).2, hfun])
    hcount
  obtain ⟨T, -, rfl⟩ := mem_image.mp ha
  refine ⟨up T, e T ∘ evenIndex, fun i => (hT T).1 ((he T).1 (evenIndex i)),
    ⟨?_, ?_⟩, hLa⟩
  · intro i j hij
    exact (he T).2.1 (show evenIndex i < evenIndex j from by
      change 2 * i.val < 2 * j.val
      omega)
  · intro i j l hij hjl
    exact (he T).2.2 _ _ _ (show evenIndex i < evenIndex j from by
      change 2 * i.val < 2 * j.val
      omega) (show evenIndex j < evenIndex l from by
      change 2 * j.val < 2 * l.val
      omega)


private def orderedRegionSample (k : ℕ) : ℕ :=
  max (2 * k + 1) (((2 * k - 1) + (2 * k - 1)).choose (2 * k - 1) + 1)

private theorem ordered_regions_of_general_position {k L : ℕ} (S : Finset Point)
    (hk : 0 < k) (hmS : orderedRegionSample k ≤ S.card) (h4k : 4 * k ≤ S.card)
    (hx : Set.InjOn Prod.fst (S : Set Point))
    (hg : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p.1 < q.1 → q.1 < r.1 → orient p q r ≠ 0)
    (hsize : regionConstant (orderedRegionSample k) k * L < S.card) :
    ∃ (up : Bool) (a : Fin (k + 1) → Point), (∀ i, a i ∈ S) ∧ OrderedTurns up a ∧
      ∀ i : Fin k, L < (S.filter (InGap up a i)).card := by
  apply dense_ordered_regions S hk (le_max_left _ _) hmS h4k _ hsize
  intro U hUS hUm
  let s := 2 * k - 1
  have hsd : s + 2 = 2 * k + 1 := by dsimp [s]; omega
  have hb : (s + s).choose s < U.card := by
    rw [hUm]
    exact Nat.lt_of_succ_le (le_max_right _ _)
  have hgU : ∀ p ∈ U, ∀ q ∈ U, ∀ r ∈ U,
      p.1 < q.1 → q.1 < r.1 → orient p q r ≠ 0 :=
    fun p hp q hq r hr => hg p (hUS hp) q (hUS hq) r (hUS hr)
  have hs : HasSeq true U (s + 2) ∨ HasSeq false U (s + 2) := by
    by_contra! hn
    exact hb.not_ge (card_le_binomial s s U (hx.mono hUS) hgU hn.1 hn.2)
  have pull {up : Bool} (h : HasSeq up U (s + 2)) :
      ∃ T ⊆ U, T.card = 2 * k + 1 ∧ GoodTurns (2 * k + 1) T := by
    rw [hsd] at h
    obtain ⟨e, hem, he⟩ := ordered_turns_of_hasSeq h
    classical
    have hi : Function.Injective e := fun i j hij => he.1.injective (congrArg Prod.fst hij)
    refine ⟨Finset.univ.image e, ?_, by simp [Finset.card_image_of_injective _ hi],
      up, e, fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, he⟩
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hem i
  exact hs.elim pull pull

private theorem orient_cyclic (a b c : Point) : orient b c a = orient a b c := by
  unfold orient
  ring

private theorem turn_cyclic (up : Bool) (a b c : Point) :
    turn up b c a ↔ turn up a b c := by
  unfold turn
  rw [orient_cyclic]

private theorem orient_right_trans {p b c z : Point}
    (hpb : p.1 < b.1) (hbc : b.1 < c.1) (hcz : c.1 < z.1)
    (hpbc : orient p b c < 0) (hbcz : orient b c z < 0) : orient p b z < 0 := by
  have h :
      orient p b z * (c.1 - b.1) =
        orient p b c * (z.1 - b.1) + orient b c z * (b.1 - p.1) := by
    unfold orient
    ring
  have h₁ := mul_neg_of_neg_of_pos hpbc (sub_pos.mpr (hbc.trans hcz))
  have h₂ := mul_neg_of_neg_of_pos hbcz (sub_pos.mpr hpb)
  have hneg : orient p b z * (c.1 - b.1) < 0 := h ▸ add_neg h₁ h₂
  by_contra! hpos
  exact hneg.not_ge (mul_nonneg hpos (sub_nonneg.mpr hbc.le))

private theorem orient_left_trans {z a b p : Point}
    (hza : z.1 < a.1) (hab : a.1 < b.1) (hbp : b.1 < p.1)
    (hzab : orient z a b < 0) (habp : orient a b p < 0) : orient z b p < 0 := by
  have h :
      orient z b p * (b.1 - a.1) =
        orient z a b * (p.1 - b.1) + orient a b p * (b.1 - z.1) := by
    unfold orient
    ring
  have h₁ := mul_neg_of_neg_of_pos hzab (sub_pos.mpr hbp)
  have h₂ := mul_neg_of_neg_of_pos habp (sub_pos.mpr (hza.trans hab))
  have hneg : orient z b p * (b.1 - a.1) < 0 := h ▸ add_neg h₁ h₂
  by_contra! hpos
  exact hneg.not_ge (mul_nonneg hpos (sub_nonneg.mpr hab.le))

/-- A point at least two gaps to the right lies below the ray from a gap
point through its right anchor. -/
private theorem right_of_gap {k : ℕ} {a : Fin (k + 1) → Point}
    {i j : Fin k} {p z : Point} (ha : OrderedTurns false a)
    (hp : InGap false a i p) (hz : InGap false a j z) (hij : i.val + 2 ≤ j.val) :
    let b : Fin (k + 1) := ⟨i.val + 1, by omega⟩
    (a b).1 < z.1 ∧ orient p (a b) z < 0 := by
  dsimp only
  let b : Fin (k + 1) := ⟨i.val + 1, by omega⟩
  let c : Fin (k + 1) := ⟨i.val + 2, by omega⟩
  let j₀ : Fin (k + 1) := ⟨j.val, by omega⟩
  have hbc : b < c := by change i.val + 1 < i.val + 2; omega
  have hcj : c ≤ j₀ := hij
  have hcz : (a c).1 < z.1 := (ha.1.monotone hcj).trans_lt hz.1
  have hpbc : orient p (a b) (a c) < 0 := by
    have h := hp.2.2 b c hbc
    have h₁ : ¬ c.val ≤ i.val := by dsimp [c]; omega
    have h₂ : i.val < b.val := by dsimp [b]; omega
    simpa only [h₁, if_false, h₂, if_true, turn, Bool.false_eq_true, if_false] using h
  have hbcz : orient (a b) (a c) z < 0 := by
    simpa only [if_pos hij, turn, c, Bool.false_eq_true, if_false] using hz.2.2 b c hbc
  exact ⟨(ha.1 hbc).trans hcz, orient_right_trans hp.2.1 (ha.1 hbc) hcz hpbc hbcz⟩

/-- The corresponding ray through the left anchor. -/
private theorem left_of_gap {k : ℕ} {a : Fin (k + 1) → Point}
    {i j : Fin k} {p z : Point} (ha : OrderedTurns false a)
    (hp : InGap false a i p) (hz : InGap false a j z) (hji : j.val + 2 ≤ i.val) :
    let b : Fin (k + 1) := ⟨i.val, by omega⟩
    z.1 < (a b).1 ∧ orient z (a b) p < 0 := by
  dsimp only
  let b : Fin (k + 1) := ⟨i.val, by omega⟩
  let c : Fin (k + 1) := ⟨i.val - 1, by omega⟩
  let j₁ : Fin (k + 1) := ⟨j.val + 1, by omega⟩
  have hcb : c < b := by change i.val - 1 < i.val; omega
  have hjc : j₁ ≤ c := by change j.val + 1 ≤ i.val - 1; omega
  have hzc : z.1 < (a c).1 := hz.2.1.trans_le (ha.1.monotone hjc)
  have hzcb : orient z (a c) (a b) < 0 := by
    have h := hz.2.2 c b hcb
    have h₁ : ¬ b.val ≤ j.val := by dsimp [b]; omega
    have h₂ : j.val < c.val := by dsimp [c]; omega
    simpa only [h₁, if_false, h₂, if_true, turn, Bool.false_eq_true, if_false] using h
  have hcbp : orient (a c) (a b) p < 0 := by
    have h := hp.2.2 c b hcb
    have h₁ : b.val ≤ i.val := le_rfl
    simpa only [if_pos h₁, turn, Bool.false_eq_true, if_false] using h
  exact ⟨hzc.trans (ha.1 hcb), orient_left_trans hzc (ha.1 hcb) hp.1 hzcb hcbp⟩

private theorem cap_edge_external {k : ℕ} {a : Fin (k + 1) → Point}
    {i j : Fin k} {p q z : Point} (ha : OrderedTurns false a)
    (hp : InGap false a i p) (hq : InGap false a i q) (hz : InGap false a j z)
    (hpq : p.1 < q.1)
    (hl : orient (a ⟨i.val, by omega⟩) p q < 0)
    (hr : orient p q (a ⟨i.val + 1, by omega⟩) < 0)
    (hsep : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) : orient p q z < 0 := by
  rcases hsep with hij | hji
  · obtain ⟨hbx, hbz⟩ := right_of_gap ha hq hz hij
    exact orient_right_trans hpq hq.2.1 hbx hr hbz
  · obtain ⟨hxb, hzb⟩ := left_of_gap ha hp hz hji
    rw [orient_cyclic z p q]
    exact orient_left_trans hxb hp.1 hpq hzb hl

private noncomputable def normalizeGap (a b p : Point) : Point :=
  ((p.1 - a.1) / (b.1 - a.1), orient a b p)

private theorem normalizeGap_orient {a b : Point} (hab : a.1 < b.1) (p q r : Point) :
    orient (normalizeGap a b p) (normalizeGap a b q) (normalizeGap a b r) =
      orient p q r := by
  have hne : b.1 - a.1 ≠ 0 := sub_ne_zero.mpr hab.ne'
  dsimp only [normalizeGap, orient]
  field_simp
  ring

private theorem normalizeGap_anchors {a b : Point} (hab : a.1 < b.1) :
    normalizeGap a b a = (0, 0) ∧ normalizeGap a b b = (1, 0) := by
  have hne : b.1 - a.1 ≠ 0 := sub_ne_zero.mpr hab.ne'
  constructor <;> apply Prod.ext <;> simp [normalizeGap, orient, hne] <;> ring

private theorem normalizedGap_bounds {k : ℕ} {a : Fin (k + 1) → Point} {i : Fin k}
    {p : Point} (hp : InGap false a i p) :
    let F := normalizeGap (a ⟨i.val, by omega⟩) (a ⟨i.val + 1, by omega⟩)
    0 < (F p).1 ∧ (F p).1 < 1 ∧ 0 < (F p).2 := by
  let l : Fin (k + 1) := ⟨i.val, by omega⟩
  let r : Fin (k + 1) := ⟨i.val + 1, by omega⟩
  have hden := sub_pos.mpr (hp.1.trans hp.2.1)
  refine ⟨div_pos (sub_pos.mpr hp.1) hden, (div_lt_one hden).mpr (sub_lt_sub_right hp.2.1 _), ?_⟩
  have h := hp.2.2 l r (by change i.val < i.val + 1; omega)
  have h₁ : ¬ r.val ≤ i.val := by dsimp [r]; omega
  have h₂ : ¬ i.val < l.val := lt_irrefl _
  simp only [h₁, h₂, if_false, turn] at h
  change 0 < orient (a l) (a r) p
  have he : orient (a l) (a r) p = - orient (a l) p (a r) := by
    unfold orient
    ring
  rw [he]
  exact neg_pos.mpr h

private theorem normalized_antichain_x {p q : Point}
    (hp : 0 < p.1) (hq : q.1 < 1) (hpy : 0 < p.2) (hqy : 0 < q.2)
    (hl : orient (0, 0) p q < 0) (hr : orient (1, 0) p q < 0) :
    p.1 < q.1 := by
  by_contra! hn
  have hl' : p.1 * q.2 < p.2 * q.1 := by
    dsimp [orient] at hl
    linarith only [hl]
  have hr' : (1 - q.1) * p.2 < (1 - p.1) * q.2 := by
    dsimp [orient] at hr
    linarith only [hr]
  have h₁ : q.2 < p.2 := by
    apply lt_of_mul_lt_mul_left _ hp.le
    exact hl'.trans_le (by nlinarith only [mul_nonneg (sub_nonneg.mpr hn) hpy.le])
  have h₂ : p.2 < q.2 := by
    apply lt_of_mul_lt_mul_left _ (sub_nonneg.mpr hq.le)
    exact hr'.trans_le (by nlinarith only [mul_nonneg (sub_nonneg.mpr hn) hqy.le])
  exact (lt_asymm h₁ h₂)

private def Exposed (Y : Finset Point) (p : Point) : Prop :=
  ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2

private theorem exposes_subset {Y Z : Finset Point} {p : Point}
    (hZY : Z ⊆ Y) (hp : Exposed Y p) : Exposed Z p := by
  obtain ⟨u, v, h⟩ := hp
  exact ⟨u, v, fun q hq hqp => h q (hZY hq) hqp⟩

private theorem exists_small_pos {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 < f x) : ∃ δ > 0, ∀ x ∈ S, δ ≤ f x := by
  classical
  rcases S.eq_empty_or_nonempty with h | h
  · subst S
    exact ⟨1, zero_lt_one, by simp⟩
  · obtain ⟨x, hx, hmin⟩ := S.exists_min_image f h
    exact ⟨f x, hf x hx, hmin⟩

/-- A strictly supporting edge exposes each of its endpoints after a
sufficiently small linear perturbation. -/
private theorem exposed_of_support {Y : Finset Point} {p r : Point} {u v : ℝ}
    (hpr : p.1 ≠ r.1) (he : u * p.1 + v * p.2 = u * r.1 + v * r.2)
    (h : ∀ q ∈ Y, q ≠ p → q ≠ r → u * p.1 + v * p.2 < u * q.1 + v * q.2) :
    Exposed Y p := by
  classical
  let L (q : Point) := u * q.1 + v * q.2
  let w : ℝ := if p.1 < r.1 then 1 else -1
  let M (q : Point) := w * q.1
  have hMr : M p < M r := by
    rcases lt_or_gt_of_ne hpr with hlt | hgt
    · simpa [M, w, hlt] using hlt
    · simpa [M, w, hgt.not_gt] using hgt
  obtain ⟨δ, hδ, hmin⟩ := exists_small_pos ((Y.erase p).erase r)
    (fun q => (L q - L p) / (1 + |M q - M p|)) (by
      intro q hq
      rw [Finset.mem_erase, Finset.mem_erase] at hq
      exact div_pos (sub_pos.mpr (h q hq.2.2 hq.2.1 hq.1)) (by positivity))
  refine ⟨u + δ * w, v, fun q hq hqp => ?_⟩
  have hsum : L p + δ * M p < L q + δ * M q := by
    by_cases hqr : q = r
    · subst q
      change L p = L r at he
      rw [he]
      exact add_lt_add_right (mul_lt_mul_of_pos_left hMr hδ) _
    · have hb := hmin q (Finset.mem_erase.mpr ⟨hqr, Finset.mem_erase.mpr ⟨hqp, hq⟩⟩)
      have hden : 0 < 1 + |M q - M p| := by positivity
      have hb' := (le_div_iff₀ hden).mp hb
      have hm := mul_le_mul_of_nonneg_left (neg_abs_le (M q - M p)) hδ.le
      linarith only [hb', hm, hδ, show δ * (1 + |M q - M p|) =
        δ + δ * |M q - M p| by ring,
        show δ * (-(|M q - M p|)) = -(δ * |M q - M p|) by ring,
        show δ * (M q - M p) = δ * M q - δ * M p by ring]
  calc
    _ = L p + δ * M p := by dsimp [L, M]; ring
    _ < L q + δ * M q := hsum
    _ = _ := by dsimp [L, M]; ring

private theorem exposed_of_directed_edge {Y : Finset Point} {p r : Point}
    (hpr : p.1 ≠ r.1) (up : Bool)
    (h : ∀ q ∈ Y, q ≠ p → q ≠ r → turn up p r q) : Exposed Y p := by
  cases up with
  | true =>
    apply exposed_of_support (u := p.2 - r.2) (v := r.1 - p.1) hpr (by ring)
    intro q hq hqp hqr
    have ht := h q hq hqp hqr
    change 0 < orient p r q at ht
    unfold orient at ht
    linarith only [ht]
  | false =>
    apply exposed_of_support (u := r.2 - p.2) (v := p.1 - r.1) hpr (by ring)
    intro q hq hqp hqr
    have ht := h q hq hqp hqr
    change orient p r q < 0 at ht
    unfold orient at ht
    linarith only [ht]

private theorem exposed_of_reversed_edge {Y : Finset Point} {p r : Point}
    (hpr : p.1 ≠ r.1) (up : Bool)
    (h : ∀ q ∈ Y, q ≠ p → q ≠ r → turn up r p q) : Exposed Y p := by
  apply exposed_of_directed_edge hpr (!up)
  intro q hq hqp hqr
  have ht := h q hq hqp hqr
  have hs : orient p r q = - orient r p q := by unfold orient; ring
  cases up
  · change 0 < orient p r q
    rw [hs]
    exact neg_pos.mpr ht
  · change orient p r q < 0
    rw [hs]
    exact neg_lt_zero.mpr ht

/-- Adjacent pairs within a piece serve as supporting edges of the whole
set when all exterior points have the same turn as the piece. -/
private theorem exposed_of_ordered_piece {Y A : Finset Point} {p : Point}
    (hA : A ⊆ Y) (hp : p ∈ A) (hcard : 2 ≤ A.card)
    (hx : Set.InjOn Prod.fst (Y : Set Point))
    (key : Point → ℝ) (hkey : Set.InjOn key (A : Set Point)) (up : Bool)
    (hin : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, key a < key b → key b < key c → turn up a b c)
    (hout : ∀ a ∈ A, ∀ b ∈ A, key a < key b → ∀ c ∈ Y, c ∉ A → turn up a b c) :
    Exposed Y p := by
  classical
  let R := A.filter (fun q => key p < key q)
  have pair {a b : Point} (ha : a ∈ A) (hb : b ∈ A) (hab : key a < key b)
      (hadj : ∀ c ∈ A, ¬(key a < key c ∧ key c < key b)) :
      ∀ c ∈ Y, c ≠ a → c ≠ b → turn up a b c := by
    intro c hc hca hcb
    by_cases hcA : c ∈ A
    · rcases lt_or_gt_of_ne (fun he => hca (hkey hcA ha he)) with hca' | hac'
      · exact (turn_cyclic up c a b).mpr (hin c hcA a ha b hb hca' hab)
      · rcases lt_or_gt_of_ne (fun he => hcb (hkey hcA hb he)) with hcb' | hbc'
        · exact (hadj c hcA ⟨hac', hcb'⟩).elim
        · exact hin a ha b hb c hcA hab hbc'
    · exact hout a ha b hb hab c hc hcA
  by_cases hR : R.Nonempty
  · obtain ⟨q, hq, hmin⟩ := R.exists_min_image key hR
    obtain ⟨hqA, hpq⟩ := Finset.mem_filter.mp hq
    apply exposed_of_directed_edge (fun he => hpq.ne (congrArg key (hx (hA hp) (hA hqA) he))) up
    exact pair hp hqA hpq fun c hc h => h.2.not_ge (hmin c (Finset.mem_filter.mpr ⟨hc, h.1⟩))
  · have hall : ∀ c ∈ A, c ≠ p → key c < key p := by
      intro c hc hcp
      rcases lt_or_gt_of_ne (fun he => hcp (hkey hc hp he)) with h | h
      · exact h
      · exact (hR ⟨c, Finset.mem_filter.mpr ⟨hc, h⟩⟩).elim
    have hne : (A.erase p).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hp]
      omega)
    obtain ⟨q, hq, hmax⟩ := (A.erase p).exists_max_image key hne
    obtain ⟨hqp, hqA⟩ := Finset.mem_erase.mp hq
    apply exposed_of_reversed_edge (fun he => hqp (hx (hA hp) (hA hqA) he).symm) up
    intro c hc hcp hcq
    exact pair hqA hp (hall q hqA hqp)
      (fun d hd h => h.1.not_ge (hmax d (Finset.mem_erase.mpr
        ⟨fun he => h.2.ne (congrArg key he), hd⟩))) c hc hcq hcp

end Erdos107Suk

theorem OMA.solution : OMA.R_Erdos107_variants_su_bound_R1.H1 := by
  sorry

