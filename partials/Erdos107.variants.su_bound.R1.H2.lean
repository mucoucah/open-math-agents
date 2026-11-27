import OMAReductions.R_Erdos107_variants_su_bound_R1
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Choose.Bounds

/-! Coordinate lemmas for Suk’s Erdős–Szekeres bound. -/

-- Step Erdos107.variants.su_bound.R1.H2: hypothesis H2 of reduction Erdos107.variants.su_bound.R1
-- Credit: @<handle>
-- H2 := ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop, Odd n →     ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧       ∀ X : Finset (ℝ × ℝ), X.card = N →         Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) →         (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 →           (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →         ∃ Y ⊆ X, Y.card = n ∧           ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2

open Finset Filter

namespace SukOdd

private abbrev Point := ℝ × ℝ

private def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

private def PlanarConvex (Y : Finset Point) : Prop :=
  ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2

private def PlanarGeneral (X : Finset Point) : Prop :=
  Set.InjOn Prod.fst (X : Set Point) ∧
    ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0

private theorem orient_cycle (a b c : Point) : orient a b c = orient b c a := by
  unfold orient
  ring

private theorem orient_flip (a b c : Point) : orient a b c = -orient b a c := by
  unfold orient
  ring

private theorem orient_basis (p q a b r : Point) :
    orient p a b * orient p q r =
      orient p r b * orient p q a + orient p a r * orient p q b := by
  unfold orient
  ring

/-- A secant with both anchors to its right also has every point in their angular sector to
its right. -/
private theorem orient_lt_of_sector {p q a b r : Point}
    (hab : 0 < orient p a b) (har : 0 < orient p a r) (hrb : 0 < orient p r b)
    (hqa : orient p q a < 0) (hqb : orient p q b < 0) :
    orient p q r < 0 := by
  refine lt_of_not_ge fun h => ?_
  have hnonneg := mul_nonneg hab.le h
  rw [orient_basis] at hnonneg
  apply (not_lt_of_ge hnonneg)
  exact add_neg (mul_neg_of_pos_of_neg hrb hqa) (mul_neg_of_pos_of_neg har hqb)

/-- A secant with opposite anchor signs is consistently oriented toward a point on the
corresponding side of both anchor rays. -/
private theorem orient_lt_of_preceding {p q a b r : Point}
    (hab : 0 < orient p a b) (har : orient p a r < 0) (hrb : 0 < orient p r b)
    (hqa : orient p q a < 0) (hqb : 0 < orient p q b) :
    orient p q r < 0 := by
  refine lt_of_not_ge fun h => ?_
  have hnonneg := mul_nonneg hab.le h
  rw [orient_basis] at hnonneg
  apply (not_lt_of_ge hnonneg)
  exact add_neg (mul_neg_of_pos_of_neg hrb hqa) (mul_neg_of_neg_of_pos har hqb)

private theorem orient_pos_of_following {p q a b r : Point}
    (hab : 0 < orient p a b) (har : 0 < orient p a r) (hrb : orient p r b < 0)
    (hqa : orient p q a < 0) (hqb : 0 < orient p q b) :
    0 < orient p q r := by
  apply (mul_pos_iff_of_pos_left hab).mp
  rw [orient_basis]
  exact add_pos (mul_pos_of_neg_of_neg hrb hqa) (mul_pos har hqb)

private theorem convex_subset {X Y : Finset Point} (hYX : Y ⊆ X) (hX : PlanarConvex X) :
    PlanarConvex Y := by
  intro p hp
  obtain ⟨u, v, huv⟩ := hX p (hYX hp)
  exact ⟨u, v, fun q hq hne => huv q (hYX hq) hne⟩

private theorem exact_convex_size {X Y : Finset Point} {n : ℕ}
    (hYX : Y ⊆ X) (hY : PlanarConvex Y) (hn : n ≤ Y.card) :
    ∃ Z ⊆ X, Z.card = n ∧ PlanarConvex Z := by
  obtain ⟨Z, hZY, hZ⟩ := Finset.exists_subset_card_eq hn
  exact ⟨Z, hZY.trans hYX, hZ, convex_subset hZY hY⟩

/-- If no consecutive directed pair attains the target, the first summand must
grow by the full surplus at every step. -/
private theorem growth_along_blocks {a b : ℕ → ℕ} {n d k : ℕ}
    (hlarge : ∀ i ≤ k, n + d ≤ a i + b i)
    (hsmall : ∀ i < k, a i + b (i + 1) < n) :
    a 0 + k * (d + 1) ≤ a k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun i hi => hlarge i (by omega)) (fun i hi => hsmall i (by omega))
    have hstep := hlarge (k + 1) le_rfl
    have hpair := hsmall k (by omega)
    rw [Nat.succ_mul]
    omega

private theorem orient_reverse (a b c : Point) : orient a b c = -orient c b a := by
  unfold orient
  ring

private theorem orient_swap_last (a b c : Point) : orient a b c = -orient a c b := by
  unfold orient
  ring

private noncomputable def rotatedKey {ι : Type*} [LinearOrder ι] (origin u : ι) :
    Bool ×ₗ ι :=
  toLex (decide (u < origin), u)

private theorem orient_of_rotatedKey {ι : Type*} [LinearOrder ι]
    {X : Finset Point} {key : Point → ι}
    (h : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, key a < key b → key b < key c →
      orient a b c < 0)
    {p q r : Point} (hp : p ∈ X) (hq : q ∈ X) (hr : r ∈ X)
    (hpq : key q ≠ key p)
    (hqr : rotatedKey (key p) (key q) < rotatedKey (key p) (key r)) :
    orient p q r < 0 := by
  unfold rotatedKey at hqr
  rw [Prod.Lex.toLex_lt_toLex] at hqr
  by_cases hq' : key q < key p <;> by_cases hr' : key r < key p
  · have he : key q < key r := by simpa [hq', hr'] using hqr
    rw [orient_cycle]
    exact h q hq r hr p hp he hr'
  · simp [hq', hr'] at hqr
    exact ((by decide : ¬ (true : Bool) < false) hqr).elim
  · have hpq' := lt_of_le_of_ne (le_of_not_gt hq') hpq.symm
    rw [← orient_cycle r p q]
    exact h r hr p hp q hq hr' hpq'
  · have hpq' := lt_of_le_of_ne (le_of_not_gt hq') hpq.symm
    have he : key q < key r := by simpa [hq', hr'] using hqr
    exact h p hp q hq r hr hpq' he

private theorem rotatedKey_injective {ι : Type*} [LinearOrder ι] (origin : ι) :
    Function.Injective (rotatedKey origin) := by
  intro u v huv
  exact congrArg (fun z => (ofLex z).2) huv

private theorem dot_strict {p r : Point} (hne : p ≠ r) :
    (r.1 - p.1) * p.1 + (r.2 - p.2) * p.2 <
      (r.1 - p.1) * r.1 + (r.2 - p.2) * r.2 := by
  rcases not_and_or.mp (fun h : p.1 = r.1 ∧ p.2 = r.2 => hne (Prod.ext h.1 h.2)) with h | h
  · nlinarith only [sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm h) : r.1 - p.1 ≠ 0),
      sq_nonneg (r.2 - p.2)]
  · nlinarith only [sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm h) : r.2 - p.2 ≠ 0),
      sq_nonneg (r.1 - p.1)]

/-- A cyclic order in which every triple turns clockwise gives strict support at every point. -/
private theorem convex_of_clockwise {ι : Type*} [LinearOrder ι]
    {X : Finset Point} {key : Point → ι} (hinj : Set.InjOn key (X : Set Point))
    (h : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, key a < key b → key b < key c →
      orient a b c < 0) : PlanarConvex X := by
  classical
  intro p hp
  let T := X.erase p
  by_cases hT : T.Nonempty
  · let key' := fun q => rotatedKey (key p) (key q)
    obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image T key' hT
    obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image T key' hT
    have hne (q : Point) (hq : q ∈ T) : key q ≠ key p :=
      fun e => (mem_erase.mp hq).1 (hinj (mem_erase.mp hq).2 hp e)
    have hinj' : Set.InjOn key' (T : Set Point) :=
      fun a ha b hb e => hinj (mem_erase.mp ha).2 (mem_erase.mp hb).2
        (rotatedKey_injective (key p) e)
    have hrot {a b : Point} (ha : a ∈ T) (hb : b ∈ T) (hab : key' a < key' b) :
        orient p a b < 0 :=
      orient_of_rotatedKey h hp (mem_erase.mp ha).2 (mem_erase.mp hb).2
        (hne a ha) hab
    by_cases hrs : r = s
    · refine ⟨r.1 - p.1, r.2 - p.2, fun q hq hqp => ?_⟩
      have hqT : q ∈ T := mem_erase.mpr ⟨hqp, hq⟩
      have hqr : q = r := hinj' hqT hr (le_antisymm (hrs ▸ hmax q hqT) (hmin q hqT))
      subst q
      exact dot_strict (mem_erase.mp hr).1.symm
    · refine ⟨r.2 - s.2, s.1 - r.1, fun q hq hqp => ?_⟩
      have hqT : q ∈ T := mem_erase.mpr ⟨hqp, hq⟩
      have hl : orient p r q ≤ 0 := by
        by_cases hqr : r = q
        · subst q
          simp [orient]
        exact (hrot hr hqT ((hmin q hqT).lt_of_ne (fun e => hqr (hinj' hr hqT e)))).le
      have hu : 0 ≤ orient p s q := by
        by_cases hqs : q = s
        · subst q
          simp [orient]
        rw [orient_swap_last]
        exact neg_nonneg.mpr
          (hrot hqT hs ((hmax q hqT).lt_of_ne (fun e => hqs (hinj' hqT hs e)))).le
      have hstrict : orient p r q < orient p s q := by
        by_cases hqr : r = q
        · rw [orient_swap_last p s q]
          have hpos := hrot hqT hs
            ((hmax q hqT).lt_of_ne (fun e => hrs (hqr.trans (hinj' hqT hs e))))
          subst q
          rw [show orient p r r = 0 by simp [orient]]
          exact neg_pos.mpr hpos
        exact (hrot hr hqT ((hmin q hqT).lt_of_ne (fun e => hqr (hinj' hr hqT e)))).trans_le hu
      unfold orient at hstrict
      linarith only [hstrict]
  · exact ⟨0, 0, fun q hq hqp => (hT ⟨q, mem_erase.mpr ⟨hqp, hq⟩⟩).elim⟩

private def anchorNorm (a b : Point) : ℝ :=
  (b.1 - a.1)^2 + (b.2 - a.2)^2

private def anchorDot (a b p : Point) : ℝ :=
  (b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)

private noncomputable def projected (a b p : Point) : Point :=
  (anchorDot a b p / orient a b p, (anchorNorm a b - anchorDot a b p) / orient a b p)

private theorem anchorNorm_pos {a b : Point} (h : a ≠ b) : 0 < anchorNorm a b := by
  unfold anchorNorm
  rcases not_and_or.mp (fun e : a.1 = b.1 ∧ a.2 = b.2 => h (Prod.ext e.1 e.2)) with e | e
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm e))) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm e)))

private theorem projected_fst_lt {a b p q : Point} (hab : a ≠ b)
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) :
    (projected a b p).1 < (projected a b q).1 ↔ orient p q a < 0 := by
  change anchorDot a b p / orient a b p < anchorDot a b q / orient a b q ↔ _
  rw [div_lt_div_iff₀ hp hq, ← sub_neg]
  have he : anchorDot a b p * orient a b q - anchorDot a b q * orient a b p =
      anchorNorm a b * orient p q a := by
    unfold anchorDot anchorNorm orient
    ring
  rw [he]
  constructor
  · intro hn
    exact lt_of_not_ge fun hn' => (not_lt_of_ge (mul_nonneg (anchorNorm_pos hab).le hn')) hn
  · exact mul_neg_of_pos_of_neg (anchorNorm_pos hab)

private theorem projected_snd_lt {a b p q : Point} (hab : a ≠ b)
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) :
    (projected a b p).2 < (projected a b q).2 ↔ 0 < orient p q b := by
  change (anchorNorm a b - anchorDot a b p) / orient a b p <
    (anchorNorm a b - anchorDot a b q) / orient a b q ↔ _
  rw [div_lt_div_iff₀ hp hq, ← sub_pos]
  have he : (anchorNorm a b - anchorDot a b q) * orient a b p -
      (anchorNorm a b - anchorDot a b p) * orient a b q =
      anchorNorm a b * orient p q b := by
    unfold anchorDot anchorNorm orient
    ring
  rw [he, mul_pos_iff_of_pos_left (anchorNorm_pos hab)]

private theorem projected_orientation {a b p q r : Point}
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) (hr : 0 < orient a b r) :
    (orient a b p * orient a b q * orient a b r) *
        orient (projected a b p) (projected a b q) (projected a b r) =
      -(anchorNorm a b)^2 * orient p q r := by
  simp only [projected, orient] at *
  unfold anchorNorm anchorDot
  field_simp [ne_of_gt hp, ne_of_gt hq, ne_of_gt hr]
  ring

section CupsCaps
open scoped Classical

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

/-- Asymmetric cups and caps: more than C(s+t,s) points in general position contain an
(s+2)-cup or a (t+2)-cap. -/
private theorem cups_caps_planar (s t : ℕ) (X : Finset (ℝ × ℝ)) (hX : PlanarGeneral X)
    (hcard : (s + t).choose s < X.card) :
    (∃ Y ⊆ X, Y.card = s + 2 ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → 0 < orient a b c) ∨
    (∃ Y ⊆ X, Y.card = t + 2 ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → orient a b c < 0) := by
  have key : ∀ (up : Bool) (k : ℕ), HasSeq up X k →
      ∃ Y ⊆ X, Y.card = k ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → turn up a b c := by
    rintro up k ⟨l, hl, hlen⟩
    have hnodup : l.Nodup := by
      apply hl.2.1.imp
      intro a b hab he
      subst b
      exact (lt_irrefl _) hab
    have hsub : l.toFinset ⊆ X := fun p hp => hl.1 p (List.mem_toFinset.1 hp)
    refine ⟨l.toFinset, hsub, (List.toFinset_card_of_nodup hnodup).trans hlen,
      hX.1.mono (Finset.coe_subset.mpr hsub), ?_⟩
    intro a ha b hb c hc hab hbc
    exact turn_of_mem hl (List.mem_toFinset.1 ha) (List.mem_toFinset.1 hb)
      (List.mem_toFinset.1 hc) hab hbc
  by_contra hcon
  rw [not_or] at hcon
  have h1 : ¬ HasSeq true X (s + 2) := fun h => hcon.1 (by
    obtain ⟨Y, hYX, hYc, hYi, hYt⟩ := key true _ h
    exact ⟨Y, hYX, hYc, hYi, fun a ha b hb c hc hab hbc => by
      simpa [turn] using hYt a ha b hb c hc hab hbc⟩)
  have h2 : ¬ HasSeq false X (t + 2) := fun h => hcon.2 (by
    obtain ⟨Y, hYX, hYc, hYi, hYt⟩ := key false _ h
    exact ⟨Y, hYX, hYc, hYi, fun a ha b hb c hc hab hbc => by
      simpa [turn] using hYt a ha b hb c hc hab hbc⟩)
  exact absurd (card_le_binomial s t X hX.1 hX.2 h1 h2) (not_le.mpr hcard)

end CupsCaps

private theorem orient_ne_of_distinct {X : Finset Point} (hX : PlanarGeneral X)
    {a b c : Point} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : orient a b c ≠ 0 := by
  intro he
  have hcab := (orient_cycle c a b).trans he
  have hbca := (orient_cycle a b c).symm.trans he
  have hbac : orient b a c = 0 := by rw [orient_flip b a c, he, neg_zero]
  have hacb : orient a c b = 0 := by rw [orient_swap_last a c b, he, neg_zero]
  have hcba : orient c b a = 0 := by rw [orient_reverse c b a, he, neg_zero]
  have habx : a.1 ≠ b.1 := fun e => hab (hX.1 ha hb e)
  have hbcx : b.1 ≠ c.1 := fun e => hbc (hX.1 hb hc e)
  have hacx : a.1 ≠ c.1 := fun e => hac (hX.1 ha hc e)
  rcases lt_or_gt_of_ne habx with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hbcx with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hacx with h₃ | h₃
  all_goals first
    | exact hX.2 a ha b hb c hc h₁ h₂ he
    | exact hX.2 a ha c hc b hb h₃ h₂ hacb
    | exact hX.2 b hb a ha c hc h₁ h₃ hbac
    | exact hX.2 b hb c hc a ha h₂ h₃ hbca
    | exact hX.2 c hc a ha b hb h₃ h₁ hcab
    | exact hX.2 c hc b hb a ha h₂ h₁ hcba

private theorem projected_fst_injOn {a b : Point} {X : Finset Point} (hab : a ≠ b)
    (hpos : ∀ p ∈ X, 0 < orient a b p)
    (ha : ∀ p ∈ X, ∀ q ∈ X, p ≠ q → orient p q a ≠ 0) :
    Set.InjOn (fun p => (projected a b p).1) (X : Set Point) := by
  intro p hp q hq he
  by_contra hne
  rcases lt_or_gt_of_ne (ha p hp q hq hne) with h | h
  · exact (ne_of_lt ((projected_fst_lt hab (hpos p hp) (hpos q hq)).2 h)) he
  · rw [orient_flip p q a] at h
    exact (ne_of_lt ((projected_fst_lt hab (hpos q hq) (hpos p hp)).2 (neg_pos.mp h))) he.symm

private theorem projected_snd_ne_of_ne {a b p q : Point} (hab : a ≠ b)
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) (h : orient p q b ≠ 0) :
    (projected a b p).2 ≠ (projected a b q).2 := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [orient_flip p q b] at h
    exact (ne_of_lt ((projected_snd_lt hab hq hp).2 (neg_lt_zero.mp h))).symm
  · exact ne_of_lt ((projected_snd_lt hab hp hq).2 h)

private theorem projected_image_general {a b : Point} {X : Finset Point}
    (hab : a ≠ b) (hpos : ∀ p ∈ X, 0 < orient a b p)
    (ha : ∀ p ∈ X, ∀ q ∈ X, p ≠ q → orient p q a ≠ 0)
    (hX : ∀ p ∈ X, ∀ q ∈ X, ∀ r ∈ X, p ≠ q → q ≠ r → p ≠ r → orient p q r ≠ 0) :
    PlanarGeneral (X.image (projected a b)) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq he
    obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := mem_image.mp hq
    exact congrArg _ (projected_fst_injOn hab hpos ha hp₀ hq₀ he)
  · intro p hp q hq r hr hpq hqr he
    obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := mem_image.mp hq
    obtain ⟨r₀, hr₀, rfl⟩ := mem_image.mp hr
    have hn := hX p₀ hp₀ q₀ hq₀ r₀ hr₀
      (fun e => hpq.ne (congrArg (fun p => (projected a b p).1) e))
      (fun e => hqr.ne (congrArg (fun p => (projected a b p).1) e))
      (fun e => (hpq.trans hqr).ne (congrArg (fun p => (projected a b p).1) e))
    have he' := projected_orientation (hpos p₀ hp₀) (hpos q₀ hq₀) (hpos r₀ hr₀)
    rw [he, mul_zero] at he'
    exact (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (anchorNorm_pos hab).ne')) hn) he'.symm

private theorem projected_turn {a b p q r : Point} (hab : a ≠ b)
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) (hr : 0 < orient a b r) :
    (0 < orient (projected a b p) (projected a b q) (projected a b r) ↔ orient p q r < 0) ∧
    (orient (projected a b p) (projected a b q) (projected a b r) < 0 ↔ 0 < orient p q r) := by
  have he := projected_orientation hp hq hr
  have hd : 0 < orient a b p * orient a b q * orient a b r := by positivity
  have hm : 0 < (anchorNorm a b)^2 := pow_pos (anchorNorm_pos hab) _
  constructor
  · rw [← mul_pos_iff_of_pos_left hd, he, neg_mul, neg_pos, mul_comm]
    constructor
    · intro hn
      exact lt_of_not_ge fun hn' => (not_lt_of_ge (mul_nonneg hn' hm.le)) hn
    · exact fun h => mul_neg_of_neg_of_pos h hm
  · have fac (x y : ℝ) (hx : 0 < x) : x * y < 0 ↔ y < 0 := by
      exact ⟨fun h => lt_of_not_ge fun h' => (not_lt_of_ge (mul_nonneg hx.le h')) h,
        mul_neg_of_pos_of_neg hx⟩
    rw [← fac _ _ hd, he, neg_mul, neg_lt_zero, mul_pos_iff_of_pos_left hm]

private theorem orient_angular_interval {a p u v r : Point}
    (huv : orient a u v < 0) (hup : orient a u p < 0) (hpv : orient a p v < 0) :
    (orient a u r < 0 → orient a v r < 0 → orient a p r < 0) ∧
    (0 < orient a u r → 0 < orient a v r → 0 < orient a p r) := by
  have he : orient a u v * orient a p r =
      orient a p v * orient a u r + orient a u p * orient a v r := by
    unfold orient
    ring
  constructor
  · intro hur hvr
    have h := add_pos (mul_pos_of_neg_of_neg hpv hur) (mul_pos_of_neg_of_neg hup hvr)
    rw [← he] at h
    exact lt_of_not_ge fun hh => (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg huv.le hh)) h
  · intro hur hvr
    have h := add_neg (mul_neg_of_neg_of_pos hpv hur) (mul_neg_of_neg_of_pos hup hvr)
    rw [← he] at h
    exact lt_of_not_ge fun hh => (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos huv.le hh)) h

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

private theorem convex_of_clockwise_blocks {X : Finset Point}
    {tag : Point → ℕ} {key : Point → ℝ}
    (hinj : Set.InjOn (fun p => toLex (tag p, key p)) (X : Set Point))
    (hone : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, tag a = tag b → tag b = tag c →
      key a < key b → key b < key c → orient a b c < 0)
    (htwo : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, tag a = tag b → tag a ≠ tag c →
      key a < key b → orient a b c < 0)
    (hthree : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, tag a < tag b → tag b < tag c →
      orient a b c < 0) :
    PlanarConvex X := by
  refine convex_of_clockwise hinj (fun a ha b hb c hc hab hbc => ?_)
  obtain ⟨hab, hkab⟩ := Prod.Lex.toLex_lt_toLex'.mp hab
  obtain ⟨hbc, hkbc⟩ := Prod.Lex.toLex_lt_toLex'.mp hbc
  rcases hab.eq_or_lt with hab | hab <;> rcases hbc.eq_or_lt with hbc | hbc
  · exact hone a ha b hb c hc hab hbc (hkab hab) (hkbc hbc)
  · exact htwo a ha b hb c hc hab ((hab.le.trans_lt hbc).ne) (hkab hab)
  · rw [orient_cycle]
    exact htwo b hb c hc a ha hbc hab.ne' (hkbc hbc)
  · exact hthree a ha b hb c hc hab hbc

private theorem convex_of_clockwise_union {B C : Finset Point} (hdisj : Disjoint B C)
    {keyB keyC : Point → ℝ}
    (hBi : Set.InjOn keyB (B : Set Point)) (hCi : Set.InjOn keyC (C : Set Point))
    (hB : ∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ B, keyB p < keyB q → keyB q < keyB r →
      orient p q r < 0)
    (hC : ∀ p ∈ C, ∀ q ∈ C, ∀ r ∈ C, keyC p < keyC q → keyC q < keyC r →
      orient p q r < 0)
    (hBC : ∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ C, keyB p < keyB q → orient p q r < 0)
    (hCB : ∀ p ∈ C, ∀ q ∈ C, ∀ r ∈ B, keyC p < keyC q → orient p q r < 0) :
    PlanarConvex (B ∪ C) := by
  classical
  let tag (p : Point) : ℕ := if p ∈ B then 0 else 1
  let key (p : Point) : ℝ := if p ∈ B then keyB p else keyC p
  have hzero {p : Point} (hp : p ∈ B) : tag p = 0 ∧ key p = keyB p := by simp [tag, key, hp]
  have hone {p : Point} (hp : p ∈ C) : tag p = 1 ∧ key p = keyC p := by
    have hnot : p ∉ B := fun h => Finset.disjoint_left.mp hdisj h hp
    simp [tag, key, hnot]
  have hcase (p : Point) (hp : p ∈ B ∪ C) :
      (p ∈ B ∧ tag p = 0 ∧ key p = keyB p) ∨
      (p ∈ C ∧ tag p = 1 ∧ key p = keyC p) := by
    rcases mem_union.mp hp with hp | hp
    · exact Or.inl ⟨hp, hzero hp⟩
    · exact Or.inr ⟨hp, hone hp⟩
  refine convex_of_clockwise_blocks (tag := tag) (key := key) ?_ ?_ ?_ ?_
  · intro p hp q hq he
    have he' := congrArg ofLex he
    have ht : tag p = tag q := congrArg Prod.fst he'
    have hk : key p = key q := congrArg Prod.snd he'
    rcases hcase p hp with ⟨hp, htp, hkp⟩ | ⟨hp, htp, hkp⟩ <;>
      rcases hcase q hq with ⟨hq, htq, hkq⟩ | ⟨hq, htq, hkq⟩ <;>
      rw [htp, htq] at ht <;> try contradiction
    · exact hBi hp hq (by simpa [hkp, hkq] using hk)
    · exact hCi hp hq (by simpa [hkp, hkq] using hk)
  · intro a ha b hb c hc hab hbc hka hkb
    rcases hcase a ha with ⟨ha, hta, hxa⟩ | ⟨ha, hta, hxa⟩ <;>
      rcases hcase b hb with ⟨hb, htb, hxb⟩ | ⟨hb, htb, hxb⟩ <;>
      rcases hcase c hc with ⟨hc, htc, hxc⟩ | ⟨hc, htc, hxc⟩ <;>
      rw [hta, htb] at hab <;> rw [htb, htc] at hbc <;> try contradiction
    · exact hB a ha b hb c hc (by simpa [hxa, hxb] using hka) (by simpa [hxb, hxc] using hkb)
    · exact hC a ha b hb c hc (by simpa [hxa, hxb] using hka) (by simpa [hxb, hxc] using hkb)
  · intro a ha b hb c hc hab hac hk
    rcases hcase a ha with ⟨ha, hta, hxa⟩ | ⟨ha, hta, hxa⟩ <;>
      rcases hcase b hb with ⟨hb, htb, hxb⟩ | ⟨hb, htb, hxb⟩ <;>
      rcases hcase c hc with ⟨hc, htc, hxc⟩ | ⟨hc, htc, hxc⟩ <;>
      rw [hta, htb] at hab <;> rw [hta, htc] at hac <;> try contradiction
    · exact hBC a ha b hb c hc (by simpa [hxa, hxb] using hk)
    · exact hCB a ha b hb c hc (by simpa [hxa, hxb] using hk)
  · intro a ha b hb c hc hab hbc
    rcases hcase a ha with ⟨_, hta, _⟩ | ⟨_, hta, _⟩ <;>
      rcases hcase b hb with ⟨_, htb, _⟩ | ⟨_, htb, _⟩ <;>
      rcases hcase c hc with ⟨_, htc, _⟩ | ⟨_, htc, _⟩ <;>
      rw [hta, htb] at hab <;> rw [htb, htc] at hbc <;> omega

private structure Pocket (a b : Point) (B : Finset Point) : Prop where
  distinct : a ≠ b
  side : ∀ p ∈ B, 0 < orient a b p
  first : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → orient p q a ≠ 0
  second : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → orient p q b ≠ 0
  triples : ∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ B, p ≠ q → q ≠ r → p ≠ r → orient p q r ≠ 0

private theorem Pocket.mono {a b : Point} {B C : Finset Point}
    (hB : Pocket a b B) (hCB : C ⊆ B) : Pocket a b C :=
  ⟨hB.distinct, fun p hp => hB.side p (hCB hp),
    fun p hp q hq => hB.first p (hCB hp) q (hCB hq),
    fun p hp q hq => hB.second p (hCB hp) q (hCB hq),
    fun p hp q hq r hr => hB.triples p (hCB hp) q (hCB hq) r (hCB hr)⟩

private theorem pocket_of_general {a b : Point} {B X : Finset Point}
    (hX : PlanarGeneral X) (hBX : B ⊆ X) (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (hside : ∀ p ∈ B, 0 < orient a b p) : Pocket a b B := by
  have hne {p : Point} (hp : p ∈ B) : p ≠ a ∧ p ≠ b := by
    constructor <;> rintro rfl <;> have ht := hside _ hp <;> unfold orient at ht <;> nlinarith only [ht]
  exact ⟨hab, hside,
    fun p hp q hq hpq => orient_ne_of_distinct hX (hBX hp) (hBX hq) ha hpq
      (hne hq).1 (hne hp).1,
    fun p hp q hq hpq => orient_ne_of_distinct hX (hBX hp) (hBX hq) hb hpq
      (hne hq).2 (hne hp).2,
    fun p hp q hq r hr => orient_ne_of_distinct hX (hBX hp) (hBX hq) (hBX hr)⟩

private noncomputable def pocketKey (a b p : Point) : ℝ :=
  (projected a b p).1

private theorem Pocket.inj {a b : Point} {B : Finset Point} (h : Pocket a b B) :
    Set.InjOn (pocketKey a b) (B : Set Point) :=
  projected_fst_injOn h.distinct h.side h.first

private def PocketTurns (a b : Point) (up : Bool) (B : Finset Point) : Prop :=
  ∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ B, pocketKey a b p < pocketKey a b q →
    pocketKey a b q < pocketKey a b r → turn up p q r

private def PocketMonotone (a b : Point) (B : Finset Point) : Prop :=
  ∀ p ∈ B, ∀ q ∈ B, pocketKey a b p < pocketKey a b q →
    (projected a b p).2 < (projected a b q).2

private def PocketAntitone (a b : Point) (B : Finset Point) : Prop :=
  ∀ p ∈ B, ∀ q ∈ B, pocketKey a b p < pocketKey a b q →
    (projected a b q).2 < (projected a b p).2

private theorem pocket_chain_or_outward {a b : Point} {B : Finset Point} {h w : ℕ}
    (hB : Pocket a b B) (hh : 0 < h) (hcard : h * w < B.card) :
    (∃ C ⊆ B, h ≤ C.card ∧ PocketMonotone a b C) ∨
      ∃ C ⊆ B, w < C.card ∧ PocketAntitone a b C := by
  let R (p q : Point) := pocketKey a b p < pocketKey a b q ∧
    (projected a b p).2 < (projected a b q).2
  obtain hchain | hanti := chain_or_antichain B R
    (fun p h => (lt_irrefl _) h.1)
    (fun hpq hqr => ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩) hh hcard
  · obtain ⟨C, hCB, hc, hC⟩ := hchain
    refine Or.inl ⟨C, hCB, hc, fun p hp q hq hpq => ?_⟩
    rcases hC hp hq (fun e => hpq.ne (congrArg (pocketKey a b) e)) with hr | hr
    · exact hr.2
    · exact (hpq.not_gt hr.1).elim
  · obtain ⟨C, hCB, hc, hC⟩ := hanti
    refine Or.inr ⟨C, hCB, hc, fun p hp q hq hpq => ?_⟩
    have hne : p ≠ q := fun e => hpq.ne (congrArg (pocketKey a b) e)
    have hp' := hCB hp
    have hq' := hCB hq
    rcases lt_or_gt_of_ne (projected_snd_ne_of_ne hB.distinct (hB.side p hp')
      (hB.side q hq') (hB.second p hp' q hq' hne)) with hr | hr
    · exact (hC hp hq hne ⟨hpq, hr⟩).elim
    · exact hr

private theorem pocket_convex {a b : Point} {B : Finset Point} {up : Bool}
    (hB : Pocket a b B) (hturn : PocketTurns a b up B) : PlanarConvex B := by
  cases up
  · exact convex_of_clockwise hB.inj hturn
  · refine convex_of_clockwise (key := fun p => -pocketKey a b p)
      (fun p hp q hq h => hB.inj hp hq (neg_injective h)) ?_
    intro p hp q hq r hr hpq hqr
    rw [orient_reverse p q r, neg_lt_zero]
    exact hturn r hr q hq p hp (neg_lt_neg_iff.mp hqr) (neg_lt_neg_iff.mp hpq)

private theorem pocket_cups_caps {a b : Point} {B : Finset Point}
    (hB : Pocket a b B) (s t : ℕ) (hcard : (s + t).choose s < B.card) :
    (∃ C ⊆ B, C.card = s + 2 ∧ PocketTurns a b false C) ∨
      (∃ C ⊆ B, C.card = t + 2 ∧ PocketTurns a b true C) := by
  classical
  let f := projected a b
  have hfi : Set.InjOn f (B : Set Point) :=
    fun _ hp _ hq h => hB.inj hp hq (congrArg Prod.fst h)
  have hg : PlanarGeneral (B.image f) :=
    projected_image_general hB.distinct hB.side hB.first hB.triples
  have hcard' : (s + t).choose s < (B.image f).card := by
    rwa [Finset.card_image_of_injOn hfi]
  have liftImage {D : Finset Point} (hD : D ⊆ B.image f) :
      ∃ C ⊆ B, C.card = D.card ∧ ∀ p ∈ C, f p ∈ D := by
    let C := B.filter fun p => f p ∈ D
    have hC : C ⊆ B := filter_subset _ _
    have he : C.image f = D := by
      ext z
      constructor
      · intro hz
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hz
        exact (mem_filter.mp hp).2
      · intro hz
        obtain ⟨p, hp, rfl⟩ := mem_image.mp (hD hz)
        exact mem_image_of_mem f (mem_filter.mpr ⟨hp, hz⟩)
    exact ⟨C, hC, by rw [← he, Finset.card_image_of_injOn (hfi.mono hC)],
      fun p hp => (mem_filter.mp hp).2⟩
  rcases cups_caps_planar s t _ hg hcard' with
    ⟨D, hD, hd, _, hturn⟩ | ⟨D, hD, hd, _, hturn⟩
  · obtain ⟨C, hC, hc, him⟩ := liftImage hD
    refine Or.inl ⟨C, hC, hc.trans hd, fun p hp q hq r hr hpq hqr => ?_⟩
    exact (projected_turn hB.distinct (hB.side p (hC hp)) (hB.side q (hC hq))
      (hB.side r (hC hr))).1.mp (hturn _ (him p hp) _ (him q hq) _ (him r hr) hpq hqr)
  · obtain ⟨C, hC, hc, him⟩ := liftImage hD
    refine Or.inr ⟨C, hC, hc.trans hd, fun p hp q hq r hr hpq hqr => ?_⟩
    exact (projected_turn hB.distinct (hB.side p (hC hp)) (hB.side q (hC hq))
      (hB.side r (hC hr))).2.mp (hturn _ (him p hp) _ (him q hq) _ (him r hr) hpq hqr)

private theorem pocket_large_turn_sum {a b : Point} {B : Finset Point} {m : ℕ}
    (hB : Pocket a b B) (hcard : 2 ^ m < B.card) :
    ∃ C ⊆ B, ∃ D ⊆ B, PocketTurns a b true C ∧ PocketTurns a b false D ∧
      m < C.card + D.card := by
  classical
  have largest (up : Bool) :
      ∃ C ⊆ B, PocketTurns a b up C ∧
        ∀ Y ⊆ B, PocketTurns a b up Y → Y.card ≤ C.card := by
    let F := B.powerset.filter (PocketTurns a b up)
    have hF : F.Nonempty := ⟨∅, by simp [F, PocketTurns]⟩
    obtain ⟨C, hC, hc⟩ := Finset.exists_max_image F Finset.card hF
    exact ⟨C, mem_powerset.mp (mem_filter.mp hC).1, (mem_filter.mp hC).2,
      fun Y hY hy => hc Y (mem_filter.mpr ⟨mem_powerset.mpr hY, hy⟩)⟩
  obtain ⟨C, hC, hc, hmaxC⟩ := largest true
  obtain ⟨D, hD, hd, hmaxD⟩ := largest false
  refine ⟨C, hC, D, hD, hc, hd, lt_of_not_ge fun h => ?_⟩
  let s := D.card - 1
  let t := C.card - 1
  have hst : s + t ≤ m := by dsimp [s, t]; omega
  have hchoose := (Nat.choose_le_two_pow (s + t) s).trans
    (Nat.pow_le_pow_right (by decide) hst)
  rcases pocket_cups_caps hB s t (hchoose.trans_lt hcard) with
    ⟨Y, hY, hy, hturn⟩ | ⟨Y, hY, hy, hturn⟩
  · have hbound := hmaxD Y hY hturn
    dsimp [s] at hy
    omega
  · have hbound := hmaxC Y hY hturn
    dsimp [t] at hy
    omega

private theorem pocket_anchor_first {a b p q : Point} {B : Finset Point}
    (hB : Pocket a b B) (hp : p ∈ B) (hq : q ∈ B)
    (h : pocketKey a b p < pocketKey a b q) : orient p q a < 0 :=
  (projected_fst_lt hB.distinct (hB.side p hp) (hB.side q hq)).mp h

private theorem pocket_anchor_forward {a b p q : Point} {B : Finset Point}
    (hB : Pocket a b B) (hmono : PocketMonotone a b B) (hp : p ∈ B) (hq : q ∈ B)
    (h : pocketKey a b p < pocketKey a b q) : 0 < orient p q b :=
  (projected_snd_lt hB.distinct (hB.side p hp) (hB.side q hq)).mp (hmono p hp q hq h)

private theorem pocket_anchor_outward {a b p q : Point} {B : Finset Point}
    (hB : Pocket a b B) (hanti : PocketAntitone a b B) (hp : p ∈ B) (hq : q ∈ B)
    (h : pocketKey a b p < pocketKey a b q) : orient p q b < 0 := by
  rw [orient_flip p q b, neg_lt_zero]
  exact (projected_snd_lt hB.distinct (hB.side q hq) (hB.side p hp)).mp (hanti p hp q hq h)

/-- A positive-turn chain in a pocket and a negative-turn chain in its clockwise successor
join to form a convex set. The anchor pairs span the adjacent pockets. -/
private theorem consecutive_pocket_chains {a b c d : Point} {B C : Finset Point}
    (hB : Pocket a b B) (hC : Pocket c d C) (hdisj : Disjoint B C)
    (hmB : PocketMonotone a b B) (hmC : PocketMonotone c d C)
    (htB : PocketTurns a b true B) (htC : PocketTurns c d false C)
    (hBC : ∀ p ∈ B, ∀ r ∈ C, 0 < orient p a r ∧ orient p r b < 0)
    (hCB : ∀ p ∈ C, ∀ r ∈ B, orient p c r < 0 ∧ 0 < orient p r d) :
    PlanarConvex (B ∪ C) := by
  refine convex_of_clockwise_union (keyB := fun p => -pocketKey a b p)
    (keyC := pocketKey c d) hdisj (fun p hp q hq he => hB.inj hp hq (neg_injective he))
    hC.inj ?_ htC ?_ ?_
  · intro p hp q hq r hr hpq hqr
    rw [orient_reverse p q r, neg_lt_zero]
    exact htB r hr q hq p hp (neg_lt_neg_iff.mp hqr) (neg_lt_neg_iff.mp hpq)
  · intro p hp q hq r hr hpq
    have hqp := neg_lt_neg_iff.mp hpq
    obtain ⟨h₁, h₂⟩ := hBC q hq r hr
    rw [orient_flip p q r, neg_lt_zero]
    apply orient_pos_of_following (a := a) (b := b) (by rw [orient_cycle q a b]; exact hB.side q hq) h₁ h₂
    · exact pocket_anchor_first hB hq hp hqp
    · exact pocket_anchor_forward hB hmB hq hp hqp
  · intro p hp q hq r hr hpq
    obtain ⟨h₁, h₂⟩ := hCB p hp r hr
    apply orient_lt_of_preceding (a := c) (b := d) (by rw [orient_cycle p c d]; exact hC.side p hp) h₁ h₂
    · exact pocket_anchor_first hC hp hq hpq
    · exact pocket_anchor_forward hC hmC hp hq hpq

/-- Outward-facing caps from separated pockets can be joined in their pocket order. -/
private theorem convex_of_outward_pockets (s : Finset ℕ) (B : ℕ → Finset Point)
    (a b : ℕ → Point)
    (hpocket : ∀ i ∈ s, Pocket (a i) (b i) (B i))
    (hanti : ∀ i ∈ s, PocketAntitone (a i) (b i) (B i))
    (hturn : ∀ i ∈ s, PocketTurns (a i) (b i) false (B i))
    (hsec : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ p ∈ B i, ∀ r ∈ B j, 0 < orient p (a i) r ∧ 0 < orient p r (b i))
    (hthree : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, i < j → j < k →
      ∀ p ∈ B i, ∀ q ∈ B j, ∀ r ∈ B k, orient p q r < 0) :
    PlanarConvex (s.biUnion B) := by
  classical
  have hc (p : Point) (hp : p ∈ s.biUnion B) : ∃ i ∈ s, p ∈ B i := mem_biUnion.mp hp
  let tag (p : Point) := if hp : p ∈ s.biUnion B then (hc p hp).choose else 0
  let key (p : Point) := pocketKey (a (tag p)) (b (tag p)) p
  have htag {p : Point} (hp : p ∈ s.biUnion B) : tag p ∈ s ∧ p ∈ B (tag p) := by
    simpa only [tag, dif_pos hp] using (hc p hp).choose_spec
  refine convex_of_clockwise_blocks (tag := tag) (key := key) ?_ ?_ ?_ ?_
  · intro p hp q hq he
    have ht : tag p = tag q := congrArg (fun w => (ofLex w).1) he
    have hk : key p = key q := congrArg (fun w => (ofLex w).2) he
    exact (hpocket _ (htag hp).1).inj (htag hp).2 (ht ▸ (htag hq).2)
      (by simpa only [key, ← ht] using hk)
  · intro p hp q hq r hr he₁ he₂ hpq hqr
    have her : tag p = tag r := he₁.trans he₂
    apply hturn _ (htag hp).1 p (htag hp).2 q (he₁ ▸ (htag hq).2)
      r (her ▸ (htag hr).2)
    · simpa only [key, ← he₁] using hpq
    · simpa only [key, ← he₁, ← her] using hqr
  · intro p hp q hq r hr he hne hk
    have hh := hpocket _ (htag hp).1
    have hq' : q ∈ B (tag p) := he ▸ (htag hq).2
    have hk' : pocketKey (a (tag p)) (b (tag p)) p < pocketKey (a (tag p)) (b (tag p)) q := by
      simpa only [key, ← he] using hk
    obtain ⟨h₁, h₂⟩ := hsec _ (htag hp).1 _ (htag hr).1 hne p (htag hp).2 r (htag hr).2
    apply orient_lt_of_sector (by rw [orient_cycle p (a (tag p)) (b (tag p))]; exact hh.side p (htag hp).2) h₁ h₂
    · exact pocket_anchor_first hh (htag hp).2 hq' hk'
    · exact pocket_anchor_outward hh (hanti _ (htag hp).1) (htag hp).2 hq' hk'
  · intro p hp q hq r hr hpq hqr
    exact hthree _ (htag hp).1 _ (htag hq).1 _ (htag hr).1 hpq hqr
      p (htag hp).2 q (htag hq).2 r (htag hr).2

private theorem convex_from_chain_run {X : Finset Point} {k d n : ℕ}
    (a b : ℕ → Point) (B : ℕ → Finset Point)
    (hsub : ∀ i ≤ k, B i ⊆ X)
    (hpocket : ∀ i ≤ k, Pocket (a i) (b i) (B i))
    (hmono : ∀ i ≤ k, PocketMonotone (a i) (b i) (B i))
    (hlarge : ∀ i ≤ k, 2 ^ (n + d) < (B i).card)
    (hdisj : ∀ i < k, Disjoint (B i) (B (i + 1)))
    (hforward : ∀ i < k, ∀ p ∈ B i, ∀ r ∈ B (i + 1),
      0 < orient p (a i) r ∧ orient p r (b i) < 0)
    (hback : ∀ i < k, ∀ p ∈ B (i + 1), ∀ r ∈ B i,
      orient p (a (i + 1)) r < 0 ∧ 0 < orient p r (b (i + 1)))
    (hlen : n ≤ k * (d + 1)) :
    ∃ Y ⊆ X, Y.card = n ∧ PlanarConvex Y := by
  classical
  by_contra hn
  have hchoices (i : ℕ) :
      ∃ C D : Finset Point, i ≤ k →
        C ⊆ B i ∧ D ⊆ B i ∧ PocketTurns (a i) (b i) true C ∧
          PocketTurns (a i) (b i) false D ∧ n + d ≤ C.card + D.card := by
    by_cases hi : i ≤ k
    · obtain ⟨C, hC, D, hD, hc, hd, hsum⟩ :=
        pocket_large_turn_sum (hpocket i hi) (hlarge i hi)
      exact ⟨C, D, fun _ => ⟨hC, hD, hc, hd, hsum.le⟩⟩
    · exact ⟨∅, ∅, fun h => (hi h).elim⟩
  choose C D hCD using hchoices
  have hcsmall (i : ℕ) (hi : i ≤ k) : (C i).card < n := by
    obtain ⟨hC, _, hc, _, _⟩ := hCD i hi
    exact lt_of_not_ge fun h => hn
      (exact_convex_size (hC.trans (hsub i hi)) (pocket_convex ((hpocket i hi).mono hC) hc) h)
  have hpairs (i : ℕ) (hi : i < k) : (C i).card + (D (i + 1)).card < n := by
    have hi' : i + 1 ≤ k := by omega
    obtain ⟨hC, _, hc, _, _⟩ := hCD i hi.le
    obtain ⟨_, hD, _, hd, _⟩ := hCD (i + 1) hi'
    have hsep : Disjoint (C i) (D (i + 1)) := (hdisj i hi).mono hC hD
    have hconv := consecutive_pocket_chains
      ((hpocket i hi.le).mono hC) ((hpocket (i + 1) hi').mono hD) hsep
      (fun p hp q hq => hmono i hi.le p (hC hp) q (hC hq))
      (fun p hp q hq => hmono (i + 1) hi' p (hD hp) q (hD hq)) hc hd
      (fun p hp r hr => hforward i hi p (hC hp) r (hD hr))
      (fun p hp r hr => hback i hi p (hD hp) r (hC hr))
    have hsub' : C i ∪ D (i + 1) ⊆ X := union_subset (hC.trans (hsub i hi.le))
      (hD.trans (hsub (i + 1) hi'))
    refine lt_of_not_ge fun h => hn (exact_convex_size hsub' hconv ?_)
    rwa [Finset.card_union_of_disjoint hsep]
  have hgrow := growth_along_blocks (a := fun i => (C i).card) (b := fun i => (D i).card)
    (fun i hi => (hCD i hi).2.2.2.2) hpairs
  have hsmall := hcsmall k le_rfl
  omega

private theorem pocket_outward_or_convex {X B : Finset Point} {a b : Point} {s n : ℕ}
    (hBX : B ⊆ X) (hB : Pocket a b B) (hanti : PocketAntitone a b B)
    (hcard : (s + n).choose s < B.card) :
    (∃ C ⊆ B, C.card = s + 2 ∧ PocketTurns a b false C ∧ PocketAntitone a b C) ∨
      ∃ Y ⊆ X, Y.card = n ∧ PlanarConvex Y := by
  rcases pocket_cups_caps hB s n hcard with ⟨C, hC, hc, ht⟩ | ⟨C, hC, hc, ht⟩
  · exact Or.inl ⟨C, hC, hc, ht, fun p hp q hq => hanti p (hC hp) q (hC hq)⟩
  · exact Or.inr (exact_convex_size (hC.trans hBX) (pocket_convex (hB.mono hC) ht) (by omega))

private theorem convex_from_outward_covers {X : Finset Point} {n : ℕ}
    (s : Finset ℕ) (B : ℕ → Finset Point) (a b : ℕ → Point)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (hsub : ∀ i ∈ s, B i ⊆ X)
    (hpocket : ∀ i ∈ s, Pocket (a i) (b i) (B i))
    (hanti : ∀ i ∈ s, PocketAntitone (a i) (b i) (B i))
    (hturn : ∀ i ∈ s, PocketTurns (a i) (b i) false (B i))
    (hsec : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ p ∈ B i, ∀ r ∈ B j, 0 < orient p (a i) r ∧ 0 < orient p r (b i))
    (hthree : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, i < j → j < k →
      ∀ p ∈ B i, ∀ q ∈ B j, ∀ r ∈ B k, orient p q r < 0)
    (hcard : n ≤ ∑ i ∈ s, (B i).card) :
    ∃ Y ⊆ X, Y.card = n ∧ PlanarConvex Y := by
  classical
  refine exact_convex_size (Y := s.biUnion B) ?_
    (convex_of_outward_pockets s B a b hpocket hanti hturn hsec hthree) ?_
  · intro p hp
    obtain ⟨i, hi, hip⟩ := mem_biUnion.mp hp
    exact hsub i hi hip
  · rwa [Finset.card_biUnion (fun i hi j hj h => hdisj i hi j hj h)]

/-- Evaluate the binomial sum at an auxiliary positive weight to bound one coefficient. -/
private theorem weighted_choose_le_pow (s n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((s + n).choose s : ℝ) * x ^ s ≤ (1 + x) ^ (s + n) := by
  rw [add_comm (1 : ℝ) x, add_pow]
  have h := Finset.single_le_sum
    (f := fun j => x ^ j * (1 : ℝ) ^ (s + n - j) * ((s + n).choose j : ℝ))
    (fun j _ => by positivity) (Finset.mem_range.mpr (show s < s + n + 1 by omega))
  simpa [mul_comm] using h

private theorem sparse_binomial_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℕ, 0 < T ∧ ∀ n : ℕ,
      ((n / T + n).choose (n / T) : ℝ) ≤ (2 : ℝ) ^ (δ * n) := by
  have base : (1 : ℝ) < 2 := by norm_num
  have hbase : (0 : ℝ) < 2 := by norm_num
  let x := min ((2 : ℝ) ^ (δ / 4) - 1) 1
  have hx : 0 < x := lt_min (sub_pos.mpr (Real.one_lt_rpow base (by linarith))) zero_lt_one
  have hupper : 1 + x ≤ (2 : ℝ) ^ (δ / 4) := by
    have h := min_le_left ((2 : ℝ) ^ (δ / 4) - 1) 1
    dsimp [x]
    linarith only [h]
  let y := Real.logb 2 x⁻¹
  obtain ⟨T, hT⟩ := exists_nat_gt (max (y / (δ / 2)) 1)
  have hTpos : 0 < T := by
    have h : (1 : ℝ) < T := (le_max_right _ _).trans_lt hT
    exact_mod_cast (zero_lt_one.trans h)
  have hy : y ≤ (δ / 2) * (T : ℝ) := by
    have h : y / (δ / 2) < (T : ℝ) := (le_max_left _ _).trans_lt hT
    linarith only [(div_lt_iff₀ (show 0 < δ / 2 by linarith)).mp h]
  refine ⟨T, hTpos, fun n => ?_⟩
  let s := n / T
  change ((s + n).choose s : ℝ) ≤ _
  have hs : s ≤ n := Nat.div_le_self _ _
  have hsmul : (s : ℝ) * (T : ℝ) ≤ n := by
    exact_mod_cast (Nat.div_mul_le_self n T)
  have hterm₁ : (1 + x) ^ (s + n) ≤ (2 : ℝ) ^ ((δ / 2) * n) := by
    calc
      (1 + x) ^ (s + n) ≤ ((2 : ℝ) ^ (δ / 4)) ^ (s + n) :=
        pow_le_pow_left₀ (by positivity) hupper _
      _ = (2 : ℝ) ^ ((δ / 4) * (↑(s + n) : ℝ)) :=
        (Real.rpow_mul_natCast hbase.le _ _).symm
      _ ≤ (2 : ℝ) ^ ((δ / 2) * n) := by
        apply Real.rpow_le_rpow_of_exponent_le base.le
        have hs' : (s : ℝ) ≤ n := by exact_mod_cast hs
        push_cast
        nlinarith only [mul_le_mul_of_nonneg_left hs' hδ.le]
  have hterm₂ : (x⁻¹) ^ s ≤ (2 : ℝ) ^ ((δ / 2) * n) := by
    have hxy : (2 : ℝ) ^ y = x⁻¹ :=
      Real.rpow_logb hbase base.ne' (inv_pos.mpr hx)
    rw [← hxy, ← Real.rpow_mul_natCast hbase.le]
    apply Real.rpow_le_rpow_of_exponent_le base.le
    calc
      y * (s : ℝ) ≤ (δ / 2 * (T : ℝ)) * (s : ℝ) :=
        mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg s)
      _ = δ / 2 * ((s : ℝ) * (T : ℝ)) := by ring
      _ ≤ δ / 2 * n := mul_le_mul_of_nonneg_left hsmul (by linarith)
  have hw := weighted_choose_le_pow s n hx.le
  calc
    ((s + n).choose s : ℝ) = (((s + n).choose s : ℝ) * x ^ s) * (x⁻¹) ^ s := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hx.ne', one_pow, mul_one]
    _ ≤ (1 + x) ^ (s + n) * (x⁻¹) ^ s :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ (2 : ℝ) ^ ((δ / 2) * n) * (2 : ℝ) ^ ((δ / 2) * n) :=
      mul_le_mul hterm₁ hterm₂ (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (δ * n) := by rw [← Real.rpow_add hbase]; congr 1; ring

private theorem orient_two_angular_intervals {o l p r l' q r' : Point}
    (hlr : orient o l r < 0) (hlp : orient o l p < 0) (hpr : orient o p r < 0)
    (hlr' : orient o l' r' < 0) (hlq' : orient o l' q < 0) (hqr' : orient o q r' < 0)
    (hll' : orient o l l' < 0) (hlr'' : orient o l r' < 0)
    (hrl' : orient o r l' < 0) (hrr' : orient o r r' < 0) :
    orient o p q < 0 := by
  have hp₁ := (orient_angular_interval hlr hlp hpr).1 hll' hrl'
  have hp₂ := (orient_angular_interval hlr hlp hpr).1 hlr'' hrr'
  rw [orient_swap_last o p l', neg_lt_zero] at hp₁
  rw [orient_swap_last o p r', neg_lt_zero] at hp₂
  have h := (orient_angular_interval hlr' hlq' hqr').2 hp₁ hp₂
  rw [orient_swap_last o q p, neg_pos] at h
  exact h

private structure PocketLayout (X : Finset Point) (k : ℕ) where
  left : ℕ → Point
  right : ℕ → Point
  part : ℕ → Finset Point
  subset : ∀ i < k, part i ⊆ X
  pocket : ∀ i < k, Pocket (left i) (right i) (part i)
  disjoint : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (part i) (part j)
  following : ∀ i, i + 1 < k → ∀ p ∈ part i, ∀ r ∈ part (i + 1),
    0 < orient p (left i) r ∧ orient p r (right i) < 0
  preceding : ∀ i, i + 1 < k → ∀ p ∈ part (i + 1), ∀ r ∈ part i,
    orient p (left (i + 1)) r < 0 ∧ 0 < orient p r (right (i + 1))
  sector : ∀ i < k, ∀ j < k, (i + 1 < j ∨ j + 1 < i) →
    ∀ p ∈ part i, ∀ r ∈ part j, 0 < orient p (left i) r ∧ 0 < orient p r (right i)
  clockwise : ∀ i j l, i < j → j < l → l < k →
    ∀ p ∈ part i, ∀ q ∈ part j, ∀ r ∈ part l, orient p q r < 0

/-- A block of consecutive chain pockets forces a join. In the other case, choose an
outward cap from each block, leaving one unused pocket between blocks. -/
private theorem convex_of_large_layout {X : Finset Point} {T R s n d : ℕ}
    (P : PocketLayout X (T * (R + 2))) (hr : n ≤ R * (d + 1))
    (ht : n ≤ T * (s + 2))
    (hbig : ∀ i < T * (R + 2), (2 ^ (n + d) + 1) * (s + n).choose s < (P.part i).card) :
    ∃ Y ⊆ X, Y.card = n ∧ PlanarConvex Y := by
  classical
  by_contra hn
  let M (i : ℕ) := ∃ B ⊆ P.part i, 2 ^ (n + d) < B.card ∧ PocketMonotone (P.left i) (P.right i) B
  let A (i : ℕ) := ∃ B ⊆ P.part i, B.card = s + 2 ∧
    PocketTurns (P.left i) (P.right i) false B ∧ PocketAntitone (P.left i) (P.right i) B
  let base (j : ℕ) := j * (R + 2)
  have hidx {j i : ℕ} (hj : j < T) (hi : i ≤ R) : base j + i < T * (R + 2) := by
    have h := Nat.mul_le_mul_right (R + 2) (show j + 1 ≤ T by omega)
    rw [Nat.add_mul, one_mul] at h
    change j * (R + 2) + i < _
    omega
  have hlocal (i : ℕ) (hi : i < T * (R + 2)) : M i ∨ A i := by
    rcases pocket_chain_or_outward (P.pocket i hi) (Nat.succ_pos (2 ^ (n + d)))
      (hbig i hi) with h | ⟨B, hB, hc, hm⟩
    · obtain ⟨B, hB, hc, hm⟩ := h
      exact Or.inl ⟨B, hB, by omega, hm⟩
    · rcases pocket_outward_or_convex (hB.trans (P.subset i hi)) ((P.pocket i hi).mono hB) hm hc
        with ⟨C, hC, hcc, hct, hca⟩ | h
      · exact Or.inr ⟨C, hC.trans hB, hcc, hct, hca⟩
      · exact (hn h).elim
  have runImpossible (j : ℕ) (hj : j < T) : ¬ ∀ i ≤ R, M (base j + i) := by
    intro hall
    have hx (i : ℕ) : ∃ B : Finset Point, i ≤ R →
        B ⊆ P.part (base j + i) ∧ 2 ^ (n + d) < B.card ∧
          PocketMonotone (P.left (base j + i)) (P.right (base j + i)) B := by
      by_cases hi : i ≤ R
      · obtain ⟨B, hB, hc, hm⟩ := hall i hi
        exact ⟨B, fun _ => ⟨hB, hc, hm⟩⟩
      · exact ⟨∅, fun h => (hi h).elim⟩
    choose B hB using hx
    apply hn
    refine convex_from_chain_run (fun i => P.left (base j + i)) (fun i => P.right (base j + i))
      B (fun i hi => (hB i hi).1.trans (P.subset _ (hidx hj hi)))
      (fun i hi => (P.pocket _ (hidx hj hi)).mono (hB i hi).1)
      (fun i hi => (hB i hi).2.2) (fun i hi => (hB i hi).2.1) ?_ ?_ ?_ hr
    · intro i hi
      exact (P.disjoint _ (hidx hj hi.le) _ (hidx hj (show i + 1 ≤ R by omega))
        (by omega)).mono (hB i hi.le).1 (hB (i + 1) (by omega)).1
    · intro i hi p hp r hr'
      exact P.following (base j + i) (by simpa only [Nat.add_assoc] using hidx hj (show i + 1 ≤ R by omega)) p ((hB i hi.le).1 hp)
        r ((hB (i + 1) (by omega)).1 hr')
    · intro i hi p hp r hr'
      exact P.preceding (base j + i) (by simpa only [Nat.add_assoc] using hidx hj (show i + 1 ≤ R by omega)) p ((hB (i + 1) (by omega)).1 hp)
        r ((hB i hi.le).1 hr')
  have hchoose (j : ℕ) : ∃ i : ℕ, ∃ B : Finset Point, j < T →
      i ≤ R ∧ B ⊆ P.part (base j + i) ∧ B.card = s + 2 ∧
        PocketTurns (P.left (base j + i)) (P.right (base j + i)) false B ∧
        PocketAntitone (P.left (base j + i)) (P.right (base j + i)) B := by
    by_cases hj : j < T
    · obtain ⟨i, hi, hni⟩ := not_forall.mp (runImpossible j hj) |>.imp fun _ h => Classical.not_imp.mp h
      rcases hlocal _ (hidx hj hi) with hm | ⟨B, hB, hc, ht, ha⟩
      · exact (hni hm).elim
      · exact ⟨i, B, fun _ => ⟨hi, hB, hc, ht, ha⟩⟩
    · exact ⟨0, ∅, fun h => (hj h).elim⟩
  choose offset B hB using hchoose
  let f (i : ℕ) := base i + offset i
  have hf {i : ℕ} (hi : i < T) : f i < T * (R + 2) := hidx hi (hB i hi).1
  have hsep {i j : ℕ} (hi : i < T) (hij : i < j) : f i + 1 < f j := by
    have h := Nat.mul_le_mul_right (R + 2) (show i + 1 ≤ j by omega)
    rw [Nat.add_mul, one_mul] at h
    have hi' := (hB i hi).1
    dsimp [f, base]
    omega
  apply hn
  refine convex_from_outward_covers (range T) B (fun i => P.left (f i))
    (fun i => P.right (f i)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi j hj hne
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have h' : f i ≠ f j := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact (lt_of_le_of_lt (Nat.le_succ _) (hsep hi' h)).ne
      · exact (lt_of_le_of_lt (Nat.le_succ _) (hsep hj' h)).ne'
    exact (P.disjoint _ (hf hi') _ (hf hj') h').mono (hB i hi').2.1 (hB j hj').2.1
  · intro i hi
    have hi' := mem_range.mp hi
    exact (hB i hi').2.1.trans (P.subset _ (hf hi'))
  · intro i hi
    have hi' := mem_range.mp hi
    exact (P.pocket _ (hf hi')).mono (hB i hi').2.1
  · exact fun i hi => (hB i (mem_range.mp hi)).2.2.2.2
  · exact fun i hi => (hB i (mem_range.mp hi)).2.2.2.1
  · intro i hi j hj hne p hp r hr'
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have h : f i + 1 < f j ∨ f j + 1 < f i :=
      (lt_or_gt_of_ne hne).imp (hsep hi') (hsep hj')
    exact P.sector _ (hf hi') _ (hf hj') h p ((hB i hi').2.1 hp) r ((hB j hj').2.1 hr')
  · intro i hi j hj l hl hij hjl p hp q hq r hr'
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have hl' := mem_range.mp hl
    exact P.clockwise _ _ _ (lt_of_le_of_lt (Nat.le_succ _) (hsep hi' hij))
      (lt_of_le_of_lt (Nat.le_succ _) (hsep hj' hjl)) (hf hl')
      p ((hB i hi').2.1 hp) q ((hB j hj').2.1 hq) r ((hB l hl').2.1 hr')
  · calc
      n ≤ T * (s + 2) := ht
      _ = ∑ i ∈ range T, (s + 2) := by simp
      _ = ∑ i ∈ range T, (B i).card :=
        Finset.sum_congr rfl fun i hi => (hB i (mem_range.mp hi)).2.2.1.symm

/-- For a fixed number of pockets, the loss allowed here is a constant factor. -/
private theorem layout_positive_fraction (k : ℕ) :
    ∃ C : ℕ, ∀ (X : Finset Point) (L : ℕ), PlanarGeneral X → C * (L + 1) < X.card →
      ∃ P : PocketLayout X k, ∀ i < k, L < (P.part i).card := by
  sorry

private theorem finite_suk_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ X : Finset Point, PlanarGeneral X →
      (2 : ℝ) ^ ((1 + δ) * n) < (X.card : ℝ) →
      ∃ Y ⊆ X, Y.card = n ∧ PlanarConvex Y := by
  let η := δ / 4
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨T, hT, hbin⟩ := sparse_binomial_bound hη
  obtain ⟨R, hR⟩ := exists_nat_ge (1 / η)
  obtain ⟨C, hC⟩ := layout_positive_fraction (T * (R + 2))
  obtain ⟨K, hK⟩ := exists_nat_ge (((C : ℝ) + 2) / η)
  filter_upwards [eventually_ge_atTop K] with n hn
  intro X hX hx
  let d := ⌊η * (n : ℝ)⌋₊
  let s := n / T
  let L := (2 ^ (n + d) + 1) * (s + n).choose s
  have hηn : 0 ≤ η * (n : ℝ) := by positivity
  have hd : (d : ℝ) ≤ η * n := Nat.floor_le hηn
  have hd' : η * (n : ℝ) < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  have hr : n ≤ R * (d + 1) := by
    have hR' : 1 ≤ (R : ℝ) * η := by linarith only [(div_le_iff₀ hη).mp hR]
    have h₁ := mul_le_mul_of_nonneg_right hR' (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h₂ := mul_le_mul_of_nonneg_left hd'.le (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    have h₃ : (n : ℝ) ≤ (R : ℝ) * ((d : ℝ) + 1) := by nlinarith only [h₁, h₂]
    exact_mod_cast h₃
  have ht : n ≤ T * (s + 2) := by
    have hn' := Nat.mod_add_div n T
    have hm := Nat.mod_lt n hT
    rw [Nat.mul_add]
    change n ≤ T * (n / T) + T * 2
    omega
  have hb : (1 : ℝ) ≤ 2 := by norm_num
  have hpow (m : ℕ) : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ (m : ℝ) := by
    rw [Real.rpow_natCast]
    norm_num
  have hfirst : ((2 ^ (n + d) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((1 + η) * n + 1) := by
    have h₁ : 2 ^ (n + d) + 1 ≤ (2 : ℕ) ^ (n + d + 1) := by
      rw [pow_succ]
      have hp : 0 < (2 : ℕ) ^ (n + d) := by positivity
      omega
    have hh : ((2 ^ (n + d) + 1 : ℕ) : ℝ) ≤ ((2 ^ (n + d + 1) : ℕ) : ℝ) := by
      exact_mod_cast h₁
    refine hh.trans ?_
    rw [hpow]
    apply Real.rpow_le_rpow_of_exponent_le hb
    push_cast
    nlinarith only [hd]
  have hL : (L : ℝ) ≤ (2 : ℝ) ^ ((1 + 2 * η) * n + 1) := by
    dsimp only [L]
    rw [Nat.cast_mul]
    calc
      _ ≤ (2 : ℝ) ^ ((1 + η) * n + 1) * (2 : ℝ) ^ (η * n) :=
        mul_le_mul hfirst (hbin n) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  let e : ℝ := (1 + 2 * η) * n + 1
  have he : 1 ≤ (2 : ℝ) ^ e := Real.one_le_rpow hb (by dsimp [e]; positivity)
  have hplus : (L : ℝ) + 1 ≤ (2 : ℝ) ^ (e + 1) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
    change (L : ℝ) ≤ 2 ^ e at hL
    linarith only [hL, he]
  have hconst : (C : ℝ) ≤ (2 : ℝ) ^ (C : ℝ) := by
    rw [← hpow]
    exact_mod_cast Nat.lt_two_pow_self.le
  have hlarge : C * (L + 1) < X.card := by
    have hc₁ : (K : ℝ) ≤ n := by exact_mod_cast hn
    have hc₂ : (C : ℝ) + 2 ≤ η * (n : ℝ) := by
      linarith only [(div_le_iff₀ hη).mp (hK.trans hc₁)]
    have hcalc : (C : ℝ) * ((L : ℝ) + 1) < (X.card : ℝ) := by
      calc
        _ ≤ (2 : ℝ) ^ (C : ℝ) * (2 : ℝ) ^ (e + 1) :=
          mul_le_mul hconst hplus (by positivity) (by positivity)
        _ = (2 : ℝ) ^ ((C : ℝ) + (e + 1)) := (Real.rpow_add (by norm_num) _ _).symm
        _ ≤ (2 : ℝ) ^ ((1 + δ) * n) := by
          apply Real.rpow_le_rpow_of_exponent_le hb
          have hδeq : δ = 4 * η := by dsimp [η]; ring
          rw [hδeq]
          dsimp [e]
          nlinarith only [hc₂, hηn]
        _ < _ := hx
    exact_mod_cast hcalc
  obtain ⟨P, hP⟩ := hC X L hX hlarge
  exact convex_of_large_layout P hr ht hP

end SukOdd

theorem OMA.solution : OMA.R_Erdos107_variants_su_bound_R1.H2 := by
  intro ε hε _
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨K, hK⟩ := exists_nat_ge (1 / δ)
  filter_upwards [SukOdd.finite_suk_bound δ hδ, eventually_ge_atTop K] with n hfinite hn
  intro _
  let x := (2 : ℝ) ^ ((1 + δ) * n)
  have hx : 1 ≤ x := Real.one_le_rpow (by norm_num) (by positivity)
  have hkn : (K : ℝ) ≤ n := by exact_mod_cast hn
  have hδn : 1 ≤ δ * (n : ℝ) := by
    have h := (div_le_iff₀ hδ).mp (hK.trans hkn)
    linarith
  refine ⟨⌊x⌋₊ + 1, ?_, fun X hX hi hg => ?_⟩
  · rw [Nat.cast_add, Nat.cast_one]
    calc
      (⌊x⌋₊ : ℝ) + 1 ≤ x + 1 :=
        add_le_add_left (Nat.floor_le (zero_le_one.trans hx)) 1
      _ ≤ x * 2 := by linarith
      _ = (2 : ℝ) ^ ((1 + δ) * n + 1) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
      _ ≤ (2 : ℝ) ^ ((1 + ε) * n) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        dsimp [δ] at hδn ⊢
        linarith only [hδn]
  · apply hfinite X ⟨hi, hg⟩
    rw [hX, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one x
