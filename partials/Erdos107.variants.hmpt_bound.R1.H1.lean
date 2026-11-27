import OMAReductions.R_Erdos107_variants_hmpt_bound_R1
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds

-- Step Erdos107.variants.hmpt_bound.R1.H1: hypothesis H1 of reduction Erdos107.variants.hmpt_bound.R1
-- Credit: @<handle>
-- H1 := ∃ A : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ X : Finset (EuclideanSpace ℝ (Fin 2)),     (∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, x ≠ y → y ≠ z → x ≠ z →       ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) →     2 ^ (A * k) ≤ X.card →     ∃ T : Fin k → Finset (EuclideanSpace ℝ (Fin 2)),       (∀ i, T i ⊆ X) ∧ (∀ i, X.card ≤ 2 ^ (A * k) * (T i).card) ∧       ∀ g : Fin k → EuclideanSpace ℝ (Fin 2), (∀ i, g i ∈ T i) →         Function.Injective g ∧ ∀ a ∈ Set.range g, a ∉ convexHull ℝ (Set.range g \ {a})  /-- The Holmsen–Mojarrad–Pach–Tardos step inside a positive-fraction configuration. -/

open Finset

namespace OMA.E107H1


lemma small_convex (k : ℕ) (hk : k ≤ 3) (X : Finset (EuclideanSpace ℝ (Fin 2)))
    (hX : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2))))
    (g : Fin k → (EuclideanSpace ℝ (Fin 2))) (hg : ∀ i, g i ∈ X) (hinj : Function.Injective g) :
    ∀ a ∈ Set.range g, a ∉ convexHull ℝ (Set.range g \ {a}) := by
  rintro a ⟨i, rfl⟩ hmem
  interval_cases k
  · exact i.elim0
  · have hsub : Set.range g \ {g i} ⊆ ∅ := by
      rintro x ⟨⟨m, rfl⟩, hne⟩
      exact hne (congrArg g (Subsingleton.elim m i))
    have := convexHull_mono hsub hmem
    simp at this
  · have hsub : Set.range g \ {g i} ⊆ {g (1 - i)} := by
      rintro x ⟨⟨m, rfl⟩, hne⟩
      fin_cases i <;> fin_cases m <;> simp_all
    have := convexHull_mono hsub hmem
    rw [convexHull_singleton] at this
    have h2 := hinj this
    fin_cases i <;> simp at h2
  · obtain ⟨j, l, hj, hl, hjl, hsub⟩ : ∃ j l : Fin 3, j ≠ i ∧ l ≠ i ∧ j ≠ l ∧
        Set.range g \ {g i} ⊆ {g j, g l} := by
      fin_cases i
      · refine ⟨1, 2, by decide, by decide, by decide, ?_⟩
        rintro x ⟨⟨m, rfl⟩, hne⟩
        fin_cases m <;> simp_all
      · refine ⟨0, 2, by decide, by decide, by decide, ?_⟩
        rintro x ⟨⟨m, rfl⟩, hne⟩
        fin_cases m <;> simp_all
      · refine ⟨0, 1, by decide, by decide, by decide, ?_⟩
        rintro x ⟨⟨m, rfl⟩, hne⟩
        fin_cases m <;> simp_all
    have := convexHull_mono hsub hmem
    rw [convexHull_pair, mem_segment_iff_wbtw] at this
    have hc := this.collinear
    have hne1 : g j ≠ g i := fun h => hj (hinj h)
    have hne2 : g i ≠ g l := fun h => hl (hinj h).symm
    have hne3 : g j ≠ g l := fun h => hjl (hinj h)
    exact hX _ (hg j) _ (hg i) _ (hg l) hne1 hne2 hne3 hc

/-- residue-class partition into k large pieces. -/
lemma partition (k : ℕ) (hk : 1 ≤ k) (X : Finset (EuclideanSpace ℝ (Fin 2))) (hkX : k ≤ X.card) :
    ∃ T : Fin k → Finset (EuclideanSpace ℝ (Fin 2)), (∀ i, T i ⊆ X) ∧ (∀ i, X.card ≤ 2 * k * (T i).card) ∧
      ∀ g : Fin k → (EuclideanSpace ℝ (Fin 2)), (∀ i, g i ∈ T i) → Function.Injective g := by
  classical
  set n := X.card with hn
  let f : ℕ → (EuclideanSpace ℝ (Fin 2)) := fun m => if h : m < n then (X.equivFin.symm ⟨m, h⟩ : (EuclideanSpace ℝ (Fin 2))) else 0
  have hfX : ∀ m < n, f m ∈ X := by
    intro m hm
    simp only [f, dif_pos hm]
    exact (X.equivFin.symm ⟨m, hm⟩).2
  have hfinj : ∀ m < n, ∀ m' < n, f m = f m' → m = m' := by
    intro m hm m' hm' h
    simp only [f, dif_pos hm, dif_pos hm'] at h
    have := X.equivFin.symm.injective (Subtype.ext h)
    simpa using this
  have hidx : ∀ (i : Fin k), ∀ m < n / k, m * k + i < n := by
    intro i m hm
    have h1 : m * k + k ≤ n / k * k := by
      have : (m + 1) * k ≤ n / k * k := Nat.mul_le_mul_right _ hm
      linarith [this]
    have h2 : n / k * k ≤ n := Nat.div_mul_le_self n k
    omega
  refine ⟨fun i => (range (n / k)).image (fun m => f (m * k + i)), ?_, ?_, ?_⟩
  · intro i x hx
    simp only [mem_image, mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact hfX _ (hidx i m hm)
  · intro i
    rw [card_image_of_injOn]
    · rw [card_range]
      have h1 : 1 ≤ n / k := (Nat.one_le_div_iff (by omega)).2 hkX
      have h2 := Nat.div_add_mod n k
      have h3 := Nat.mod_lt n (show k > 0 by omega)
      nlinarith
    · intro m hm m' hm' h
      simp only [coe_range, Set.mem_Iio] at hm hm'
      have := hfinj _ (hidx i m hm) _ (hidx i m' hm') h
      have hk0 : 0 < k := by omega
      have : m * k = m' * k := by omega
      exact Nat.eq_of_mul_eq_mul_right hk0 this
  · intro g hg i j hij
    have hi := hg i
    have hj := hg j
    simp only [mem_image, mem_range] at hi hj
    obtain ⟨m, hm, hmi⟩ := hi
    obtain ⟨m', hm', hmj⟩ := hj
    have := hfinj _ (hidx i m hm) _ (hidx j m' hm') (hmi.trans (hij.trans hmj.symm))
    have h1 : (m * k + i) % k = (m' * k + j) % k := by rw [this]
    rw [Nat.mul_comm m, Nat.mul_comm m', Nat.mul_add_mod, Nat.mul_add_mod,
      Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at h1
    exact Fin.ext h1



section Own
open scoped Classical

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

private abbrev Point := ℝ × ℝ

private def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

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

private theorem finite_image_pullback {α β : Type*} [DecidableEq β] (L : α → β)
    (X : Finset α) (Z : Finset β) (hZ : Z ⊆ X.image L) (hL : Set.InjOn L (X : Set α)) :
    ∃ Y ⊆ X, Y.image L = Z ∧ Y.card = Z.card := by
  classical
  let Y := X.filter fun y => L y ∈ Z
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image L = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hy).2
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hZ hz)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hz⟩, rfl⟩
  refine ⟨Y, hYX, hYZ, ?_⟩
  rw [← hYZ, Finset.card_image_of_injOn (hL.mono hYX)]

private theorem planar_coordinates (X : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ x y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ,
      Set.InjOn x (X : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  classical
  let bad := (X ×ˢ X).image fun uv : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ :=
    EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : EuclideanSpace ℝ (Fin 2)) (hx : x p = x q) (hy : y p = y q) : p = q := by
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 = q 1 at hy
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      rw [hy] at hx
      exact add_right_cancel hx
    · exact hy
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq hx
  by_cases hy : y p = y q
  · exact hjoint p q hx hy
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 ≠ q 1 at hy
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    nlinarith only [hx]

end Own

/-- The genuine Por-Valtr positive-fraction Erdos-Szekeres theorem for k at least 4 (open gap). -/
lemma core_large : ∃ A : ℕ, ∀ k : ℕ, 4 ≤ k → ∀ X : Finset (EuclideanSpace ℝ (Fin 2)),
    (∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) →
    2 ^ (A * k) ≤ X.card →
    ∃ T : Fin k → Finset (EuclideanSpace ℝ (Fin 2)),
      (∀ i, T i ⊆ X) ∧ (∀ i, X.card ≤ 2 ^ (A * k) * (T i).card) ∧
      ∀ g : Fin k → (EuclideanSpace ℝ (Fin 2)), (∀ i, g i ∈ T i) →
        Function.Injective g ∧ ∀ a ∈ Set.range g, a ∉ convexHull ℝ (Set.range g \ {a}) := by
  sorry

end OMA.E107H1

theorem OMA.solution : OMA.R_Erdos107_variants_hmpt_bound_R1.H1 := by
  obtain ⟨A, hA⟩ := OMA.E107H1.core_large
  refine ⟨max A 1, ?_⟩
  intro k hk X hX hcard
  have hpow : 2 ^ (A * k) ≤ 2 ^ (max A 1 * k) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (le_max_left _ _))
  by_cases hk4 : 4 ≤ k
  · obtain ⟨T, h1, h2, h3⟩ := hA k hk4 X hX (hpow.trans hcard)
    exact ⟨T, h1, fun i => (h2 i).trans (Nat.mul_le_mul_right _ hpow), h3⟩
  · have hk3 : k ≤ 3 := by omega
    have h2k : 2 * k ≤ 2 ^ (max A 1 * k) := by
      have : 2 ^ k ≤ 2 ^ (max A 1 * k) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
      have : 2 * k ≤ 2 ^ k := by interval_cases k <;> norm_num
      omega
    have hkX : k ≤ X.card := by omega
    obtain ⟨T, h1, h2, h3⟩ := OMA.E107H1.partition k hk X hkX
    refine ⟨T, h1, fun i => (h2 i).trans (Nat.mul_le_mul_right _ h2k), fun g hg => ?_⟩
    have hinj := h3 g hg
    exact ⟨hinj, OMA.E107H1.small_convex k hk3 X hX g (fun i => h1 i (hg i)) hinj⟩
