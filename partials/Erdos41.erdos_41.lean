import FormalConjectures.ErdosProblems.«41»

-- Problem: Erdős Problem 41
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/41.lean:55 (declaration Erdos41.erdos_41)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
The remaining case is an infinite set with unique triple sums and an enumeration
of eventual cubic upper growth. Such a set would also obey the short-pair bounds below.
-/

namespace Erdos41Relay

open Filter Set

private lemma signed_triples_eq {A : Set ℕ} (hA : Erdos41.NtupleCondition A 3)
    {a b x y u v : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hx : x ∈ A) (hy : y ∈ A) (hu : u ∈ A) (hv : v ∈ A)
    (hya : y ≠ a) (hyx : y ≠ x) (hau : a ≠ u)
    (hs : (a : ℤ) + x - y = b + u - v) : a = b ∧ x = u ∧ y = v := by
  let P : Multiset ℕ := v ::ₘ a ::ₘ {x}
  let Q : Multiset ℕ := y ::ₘ b ::ₘ {u}
  have hpq : P = Q := hA P Q (by
    intro z hz
    simp only [P, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption) (by
    intro z hz
    simp only [Q, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption) (by simp [P]) (by simp [Q]) (by
    simp [P, Q]
    omega)
  have hyP : y ∈ P := by rw [hpq]; simp [Q]
  have hyv : y = v := by
    simp only [P, Multiset.mem_cons, Multiset.mem_singleton] at hyP
    exact hyP.resolve_right (not_or_intro hya hyx)
  subst v
  have hpair : (a ::ₘ {x} : Multiset ℕ) = b ::ₘ {u} :=
    (Multiset.cons_inj_right y).mp hpq
  have ha' : a = b := by
    have hm : a ∈ (b ::ₘ {u} : Multiset ℕ) := hpair ▸ Multiset.mem_cons_self _ _
    exact (Multiset.mem_cons.mp hm).resolve_right (by simpa using hau)
  subst b
  exact ⟨rfl, by simpa using (Multiset.cons_inj_right a).mp hpair, rfl⟩

/-- Each short ordered difference can be translated by each element of a disjoint
anchor set, with all the resulting signed sums distinct. -/
private lemma closePair_capacity {A : Set ℕ} (hA : Erdos41.NtupleCondition A 3)
    (L H : ℕ) (U : Finset ℕ) (D : Finset (ℕ × ℕ))
    (hU : ∀ a ∈ U, a ∈ A ∧ L ≤ a ∧ a ≤ L + H)
    (hD : ∀ p ∈ D, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ∉ U ∧ p.2 ∉ U ∧ p.1 ≠ p.2 ∧
      p.1 ≤ p.2 + H ∧ p.2 ≤ p.1 + H) :
    U.card * D.card ≤ 3 * H + 1 := by
  let s (q : ℕ × ℕ × ℕ) : ℤ := (q.1 : ℤ) + q.2.1 - q.2.2
  let T := Finset.Icc ((L : ℤ) - H) ((L : ℤ) + 2 * H)
  have hmaps : Set.MapsTo s ↑(U ×ˢ D) ↑T := by
    rintro ⟨a, x, y⟩ h
    have hm := Finset.mem_product.mp (Finset.mem_coe.mp h)
    have ⟨_, hLa, haH⟩ := hU a hm.1
    have ⟨_, _, _, _, _, hxy, hyx⟩ := hD (x, y) hm.2
    apply Finset.mem_Icc.mpr
    dsimp [s]
    constructor <;> omega
  have hinj : Set.InjOn s ↑(U ×ˢ D) := by
    rintro ⟨a, x, y⟩ hp ⟨b, u, v⟩ hq hs
    have hp' := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_product.mp (Finset.mem_coe.mp hq)
    have ⟨hx, hy, _, hyU, hxy, _, _⟩ := hD (x, y) hp'.2
    have ⟨hu, hv, huU, _, _, _, _⟩ := hD (u, v) hq'.2
    have hya : y ≠ a := fun e => hyU (e.symm ▸ hp'.1)
    have hau : a ≠ u := fun e => huU (e ▸ hp'.1)
    obtain ⟨rfl, rfl, rfl⟩ :=
      signed_triples_eq hA (hU a hp'.1).1 (hU b hq'.1).1 hx hy hu hv
        hya hxy.symm hau hs
    rfl
  have hc := Finset.card_le_card_of_injOn s hmaps hinj
  rw [Finset.card_product] at hc
  dsimp [T] at hc
  rw [Int.card_Icc] at hc
  omega

/-- The total of the within-block ordered differences is controlled by any disjoint
anchor block of the same width. The other blocks may be arbitrarily far away. -/
private lemma blocks_closePair_capacity {A : Set ℕ} (hA : Erdos41.NtupleCondition A 3)
    {ι : Type*} (I : Finset ι) (B : ι → Finset ℕ) (L H : ℕ) (U : Finset ℕ)
    (hU : ∀ a ∈ U, a ∈ A ∧ L ≤ a ∧ a ≤ L + H)
    (hB : ∀ j ∈ I, ∀ x ∈ B j, x ∈ A ∧ x ∉ U)
    (hspan : ∀ j ∈ I, ∀ x ∈ B j, ∀ y ∈ B j, x ≤ y + H)
    (hdisj : (↑I : Set ι).PairwiseDisjoint B) :
    U.card * (∑ j ∈ I, ((B j).card * (B j).card - (B j).card)) ≤ 3 * H + 1 := by
  let D := I.biUnion fun j => (B j).offDiag
  have hoff : (↑I : Set ι).PairwiseDisjoint (fun j => (B j).offDiag) := by
    rw [Finset.pairwiseDisjoint_iff] at hdisj ⊢
    intro i hi j hj
    rintro ⟨⟨x, y⟩, hp⟩
    obtain ⟨hpi, hpj⟩ := Finset.mem_inter.mp hp
    exact hdisj hi hj ⟨x, Finset.mem_inter.mpr
      ⟨(Finset.mem_offDiag.mp hpi).1, (Finset.mem_offDiag.mp hpj).1⟩⟩
  have hD : D.card = ∑ j ∈ I, ((B j).card * (B j).card - (B j).card) := by
    rw [Finset.card_biUnion hoff]
    simp only [Finset.offDiag_card]
  rw [← hD]
  apply closePair_capacity hA L H U D hU
  intro p hp
  obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hpj
  exact ⟨(hB j hj _ hx).1, (hB j hj _ hy).1, (hB j hj _ hx).2, (hB j hj _ hy).2, hne,
    hspan j hj _ hx _ hy, hspan j hj _ hy _ hx⟩

private lemma finite_count_cube {A : Set ℕ} (hA : Erdos41.NtupleCondition A 3)
    (S : Finset ℕ) (N : ℕ) (hS : ∀ a ∈ S, a ∈ A ∧ a ≤ N) :
    S.card ^ 3 ≤ 864 * (N + 1) := by
  let k := S.card / 3
  have hk : 3 * k ≤ S.card := by dsimp [k]; omega
  let e := S.orderEmbOfFin (k := S.card) rfl
  let head (i : Fin k) : ℕ := e ⟨i, by have := i.isLt; omega⟩
  let mid (i : Fin k) : ℕ := e ⟨k + i, by have := i.isLt; omega⟩
  let tail (i : Fin k) : ℕ := e ⟨2 * k + i, by have := i.isLt; omega⟩
  have hh i : head i ∈ S := Finset.orderEmbOfFin_mem S rfl _
  have hm i : mid i ∈ S := Finset.orderEmbOfFin_mem S rfl _
  have ht i : tail i ∈ S := Finset.orderEmbOfFin_mem S rfl _
  have hhm (i j : Fin k) : head i < mid j := by
    apply e.strictMono
    change (i : ℕ) < k + (j : ℕ)
    have := i.isLt
    omega
  have hmt (i j : Fin k) : mid i < tail j := by
    apply e.strictMono
    change k + (i : ℕ) < 2 * k + (j : ℕ)
    have := i.isLt
    omega
  let g (q : Fin k × Fin k × Fin k) : Fin (3 * N + 1) :=
    ⟨head q.1 + mid q.2.1 + tail q.2.2, by
      have := (hS _ (hh q.1)).2
      have := (hS _ (hm q.2.1)).2
      have := (hS _ (ht q.2.2)).2
      omega⟩
  have hg : Function.Injective g := by
    rintro ⟨i, j, l⟩ ⟨i', j', l'⟩ heq
    have hs : head i + mid j + tail l = head i' + mid j' + tail l' :=
      congrArg Fin.val heq
    have hdiff : (head i : ℤ) + mid j - tail l' = head i' + mid j' - tail l := by omega
    obtain ⟨hi, hj, hl⟩ := signed_triples_eq hA
      (hS _ (hh i)).1 (hS _ (hh i')).1 (hS _ (hm j)).1 (hS _ (ht l')).1
      (hS _ (hm j')).1 (hS _ (ht l)).1 ((hhm i j).trans (hmt j l')).ne'
      (hmt j l').ne' (hhm i j').ne hdiff
    have hi' : i = i' := Fin.ext (congrArg (fun x : Fin S.card => x.val) (e.injective hi))
    have hj' : j = j' := Fin.ext (by
      have := congrArg Fin.val (e.injective hj)
      change k + (j : ℕ) = k + (j' : ℕ) at this
      omega)
    have hl' : l = l' := Fin.ext (by
      have := congrArg Fin.val (e.injective hl)
      change 2 * k + (l' : ℕ) = 2 * k + (l : ℕ) at this
      omega)
    simp [hi', hj', hl']
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have hc' : k ^ 3 ≤ 3 * N + 1 := by simpa [pow_succ, mul_assoc] using hc
  by_cases hzero : k = 0
  · have hsmall : S.card ≤ 2 := by dsimp [k] at hzero; omega
    exact (Nat.pow_le_pow_left hsmall 3).trans (by omega)
  · have hs : S.card ≤ 6 * k := by dsimp [k] at *; omega
    calc
      _ ≤ (6 * k) ^ 3 := Nat.pow_le_pow_left hs 3
      _ = 216 * k ^ 3 := by ring
      _ ≤ 216 * (3 * N + 1) := Nat.mul_le_mul_left _ hc'
      _ ≤ _ := by omega

private lemma scaled_count_of_ne_zero (A : Set ℕ)
    (h : atTop.liminf (fun N : ℕ =>
      ((A ∩ Icc 1 N).ncard : ℝ) / (N : ℝ) ^ (1 / 3 : ℝ)) ≠ 0) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ N : ℕ in atTop, N ≤ (d * (A ∩ Icc 1 N).ncard) ^ 3 := by
  let r := fun N : ℕ => ((A ∩ Icc 1 N).ncard : ℝ) / (N : ℝ) ^ (1 / 3 : ℝ)
  let S : Set ℝ := { l | ∀ᶠ N in atTop, l ≤ r N }
  have hS : sSup S ≠ 0 := by rwa [Filter.liminf_eq] at h
  have hbounded : BddAbove S := by
    by_contra hb
    exact hS (Real.sSup_of_not_bddAbove hb)
  have hz : (0 : ℝ) ∈ S := Eventually.of_forall (fun _ => by dsimp [r]; positivity)
  have hpos : 0 < sSup S := (le_csSup hbounded hz).lt_of_ne hS.symm
  obtain ⟨c, hc, hcs⟩ := exists_between hpos
  obtain ⟨b, hb, hcb⟩ := exists_lt_of_lt_csSup ⟨0, hz⟩ hcs
  obtain ⟨d, hd⟩ := exists_nat_gt (1 / c)
  have hdR : 0 < (d : ℝ) := (by positivity : 0 < 1 / c).trans hd
  have hdc : 1 ≤ (d : ℝ) * c := ((div_lt_iff₀ hc).mp hd).le
  refine ⟨d, by exact_mod_cast hdR, ?_⟩
  filter_upwards [hb, eventually_gt_atTop 0] with N hN hNpos
  have hzN : 0 < (N : ℝ) := by exact_mod_cast hNpos
  let x := (N : ℝ) ^ (1 / 3 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos hzN _
  have hcx : c * x ≤ ((A ∩ Icc 1 N).ncard : ℝ) :=
    (le_div_iff₀ hx).mp (hcb.le.trans hN)
  have hroot : x ≤ (d : ℝ) * (A ∩ Icc 1 N).ncard := by
    calc
      x = 1 * x := by simp
      _ ≤ ((d : ℝ) * c) * x := mul_le_mul_of_nonneg_right hdc hx.le
      _ = (d : ℝ) * (c * x) := mul_assoc ..
      _ ≤ _ := mul_le_mul_of_nonneg_left hcx hdR.le
  have h3 := pow_le_pow_left₀ hx.le hroot 3
  have hx3 : x ^ (3 : ℕ) = (N : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast hzN.le]
    norm_num
  rw [hx3] at h3
  exact_mod_cast h3

private lemma enumeration_le_cube {A : Set ℕ} (hA : A.Infinite) (d : ℕ)
    (hd : ∀ᶠ N : ℕ in atTop, N ≤ (d * (A ∩ Icc 1 N).ncard) ^ 3) :
    ∀ᶠ n : ℕ in atTop, Nat.nth (· ∈ A) n ≤ (d * (n + 1)) ^ 3 := by
  let f := Nat.nth (· ∈ A)
  have hmono : StrictMono f := Nat.nth_strictMono hA
  have hrange : Set.range f = A := Nat.range_nth_of_infinite hA
  have hnd : ∀ᶠ n in atTop, f n ≤ (d * (A ∩ Icc 1 (f n)).ncard) ^ 3 :=
    hmono.tendsto_atTop.eventually hd
  filter_upwards [hnd] with n hn
  have hsub : A ∩ Icc 1 (f n) ⊆ f '' Iic n := by
    rintro x ⟨hx, _, hxn⟩
    rw [← hrange] at hx
    obtain ⟨j, rfl⟩ := hx
    exact ⟨j, hmono.le_iff_le.mp hxn, rfl⟩
  have hc := Set.ncard_le_ncard hsub ((Set.finite_Iic n).image f)
  rw [Set.ncard_image_of_injective _ hmono.injective] at hc
  have hc' : (A ∩ Icc 1 (f n)).ncard ≤ n + 1 := by simpa using hc
  exact hn.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left d hc') 3)

/-- If the counting ratio has positive liminf, all short pairs in the tail
satisfy a single quadratic bound, independent of the location of their endpoints. -/
private lemma tail_closePairs_quadratic {A : Set ℕ} (hA : Erdos41.NtupleCondition A 3)
    (d : ℕ) (hd : ∀ᶠ N : ℕ in atTop, N ≤ (d * (A ∩ Icc 1 N).ncard) ^ 3) :
    ∀ᶠ k : ℕ in atTop, ∀ D : Finset (ℕ × ℕ),
      (∀ p ∈ D, p.1 ∈ A ∧ p.2 ∈ A ∧ k ^ 3 < p.1 ∧ k ^ 3 < p.2 ∧ p.1 ≠ p.2 ∧
        p.1 ≤ p.2 + k ^ 3 ∧ p.2 ≤ p.1 + k ^ 3) → D.card ≤ 4 * d * k ^ 2 := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hd
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop 0] with k hk hkpos
  intro D hD
  let H := k ^ 3
  let U := (Finset.Icc 1 H).filter (· ∈ A)
  have hco : (↑U : Set ℕ) = A ∩ Icc 1 H := by
    ext x
    simp [U]
    tauto
  have hc : (A ∩ Icc 1 H).ncard = U.card := by rw [← hco, Set.ncard_coe_finset]
  have hkH : k ≤ H := Nat.le_self_pow (by decide) _
  have hcube : k ^ 3 ≤ (d * U.card) ^ 3 := hc ▸ hN₀ H (hk.trans hkH)
  have hkU : k ≤ d * U.card := le_of_pow_le_pow_left₀ (by decide) (Nat.zero_le _) hcube
  have hU : ∀ a ∈ U, a ∈ A ∧ 0 ≤ a ∧ a ≤ 0 + H := by
    intro a ha
    rw [← Finset.mem_coe, hco] at ha
    exact ⟨ha.1, Nat.zero_le _, by simpa using ha.2.2⟩
  have hnotU {a : ℕ} (ha : H < a) : a ∉ U := fun hu => (not_le_of_gt ha) (by
    simpa using (hU a hu).2.2)
  have hcap := closePair_capacity hA 0 H U D hU (by
    intro p hp
    obtain ⟨ha, hb, hLa, hLb, hne, h1, h2⟩ := hD p hp
    exact ⟨ha, hb, hnotU hLa, hnotU hLb, hne, h1, h2⟩)
  have hHpos : 1 ≤ H := Nat.pow_pos hkpos
  apply Nat.le_of_mul_le_mul_left (c := k) _ hkpos
  calc
    k * D.card ≤ (d * U.card) * D.card := Nat.mul_le_mul_right _ hkU
    _ = d * (U.card * D.card) := mul_assoc ..
    _ ≤ d * (4 * H) := Nat.mul_le_mul_left _ (hcap.trans (by omega))
    _ = k * (4 * d * k ^ 2) := by dsimp [H]; ring

private lemma all_closePairs_quadratic {A : Set ℕ} (hA : Erdos41.NtupleCondition A 3)
    (d : ℕ) (hd : ∀ᶠ N : ℕ in atTop, N ≤ (d * (A ∩ Icc 1 N).ncard) ^ 3) :
    ∀ᶠ k : ℕ in atTop, ∀ D : Finset (ℕ × ℕ),
      (∀ p ∈ D, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 ∧
        p.1 ≤ p.2 + k ^ 3 ∧ p.2 ≤ p.1 + k ^ 3) → D.card ≤ (196 + 4 * d) * k ^ 2 := by
  classical
  filter_upwards [tail_closePairs_quadratic hA d hd, eventually_gt_atTop 0] with k htail hk
  intro D hD
  let H := k ^ 3
  let U := (Finset.Icc 0 (2 * H)).filter (· ∈ A)
  let far (p : ℕ × ℕ) : Prop := H < p.1 ∧ H < p.2
  let T := D.filter far
  let E := D.filter (fun p => ¬ far p)
  have hT : T.card ≤ 4 * d * k ^ 2 := htail T (by
    intro p hp
    obtain ⟨hpD, hfar⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2, hne, h12, h21⟩ := hD p hpD
    exact ⟨h1, h2, hfar.1, hfar.2, hne, h12, h21⟩)
  have hsub : E ⊆ U ×ˢ U := by
    intro p hp
    obtain ⟨hpD, hfar⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2, _, h12, h21⟩ := hD p hpD
    change ¬ (H < p.1 ∧ H < p.2) at hfar
    change p.1 ≤ p.2 + H at h12
    change p.2 ≤ p.1 + H at h21
    apply Finset.mem_product.mpr
    simp only [U, Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and]
    exact ⟨⟨by omega, h1⟩, ⟨by omega, h2⟩⟩
  have hU := finite_count_cube hA U (2 * H) (by
    intro a ha
    have h := Finset.mem_filter.mp ha
    exact ⟨h.2, (Finset.mem_Icc.mp h.1).2⟩)
  have hH : 1 ≤ H := Nat.pow_pos hk
  have hU' : U.card ≤ 14 * k := by
    apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (Nat.zero_le _)
    grw [hU]
    rw [mul_pow]
    norm_num [← show H = k ^ 3 by rfl]
    omega
  have hE : E.card ≤ 196 * k ^ 2 := by
    calc
      E.card ≤ (U ×ˢ U).card := Finset.card_le_card hsub
      _ = U.card * U.card := Finset.card_product ..
      _ ≤ (14 * k) * (14 * k) := Nat.mul_le_mul hU' hU'
      _ = _ := by ring
  have hsplit : T.card + E.card = D.card := Finset.card_filter_add_card_filter_not far
  calc
    D.card = T.card + E.card := hsplit.symm
    _ ≤ 4 * d * k ^ 2 + 196 * k ^ 2 := Nat.add_le_add hT hE
    _ = _ := by ring

private lemma eventually_ratio_le_twelve {A : Set ℕ} (hA : Erdos41.NtupleCondition A 3) :
    ∀ᶠ N : ℕ in atTop, ((A ∩ Icc 1 N).ncard : ℝ) / (N : ℝ) ^ (1 / 3 : ℝ) ≤ 12 := by
  classical
  filter_upwards [eventually_gt_atTop 0] with N hN
  let S := (Finset.Icc 1 N).filter (· ∈ A)
  have hS : (↑S : Set ℕ) = A ∩ Icc 1 N := by
    ext x
    simp [S]
    tauto
  have hcard := finite_count_cube hA S N (by
    intro a ha
    have h := Finset.mem_filter.mp ha
    exact ⟨h.2, (Finset.mem_Icc.mp h.1).2⟩)
  have hnat : S.card ^ 3 ≤ 12 ^ 3 * N := by
    norm_num at *
    omega
  have hreal : (S.card : ℝ) ^ 3 ≤ 12 ^ 3 * (N : ℝ) := by exact_mod_cast hnat
  have hpos : 0 < (N : ℝ) := by exact_mod_cast hN
  let x := (N : ℝ) ^ (1 / 3 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos hpos _
  have hx3 : x ^ (3 : ℕ) = (N : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast hpos.le]
    norm_num
  rw [← hS, Set.ncard_coe_finset]
  apply (div_le_iff₀ hx).mpr
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
  rwa [mul_pow, hx3]

private lemma scaled_count_of_enumeration_le_cube {f : ℕ → ℕ} (hf : StrictMono f)
    (d : ℕ) (hd : ∀ᶠ n : ℕ in atTop, f n ≤ (d * (n + 1)) ^ 3) :
    ∀ᶠ N : ℕ in atTop, N ≤ (3 * d * (range f ∩ Icc 1 N).ncard) ^ 3 := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hd
  have hcount (j N : ℕ) (h : f j ≤ N) : j ≤ (range f ∩ Icc 1 N).ncard := by
    have hs : f '' Icc 1 j ⊆ range f ∩ Icc 1 N := by
      rintro _ ⟨i, ⟨hi, hij⟩, rfl⟩
      exact ⟨mem_range_self _, hi.trans (hf.id_le i), (hf.monotone hij).trans h⟩
    have hc := Set.ncard_le_ncard hs ((finite_Icc ..).subset inter_subset_right)
    rw [Set.ncard_image_of_injective _ hf.injective] at hc
    simpa using hc
  filter_upwards [eventually_ge_atTop (f (max 1 n₀))] with N hN
  let m := (range f ∩ Icc 1 N).ncard
  have hm : max 1 n₀ ≤ m := hcount _ _ hN
  have hl : N < f (m + 1) := by
    by_contra! hn
    have hh : m + 1 ≤ m := hcount _ _ hn
    omega
  have hmc : d * (m + 1 + 1) ≤ 3 * d * m := by
    rw [mul_comm 3 d, mul_assoc]
    apply Nat.mul_le_mul_left
    omega
  exact hl.le.trans ((hn₀ _ (by omega)).trans (Nat.pow_le_pow_left hmc 3))

private lemma liminf_pos_of_scaled_count {A : Set ℕ} (hA : Erdos41.NtupleCondition A 3)
    (d : ℕ) (hdpos : 0 < d)
    (hd : ∀ᶠ N : ℕ in atTop, N ≤ (d * (A ∩ Icc 1 N).ncard) ^ 3) :
    0 < atTop.liminf (fun N : ℕ =>
      ((A ∩ Icc 1 N).ncard : ℝ) / (N : ℝ) ^ (1 / 3 : ℝ)) := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hdpos
  apply (by positivity : 0 < (d : ℝ)⁻¹).trans_le
  apply le_liminf_of_le (isCoboundedUnder_ge_of_eventually_le atTop (eventually_ratio_le_twelve hA))
  filter_upwards [hd, eventually_gt_atTop 0] with N hn hnpos
  have hnR : 0 < (N : ℝ) := by exact_mod_cast hnpos
  let x := (N : ℝ) ^ (1 / 3 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos hnR _
  have hx3 : x ^ (3 : ℕ) = (N : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast hnR.le]
    norm_num
  apply (le_div_iff₀ hx).mpr
  rw [inv_mul_le_iff₀ hd']
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
  rw [hx3]
  exact_mod_cast hn

private lemma liminf_ne_zero_iff_cubic_enumeration {A : Set ℕ}
    (hA : Erdos41.NtupleCondition A 3) (hInf : A.Infinite) :
    (atTop.liminf (fun N : ℕ =>
      ((A ∩ Icc 1 N).ncard : ℝ) / (N : ℝ) ^ (1 / 3 : ℝ)) ≠ 0) ↔
      ∃ d : ℕ, 0 < d ∧ ∀ᶠ n : ℕ in atTop, Nat.nth (· ∈ A) n ≤ (d * (n + 1)) ^ 3 := by
  constructor
  · intro hzero
    obtain ⟨d, hdpos, hd⟩ := scaled_count_of_ne_zero A hzero
    exact ⟨d, hdpos, enumeration_le_cube hInf d hd⟩
  · rintro ⟨d, hdpos, hd⟩
    have hcount := scaled_count_of_enumeration_le_cube (Nat.nth_strictMono hInf) d hd
    rw [Nat.range_nth_of_infinite hInf] at hcount
    exact (liminf_pos_of_scaled_count hA (3 * d) (Nat.mul_pos (by decide) hdpos) hcount).ne'

end Erdos41Relay

theorem OMA.solution : type_of% @Erdos41.erdos_41 := by
  intro A hA hInf
  by_contra hzero
  obtain ⟨d, hdpos, hd⟩ := Erdos41Relay.scaled_count_of_ne_zero A hzero
  have hcubic := Erdos41Relay.enumeration_le_cube hInf d hd
  have hshort := Erdos41Relay.all_closePairs_quadratic hA d hd
  sorry

