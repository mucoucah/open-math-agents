import FormalConjectures.ErdosProblems.«713»

/-! # Erdős Problem 713, rationality of the extremal exponent -/
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/713.lean:65 (declaration Erdos713.erdos_713.parts.ii)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics SimpleGraph Finset
open scoped Classical BigOperators

/-- The extremal number is bounded by a power and attains that scale along a subsequence. -/
def OMA.ExtremalPowerOrder {V : Type*} (G : SimpleGraph V) (α : ℝ) : Prop :=
  (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) ∧
    ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)

theorem OMA.extremalPowerOrder_of_equivalent {V : Type*} {G : SimpleGraph V} {α c : ℝ}
    (hc : c ≠ 0) (hG : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ α)) :
    OMA.ExtremalPowerOrder G α := by
  refine ⟨hG.isBigO.trans (isBigO_const_mul_self c _ _), ?_⟩
  intro hn
  have reverse : (fun n : ℕ => (n : ℝ) ^ α) =O[atTop]
      (fun n : ℕ => (extremalNumber n G : ℝ)) :=
    (isBigO_self_const_mul hc _ _).trans hG.symm.isBigO
  apply isLittleO_irrefl (f'' := fun n : ℕ => (n : ℝ) ^ α) _ (reverse.trans_isLittleO hn)
  apply Eventually.frequently
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (Real.rpow_pos_of_pos (by exact_mod_cast hn) α).ne'

theorem OMA.extremalNumber_isBigO_of_contained {V W : Type*}
    {F : SimpleGraph V} {G : SimpleGraph W} (h : F ⊑ G) :
    (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop]
      (fun n : ℕ => (extremalNumber n G : ℝ)) := by
  apply IsBigO.of_bound 1
  refine Eventually.of_forall fun n => ?_
  simp only [Real.norm_natCast, one_mul]
  exact_mod_cast h.extremalNumber_le (n := n)

/-- Deleting one edge per copy gives a lower bound on the number of copies. -/
theorem OMA.card_edges_le_extremal_add_copyCount {V W : Type*} [Fintype V]
    (H : SimpleGraph V) (J : SimpleGraph W) (hJ : J ≠ ⊥) :
    H.edgeFinset.card ≤ extremalNumber (Fintype.card V) J + H.copyCount J := by
  apply H.le_card_edgeFinset_killCopies_add_copyCount.trans
  apply Nat.add_le_add_right
  convert! card_edgeFinset_le_extremalNumber (free_killCopies (G := H) hJ)

theorem OMA.eventually_copyCount_lower {W : Type*} {J : SimpleGraph W} (hJ : J ≠ ⊥)
    {α δ : ℝ} (hδ : 0 < δ)
    (hsmall : (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    ∀ᶠ n : ℕ in atTop, ∀ H : SimpleGraph (Fin n), δ * (n : ℝ) ^ α ≤ H.edgeFinset.card →
      (δ / 2) * (n : ℝ) ^ α ≤ H.copyCount J := by
  filter_upwards [hsmall.bound (show 0 < δ / 2 by positivity)] with n hn
  intro H hH
  rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) α)] at hn
  have hcount : (H.edgeFinset.card : ℝ) ≤ (extremalNumber n J : ℝ) + H.copyCount J := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using
      OMA.card_edges_le_extremal_add_copyCount H J hJ :
      H.edgeFinset.card ≤ extremalNumber n J + H.copyCount J)
  linarith

private theorem card_colorings_prescribed {E : Type*} [Fintype E] [DecidableEq E] (k : ℕ)
    (T : Finset E) (g : E → Fin k) :
    (Finset.univ.filter fun f : E → Fin k => ∀ e ∈ T, f e = g e).card =
      k ^ (Fintype.card E - T.card) := by
  let opts (e : E) : Finset (Fin k) := if e ∈ T then {g e} else Finset.univ
  have hf : (Finset.univ.filter fun f : E → Fin k => ∀ e ∈ T, f e = g e) =
      Fintype.piFinset opts := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h e
      by_cases he : e ∈ T
      · simpa [opts, he] using h e he
      · simp [opts, he]
    · intro h e he
      simpa [opts, he] using h e
  rw [hf, Fintype.card_piFinset, ← Finset.card_compl]
  have hcard (e : E) : (opts e).card = if e ∈ T then 1 else k := by
    by_cases he : e ∈ T <;> simp [opts, he]
  simp only [hcard]
  simpa only [Finset.mem_compl, ite_not, Finset.prod_const] using
    Finset.prod_ite_mem_eq Tᶜ (fun _ => k)

private theorem card_colorings_fixed {E : Type*} [Fintype E] [DecidableEq E] (k : ℕ) (z : Fin k)
    (T : Finset E) :
    (Finset.univ.filter fun f : E → Fin k => ∀ e ∈ T, f e = z).card =
      k ^ (Fintype.card E - T.card) :=
  card_colorings_prescribed k T (fun _ => z)

private theorem sum_card_filter_swap {E C : Type*}
    (S : Finset E) (T : Finset C) (P : E → C → Prop)
    [∀ e c, Decidable (P e c)] :
    (∑ e ∈ S, (T.filter (P e)).card) =
      ∑ c ∈ T, (S.filter (fun e => P e c)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

private def colorGraph {V : Type*} (H : SimpleGraph V) {k : ℕ}
    (f : Sym2 V → Fin k) (z : Fin k) : SimpleGraph V :=
  H.deleteEdges {e | f e ≠ z}

private theorem card_colorGraph {V : Type*} [Fintype V] (H : SimpleGraph V) {k : ℕ}
    (f : Sym2 V → Fin k) (z : Fin k) :
    (colorGraph H f z).edgeFinset.card = (H.edgeFinset.filter fun e => f e = z).card := by
  congr 1
  ext e
  rw [Finset.mem_filter, mem_edgeFinset, mem_edgeFinset]
  induction e using Sym2.inductionOn with
  | hf u v =>
    change (H.deleteEdges {e | f e ≠ z}).Adj u v ↔ H.Adj u v ∧ f s(u, v) = z
    simp only [deleteEdges_adj, Set.mem_ofPred_eq, not_not]

private noncomputable def copiedEdges {V W : Type*} {H : SimpleGraph V} {J : SimpleGraph W}
    [Fintype W] (c : J.Copy H) : Finset (Sym2 V) :=
  J.edgeFinset.map c.toEmbedding.sym2Map

private theorem card_copiedEdges {V W : Type*} {H : SimpleGraph V} {J : SimpleGraph W}
    [Fintype W] (c : J.Copy H) :
    (copiedEdges c).card = J.edgeFinset.card := Finset.card_map _

private theorem copy_uses_color {V W : Type*} {H : SimpleGraph V} {J : SimpleGraph W}
    [Fintype W] {k : ℕ} (f : Sym2 V → Fin k) (z : Fin k) (c : J.Copy H) :
    (∀ e ∈ copiedEdges c, f e = z) ↔
      ∀ ⦃u v⦄, J.Adj u v → (colorGraph H f z).Adj (c u) (c v) := by
  constructor
  · intro hc u v huv
    apply deleteEdges_adj.mpr
    refine ⟨c.toHom.map_rel' huv, ?_⟩
    exact not_not_intro (hc _ (Finset.mem_map.mpr ⟨s(u, v), by simpa using huv, rfl⟩))
  · intro hc e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    induction a using Sym2.inductionOn with
    | hf u v =>
      have huv : J.Adj u v := by simpa using ha
      exact not_not.mp (deleteEdges_adj.mp (hc huv)).2

private theorem labelledCopyCount_colorGraph {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (J : SimpleGraph W) {k : ℕ}
    (f : Sym2 V → Fin k) (z : Fin k) :
    (colorGraph H f z).labelledCopyCount J =
      (Finset.univ.filter fun c : J.Copy H => ∀ e ∈ copiedEdges c, f e = z).card := by
  let incl := Copy.ofLE (colorGraph H f z) H (H.deleteEdges_le _)
  let e : J.Copy (colorGraph H f z) ≃ {c : J.Copy H // ∀ e ∈ copiedEdges c, f e = z} := {
    toFun := fun c => ⟨incl.comp c, (copy_uses_color f z _).2 fun {_ _} h => c.toHom.map_rel' h⟩
    invFun := fun c => ⟨⟨c.1, fun h => (copy_uses_color f z c.1).1 c.2 h⟩, c.1.injective⟩
    left_inv := fun c => Copy.ext fun _ => rfl
    right_inv := fun c => Subtype.ext (Copy.ext fun _ => rfl)
  }
  rw [labelledCopyCount, Fintype.card_congr e]
  exact Fintype.card_ofFinset (p := {c : J.Copy H | ∀ e ∈ copiedEdges c, f e = z}) _
    (fun c => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq])

/-- Averaging the graphs of one color amplifies the elementary copy-count bound. -/
theorem OMA.coloring_labelledCopyCount_bound {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (J : SimpleGraph W) (hJ : J ≠ ⊥) {k : ℕ} (z : Fin k) :
    k ^ (J.edgeFinset.card - 1) * H.edgeFinset.card ≤
      k ^ J.edgeFinset.card * extremalNumber (Fintype.card V) J + H.labelledCopyCount J := by
  let e := J.edgeFinset.card
  let m := Fintype.card (Sym2 V)
  let X := extremalNumber (Fintype.card V) J
  change k ^ (e - 1) * H.edgeFinset.card ≤ k ^ e * X + H.labelledCopyCount J
  have hk : 0 < k := z.pos
  by_cases hcontained : J ⊑ H
  · obtain ⟨c⟩ := hcontained
    have hem : e ≤ m := by
      change J.edgeFinset.card ≤ Fintype.card (Sym2 V)
      rw [← card_copiedEdges c]
      exact Finset.card_le_univ _
    have he : 0 < e := by
      apply Finset.card_pos.mpr
      by_contra hf
      apply hJ
      apply edgeFinset_inj.mp
      rw [Finset.not_nonempty_iff_eq_empty.mp hf, edgeFinset_bot]
    have hEdge (a : Sym2 V) :
        (univ.filter fun f : Sym2 V → Fin k => f a = z).card = k ^ (m - 1) := by
      simpa using card_colorings_fixed k z {a}
    have edgesSum :
        (∑ f : Sym2 V → Fin k, (colorGraph H f z).edgeFinset.card) =
          H.edgeFinset.card * k ^ (m - 1) := by
      simp_rw [card_colorGraph]
      rw [sum_card_filter_swap (univ : Finset (Sym2 V → Fin k)) H.edgeFinset
        (fun f a => f a = z)]
      simp [hEdge]
    have copiesSum :
        (∑ f : Sym2 V → Fin k, (colorGraph H f z).labelledCopyCount J) =
          H.labelledCopyCount J * k ^ (m - e) := by
      simp_rw [labelledCopyCount_colorGraph]
      rw [sum_card_filter_swap (univ : Finset (Sym2 V → Fin k))
        (univ : Finset (J.Copy H)) (fun f c => ∀ a ∈ copiedEdges c, f a = z)]
      simp_rw [card_colorings_fixed, card_copiedEdges]
      simp [labelledCopyCount, e, m]
    have bound (f : Sym2 V → Fin k) :
        (colorGraph H f z).edgeFinset.card ≤
          X + (colorGraph H f z).labelledCopyCount J :=
      (OMA.card_edges_le_extremal_add_copyCount (colorGraph H f z) J hJ).trans
        (Nat.add_le_add_left (copyCount_le_labelledCopyCount ..) X)
    have summed := Finset.sum_le_sum (s := (univ : Finset (Sym2 V → Fin k))) (fun f _ => bound f)
    rw [edgesSum, Finset.sum_add_distrib, copiesSum] at summed
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin] at summed
    have hm : k ^ m = k ^ (m - e) * k ^ e := by
      rw [← pow_add]
      congr 1
      omega
    have hm1 : k ^ (m - 1) = k ^ (m - e) * k ^ (e - 1) := by
      rw [← pow_add]
      congr 1
      omega
    change H.edgeFinset.card * k ^ (m - 1) ≤
      k ^ m * X + H.labelledCopyCount J * k ^ (m - e) at summed
    rw [hm1, hm] at summed
    apply Nat.le_of_mul_le_mul_left _ (pow_pos hk (m - e))
    calc
      k ^ (m - e) * (k ^ (e - 1) * H.edgeFinset.card) =
          H.edgeFinset.card * (k ^ (m - e) * k ^ (e - 1)) := by ac_rfl
      _ ≤ (k ^ (m - e) * k ^ e) * X + H.labelledCopyCount J * k ^ (m - e) := summed
      _ = k ^ (m - e) * (k ^ e * X + H.labelledCopyCount J) := by rw [Nat.mul_add]; ac_rfl
  · have hbound := card_edgeFinset_le_extremalNumber (show J.Free H from hcontained)
    have hpow : k ^ (e - 1) ≤ k ^ e := pow_le_pow_right₀ (by omega) (by omega)
    exact ((Nat.mul_le_mul hpow hbound).trans (Nat.le_add_right _ _))

/-- Every fixed positive multiple of the power is eventually a lower bound for
labelled copies of a pattern with at least two edges and lower extremal order. -/
theorem OMA.eventually_labelledCopyCount_amplified {W : Type*} [Fintype W] {J : SimpleGraph W}
    (hJ : 2 ≤ J.edgeFinset.card) {α δ C : ℝ} (hδ : 0 < δ)
    (hsmall : (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    ∀ᶠ n : ℕ in atTop, ∀ H : SimpleGraph (Fin n), δ * (n : ℝ) ^ α ≤ H.edgeFinset.card →
      C * (n : ℝ) ^ α ≤ H.labelledCopyCount J := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * C / δ)
  let K := k + 1
  let e := J.edgeFinset.card
  let t := (K : ℝ) ^ (e - 1)
  have hK : 0 < (K : ℝ) := by dsimp [K]; positivity
  have hK1 : 1 ≤ (K : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have ht : (K : ℝ) ≤ t := by
    calc
      (K : ℝ) = (K : ℝ) ^ (1 : ℕ) := by simp
      _ ≤ t := pow_le_pow_right₀ hK1 (by omega)
  have htarget : C ≤ t * (δ / 2) := by
    have hlt : 2 * C < (k : ℝ) * δ := (div_lt_iff₀ hδ).mp hk
    have hkt : (k : ℝ) ≤ t := by
      apply le_trans _ ht
      dsimp [K]
      push_cast
      linarith
    nlinarith only [hlt, mul_le_mul_of_nonneg_right hkt hδ.le]
  filter_upwards [hsmall.bound (show 0 < δ / (2 * (K : ℝ)) by positivity)] with n hn
  intro H hH
  have hpow : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_natCast, Real.norm_of_nonneg hpow] at hn
  have hprune : (K : ℝ) * (extremalNumber n J : ℝ) ≤ δ / 2 * (n : ℝ) ^ α := by
    calc
      _ ≤ (K : ℝ) * (δ / (2 * (K : ℝ)) * (n : ℝ) ^ α) :=
        mul_le_mul_of_nonneg_left hn hK.le
      _ = _ := by field_simp
  have hne : J ≠ ⊥ := by
    intro hb
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < J.edgeFinset.card)
    have hmem := mem_edgeFinset.mp ha
    simp only [hb, edgeSet_bot, Set.mem_empty_iff_false] at hmem
  have hfinite := OMA.coloring_labelledCopyCount_bound H J hne
      (show Fin K from ⟨0, Nat.succ_pos k⟩)
  rw [Fintype.card_fin] at hfinite
  have hcount : t * (H.edgeFinset.card : ℝ) ≤
      t * ((K : ℝ) * (extremalNumber n J : ℝ)) + H.labelledCopyCount J := by
    rw [← mul_assoc]
    have hp : t * (K : ℝ) = (K : ℝ) ^ e := by
      dsimp [t]
      rw [← pow_succ, show e - 1 + 1 = e by omega]
    rw [hp]
    dsimp only [t, e]
    exact_mod_cast hfinite
  calc
    _ ≤ (t * (δ / 2)) * (n : ℝ) ^ α := mul_le_mul_of_nonneg_right htarget hpow
    _ ≤ _ := by
      have ht0 : 0 ≤ t := hK.le.trans ht
      nlinarith only [hcount, mul_le_mul_of_nonneg_left hH ht0,
        mul_le_mul_of_nonneg_left hprune ht0]

/-- Uniform edge coloring of a complete host yields the deletion lower bound
on a subsequence of vertex counts. -/
theorem OMA.extremalNumber_power_subseq_lower {W : Type*} [Fintype W] (J : SimpleGraph W)
    (hJ : 2 ≤ J.edgeFinset.card) {a : ℕ} (ha : 2 ≤ a) :
    let d := J.edgeFinset.card - 1
    let x := Fintype.card W - 2
    (a : ℝ) ^ (2 * d) ≤ 64 * (a : ℝ) ^ x * (extremalNumber (a ^ d) J : ℝ) := by
  intro d x
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hv : 2 ≤ Fintype.card W := by
    by_contra! hv
    have hc := J.card_edgeFinset_le_card_choose_two
    rw [Nat.choose_eq_zero_of_lt hv] at hc
    omega
  have hvx : Fintype.card W = x + 2 := by dsimp [x]; omega
  have hne : J ≠ ⊥ := by
    intro hb
    obtain ⟨b, hb'⟩ := Finset.card_pos.mp (by omega : 0 < J.edgeFinset.card)
    have hmem := mem_edgeFinset.mp hb'
    simp only [hb, edgeSet_bot, Set.mem_empty_iff_false] at hmem
  let n := a ^ d
  let K := 8 * a ^ x
  have hn : 2 ≤ n := calc
    2 ≤ a := ha
    _ = a ^ (1 : ℕ) := by simp
    _ ≤ n := pow_le_pow_right₀ (by omega) hd
  let H : SimpleGraph (Fin n) := ⊤
  let E := (H.edgeFinset.card : ℝ)
  let M := (K : ℝ) ^ d
  have hE : (n : ℝ) ^ (2 : ℕ) ≤ 4 * E := by
    dsimp [E, H]
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, Nat.cast_choose_two]
    have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) by positivity)
      (show 0 ≤ (n : ℝ) - 2 by linarith)]
  have hCopies : H.labelledCopyCount J ≤ n ^ Fintype.card W := by
    have h := Fintype.card_le_of_injective (fun c : J.Copy H => (c : W → Fin n))
      (fun _ _ h => Copy.ext (congrFun h))
    unfold labelledCopyCount
    calc
      _ ≤ Fintype.card (W → Fin n) := by convert! h
      _ = _ := by simp
  have hCopiesR : (H.labelledCopyCount J : ℝ) ≤ (n : ℝ) ^ Fintype.card W := by
    exact_mod_cast hCopies
  have hM : 8 * (n : ℝ) ^ x ≤ M := by
    have h8 : (8 : ℝ) ≤ (8 : ℝ) ^ d := by
      calc
        (8 : ℝ) = (8 : ℝ) ^ (1 : ℕ) := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hd
    dsimp [M, K, n]
    push_cast
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm d x]
    exact mul_le_mul_of_nonneg_right h8 (by positivity)
  have hAbs : 2 * (H.labelledCopyCount J : ℝ) ≤ M * E := by
    calc
      _ ≤ 2 * (n : ℝ) ^ Fintype.card W := mul_le_mul_of_nonneg_left hCopiesR (by norm_num)
      _ = (8 * (n : ℝ) ^ x) * ((n : ℝ) ^ (2 : ℕ) / 4) := by rw [hvx, pow_add]; ring
      _ ≤ _ := mul_le_mul hM (by linarith only [hE]) (by positivity) (by positivity)
  have hK : 0 < K := by
    dsimp [K]
    exact Nat.mul_pos (by decide) (pow_pos (by omega) _)
  have hMpos : 0 < M := by
    have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    exact pow_pos this _
  have hfin := OMA.coloring_labelledCopyCount_bound H J hne (⟨0, hK⟩ : Fin K)
  rw [Fintype.card_fin] at hfin
  have hf : M * E ≤ M * ((K : ℝ) * (extremalNumber n J : ℝ)) + H.labelledCopyCount J := by
    rw [← mul_assoc]
    have hp : M * (K : ℝ) = (K : ℝ) ^ J.edgeFinset.card := by
      dsimp [M, d]
      rw [← pow_succ, show J.edgeFinset.card - 1 + 1 = J.edgeFinset.card by omega]
    rw [hp]
    dsimp only [M, E, d]
    norm_cast
    convert! hfin
  have hbound : E ≤ 2 * (K : ℝ) * (extremalNumber n J : ℝ) := by
    apply le_of_mul_le_mul_left _ hMpos
    nlinarith only [hf, hAbs]
  have hfinal : (n : ℝ) ^ (2 : ℕ) ≤ 8 * (K : ℝ) * (extremalNumber n J : ℝ) := by
    linarith only [hE, hbound]
  dsimp only [n, K] at hfinal
  push_cast at hfinal
  rw [← pow_mul, Nat.mul_comm d 2] at hfinal
  convert hfinal using 1
  ring

/-- The rational exponent in the random-deletion lower bound. -/
noncomputable def OMA.deletionExponent {W : Type*} [Fintype W] (J : SimpleGraph W) : ℚ :=
  2 - ((Fintype.card W - 2 : ℕ) : ℚ) / ((J.edgeFinset.card - 1 : ℕ) : ℚ)

/-- Any power upper bound on the extremal number obeys the classical
random-deletion lower bound on its exponent. -/
theorem OMA.exponent_ge_deletion_bound {W : Type*} [Fintype W] (J : SimpleGraph W)
    (hJ : 2 ≤ J.edgeFinset.card) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    (OMA.deletionExponent J : ℝ) ≤ α := by
  unfold OMA.deletionExponent
  push_cast
  let x := Fintype.card W - 2
  let d := J.edgeFinset.card - 1
  change 2 - (x : ℝ) / (d : ℝ) ≤ α
  by_contra! hα
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let β := ((2 * d : ℕ) : ℝ) - (x : ℝ) - (d : ℝ) * α
  have hβ : 0 < β := by
    have hx : (x : ℝ) / (d : ℝ) < 2 - α := by linarith
    have hx' := (div_lt_iff₀ hdR).mp hx
    dsimp [β]
    push_cast
    nlinarith only [hx']
  obtain ⟨C, hC⟩ := isBigO_iff.mp hO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  have hlarge : ∀ᶠ a : ℕ in atTop, 64 * C < (a : ℝ) ^ β :=
    ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨a, ha, hlarge'⟩ := ((eventually_ge_atTop (max 2 N)).and hlarge).exists
  have ha2 : 2 ≤ a := (le_max_left _ _).trans ha
  have hap : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hpow : a ≤ a ^ d := by
    calc
      a = a ^ (1 : ℕ) := by simp
      _ ≤ a ^ d := pow_le_pow_right₀ (by omega) hd
  have hN' := hN (a ^ d) ((le_max_right _ _).trans (ha.trans hpow))
  rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (a ^ d)) α)] at hN'
  push_cast at hN'
  have hsplit : (a : ℝ) ^ β =
      (a : ℝ) ^ (2 * d) / ((a : ℝ) ^ x * ((a : ℝ) ^ d) ^ α) := by
    dsimp [β]
    rw [Real.rpow_sub hap, Real.rpow_sub hap, Real.rpow_natCast, Real.rpow_natCast,
      Real.rpow_natCast_mul hap.le, div_div]
  apply (not_le_of_gt hlarge')
  rw [hsplit, div_le_iff₀ (by positivity)]
  calc
    _ ≤ 64 * (a : ℝ) ^ x * (extremalNumber (a ^ d) J : ℝ) :=
      OMA.extremalNumber_power_subseq_lower J hJ ha2
    _ ≤ (64 * (a : ℝ) ^ x) * (C * ((a : ℝ) ^ d) ^ α) :=
      mul_le_mul_of_nonneg_left hN' (by positivity)
    _ = _ := by ring

/-- Minimize the total of vertices and edges among copies that retain the power scale. -/
theorem OMA.exists_minimal_extremalPower {q : ℕ} {G : SimpleGraph (Fin q)} {α : ℝ}
    (hG : OMA.ExtremalPowerOrder G α) :
    ∃ (r : ℕ) (F : SimpleGraph (Fin r)), F ⊑ G ∧ OMA.ExtremalPowerOrder F α ∧
      ∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →
        s + J.edgeFinset.card < r + F.edgeFinset.card →
        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
  let eligible (k : ℕ) : Prop :=
    ∃ (r : ℕ) (F : SimpleGraph (Fin r)),
      r + F.edgeFinset.card = k ∧ F ⊑ G ∧ OMA.ExtremalPowerOrder F α
  have hex : ∃ k, eligible k :=
    ⟨q + G.edgeFinset.card, q, G, rfl, IsContained.refl G, hG⟩
  obtain ⟨r, F, hcard, hFG, hF⟩ := Nat.find_spec hex
  refine ⟨r, F, hFG, hF, fun s J hJF hsmall => ?_⟩
  by_contra hJ
  exact (Nat.not_lt_of_ge (Nat.find_min' hex
    ⟨s, J, rfl, hJF.trans hFG, (OMA.extremalNumber_isBigO_of_contained hJF).trans hF.1, hJ⟩))
      (hsmall.trans_eq hcard)

noncomputable def OMA.tupleCommon {W : Type*} [Fintype W]
    (X : SimpleGraph W) {t : ℕ} (p : Fin t → W) : Finset W :=
  univ.filter fun w => ∀ i, X.Adj (p i) w

theorem OMA.mem_tupleCommon {W : Type*} [Fintype W]
    (X : SimpleGraph W) {t : ℕ} (p : Fin t → W) (v : W) :
    v ∈ OMA.tupleCommon X p ↔ ∀ i, X.Adj (p i) v := by
  simp [OMA.tupleCommon]

private theorem card_tuples_in {W : Type*} [Fintype W] (t : ℕ) (S : Finset W) :
    (univ.filter fun p : Fin t → W => ∀ i, p i ∈ S).card = S.card ^ t := by
  have h : (univ.filter fun p : Fin t → W => ∀ i, p i ∈ S) =
      Fintype.piFinset (fun _ : Fin t => S) := by
    ext p
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  simp

private theorem rich_tuples_of_sample_sum {W : Type*} [Fintype W]
    (X : SimpleGraph W) {t : ℕ} (ht : 0 < t) (s : ℕ) (Q : Finset (Fin t → W))
    (hdense : Fintype.card W ^ t * (s ^ t + s) < ∑ q ∈ Q, (OMA.tupleCommon X q).card) :
    ∃ q ∈ Q, ∃ A : Finset W, A ⊆ OMA.tupleCommon X q ∧ s ≤ A.card ∧
      ∀ p : Fin t → W, (∀ i, p i ∈ A) → s ≤ (OMA.tupleCommon X p).card := by
  let bad : Finset (Fin t → W) := univ.filter fun p => (OMA.tupleCommon X p).card < s
  let inCommon (q : Fin t → W) := bad.filter fun p => ∀ i, p i ∈ OMA.tupleCommon X q
  have hflip (p q : Fin t → W) :
      (∀ i, p i ∈ OMA.tupleCommon X q) ↔ (∀ i, q i ∈ OMA.tupleCommon X p) := by
    simp only [OMA.mem_tupleCommon]
    exact ⟨fun h i j => (h j i).symm, fun h i j => (h j i).symm⟩
  have hbad : (∑ q ∈ Q, (inCommon q).card) ≤ Fintype.card W ^ t * s ^ t := by
    change (∑ q ∈ Q, (bad.filter fun p => ∀ i, p i ∈ OMA.tupleCommon X q).card) ≤ _
    rw [sum_card_filter_swap]
    simp_rw [hflip _ _]
    calc
      _ ≤ ∑ _p ∈ bad, s ^ t := by
        apply sum_le_sum
        intro p hp
        have hsub :
            Q.filter (fun q => ∀ i, q i ∈ OMA.tupleCommon X p) ⊆
              univ.filter (fun q => ∀ i, q i ∈ OMA.tupleCommon X p) :=
          filter_subset_filter _ (subset_univ Q)
        apply (card_le_card hsub).trans
        rw [card_tuples_in]
        exact Nat.pow_le_pow_left (mem_filter.mp hp).2.le t
      _ = bad.card * s ^ t := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by simpa using card_le_univ bad)
  have hex : ∃ q ∈ Q, (inCommon q).card + s < (OMA.tupleCommon X q).card := by
    by_contra! h
    have hsum := sum_le_sum h
    rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
    have hQ : Q.card ≤ Fintype.card W ^ t := by simpa using card_le_univ Q
    rw [Nat.mul_add] at hdense
    exact (not_lt_of_ge (hsum.trans (Nat.add_le_add hbad (Nat.mul_le_mul_right s hQ)))) hdense
  obtain ⟨q, hqQ, hq⟩ := hex
  let removed := (inCommon q).image fun p => p ⟨0, ht⟩
  let A := OMA.tupleCommon X q \ removed
  refine ⟨q, hqQ, A, sdiff_subset, ?_, ?_⟩
  · have hremoved : removed.card ≤ (inCommon q).card := card_image_le
    have hloss := le_card_sdiff removed (OMA.tupleCommon X q)
    change s ≤ (OMA.tupleCommon X q \ removed).card
    omega
  · intro p hp
    by_contra! hfew
    have hpin : p ∈ inCommon q :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hfew⟩, fun i => (mem_sdiff.mp (hp i)).1⟩
    exact (mem_sdiff.mp (hp ⟨0, ht⟩)).2 (mem_image.mpr ⟨p, hpin, rfl⟩)

/-- A moment condition yields a large vertex set whose short tuples have many common neighbors. -/
theorem OMA.rich_tuples_of_degree_moment {W : Type*} [Fintype W]
    (X : SimpleGraph W) {t : ℕ} (ht : 0 < t) (s : ℕ)
    (hdense : Fintype.card W ^ t * (s ^ t + s) < ∑ v, X.degree v ^ t) :
    ∃ A : Finset W, s ≤ A.card ∧ ∀ p : Fin t → W,
      (∀ i, p i ∈ A) → s ≤ (OMA.tupleCommon X p).card := by
  have htotal : (∑ q : Fin t → W, (OMA.tupleCommon X q).card) = ∑ v, X.degree v ^ t := by
    simp only [OMA.tupleCommon]
    rw [sum_card_filter_swap]
    have hfiber (v : W) :
        (univ.filter fun p : Fin t → W => ∀ i, X.Adj (p i) v).card = X.degree v ^ t := by
      simpa only [mem_neighborFinset, X.adj_comm v, card_neighborFinset_eq_degree] using
        card_tuples_in t (X.neighborFinset v)
    simp_rw [hfiber]
  obtain ⟨_, _, A, _, hA, hrich⟩ :=
    rich_tuples_of_sample_sum X ht s univ (htotal.symm ▸ hdense)
  exact ⟨A, hA, hrich⟩

private theorem card_injective_tuples_in {W : Type*} [Fintype W] (t : ℕ) (S : Finset W) :
    ((univ.filter Function.Injective).filter fun p : Fin t → W => ∀ i, p i ∈ S).card =
      S.card.descFactorial t := by
  let T := (univ.filter Function.Injective).filter fun p : Fin t → W => ∀ i, p i ∈ S
  have hEquiv : T ≃ (Fin t ↪ S) := {
    toFun := fun p => ⟨fun i => ⟨p.val i, (mem_filter.mp p.property).2 i⟩,
      fun i j hij => (mem_filter.mp (mem_filter.mp p.property).1).2 (congrArg Subtype.val hij)⟩
    invFun := fun p => ⟨fun i => (p i).val, by
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, fun i => (p i).property⟩
      intro i j hij
      exact p.injective (Subtype.ext hij)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  simpa only [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_fin] using Fintype.card_congr hEquiv

/-- The rich set can be chosen inside the common neighborhood of an injective sample. -/
theorem OMA.rich_tuples_of_descending_degree_moment {W : Type*} [Fintype W]
    (X : SimpleGraph W) {t : ℕ} (ht : 0 < t) (s : ℕ)
    (hdense : Fintype.card W ^ t * (s ^ t + s) < ∑ v, (X.degree v).descFactorial t) :
    ∃ q : Fin t ↪ W, ∃ A : Finset W, A ⊆ OMA.tupleCommon X q ∧ s ≤ A.card ∧
      ∀ p : Fin t → W, (∀ i, p i ∈ A) → s ≤ (OMA.tupleCommon X p).card := by
  let Q : Finset (Fin t → W) := univ.filter Function.Injective
  have hmoment : (∑ q ∈ Q, (OMA.tupleCommon X q).card) = ∑ v, (X.degree v).descFactorial t := by
    simp only [OMA.tupleCommon]
    rw [sum_card_filter_swap]
    have hfiber (v : W) :
        (Q.filter fun p : Fin t → W => ∀ i, X.Adj (p i) v).card =
          (X.degree v).descFactorial t := by
      simpa only [Q, mem_neighborFinset, X.adj_comm v, card_neighborFinset_eq_degree] using
        card_injective_tuples_in t (X.neighborFinset v)
    simp_rw [hfiber]
  obtain ⟨q, hq, A, hsub, hA, hrich⟩ :=
    rich_tuples_of_sample_sum X ht s Q (hmoment.symm ▸ hdense)
  exact ⟨⟨q, (mem_filter.mp hq).2⟩, A, hsub, hA, hrich⟩

private theorem contained_of_rich_tuples_with_exceptional {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V)
    (E : Finset {v : V // v ∉ R}) (m : E ↪ W) {t s : ℕ}
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ E, F.degree v.val ≤ t) (ht : t ≤ s) (hs : Fintype.card V ≤ s)
    {A : Finset W} (hA : s ≤ A.card)
    (hrich : ∀ p : Fin t → W, (∀ i, p i ∈ A) → s ≤ (OMA.tupleCommon X p).card)
    (hattach : ∀ x : E, ∀ w ∈ A, X.Adj (m x) w) :
    F ⊑ X := by
  let L := {v : V // v ∉ R}
  let U := {v : L // v ∉ E}
  let eL : E ⊕ U ≃ L := Equiv.sumCompl (fun v => v ∈ E)
  let e : R ⊕ (E ⊕ U) ≃ V :=
    (Equiv.sumCongr (Equiv.refl R) eL).trans (Equiv.sumCompl (fun v => v ∈ R))
  have hfit : R.card ≤ A.card := (card_le_univ R).trans (hs.trans hA)
  let j : R ↪ A :=
    R.equivFin.toEmbedding.trans ((Fin.castLEEmb hfit).trans A.equivFin.symm.toEmbedding)
  let f : R ↪ W := j.trans (Function.Embedding.subtype _)
  let D : Finset W := univ.map f ∪ univ.map m
  let neighbors (v : U) : Finset R := univ.filter fun u => F.Adj v.val.val u.val
  let choices (v : U) : Finset W := (univ.filter fun w => ∀ u ∈ neighbors v, X.Adj (f u) w) \ D
  have huniv : D.card + Fintype.card U ≤ Fintype.card V := by
    have hD := card_union_le (univ.map f) (univ.map m)
    simp only [card_map, card_univ] at hD
    have hV := Fintype.card_congr e
    simp only [Fintype.card_sum] at hV
    change (univ.map f ∪ univ.map m).card + Fintype.card U ≤ _
    omega
  have hchoices (v : U) : Fintype.card U ≤ (choices v).card := by
    let B := (neighbors v).map f
    have hBA : B ⊆ A := by
      intro w hw
      obtain ⟨u, _, rfl⟩ := mem_map.mp hw
      exact (j u).property
    have hB : B.card ≤ t := by
      rw [card_map]
      let incl : R ↪ V := Function.Embedding.subtype _
      have hsub : (neighbors v).map incl ⊆ F.neighborFinset v.val.val := by
        intro x hx
        obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
        exact (F.mem_neighborFinset _ _).mpr (mem_filter.mp hu).2
      have hc := card_le_card hsub
      rw [card_map, card_neighborFinset_eq_degree] at hc
      exact hc.trans (hdeg v.val v.property)
    obtain ⟨T, hBT, hTA, hT⟩ := exists_subsuperset_card_eq hBA hB (ht.trans hA)
    let b : T ≃ Fin t := T.equivFin.trans (finCongr hT)
    let p (i : Fin t) : W := (b.symm i).val
    have hp : ∀ i, p i ∈ A := fun i => hTA (b.symm i).property
    have hcom : OMA.tupleCommon X p \ D ⊆ choices v := by
      intro w hw
      obtain ⟨hw, hD⟩ := mem_sdiff.mp hw
      refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, hD⟩
      intro u hu
      have hfu : f u ∈ T := hBT (mem_map.mpr ⟨u, hu, rfl⟩)
      have he := (OMA.mem_tupleCommon X p w).mp hw (b ⟨f u, hfu⟩)
      simpa [p] using he
    have hloss := le_card_sdiff D (OMA.tupleCommon X p)
    have hsize := card_le_card hcom
    have hrich' := hrich p hp
    omega
  obtain ⟨g, hg, hgchoice⟩ := (all_card_le_biUnion_card_iff_exists_injective choices).mp (by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · exact (card_le_univ S).trans ((hchoices v).trans (card_le_card (subset_biUnion_of_mem choices hv))))
  have hmoff (x : E) (y : U) : m x ≠ g y := by
    intro h
    apply (mem_sdiff.mp (hgchoice y)).2
    exact mem_union_right _ (mem_map.mpr ⟨x, mem_univ _, h⟩)
  let mix : E ⊕ U → W := Sum.elim m g
  have hmix : Function.Injective mix := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (m.injective h)
    · exact (hmoff x y h).elim
    · exact (hmoff y x h.symm).elim
    · exact congrArg Sum.inr (hg h)
  have hfoff (x : R) (y : E ⊕ U) : f x ≠ mix y := by
    cases y with
    | inl y => exact (hattach y (f x) (j x).property).ne.symm
    | inr y =>
      intro h
      apply (mem_sdiff.mp (hgchoice y)).2
      exact mem_union_left _ (mem_map.mpr ⟨x, mem_univ _, h⟩)
  let join : R ⊕ (E ⊕ U) → W := Sum.elim f mix
  have hinj : Function.Injective join := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (f.injective h)
    · exact (hfoff x y h).elim
    · exact (hfoff y x h.symm).elim
    · exact congrArg Sum.inr (hmix h)
  have hcross (u : E ⊕ U) (v : R) (h : F.Adj (e (.inr u)) v.val) :
      X.Adj (mix u) (f v) := by
    cases u with
    | inl w => exact hattach w (f v) (j v).property
    | inr w =>
      have hmem : v ∈ neighbors w := mem_filter.mpr ⟨mem_univ _, h⟩
      exact ((mem_filter.mp (mem_sdiff.mp (hgchoice w)).1).2 v hmem).symm
  have hpres : ∀ u v : R ⊕ (E ⊕ U), F.Adj (e u) (e v) → X.Adj (join u) (join v) := by
    rintro (u | u) (v | v) h
    · exact ((hcolors h).mp u.property v.property).elim
    · exact (hcross v u h.symm).symm
    · exact hcross u v h
    · exact ((eL u).property ((hcolors h).mpr (eL v).property)).elim
  refine ⟨⟨⟨join ∘ e.symm, ?_⟩, hinj.comp e.symm.injective⟩⟩
  intro u v huv
  simpa using hpres (e.symm u) (e.symm v) (by simpa using huv)

private theorem contained_of_rich_tuples {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V) {t s : ℕ}
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ R, F.degree v ≤ t) (ht : t ≤ s) (hs : Fintype.card V ≤ s)
    {A : Finset W} (hA : s ≤ A.card)
    (hrich : ∀ p : Fin t → W, (∀ i, p i ∈ A) → s ≤ (OMA.tupleCommon X p).card) :
    F ⊑ X := by
  let E : Finset {v : V // v ∉ R} := ∅
  let m : E ↪ W := ⟨fun v => (notMem_empty v.val v.property).elim,
    fun v => (notMem_empty v.val v.property).elim⟩
  exact contained_of_rich_tuples_with_exceptional F X R E m hcolors
    (fun v _ => hdeg v.val v.property) ht hs hA hrich
    (fun v => (notMem_empty v.val v.property).elim)

/-- The one-sided degree bound forces a uniform bound for the degree moment of a free host. -/
theorem OMA.degree_side_moment_bound {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ R, F.degree v ≤ t) (hfree : F.Free X) :
    let s := max t (Fintype.card V)
    (∑ v, X.degree v ^ t) ≤ Fintype.card W ^ t * (s ^ t + s) := by
  intro s
  by_contra! h
  obtain ⟨A, hA, hrich⟩ := OMA.rich_tuples_of_degree_moment X ht s h
  exact hfree (contained_of_rich_tuples F X R hcolors hdeg (le_max_left _ _) (le_max_right _ _) hA hrich)

/-- Up to t vertices on the degree-bounded side may have unrestricted degrees. -/
theorem OMA.degree_side_descending_moment_bound {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (E : Finset {v : V // v ∉ R}) (hE : E.card ≤ t)
    (hdeg : ∀ v ∉ E, F.degree v.val ≤ t) (hfree : F.Free X) :
    let s := max t (Fintype.card V)
    (∑ v, (X.degree v).descFactorial t) ≤ Fintype.card W ^ t * (s ^ t + s) := by
  intro s
  by_contra! h
  obtain ⟨q, A, hsub, hA, hrich⟩ := OMA.rich_tuples_of_descending_degree_moment X ht s h
  let k : E ↪ Fin t := E.equivFin.toEmbedding.trans (Fin.castLEEmb hE)
  let m : E ↪ W := k.trans q
  apply hfree (contained_of_rich_tuples_with_exceptional F X R E m hcolors hdeg
    (le_max_left _ _) (le_max_right _ _) hA hrich ?_)
  intro x w hw
  exact (OMA.mem_tupleCommon X q w).mp (hsub hw) (k x)

private theorem degree_moment_le_of_descending {W : Type*} [Fintype W] (X : SimpleGraph W)
    {t C : ℕ} (ht : 0 < t) (hn : 0 < Fintype.card W)
    (hdesc : (∑ v, (X.degree v).descFactorial t) ≤ Fintype.card W ^ t * C) :
    (∑ v, X.degree v ^ t) ≤ Fintype.card W ^ t * (2 ^ t * (C + t ^ t)) := by
  have hterm (d : ℕ) : d ^ t ≤ 2 ^ t * (d.descFactorial t + t ^ t) := by
    have hd : d ≤ 2 * max (d - t) t := by
      have h₁ := le_max_left (d - t) t
      have h₂ := le_max_right (d - t) t
      omega
    have htrunc : (d - t) ^ t ≤ d.descFactorial t :=
      (Nat.pow_le_pow_left (by omega) t).trans (Nat.pow_sub_le_descFactorial d t)
    calc
      _ ≤ (2 * max (d - t) t) ^ t := Nat.pow_le_pow_left hd t
      _ = 2 ^ t * (max (d - t) t) ^ t := mul_pow _ _ _
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        rcases le_total (d - t) t with h | h
        · rw [max_eq_right h]
          exact Nat.le_add_left _ _
        · rw [max_eq_left h]
          exact htrunc.trans (Nat.le_add_right _ _)
  let n := Fintype.card W
  have hnle : n ≤ n ^ t := by
    calc
      n = n ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hn ht
  calc
    (∑ v, X.degree v ^ t) ≤ ∑ v, 2 ^ t * ((X.degree v).descFactorial t + t ^ t) :=
      sum_le_sum fun v _ => hterm _
    _ = 2 ^ t * ((∑ v, (X.degree v).descFactorial t) + n * t ^ t) := by
      rw [← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      simp [n]
    _ ≤ 2 ^ t * (n ^ t * C + n ^ t * t ^ t) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add hdesc (Nat.mul_le_mul_right _ hnle))
    _ = _ := by simp only [← Nat.mul_add]; ac_rfl

private theorem edge_bound_of_degree_moment {W : Type*} [Fintype W] (X : SimpleGraph W)
    (hn : 0 < Fintype.card W) {t C : ℕ} (ht : 0 < t) (hC : 0 < C)
    (hmoment : (∑ v, X.degree v ^ t) ≤ Fintype.card W ^ t * C) :
    (X.edgeFinset.card : ℝ) ≤ (C : ℝ) * (Fintype.card W : ℝ) ^ (2 - 1 / (t : ℝ)) := by
  let n : ℝ := Fintype.card W
  let β : ℝ := 1 - 1 / (t : ℝ)
  have hnpos : 0 < n := Nat.cast_pos.mpr hn
  have htpos : 0 < (t : ℝ) := by exact_mod_cast ht
  have hmean := Real.pow_arith_mean_le_arith_mean_pow (univ : Finset W) (fun _ => n⁻¹)
      (fun v => (X.degree v : ℝ)) (fun _ _ => by positivity)
      (by simp [n, hnpos.ne'])
      (fun _ _ => by positivity) t
  simp_rw [← mul_sum] at hmean
  have hhand : (∑ v, (X.degree v : ℝ)) = 2 * (X.edgeFinset.card : ℝ) := by
    exact_mod_cast X.sum_degrees_eq_twice_card_edges
  rw [hhand] at hmean
  have hm : (∑ v, (X.degree v : ℝ) ^ t) ≤ n ^ t * C := by
    dsimp only [n]
    exact_mod_cast hmoment
  have hb : (n ^ β) ^ t = n ^ t / n := by
    rw [← Real.rpow_natCast (n ^ β) t, ← Real.rpow_mul hnpos.le,
      show β * (t : ℝ) = (t : ℝ) - 1 by dsimp [β]; field_simp,
      Real.rpow_sub hnpos, Real.rpow_natCast, Real.rpow_one]
  have hCpow : (C : ℝ) ≤ (C : ℝ) ^ t := by
    calc
      (C : ℝ) = (C : ℝ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hC) ht
  have hroot : (2 * (X.edgeFinset.card : ℝ) / n) ^ t ≤ ((C : ℝ) * n ^ β) ^ t := by
    calc
      _ = (n⁻¹ * (2 * (X.edgeFinset.card : ℝ))) ^ t := by rw [div_eq_inv_mul]
      _ ≤ n⁻¹ * (n ^ t * C) := hmean.trans (mul_le_mul_of_nonneg_left hm (by positivity))
      _ = (C : ℝ) * (n ^ β) ^ t := by rw [hb, div_eq_mul_inv]; ring
      _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hCpow (by positivity)
  have hlin : 2 * (X.edgeFinset.card : ℝ) / n ≤ (C : ℝ) * n ^ β :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) ht.ne').mp hroot
  have he : (C : ℝ) * n ^ β * n = (C : ℝ) * n ^ (2 - 1 / (t : ℝ)) := by
    calc
      _ = (C : ℝ) * (n ^ β * n ^ (1 : ℝ)) := by rw [Real.rpow_one, mul_assoc]
      _ = _ := by
        rw [← Real.rpow_add hnpos]
        congr 2
        dsimp [β]
        ring
  have h := (div_le_iff₀ hnpos).mp hlin
  rw [he] at h
  change (X.edgeFinset.card : ℝ) ≤ (C : ℝ) * n ^ (2 - 1 / (t : ℝ))
  linarith only [h, Nat.cast_nonneg (α := ℝ) X.edgeFinset.card]

/-- A bipartition with degree at most t on one side gives an extremal bound of order n^(2 − 1/t). -/
theorem OMA.extremalNumber_le_degree_side_power {V : Type*} [Fintype V]
    (F : SimpleGraph V) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ R, F.degree v ≤ t) (hF : F ≠ ⊥) {n : ℕ} (hn : 0 < n) :
    let s := max t (Fintype.card V)
    (extremalNumber n F : ℝ) ≤ ((s ^ t + s : ℕ) : ℝ) * (n : ℝ) ^ (2 - 1 / (t : ℝ)) := by
  intro s
  obtain ⟨X, _, hX⟩ := exists_isExtremal_free (V := Fin n) hF
  obtain ⟨hfree, he⟩ := isExtremal_free_iff.mp hX
  rw [Fintype.card_fin] at he
  have hs : 0 < s := ht.trans_le (le_max_left _ _)
  have hC : 0 < s ^ t + s := by omega
  rw [← he]
  have h := edge_bound_of_degree_moment X (by simpa using hn) ht hC
    (OMA.degree_side_moment_bound F X R ht hcolors hdeg hfree)
  simp only [Fintype.card_fin] at h
  convert! h

private theorem exponent_le_of_extremal_bound {V : Type*} (F : SimpleGraph V)
    {C α β : ℝ} (hα : OMA.ExtremalPowerOrder F α)
    (hbound : ∀ {n : ℕ}, 0 < n → (extremalNumber n F : ℝ) ≤ C * (n : ℝ) ^ β) :
    α ≤ β := by
  by_contra! hgt
  have hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ β) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact hbound hn
  have hsmall : (fun n : ℕ => (n : ℝ) ^ β) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) :=
      (eventually_gt_atTop (0 : ℕ)).mono fun n hn => by exact_mod_cast hn
    apply (isLittleO_iff_tendsto' (hpos.mono fun n hn hzero =>
      ((Real.rpow_pos_of_pos hn α).ne' hzero).elim)).2
    refine ((tendsto_rpow_neg_atTop (sub_pos.mpr hgt)).comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [hpos] with n hn
    change (n : ℝ) ^ (-(α - β)) = _
    rw [neg_sub, Real.rpow_sub hn]
  exact hα.2 (hO.trans_isLittleO hsmall)

theorem OMA.exponent_le_degree_side_bound {V : Type*} [Fintype V]
    (F : SimpleGraph V) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ R, F.degree v ≤ t) (hF : F ≠ ⊥)
    {α : ℝ} (hα : OMA.ExtremalPowerOrder F α) :
    α ≤ 2 - 1 / (t : ℝ) := by
  exact exponent_le_of_extremal_bound F hα
    (fun hn => OMA.extremalNumber_le_degree_side_power F R ht hcolors hdeg hF hn)

/-- The exceptional vertices preserve the upper exponent 2 − 1/t. -/
theorem OMA.extremalNumber_le_exceptional_degree_side_power {V : Type*} [Fintype V]
    (F : SimpleGraph V) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (E : Finset {v : V // v ∉ R}) (hE : E.card ≤ t)
    (hdeg : ∀ v ∉ E, F.degree v.val ≤ t) (hF : F ≠ ⊥) {n : ℕ} (hn : 0 < n) :
    let s := max t (Fintype.card V)
    (extremalNumber n F : ℝ) ≤ ((2 ^ t * (s ^ t + s + t ^ t) : ℕ) : ℝ) *
      (n : ℝ) ^ (2 - 1 / (t : ℝ)) := by
  intro s
  obtain ⟨X, _, hX⟩ := exists_isExtremal_free (V := Fin n) hF
  obtain ⟨hfree, he⟩ := isExtremal_free_iff.mp hX
  rw [Fintype.card_fin] at he
  have hC : 0 < 2 ^ t * (s ^ t + s + t ^ t) :=
    Nat.mul_pos (by positivity) (by have hs : 0 < s := ht.trans_le (le_max_left _ _); omega)
  have hnX : 0 < Fintype.card (Fin n) := by simpa using hn
  have hm := degree_moment_le_of_descending X ht hnX
    (OMA.degree_side_descending_moment_bound F X R ht hcolors E hE hdeg hfree)
  rw [← he]
  have h := edge_bound_of_degree_moment X hnX ht hC hm
  simp only [Fintype.card_fin] at h
  convert! h

theorem OMA.exponent_le_exceptional_degree_side_bound {V : Type*} [Fintype V]
    (F : SimpleGraph V) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (E : Finset {v : V // v ∉ R}) (hE : E.card ≤ t)
    (hdeg : ∀ v ∉ E, F.degree v.val ≤ t) (hF : F ≠ ⊥)
    {α : ℝ} (hα : OMA.ExtremalPowerOrder F α) :
    α ≤ 2 - 1 / (t : ℝ) := by
  exact exponent_le_of_extremal_bound F hα
    (fun hn => OMA.extremalNumber_le_exceptional_degree_side_power F R ht hcolors E hE hdeg hF hn)

private theorem ne_bot_of_extremalPowerOrder {r : ℕ} (F : SimpleGraph (Fin r))
    {α : ℝ} (hF : OMA.ExtremalPowerOrder F α) : F ≠ ⊥ := by
  intro hbot
  apply hF.2
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [eventually_ge_atTop r] with n hn
  have h : extremalNumber n F ≤ 0 := by
    rw [← Fintype.card_fin n, extremalNumber_le_iff]
    intro X _ hfree
    exact (hfree (by rw [hbot, bot_isContained_iff_card_le]; simpa using hn)).elim
  simp only [Nat.le_zero.mp h, Nat.cast_zero, norm_zero]
  positivity

private def affineIncidence {K : Type*} [Field K] (a b : K × K) : Prop :=
  a.2 + b.2 = a.1 * b.1

private def affineBipartiteGraph (K : Type*) [Field K] : SimpleGraph ((K × K) ⊕ (K × K)) where
  Adj a b := match a, b with
    | .inl x, .inr y | .inr x, .inl y => affineIncidence x y
    | _, _ => False
  symm := by
    refine ⟨?_⟩
    rintro (x | x) (y | y) h
    all_goals first | exact h | simpa [affineIncidence, add_comm, mul_comm] using h
  loopless := by
    refine ⟨?_⟩
    rintro (x | x) h <;> exact h

private theorem affine_common_unique {K : Type*} [Field K]
    {a b u v : K × K} (hab : a ≠ b)
    (hau : affineIncidence a u) (hbu : affineIncidence b u)
    (hav : affineIncidence a v) (hbv : affineIncidence b v) : u = v := by
  unfold affineIncidence at *
  have hfst : a.1 ≠ b.1 := by
    intro h
    apply hab
    have hs : a.2 = b.2 := by
      rw [h] at hau
      exact add_right_cancel (hau.trans hbu.symm)
    exact Prod.ext h hs
  have hzero : (a.1 - b.1) * (u.1 - v.1) = 0 := by
    linear_combination hbu - hau + hav - hbv
  have h : u.1 = v.1 := sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hfst))
  apply Prod.ext h
  rw [h] at hau
  exact add_left_cancel (hau.trans hav.symm)

private theorem affineBipartiteGraph_free (K : Type*) [Field K] :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free (affineBipartiteGraph K) := by
  let X := affineBipartiteGraph K
  have hcommon : ∀ a b u v, a ≠ b →
      X.Adj a u → X.Adj b u → X.Adj a v → X.Adj b v → u = v := by
    rintro (a | a) (b | b) (u | u) (v | v) hab hau hbu hav hbv
    all_goals simp_all [X, affineBipartiteGraph]
    all_goals exact affine_common_unique hab hau hbu hav hbv
  intro h
  let f := h.some
  have hadj (i j : Fin 2) : X.Adj (f (.inl i)) (f (.inr j)) :=
    f.toHom.map_rel' (Or.inl ⟨rfl, rfl⟩)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hne : f (.inl 0) ≠ f (.inl 1) := fun h => h01 (Sum.inl.inj (f.injective h))
  have heq := hcommon _ _ _ _ hne (hadj 0 0) (hadj 1 0) (hadj 0 1) (hadj 1 1)
  exact h01 (Sum.inr.inj (f.injective heq))

private theorem affineBipartiteGraph_edges (K : Type*) [Field K] [Fintype K] :
    Fintype.card K ^ 3 ≤ (affineBipartiteGraph K).edgeFinset.card := by
  let X := affineBipartiteGraph K
  let fn : (K × K) × K → X.edgeFinset := fun z =>
    ⟨s(Sum.inl z.1, Sum.inr (z.2, z.1.1 * z.2 - z.1.2)), by
      apply mem_edgeFinset.mpr
      change z.1.2 + (z.1.1 * z.2 - z.1.2) = z.1.1 * z.2
      ring⟩
  have hinj : Function.Injective fn := by
    intro a b h
    have he := Sym2.eq_iff.mp (congrArg Subtype.val h)
    rcases he with ⟨hl, hr⟩ | ⟨hl, _⟩
    · exact Prod.ext (Sum.inl.inj hl) (congrArg Prod.fst (Sum.inr.inj hr))
    · exact (Sum.inl_ne_inr hl).elim
  simpa only [Fintype.card_coe, Fintype.card_prod, pow_succ, pow_zero, one_mul] using
    Fintype.card_le_of_injective fn hinj

/-- The affine incidence graphs give the four-cycle lower bound on a prime subsequence. -/
theorem OMA.cycle_four_extremal_subseq {p : ℕ} (hp : p.Prime) :
    p ^ 3 ≤ extremalNumber (2 * p ^ 2) (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h := (affineBipartiteGraph_edges (ZMod p)).trans
    (card_edgeFinset_le_extremalNumber (affineBipartiteGraph_free (ZMod p)))
  simpa [Fintype.card_sum, Fintype.card_prod, ZMod.card, two_mul, pow_two] using h

theorem OMA.exponent_ge_cycle_four {W : Type*} {F : SimpleGraph W}
    (hC4 : completeBipartiteGraph (Fin 2) (Fin 2) ⊑ F) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    (3 / 2 : ℝ) ≤ α := by
  by_contra! hα
  obtain ⟨C, hC⟩ := isBigO_iff.mp hO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  have hβ : 0 < 3 - 2 * α := by linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, C * (2 : ℝ) ^ α < (n : ℝ) ^ (3 - 2 * α) :=
    ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨M, hM⟩ := eventually_atTop.mp hlarge
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max M N)
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hprime.pos
  have hpN : N ≤ 2 * p ^ 2 :=
    (le_max_right _ _).trans (hp.trans (by nlinarith only [hprime.two_le]))
  have hupper := hN _ hpN
  rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hupper
  push_cast at hupper
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hp0.le] at hupper
  have hlower : (p : ℝ) ^ (3 : ℕ) ≤ (extremalNumber (2 * p ^ 2) F : ℝ) := by
    exact_mod_cast ((OMA.cycle_four_extremal_subseq hprime).trans hC4.extremalNumber_le)
  have hle := hlower.trans hupper
  have hlt := hM p ((le_max_left _ _).trans hp)
  rw [Real.rpow_sub hp0, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast,
    lt_div_iff₀ (Real.rpow_pos_of_pos hp0 _)] at hlt
  exact (not_lt_of_ge hle) (by simpa [mul_assoc] using hlt)

private def quadraticIncidence {K : Type*} [Field K] (p l : K × K × K) : Prop :=
  p.2.1 + l.2.1 = p.1 * l.1 ∧ p.2.2 + l.2.2 = p.1 * l.1 ^ 2

private def quadraticBipartiteGraph (K : Type*) [Field K] :
    SimpleGraph ((K × K × K) ⊕ (K × K × K)) where
  Adj a b := match a, b with
    | .inl p, .inr l | .inr l, .inl p => quadraticIncidence p l
    | _, _ => False
  symm := by
    refine ⟨?_⟩
    rintro (a | a) (b | b) h <;> exact h
  loopless := by
    refine ⟨?_⟩
    rintro (a | a) h <;> exact h

private theorem quadratic_incident_line_eq {K : Type*} [Field K] {p l m : K × K × K}
    (hl : quadraticIncidence p l) (hm : quadraticIncidence p m) (h : l.1 = m.1) :
    l = m := by
  obtain ⟨hl₁, hl₂⟩ := hl
  obtain ⟨hm₁, hm₂⟩ := hm
  rw [h] at hl₁ hl₂
  exact Prod.ext h (Prod.ext (add_left_cancel (hl₁.trans hm₁.symm))
    (add_left_cancel (hl₂.trans hm₂.symm)))

private theorem quadratic_incident_point_eq {K : Type*} [Field K] {a b l : K × K × K}
    (ha : quadraticIncidence a l) (hb : quadraticIncidence b l) (h : a.1 = b.1) :
    a = b := by
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  rw [h] at ha₁ ha₂
  exact Prod.ext h (Prod.ext (add_right_cancel (ha₁.trans hb₁.symm))
    (add_right_cancel (ha₂.trans hb₂.symm)))

/-- The three slopes around an alternating six-cycle would force two points to coincide. -/
private theorem quadratic_no_six_incidence {K : Type*} [Field K]
    {a b c l m n : K × K × K} (hlm : l ≠ m) (hln : l ≠ n)
    (hal : quadraticIncidence a l) (hbl : quadraticIncidence b l)
    (hbm : quadraticIncidence b m) (hcm : quadraticIncidence c m)
    (hcn : quadraticIncidence c n) (han : quadraticIncidence a n) :
    a = b := by
  have hlm' : l.1 - m.1 ≠ 0 := sub_ne_zero.mpr fun h =>
    hlm (quadratic_incident_line_eq hbl hbm h)
  have hln' : l.1 - n.1 ≠ 0 := sub_ne_zero.mpr fun h =>
    hln (quadratic_incident_line_eq hal han h)
  have h₁ : (a.1 - b.1) * (l.1 - n.1) + (b.1 - c.1) * (m.1 - n.1) = 0 := by
    linear_combination hbl.1 - hal.1 + hcm.1 - hbm.1 + han.1 - hcn.1
  have h₂ : (a.1 - b.1) * (l.1 ^ 2 - n.1 ^ 2) +
      (b.1 - c.1) * (m.1 ^ 2 - n.1 ^ 2) = 0 := by
    linear_combination hbl.2 - hal.2 + hcm.2 - hbm.2 + han.2 - hcn.2
  have h₃ : (a.1 - b.1) * (l.1 - n.1) * (l.1 - m.1) = 0 := by
    linear_combination h₂ - (m.1 + n.1) * h₁
  exact quadratic_incident_point_eq hal hbl
    (sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp h₃).resolve_right hlm')).resolve_right hln'))

private theorem quadratic_neighbor_of_point {K : Type*} [Field K]
    {p : K × K × K} {x : (K × K × K) ⊕ (K × K × K)}
    (h : (quadraticBipartiteGraph K).Adj (.inl p) x) :
    ∃ l, x = .inr l ∧ quadraticIncidence p l := by
  cases x with
  | inl a => exact h.elim
  | inr l => exact ⟨l, rfl, h⟩

private theorem quadratic_neighbor_of_line {K : Type*} [Field K]
    {l : K × K × K} {x : (K × K × K) ⊕ (K × K × K)}
    (h : (quadraticBipartiteGraph K).Adj (.inr l) x) :
    ∃ p, x = .inl p ∧ quadraticIncidence p l := by
  cases x with
  | inl p => exact ⟨p, rfl, h⟩
  | inr a => exact h.elim

private theorem quadratic_no_six_from_point {K : Type*} [Field K]
    {a : K × K × K} {v₁ v₂ v₃ v₄ v₅ : (K × K × K) ⊕ (K × K × K)}
    (h₀₁ : (quadraticBipartiteGraph K).Adj (.inl a) v₁)
    (h₁₂ : (quadraticBipartiteGraph K).Adj v₁ v₂)
    (h₂₃ : (quadraticBipartiteGraph K).Adj v₂ v₃)
    (h₃₄ : (quadraticBipartiteGraph K).Adj v₃ v₄)
    (h₄₅ : (quadraticBipartiteGraph K).Adj v₄ v₅)
    (h₅₀ : (quadraticBipartiteGraph K).Adj v₅ (.inl a))
    (h₀₂ : Sum.inl a ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₁₅ : v₁ ≠ v₅) : False := by
  obtain ⟨l, rfl, hal⟩ := quadratic_neighbor_of_point h₀₁
  obtain ⟨b, rfl, hbl⟩ := quadratic_neighbor_of_line h₁₂
  obtain ⟨m, rfl, hbm⟩ := quadratic_neighbor_of_point h₂₃
  obtain ⟨c, rfl, hcm⟩ := quadratic_neighbor_of_line h₃₄
  obtain ⟨n, rfl, hcn⟩ := quadratic_neighbor_of_point h₄₅
  exact h₀₂ (congrArg Sum.inl (quadratic_no_six_incidence
    (fun h => h₁₃ (congrArg Sum.inr h)) (fun h => h₁₅ (congrArg Sum.inr h))
    hal hbl hbm hcm hcn h₅₀))

private theorem quadraticBipartiteGraph_free (K : Type*) [Field K] :
    (cycleGraph 6).Free (quadraticBipartiteGraph K) := by
  intro h
  let f := h.some
  have hadj (i : Fin 6) : (quadraticBipartiteGraph K).Adj (f i) (f (i + 1)) :=
    f.toHom.map_rel' (cycleGraph_adj.mpr (Or.inr (add_sub_cancel_left i 1)))
  have h₀₁ : (quadraticBipartiteGraph K).Adj (f 0) (f 1) := hadj 0
  have h₁₂ : (quadraticBipartiteGraph K).Adj (f 1) (f 2) := hadj 1
  have h₂₃ : (quadraticBipartiteGraph K).Adj (f 2) (f 3) := hadj 2
  have h₃₄ : (quadraticBipartiteGraph K).Adj (f 3) (f 4) := hadj 3
  have h₄₅ : (quadraticBipartiteGraph K).Adj (f 4) (f 5) := hadj 4
  have h₅₀ : (quadraticBipartiteGraph K).Adj (f 5) (f 0) := hadj 5
  have h₀₂ : f 0 ≠ f 2 := fun he => (by decide : (0 : Fin 6) ≠ 2) (f.injective he)
  have h₁₃ : f 1 ≠ f 3 := fun he => (by decide : (1 : Fin 6) ≠ 3) (f.injective he)
  have h₁₅ : f 1 ≠ f 5 := fun he => (by decide : (1 : Fin 6) ≠ 5) (f.injective he)
  have h₂₄ : f 2 ≠ f 4 := fun he => (by decide : (2 : Fin 6) ≠ 4) (f.injective he)
  have h₂₀ : f 2 ≠ f 0 := h₀₂.symm
  cases h₀ : f 0 with
  | inl a =>
    rw [h₀] at h₀₁ h₅₀ h₀₂
    exact quadratic_no_six_from_point h₀₁ h₁₂ h₂₃ h₃₄ h₄₅ h₅₀ h₀₂ h₁₃ h₁₅
  | inr l =>
    rw [h₀] at h₀₁
    obtain ⟨a, h₁, _⟩ := quadratic_neighbor_of_line h₀₁
    rw [h₁] at h₁₂ h₁₃
    have h₀₁' : (quadraticBipartiteGraph K).Adj (f 0) (.inl a) := by
      simpa only [h₀, h₁] using h₀₁
    exact quadratic_no_six_from_point h₁₂ h₂₃ h₃₄ h₄₅ h₅₀ h₀₁' h₁₃ h₂₄ h₂₀

private theorem quadraticBipartiteGraph_edges (K : Type*) [Field K] [Fintype K] :
    Fintype.card K ^ 4 ≤ (quadraticBipartiteGraph K).edgeFinset.card := by
  let X := quadraticBipartiteGraph K
  let fn : (K × K × K) × K → X.edgeFinset := fun z =>
    ⟨s(.inl z.1, .inr (z.2, z.1.1 * z.2 - z.1.2.1, z.1.1 * z.2 ^ 2 - z.1.2.2)), by
      apply mem_edgeFinset.mpr
      change quadraticIncidence z.1 (z.2, _, _)
      constructor <;> dsimp <;> ring⟩
  have hinj : Function.Injective fn := by
    intro a b h
    have he := Sym2.eq_iff.mp (congrArg Subtype.val h)
    rcases he with ⟨hl, hr⟩ | ⟨hl, _⟩
    · exact Prod.ext (Sum.inl.inj hl) (congrArg Prod.fst (Sum.inr.inj hr))
    · exact (Sum.inl_ne_inr hl).elim
  simpa only [Fintype.card_coe, Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc]
    using Fintype.card_le_of_injective fn hinj

/-- The quadratic incidence graphs give the six-cycle lower bound on a prime subsequence. -/
theorem OMA.cycle_six_extremal_subseq {p : ℕ} (hp : p.Prime) :
    p ^ 4 ≤ extremalNumber (2 * p ^ 3) (cycleGraph 6) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h := (quadraticBipartiteGraph_edges (ZMod p)).trans
    (card_edgeFinset_le_extremalNumber (quadraticBipartiteGraph_free (ZMod p)))
  simpa [Fintype.card_sum, Fintype.card_prod, ZMod.card, two_mul, pow_succ, mul_assoc] using h

private theorem exponent_ge_of_large_prime_power_lower_mul {W : Type*} {F : SimpleGraph W}
    {a b : ℕ} (D p₀ : ℕ) (hb : 0 < b)
    (hlower : ∀ p : ℕ, p.Prime → p₀ ≤ p → p ^ a ≤ D * extremalNumber (2 * p ^ b) F) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ α)) :
    (a : ℝ) / b ≤ α := by
  by_contra! hα
  obtain ⟨C, hC⟩ := isBigO_iff.mp hO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hβ : 0 < (a : ℝ) - b * α := by
    have h := (lt_div_iff₀ hb').mp hα
    linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, ((D : ℝ) * C) * (2 : ℝ) ^ α < (n : ℝ) ^ ((a : ℝ) - b * α) :=
    ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨M, hM⟩ := eventually_atTop.mp hlarge
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max (max M N) p₀)
  have hpMN : max M N ≤ p := (le_max_left _ _).trans hp
  have hp₀ : p₀ ≤ p := (le_max_right _ _).trans hp
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hprime.pos
  have hpow : p ≤ p ^ b := by
    simpa only [pow_one] using (pow_le_pow_right₀ (Nat.succ_le_of_lt hprime.pos) hb)
  have hpN : N ≤ 2 * p ^ b := (le_max_right _ _).trans (hpMN.trans (by omega))
  have hupper := hN _ hpN
  rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hupper
  push_cast at hupper
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hp0.le] at hupper
  have hpLower : (p : ℝ) ^ a ≤ (D : ℝ) * (extremalNumber (2 * p ^ b) F : ℝ) := by
    exact_mod_cast hlower p hprime hp₀
  have hlt := hM p ((le_max_left _ _).trans hpMN)
  rw [Real.rpow_sub hp0, Real.rpow_natCast,
    lt_div_iff₀ (Real.rpow_pos_of_pos hp0 _)] at hlt
  have hbound := hpLower.trans (mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg D))
  exact (not_lt_of_ge hbound) (by simpa [mul_assoc] using hlt)

private theorem exponent_ge_of_prime_power_lower_mul {W : Type*} {F : SimpleGraph W}
    {a b : ℕ} (D : ℕ) (hb : 0 < b)
    (hlower : ∀ p : ℕ, p.Prime → p ^ a ≤ D * extremalNumber (2 * p ^ b) F) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ α)) :
    (a : ℝ) / b ≤ α :=
  exponent_ge_of_large_prime_power_lower_mul D 0 hb (fun p hp _ => hlower p hp) hO

private theorem exponent_ge_of_prime_power_lower {W : Type*} {F : SimpleGraph W}
    {a b : ℕ} (hb : 0 < b)
    (hlower : ∀ p : ℕ, p.Prime → p ^ a ≤ extremalNumber (2 * p ^ b) F) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ α)) :
    (a : ℝ) / b ≤ α := by
  apply exponent_ge_of_prime_power_lower_mul 1 hb _ hO
  intro p hp
  simpa using hlower p hp

theorem OMA.exponent_ge_cycle_six {W : Type*} {F : SimpleGraph W}
    (hC6 : cycleGraph 6 ⊑ F) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    (4 / 3 : ℝ) ≤ α := by
  simpa only [Nat.cast_ofNat] using exponent_ge_of_prime_power_lower (a := 4) (b := 3)
    (by decide) (fun _ hp => (OMA.cycle_six_extremal_subseq hp).trans hC6.extremalNumber_le) hO

private theorem quadratic_norm_two_circles {K : Type*} [Field K]
    (σ : K →+* K) {a b q r x y z : K} (hab : a ≠ b)
    (hx : (x + a) * σ (x + a) = q) (hx' : (x + b) * σ (x + b) = r)
    (hy : (y + a) * σ (y + a) = q) (hy' : (y + b) * σ (y + b) = r)
    (hz : (z + a) * σ (z + a) = q) (hz' : (z + b) * σ (z + b) = r) :
    x = y ∨ x = z ∨ y = z := by
  let C := q - r - (a * σ a - b * σ b)
  have elim (t : K) (ht : (t + a) * σ (t + a) = q)
      (ht' : (t + b) * σ (t + b) = r) :
      (t + a) * (C - (σ a - σ b) * t + (a - b) * σ a) = (a - b) * q := by
    rw [map_add] at ht ht'
    have hlin : (a - b) * σ t + (σ a - σ b) * t = C := by
      dsimp [C]
      linear_combination ht - ht'
    linear_combination (a - b) * ht - (t + a) * hlin
  have diff (u v : K) (huv : u ≠ v)
      (hu : (u + a) * (C - (σ a - σ b) * u + (a - b) * σ a) = (a - b) * q)
      (hv : (v + a) * (C - (σ a - σ b) * v + (a - b) * σ a) = (a - b) * q) :
      C + (a - b) * σ a - (σ a - σ b) * (u + v + a) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr huv)
    linear_combination hu - hv
  by_cases hxy : x = y
  · exact Or.inl hxy
  by_cases hxz : x = z
  · exact Or.inr (Or.inl hxz)
  refine Or.inr (Or.inr (sub_eq_zero.mp ?_))
  have h₁ := diff x y hxy (elim x hx hx') (elim y hy hy')
  have h₂ := diff x z hxz (elim x hx hx') (elim z hz hz')
  apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr (fun h => hab (σ.injective h)))
  linear_combination h₂ - h₁

private def normIncidence {k K : Type*} [Field k] [Field K] [Algebra k K]
    (a b : K × k) : Prop :=
  a.2 ≠ 0 ∧ b.2 ≠ 0 ∧ Algebra.norm k (a.1 + b.1) = a.2 * b.2

private theorem normIncidence_symm {k K : Type*} [Field k] [Field K] [Algebra k K]
    {a b : K × k} (h : normIncidence a b) : normIncidence b a :=
  ⟨h.2.1, h.1, by rw [add_comm, mul_comm]; exact h.2.2⟩

private theorem normIncidence_coordinate_ne {k K : Type*} [Field k] [Field K] [Algebra k K]
    {a b y : K × k} (hab : a ≠ b) (ha : normIncidence a y) (hb : normIncidence b y) :
    a.1 ≠ b.1 := by
  intro he
  apply hab
  refine Prod.ext he (mul_right_cancel₀ ha.2.1 ?_)
  rw [← ha.2.2, ← hb.2.2, he]

private theorem norm_coordinate_sum_ne {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K →+* K) (hN : ∀ u : K, algebraMap k K (Algebra.norm k u) = u * σ u)
    {a y : K × k} (h : normIncidence a y) : a.1 + y.1 ≠ 0 := by
  intro he
  have hm := hN (a.1 + y.1)
  rw [h.2.2, he, zero_mul] at hm
  exact (map_ne_zero (algebraMap k K)).2 (mul_ne_zero h.1 h.2.1) hm

private theorem norm_normalize {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K →+* K) (hN : ∀ u : K, algebraMap k K (Algebra.norm k u) = u * σ u)
    {a b y : K × k} (hab : a.1 ≠ b.1) (ha : normIncidence a y) (hb : normIncidence b y) :
    let t := (a.1 + y.1)⁻¹
    let c := (b.1 - a.1)⁻¹
    (t + c) * σ (t + c) =
      (algebraMap k K b.2 / algebraMap k K a.2) * (c * σ c) := by
  dsimp only
  have hₐ := norm_coordinate_sum_ne σ hN ha
  have hba := sub_ne_zero.mpr hab.symm
  have he : (a.1 + y.1)⁻¹ + (b.1 - a.1)⁻¹ =
      ((b.1 + y.1) / (a.1 + y.1)) * (b.1 - a.1)⁻¹ := by
    field_simp
    ring
  rw [he, map_mul, map_div₀]
  have h₁ := hN (a.1 + y.1)
  have h₂ := hN (b.1 + y.1)
  rw [ha.2.2, map_mul] at h₁
  rw [hb.2.2, map_mul] at h₂
  calc
    _ = ((b.1 + y.1) * σ (b.1 + y.1) / ((a.1 + y.1) * σ (a.1 + y.1))) *
        ((b.1 - a.1)⁻¹ * σ (b.1 - a.1)⁻¹) := by rw [mul_div_mul_comm]; ring
    _ = _ := by
      rw [← h₁, ← h₂, mul_div_mul_right _ _ ((map_ne_zero (algebraMap k K)).2 ha.2.1)]

private theorem normIncidence_no_three_common {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K →+* K) (hN : ∀ u : K, algebraMap k K (Algebra.norm k u) = u * σ u)
    {a b c x y z : K × k} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hax : normIncidence a x) (hbx : normIncidence b x) (hcx : normIncidence c x)
    (hay : normIncidence a y) (hby : normIncidence b y) (hcy : normIncidence c y)
    (haz : normIncidence a z) (hbz : normIncidence b z) (hcz : normIncidence c z) :
    x = y ∨ x = z ∨ y = z := by
  have hab' := normIncidence_coordinate_ne hab hax hbx
  have hac' := normIncidence_coordinate_ne hac hax hcx
  have hbc' := normIncidence_coordinate_ne hbc hbx hcx
  have hcenter : (b.1 - a.1)⁻¹ ≠ (c.1 - a.1)⁻¹ :=
    fun h => hbc' (sub_left_inj.mp (inv_injective h))
  have unnormalize {u v : K × k} (hu : normIncidence a u) (hv : normIncidence a v)
      (he : (a.1 + u.1)⁻¹ = (a.1 + v.1)⁻¹) : u = v := by
    by_contra hne
    exact normIncidence_coordinate_ne hne (normIncidence_symm hu) (normIncidence_symm hv)
      (add_left_cancel (inv_injective he))
  rcases quadratic_norm_two_circles σ hcenter
      (norm_normalize σ hN hab' hax hbx) (norm_normalize σ hN hac' hax hcx)
      (norm_normalize σ hN hab' hay hby) (norm_normalize σ hN hac' hay hcy)
      (norm_normalize σ hN hab' haz hbz) (norm_normalize σ hN hac' haz hcz) with h | h | h
  · exact Or.inl (unnormalize hax hay h)
  · exact Or.inr (Or.inl (unnormalize hax haz h))
  · exact Or.inr (Or.inr (unnormalize hay haz h))

private def normBipartiteGraph (k K : Type*) [Field k] [Field K] [Algebra k K] :
    SimpleGraph ((K × k) ⊕ (K × k)) where
  Adj a b := match a, b with
    | .inl x, .inr y | .inr x, .inl y => normIncidence x y
    | _, _ => False
  symm := ⟨by
    rintro (x | x) (y | y) h
    all_goals first | exact h | exact normIncidence_symm h⟩
  loopless := ⟨by rintro (x | x) h <;> exact h⟩

private theorem normBipartiteGraph_free {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K →+* K) (hN : ∀ u : K, algebraMap k K (Algebra.norm k u) = u * σ u) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Free (normBipartiteGraph k K) := by
  let X := normBipartiteGraph k K
  have hcommon : ∀ a b c x y z, a ≠ b → a ≠ c → b ≠ c →
      X.Adj a x → X.Adj b x → X.Adj c x → X.Adj a y → X.Adj b y → X.Adj c y →
      X.Adj a z → X.Adj b z → X.Adj c z → x = y ∨ x = z ∨ y = z := by
    rintro (a | a) (b | b) (c | c) (x | x) (y | y) (z | z)
      hab hac hbc hax hbx hcx hay hby hcy haz hbz hcz
    all_goals simp_all [X, normBipartiteGraph]
    all_goals exact normIncidence_no_three_common σ hN hab hac hbc hax hbx hcx hay hby hcy haz hbz hcz
  intro h
  let f := h.some
  have hadj (i j : Fin 3) : X.Adj (f (.inl i)) (f (.inr j)) :=
    f.toHom.map_rel' (Or.inl ⟨rfl, rfl⟩)
  have hleft {i j : Fin 3} (hne : i ≠ j) : f (.inl i) ≠ f (.inl j) :=
    fun hh => hne (Sum.inl.inj (f.injective hh))
  have hright {i j : Fin 3} (hne : i ≠ j) : f (.inr i) ≠ f (.inr j) :=
    fun hh => hne (Sum.inr.inj (f.injective hh))
  rcases hcommon _ _ _ _ _ _
      (hleft (by decide : (0 : Fin 3) ≠ 1)) (hleft (by decide : (0 : Fin 3) ≠ 2))
      (hleft (by decide : (1 : Fin 3) ≠ 2))
      (hadj 0 0) (hadj 1 0) (hadj 2 0) (hadj 0 1) (hadj 1 1) (hadj 2 1)
      (hadj 0 2) (hadj 1 2) (hadj 2 2) with he | he | he
  · exact hright (by decide : (0 : Fin 3) ≠ 1) he
  · exact hright (by decide : (0 : Fin 3) ≠ 2) he
  · exact hright (by decide : (1 : Fin 3) ≠ 2) he

private theorem normBipartiteGraph_edges {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype k] [Fintype K]
    (σ : K →+* K) (hN : ∀ u : K, algebraMap k K (Algebra.norm k u) = u * σ u) :
    Fintype.card K * (Fintype.card k - 1) * (Fintype.card K - 1) ≤
      (normBipartiteGraph k K).edgeFinset.card := by
  let X := normBipartiteGraph k K
  let fn : (K × kˣ) × Kˣ → X.edgeFinset := fun z =>
    ⟨s(.inl (z.1.1, z.1.2), .inr ((z.2 : K) - z.1.1, Algebra.norm k (z.2 : K) / z.1.2)),
      by
        apply mem_edgeFinset.mpr
        have hpos : Algebra.norm k (z.2 : K) ≠ 0 := by
          intro h
          have hn := hN (z.2 : K)
          rw [h, map_zero] at hn
          exact mul_ne_zero z.2.ne_zero ((map_ne_zero σ).2 z.2.ne_zero) hn.symm
        refine ⟨z.1.2.ne_zero, div_ne_zero hpos z.1.2.ne_zero, ?_⟩
        change Algebra.norm k (z.1.1 + ((z.2 : K) - z.1.1)) =
          (z.1.2 : k) * (Algebra.norm k (z.2 : K) / z.1.2)
        rw [add_sub_cancel, mul_comm, div_mul_cancel₀ _ z.1.2.ne_zero]⟩
  have hinj : Function.Injective fn := by
    intro a b h
    have h' := Sym2.eq_iff.mp (congrArg Subtype.val h)
    rcases h' with ⟨hl, hr⟩ | ⟨hl, _⟩
    · have he := Sum.inl.inj hl
      have hfst : a.1.1 = b.1.1 := congrArg (Prod.fst : K × k → K) he
      have hlabel : a.1.2 = b.1.2 := Units.ext (congrArg (Prod.snd : K × k → k) he)
      have hu : (a.2 : K) - a.1.1 = (b.2 : K) - b.1.1 :=
        congrArg (Prod.fst : K × k → K) (Sum.inr.inj hr)
      rw [hfst] at hu
      exact Prod.ext (Prod.ext hfst hlabel) (Units.ext (sub_left_inj.mp hu))
    · exact (Sum.inl_ne_inr hl).elim
  simpa only [Fintype.card_prod, Fintype.card_units, Fintype.card_coe] using
    Fintype.card_le_of_injective fn hinj

private theorem finite_quadratic_norm {p : ℕ} [Fact p.Prime] (u : GaloisField p 2) :
    algebraMap (ZMod p) (GaloisField p 2) (Algebra.norm (ZMod p) u) =
      u * frobenius (GaloisField p 2) p u := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hf : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have hs : p - 1 + 1 = p := by omega
    have he : (p ^ 2 - 1) + 1 = (p - 1) * (p + 1) + 1 := by
      rw [Nat.sub_add_cancel (show 1 ≤ p ^ 2 from Nat.one_le_of_lt (pow_pos (by omega) _))]
      nlinarith only [congrArg (fun t : ℕ => t * (p + 1)) hs]
    exact Nat.add_right_cancel he
  rw [FiniteField.algebraMap_norm_eq_pow, GaloisField.card _ _ (by decide), Nat.card_eq_fintype_card,
    ZMod.card, hf, Nat.mul_div_cancel_left _ (show 0 < p - 1 by omega),
    frobenius_def, pow_succ']

/-- The quadratic norm graphs give the $(3,3)$ lower bound on a prime subsequence. -/
theorem OMA.complete_bipartite_three_extremal_subseq {p : ℕ} (hp : p.Prime) :
    p ^ 5 ≤ 4 * extremalNumber (2 * p ^ 3) (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p 2
  let _ : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by decide)
  have h := (normBipartiteGraph_edges (frobenius K p) finite_quadratic_norm).trans
    (card_edgeFinset_le_extremalNumber (normBipartiteGraph_free (frobenius K p) finite_quadratic_norm))
  rw [Fintype.card_sum, Fintype.card_prod, hK, ZMod.card,
    ← two_mul, show p ^ 2 * p = p ^ 3 by ring] at h
  have hp' := hp.two_le
  have hp₂ : 2 ≤ p ^ 2 := by nlinarith
  calc
    p ^ 5 = p ^ 2 * p * p ^ 2 := by ring
    _ ≤ p ^ 2 * (2 * (p - 1)) * (2 * (p ^ 2 - 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    _ = 4 * (p ^ 2 * (p - 1) * (p ^ 2 - 1)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 h

theorem OMA.exponent_ge_complete_bipartite_three {W : Type*} {F : SimpleGraph W}
    (hK33 : completeBipartiteGraph (Fin 3) (Fin 3) ⊑ F) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    (5 / 3 : ℝ) ≤ α := by
  simpa only [Nat.cast_ofNat] using exponent_ge_of_prime_power_lower_mul (a := 5) (b := 3)
    4 (by decide) (fun _ hp => (OMA.complete_bipartite_three_extremal_subseq hp).trans
      (Nat.mul_le_mul_left 4 hK33.extremalNumber_le)) hO

private def vertexSampleGraph {V : Type*} (H : SimpleGraph V) (P : V → Prop) : SimpleGraph V :=
  H.deleteEdges {e | ¬ ∀ v ∈ e, P v}

private theorem vertexSampleGraph_live {V : Type*} {H : SimpleGraph V} {P : V → Prop}
    {u v : V} (h : (vertexSampleGraph H P).Adj u v) : P u :=
  (not_not.mp (deleteEdges_adj.mp h).2) u (by simp)

private theorem card_subsets_avoiding_root_blocks {V : Type*} [Fintype V]
    (T : V → Finset V) (k : ℕ) (hT : ∀ x, (T x).card ≤ k)
    {e : Sym2 V} (hgood : ∀ x ∈ e, ∀ y ∈ e, y ∉ T x) :
    2 ^ (Fintype.card V - (2 * k + 2)) ≤
      (univ.filter fun f : V → Fin 2 => ∀ v ∈ e,
        f v = 1 ∧ ∀ w ∈ T v, f w = 0).card := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    let S := (T x ∪ T y) ∪ {x, y}
    let g : V → Fin 2 := fun v => if v = x ∨ v = y then 1 else 0
    have hxs : x ∈ S := by simp [S]
    have hys : y ∈ S := by simp [S]
    have hs : S.card ≤ 2 * k + 2 := by
      have hp : ({x, y} : Finset V).card ≤ 2 := card_insert_le _ _
          |>.trans (by simp)
      exact (card_union_le _ _).trans (by
        have h := (card_union_le (T x) (T y)).trans (Nat.add_le_add (hT x) (hT y))
        omega)
    have hT0 {v : V} (hv : v ∈ s(x,y)) {w : V} (hw : w ∈ T v) : g w = 0 := by
      have hne (u : V) (hu : u ∈ s(x,y)) : w ≠ u := fun he =>
        hgood v hv u hu (he ▸ hw)
      simp [g, hne x (by simp), hne y (by simp)]
    calc
      _ ≤ 2 ^ (Fintype.card V - S.card) := pow_le_pow_right₀ (by decide) (by omega)
      _ = (univ.filter fun f : V → Fin 2 => ∀ v ∈ S, f v = g v).card :=
        (card_colorings_prescribed 2 S g).symm
      _ ≤ _ := by
        apply card_le_card
        intro f hf
        rw [mem_filter] at hf ⊢
        refine ⟨mem_univ _, ?_⟩
        intro v hv
        rcases (show v = x ∨ v = y by simpa using hv) with rfl | rfl
        · refine ⟨by simpa [g] using hf.2 v hxs, fun w hw => ?_⟩
          rw [hf.2 w (by simp [S, hw]), hT0 (by simp) hw]
        · refine ⟨by simpa [g] using hf.2 v hys, fun w hw => ?_⟩
          rw [hf.2 w (by simp [S, hw]), hT0 (by simp) hw]

set_option maxHeartbeats 600000 in
/-- Small hitting sets for every vertex-rooted copy give a linear-error bound on host edges. -/
theorem OMA.card_edges_le_of_root_copy_hitting_sets {V W : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (J : SimpleGraph W) (r : W) (k : ℕ)
    (hJ : ∀ v : W, ∃ w, J.Adj v w) (T : V → Finset V)
    (hT : ∀ x, (T x).card ≤ k) (hoff : ∀ x, x ∉ T x)
    (hhit : ∀ c : J.Copy H, ∃ v, c v ∈ T (c r)) :
    H.edgeFinset.card ≤ k * Fintype.card V + 2 ^ (2 * k + 2) * extremalNumber (Fintype.card V) J := by
  let B : Finset (Sym2 V) := univ.biUnion fun x => (T x).image fun y => s(x,y)
  let live (f : V → Fin 2) (x : V) := f x = 1 ∧ ∀ y ∈ T x, f y = 0
  let n := Fintype.card V
  let d := 2 * k + 2
  let A := H.edgeFinset.filter fun e => e ∉ B
  have hB : B.card ≤ n * k := calc
    _ ≤ ∑ x : V, ((T x).image fun y => s(x,y)).card := card_biUnion_le
    _ ≤ ∑ _ : V, k := sum_le_sum fun x _ => card_image_le.trans (hT x)
    _ = _ := by simp [n, Nat.mul_comm]
  have hfree (f : V → Fin 2) : J.Free (vertexSampleGraph H (live f)) := by
    intro h
    let c := h.some
    have hs (v : W) : live f (c v) := by
      obtain ⟨w, hw⟩ := hJ v
      exact vertexSampleGraph_live (c.toHom.map_rel' hw)
    let incl : (vertexSampleGraph H (live f)).Copy H := Copy.ofLE _ _ (H.deleteEdges_le _)
    obtain ⟨v, hv⟩ := hhit (incl.comp c)
    change c v ∈ T (c r) at hv
    exact (by decide : (1 : Fin 2) ≠ 0) ((hs v).1.symm.trans ((hs r).2 _ hv))
  have hgood {e : Sym2 V} (he : e ∈ A) : ∀ x ∈ e, ∀ y ∈ e, y ∉ T x := by
    intro x hx y hy hxy
    apply (mem_filter.mp he).2
    apply mem_biUnion.mpr
    refine ⟨x, mem_univ _, mem_image.mpr ⟨y, hxy, ?_⟩⟩
    have hne : x ≠ y := by
      intro h
      subst y
      exact hoff x hxy
    exact ((Sym2.mem_and_mem_iff hne).mp ⟨hx, hy⟩).symm
  have hsample (f : V → Fin 2) :
      (A.filter fun e => ∀ v ∈ e, live f v).card ≤ extremalNumber n J := by
    have hsub : (A.filter fun e => ∀ v ∈ e, live f v) ⊆
        (vertexSampleGraph H (live f)).edgeFinset := by
      intro e he
      obtain ⟨ha, hlive⟩ := mem_filter.mp he
      rw [mem_edgeFinset, vertexSampleGraph, edgeSet_deleteEdges]
      exact ⟨mem_edgeFinset.mp (mem_filter.mp ha).1, not_not_intro hlive⟩
    exact (card_le_card hsub).trans (card_edgeFinset_le_extremalNumber (hfree f))
  have hsum : A.card * 2 ^ (n - d) ≤ 2 ^ n * extremalNumber n J := by
    calc
      _ = ∑ _ ∈ A, 2 ^ (n - d) := by simp
      _ ≤ ∑ e ∈ A, (univ.filter fun f : V → Fin 2 => ∀ v ∈ e, live f v).card :=
        sum_le_sum fun _ he => card_subsets_avoiding_root_blocks T k hT (hgood he)
      _ = ∑ f : V → Fin 2, (A.filter fun e => ∀ v ∈ e, live f v).card :=
        sum_card_filter_swap A univ (fun e f => ∀ v ∈ e, live f v)
      _ ≤ ∑ _ : V → Fin 2, extremalNumber n J :=
        sum_le_sum fun f _ => hsample f
      _ = _ := by simp [n]
  have hA : A.card ≤ 2 ^ d * extremalNumber n J := by
    have hpow : 0 < (2 : ℕ) ^ (n - d) := pow_pos (by decide) _
    apply (Nat.mul_le_mul_right_iff hpow).mp
    calc
      _ ≤ 2 ^ n * extremalNumber n J := hsum
      _ ≤ (2 ^ (d + (n - d))) * extremalNumber n J :=
        Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by decide) (by omega))
      _ = _ := by simp only [pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hcomp := card_filter_add_card_filter_not (s := H.edgeFinset) (p := fun e => e ∈ B)
  have hbad : (H.edgeFinset.filter fun e => e ∈ B).card ≤ B.card :=
    card_le_card fun _ h => (mem_filter.mp h).2
  change (H.edgeFinset.filter fun e => e ∈ B).card + A.card = H.edgeFinset.card at hcomp
  rw [Nat.mul_comm k]
  change H.edgeFinset.card ≤ n * k + 2 ^ d * extremalNumber n J
  omega

/-- Two copies of a graph with only their prescribed root identified. -/
def OMA.rootedDouble {W : Type*} (J : SimpleGraph W) (r : W) :
    SimpleGraph (W ⊕ {v : W // v ≠ r}) where
  Adj a b := match a, b with
    | .inl u, .inl v => J.Adj u v
    | .inl u, .inr v => u = r ∧ J.Adj r v
    | .inr u, .inl v => v = r ∧ J.Adj r u
    | .inr u, .inr v => J.Adj u v
  symm := ⟨by
    rintro (u | u) (v | v) h
    all_goals first | exact h | exact Adj.symm h⟩
  loopless := ⟨by rintro (u | u) h <;> exact J.loopless.irrefl _ h⟩

private theorem rootedDouble_contained_of_pair {V W : Type*}
    {H : SimpleGraph V} {J : SimpleGraph W} {r : W} (c d : J.Copy H)
    (hroot : c r = d r) (hdis : ∀ u v, c u = d v → v = r) :
    OMA.rootedDouble J r ⊑ H := by
  let f : W ⊕ {v : W // v ≠ r} → V := Sum.elim c (fun v => d v)
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · rintro (u | u) (v | v) h
    · exact c.toHom.map_rel' h
    · change u = r ∧ J.Adj r v at h
      change H.Adj (c u) (d v)
      rw [h.1, hroot]
      exact d.toHom.map_rel' h.2
    · change v = r ∧ J.Adj r u at h
      change H.Adj (d u) (c v)
      rw [h.1, hroot]
      exact Adj.symm (d.toHom.map_rel' h.2)
    · exact d.toHom.map_rel' h
  · rintro (u | u) (v | v) h
    · exact congrArg Sum.inl (c.injective h)
    · exact (v.2 (hdis u v h)).elim
    · exact (u.2 (hdis v u h.symm)).elim
    · exact congrArg Sum.inr (Subtype.ext (d.injective h))

/-- Identifying the roots of two copies preserves the extremal scale above linear growth. -/
theorem OMA.extremalNumber_le_rootedDouble {W : Type*} [Fintype W]
    (J : SimpleGraph W) (r : W) (hJ : ∀ v : W, ∃ w, J.Adj v w) (n : ℕ) :
    extremalNumber n (OMA.rootedDouble J r) ≤
      Fintype.card W * n + 2 ^ (2 * Fintype.card W + 2) * extremalNumber n J := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro H _ hfree
  let T (x : Fin n) : Finset (Fin n) := if h : ∃ c : J.Copy H, c r = x then
    (univ.erase r).image h.choose else ∅
  have hT (x : Fin n) : (T x).card ≤ Fintype.card W := by
    unfold T
    split
    · exact card_image_le.trans (card_le_univ _)
    · simp
  have hoff (x : Fin n) : x ∉ T x := by
    unfold T
    split
    next h =>
      intro hx
      obtain ⟨v, hv, he⟩ := mem_image.mp hx
      exact (mem_erase.mp hv).1 (h.choose.injective (he.trans h.choose_spec.symm))
    · simp
  apply OMA.card_edges_le_of_root_copy_hitting_sets H J r _ hJ T hT hoff
  intro d
  have hx : ∃ c : J.Copy H, c r = d r := ⟨d, rfl⟩
  simp only [T, dif_pos hx]
  by_contra! hdis
  apply hfree
  refine rootedDouble_contained_of_pair hx.choose d hx.choose_spec ?_
  intro u v he
  by_cases hur : u = r
  · rw [hur, hx.choose_spec] at he
    exact d.injective he.symm
  · exact (hdis v (mem_image.mpr ⟨u, mem_erase.mpr ⟨hur, mem_univ _⟩, he⟩)).elim

theorem OMA.extremalNumber_rootedDouble_isLittleO {W : Type*} [Fintype W]
    (J : SimpleGraph W) (r : W) (hJ : ∀ v : W, ∃ w, J.Adj v w) {α : ℝ} (hα : 1 < α)
    (hsmall : (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    (fun n : ℕ => (extremalNumber n (OMA.rootedDouble J r) : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ α) := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact_mod_cast hn
  have hlin : (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
    apply (isLittleO_iff_tendsto' (hpos.mono fun n hn h =>
      ((Real.rpow_pos_of_pos hn α).ne' h).elim)).mpr
    apply ((tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards [hpos] with n hn
    change (n : ℝ) ^ (-(α - 1)) = (n : ℝ) / (n : ℝ) ^ α
    rw [neg_sub, Real.rpow_sub hn, Real.rpow_one]
  let k := Fintype.card W
  have hbig : (fun n : ℕ => (extremalNumber n (OMA.rootedDouble J r) : ℝ)) =O[atTop]
      (fun n : ℕ => (k : ℝ) * n + (2 : ℝ) ^ (2 * k + 2) * extremalNumber n J) := by
    apply IsBigO.of_bound' (Eventually.of_forall fun n => ?_)
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
    exact_mod_cast OMA.extremalNumber_le_rootedDouble J r hJ n
  exact hbig.trans_isLittleO ((hlin.const_mul_left (k : ℝ)).add
    (hsmall.const_mul_left ((2 : ℝ) ^ (2 * k + 2))))

theorem OMA.minimal_power_not_contained_rootedDouble {q s : ℕ}
    {F : SimpleGraph (Fin q)} {J : SimpleGraph (Fin s)} {α : ℝ} (hα : 1 < α)
    (hF : OMA.ExtremalPowerOrder F α)
    (hsmall : (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α))
    (r : Fin s) (hJ : ∀ v : Fin s, ∃ w, J.Adj v w) :
    ¬ F ⊑ OMA.rootedDouble J r := by
  intro hc
  exact hF.2 ((OMA.extremalNumber_isBigO_of_contained hc).trans_isLittleO
    (OMA.extremalNumber_rootedDouble_isLittleO J r hJ hα hsmall))

private abbrev eightVertex (K : Type*) := K × (K × K × K) × K

private def eightIncidence {K : Type*} [Field K] (p l : eightVertex K) : Prop :=
  p.2.1.1 + l.2.1.1 = p.1 * l.1 ∧
  p.2.1.2.1 + l.2.1.2.1 = p.1 * l.1 ^ 2 ∧
  p.2.1.2.2 + l.2.1.2.2 = p.1 * l.1 ^ 3 ∧
  p.2.2 + l.2.2 = p.1 * l.2.1.1

private theorem eight_incident_line_eq {K : Type*} [Field K] {p l m : eightVertex K}
    (hl : eightIncidence p l) (hm : eightIncidence p m) (h : l.1 = m.1) : l = m := by
  obtain ⟨hl₁, hl₂, hl₃, hl₄⟩ := hl
  obtain ⟨hm₁, hm₂, hm₃, hm₄⟩ := hm
  rw [h] at hl₁ hl₂ hl₃
  have hb := add_left_cancel (hl₁.trans hm₁.symm)
  rw [hb] at hl₄
  exact Prod.ext h (Prod.ext (Prod.ext hb
    (Prod.ext (add_left_cancel (hl₂.trans hm₂.symm)) (add_left_cancel (hl₃.trans hm₃.symm))))
    (add_left_cancel (hl₄.trans hm₄.symm)))

private theorem eight_incident_point_eq {K : Type*} [Field K] {p q l : eightVertex K}
    (hp : eightIncidence p l) (hq : eightIncidence q l) (h : p.1 = q.1) : p = q := by
  obtain ⟨hp₁, hp₂, hp₃, hp₄⟩ := hp
  obtain ⟨hq₁, hq₂, hq₃, hq₄⟩ := hq
  rw [h] at hp₁ hp₂ hp₃ hp₄
  exact Prod.ext h (Prod.ext (Prod.ext (add_right_cancel (hp₁.trans hq₁.symm))
    (Prod.ext (add_right_cancel (hp₂.trans hq₂.symm)) (add_right_cancel (hp₃.trans hq₃.symm))))
    (add_right_cancel (hp₄.trans hq₄.symm)))

private theorem opposite_slope_eq_of_moments {K : Type*} [Field K]
    {a b c d u v w x : K} (hu : u ≠ 0) (hab : a ≠ b) (had : a ≠ d)
    (h₀ : u + v + w + x = 0)
    (h₁ : u*a + v*b + w*c + x*d = 0)
    (h₂ : u*a^2 + v*b^2 + w*c^2 + x*d^2 = 0)
    (h₃ : u*a^3 + v*b^3 + w*c^3 + x*d^3 = 0) : a = c := by
  have h : ((a-b) * (a-d) * u) * (a-c) = 0 := by
    linear_combination h₃ - (b+c+d)*h₂ + (b*c+b*d+c*d)*h₁ - (b*c*d)*h₀
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr had)) hu))

private theorem eight_no_incidence_cycle {K : Type*} [Field K] (h₂char : (2 : K) ≠ 0)
    {a b c d l m n o : eightVertex K} (hab : a ≠ b) (hbc : b ≠ c)
    (hlm : l ≠ m) (hlo : l ≠ o) (hmn : m ≠ n)
    (hal : eightIncidence a l) (hbl : eightIncidence b l)
    (hbm : eightIncidence b m) (hcm : eightIncidence c m)
    (hcn : eightIncidence c n) (hdn : eightIncidence d n)
    (hdo : eightIncidence d o) (hao : eightIncidence a o) : False := by
  have hab' := sub_ne_zero.mpr (fun h => hab (eight_incident_point_eq hbl hal h).symm)
  have hbc' := sub_ne_zero.mpr (fun h => hbc (eight_incident_point_eq hcm hbm h).symm)
  have hlm' := fun h => hlm (eight_incident_line_eq hbl hbm h)
  have hlo' := fun h => hlo (eight_incident_line_eq hal hao h)
  have hmn' := fun h => hmn (eight_incident_line_eq hcm hcn h)
  let u := b.1 - a.1
  let v := c.1 - b.1
  let w := d.1 - c.1
  let x := a.1 - d.1
  have h₀ : u + v + w + x = 0 := by dsimp [u, v, w, x]; ring
  have h₁ : u*l.1 + v*m.1 + w*n.1 + x*o.1 = 0 := by
    dsimp [u, v, w, x]
    linear_combination hal.1 - hbl.1 + hbm.1 - hcm.1 + hcn.1 - hdn.1 + hdo.1 - hao.1
  have h₂ : u*l.1^2 + v*m.1^2 + w*n.1^2 + x*o.1^2 = 0 := by
    dsimp [u, v, w, x]
    linear_combination hal.2.1 - hbl.2.1 + hbm.2.1 - hcm.2.1 +
      hcn.2.1 - hdn.2.1 + hdo.2.1 - hao.2.1
  have h₃ : u*l.1^3 + v*m.1^3 + w*n.1^3 + x*o.1^3 = 0 := by
    dsimp [u, v, w, x]
    linear_combination hal.2.2.1 - hbl.2.2.1 + hbm.2.2.1 - hcm.2.2.1 +
      hcn.2.2.1 - hdn.2.2.1 + hdo.2.2.1 - hao.2.2.1
  have hln : n.1 = l.1 := (opposite_slope_eq_of_moments hab' hlm' hlo' h₀ h₁ h₂ h₃).symm
  have hmo : o.1 = m.1 := (opposite_slope_eq_of_moments (b := n.1) (c := o.1) (d := l.1)
    (u := v) (v := w) (w := x) (x := u) hbc' hmn' (Ne.symm hlm')
    (by linear_combination h₀) (by linear_combination h₁)
    (by linear_combination h₂) (by linear_combination h₃)).symm
  rw [hln, hmo] at h₁
  have huw : u + w = 0 := by
    have h : (l.1 - m.1) * (u + w) = 0 := by linear_combination h₁ - m.1*h₀
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hlm')
  have hvx : v + x = 0 := by linear_combination h₀ - huw
  have hn : n.2.1.1 - l.2.1.1 = (l.1-m.1)*v := by
    have hn := hcn.1
    rw [hln] at hn
    dsimp [v]
    linear_combination hn - hbl.1 - hcm.1 + hbm.1
  have ho : o.2.1.1 - m.2.1.1 = (m.1-l.1)*w := by
    have ho := hdo.1
    have hn := hdn.1
    have hcn' := hcn.1
    rw [hmo] at ho
    rw [hln] at hn hcn'
    dsimp [w]
    linear_combination ho - hcm.1 - hn + hcn'
  have hlast : u*l.2.1.1 + v*m.2.1.1 + w*n.2.1.1 + x*o.2.1.1 = 0 := by
    dsimp [u, v, w, x]
    linear_combination hal.2.2.2 - hbl.2.2.2 + hbm.2.2.2 - hcm.2.2.2 +
      hcn.2.2.2 - hdn.2.2.2 + hdo.2.2.2 - hao.2.2.2
  have hred : w * ((l.1 - m.1) * v) + x * ((m.1 - l.1) * w) = 0 := by
    linear_combination hlast - l.2.1.1*huw - m.2.1.1*hvx - w*hn - x*ho
  have hzero : (2 : K) * (l.1 - m.1) * u * v = 0 := by
    linear_combination -hred + (l.1-m.1)*((v-x)*huw + u*hvx)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h₂char (sub_ne_zero.mpr hlm')) hab') hbc') hzero

private def eightBipartiteGraph (K : Type*) [Field K] :
    SimpleGraph (eightVertex K ⊕ eightVertex K) where
  Adj a b := match a, b with
    | .inl p, .inr l | .inr l, .inl p => eightIncidence p l
    | _, _ => False
  symm := ⟨by rintro (a | a) (b | b) h <;> exact h⟩
  loopless := ⟨by rintro (a | a) h <;> exact h⟩

private theorem eight_neighbor_of_point {K : Type*} [Field K]
    {p : eightVertex K} {x : eightVertex K ⊕ eightVertex K}
    (h : (eightBipartiteGraph K).Adj (.inl p) x) :
    ∃ l, x = .inr l ∧ eightIncidence p l := by
  cases x with
  | inl a => exact h.elim
  | inr l => exact ⟨l, rfl, h⟩

private theorem eight_neighbor_of_line {K : Type*} [Field K]
    {l : eightVertex K} {x : eightVertex K ⊕ eightVertex K}
    (h : (eightBipartiteGraph K).Adj (.inr l) x) :
    ∃ p, x = .inl p ∧ eightIncidence p l := by
  cases x with
  | inl p => exact ⟨p, rfl, h⟩
  | inr a => exact h.elim

private theorem eightBipartiteGraph_free (K : Type*) [Field K] (h₂char : (2 : K) ≠ 0) :
    (cycleGraph 8).Free (eightBipartiteGraph K) := by
  intro h
  let f := h.some
  have hadj (i j : Fin 8) :
      (eightBipartiteGraph K).Adj (f (i+j)) (f (i+(j+1))) := by
    rw [← add_assoc]
    exact f.toHom.map_rel' (cycleGraph_adj.mpr (Or.inr (add_sub_cancel_left (i+j) 1)))
  obtain ⟨i, a, ha⟩ : ∃ (i : Fin 8) (a : eightVertex K), f i = .inl a := by
    cases h₀ : f 0 with
    | inl a => exact ⟨0, a, h₀⟩
    | inr l =>
      have h₀₁ : (eightBipartiteGraph K).Adj (f 0) (f 1) := hadj 0 0
      rw [h₀] at h₀₁
      obtain ⟨a, ha, _⟩ := eight_neighbor_of_line h₀₁
      exact ⟨1, a, ha⟩
  have step (j : Fin 8) : (eightBipartiteGraph K).Adj (f (i+j)) (f (i+(j+1))) := hadj i j
  have h₀ : (eightBipartiteGraph K).Adj (.inl a) (f (i+1)) := by
    simpa only [add_zero, ha, show (0 : Fin 8) + 1 = 1 by decide] using step 0
  obtain ⟨l, hl, hal⟩ := eight_neighbor_of_point h₀
  have h₁ : (eightBipartiteGraph K).Adj (.inr l) (f (i+2)) := by
    simpa only [hl, show (1 : Fin 8) + 1 = 2 by decide] using step 1
  obtain ⟨b, hb, hbl⟩ := eight_neighbor_of_line h₁
  have h₂ : (eightBipartiteGraph K).Adj (.inl b) (f (i+3)) := by
    simpa only [hb, show (2 : Fin 8) + 1 = 3 by decide] using step 2
  obtain ⟨m, hm, hbm⟩ := eight_neighbor_of_point h₂
  have h₃ : (eightBipartiteGraph K).Adj (.inr m) (f (i+4)) := by
    simpa only [hm, show (3 : Fin 8) + 1 = 4 by decide] using step 3
  obtain ⟨c, hc, hcm⟩ := eight_neighbor_of_line h₃
  have h₄ : (eightBipartiteGraph K).Adj (.inl c) (f (i+5)) := by
    simpa only [hc, show (4 : Fin 8) + 1 = 5 by decide] using step 4
  obtain ⟨n, hn, hcn⟩ := eight_neighbor_of_point h₄
  have h₅ : (eightBipartiteGraph K).Adj (.inr n) (f (i+6)) := by
    simpa only [hn, show (5 : Fin 8) + 1 = 6 by decide] using step 5
  obtain ⟨d, hd, hdn⟩ := eight_neighbor_of_line h₅
  have h₆ : (eightBipartiteGraph K).Adj (.inl d) (f (i+7)) := by
    simpa only [hd, show (6 : Fin 8) + 1 = 7 by decide] using step 6
  obtain ⟨o, ho, hdo⟩ := eight_neighbor_of_point h₆
  have hao : eightIncidence a o := by
    have h₇ : (eightBipartiteGraph K).Adj (f (i+7)) (f (i+0)) := step 7
    rw [ho, add_zero, ha] at h₇
    exact h₇
  have ne (j k : Fin 8) (hjk : j ≠ k) : f (i+j) ≠ f (i+k) :=
    fun h => hjk (add_left_cancel (f.injective h))
  have ha' : f (i+0) = .inl a := by simpa only [add_zero] using ha
  exact eight_no_incidence_cycle h₂char
    (fun e => ne 0 2 (by decide) (by rw [ha', hb, e]))
    (fun e => ne 2 4 (by decide) (by rw [hb, hc, e]))
    (fun e => ne 1 3 (by decide) (by rw [hl, hm, e]))
    (fun e => ne 1 7 (by decide) (by rw [hl, ho, e]))
    (fun e => ne 3 5 (by decide) (by rw [hm, hn, e]))
    hal hbl hbm hcm hcn hdn hdo hao

private theorem eightBipartiteGraph_edges (K : Type*) [Field K] [Fintype K] :
    Fintype.card K ^ 6 ≤ (eightBipartiteGraph K).edgeFinset.card := by
  let X := eightBipartiteGraph K
  let line (p : eightVertex K) (a : K) : eightVertex K :=
    let b := p.1 * a - p.2.1.1
    (a, (b, p.1 * a ^ 2 - p.2.1.2.1, p.1 * a ^ 3 - p.2.1.2.2), p.1 * b - p.2.2)
  let fn : eightVertex K × K → X.edgeFinset := fun z =>
    ⟨s(.inl z.1, .inr (line z.1 z.2)), by
      apply mem_edgeFinset.mpr
      change eightIncidence z.1 (line z.1 z.2)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [line] <;> ring⟩
  have hinj : Function.Injective fn := by
    intro a b h
    rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨hl, hr⟩ | ⟨hl, _⟩
    · exact Prod.ext (Sum.inl.inj hl) (congrArg Prod.fst (Sum.inr.inj hr))
    · exact (Sum.inl_ne_inr hl).elim
  simpa only [Fintype.card_coe, Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc]
    using Fintype.card_le_of_injective fn hinj

/-- A finite-field lower bound for the eight-cycle along odd primes. -/
theorem OMA.cycle_eight_extremal_subseq {p : ℕ} (hp : p.Prime) (h₂ : 2 < p) :
    p ^ 6 ≤ extremalNumber (2 * p ^ 5) (cycleGraph 8) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h₂' : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact (not_le.mpr h₂) (Nat.le_of_dvd (by decide) hdiv)
  have h := (eightBipartiteGraph_edges (ZMod p)).trans
    (card_edgeFinset_le_extremalNumber (eightBipartiteGraph_free (ZMod p) h₂'))
  simpa [Fintype.card_sum, Fintype.card_prod, ZMod.card, two_mul, pow_succ, mul_assoc] using h

theorem OMA.exponent_ge_cycle_eight {W : Type*} {F : SimpleGraph W}
    (hC8 : cycleGraph 8 ⊑ F) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    (6 / 5 : ℝ) ≤ α := by
  simpa only [Nat.cast_ofNat] using exponent_ge_of_large_prime_power_lower_mul
    (a := 6) (b := 5) 1 3 (by decide)
    (fun _ hp hp₃ => by simpa only [one_mul] using
      (OMA.cycle_eight_extremal_subseq hp (by omega)).trans hC8.extremalNumber_le) hO

/-- Join two graphs by identifying the two vertices of their prescribed edges. -/
def OMA.edgeAmalgam {W U : Type*} (J : SimpleGraph W) (K : SimpleGraph U)
    (r : Fin 2 ↪ W) (s : Fin 2 ↪ U) : SimpleGraph (W ⊕ {v : U // v ∉ Set.range s}) where
  Adj a b := match a, b with
    | .inl u, .inl v => J.Adj u v
    | .inl u, .inr v => ∃ i, u = r i ∧ K.Adj (s i) v
    | .inr u, .inl v => ∃ i, v = r i ∧ K.Adj (s i) u
    | .inr u, .inr v => K.Adj u v
  symm := ⟨by
    rintro (u | u) (v | v) h
    all_goals first | exact h | exact Adj.symm h⟩
  loopless := ⟨by rintro (u | u) h <;> exact h.ne rfl⟩

private theorem edgeAmalgam_contained_of_pair {V W U : Type*}
    {H : SimpleGraph V} {J : SimpleGraph W} {K : SimpleGraph U}
    {r : Fin 2 ↪ W} {s : Fin 2 ↪ U} (c : J.Copy H) (d : K.Copy H)
    (hroot : ∀ i, c (r i) = d (s i))
    (hdis : ∀ u v, c u = d v → v ∈ Set.range s) :
    OMA.edgeAmalgam J K r s ⊑ H := by
  let f : W ⊕ {v : U // v ∉ Set.range s} → V := Sum.elim c (fun v => d v)
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · rintro (u | u) (v | v) h
    · exact c.toHom.map_rel' h
    · obtain ⟨i, rfl, hi⟩ := h
      change H.Adj (c (r i)) (d v)
      rw [hroot]
      exact d.toHom.map_rel' hi
    · obtain ⟨i, rfl, hi⟩ := h
      change H.Adj (d u) (c (r i))
      rw [hroot]
      exact (d.toHom.map_rel' hi).symm
    · exact d.toHom.map_rel' h
  · rintro (u | u) (v | v) h
    · exact congrArg Sum.inl (c.injective h)
    · exact (v.2 (hdis u v h)).elim
    · exact (u.2 (hdis v u h.symm)).elim
    · exact congrArg Sum.inr (Subtype.ext (d.injective h))

private theorem card_colorings_avoiding_edge_block {V : Type*} [Fintype V]
    (T : Finset V) (k : ℕ) (hT : T.card ≤ k)
    {e : Sym2 V} (hdis : ∀ v ∈ e, v ∉ T) :
    2 ^ (Fintype.card V - (k + 2)) ≤
      (univ.filter fun f : V → Fin 2 => (∀ v ∈ e, f v = 1) ∧ ∀ w ∈ T, f w = 0).card := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    let S := insert x (insert y T)
    let g (v : V) : Fin 2 := if v = x ∨ v = y then 1 else 0
    have hS : S.card ≤ k + 2 := by
      have h := card_insert_le x (insert y T)
      have h' := card_insert_le y T
      change S.card ≤ _ at h
      omega
    calc
      _ ≤ 2 ^ (Fintype.card V - S.card) := pow_le_pow_right₀ (by decide) (by omega)
      _ = (univ.filter fun f : V → Fin 2 => ∀ v ∈ S, f v = g v).card :=
        (card_colorings_prescribed 2 S g).symm
      _ ≤ _ := by
        apply card_le_card
        intro f hf
        rw [mem_filter] at hf ⊢
        refine ⟨mem_univ _, ?_, ?_⟩
        · intro v hv
          rcases (show v = x ∨ v = y by simpa using hv) with h | h
          · rw [h]
            simpa [g] using hf.2 x (by simp [S])
          · rw [h]
            simpa [g] using hf.2 y (by simp [S])
        · intro w hw
          have hx : w ≠ x := fun he => hdis x (by simp) (he ▸ hw)
          have hy : w ≠ y := fun he => hdis y (by simp) (he ▸ hw)
          simpa [g, hx, hy] using hf.2 w (by simp [S, hw])

/-- A hitting set attached to each root edge bounds the host density by a constant multiple. -/
theorem OMA.card_edges_le_of_edge_copy_hitting_sets {V U : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (K : SimpleGraph U)
    (r q : U) (hrs : K.Adj r q) (hK : ∀ u : U, ∃ v, K.Adj u v)
    (T : Sym2 V → Finset V) (k : ℕ) (hT : ∀ e, (T e).card ≤ k)
    (hoff : ∀ e : Sym2 V, ∀ v ∈ e, v ∉ T e)
    (hhit : ∀ c : K.Copy H, ∃ v, c v ∈ T s(c r, c q)) :
    H.edgeFinset.card ≤ 2 ^ (k + 2) * extremalNumber (Fintype.card V) K := by
  let live (f : V → Fin 2) (e : Sym2 V) := (∀ v ∈ e, f v = 1) ∧ ∀ w ∈ T e, f w = 0
  let X (f : V → Fin 2) := H.deleteEdges {e | ¬ live f e}
  let n := Fintype.card V
  have hfree (f : V → Fin 2) : K.Free (X f) := by
    intro h
    let c := h.some
    have hc {u v : U} (huv : K.Adj u v) : live f s(c u, c v) :=
      not_not.mp (deleteEdges_adj.mp (c.toHom.map_rel' huv)).2
    let incl : (X f).Copy H := Copy.ofLE _ _ (H.deleteEdges_le _)
    obtain ⟨v, hv⟩ := hhit (incl.comp c)
    obtain ⟨w, hw⟩ := hK v
    have hv' : f (c v) = 0 := (hc hrs).2 (c v) hv
    have hone : f (c v) = 1 := (hc hw).1 _ (by simp)
    exact (by decide : (1 : Fin 2) ≠ 0) (hone.symm.trans hv')
  have hsample (f : V → Fin 2) :
      (H.edgeFinset.filter (live f)).card ≤ extremalNumber n K := by
    have hsub : H.edgeFinset.filter (live f) ⊆ (X f).edgeFinset := by
      intro e he
      obtain ⟨ha, hlive⟩ := mem_filter.mp he
      change e ∈ (H.deleteEdges {e | ¬ live f e}).edgeFinset
      rw [mem_edgeFinset, edgeSet_deleteEdges]
      exact ⟨mem_edgeFinset.mp ha, not_not_intro hlive⟩
    exact (card_le_card hsub).trans (card_edgeFinset_le_extremalNumber (hfree f))
  have hsum : H.edgeFinset.card * 2 ^ (n - (k + 2)) ≤ 2 ^ n * extremalNumber n K := by
    calc
      _ = ∑ _ ∈ H.edgeFinset, 2 ^ (n - (k + 2)) := by simp
      _ ≤ ∑ e ∈ H.edgeFinset, (univ.filter fun f : V → Fin 2 => live f e).card :=
        sum_le_sum fun e _ => card_colorings_avoiding_edge_block (T e) k (hT e) (hoff e)
      _ = ∑ f : V → Fin 2, (H.edgeFinset.filter (live f)).card :=
        sum_card_filter_swap H.edgeFinset univ (fun e f => live f e)
      _ ≤ ∑ _ : V → Fin 2, extremalNumber n K := sum_le_sum fun f _ => hsample f
      _ = _ := by simp [n]
  have hpow : 0 < (2 : ℕ) ^ (n - (k + 2)) := pow_pos (by decide) _
  change H.edgeFinset.card ≤ 2 ^ (k + 2) * extremalNumber n K
  apply (Nat.mul_le_mul_right_iff hpow).mp
  calc
    _ ≤ 2 ^ n * extremalNumber n K := hsum
    _ ≤ 2 ^ (k + 2 + (n - (k + 2))) * extremalNumber n K :=
      Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by decide) (by omega))
    _ = _ := by simp only [pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

set_option maxHeartbeats 600000 in
/-- When each rooted copy in the subgraph has a partner in the host, avoid the amalgam
by bounding the number of edges in the subgraph. -/
theorem OMA.card_edges_le_of_edgeAmalgam_free {V W U : Type*} [Fintype V] [Fintype W]
    (J : SimpleGraph W) (K : SimpleGraph U) (r : Fin 2 ↪ W) (s : Fin 2 ↪ U)
    (hs : K.Adj (s 0) (s 1)) (hK : ∀ u : U, ∃ v, K.Adj u v)
    (H X : SimpleGraph V) [DecidableRel X.Adj] (hX : X ≤ H)
    (hfree : (OMA.edgeAmalgam J K r s).Free H)
    (hpartner : ∀ d : K.Copy X, ∃ c : J.Copy H, ∀ i, c (r i) = d (s i)) :
    X.edgeFinset.card ≤ 2 ^ (2 * Fintype.card W + 2) * extremalNumber (Fintype.card V) K := by
  let HasCopy (x y : V) := ∃ c : J.Copy H, c (r 0) = x ∧ c (r 1) = y
  let outside : Finset W := univ.filter fun u => u ∉ Set.range r
  let B (x y : V) : Finset V := if h : HasCopy x y then outside.image h.choose else ∅
  let T : Sym2 V → Finset V :=
    Sym2.lift ⟨fun x y => B x y ∪ B y x, fun x y => union_comm _ _⟩
  have hB (x y : V) : (B x y).card ≤ Fintype.card W := by
    unfold B
    split
    · exact card_image_le.trans (card_le_univ _)
    · simp
  have hoffB (x y : V) : x ∉ B x y ∧ y ∉ B x y := by
    unfold B
    split
    next h =>
      constructor <;> intro hv <;> obtain ⟨u, hu, he⟩ := mem_image.mp hv
      · exact (mem_filter.mp hu).2 ⟨0, h.choose.injective (h.choose_spec.1.trans he.symm)⟩
      · exact (mem_filter.mp hu).2 ⟨1, h.choose.injective (h.choose_spec.2.trans he.symm)⟩
    · simp
  apply OMA.card_edges_le_of_edge_copy_hitting_sets X K (s 0) (s 1) hs hK T
      (2 * Fintype.card W)
  · intro e
    induction e using Sym2.inductionOn with
    | hf x y =>
      change (B x y ∪ B y x).card ≤ _
      exact (card_union_le _ _).trans (by
        have h := Nat.add_le_add (hB x y) (hB y x)
        omega)
  · intro e
    induction e using Sym2.inductionOn with
    | hf x y =>
      intro v hv
      change v ∉ B x y ∪ B y x
      rcases (show v = x ∨ v = y by simpa using hv) with hv' | hv'
      · rw [hv']
        exact fun h => (mem_union.mp h).elim (hoffB x y).1 (hoffB y x).2
      · rw [hv']
        exact fun h => (mem_union.mp h).elim (hoffB x y).2 (hoffB y x).1
  · intro d
    let x := d (s 0)
    let y := d (s 1)
    obtain ⟨c, hc⟩ := hpartner d
    have hcopy : HasCopy x y := ⟨c, hc 0, hc 1⟩
    let i : X.Copy H := Copy.ofLE X H hX
    by_contra! hav
    apply hfree
    have roots (j : Fin 2) : hcopy.choose (r j) = d (s j) := by
      refine Fin.cases hcopy.choose_spec.1 (fun k => ?_) j
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      exact hcopy.choose_spec.2
    refine edgeAmalgam_contained_of_pair hcopy.choose (i.comp d) roots ?_
    intro u v he
    by_cases hu : u ∈ Set.range r
    · obtain ⟨j, rfl⟩ := hu
      exact ⟨j, d.injective ((roots j).symm.trans he)⟩
    · exfalso
      apply hav v
      change d v ∈ B x y ∪ B y x
      exact mem_union_left _ (by
        simp only [B, dif_pos hcopy]
        exact mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, hu⟩, he⟩)

/-- A rooted containment permits adding a second piece along the distinguished edge
at constant cost in the extremal number. -/
theorem OMA.extremalNumber_le_edgeAmalgam_of_rooted_copy {W U : Type*} [Fintype W]
    (J : SimpleGraph W) (K : SimpleGraph U) (r : Fin 2 ↪ W) (s : Fin 2 ↪ U)
    (hs : K.Adj (s 0) (s 1)) (hK : ∀ u : U, ∃ v, K.Adj u v)
    (b : J.Copy K) (hb : ∀ i, b (r i) = s i) (n : ℕ) :
    extremalNumber n (OMA.edgeAmalgam J K r s) ≤
      2 ^ (2 * Fintype.card W + 2) * extremalNumber n K := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro H _ hfree
  exact OMA.card_edges_le_of_edgeAmalgam_free J K r s hs hK H H le_rfl hfree
    (fun d => ⟨d.comp b, fun i => congrArg d (hb i)⟩)

set_option maxHeartbeats 400000 in
/-- If one piece is symmetric on the distinguished edge, gluing the two pieces there
has extremal order at most the sum of their individual orders. -/
theorem OMA.extremalNumber_le_edgeAmalgam_of_flip {W U : Type*} [Fintype W]
    (J : SimpleGraph W) (K : SimpleGraph U) (r : Fin 2 ↪ W) (s : Fin 2 ↪ U)
    (hr : J.Adj (r 0) (r 1)) (hs : K.Adj (s 0) (s 1))
    (hK : ∀ u : U, ∃ v, K.Adj u v)
    (flip : J.Copy J) (hf₀ : flip (r 0) = r 1) (hf₁ : flip (r 1) = r 0) (n : ℕ) :
    extremalNumber n (OMA.edgeAmalgam J K r s) ≤
      extremalNumber n J + 2 ^ (2 * Fintype.card W + 2) * extremalNumber n K := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro H _ hfree
  let marked (e : Sym2 (Fin n)) : Prop := ∃ c : J.Copy H, s(c (r 0), c (r 1)) = e
  let X := H.deleteEdges {e | ¬ marked e}
  let Y := H.deleteEdges {e | marked e}
  let iy : Y.Copy H := Copy.ofLE Y H (H.deleteEdges_le _)
  have hYfree : J.Free Y := by
    intro h
    let c := h.some
    exact (deleteEdges_adj.mp (c.toHom.map_rel' hr)).2 ⟨iy.comp c, rfl⟩
  have hY := card_edgeFinset_le_extremalNumber hYfree
  have hpart : X.edgeFinset.card + Y.edgeFinset.card = H.edgeFinset.card := by
    have hx : X.edgeFinset = H.edgeFinset.filter marked := by
      ext e
      change e ∈ (H.deleteEdges {e | ¬ marked e}).edgeFinset ↔ _
      rw [mem_edgeFinset, edgeSet_deleteEdges, mem_filter, mem_edgeFinset]
      simp
    have hy : Y.edgeFinset = H.edgeFinset.filter fun e => ¬ marked e := by
      ext e
      change e ∈ (H.deleteEdges {e | marked e}).edgeFinset ↔ _
      rw [mem_edgeFinset, edgeSet_deleteEdges, mem_filter, mem_edgeFinset]
      rfl
    rw [hx, hy]
    exact card_filter_add_card_filter_not marked
  have hX := OMA.card_edges_le_of_edgeAmalgam_free J K r s hs hK H X
    (H.deleteEdges_le _) hfree (by
      intro d
      have hmarked : marked s(d (s 0), d (s 1)) :=
        not_not.mp (deleteEdges_adj.mp (d.toHom.map_rel' hs)).2
      obtain ⟨c, hc⟩ := hmarked
      have of_endpoints (c' : J.Copy H) (h₀ : c' (r 0) = d (s 0))
          (h₁ : c' (r 1) = d (s 1)) : ∀ i, c' (r i) = d (s i) := by
        intro i
        fin_cases i
        · exact h₀
        · exact h₁
      rcases Sym2.eq_iff.mp hc with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
      · exact ⟨c, of_endpoints c h₀ h₁⟩
      · refine ⟨c.comp flip, of_endpoints (c.comp flip) ?_ ?_⟩
        · change c (flip (r 0)) = _
          rw [hf₀, h₁]
        · change c (flip (r 1)) = _
          rw [hf₁, h₀])
  rw [← hpart, Nat.add_comm]
  exact Nat.add_le_add hY hX

theorem OMA.extremalNumber_edgeAmalgam_isLittleO_of_flip {W U : Type*} [Fintype W]
    (J : SimpleGraph W) (K : SimpleGraph U) (r : Fin 2 ↪ W) (s : Fin 2 ↪ U)
    (hr : J.Adj (r 0) (r 1)) (hs : K.Adj (s 0) (s 1))
    (hK : ∀ u : U, ∃ v, K.Adj u v)
    (flip : J.Copy J) (hf₀ : flip (r 0) = r 1) (hf₁ : flip (r 1) = r 0)
    {α : ℝ}
    (hJsmall : (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α))
    (hKsmall : (fun n : ℕ => (extremalNumber n K : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    (fun n : ℕ => (extremalNumber n (OMA.edgeAmalgam J K r s) : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ α) := by
  let c : ℕ := 2 ^ (2 * Fintype.card W + 2)
  have hBig : (fun n : ℕ => (extremalNumber n (OMA.edgeAmalgam J K r s) : ℝ)) =O[atTop]
      (fun n : ℕ => (extremalNumber n J : ℝ) + (c : ℝ) * extremalNumber n K) := by
    apply IsBigO.of_bound' (Eventually.of_forall fun n => ?_)
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
    exact_mod_cast OMA.extremalNumber_le_edgeAmalgam_of_flip J K r s hr hs hK flip hf₀ hf₁ n
  exact hBig.trans_isLittleO (hJsmall.add (hKsmall.const_mul_left (c : ℝ)))

theorem OMA.extremalNumber_edgeAmalgam_isLittleO_of_rooted_copy {W U : Type*} [Fintype W]
    (J : SimpleGraph W) (K : SimpleGraph U) (r : Fin 2 ↪ W) (s : Fin 2 ↪ U)
    (hs : K.Adj (s 0) (s 1)) (hK : ∀ u : U, ∃ v, K.Adj u v)
    (b : J.Copy K) (hb : ∀ i, b (r i) = s i) {α : ℝ}
    (hKsmall : (fun n : ℕ => (extremalNumber n K : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    (fun n : ℕ => (extremalNumber n (OMA.edgeAmalgam J K r s) : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ α) := by
  let c : ℕ := 2 ^ (2 * Fintype.card W + 2)
  have hBig : (fun n : ℕ => (extremalNumber n (OMA.edgeAmalgam J K r s) : ℝ)) =O[atTop]
      (fun n : ℕ => (c : ℝ) * extremalNumber n K) := by
    apply IsBigO.of_bound' (Eventually.of_forall fun n => ?_)
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
    exact_mod_cast OMA.extremalNumber_le_edgeAmalgam_of_rooted_copy J K r s hs hK b hb n
  exact hBig.trans_isLittleO (hKsmall.const_mul_left (c : ℝ))

private theorem card_edges_with_endpoints_in {V W : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {F : SimpleGraph W} (hfree : F.Free H) (A : Finset V) :
    (H.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ A).card ≤ extremalNumber A.card F := by
  have hfree' : F.Free (H.induce (A : Set V)) := fun c => hfree (c.trans ⟨Copy.induce H (A : Set V)⟩)
  have heq : H.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ A) =
      (H.induce (A : Set V)).edgeFinset.map (Function.Embedding.subtype (· ∈ (A : Set V))).sym2Map := by
    calc
      _ = H.edgeFinset ∩ A.sym2 := by
        ext e
        simp [Finset.mem_sym2_iff]
      _ = _ := by
        have h := (map_edgeFinset_induce (s := (A : Set V)) (G := H)).symm
        convert h using 2 <;> ext v <;> first | rfl | simp
  rw [heq, card_map, ← Fintype.card_coe A]
  exact card_edgeFinset_le_extremalNumber hfree'

/-- Cover edges meeting a set of m vertices by subgraphs on at most 2m vertices. -/
theorem OMA.card_incident_edges_le_of_small_extremal_bound {V W : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {F : SimpleGraph W} (hfree : F.Free H)
    (A : Finset V) (hA : 0 < A.card) (C : ℝ)
    (hC : ∀ m ≤ 2 * A.card, (extremalNumber m F : ℝ) ≤ C) :
    ((H.edgeFinset.filter fun e => ∃ v ∈ e, v ∈ A).card : ℝ) ≤
      ((Fintype.card V / A.card : ℕ) + 1 : ℝ) * C := by
  let n := Fintype.card V
  let m := A.card
  let lab := Fintype.equivFin V
  let B (j : ℕ) : Finset V := univ.filter fun v => (lab v).val / m = j
  have hB (j : ℕ) : (B j).card ≤ m := by
    let g (v : B j) : Fin m := ⟨(lab v).val % m, Nat.mod_lt _ hA⟩
    have hg : Function.Injective g := by
      intro v w h
      apply Subtype.ext
      apply lab.injective
      apply Fin.ext
      have hmod : (lab v).val % m = (lab w).val % m := congrArg Fin.val h
      have hv : (lab v).val / m = j := (mem_filter.mp v.property).2
      have hw : (lab w).val / m = j := (mem_filter.mp w.property).2
      calc
        (lab v).val = (lab v).val % m + m * ((lab v).val / m) := (Nat.mod_add_div _ _).symm
        _ = (lab w).val % m + m * ((lab w).val / m) := by rw [hmod, hv, hw]
        _ = (lab w).val := Nat.mod_add_div _ _
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective g hg
  let E (j : ℕ) : Finset (Sym2 V) := H.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ A ∪ B j
  have size (j : ℕ) : (A ∪ B j).card ≤ 2 * m :=
    (card_union_le _ _).trans (by rw [two_mul]; exact Nat.add_le_add_left (hB j) m)
  have hE (j : ℕ) : ((E j).card : ℝ) ≤ C := by
    exact (Nat.cast_le.mpr (card_edges_with_endpoints_in H hfree (A ∪ B j))).trans (hC _ (size j))
  let idx := range (n / m + 1)
  have cover : H.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ A) ⊆ idx.biUnion E := by
    intro e he
    obtain ⟨hadj, u, hu, hAu⟩ := mem_filter.mp he
    obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.mp hu
    let j := (lab v).val / m
    have hj : j ∈ idx := mem_range.mpr
      (Nat.lt_succ_of_le (Nat.div_le_div_right (lab v).isLt.le))
    have hBv : v ∈ B j := mem_filter.mpr ⟨mem_univ _, rfl⟩
    apply mem_biUnion.mpr
    refine ⟨j, hj, mem_filter.mpr ⟨hadj, ?_⟩⟩
    intro w hw
    rcases (show w = u ∨ w = v by simpa using hw) with rfl | rfl
    · exact mem_union_left _ hAu
    · exact mem_union_right _ hBv
  calc
    _ ≤ ((idx.biUnion E).card : ℝ) := Nat.cast_le.mpr (card_le_card cover)
    _ ≤ ∑ j ∈ idx, ((E j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _ ∈ idx, C := sum_le_sum fun j _ => hE j
    _ = _ := by simp [idx, n, m]

private theorem exists_pos_global_extremal_bound {W : Type*} (F : SimpleGraph W)
    {α : ℝ} (hα : 0 ≤ α)
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, (extremalNumber n F : ℝ) ≤ D * (n : ℝ) ^ α := by
  obtain ⟨C, hC⟩ := isBigO_iff.mp hO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  let B := (range (N+1)).sup (fun n => extremalNumber n F)
  let D : ℝ := max C ((B : ℝ) + 1)
  have hD : 0 < D := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨D, hD, fun n => ?_⟩
  by_cases hNn : N ≤ n
  · have h := hN n hNn
    rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  by_cases hn : n = 0
  · subst n
    have hz : extremalNumber 0 F = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← Fintype.card_fin 0, extremalNumber_le_iff]
      intro H _ _
      simpa only [Fintype.card_fin, Nat.choose_zero_succ] using H.card_edgeFinset_le_card_choose_two
    rw [hz, Nat.cast_zero]
    positivity
  · have hle : extremalNumber n F ≤ B := le_sup (f := fun n => extremalNumber n F)
      (mem_range.mpr (by omega))
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hp : (1 : ℝ) ≤ (n : ℝ) ^ α := Real.one_le_rpow hn' hα
    calc
      _ ≤ (B : ℝ) := Nat.cast_le.mpr hle
      _ ≤ D := (by linarith : (B : ℝ) ≤ (B : ℝ) + 1).trans (le_max_right _ _)
      _ ≤ _ := le_mul_of_one_le_right hD.le hp

private theorem rpow_eq_mul_rpow_sub_one {x a : ℝ} (hx : 0 < x) :
    x ^ a = x * x ^ (a - 1) := by
  calc
    x ^ a = x ^ (1 + (a - 1)) := by congr 1; ring
    _ = _ := by rw [Real.rpow_add hx, Real.rpow_one]

/-- A small vertex set meets few edges at any prescribed superlinear extremal scale. -/
theorem OMA.card_incident_edges_le_power {V W : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {F : SimpleGraph W} (hfree : F.Free H) {α C : ℝ} (hα : 1 < α)
    (hC : 0 ≤ C) (hbound : ∀ m : ℕ, (extremalNumber m F : ℝ) ≤ C * (m : ℝ) ^ α)
    (A : Finset V) :
    ((H.edgeFinset.filter fun e => ∃ v ∈ e, v ∈ A).card : ℝ) ≤
      (2 * C * (2 : ℝ) ^ α) * (Fintype.card V : ℝ) * (A.card : ℝ) ^ (α - 1) := by
  by_cases hA : 0 < A.card
  · have hm : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA
    have hcard : A.card ≤ Fintype.card V := card_le_univ _
    have hdiv : (Fintype.card V / A.card + 1) * A.card ≤ 2 * Fintype.card V := by
      rw [Nat.add_mul, one_mul, two_mul]
      exact Nat.add_le_add (Nat.div_mul_le_self _ _) hcard
    have hd : ((Fintype.card V / A.card : ℕ) + 1 : ℝ) * A.card ≤
        2 * (Fintype.card V : ℝ) := by exact_mod_cast hdiv
    have hex : ∀ m ≤ 2 * A.card, (extremalNumber m F : ℝ) ≤ C * (2 * (A.card : ℝ)) ^ α := by
      intro m hm'
      exact (hbound m).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hm') (by linarith)) hC)
    calc
      _ ≤ ((Fintype.card V / A.card : ℕ) + 1 : ℝ) * (C * (2 * (A.card : ℝ)) ^ α) :=
        OMA.card_incident_edges_le_of_small_extremal_bound H hfree A hA _ hex
      _ = (C * (2 : ℝ) ^ α * (A.card : ℝ) ^ (α - 1)) *
          (((Fintype.card V / A.card : ℕ) + 1 : ℝ) * A.card) := by
        rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hm.le, rpow_eq_mul_rpow_sub_one hm]
        ring
      _ ≤ (C * (2 : ℝ) ^ α * (A.card : ℝ) ^ (α - 1)) * (2 * (Fintype.card V : ℝ)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by ring
  · have he : A = ∅ := card_eq_zero.mp (Nat.eq_zero_of_not_pos hA)
    rw [he]
    simpa only [notMem_empty, and_false, exists_false, filter_false, card_empty, Nat.cast_zero]
      using (show (0 : ℝ) ≤ (2 * C * (2 : ℝ) ^ α) * Fintype.card V * (0 : ℝ) ^ (α - 1) by
        positivity)

/-- At a superlinear extremal scale, remove high-degree vertices at arbitrarily small
constant cost in the number of retained edges. -/
theorem OMA.exists_subgraph_bounded_degree_at_extremal_scale {W : Type*} (F : SimpleGraph W)
    {α : ℝ} (hα : 1 < α)
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 0 < n → ∀ H : SimpleGraph (Fin n), F.Free H →
      ∃ X : SimpleGraph (Fin n), X ≤ H ∧
        (∀ v, (X.degree v : ℝ) ≤ D * (n : ℝ) ^ (α - 1)) ∧
        (H.edgeFinset.card : ℝ) ≤ X.edgeFinset.card + ε * (n : ℝ) ^ α := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_global_extremal_bound F (by linarith) hO
  let K : ℝ := 2 * C * (2 : ℝ) ^ α
  have hK : 0 < K := by dsimp [K]; positivity
  let t : ℝ := (ε / K) ^ (1 / (α - 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₀ : K * t ^ (α - 1) = ε := by
    dsimp [t]
    rw [← Real.rpow_mul (by positivity : 0 ≤ ε / K), one_div,
      inv_mul_cancel₀ (sub_pos.mpr hα).ne', Real.rpow_one]
    field_simp
  let D : ℝ := 2 * C / t
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun n hn H hfree => ?_⟩
  let b : ℝ := D * (n : ℝ) ^ (α - 1)
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hb : 0 < b := by dsimp [b]; positivity
  let A : Finset (Fin n) := univ.filter fun v => b < (H.degree v : ℝ)
  have hdegSum : ∑ v : Fin n, (H.degree v : ℝ) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  have hm : (H.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ α := by
    have h := card_edgeFinset_le_extremalNumber hfree
    rw [Fintype.card_fin] at h
    exact (Nat.cast_le.mpr h).trans (hbound n)
  have hA : (A.card : ℝ) ≤ t * n := by
    apply (mul_le_mul_iff_right₀ hb).mp
    calc
      _ = ∑ _ ∈ A, b := by simp [mul_comm]
      _ ≤ ∑ v ∈ A, (H.degree v : ℝ) := sum_le_sum fun v hv => (mem_filter.mp hv).2.le
      _ ≤ ∑ v : Fin n, (H.degree v : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ A) fun _ _ _ => Nat.cast_nonneg _
      _ = 2 * (H.edgeFinset.card : ℝ) := hdegSum
      _ ≤ 2 * (C * (n : ℝ) ^ α) := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by
        rw [rpow_eq_mul_rpow_sub_one hn']
        dsimp [b, D]
        field_simp
  let hits (e : Sym2 (Fin n)) : Prop := ∃ v ∈ e, v ∈ A
  let : DecidablePred hits := fun _ => Classical.propDecidable _
  let X := H.deleteEdges {e | hits e}
  let : DecidableRel X.Adj := fun _ _ => Classical.propDecidable _
  have hX : X ≤ H := H.deleteEdges_le _
  have hsplit : X.edgeFinset.card + (H.edgeFinset.filter hits).card = H.edgeFinset.card := by
    have heq : X.edgeFinset = H.edgeFinset.filter fun e => ¬ hits e := by
      ext e
      change e ∈ (H.deleteEdges {e | hits e}).edgeFinset ↔ _
      rw [mem_edgeFinset, edgeSet_deleteEdges, mem_filter, mem_edgeFinset]
      rfl
    rw [heq, add_comm]
    exact card_filter_add_card_filter_not hits
  refine ⟨X, hX, ?_, ?_⟩
  · intro v
    change (X.degree v : ℝ) ≤ b
    by_cases hv : v ∈ A
    · have hz : X.degree v = 0 := by
        apply (X.degree_eq_zero_iff_notMem_support v).mpr
        intro h
        obtain ⟨w, hw⟩ := X.mem_support.mp h
        exact (deleteEdges_adj.mp hw).2 ⟨v, by simp, hv⟩
      rw [hz, Nat.cast_zero]
      exact hb.le
    · have hv' : (H.degree v : ℝ) ≤ b := le_of_not_gt fun h =>
        hv (mem_filter.mpr ⟨mem_univ _, h⟩)
      exact (Nat.cast_le.mpr (degree_le_of_le hX)).trans hv'
  · have hloss : ((H.edgeFinset.filter hits).card : ℝ) ≤ ε * (n : ℝ) ^ α := by
      have hl := OMA.card_incident_edges_le_power H hfree hα hC.le hbound A
      rw [Fintype.card_fin] at hl
      calc
        _ ≤ K * (n : ℝ) * (A.card : ℝ) ^ (α - 1) := by
          convert hl using 2
          apply congrArg Finset.card
          ext e
          simp only [mem_filter, hits]
        _ ≤ K * (n : ℝ) * (t * n) ^ (α - 1) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hA (by linarith)) (by positivity)
        _ = K * t ^ (α - 1) * ((n : ℝ) * (n : ℝ) ^ (α - 1)) := by
          rw [Real.mul_rpow ht.le hn'.le]
          ring
        _ = _ := by rw [ht₀, ← rpow_eq_mul_rpow_sub_one hn']
    have hsplit' : (X.edgeFinset.card : ℝ) + (H.edgeFinset.filter hits).card =
        (H.edgeFinset.card : ℝ) := by exact_mod_cast hsplit
    exact hsplit'.symm.le.trans (add_le_add (le_refl _) hloss)

set_option maxHeartbeats 400000 in
private theorem exists_subgraph_min_degree_after_pruning {n : ℕ} (H : SimpleGraph (Fin n))
    {b : ℝ} (hb : 0 ≤ b) :
    ∃ X : SimpleGraph (Fin n), X ≤ H ∧
      (H.edgeFinset.card : ℝ) ≤ X.edgeFinset.card + b * n ∧
      (∀ u ∈ X.support, b ≤ (X.degree u : ℝ)) := by
  let P (k : ℕ) : Prop := ∃ X : SimpleGraph (Fin n), X ≤ H ∧
    X.support.toFinset.card = k ∧ (H.edgeFinset.card : ℝ) ≤ X.edgeFinset.card + b * (n - (k : ℝ))
  have hcard (X : SimpleGraph (Fin n)) : X.support.toFinset.card ≤ n := by
    simpa only [Fintype.card_fin] using card_le_univ X.support.toFinset
  have hex : ∃ k, P k := by
    refine ⟨_, H, le_rfl, rfl, le_add_of_nonneg_right (mul_nonneg hb ?_)⟩
    exact sub_nonneg.mpr (Nat.cast_le.mpr (hcard H))
  let k := Nat.find hex
  obtain ⟨X, hXH, hk, hcount⟩ := Nat.find_spec hex
  refine ⟨X, hXH, ?_, ?_⟩
  · exact hcount.trans (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg _)) hb))
  · by_contra! hlow
    obtain ⟨v, hv, hdeg⟩ := hlow
    let Y := X.deleteIncidenceSet v
    let : DecidableRel Y.Adj := fun _ _ => Classical.propDecidable _
    let l := Y.support.toFinset.card
    have hsub : Y.support.toFinset ⊆ X.support.toFinset.erase v := by
      intro u hu
      obtain ⟨huX, hne⟩ := X.support_deleteIncidenceSet_subset v (Set.mem_toFinset.mp hu)
      exact mem_erase.mpr ⟨hne, Set.mem_toFinset.mpr huX⟩
    have hlt : l < k := by
      have h := card_le_card hsub
      rw [card_erase_of_mem (Set.mem_toFinset.mpr hv), hk] at h
      have hp : 0 < k := by
        change 0 < Nat.find hex
        rw [← hk]
        exact card_pos.mpr ⟨v, Set.mem_toFinset.mpr hv⟩
      omega
    have hle : (l : ℝ) + 1 ≤ k := by exact_mod_cast (show l + 1 ≤ k by omega)
    have he : (Y.edgeFinset.card : ℝ) + X.degree v = X.edgeFinset.card := by
      have h : Y.edgeFinset.card = X.edgeFinset.card - X.degree v := by
        convert X.card_edgeFinset_deleteIncidenceSet v using 2
        ext e
        simp only [mem_edgeFinset]
        rfl
      have h' : Y.edgeFinset.card + X.degree v = X.edgeFinset.card := by
        rw [h, Nat.sub_add_cancel (X.degree_le_card_edgeFinset v)]
      exact_mod_cast h'
    have hnot : ¬ P l := Nat.find_min hex hlt
    apply hnot
    have hYX : Y ≤ X := X.deleteIncidenceSet_le v
    have h₁ : (X.edgeFinset.card : ℝ) + b * (n - (k : ℝ)) ≤
        Y.edgeFinset.card + b * (n - (l : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hle hb
      nlinarith only [h, he, hdeg]
    exact ⟨Y, hYX.trans hXH, rfl, hcount.trans h₁⟩

/-- At a superlinear extremal power, arbitrarily large forbidden-free hosts
attain that power with comparable degrees on their support. -/
theorem OMA.frequently_almost_regular_at_extremal_scale {W : Type*} (F : SimpleGraph W)
    {α : ℝ} (hα : 1 < α) (hF : OMA.ExtremalPowerOrder F α) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∃ᶠ n : ℕ in atTop,
      ∃ X : SimpleGraph (Fin n), F.Free X ∧
        c * (n : ℝ) ^ α ≤ X.edgeFinset.card ∧
        (∀ u, (X.degree u : ℝ) ≤ D * (n : ℝ) ^ (α - 1)) ∧
        (∀ u ∈ X.support, c * (n : ℝ) ^ (α - 1) ≤ (X.degree u : ℝ)) := by
  have h := hF.2
  rw [isLittleO_iff] at h
  push Not at h
  obtain ⟨δ, hδ, hfreq⟩ := h
  have hfreq' : ∃ᶠ n : ℕ in atTop, δ * (n : ℝ) ^ α < (extremalNumber n F : ℝ) :=
    hfreq.mono fun n hn => by
      simpa only [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hn
  obtain ⟨D, hD, hreg⟩ :=
    OMA.exists_subgraph_bounded_degree_at_extremal_scale F hα hF.1 (by positivity : 0 < δ / 4)
  refine ⟨δ / 4, D, by positivity, hD, ?_⟩
  refine (hfreq'.and_eventually (eventually_gt_atTop (0 : ℕ))).mono ?_
  rintro n ⟨hn, hn₀⟩
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn₀
  have hlo : 0 ≤ δ * (n : ℝ) ^ α := by positivity
  obtain ⟨H, inst, hfree, hEH⟩ := (lt_extremalNumber_iff_of_nonneg (V := Fin n) F hlo).mp
    (by simpa only [Fintype.card_fin] using hn)
  have hi : inst = fun a b => Classical.propDecidable (H.Adj a b) := Subsingleton.elim _ _
  subst inst
  obtain ⟨Y, hY, hdeg, hcount⟩ := hreg n hn₀ H hfree
  let b := δ / 4 * (n : ℝ) ^ (α - 1)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  obtain ⟨X, hXY, hcount', hmin⟩ := exists_subgraph_min_degree_after_pruning Y hb
  have hscale : b * n = δ / 4 * (n : ℝ) ^ α := by
    dsimp [b]
    rw [rpow_eq_mul_rpow_sub_one (a := α) hn']
    ring
  have he : δ / 4 * (n : ℝ) ^ α ≤ (X.edgeFinset.card : ℝ) := by
    rw [hscale] at hcount'
    have hp : 0 ≤ (δ / 4) * (n : ℝ) ^ α := by positivity
    linarith only [hEH, hcount, hcount', hp]
  refine ⟨X, fun hc => hfree (hc.trans ⟨Copy.ofLE X H (hXY.trans hY)⟩), he, ?_, hmin⟩
  intro u
  exact (Nat.cast_le.mpr (degree_le_of_le hXY)).trans (hdeg u)

/-- The remaining superlinear rationality question for graphs minimal at the given power scale. -/
theorem OMA.core_minimal_power :
    ∀ (r : ℕ) (F : SimpleGraph (Fin r)), F.IsBipartite →
      ∀ α : ℝ, α ∈ Set.Ioo 1 2 → OMA.ExtremalPowerOrder F α →
        (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →
          s + J.edgeFinset.card < r + F.edgeFinset.card →
          (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) →
        (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F → 2 ≤ J.edgeFinset.card →
          (OMA.deletionExponent J : ℝ) < α) →
        (∀ (R : Finset (Fin r)) (t : ℕ), 0 < t →
          (∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R)) →
          ∀ E : Finset {v : Fin r // v ∉ R}, E.card ≤ t →
            (∀ v ∉ E, F.degree v.val ≤ t) → α < 2 - 1 / (t : ℝ)) →
        (completeBipartiteGraph (Fin 2) (Fin 2) ⊑ F → (3 / 2 : ℝ) < α) →
        (cycleGraph 6 ⊑ F → (4 / 3 : ℝ) < α) →
        (cycleGraph 8 ⊑ F → (6 / 5 : ℝ) < α) →
        (completeBipartiteGraph (Fin 3) (Fin 3) ⊑ F → (5 / 3 : ℝ) < α) →
        (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →
          s + J.edgeFinset.card < r + F.edgeFinset.card →
          ∀ v : Fin s, (∀ u : Fin s, ∃ w, J.Adj u w) → ¬ F ⊑ OMA.rootedDouble J v) →
        (∀ (j : ℕ) (J : SimpleGraph (Fin j)), J ⊑ F →
          j + J.edgeFinset.card < r + F.edgeFinset.card →
          ∀ (k : ℕ) (K : SimpleGraph (Fin k)), K ⊑ F →
            k + K.edgeFinset.card < r + F.edgeFinset.card →
            ∀ (a : Fin 2 ↪ Fin j) (b : Fin 2 ↪ Fin k),
              J.Adj (a 0) (a 1) → K.Adj (b 0) (b 1) →
              (∀ u : Fin k, ∃ v, K.Adj u v) →
              ((∃ f : J.Copy J, f (a 0) = a 1 ∧ f (a 1) = a 0) ∨
                (∃ f : J.Copy K, ∀ i, f (a i) = b i)) →
              ¬ F ⊑ OMA.edgeAmalgam J K a b) →
        (∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∃ᶠ n : ℕ in atTop,
          ∃ X : SimpleGraph (Fin n), F.Free X ∧
            c * (n : ℝ) ^ α ≤ X.edgeFinset.card ∧
            (∀ u, (X.degree u : ℝ) ≤ D * (n : ℝ) ^ (α - 1)) ∧
            (∀ u ∈ X.support, c * (n : ℝ) ^ (α - 1) ≤ (X.degree u : ℝ))) →
        α ∈ Set.range ((↑) : ℚ → ℝ) := by
  sorry

/-- The superlinear case reduces to a graph minimal at the given power scale. -/
theorem OMA.core_superlinear :
    ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
      ∀ α c : ℝ, α ∈ Set.Ioo 1 2 → 0 < c →
        Asymptotics.IsEquivalent atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => c * (n : ℝ) ^ α) →
        α ∈ Set.range ((↑) : ℚ → ℝ) := by
  intro q G hb _ α c hα hc hG
  by_cases hmatch : ∃ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ G ∧
      2 ≤ J.edgeFinset.card ∧ (OMA.deletionExponent J : ℝ) = α
  · obtain ⟨_, J, _, _, heq⟩ := hmatch
    exact ⟨OMA.deletionExponent J, heq⟩
  · obtain ⟨r, F, hFG, hF, hminimal⟩ :=
      OMA.exists_minimal_extremalPower (OMA.extremalPowerOrder_of_equivalent hc.ne' hG)
    by_cases hupper : ∃ t : ℕ, α = 2 - 1 / (t : ℝ)
    · obtain ⟨t, heq⟩ := hupper
      refine ⟨2 - 1 / (t : ℚ), ?_⟩
      push_cast
      exact heq.symm
    by_cases hsix : α = (4 / 3 : ℝ)
    · exact ⟨4 / 3, by push_cast; exact hsix.symm⟩
    by_cases height : α = (6 / 5 : ℝ)
    · exact ⟨6 / 5, by push_cast; exact height.symm⟩
    apply OMA.core_minimal_power r F (Colorable.of_hom hFG.some.toHom hb) α hα hF hminimal
    · intro s J hJF hJ
      have hle := OMA.exponent_ge_deletion_bound J hJ
        ((OMA.extremalNumber_isBigO_of_contained hJF).trans hF.1)
      exact lt_of_le_of_ne hle (fun heq => hmatch ⟨s, J, hJF.trans hFG, hJ, heq⟩)
    · intro R t ht hcolors E hE hdeg
      exact lt_of_le_of_ne
        (OMA.exponent_le_exceptional_degree_side_bound F R ht hcolors E hE hdeg
          (ne_bot_of_extremalPowerOrder F hF) hF)
        (fun heq => hupper ⟨t, heq⟩)
    · intro hC4
      exact lt_of_le_of_ne (OMA.exponent_ge_cycle_four hC4 hF.1) (fun heq =>
        hupper ⟨2, by rw [← heq]; norm_num⟩)
    · intro hC6
      exact lt_of_le_of_ne (OMA.exponent_ge_cycle_six hC6 hF.1) (Ne.symm hsix)
    · intro hC8
      exact lt_of_le_of_ne (OMA.exponent_ge_cycle_eight hC8 hF.1) (Ne.symm height)
    · intro hK33
      exact lt_of_le_of_ne (OMA.exponent_ge_complete_bipartite_three hK33 hF.1)
        (fun heq => hupper ⟨3, by rw [← heq]; norm_num⟩)
    · intro s J hJF hsize v hJ
      exact OMA.minimal_power_not_contained_rootedDouble hα.1 hF (hminimal s J hJF hsize) v hJ
    · intro j J hJF hj k K hKF hk a b ha hb hK hcase hc
      have hsmallJ := hminimal j J hJF hj
      have hsmallK := hminimal k K hKF hk
      apply hF.2
      apply (OMA.extremalNumber_isBigO_of_contained hc).trans_isLittleO
      rcases hcase with ⟨f, h₀, h₁⟩ | ⟨f, hf⟩
      · exact OMA.extremalNumber_edgeAmalgam_isLittleO_of_flip J K a b ha hb hK f h₀ h₁ hsmallJ hsmallK
      · exact OMA.extremalNumber_edgeAmalgam_isLittleO_of_rooted_copy J K a b hb hK f hf hsmallK
    · exact OMA.frequently_almost_regular_at_extremal_scale F hα.1 hF

theorem OMA.solution : type_of% @Erdos713.erdos_713.parts.ii := by
  intro q G hb he α c hα hc hG
  rcases eq_or_lt_of_le hα.1 with h | h
  · exact ⟨1, by simp [← h]⟩
  · exact OMA.core_superlinear q G hb he α c ⟨h, hα.2⟩ hc hG
