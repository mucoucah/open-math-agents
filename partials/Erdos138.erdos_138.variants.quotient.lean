import FormalConjectures.ErdosProblems.«138»

-- Problem: Erdős Problem 138 — quotient
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/138.lean:121 (declaration Erdos138.erdos_138.variants.quotient)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Coloring formulations for the successive van der Waerden number ratios. -/

namespace OMAErdos138Quotient

open Erdos138 Filter

private lemma mono_of_affine_points {N k : ℕ} {κ : Type} [Finite κ]
    {c : ↥(Finset.Icc 1 N) → κ} (v : κ)
    (f : Fin k → ↥(Finset.Icc 1 N)) {a d : ℕ} (hd : 0 < d)
    (hf : ∀ i : Fin k, (f i).val = a + i.val * d) (hc : ∀ i, c (f i) = v) :
    ContainsMonoAPofLength c k := by
  refine ⟨v, Set.range f, ⟨a, d, ?_, ?_⟩, ?_⟩
  · let g : Fin k → ℕ := fun i => (f i).val
    have hgi : Function.Injective g := by
      intro i j hij
      apply Fin.ext
      apply Nat.mul_right_cancel hd
      exact Nat.add_left_cancel ((hf i).symm.trans (hij.trans (hf j)))
    change ENat.card (Subtype.val '' Set.range f : Set ℕ) = k
    rw [← Set.range_comp]
    change ENat.card (Set.range g) = k
    rw [← ENat.card_congr (Equiv.ofInjective g hgi)]
    simp [ENat.card_eq_coe_fintype_card]
  · rw [← Set.range_comp']
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i.val, by exact_mod_cast i.isLt, ?_⟩
      simpa [nsmul_eq_mul] using (hf i).symm
    · rintro ⟨j, hj, rfl⟩
      let i : Fin k := ⟨j, by exact_mod_cast hj⟩
      refine ⟨i, ?_⟩
      simpa [i, nsmul_eq_mul] using hf i
  · rintro _ ⟨i, rfl⟩
    exact hc i

private lemma affine_points_of_mono {N k : ℕ} {κ : Type} [Finite κ]
    {c : ↥(Finset.Icc 1 N) → κ} (hk : 2 ≤ k) (h : ContainsMonoAPofLength c k) :
    ∃ (v : κ) (a d : ℕ) (f : Fin k → ↥(Finset.Icc 1 N)),
      0 < d ∧ (∀ i : Fin k, (f i).val = a + i.val * d) ∧ ∀ i, c (f i) = v := by
  classical
  obtain ⟨v, s, ha, hc⟩ := h
  obtain ⟨a, d, hcard, hshape⟩ := ha
  have hd : 0 < d := by
    by_contra! hzero
    have hd0 : d = 0 := by omega
    have hincl : (Subtype.val '' s : Set ℕ) ⊆ {a} := by
      rw [hshape]
      rintro _ ⟨j, hj, rfl⟩
      simp [hd0]
    have hle := ENat.card_le_card_of_injective (Set.inclusion_injective hincl)
    rw [show ENat.card (Subtype.val '' s : Set ℕ) = k from hcard] at hle
    have hkle : (k : ℕ∞) ≤ 1 := by simpa using hle
    have hkle' : k ≤ 1 := by exact_mod_cast hkle
    omega
  have hmem (i : Fin k) : ∃ x ∈ s, x.val = a + i.val * d := by
    change a + i.val * d ∈ (Subtype.val '' s : Set ℕ)
    rw [hshape]
    exact ⟨i.val, by exact_mod_cast i.isLt, rfl⟩
  choose f hfs hfv using hmem
  exact ⟨v, a, d, f, hd, hfv, fun i => hc (f i) (hfs i)⟩

private lemma guarantee_nonempty (k : ℕ) : (monoAP_guarantee_set 2 k).Nonempty := by
  classical
  obtain ⟨ι, _, hj⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin 2)
  let N := 1 + Fintype.card ι * k
  refine ⟨N, ?_⟩
  intro c
  let point (w : ι → Fin k) : ↥(Finset.Icc 1 N) :=
    ⟨1 + ∑ i, (w i).val, Finset.mem_Icc.mpr
      ⟨Nat.le_add_right _ _, Nat.add_le_add_left (by
        simpa using (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          (w i).isLt.le)) _⟩⟩
  obtain ⟨line, v, hv⟩ := hj (c ∘ point)
  let free : Finset ι := Finset.univ.filter fun i => line.idxFun i = none
  have hfree : 0 < free.card := by
    obtain ⟨i, hi⟩ := line.proper
    exact Finset.card_pos.mpr ⟨i, by simp [free, hi]⟩
  let a := 1 + ∑ i ∈ freeᶜ, ((line.idxFun i).map Fin.val).getD 0
  refine mono_of_affine_points v (point ∘ line) (a := a) hfree ?_ hv
  intro x
  change 1 + ∑ i, (line x i).val = a + x.val * free.card
  have hvar : ∑ i ∈ free, (line x i).val = free.card * x.val := by
    rw [← Finset.sum_const_nat]
    intro i hi
    rw [line.apply_none _ _ (Finset.mem_filter.mp hi).2]
  have hfix : ∑ i ∈ freeᶜ, (line x i).val =
      ∑ i ∈ freeᶜ, ((line.idxFun i).map Fin.val).getD 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hn : line.idxFun i ≠ none := by simpa [free] using hi
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hn
    simp [← hy]
  rw [← Finset.sum_add_sum_compl free, hvar, hfix]
  dsimp [a]
  ac_rfl

private def includeInterval {n N : ℕ} (h : n ≤ N) (x : ↥(Finset.Icc 1 n)) :
    ↥(Finset.Icc 1 N) :=
  ⟨x.val, Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp x.property).1, (Finset.mem_Icc.mp x.property).2.trans h⟩⟩

private lemma guarantee_mono {r k n N : ℕ} (h : n ≤ N)
    (hn : n ∈ monoAP_guarantee_set r k) : N ∈ monoAP_guarantee_set r k := by
  intro coloring
  obtain ⟨v, s, hap, hcolor⟩ := hn (coloring ∘ includeInterval h)
  refine ⟨v, includeInterval h '' s, ?_, ?_⟩
  · rwa [Set.image_image]
  · rintro _ ⟨x, hx, rfl⟩
    exact hcolor x hx

private lemma exists_avoiding_iff_lt {k N : ℕ}
    (hne : (monoAP_guarantee_set 2 k).Nonempty) :
    (∃ c : ↥(Finset.Icc 1 N) → Fin 2, ¬ ContainsMonoAPofLength c k) ↔ N < W k := by
  classical
  change (∃ c : ↥(Finset.Icc 1 N) → Fin 2, ¬ ContainsMonoAPofLength c k) ↔
    N < sInf (monoAP_guarantee_set 2 k)
  rw [← not_forall, lt_iff_not_ge]
  change N ∉ monoAP_guarantee_set 2 k ↔ ¬ sInf (monoAP_guarantee_set 2 k) ≤ N
  exact not_congr ⟨Nat.sInf_le, fun h => guarantee_mono h (Nat.sInf_mem hne)⟩

private lemma length_le_W {k : ℕ} (hne : (monoAP_guarantee_set 2 k).Nonempty) :
    k ≤ W k := by
  have hw : W k ∈ monoAP_guarantee_set 2 k := Nat.sInf_mem hne
  obtain ⟨_, s, hap, _⟩ := hw (fun _ => (0 : Fin 2))
  have hsub : (Subtype.val '' s : Set ℕ) ⊆ (↑(Finset.Icc 1 (W k)) : Set ℕ) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hcard := ENat.card_le_card_of_injective (Set.inclusion_injective hsub)
  simpa [hap.card, ENat.card_coe_set_eq, Nat.card_Icc] using hcard

private lemma quotient_iff_eventually_avoiding
    (hne : ∀ k, (monoAP_guarantee_set 2 k).Nonempty) :
    Tendsto (fun k => (W (k + 1) : ℚ) / W k) atTop atTop ↔
      ∀ m : ℕ, ∀ᶠ k in atTop,
        ∃ c : ↥(Finset.Icc 1 (m * W k)) → Fin 2, ¬ ContainsMonoAPofLength c (k + 1) := by
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < (W k : ℚ) :=
    eventually_atTop.mpr ⟨1, fun k hk => by
      exact_mod_cast Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hk) (length_le_W (hne k))⟩
  constructor
  · intro h m
    filter_upwards [tendsto_atTop.mp h ((m : ℚ) + 1), hpos] with k hk hpk
    apply (exists_avoiding_iff_lt (hne (k + 1))).mpr
    exact_mod_cast (lt_div_iff₀ hpk).mp ((lt_add_one (m : ℚ)).trans_le hk)
  · intro h
    refine tendsto_atTop.mpr fun q => ?_
    obtain ⟨m, hqm⟩ := exists_nat_ge q
    filter_upwards [h m, hpos] with k hk hpk
    apply hqm.trans
    apply le_of_lt
    apply (lt_div_iff₀ hpk).mpr
    exact_mod_cast (exists_avoiding_iff_lt (hne (k + 1))).mp hk

private def AvoidsCyclicAP (p k : ℕ) (g : ZMod p → Fin 2) : Prop :=
  ∀ a d : ZMod p, d ≠ 0 → ∀ v : Fin 2,
    ∃ i : Fin k, g (a + (i.val : ZMod p) * d) ≠ v

private lemma progression_span_le {N k a d : ℕ} (f : Fin (k + 1) → ↥(Finset.Icc 1 N))
    (hf : ∀ i : Fin (k + 1), (f i).val = a + i.val * d) : 1 + k * d ≤ N := by
  have hfirst := (Finset.mem_Icc.mp (f ⟨0, Nat.zero_lt_succ k⟩).property).1
  have ha : 1 ≤ a := by simpa [hf] using hfirst
  have hlast := (Finset.mem_Icc.mp (f ⟨k, Nat.lt_succ_self k⟩).property).2
  exact (Nat.add_le_add_right ha _).trans (by simpa [hf] using hlast)

private lemma periodic_avoids_of_cyclic {k N p : ℕ} (hk : 1 ≤ k) (hN : N ≤ k * p)
    {g : ZMod p → Fin 2} (hg : AvoidsCyclicAP p (k + 1) g) :
    ¬ ContainsMonoAPofLength (fun x : ↥(Finset.Icc 1 N) => g x.val) (k + 1) := by
  intro h
  obtain ⟨v, a, d, f, hd, hfp, hfc⟩ := affine_points_of_mono (by omega) h
  have hz : (d : ZMod p) ≠ 0 := by
    intro hzero
    have hpd := Nat.le_of_dvd hd ((ZMod.natCast_eq_zero_iff d p).mp hzero)
    have hmul := Nat.mul_le_mul_left k hpd
    have hspan := progression_span_le f hfp
    omega
  obtain ⟨i, hi⟩ := hg (a : ZMod p) (d : ZMod p) hz v
  apply hi
  simpa [hfp, Nat.cast_add, Nat.cast_mul] using hfc i

private lemma avoiding_of_cyclic {k N p : ℕ} (hk : 1 ≤ k) (hN : N ≤ k * p)
    {g : ZMod p → Fin 2} (hg : AvoidsCyclicAP p (k + 1) g) :
    ∃ c : ↥(Finset.Icc 1 N) → Fin 2, ¬ ContainsMonoAPofLength c (k + 1) :=
  ⟨_, periodic_avoids_of_cyclic hk hN hg⟩

private lemma mono_of_short_cyclic_step {k p : ℕ} [NeZero p] (hk : 2 ≤ k)
    {g : ZMod p → Fin 2} {a d : ZMod p} {v : Fin 2}
    (hd : d ≠ 0) (hshort : 2 * d.val ≤ p)
    (hmono : ∀ i : Fin (k + 1), g (a + (i.val : ZMod p) * d) = v) :
    ContainsMonoAPofLength (fun x : ↥(Finset.Icc 1 (k * p)) => g x.val) (k + 1) := by
  let A := (a - 1).val + 1
  have hA : (A : ZMod p) = a := by
    simp [A, Nat.cast_add]
  have hAp : A ≤ p := ZMod.val_lt (a - 1)
  have hstep : 0 < d.val := Nat.pos_of_ne_zero (fun h => hd ((ZMod.val_eq_zero d).mp h))
  have hspan := Nat.mul_le_mul_left k hshort
  have hbase := Nat.mul_le_mul_right p hk
  rw [← Nat.mul_assoc, Nat.mul_comm k 2, Nat.mul_assoc] at hspan
  have htotal : A + k * d.val ≤ k * p := by omega
  let f (i : Fin (k + 1)) : ↥(Finset.Icc 1 (k * p)) :=
    ⟨A + i.val * d.val, Finset.mem_Icc.mpr
      ⟨by dsimp [A]; omega, (Nat.add_le_add_left
        (Nat.mul_le_mul_right d.val (Nat.lt_succ_iff.mp i.isLt)) A).trans htotal⟩⟩
  refine mono_of_affine_points v f hstep (fun _ => rfl) ?_
  intro i
  change g ((↑(A + i.val * d.val)) : ZMod p) = v
  simpa [Nat.cast_add, Nat.cast_mul, hA, ZMod.natCast_zmod_val] using hmono i

private lemma periodic_avoids_iff_cyclic {k p : ℕ} [NeZero p] (hk : 2 ≤ k)
    (g : ZMod p → Fin 2) :
    (¬ ContainsMonoAPofLength (fun x : ↥(Finset.Icc 1 (k * p)) => g x.val) (k + 1)) ↔
      AvoidsCyclicAP p (k + 1) g := by
  refine ⟨?_, periodic_avoids_of_cyclic (by omega) le_rfl⟩
  intro h a d hd v
  by_contra! hmono
  apply h
  by_cases hshort : 2 * d.val ≤ p
  · exact mono_of_short_cyclic_step hk hd hshort hmono
  · have hshort' : 2 * (-d).val ≤ p := by
      rw [ZMod.neg_val, if_neg hd]
      omega
    apply mono_of_short_cyclic_step (a := a + (k : ZMod p) * d) hk
      (neg_ne_zero.mpr hd) hshort'
    intro i
    have hcast : (i.rev.val : ZMod p) = (k : ZMod p) - (i.val : ZMod p) := by
      rw [Fin.val_rev]
      simp [Nat.cast_sub (Nat.lt_succ_iff.mp i.isLt)]
    convert hmono i.rev using 2
    rw [hcast]
    ring

private lemma quotient_of_eventually_cyclic
    (h : ∀ m : ℕ, ∀ᶠ k in atTop, ∃ p : ℕ, m * W k ≤ k * p ∧
      ∃ g : ZMod p → Fin 2, AvoidsCyclicAP p (k + 1) g) :
    Tendsto (fun k => (W (k + 1) : ℚ) / W k) atTop atTop := by
  apply (quotient_iff_eventually_avoiding guarantee_nonempty).mpr
  intro m
  filter_upwards [eventually_ge_atTop 1, h m] with k hk hc
  obtain ⟨p, hp, g, hg⟩ := hc
  exact avoiding_of_cyclic hk hp hg

private def RobustCyclicAvoidance (p n : ℕ) (g : ZMod p → Fin 2) : Prop :=
  ∀ a d : ZMod p, d ≠ 0 → ∀ (v : Fin 2) (s : Finset (Fin n)), s.card ≤ 2 →
    ∃ i ∉ s, g (a + (i.val : ZMod p) * d) ≠ v

private lemma cyclic_zero_positions {q n : ℕ} [Fact q.Prime]
    (hlo : q ≤ n) (hhi : n ≤ 2 * q) (a d : ZMod q) (hd : d ≠ 0) :
    ∃ s : Finset (Fin n), s.Nonempty ∧ s.card ≤ 2 ∧
      ∀ i : Fin n, i ∈ s ↔ a + (i.val : ZMod q) * d = 0 := by
  let s := Finset.univ.filter fun i : Fin n => a + (i.val : ZMod q) * d = 0
  have hmem (i : Fin n) : i ∈ s ↔ a + (i.val : ZMod q) * d = 0 := by simp [s]
  refine ⟨s, ?_, ?_, hmem⟩
  · let t := -a / d
    let i : Fin n := ⟨t.val, (ZMod.val_lt t).trans_le hlo⟩
    refine ⟨i, (hmem i).mpr ?_⟩
    change a + (t.val : ZMod q) * d = 0
    simp [t, hd]
  · have hcard : s.card ≤ (Finset.range 2).card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val / q)
      · intro i _
        apply Finset.mem_range.mpr
        exact (Nat.div_lt_iff_lt_mul (Fact.out : q.Prime).pos).mpr (i.isLt.trans_le hhi)
      · intro i hi j hj hdiv
        have hcast : (i.val : ZMod q) = (j.val : ZMod q) := by
          apply mul_right_cancel₀ hd
          linear_combination (hmem i).mp hi - (hmem j).mp hj
        have hmod : i.val % q = j.val % q := by
          simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast
        change i.val / q = j.val / q at hdiv
        exact Fin.ext (by rw [← Nat.mod_add_div i.val q, ← Nat.mod_add_div j.val q, hmod, hdiv])
    simpa using hcard

-- The second modulus flips the first coloring at at most two positions of a mixed-step AP.
private lemma avoiding_of_robust_cyclic {k N p q : ℕ} [Fact q.Prime]
    (hk : 2 ≤ k) (hco : p.Coprime q) (hlo : q ≤ k + 1) (hhi : k + 1 ≤ 2 * q)
    (hN : N ≤ k * (p * q)) {g : ZMod p → Fin 2} (hg : RobustCyclicAvoidance p (k + 1) g) :
    ∃ c : ↥(Finset.Icc 1 N) → Fin 2, ¬ ContainsMonoAPofLength c (k + 1) := by
  let c (x : ↥(Finset.Icc 1 N)) :=
    if (x.val : ZMod q) = 0 then (g x.val).rev else g x.val
  refine ⟨c, fun h => ?_⟩
  obtain ⟨v, a, d, f, hd, hfp, hfc⟩ := affine_points_of_mono (by omega) h
  let P (i : Fin (k + 1)) : ZMod p := (a : ZMod p) + (i.val : ZMod p) * (d : ZMod p)
  let Q (i : Fin (k + 1)) : ZMod q := (a : ZMod q) + (i.val : ZMod q) * (d : ZMod q)
  have hcolor (i : Fin (k + 1)) : (if Q i = 0 then (g (P i)).rev else g (P i)) = v := by
    simpa [c, P, Q, hfp, Nat.cast_add, Nat.cast_mul] using hfc i
  by_cases hq : (d : ZMod q) = 0
  · have hp : (d : ZMod p) ≠ 0 := by
      intro hdp
      have hdiv := hco.mul_dvd_of_dvd_of_dvd
        ((ZMod.natCast_eq_zero_iff d p).mp hdp) ((ZMod.natCast_eq_zero_iff d q).mp hq)
      have hmul := Nat.mul_le_mul_left k (Nat.le_of_dvd hd hdiv)
      have hspan := progression_span_le f hfp
      omega
    by_cases ha : (a : ZMod q) = 0
    · obtain ⟨i, _, hi⟩ := hg (a : ZMod p) (d : ZMod p) hp v.rev ∅ (by simp)
      apply hi
      have hh : (g (P i)).rev = v := by simpa [Q, hq, ha] using hcolor i
      simpa using congrArg Fin.rev hh
    · obtain ⟨i, _, hi⟩ := hg (a : ZMod p) (d : ZMod p) hp v ∅ (by simp)
      apply hi
      simpa [Q, hq, ha] using hcolor i
  · obtain ⟨s, hs, hcard, hmem⟩ := cyclic_zero_positions hlo hhi (a : ZMod q) (d : ZMod q) hq
    by_cases hp : (d : ZMod p) = 0
    · obtain ⟨i, hi⟩ := hs
      have hout : ∃ j, j ∉ s := by
        by_contra! hall
        rw [Finset.eq_univ_of_forall hall, Finset.card_univ, Fintype.card_fin] at hcard
        omega
      obtain ⟨j, hj⟩ := hout
      have hQi : Q i = 0 := (hmem i).mp hi
      have hQj : Q j ≠ 0 := mt (hmem j).mpr hj
      have hvi : (g (a : ZMod p)).rev = v := by
        simpa [P, hp, hQi] using hcolor i
      have hvj : g (a : ZMod p) = v := by
        simpa [P, hp, hQj] using hcolor j
      rw [hvj] at hvi
      exact (show ∀ x : Fin 2, x.rev ≠ x by decide) v hvi
    · obtain ⟨i, hi, hgi⟩ := hg (a : ZMod p) (d : ZMod p) hp v s hcard
      have hQi : Q i ≠ 0 := mt (hmem i).mpr hi
      apply hgi
      simpa [hQi] using hcolor i

private lemma quotient_of_eventually_robust_cyclic
    (h : ∀ m : ℕ, ∀ᶠ k in atTop, ∃ p q : ℕ, q.Prime ∧ p.Coprime q ∧
      q ≤ k + 1 ∧ k + 1 ≤ 2 * q ∧ m * W k ≤ k * (p * q) ∧
      ∃ g : ZMod p → Fin 2, RobustCyclicAvoidance p (k + 1) g) :
    Tendsto (fun k => (W (k + 1) : ℚ) / W k) atTop atTop := by
  apply (quotient_iff_eventually_avoiding guarantee_nonempty).mpr
  intro m
  filter_upwards [eventually_ge_atTop 2, h m] with k hk hc
  obtain ⟨p, q, hq, hco, hlo, hhi, hN, g, hg⟩ := hc
  let _ : Fact q.Prime := ⟨hq⟩
  exact avoiding_of_robust_cyclic hk hco hlo hhi hN hg

end OMAErdos138Quotient

theorem OMA.solution : type_of% @Erdos138.erdos_138.variants.quotient := by
  apply (OMAErdos138Quotient.quotient_iff_eventually_avoiding
    OMAErdos138Quotient.guarantee_nonempty).mpr
  sorry

