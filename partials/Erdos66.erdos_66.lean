import FormalConjectures.ErdosProblems.«66»

/-!
# Erdős Problem 66

A compactness reduction to finite prefix constraints with rational bounds on
the representation count divided by the integer base-two logarithm.
-/
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/66.lean:40 (declaration Erdos66.erdos_66)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter AdditiveCombinatorics
open scoped Topology

namespace OMA.Erdos66

private lemma sumRep_eq_of_agree_below {A B : Set ℕ} {n : ℕ}
    (h : ∀ m ≤ n, m ∈ A ↔ m ∈ B) : sumRep A n = sumRep B n := by
  classical
  rw [sumRep_def, sumRep_def]
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact and_congr (h p.1 (by omega)) (h p.2 (by omega))

private lemma continuous_sumRep_indicator (n : ℕ) :
    Continuous (fun f : ℕ → Bool => sumRep {m | f m = true} n) := by
  classical
  let restriction : (ℕ → Bool) → (Fin (n + 1) → Bool) := fun f i => f i
  let count : (Fin (n + 1) → Bool) → ℕ :=
    fun f => sumRep {m | ∃ i : Fin (n + 1), (i : ℕ) = m ∧ f i = true} n
  have hrestriction : Continuous restriction := continuous_pi fun _ => continuous_apply _
  have hcount : Continuous count := continuous_of_discreteTopology
  convert hcount.comp hrestriction using 1
  funext f
  apply sumRep_eq_of_agree_below
  intro m hm
  constructor
  · intro hf
    exact ⟨⟨m, by omega⟩, rfl, hf⟩
  · rintro ⟨i, rfl, hi⟩
    exact hi

/-- Constraints involving one representation count at a time have a global solution
whenever every finite prefix has a solution. -/
lemma exists_set_of_finite_sumRep_constraints (P : ℕ → Set ℕ)
    (h : ∀ N, ∃ B : Finset ℕ, ∀ n ≤ N, sumRep (↑B : Set ℕ) n ∈ P n) :
    ∃ A : Set ℕ, ∀ n, sumRep A n ∈ P n := by
  classical
  let C (n : ℕ) : Set (ℕ → Bool) := {f | sumRep {m | f m = true} n ∈ P n}
  have hclosed (n) : IsClosed (C n) :=
    (isClosed_discrete (P n)).preimage (continuous_sumRep_indicator n)
  have hfinite (s : Finset ℕ) : (⋂ n ∈ s, C n).Nonempty := by
    obtain ⟨B, hB⟩ := h (s.sup id)
    refine ⟨fun m => decide (m ∈ B), ?_⟩
    simp only [Set.mem_iInter]
    intro n hn
    change sumRep {m | decide (m ∈ B) = true} n ∈ P n
    have hBset : {m : ℕ | decide (m ∈ B) = true} = (↑B : Set ℕ) := by
      ext m
      simp
    rw [hBset]
    exact hB n (Finset.le_sup (f := id) hn)
  obtain ⟨f, hf⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  exact ⟨{m | f m = true}, Set.mem_iInter.mp hf⟩

private lemma tendsto_natLog_two_atTop :
    Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ)) atTop atTop := by
  refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_atTop.mpr fun k => ?_)
  exact ⟨2 ^ k, fun n hn => Nat.le_log_of_pow_le Nat.one_lt_two hn⟩

lemma tendsto_log_div_natLog_two :
    Tendsto (fun n : ℕ => Real.log n / (Nat.log 2 n : ℝ)) atTop (𝓝 (Real.log 2)) := by
  have hupper : Tendsto (fun n : ℕ => Real.log 2 + Real.log 2 / (Nat.log 2 n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natLog_two_atTop)
  have hbounds : ∀ᶠ n : ℕ in atTop,
      Real.log 2 ≤ Real.log n / (Nat.log 2 n : ℝ) ∧
        Real.log n / (Nat.log 2 n : ℝ) ≤ Real.log 2 + Real.log 2 / (Nat.log 2 n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hpos : 0 < (Nat.log 2 n : ℝ) := by
      exact_mod_cast Nat.log_pos Nat.one_lt_two hn
    have hlo : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have hhi : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have hloglo := Real.log_le_log (by positivity) hlo
    have hloghi := Real.log_lt_log (by exact_mod_cast (by omega : 0 < n)) hhi
    rw [Real.log_pow] at hloglo hloghi
    push_cast at hloghi
    constructor
    · exact (le_div_iff₀ hpos).2 (by linarith)
    · apply (div_le_iff₀ hpos).2
      rw [add_mul, div_mul_cancel₀ _ hpos.ne']
      linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

lemma tendsto_div_natLog_two_iff (u : ℕ → ℝ) (c : ℝ) :
    Tendsto (fun n => u n / (Nat.log 2 n : ℝ)) atTop (𝓝 c) ↔
      Tendsto (fun n => u n / Real.log n) atTop (𝓝 (c / Real.log 2)) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop, (Nat.log 2 n : ℝ) ≠ 0 ∧ Real.log n ≠ 0 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnat : 0 < (Nat.log 2 n : ℝ) := by exact_mod_cast Nat.log_pos Nat.one_lt_two hn
    have hreal : 0 < Real.log n :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    exact ⟨hnat.ne', hreal.ne'⟩
  constructor
  · intro h
    apply (h.div tendsto_log_div_natLog_two htwo.ne').congr'
    filter_upwards [hevent] with n hn
    dsimp
    field_simp [hn.1, hn.2]
  · intro h
    have hmul := h.mul tendsto_log_div_natLog_two
    rw [div_mul_cancel₀ _ htwo.ne'] at hmul
    apply hmul.congr'
    filter_upwards [hevent] with n hn
    field_simp [hn.1, hn.2]

/-- All constraints on a prefix are rational inequalities. Only indices k with
k + 2 ≤ M can contribute a constraint at prefix length M. -/
def finiteDyadicRepresentation : Prop :=
  ∃ (L U : ℕ → ℚ) (start : ℕ → ℕ),
    0 < L 0 ∧
    (∀ k, U k - L k ≤ 1 / (k + 1 : ℚ)) ∧
    ∀ M, ∃ B : Finset ℕ, B ⊆ Finset.range (M + 1) ∧
      ∀ k n, max (k + 2) (start k) ≤ n → n ≤ M →
        L k ≤ (sumRep (↑B : Set ℕ) n : ℚ) / (Nat.log 2 n : ℚ) ∧
          (sumRep (↑B : Set ℕ) n : ℚ) / (Nat.log 2 n : ℚ) ≤ U k

private lemma rat_ratioBounds_iff (l u : ℚ) (a b : ℕ) :
    (l ≤ (a : ℚ) / b ∧ (a : ℚ) / b ≤ u) ↔
      ((l : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b ≤ (u : ℝ)) := by
  rw [← Rat.cast_le (K := ℝ), ← Rat.cast_le (K := ℝ) (p := (a : ℚ) / b) (q := u)]
  simp only [Rat.cast_div, Rat.cast_natCast]

lemma exists_limit_of_finiteDyadicRepresentation (h : finiteDyadicRepresentation) :
    ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
      Tendsto (fun n => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  obtain ⟨L, U, start, hL, hwidth, hfinite⟩ := h
  let P (n : ℕ) : Set ℕ := {r | ∀ k, max (k + 2) (start k) ≤ n →
    L k ≤ (r : ℚ) / (Nat.log 2 n : ℚ) ∧ (r : ℚ) / (Nat.log 2 n : ℚ) ≤ U k}
  obtain ⟨A, hA⟩ : ∃ A : Set ℕ, ∀ n, sumRep A n ∈ P n := by
    apply exists_set_of_finite_sumRep_constraints
    intro M
    obtain ⟨B, _, hB⟩ := hfinite M
    exact ⟨B, fun n hn k hk => hB k n hk hn⟩
  let u (n : ℕ) : ℝ := (sumRep A n : ℝ) / (Nat.log 2 n : ℝ)
  have hb (k n : ℕ) (hn : max (k + 2) (start k) ≤ n) :
      (L k : ℝ) ≤ u n ∧ u n ≤ (U k : ℝ) := by
    have hr : L k ≤ (sumRep A n : ℚ) / (Nat.log 2 n : ℚ) ∧
        (sumRep A n : ℚ) / (Nat.log 2 n : ℚ) ≤ U k := hA n k hn
    dsimp [u]
    exact (rat_ratioBounds_iff _ _ _ _).mp hr
  have hcauchy : CauchySeq u := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    have hw : (U k : ℝ) - (L k : ℝ) ≤ 1 / (k + 1 : ℝ) := by
      simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr (hwidth k)
    refine ⟨max (k + 2) (start k), fun m hm n hn => ?_⟩
    have ⟨hml, hmu⟩ := hb k m hm
    have ⟨hnl, hnu⟩ := hb k n hn
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hdpos : 0 < d := by
    have hlpos : (0 : ℝ) < (L 0 : ℝ) := by exact_mod_cast hL
    apply hlpos.trans_le
    exact ge_of_tendsto hd <|
      (eventually_ge_atTop (max (0 + 2) (start 0))).mono fun n hn => (hb 0 n hn).1
  refine ⟨A, d / Real.log 2, div_pos hdpos (Real.log_pos (by norm_num)), ?_⟩
  exact (tendsto_div_natLog_two_iff (fun n => (sumRep A n : ℝ)) d).mp hd

lemma finiteDyadicRepresentation_of_exists_limit
    (h : ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    finiteDyadicRepresentation := by
  classical
  obtain ⟨A, c, hc, ht⟩ := h
  let u (n : ℕ) : ℝ := (sumRep A n : ℝ) / (Nat.log 2 n : ℝ)
  let d : ℝ := c * Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : Tendsto u atTop (𝓝 d) := by
    apply (tendsto_div_natLog_two_iff (fun n => (sumRep A n : ℝ)) d).mpr
    simpa only [d, mul_div_cancel_right₀ _ htwo.ne'] using ht
  have hdpos : 0 < d := by
    refine lt_of_le_of_ne (ge_of_tendsto' hd (fun n => ?_)) (Ne.symm ?_)
    · dsimp [u]
      positivity
    · exact mul_ne_zero hc htwo.ne'
  have hinterval (k : ℕ) : ∃ (l r : ℚ) (N : ℕ),
      0 < l ∧ r - l ≤ 1 / (k + 1 : ℚ) ∧
        ∀ n ≥ N, (l : ℝ) ≤ u n ∧ u n ≤ r := by
    let δ : ℝ := (1 / (k + 1 : ℝ)) / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨l, hl, hld⟩ := exists_rat_btwn (show max 0 (d - δ) < d by
      exact max_lt hdpos (by linarith))
    obtain ⟨r, hdr, hr⟩ := exists_rat_btwn (show d < d + δ by linarith)
    have hwidth : r - l ≤ 1 / (k + 1 : ℚ) := by
      apply (Rat.cast_le (K := ℝ)).mp
      push_cast
      have hlow : d - δ < (l : ℝ) := lt_of_le_of_lt (le_max_right _ _) hl
      dsimp [δ] at hlow hr
      linarith
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hd
      (min (d - (l : ℝ)) ((r : ℝ) - d)) (lt_min (sub_pos.mpr hld) (sub_pos.mpr hdr))
    refine ⟨l, r, N, ?_, hwidth, fun n hn => ?_⟩
    · exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hl
    · have hnear := hN n hn
      rw [Real.dist_eq, lt_min_iff, abs_lt, abs_lt] at hnear
      constructor <;> linarith [hnear.1.1, hnear.2.2]
  choose L U start hL hwidth hbounds using hinterval
  refine ⟨L, U, start, hL 0, hwidth, fun M => ?_⟩
  let B := (Finset.range (M + 1)).filter fun m => m ∈ A
  refine ⟨B, Finset.filter_subset _ _, fun k n hkn hnM => ?_⟩
  have hsame : sumRep (↑B : Set ℕ) n = sumRep A n := by
    apply sumRep_eq_of_agree_below
    intro m hm
    have hmM : m ≤ M := hm.trans hnM
    simp [B, hmM]
  rw [hsame]
  exact (rat_ratioBounds_iff _ _ _ _).mpr (hbounds k n (le_trans (le_max_right _ _) hkn))

open scoped Classical in
/-- Below twice the cutoff, each new representation uses exactly one entry at or above
the cutoff. Its ordered count is twice the number of admissible new entries. -/
lemma sumRep_eq_prefix_add_twice (A : Set ℕ) {m n : ℕ} (hn : n < 2 * m) :
    sumRep A n = sumRep (A ∩ Set.Iio m) n +
      2 * ((Finset.Icc m n).filter fun j => j ∈ A ∧ n - j ∈ A ∧ n - j < m).card := by
  classical
  let R := (Finset.HasAntidiagonal.antidiagonal n).filter
    fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A
  let early := R.filter fun p => p.1 < m
  let low := early.filter fun p => p.2 < m
  let left := R.filter fun p => m ≤ p.1
  let right := early.filter fun p => m ≤ p.2
  let choices := (Finset.Icc m n).filter fun j => j ∈ A ∧ n - j ∈ A ∧ n - j < m
  have hR : early.card + left.card = R.card := by
    simpa only [early, left, not_lt] using
      (Finset.card_filter_add_card_filter_not (s := R) fun p => p.1 < m)
  have hearly : low.card + right.card = early.card := by
    simpa only [low, right, not_lt] using
      (Finset.card_filter_add_card_filter_not (s := early) fun p => p.2 < m)
  have hlow : sumRep (A ∩ Set.Iio m) n = low.card := by
    rw [sumRep_def]
    congr 1
    ext p
    simp only [low, early, R, Finset.mem_filter, Set.mem_inter_iff, Set.mem_Iio]
    tauto
  have hswap : left.card = right.card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    · intro p hp
      simp only [Finset.mem_coe, left, R, Finset.mem_filter,
        Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rcases hp with ⟨⟨hs, h₁, h₂⟩, hm⟩
      simp only [Finset.mem_coe, right, early, R, Finset.mem_filter,
        Finset.HasAntidiagonal.mem_antidiagonal, Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨⟨by omega, h₂, h₁⟩, by omega⟩, hm⟩
    · intro p hp
      simp only [Finset.mem_coe, right, early, R, Finset.mem_filter,
        Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rcases hp with ⟨⟨⟨hs, h₁, h₂⟩, _⟩, hm⟩
      simp only [Finset.mem_coe, left, R, Finset.mem_filter,
        Finset.HasAntidiagonal.mem_antidiagonal, Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨by omega, h₂, h₁⟩, hm⟩
  have hchoices : right.card = choices.card := by
    refine Finset.card_nbij' Prod.snd (fun j => (n - j, j)) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro p hp
      simp only [Finset.mem_coe, right, early, R, Finset.mem_filter,
        Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rcases hp with ⟨⟨⟨hs, h₁, h₂⟩, hlo⟩, hhi⟩
      have hsub : n - p.2 = p.1 := by omega
      simp only [Finset.mem_coe, choices, Finset.mem_filter, Finset.mem_Icc, hsub]
      exact ⟨⟨hhi, by omega⟩, h₂, h₁, hlo⟩
    · intro j hj
      simp only [Finset.mem_coe, choices, Finset.mem_filter, Finset.mem_Icc] at hj
      rcases hj with ⟨⟨hlo, hhi⟩, hj, hsub, hm⟩
      simp only [Finset.mem_coe, right, early, R, Finset.mem_filter,
        Finset.HasAntidiagonal.mem_antidiagonal]
      exact ⟨⟨⟨by omega, hsub, hj⟩, hm⟩, hlo⟩
    · intro p hp
      simp only [Finset.mem_coe, right, early, R, Finset.mem_filter,
        Finset.HasAntidiagonal.mem_antidiagonal] at hp
      exact Prod.ext (by dsimp; omega) rfl
  rw [sumRep_def A n]
  change R.card = sumRep (A ∩ Set.Iio m) n + 2 * choices.card
  omega

/-- With the prefix fixed, each extension bit has coefficient zero or two in the
representation count at any sum below twice the cutoff. -/
lemma sumRep_union_extension {B D : Finset ℕ} {m n : ℕ}
    (hB : B ⊆ Finset.range m) (hD : D ⊆ Finset.Ico m (2 * m)) (hn : n < 2 * m) :
    sumRep (↑(B ∪ D) : Set ℕ) n = sumRep (↑B : Set ℕ) n +
      2 * (D.filter fun j => j ≤ n ∧ n - j ∈ B).card := by
  classical
  have hbelow {j : ℕ} (hj : j ∈ B) : j < m := Finset.mem_range.mp (hB hj)
  have habove {j : ℕ} (hj : j ∈ D) : m ≤ j := (Finset.mem_Ico.mp (hD hj)).1
  have hcut : (↑(B ∪ D) : Set ℕ) ∩ Set.Iio m = (↑B : Set ℕ) := by
    ext j
    simp only [Set.mem_inter_iff, Set.mem_Iio, Finset.mem_coe, Finset.mem_union]
    constructor
    · rintro ⟨hj | hj, hm⟩
      · exact hj
      · exact False.elim (not_lt_of_ge (habove hj) hm)
    · intro hj
      exact ⟨Or.inl hj, hbelow hj⟩
  rw [sumRep_eq_prefix_add_twice _ hn, hcut]
  congr 3
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_coe, Finset.mem_union]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hj, hsub, hm⟩
    exact ⟨hj.resolve_left fun hj => not_lt_of_ge hlo (hbelow hj), hhi,
      hsub.resolve_right fun hsub => not_lt_of_ge (habove hsub) hm⟩
  · rintro ⟨hj, hhi, hsub⟩
    exact ⟨⟨habove hj, hhi⟩, Or.inr hj, Or.inl hsub, hbelow hsub⟩

/-- A prefix invariant that permits all dyadic extensions supplies a global set.
At each stage the extension conditions involve only the new membership bits. -/
lemma exists_set_of_dyadic_extensions (P : ℕ → Set ℕ) (good : ℕ → Finset ℕ → Prop)
    (hinit : ∃ B : Finset ℕ, B ⊆ Finset.range 1 ∧ good 0 B ∧ sumRep (↑B : Set ℕ) 0 ∈ P 0)
    (hstep : ∀ k (B : Finset ℕ), B ⊆ Finset.range (2 ^ k) → good k B →
      ∃ D : Finset ℕ, D ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) ∧ good (k + 1) (B ∪ D) ∧
        ∀ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          sumRep (↑B : Set ℕ) n + 2 * (D.filter fun j => j ≤ n ∧ n - j ∈ B).card ∈ P n) :
    ∃ A : Set ℕ, ∀ n, sumRep A n ∈ P n := by
  have hprefix (k : ℕ) : ∃ B : Finset ℕ,
      B ⊆ Finset.range (2 ^ k) ∧ good k B ∧ ∀ n < 2 ^ k, sumRep (↑B : Set ℕ) n ∈ P n := by
    induction k with
    | zero =>
      obtain ⟨B, hB, hg, hzero⟩ := hinit
      refine ⟨B, hB, hg, fun n hn => ?_⟩
      have h : n = 0 := by simpa using hn
      simpa only [h] using hzero
    | succ k ih =>
      obtain ⟨B, hB, hg, hcounts⟩ := ih
      obtain ⟨D, hD, hnext, hband⟩ := hstep k B hB hg
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
      have hle : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := by rw [hpow]; omega
      refine ⟨B ∪ D, ?_, hnext, fun n hn => ?_⟩
      · intro m hm
        apply Finset.mem_range.mpr
        rcases Finset.mem_union.mp hm with hm | hm
        · exact (Finset.mem_range.mp (hB hm)).trans_le hle
        · exact (Finset.mem_Ico.mp (hD hm)).2
      · by_cases hold : n < 2 ^ k
        · have hagree : sumRep (↑(B ∪ D) : Set ℕ) n = sumRep (↑B : Set ℕ) n := by
            apply sumRep_eq_of_agree_below
            intro m hm
            have hnot : m ∉ D := fun hmD =>
              (not_lt_of_ge (Finset.mem_Ico.mp (hD hmD)).1) (hm.trans_lt hold)
            simp [hnot]
          rw [hagree]
          exact hcounts n hold
        · rw [sumRep_union_extension hB (hpow ▸ hD) (hpow ▸ hn)]
          exact hband n (Finset.mem_Ico.mpr ⟨le_of_not_gt hold, hn⟩)
  apply exists_set_of_finite_sumRep_constraints P
  intro N
  obtain ⟨B, _, _, hcounts⟩ := hprefix N
  exact ⟨B, fun n hn => hcounts n (hn.trans_lt N.lt_two_pow_self)⟩

/-- An invariant on finite prefixes and the local constraints it must preserve. -/
def HasDyadicExtensions (P : ℕ → Set ℕ) : Prop :=
  ∃ good : ℕ → Finset ℕ → Prop,
    (∃ B : Finset ℕ, B ⊆ Finset.range 1 ∧ good 0 B ∧ sumRep (↑B : Set ℕ) 0 ∈ P 0) ∧
    ∀ k (B : Finset ℕ), B ⊆ Finset.range (2 ^ k) → good k B →
      ∃ D : Finset ℕ, D ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) ∧ good (k + 1) (B ∪ D) ∧
        ∀ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          sumRep (↑B : Set ℕ) n + 2 * (D.filter fun j => j ≤ n ∧ n - j ∈ B).card ∈ P n

lemma hasDyadicExtensions_iff_exists_set (P : ℕ → Set ℕ) :
    HasDyadicExtensions P ↔ ∃ A : Set ℕ, ∀ n, sumRep A n ∈ P n := by
  classical
  constructor
  · rintro ⟨good, hinit, hstep⟩
    exact exists_set_of_dyadic_extensions P good hinit hstep
  · rintro ⟨A, hA⟩
    let truncation (m : ℕ) := (Finset.range m).filter fun j => j ∈ A
    have hmem (m j : ℕ) : j ∈ truncation m ↔ j < m ∧ j ∈ A := by simp [truncation]
    have hcounts {m n : ℕ} (hn : n < m) : sumRep (↑(truncation m) : Set ℕ) n ∈ P n := by
      have heq : sumRep (↑(truncation m) : Set ℕ) n = sumRep A n := by
        apply sumRep_eq_of_agree_below
        intro j hj
        simp [hmem, hj.trans_lt hn]
      simpa only [heq] using hA n
    refine ⟨fun k B => B = truncation (2 ^ k), ⟨truncation 1, Finset.filter_subset _ _, rfl,
      hcounts Nat.zero_lt_one⟩, ?_⟩
    intro k B hB hgood
    change B = truncation (2 ^ k) at hgood
    subst B
    let D := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter fun j => j ∈ A
    have hD : D ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := Finset.filter_subset _ _
    have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
    have hle : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := by rw [hpow]; omega
    have hunion : truncation (2 ^ k) ∪ D = truncation (2 ^ (k + 1)) := by
      ext j
      simp only [Finset.mem_union, hmem, D, Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro (⟨hj, hA⟩ | ⟨⟨_, hj⟩, hA⟩)
        · exact ⟨hj.trans_le hle, hA⟩
        · exact ⟨hj, hA⟩
      · rintro ⟨hj, hA⟩
        by_cases hbelow : j < 2 ^ k
        · exact Or.inl ⟨hbelow, hA⟩
        · exact Or.inr ⟨⟨le_of_not_gt hbelow, hj⟩, hA⟩
    refine ⟨D, hD, hunion, fun n hn => ?_⟩
    have htop := (Finset.mem_Ico.mp hn).2
    rw [← sumRep_union_extension hB (hpow ▸ hD) (hpow ▸ htop), hunion]
    exact hcounts htop

lemma finiteDyadicRepresentation_iff_hasDyadicExtensions :
    finiteDyadicRepresentation ↔
      ∃ (L U : ℕ → ℚ) (start : ℕ → ℕ), 0 < L 0 ∧
        (∀ k, U k - L k ≤ 1 / (k + 1 : ℚ)) ∧
        HasDyadicExtensions (fun n => {r | ∀ k, max (k + 2) (start k) ≤ n →
          L k ≤ (r : ℚ) / (Nat.log 2 n : ℚ) ∧ (r : ℚ) / (Nat.log 2 n : ℚ) ≤ U k}) := by
  classical
  constructor
  · rintro ⟨L, U, start, hL, hwidth, hfinite⟩
    refine ⟨L, U, start, hL, hwidth, (hasDyadicExtensions_iff_exists_set _).mpr ?_⟩
    apply exists_set_of_finite_sumRep_constraints
    intro M
    obtain ⟨B, _, hB⟩ := hfinite M
    exact ⟨B, fun n hn k hk => hB k n hk hn⟩
  · rintro ⟨L, U, start, hL, hwidth, hgood⟩
    obtain ⟨A, hA⟩ := (hasDyadicExtensions_iff_exists_set _).mp hgood
    refine ⟨L, U, start, hL, hwidth, fun M => ?_⟩
    let B := (Finset.range (M + 1)).filter fun j => j ∈ A
    refine ⟨B, Finset.filter_subset _ _, fun k n hkn hnM => ?_⟩
    have heq : sumRep (↑B : Set ℕ) n = sumRep A n := by
      apply sumRep_eq_of_agree_below
      intro j hj
      simp [B, hj.trans hnM]
    rw [heq]
    exact hA n k hkn

end OMA.Erdos66

theorem OMA.solution : type_of% @Erdos66.erdos_66 := by
  have hfinite : OMA.Erdos66.finiteDyadicRepresentation := by
    sorry
  obtain ⟨A, c, hc, hlim⟩ := OMA.Erdos66.exists_limit_of_finiteDyadicRepresentation hfinite
  exact ⟨A, c, ne_of_gt hc, hlim⟩

