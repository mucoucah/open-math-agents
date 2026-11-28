import FormalConjectures.ErdosProblems.«5»

-- Problem: Erdős Problem 5 — hildebrand maier
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/5.lean:125 (declaration Erdos5.erdos_5.variants.hildebrand_maier)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.HM

open Filter Real Finset Erdos5

/-- Core (Maier matrix method, positive density of large gaps): for every A > 0,
a positive proportion of indices n < N have primeGap n > A log n. -/
theorem core : ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    c * N ≤ (((range N).filter fun n : ℕ => A * log (n : ℝ) < (primeGap n : ℝ)).card : ℝ) := by
  sorry

lemma sum_gaps (N : ℕ) : ∑ n ∈ range N, (primeGap n : ℝ) ≤ Nat.nth Nat.Prime N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, primeGap, Nat.cast_sub
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self n)).le]
    linarith

lemma log_small : ∀ᶠ n : ℕ in atTop, log n ≤ (n : ℝ) / 5 := by
  have := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 5 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually this] with n hn
  simp only [id_eq, Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at hn
  linarith [le_abs_self (log (n : ℝ))]

lemma nth_le : ∀ᶠ n : ℕ in atTop, (Nat.nth Nat.Prime n : ℝ) ≤ 5 * n * log n := by
  filter_upwards [log_small, eventually_ge_atTop 8] with n hl hn8
  have hn : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hL : 2 ≤ log (n : ℝ) := by
    have h8 : log (8 : ℝ) ≤ log n := Real.log_le_log (by norm_num) hn
    have : log (8 : ℝ) = 3 * log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  set L := log (n : ℝ) with hLdef
  set x := 5 * (n : ℝ) * L with hx
  have hx1 : 80 ≤ x := by rw [hx]; nlinarith
  have hxn : x ≤ (n : ℝ) ^ 2 := by rw [hx, sq]; nlinarith
  have hlogx : log x ≤ 2 * L := by
    have := Real.log_le_log (by linarith) hxn
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hlogx2 : log (x + 2) ≤ log 2 + 2 * L := by
    have e : log (2 * (n : ℝ) ^ 2) = log 2 + 2 * L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hLdef]; norm_num
    rw [← e]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hlxpos : 0 < log x := Real.log_pos (by linarith)
  have hpi := Chebyshev.pi_ge' (show (1 : ℝ) < x by linarith)
  have hcount : (n : ℝ) + 1 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    refine le_trans ?_ hpi
    rw [le_div_iff₀ hlxpos]
    have h2 := Real.log_two_gt_d9
    have h2' := Real.log_two_lt_d9
    have e1 : ((n : ℝ) + 1) * log x ≤ ((n : ℝ) + 1) * (2 * L) :=
      mul_le_mul_of_nonneg_left hlogx (by positivity)
    have e2 : (x - 1) * 0.6931471 ≤ (x - 1) * log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hlt : n < Nat.count Nat.Prime (⌊x⌋₊ + 1) := by
    have : n + 1 ≤ Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hcount
    unfold Nat.primeCounting Nat.primeCounting' at this
    omega
  have := Nat.nth_lt_of_lt_count hlt
  have h3 : Nat.nth Nat.Prime n ≤ ⌊x⌋₊ := by omega
  calc (Nat.nth Nat.Prime n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h3
    _ ≤ x := Nat.floor_le (by linarith)

/-- Bounded windows above A recur at the index scale. -/
lemma windows (A : ℝ) (hA : 0 < A) : ∃ B : ℝ,
    ∃ᶠ n : ℕ in atTop, normalizedGap n ∈ Set.Icc A B := by
  obtain ⟨c, hc, hden⟩ := core A hA
  refine ⟨40 / c, frequently_atTop.mpr ?_⟩
  intro M
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hden.and nth_le)
  obtain ⟨T, hT⟩ := exists_nat_ge (2 / c)
  let t := max M (max T (max N₀ 8))
  have htM : M ≤ t := le_max_left ..
  have htT : T ≤ t := (le_max_left ..).trans (le_max_right ..)
  have htN : N₀ ≤ t := (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have ht8 : 8 ≤ t := (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
  have tpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have tc : 2 ≤ c * t := by
    have hh := (div_le_iff₀ hc).mp (hT.trans (Nat.cast_le.mpr htT))
    linarith
  have ltlog : 0 < log (t : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  obtain ⟨hn, hn'⟩ := hN₀ (t ^ 2) (htN.trans (by nlinarith))
  let P := (range (t ^ 2)).filter fun n : ℕ => A * log (n : ℝ) < (primeGap n : ℝ)
  let S := P \ range t
  have hcard : c * (t : ℝ) ^ 2 / 2 ≤ S.card := by
    change c * ((t ^ 2 : ℕ) : ℝ) ≤ (P.card : ℝ) at hn
    push_cast at hn
    have hh := le_card_sdiff (range t) P
    rw [card_range] at hh
    have hh' : P.card ≤ S.card + t := by dsimp [S]; omega
    have r : (P.card : ℝ) ≤ S.card + (t : ℝ) := by exact_mod_cast hh'
    nlinarith [mul_le_mul_of_nonneg_right tc tpos.le]
  by_contra! bad
  have large (n : ℕ) (hn : n ∈ S) : 40 / c * log t ≤ (primeGap n : ℝ) := by
    obtain ⟨hp, ht⟩ := mem_sdiff.mp hn
    have hit := (mem_filter.mp hp).2
    have htn : t ≤ n := by simpa using ht
    have hlogn : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hge : A ≤ normalizedGap n := by
      unfold normalizedGap
      rw [le_div_iff₀ hlogn]; linarith
    have hnot := bad n (htM.trans htn)
    have hgt : 40 / c < normalizedGap n := by
      by_contra hh
      exact hnot ⟨hge, not_lt.mp hh⟩
    unfold normalizedGap at hgt
    rw [lt_div_iff₀ hlogn] at hgt
    have : log (t : ℝ) ≤ log n := Real.log_le_log tpos (by exact_mod_cast htn)
    nlinarith [div_pos (show (0 : ℝ) < 40 by norm_num) hc]
  have total : (S.card : ℝ) * (40 / c * log t) ≤ (Nat.nth Nat.Prime (t ^ 2) : ℝ) := calc
    _ = ∑ _n ∈ S, 40 / c * log t := by simp
    _ ≤ ∑ n ∈ S, (primeGap n : ℝ) := sum_le_sum large
    _ ≤ ∑ n ∈ range (t ^ 2), (primeGap n : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg (sdiff_subset.trans (filter_subset _ _))
      exact fun n _ _ => Nat.cast_nonneg _
    _ ≤ _ := sum_gaps _
  have hp : (Nat.nth Nat.Prime (t ^ 2) : ℝ) ≤ 10 * (t : ℝ) ^ 2 * log t := by
    have e : log (((t ^ 2 : ℕ)) : ℝ) = 2 * log t := by
      push_cast; rw [Real.log_pow]; norm_num
    rw [e] at hn'; push_cast at hn'; linarith
  have high : c * (t : ℝ) ^ 2 / 2 * (40 / c * log t) ≤ 10 * (t : ℝ) ^ 2 * log t :=
    (mul_le_mul_of_nonneg_right hcard
      (mul_nonneg (div_pos (by norm_num) hc).le ltlog.le)).trans (total.trans hp)
  have eq : c * (t : ℝ) ^ 2 / 2 * (40 / c * log t) = 20 * ((t : ℝ) ^ 2 * log t) := by
    field_simp; ring
  rw [eq] at high
  nlinarith [mul_pos (sq_pos_of_pos tpos) ltlog]

end OMA.HM

open Filter Real Erdos5 in
theorem OMA.solution : type_of% @Erdos5.erdos_5.variants.hildebrand_maier := by
  intro C
  set A := max C 0 + 1 with hAdef
  have hA : 0 < A := by rw [hAdef]; linarith [le_max_right C 0]
  obtain ⟨B, visits⟩ := OMA.HM.windows A hA
  obtain ⟨x, hx, cluster⟩ := isCompact_Icc.exists_mapClusterPt_of_frequently visits
  refine ⟨x, cluster, lt_of_lt_of_le ?_ hx.1⟩
  rw [hAdef]; linarith [le_max_left C 0]
