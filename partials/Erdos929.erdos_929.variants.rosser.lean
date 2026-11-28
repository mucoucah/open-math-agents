import FormalConjectures.ErdosProblems.«929»

-- Problem: Erdős Problem 929 — rosser
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/929.lean:100 (declaration Erdos929.erdos_929.variants.rosser)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E929

open Filter Erdos929

/-- Shifting by `x!` does not change the covering property. -/
lemma cover_shift (x k n : ℕ) :
    AllHaveSmallPrimeFactor x k (n + x.factorial) ↔ AllHaveSmallPrimeFactor x k n := by
  have key (p i : ℕ) (pr : p.Prime) (px : p ≤ x) : p ∣ n + x.factorial + i ↔ p ∣ n + i := by
    rw [Nat.add_right_comm]
    exact (Nat.dvd_add_iff_left (Nat.dvd_factorial pr.pos px)).symm
  constructor <;> intro h i hi <;> obtain ⟨p, pr, px, d⟩ := h i hi
  · exact ⟨p, pr, px, (key p i pr px).mp d⟩
  · exact ⟨p, pr, px, (key p i pr px).mpr d⟩

/-- A set of positive density is nonempty. -/
lemma nonempty_of_pos (T : Set ℕ) (h : T.HasPosDensity) : T.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  obtain ⟨α, hα, hd⟩ := h
  have h0 : ∀ b : ℕ, (∅ : Set ℕ).partialDensity Set.univ b = 0 := by
    intro b; simp [Set.partialDensity]
  have : Tendsto (fun b : ℕ => (∅ : Set ℕ).partialDensity Set.univ b) atTop (nhds 0) := by
    simp only [h0]; exact tendsto_const_nhds
  exact hα.ne' (tendsto_nhds_unique hd this)

section Periodic
open Classical

lemma pd_count (T : Set ℕ) (b : ℕ) :
    T.partialDensity Set.univ b = (Nat.count (· ∈ T) b : ℝ) / b := by
  classical
  have h1 : (T ∩ Set.univ) ∩ Set.Iio b = (((Finset.range b).filter (· ∈ T) : Finset ℕ) : Set ℕ) := by
    ext x; simp [and_comm]
  have h2 : (Set.univ ∩ Set.Iio b : Set ℕ) = ((Finset.range b : Finset ℕ) : Set ℕ) := by
    ext x; simp
  simp only [Set.partialDensity]
  rw [h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_range,
    Nat.count_eq_card_filter_range]

lemma count_mul_per (T : Set ℕ) (m : ℕ) (hper : ∀ n, n + m ∈ T ↔ n ∈ T) (q : ℕ) :
    Nat.count (· ∈ T) (q * m) = q * Nat.count (· ∈ T) m := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [add_mul, one_mul, Nat.count_add, ih, add_mul, one_mul]
    congr 1
    have hq : ∀ j n, n + j * m ∈ T ↔ n ∈ T := by
      intro j; induction j with
      | zero => intro n; simp
      | succ j ihj => intro n; rw [show n + (j+1)*m = (n + j*m) + m by ring, hper, ihj]
    congr 1; funext k
    simp only [eq_iff_iff]
    rw [show q * m + k = k + q * m by ring, hq]

lemma periodic_pos (T : Set ℕ) (m : ℕ) (hm : 0 < m) (hper : ∀ n, n + m ∈ T ↔ n ∈ T)
    (hne : T.Nonempty) : T.HasPosDensity := by
  set c := Nat.count (· ∈ T) m with hc
  have hq : ∀ j n, n + j * m ∈ T ↔ n ∈ T := by
    intro j; induction j with
    | zero => intro n; simp
    | succ j ihj => intro n; rw [show n + (j+1)*m = (n + j*m) + m by ring, hper, ihj]
  have cpos : 0 < c := by
    obtain ⟨t, ht⟩ := hne
    apply Nat.pos_of_ne_zero; apply Nat.count_ne_iff_exists.mpr ⟨t % m, Nat.mod_lt _ hm, ?_⟩
    have := (hq (t / m) (t % m)).mp (by rw [show t % m + t / m * m = t by
      rw [mul_comm]; exact Nat.mod_add_div t m]; exact ht)
    exact this
  refine ⟨(c : ℝ) / m, by positivity, ?_⟩
  have mR : (0 : ℝ) < m := by exact_mod_cast hm
  -- bounds
  have lo : ∀ b : ℕ, ((b : ℝ) / m - 1) * c ≤ Nat.count (· ∈ T) b := by
    intro b
    have h1 : (b / m) * m ≤ b := Nat.div_mul_le_self b m
    have h2 := Nat.count_monotone (· ∈ T) h1
    rw [count_mul_per T m hper] at h2
    have h3 : ((b : ℝ) / m - 1) ≤ ((b / m : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := b) hm
      have h4 : (b : ℝ) < ((b / m : ℕ) : ℝ) * m + m := by exact_mod_cast this
      rw [div_sub_one mR.ne', div_le_iff₀ mR]; linarith
    calc ((b : ℝ) / m - 1) * c ≤ ((b / m : ℕ) : ℝ) * c :=
          mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
      _ ≤ _ := by exact_mod_cast h2
  have hi : ∀ b : ℕ, (Nat.count (· ∈ T) b : ℝ) ≤ ((b : ℝ) / m + 1) * c := by
    intro b
    have h1 : b ≤ (b / m + 1) * m := by
      have := Nat.lt_div_mul_add (a := b) hm; rw [add_mul, one_mul]; omega
    have h2 := Nat.count_monotone (· ∈ T) h1
    rw [count_mul_per T m hper] at h2
    have h3 : ((b / m : ℕ) : ℝ) ≤ (b : ℝ) / m := by
      rw [le_div_iff₀ mR]; exact_mod_cast Nat.div_mul_le_self b m
    calc (Nat.count (· ∈ T) b : ℝ) ≤ (((b / m + 1 : ℕ)) : ℝ) * c := by exact_mod_cast h2
      _ ≤ _ := by push_cast; exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have key : ∀ᶠ b : ℕ in atTop, |T.partialDensity Set.univ b - c / m| ≤ c / b := by
    filter_upwards [eventually_ge_atTop 1] with b hb
    have bR : (0 : ℝ) < b := by exact_mod_cast hb
    rw [pd_count, abs_le]
    have l := lo b; have u := hi b
    have e1 : ((b : ℝ) / m - 1) * c / b = c / m - c / b := by field_simp
    have e2 : ((b : ℝ) / m + 1) * c / b = c / m + c / b := by field_simp
    have l2 := div_le_div_of_nonneg_right l bR.le
    have u2 := div_le_div_of_nonneg_right u bR.le
    rw [e1] at l2; rw [e2] at u2
    constructor <;> linarith
  have lim : Tendsto (fun b : ℕ => (c : ℝ) / b) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  unfold Set.HasDensity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun b => norm_nonneg _) ?_ lim
  filter_upwards [key] with b hb
  simpa [Real.norm_eq_abs] using hb

end Periodic

/-- At the least admissible bound a covered block exists. -/
lemma witness (k : ℕ) : ∃ n, AllHaveSmallPrimeFactor (S k) k n := by
  have per (x : ℕ) := periodic_pos {n | AllHaveSmallPrimeFactor x k n} x.factorial
    (Nat.factorial_pos _) (cover_shift x k)
  have first : AllHaveSmallPrimeFactor (k + 1) k 1 := by
    intro i hi
    obtain ⟨lo, up⟩ := Finset.mem_Icc.mp hi
    obtain ⟨p, pr, dv⟩ := Nat.exists_prime_and_dvd (show 1 + i ≠ 1 by omega)
    exact ⟨p, pr, by have := Nat.le_of_dvd (show 0 < 1 + i by omega) dv; omega, dv⟩
  have ne : {x : ℕ | {n : ℕ | AllHaveSmallPrimeFactor x k n}.HasPosDensity}.Nonempty :=
    ⟨k + 1, per _ ⟨1, first⟩⟩
  exact nonempty_of_pos _ (Nat.sInf_mem ne)

/-- Lower-bound linear sieve weights (Rosser, Iwaniec, sifting limit 2): the only missing
input. Weights of total mass at most `C x^(2+δ)`, main term at least `1 / (C x^δ)`, and
nonpositive divisor sums at every integer having a prime factor at most `x`. -/
lemma sieve_weights : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 0 < x →
    ∃ (D : Finset ℕ) (lam : ℕ → ℝ),
      (∀ d ∈ D, 0 < d) ∧
      (∑ d ∈ D, |lam d| ≤ C * (x : ℝ) ^ (2 + δ)) ∧
      (1 ≤ C * (x : ℝ) ^ δ * ∑ d ∈ D, lam d / d) ∧
      (∀ m : ℕ, 0 < m → (∃ p, p.Prime ∧ p ≤ x ∧ p ∣ m) →
        ∑ d ∈ D.filter (fun d => d ∣ m), lam d ≤ 0) := by
  sorry

/-- Number of multiples of `d` in a block, as a real sum of indicators. -/
lemma cnt_eq (d n k : ℕ) :
    (∑ i ∈ Finset.Icc 1 k, (if d ∣ n + i then (1 : ℝ) else 0)) =
      (((n + k) / d : ℕ) : ℝ) - ((n / d : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have e : (n + (k + 1)) / d = (n + k) / d + if d ∣ n + (k + 1) then 1 else 0 := by
      rw [← add_assoc]; exact Nat.succ_div
    rw [e]
    by_cases h : d ∣ n + (k + 1)
    · simp only [h, if_true]; push_cast; ring
    · simp only [h, if_false]; push_cast; ring

/-- The count of multiples of `d` in a block of length `k` is within one of `k / d`. -/
lemma cnt_close (d n k : ℕ) (hd : 0 < d) :
    |(∑ i ∈ Finset.Icc 1 k, (if d ∣ n + i then (1 : ℝ) else 0)) - (k : ℝ) / d| ≤ 1 := by
  rw [cnt_eq]
  have dR : (0 : ℝ) < d := by exact_mod_cast hd
  have fl (a : ℕ) : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d ∧ (a : ℝ) / d < ((a / d : ℕ) : ℝ) + 1 := by
    constructor
    · rw [le_div_iff₀ dR]; exact_mod_cast Nat.div_mul_le_self a d
    · have := Nat.lt_div_mul_add (a := a) hd
      have h4 : (a : ℝ) < ((a / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
      rw [div_lt_iff₀ dR, add_mul, one_mul]; exact h4
  obtain ⟨a1, a2⟩ := fl (n + k)
  obtain ⟨b1, b2⟩ := fl n
  have e : ((n + k : ℕ) : ℝ) / d = (n : ℝ) / d + (k : ℝ) / d := by push_cast; ring
  rw [e] at a1 a2
  rw [abs_le]; constructor <;> linarith

/-- Iwaniec (Rosser linear sieve): the Jacobsthal function of the primorial of `x`
is at most `x ^ (2 + δ)` up to a constant. Deduced from `sieve_weights` by double counting. -/
lemma jacobsthal_core : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ x k n : ℕ,
    AllHaveSmallPrimeFactor x k n → (k : ℝ) ≤ C * (x : ℝ) ^ (2 + δ) := by
  intro δ hδ
  obtain ⟨C, hC, hw⟩ := sieve_weights (δ / 2) (by linarith)
  refine ⟨C * C, by positivity, ?_⟩
  intro x k n hcov
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [Nat.cast_zero]; positivity
    · obtain ⟨p, pr, px, -⟩ := hcov 1 (Finset.mem_Icc.mpr ⟨le_refl _, hk⟩)
      exact absurd pr.pos (by omega)
  · obtain ⟨D, lam, hDpos, habs, hmain, hsieve⟩ := hw x hx
    have xR : (0 : ℝ) < x := by exact_mod_cast hx
    have h1 : ∑ i ∈ Finset.Icc 1 k, ∑ d ∈ D.filter (fun d => d ∣ n + i), lam d ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      obtain ⟨p, pr, px, dv⟩ := hcov i hi
      exact hsieve (n + i) (by have := (Finset.mem_Icc.mp hi).1; omega) ⟨p, pr, px, dv⟩
    have h2 : ∑ i ∈ Finset.Icc 1 k, ∑ d ∈ D.filter (fun d => d ∣ n + i), lam d
        = ∑ d ∈ D, lam d * ∑ i ∈ Finset.Icc 1 k, (if d ∣ n + i then (1 : ℝ) else 0) := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    have h3 : (k : ℝ) * (∑ d ∈ D, lam d / d) - ∑ d ∈ D, |lam d|
        ≤ ∑ d ∈ D, lam d * ∑ i ∈ Finset.Icc 1 k, (if d ∣ n + i then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro d hd
      have hc := cnt_close d n k (hDpos d hd)
      set c := ∑ i ∈ Finset.Icc 1 k, (if d ∣ n + i then (1 : ℝ) else 0)
      have h5 : -(|lam d| * 1) ≤ lam d * (c - (k : ℝ) / d) := by
        have := neg_abs_le (lam d * (c - (k : ℝ) / d))
        rw [abs_mul] at this
        have h6 : |lam d| * |c - (k : ℝ) / d| ≤ |lam d| * 1 :=
          mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        linarith
      have h7 : lam d * (c - (k : ℝ) / d) = lam d * c - (k : ℝ) * (lam d / d) := by ring
      linarith
    rw [h2] at h1
    have h4 : (k : ℝ) * (∑ d ∈ D, lam d / d) ≤ ∑ d ∈ D, |lam d| := by linarith
    have kR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have e1 : (x : ℝ) ^ (δ / 2) * (x : ℝ) ^ (2 + δ / 2) = (x : ℝ) ^ (2 + δ) := by
      rw [← Real.rpow_add xR]; congr 1; ring
    have p1 : 0 ≤ C * (x : ℝ) ^ (δ / 2) := by positivity
    calc (k : ℝ) ≤ (k : ℝ) * (C * (x : ℝ) ^ (δ / 2) * ∑ d ∈ D, lam d / d) :=
          le_mul_of_one_le_right kR hmain
      _ = (C * (x : ℝ) ^ (δ / 2)) * ((k : ℝ) * ∑ d ∈ D, lam d / d) := by ring
      _ ≤ (C * (x : ℝ) ^ (δ / 2)) * (C * (x : ℝ) ^ (2 + δ / 2)) :=
          mul_le_mul_of_nonneg_left (h4.trans habs) p1
      _ = C * C * ((x : ℝ) ^ (δ / 2) * (x : ℝ) ^ (2 + δ / 2)) := by ring
      _ = C * C * (x : ℝ) ^ (2 + δ) := by rw [e1]

/-- The algebra: `k ≤ C x^(2+ε)` forces `x ≥ k^(1/2-ε)` for large `k`. -/
lemma algebra (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∀ᶠ k : ℕ in atTop, ∀ x : ℝ, 0 ≤ x → (k : ℝ) ≤ C * x ^ (2 + ε) →
      (k : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ x := by
  have far : ∀ᶠ k : ℕ in atTop, C < (k : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  filter_upwards [far, eventually_ge_atTop 1] with k hk h1 x hx hkx
  by_contra hlt
  push_neg at hlt
  have k1 : (1 : ℝ) ≤ k := by exact_mod_cast h1
  have kp : (0 : ℝ) < k := by linarith
  have step1 : x ^ (2 + ε) < ((k : ℝ) ^ ((1 : ℝ) / 2 - ε)) ^ (2 + ε) :=
    Real.rpow_lt_rpow hx hlt (by linarith)
  rw [← Real.rpow_mul kp.le] at step1
  have step2 : (k : ℝ) ^ (((1 : ℝ) / 2 - ε) * (2 + ε)) ≤ (k : ℝ) ^ (1 - ε) :=
    Real.rpow_le_rpow_of_exponent_le k1 (by nlinarith)
  have split : (k : ℝ) = (k : ℝ) ^ ε * (k : ℝ) ^ (1 - ε) := by
    rw [← Real.rpow_add kp]; norm_num
  have pos1 : 0 < (k : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos kp _
  have : (k : ℝ) < C * (k : ℝ) ^ (1 - ε) := by
    calc (k : ℝ) ≤ C * x ^ (2 + ε) := hkx
      _ < C * (k : ℝ) ^ (1 - ε) := by
        apply mul_lt_mul_of_pos_left _ hC; linarith
  rw [split] at this
  nlinarith

end OMA.E929

theorem OMA.solution : type_of% @Erdos929.erdos_929.variants.rosser := by
  intro ε hε
  obtain ⟨C, hC, core⟩ := OMA.E929.jacobsthal_core ε hε
  filter_upwards [OMA.E929.algebra ε C hε hC] with k hk
  obtain ⟨n, hn⟩ := OMA.E929.witness k
  exact hk _ (Nat.cast_nonneg _) (core _ k n hn)
