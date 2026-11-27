import FormalConjectures.ErdosProblems.«30»
import Mathlib.Combinatorics.Additive.Energy

-- Problem: Erdős Problem 30
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/30.lean:59 (declaration Erdos30.erdos_30)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E30

open Filter
open scoped Asymptotics

lemma h_witness (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = Erdos30.h N := by
  unfold Erdos30.h Finset.maxSidonSubsetCard
  set S := (Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)
  have hne : S.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro i₁ hi₁
    simp at hi₁
  obtain ⟨A, hA, hmax⟩ := Finset.exists_mem_eq_sup S hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, hmax.symm⟩

lemma h_le_nat (N : ℕ) : Erdos30.h N ≤ Nat.sqrt (2 * N) + 1 := by
  obtain ⟨A, hA, hS, hc⟩ := h_witness N
  rw [← hc]
  apply Erdos30.erdos_30.variants.lindstrom_weak A N hS
  intro x hx
  have := hA hx
  simp only [Finset.mem_Icc] at this
  simp only [Finset.mem_range]
  omega

lemma h_le_real (N : ℕ) : (Erdos30.h N : ℝ) ≤ 2 * (N : ℝ).sqrt + 1 := by
  have h1 := h_le_nat N
  have h2 : ((Nat.sqrt (2 * N) : ℕ) : ℝ) ≤ 2 * (N : ℝ).sqrt := by
    have hs : ((Nat.sqrt (2 * N) : ℕ) : ℝ) ≤ Real.sqrt ((2 * N : ℕ) : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    calc ((Nat.sqrt (2 * N) : ℕ) : ℝ) ≤ Real.sqrt ((2 * N : ℕ) : ℝ) := hs
      _ ≤ Real.sqrt (4 * N) := by
          apply Real.sqrt_le_sqrt; push_cast; nlinarith [(N.cast_nonneg : (0:ℝ) ≤ N)]
      _ = 2 * (N : ℝ).sqrt := by
          rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have : (Erdos30.h N : ℝ) ≤ ((Nat.sqrt (2 * N) : ℕ) : ℝ) + 1 := by exact_mod_cast h1
  linarith

/-- The trivial range `ε ≥ 1/2`. -/
lemma large_eps (ε : ℝ) (hε : 1 / 2 ≤ ε) :
    (fun N : ℕ => (Erdos30.h N : ℝ) - (N : ℝ).sqrt) =O[atTop] fun N => (N : ℝ) ^ ε := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : (N : ℝ).sqrt ≤ (N : ℝ) ^ ε := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN' hε
  have h1 : (1 : ℝ) ≤ (N : ℝ).sqrt := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN'
  have hup := h_le_real N
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ ε := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos, abs_le]
  have h0 : (0 : ℝ) ≤ Erdos30.h N := Nat.cast_nonneg _
  constructor <;> nlinarith

open scoped Finset Pointwise

/-- Each ordered pair of unequal shifts gives at most one collision. -/
lemma sidon_energy_le (A T : Finset ℕ) (hS : IsSidon (A : Set ℕ)) :
    A.addEnergy T ≤ A.card * T.card + T.card ^ 2 := by
  let P := ((A ×ˢ A) ×ˢ T ×ˢ T).filter
    (fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.1 + x.2.1 = x.1.2 + x.2.2)
  let f : (ℕ × ℕ) × ℕ × ℕ → (ℕ × ℕ) ⊕ (ℕ × ℕ) :=
    fun ((a, _), u, v) => if u = v then Sum.inl (a, u) else Sum.inr (u, v)
  have hmem : ∀ ⦃a b u v : ℕ⦄, ((a, b), u, v) ∈ P ↔
      (a ∈ A ∧ b ∈ A) ∧ (u ∈ T ∧ v ∈ T) ∧ a + u = b + v := by
    simp [P, Finset.mem_filter, Finset.mem_product, and_assoc]
  have hmap : Set.MapsTo f (↑P : Set _) (↑((A ×ˢ T).disjSum (T ×ˢ T)) : Set _) := by
    rintro ⟨⟨a, b⟩, u, v⟩ hx
    obtain ⟨⟨ha, hb⟩, ⟨hu, hv⟩, he⟩ := hmem.mp (Finset.mem_coe.mp hx)
    by_cases huv : u = v <;> simp [f, huv, ha, hu, hv]
  have hinj : Set.InjOn f (↑P : Set _) := by
    rintro ⟨⟨a, b⟩, u, v⟩ hx ⟨⟨c, d⟩, w, z⟩ hy h
    obtain ⟨⟨ha, hb⟩, _, hab⟩ := hmem.mp (Finset.mem_coe.mp hx)
    obtain ⟨⟨hc, hd⟩, _, hcd⟩ := hmem.mp (Finset.mem_coe.mp hy)
    by_cases huv : u = v <;> by_cases hwz : w = z <;>
      simp [f, huv, hwz] at h
    · obtain ⟨rfl, rfl⟩ := h
      have hbd : b = d := by omega
      simp [hbd, huv, hwz]
    · obtain ⟨rfl, rfl⟩ := h
      obtain huv' | hvu := lt_or_gt_of_ne huv
      · obtain ⟨rfl, rfl⟩ := Finset.IsSidon.eq_of_tsub hS ha hb hc hd
          (by omega) (by omega) (by omega)
        rfl
      · obtain ⟨rfl, rfl⟩ := Finset.IsSidon.eq_of_tsub hS hb ha hd hc
          (by omega) (by omega) (by omega)
        rfl
  simpa [P, Finset.addEnergy, pow_two] using Finset.card_le_card_of_injOn f hmap hinj

/-- Cauchy–Schwarz applied to the representations of a point by a mark and a shift. -/
lemma sidon_shift_bound {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hS : IsSidon (A : Set ℕ)) (t : ℕ) :
    (A.card * t) ^ 2 ≤ (N + t) * (A.card * t + t ^ 2) := by
  let T := Finset.range t
  let U := Finset.range (N + t)
  have hfilter : ((A ×ˢ T).filter (fun p => p.1 + p.2 ∈ U)) = A ×ˢ T := by
    apply Finset.filter_eq_self.mpr
    rintro ⟨a, b⟩ hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    have ha' := (Finset.mem_Icc.mp (hA ha)).2
    have hb' := Finset.mem_range.mp hb
    exact Finset.mem_range.mpr (by omega)
  have hcs := Finset.card_sq_le_card_mul_addEnergy A T U
  rw [hfilter, Finset.card_product] at hcs
  have hh := hcs.trans (Nat.mul_le_mul_left U.card (sidon_energy_le A T hS))
  simpa [U, T] using hh

/-- A quarter-power upper error, obtained by choosing shifts on the scale of `N^(3/4)`. -/
lemma h_le_sqrt_add_quarter {N : ℕ} (hN : 1 ≤ N) :
    (Erdos30.h N : ℝ) ≤ (N : ℝ).sqrt + 8 * ((N : ℝ).sqrt).sqrt := by
  obtain ⟨A, hA, hS, hcard⟩ := h_witness N
  let s := (N : ℝ).sqrt
  let r := s.sqrt
  let x := s * r
  let t := ⌈x⌉₊
  let k : ℝ := Erdos30.h N
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 1 ≤ s := by simpa [s] using Real.sqrt_le_sqrt hn
  have hr : 1 ≤ r := by simpa [r] using Real.sqrt_le_sqrt hs
  have hx : 1 ≤ x := one_le_mul_of_one_le_of_one_le hs hr
  have hs2 : s ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = s := Real.sq_sqrt (by linarith)
  have hxt : x ≤ (t : ℝ) := Nat.le_ceil x
  have ht : (0 : ℝ) < t := by linarith
  have ht_le : (t : ℝ) ≤ 2 * x := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
    change (t : ℝ) < x + 1 at hceil
    linarith
  have hk : k ≤ 3 * s := by
    have hweak := h_le_real N
    change k ≤ 2 * s + 1 at hweak
    linarith
  have hx_s : s ≤ x := by
    dsimp [x]
    calc s = s * 1 := (mul_one s).symm
      _ ≤ s * r := mul_le_mul_of_nonneg_left hr (by linarith)
  have hshift := sidon_shift_bound A hA hS t
  rw [hcard] at hshift
  have hshift' : (k * (t : ℝ)) ^ 2 ≤ ((N : ℝ) + t) * (k * t + (t : ℝ) ^ 2) := by
    have hcast : (((Erdos30.h N * t) ^ 2 : ℕ) : ℝ) ≤
        ((((N + t) * (Erdos30.h N * t + t ^ 2)) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hshift
    push_cast at hcast
    exact hcast
  have hcancel : k ^ 2 * (t : ℝ) ≤ ((N : ℝ) + t) * (k + t) := by
    apply (mul_le_mul_iff_of_pos_right ht).mp
    calc
      k ^ 2 * (t : ℝ) * t = (k * (t : ℝ)) ^ 2 := by ring
      _ ≤ ((N : ℝ) + t) * (k * t + (t : ℝ) ^ 2) := hshift'
      _ = ((N : ℝ) + t) * (k + t) * t := by ring
  have hnk : (N : ℝ) * k ≤ 3 * x * (t : ℝ) := calc
    _ ≤ (N : ℝ) * (3 * s) := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = 3 * x ^ 2 := by
      dsimp [x]
      rw [mul_pow, hr2, hs2]
      ring
    _ = 3 * x * x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hxt (by linarith)
  have htk : (t : ℝ) * k ≤ 3 * x * (t : ℝ) := by
    rw [mul_comm (t : ℝ) k]
    exact mul_le_mul_of_nonneg_right (by linarith) ht.le
  have htt : (t : ℝ) * t ≤ 2 * x * (t : ℝ) :=
    mul_le_mul_of_nonneg_right ht_le ht.le
  have hk2 : k ^ 2 ≤ (N : ℝ) + 8 * x := by
    apply (mul_le_mul_iff_of_pos_right ht).mp
    linarith only [hcancel, hnk, htk, htt]
  by_contra! hbad
  change s + 8 * r < k at hbad
  have hmul : 8 * x < (k - s) * s := calc
    _ = (8 * r) * s := by
      dsimp [x]
      ring
    _ < _ := mul_lt_mul_of_pos_right (by linarith) (by linarith)
  have hdiff : (k - s) * s ≤ k ^ 2 - (N : ℝ) := by
    have hnonneg : 0 ≤ (k - s) * k := mul_nonneg (by linarith) (by linarith)
    rw [← hs2]
    calc
      _ ≤ (k - s) * s + (k - s) * k := le_add_of_nonneg_right hnonneg
      _ = _ := by ring
  linarith only [hmul.trans_le hdiff, hk2]

lemma upper_error_bound (ε : ℝ) (hε : 1 / 4 ≤ ε) :
    ∀ᶠ N : ℕ in atTop, (Erdos30.h N : ℝ) - (N : ℝ).sqrt ≤ 8 * (N : ℝ) ^ ε := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hroot : ((N : ℝ).sqrt).sqrt = (N : ℝ) ^ (1 / 4 : ℝ) := by
    simp only [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (by positivity)]
    norm_num
  have hquarter := h_le_sqrt_add_quarter hN
  rw [hroot] at hquarter
  have hpow := Real.rpow_le_rpow_of_exponent_le hn hε
  linarith

/-- The lower error below one half and the upper error below one quarter. -/
lemma unresolved_bounds (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    (∃ C : ℝ, ∀ᶠ N : ℕ in atTop, (N : ℝ).sqrt - (Erdos30.h N : ℝ) ≤ C * (N : ℝ) ^ ε) ∧
    (ε < 1 / 4 →
      ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, (Erdos30.h N : ℝ) - (N : ℝ).sqrt ≤ C * (N : ℝ) ^ ε) := by
  sorry

lemma small_eps (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    (fun N : ℕ => (Erdos30.h N : ℝ) - (N : ℝ).sqrt) =O[atTop] fun N => (N : ℝ) ^ ε := by
  obtain ⟨⟨L, hL⟩, hu⟩ := unresolved_bounds ε hε0 hε
  have hupper : ∃ U : ℝ, ∀ᶠ N : ℕ in atTop,
      (Erdos30.h N : ℝ) - (N : ℝ).sqrt ≤ U * (N : ℝ) ^ ε := by
    rcases le_or_gt (1 / 4) ε with h | h
    · exact ⟨8, upper_error_bound ε h⟩
    · exact hu h
  obtain ⟨U, hU⟩ := hupper
  refine Asymptotics.IsBigO.of_bound (max L U) ?_
  filter_upwards [hL, hU] with N hlow hupp
  have hp : 0 ≤ (N : ℝ) ^ ε := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp, abs_le]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right (le_max_left L U) hp
    linarith
  · exact hupp.trans (mul_le_mul_of_nonneg_right (le_max_right L U) hp)

end OMA.E30

theorem OMA.solution : type_of% @Erdos30.erdos_30 := by
  intro ε hε
  rcases le_or_gt (1 / 2) ε with h | h
  · exact OMA.E30.large_eps ε h
  · exact OMA.E30.small_eps ε hε h
