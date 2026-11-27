import FormalConjectures.ErdosProblems.«1191»

/-! A finite dyadic obstruction for the squared critical density of Sidon sets. -/

-- Problem: Erdős Problem 1191 — i
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1191.lean:44 (declaration Erdos1191.erdos_1191.parts.i)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E1191i

open Filter
open Set
open scoped Topology

/-- A liminf of `ofReal` values vanishes as soon as the values are frequently below
every positive threshold. -/
theorem liminf_ofReal_zero_of_frequently {u : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ x in atTop, u x ≤ ε) :
    liminf (fun x ↦ ENNReal.ofReal (u x)) atTop = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  apply Filter.liminf_le_of_frequently_le'
  refine (h ε (by exact_mod_cast hε)).mono fun x hx => ?_
  exact ENNReal.ofReal_le_of_le_toReal (by simpa using hx)

/-- Pointwise bridge: the normalised count is at most `ε` as soon as the rpow-free
inequality `count ^ 2 * log x ≤ ε ^ 2 * x` holds. -/
theorem normalised_le_of_sq_le {n x : ℕ} {ε : ℝ} (hε : 0 < ε) (hx : 1 ≤ x)
    (h : (n : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x) :
    (n : ℝ) / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ) ≤ ε := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, div_mul_eq_mul_div,
    div_le_iff₀ (Real.sqrt_pos.2 hx0)]
  have h1 : (n : ℝ) * Real.sqrt (Real.log x) = Real.sqrt ((n : ℝ) ^ 2 * Real.log x) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg n)]
  have h2 : ε * Real.sqrt x = Real.sqrt (ε ^ 2 * x) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
  rw [h1, h2]
  exact Real.sqrt_le_sqrt h

private theorem prefix_filter_card (S : Finset ℕ) (hS : ∀ a ∈ S, 1 ≤ a) (x : ℕ) :
    (S.filter (· ≤ x)).card = ((S : Set ℕ) ∩ Icc 1 x).ncard := by
  have h : (↑(S.filter (· ≤ x)) : Set ℕ) = (S : Set ℕ) ∩ Icc 1 x := by
    ext a
    simp only [Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_Icc]
    exact ⟨fun ha => ⟨ha.1, hS a ha.1, ha.2⟩, fun ha => ⟨ha.1, ha.2.2⟩⟩
  rw [← h, ncard_coe_finset]

/-- All Sidon subsets of the horizon have a small count at some dyadic scale. -/
def DyadicHorizon (d J K : ℕ) : Prop :=
  ∀ S : Finset ℕ,
    (S : Set ℕ) ⊆ Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
      ∃ j ∈ Finset.Icc J K, d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 2 ^ j

/-- An exhaustive search through finite subsets decides a fixed horizon. -/
def decidableDyadicHorizon (d J K : ℕ) : Decidable (DyadicHorizon d J K) := by
  letI (S : Finset ℕ) : Decidable (IsSidon (S : Set ℕ)) := by
    change Decidable (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ e ∈ S,
      a + c = b + e → (a = b ∧ c = e) ∨ (a = e ∧ c = b))
    infer_instance
  have h : DyadicHorizon d J K ↔ ∀ S ⊆ Finset.Icc 1 (2 ^ K), IsSidon (S : Set ℕ) →
      ∃ j ∈ Finset.Icc J K, d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 2 ^ j := by
    simp only [DyadicHorizon, Set.subset_def, Finset.subset_iff, Finset.mem_coe,
      Set.mem_Icc, Finset.mem_Icc]
  exact decidable_of_iff _ h.symm

/-- A uniform finite horizon for each density threshold and starting scale. -/
def DyadicFiniteObstruction : Prop :=
  ∀ d J : ℕ, 0 < d → ∃ K ≥ J, DyadicHorizon d J K

/-- The finite dyadic obstruction suffices for the squared critical density bound. -/
theorem core_sq_from_finite_obstruction (h : DyadicFiniteObstruction)
    (A : Set ℕ) (hS : IsSidon A) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ x : ℕ, N ≤ x ∧ 1 ≤ x ∧
      ((A ∩ Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hεsq : 0 < ε ^ 2 := by positivity
  obtain ⟨d, hd⟩ := exists_nat_ge (Real.log 2 / ε ^ 2)
  have hdpos : 0 < d := by
    exact_mod_cast (div_pos hlog hεsq).trans_le hd
  have hdlog : Real.log 2 ≤ (d : ℝ) * ε ^ 2 := (div_le_iff₀ hεsq).mp hd
  obtain ⟨K, _, hK⟩ := h d N hdpos
  have hfin : (A ∩ Icc 1 (2 ^ K)).Finite :=
    (finite_Icc _ _).subset inter_subset_right
  let S := hfin.toFinset
  have hcoe : (S : Set ℕ) = A ∩ Icc 1 (2 ^ K) := hfin.coe_toFinset
  have hsub : (S : Set ℕ) ⊆ Icc 1 (2 ^ K) := hcoe ▸ inter_subset_right
  have hsid : IsSidon (S : Set ℕ) := by
    rw [hcoe]
    intro a ha b hb c hc e he heq
    exact hS a ha.1 b hb.1 c hc.1 e he.1 heq
  obtain ⟨j, hj, hjcount⟩ := hK S hsub hsid
  obtain ⟨hNj, hjK⟩ := Finset.mem_Icc.mp hj
  have hpow : (2 : ℕ) ^ j ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hjK
  rw [prefix_filter_card S (fun a ha => (hsub ha).1), hcoe, inter_assoc,
    inter_eq_right.mpr (Icc_subset_Icc_right hpow)] at hjcount
  let m : ℝ := (A ∩ Icc 1 (2 ^ j)).ncard
  have hcount : (d : ℝ) * m ^ 2 * (j : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    dsimp [m]
    exact_mod_cast hjcount
  refine ⟨2 ^ j, hNj.trans Nat.lt_two_pow_self.le, Nat.succ_le_of_lt (by positivity), ?_⟩
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  change m ^ 2 * ((j : ℝ) * Real.log 2) ≤ ε ^ 2 * (2 : ℝ) ^ j
  calc
    _ ≤ m ^ 2 * ((j : ℝ) * ((d : ℝ) * ε ^ 2)) := by gcongr
    _ = ε ^ 2 * ((d : ℝ) * m ^ 2 * (j : ℝ)) := by ring
    _ ≤ ε ^ 2 * (2 : ℝ) ^ j := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hεsq.le

/-- A sequence of sets has a limit along a subsequence whose finite prefixes agree. -/
private theorem matching_prefixes (W : ℕ → Set ℕ) :
    ∃ A : Set ℕ, A ⊆ Ioi 0 ∧
      ∀ b k : ℕ, ∃ n ≥ k, W n ∩ Icc 1 b = A ∩ Icc 1 b := by
  classical
  let w (n a : ℕ) : Bool := decide (a ∈ W n)
  obtain ⟨f, φ, hφ, hf⟩ := CompactSpace.tendsto_subseq w
  let A : Set ℕ := {a | f a = true ∧ 1 ≤ a}
  refine ⟨A, fun a ha => (show 1 ≤ a from ha.2), fun b k => ?_⟩
  have hcoord (a : ℕ) : ∀ᶠ i in atTop, w (φ i) a = f a := by
    have ht : Tendsto (fun i => w (φ i) a) atTop (𝓝 (f a)) :=
      (continuous_apply a).continuousAt.tendsto.comp hf
    rwa [nhds_discrete Bool, tendsto_pure] at ht
  have hagree : ∀ᶠ i in atTop, ∀ a ∈ Finset.Icc 1 b, w (φ i) a = f a :=
    (eventually_all_finset _).2 fun a _ => hcoord a
  obtain ⟨i, hi, heq⟩ := ((hφ.tendsto_atTop.eventually_ge_atTop k).and hagree).exists
  refine ⟨φ i, hi, ?_⟩
  ext a
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨ha, hb⟩
    have haeq := heq a (Finset.mem_Icc.mpr hb)
    have ht : w (φ i) a = true := by simp [w, ha]
    exact ⟨⟨haeq.symm.trans ht, hb.1⟩, hb⟩
  · rintro ⟨ha, hb⟩
    have haeq := heq a (Finset.mem_Icc.mpr hb)
    have ht := haeq.trans (show f a = true from ha.1)
    exact ⟨by simpa [w] using ht, hb⟩

private theorem infinite_of_strict_dyadic_counts {A : Set ℕ} {d J : ℕ}
    (h : ∀ j ≥ J, 2 ^ j < d * (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * j) :
    A.Infinite := by
  intro hfin
  let c := d * A.ncard ^ 2
  let k := max J (2 * c)
  have hj : J ≤ 2 * k := by
    have hJ : J ≤ k := le_max_left _ _
    omega
  have hcard : (A ∩ Icc 1 (2 ^ (2 * k))).ncard ≤ A.ncard :=
    ncard_le_ncard inter_subset_left hfin
  have hupper : d * (A ∩ Icc 1 (2 ^ (2 * k))).ncard ^ 2 * (2 * k) ≤ c * (2 * k) := by
    dsimp [c]
    gcongr
  refine (h (2 * k) hj).not_ge (hupper.trans ?_)
  calc
    c * (2 * k) = (2 * c) * k := by ring
    _ ≤ k * k := Nat.mul_le_mul_right _ (le_max_right _ _)
    _ ≤ (2 ^ k) * (2 ^ k) :=
      Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le
    _ = 2 ^ (2 * k) := by rw [mul_comm 2 k, pow_mul, pow_two]

private theorem infinite_witness_of_finite_witnesses {d J : ℕ}
    (h : ∀ K ≥ J, ∃ S : Finset ℕ,
      (S : Set ℕ) ⊆ Icc 1 (2 ^ K) ∧ IsSidon (S : Set ℕ) ∧
        ∀ j ∈ Finset.Icc J K, 2 ^ j < d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j) :
    ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧
      ∀ j ≥ J, 2 ^ j < d * (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * j := by
  choose W hbound hsid hcount using fun n : ℕ => h (max J n) (le_max_left _ _)
  obtain ⟨A, hpos, hprefix⟩ := matching_prefixes (fun n => (W n : Set ℕ))
  have hlower (j : ℕ) (hj : J ≤ j) :
      2 ^ j < d * (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * j := by
    obtain ⟨n, hn, heq⟩ := hprefix (2 ^ j) j
    have hc := hcount n j (Finset.mem_Icc.mpr ⟨hj, hn.trans (le_max_right _ _)⟩)
    rwa [prefix_filter_card (W n) (fun a ha => (hbound n ha).1), heq] at hc
  refine ⟨A, infinite_of_strict_dyadic_counts hlower, ?_, hlower⟩
  intro a ha b hb c hc e he heq
  obtain ⟨n, -, hn⟩ := hprefix (max (max a b) (max c e)) 0
  have hmem (u : ℕ) (hu : u ∈ A) (hle : u ≤ max (max a b) (max c e)) : u ∈ W n := by
    have hm : u ∈ A ∩ Icc 1 (max (max a b) (max c e)) :=
      ⟨hu, Nat.succ_le_of_lt (hpos hu), hle⟩
    exact (show u ∈ (W n : Set ℕ) ∩ Icc 1 (max (max a b) (max c e)) from hn.symm ▸ hm).1
  apply hsid n a (hmem a ha (by omega)) b (hmem b hb (by omega))
    c (hmem c hc (by omega)) e (hmem e he (by omega)) heq

private theorem critical_lower_bound_of_dyadic {A : Set ℕ} {d J : ℕ} (hd : 0 < d)
    (h : ∀ j ≥ J, 2 ^ j < d * (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * j)
    {x : ℕ} (hx : 2 ^ J ≤ x) :
    Real.log 2 / (2 * (d : ℝ)) * x <
      ((A ∩ Icc 1 x).ncard : ℝ) ^ 2 * Real.log x := by
  let j := Nat.log 2 x
  have hj : J ≤ j := Nat.le_log_of_pow_le (by decide) hx
  have hxpos : 0 < x := (show 0 < (2 : ℕ) ^ J by positivity).trans_le hx
  have hlo : 2 ^ j ≤ x := Nat.pow_log_le_self 2 hxpos.ne'
  have hhi : (x : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
    have hnat : x ≤ 2 * 2 ^ j := by
      simpa only [j, Nat.succ_eq_add_one, pow_succ, mul_comm] using
        (Nat.lt_pow_succ_log_self (by decide : 1 < 2) x).le
    exact_mod_cast hnat
  have hcount : (A ∩ Icc 1 (2 ^ j)).ncard ≤ (A ∩ Icc 1 x).ncard :=
    ncard_le_ncard (inter_subset_inter_right _ (Icc_subset_Icc_right hlo))
      ((finite_Icc 1 x).subset inter_subset_right)
  have hlog : (j : ℝ) * Real.log 2 ≤ Real.log x := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hlo)
  have hlogpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  let m : ℝ := (A ∩ Icc 1 (2 ^ j)).ncard
  have hdyadic : (2 : ℝ) ^ j < (d : ℝ) * m ^ 2 * (j : ℝ) := by
    dsimp [m]
    exact_mod_cast h j hj
  calc
    _ ≤ (Real.log 2 / (2 * (d : ℝ))) * (2 * (2 : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_left hhi (by positivity)
    _ = (Real.log 2 / (d : ℝ)) * (2 : ℝ) ^ j := by ring
    _ < (Real.log 2 / (d : ℝ)) * ((d : ℝ) * m ^ 2 * j) :=
      mul_lt_mul_of_pos_left hdyadic (div_pos hlogpos hdreal)
    _ = m ^ 2 * ((j : ℝ) * Real.log 2) := by
      field_simp [hdreal.ne']
    _ ≤ _ := by
      have hm : m ≤ ((A ∩ Icc 1 x).ncard : ℝ) := by
        dsimp [m]
        exact_mod_cast hcount
      gcongr

/-- A squared critical bound for all infinite Sidon sets forces a finite dyadic obstruction. -/
theorem finite_obstruction_from_core_sq
    (hsq : ∀ (A : Set ℕ), A.Infinite → IsSidon A → ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ x : ℕ, N ≤ x ∧ 1 ≤ x ∧
        ((A ∩ Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x) :
    DyadicFiniteObstruction := by
  classical
  by_contra hn
  unfold DyadicFiniteObstruction DyadicHorizon at hn
  push Not at hn
  obtain ⟨d, J, hd, hw⟩ := hn
  obtain ⟨A, hinf, hsid, hlower⟩ := infinite_witness_of_finite_witnesses hw
  let c : ℝ := Real.log 2 / (2 * (d : ℝ))
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨x, hx, _, hbound⟩ :=
    hsq A hinf hsid (Real.sqrt c) (Real.sqrt_pos.mpr hc) (2 ^ J)
  rw [Real.sq_sqrt hc.le] at hbound
  exact (critical_lower_bound_of_dyadic hd hlower hx).not_ge hbound

theorem finite_obstruction : DyadicFiniteObstruction := by
  sorry

/-- The open core (Erdős 1191 i) in rpow-free form: beyond every threshold there is a
scale `x` at which `|A ∩ [1,x]| ^ 2 * log x ≤ ε ^ 2 * x`. -/
theorem core_sq (A : Set ℕ) (_hinf : A.Infinite) (hS : IsSidon A) (ε : ℝ) (hε : 0 < ε)
    (N : ℕ) : ∃ x : ℕ, N ≤ x ∧ 1 ≤ x ∧
      ((A ∩ .Icc 1 x).ncard : ℝ) ^ 2 * Real.log x ≤ ε ^ 2 * x := by
  exact core_sq_from_finite_obstruction finite_obstruction A hS ε hε N

/-- The frequently-small form of the core, deduced from the rpow-free form. -/
theorem core (A : Set ℕ) (hinf : A.Infinite) (hS : IsSidon A) (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ x : ℕ in atTop, ((A ∩ .Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) *
      Real.log x ^ (1 / 2 : ℝ)) ≤ ε := by
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨x, hNx, hx1, hx⟩ := core_sq A hinf hS ε hε N
  exact ⟨x, hNx, normalised_le_of_sq_le hε hx1 hx⟩

end OMA.E1191i

theorem OMA.solution : type_of% @Erdos1191.erdos_1191.parts.i := by
  intro A hinf hS
  exact OMA.E1191i.liminf_ofReal_zero_of_frequently (OMA.E1191i.core A hinf hS)
