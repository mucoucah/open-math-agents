import FormalConjectures.ErdosProblems.«1191»

/-! Finite dyadic checkpoint witnesses for Erdős problem 1191(ii). -/

-- Problem: Erdős Problem 1191 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1191.lean:57 (declaration Erdos1191.erdos_1191.parts.ii)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Set
open scoped Topology

/-- A squared lower bound at the dyadic cutoffs suffices for the liminf. -/
private lemma density_from_dyadic_counts (A : Set ℕ) (d J : ℕ)
    (h : ∀ j ≥ J, 2 ^ j ≤ (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    ∃ c > (0 : ℝ), 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ c)) atTop := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let c : ℕ := 2 * (d + 1)
  refine ⟨(c : ℝ), by dsimp [c]; positivity, ?_⟩
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ x : ℕ in atTop, 2 / Real.log 2 ≤ Real.log (x : ℝ) :=
    hlog.eventually_ge_atTop _
  have hpoint : ∀ᶠ x : ℕ in atTop,
      (1 / 2 : ℝ) ≤ (A ∩ Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (c : ℝ) := by
    filter_upwards [hlarge, eventually_ge_atTop (2 ^ max J 1 : ℕ)] with x hx hxpow
    let j := Nat.log 2 x
    have hj : max J 1 ≤ j := Nat.le_log_of_pow_le (by decide) hxpow
    have hJ : J ≤ j := (le_max_left _ _).trans hj
    have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
    have hx0 : 0 < x := (pow_pos (by decide) _ : 0 < 2 ^ max J 1).trans_le hxpow
    have hlo : 2 ^ j ≤ x := Nat.pow_log_le_self 2 hx0.ne'
    have hhi : x ≤ 2 * 2 ^ j := by
      simpa only [pow_succ, mul_comm] using (Nat.lt_pow_succ_log_self (by decide : 1 < 2) x).le
    have hcount : (A ∩ Icc 1 (2 ^ j)).ncard ≤ (A ∩ Icc 1 x).ncard :=
      Set.ncard_le_ncard (inter_subset_inter_right _ (Icc_subset_Icc_right hlo))
        ((finite_Icc 1 x).subset inter_subset_right)
    have hjlog : (j : ℝ) * Real.log 2 ≤ Real.log (x : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hlo)
    have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
    have hlogsq : 2 ≤ Real.log (x : ℝ) * Real.log 2 := (div_le_iff₀ hlog2).1 hx
    have hjreal : 1 ≤ (j : ℝ) := by exact_mod_cast hj1
    have hjbase : (j : ℝ) + 1 ≤ Real.log (x : ℝ) ^ 2 := by
      calc
        _ ≤ (j : ℝ) * 2 := by linarith
        _ ≤ (j : ℝ) * (Real.log (x : ℝ) * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlogsq (Nat.cast_nonneg j)
        _ = Real.log (x : ℝ) * ((j : ℝ) * Real.log 2) := by ring
        _ ≤ _ := by simpa only [pow_two] using mul_le_mul_of_nonneg_left hjlog hlog0
    let m : ℝ := (A ∩ Icc 1 (2 ^ j)).ncard
    have hroot : Real.sqrt ((2 : ℝ) ^ j) ≤ m * ((j : ℝ) + 1) ^ (d + 1) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, ← pow_mul, mul_comm (d + 1) 2]
      dsimp [m]
      exact_mod_cast h j hJ
    have hscale : Real.sqrt (x : ℝ) ≤ 2 * Real.sqrt ((2 : ℝ) ^ j) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      apply le_trans (show (x : ℝ) ≤ 2 * (2 : ℝ) ^ j by exact_mod_cast hhi)
      nlinarith [show 0 ≤ (2 : ℝ) ^ j by positivity]
    have hweighted : m * ((j : ℝ) + 1) ^ (d + 1) ≤
        (A ∩ Icc 1 x).ncard * Real.log (x : ℝ) ^ (c : ℝ) := by
      rw [Real.rpow_natCast, show c = 2 * (d + 1) from rfl, pow_mul]
      apply mul_le_mul (by dsimp [m]; exact_mod_cast hcount)
        (pow_le_pow_left₀ (by positivity) hjbase _) (by positivity) (Nat.cast_nonneg _)
    rw [← Real.sqrt_eq_rpow, div_mul_eq_mul_div₀]
    apply (le_div_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hx0))).2
    linarith [hscale, hroot, hweighted]
  exact (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).trans_le
    (le_liminf_of_le (h := hpoint.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx))

/-- A property of finitely many coordinates of a Boolean sequence is closed. -/
private lemma closed_prefix_condition (n : ℕ) (P : (ℕ → Bool) → Prop)
    (hP : ∀ f g, (∀ i ≤ n, f i = g i) → P f → P g) : IsClosed {f | P f} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro f hf
  have hagree : ∀ᶠ g in 𝓝 f, ∀ i ∈ Finset.range (n + 1), g i = f i := by
    refine (eventually_all_finset _).mpr fun i _ ↦ ?_
    have hopen : IsOpen ((fun g : ℕ → Bool ↦ g i) ⁻¹' {f i}) :=
      (isOpen_discrete _).preimage (continuous_apply i)
    exact hopen.mem_nhds (by simp)
  exact hagree.mono fun g hg hPg ↦ hf (hP g f
    (fun i hi ↦ hg i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) hPg)

/-- Compatible finite prefix constraints have a common Boolean solution. -/
private lemma compact_prefix_conditions (P : ℕ → (ℕ → Bool) → Prop)
    (hloc : ∀ n f g, (∀ i ≤ n, f i = g i) → P n f → P n g)
    (hfin : ∀ N, ∃ f, ∀ n ≤ N, P n f) : ∃ f, ∀ n, P n f := by
  classical
  let C (n : ℕ) : Set (ℕ → Bool) := {f | P n f}
  have hnonempty := (isCompact_univ : IsCompact (univ : Set (ℕ → Bool))).inter_iInter_nonempty C
    (fun n ↦ closed_prefix_condition n (P n) (hloc n)) ?_
  · obtain ⟨f, _, hf⟩ := hnonempty
    exact ⟨f, mem_iInter.mp hf⟩
  · intro u
    obtain ⟨N, hN⟩ := (u.finite_toSet.bddAbove : BddAbove (u : Set ℕ))
    obtain ⟨f, hf⟩ := hfin N
    exact ⟨f, mem_univ _, mem_iInter₂.mpr fun n hn ↦ hf n (hN hn)⟩

private lemma infinite_of_dyadic_counts (A : Set ℕ) (d J : ℕ)
    (h : ∀ j ≥ J, 2 ^ j ≤ (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    A.Infinite := by
  intro hfin
  let M : ℝ := (A.ncard : ℝ) ^ 2
  let k : ℕ := 2 * (d + 1)
  have hM : 0 ≤ M := sq_nonneg _
  have hdecay : Tendsto (fun j : ℕ ↦ (2 * M) * (((j + 1 : ℕ) : ℝ) ^ k / 2 ^ (j + 1)))
      atTop (𝓝 (0 : ℝ)) := by
    have hbase := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
    simpa only [Function.comp_apply, mul_zero] using
      (hbase.comp (tendsto_add_atTop_nat 1)).const_mul (2 * M)
  obtain ⟨j, hj, hsmall⟩ := ((eventually_ge_atTop J).and
    (hdecay.eventually_lt_const (by norm_num : (0 : ℝ) < 1))).exists
  have hcount : ((A ∩ Icc 1 (2 ^ j)).ncard : ℝ) ≤ A.ncard := by
    exact_mod_cast (Set.ncard_le_ncard inter_subset_left hfin)
  have hcast : (2 : ℝ) ^ j ≤ ((A ∩ Icc 1 (2 ^ j)).ncard : ℝ) ^ 2 * ((j : ℝ) + 1) ^ k := by
    exact_mod_cast h j hj
  have hlower : (2 : ℝ) ^ j ≤ M * ((j : ℝ) + 1) ^ k :=
    hcast.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcount 2) (by positivity))
  rw [Nat.cast_add, Nat.cast_one, pow_succ, ← mul_div_assoc] at hsmall
  have hnum := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ j * 2)).mp hsmall
  linarith

/-- Finite witnesses must work simultaneously at all earlier dyadic cutoffs. -/
private def FiniteDyadicSidon (d J : ℕ) : Prop :=
  ∀ N : ℕ, ∃ S : Set ℕ, S ⊆ Icc 1 (2 ^ N) ∧ IsSidon S ∧
    ∀ j, J ≤ j → j ≤ N → 2 ^ j ≤ (S ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1))

private lemma sidon_of_finite_dyadic_witnesses (d J : ℕ) (h : FiniteDyadicSidon d J) :
    ∃ A : Set ℕ, IsSidon A ∧
      ∀ j ≥ J, 2 ^ j ≤ (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1)) := by
  classical
  let cut (f : ℕ → Bool) (n : ℕ) : Set ℕ := {a | f a = true} ∩ Icc 1 n
  let P (n : ℕ) (f : ℕ → Bool) : Prop := IsSidon (cut f n) ∧
    ∀ j, J ≤ j → 2 ^ j ≤ n →
      2 ^ j ≤ (cut f n ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1))
  obtain ⟨f, hf⟩ : ∃ f, ∀ n, P n f := by
    apply compact_prefix_conditions P
    · intro n f g hagree hf
      have hcut : cut f n = cut g n := by
        ext a
        constructor
        · rintro ⟨ha, hn⟩
          exact ⟨(hagree a hn.2).symm.trans (show f a = true from ha), hn⟩
        · rintro ⟨ha, hn⟩
          exact ⟨(hagree a hn.2).trans (show g a = true from ha), hn⟩
      simpa only [P, hcut] using hf
    · intro N
      obtain ⟨S, _, hSidon, hcount⟩ := h N
      let f : ℕ → Bool := fun a ↦ decide (a ∈ S)
      refine ⟨f, fun n hn ↦ ?_⟩
      have hcut : cut f n = S ∩ Icc 1 n := by
        ext a
        simp [cut, f]
      dsimp only [P]
      rw [hcut]
      refine ⟨?_, fun j hJ hj ↦ ?_⟩
      · intro a ha b hb c hc e he hsum
        exact hSidon a ha.1 b hb.1 c hc.1 e he.1 hsum
      · rw [inter_assoc, inter_eq_right.mpr (Icc_subset_Icc_right hj)]
        have hle : (2 : ℕ) ^ j ≤ 2 ^ N := hj.trans (hn.trans N.lt_two_pow_self.le)
        exact hcount j hJ ((pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hle)
  let A := {a | f a = true} ∩ Ici 1
  have hcut (n : ℕ) : A ∩ Icc 1 n = cut f n := by
    dsimp only [A, cut]
    rw [inter_assoc, inter_eq_right.mpr Icc_subset_Ici_self]
  refine ⟨A, ?_, fun j hj ↦ ?_⟩
  · intro a ha b hb c hc e he hsum
    let n := a + b + c + e
    have hm (x : ℕ) (hx : x ∈ A) (hn : x ≤ n) : x ∈ cut f n := by
      rw [← hcut]
      exact ⟨hx, hx.2, hn⟩
    exact (hf n).1 a (hm a ha (by dsimp [n]; omega)) b (hm b hb (by dsimp [n]; omega))
      c (hm c hc (by dsimp [n]; omega)) e (hm e he (by dsimp [n]; omega)) hsum
  · have hcount := (hf (2 ^ j)).2 j hj le_rfl
    simpa only [← hcut, inter_assoc, inter_self] using hcount

/-- A positive liminf supplies the finite checkpoint witnesses by restriction. -/
private lemma finite_dyadic_witnesses_of_density (A : Set ℕ) (hA : IsSidon A)
    (c : ℝ) (hc : 0 < c)
    (hlim : 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ c)) atTop) :
    ∃ d J : ℕ, FiniteDyadicSidon d J := by
  obtain ⟨r, hr, hrlt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlim
  have hrpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hr)
  have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (2 : ℝ) > 0)
    norm_num at h
    exact h
  obtain ⟨d, hd⟩ := exists_nat_ge c
  have hdyadic : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hlower := hdyadic.eventually (eventually_lt_of_lt_liminf hrlt)
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp hlower
  obtain ⟨L, hL⟩ := exists_nat_ge (r : ℝ)⁻¹
  refine ⟨d, max J₀ L, fun N ↦ ⟨A ∩ Icc 1 (2 ^ N), inter_subset_right, ?_, ?_⟩⟩
  · intro a ha b hb u hu v hv hsum
    exact hA a ha.1 b hb.1 u hu.1 v hv.1 hsum
  · intro j hJ hN
    have hjN : (2 : ℕ) ^ j ≤ 2 ^ N := pow_le_pow_right₀ (by decide) hN
    rw [inter_assoc, inter_eq_right.mpr (Icc_subset_Icc_right hjN)]
    let b : ℝ := (j : ℝ) + 1
    let m : ℝ := (A ∩ Icc 1 (2 ^ j)).ncard
    have hm : 0 ≤ m := by dsimp [m]; positivity
    have hb : 1 ≤ b := le_add_of_nonneg_left (Nat.cast_nonneg j)
    have hL' : (r : ℝ)⁻¹ ≤ b := hL.trans (by
      have hjL : (L : ℝ) ≤ j := by exact_mod_cast ((le_max_right J₀ L).trans hJ)
      dsimp [b]
      linarith)
    have hlogj : Real.log ((2 : ℝ) ^ j) ≤ b := by
      rw [Real.log_pow]
      dsimp only [b]
      calc
        _ ≤ (j : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2le (Nat.cast_nonneg _)
        _ ≤ _ := by linarith
    have hlogpow : Real.log ((2 : ℝ) ^ j) ^ c ≤ b ^ d := by
      calc
        _ ≤ b ^ c := Real.rpow_le_rpow (by rw [Real.log_pow]; positivity) hlogj hc.le
        _ ≤ b ^ (d : ℝ) := Real.rpow_le_rpow_of_exponent_le hb hd
        _ = _ := Real.rpow_natCast b d
    have hrbound := ENNReal.coe_lt_ofReal.mp (hJ₀ j ((le_max_left J₀ L).trans hJ))
    push_cast at hrbound
    rw [← Real.sqrt_eq_rpow, div_mul_eq_mul_div₀] at hrbound
    have hweighted : (r : ℝ) * Real.sqrt ((2 : ℝ) ^ j) ≤ m * b ^ d := by
      apply ((le_div_iff₀ (Real.sqrt_pos.2 (by positivity))).1 hrbound.le).trans
      exact mul_le_mul_of_nonneg_left hlogpow hm
    have hroot : Real.sqrt ((2 : ℝ) ^ j) ≤ m * b ^ (d + 1) := by
      calc
        _ = (r : ℝ)⁻¹ * ((r : ℝ) * Real.sqrt ((2 : ℝ) ^ j)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hrpos.ne', one_mul]
        _ ≤ b * (m * b ^ d) :=
          mul_le_mul hL' hweighted (by positivity) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    have hsquare := (Real.sqrt_le_iff.mp hroot).2
    rw [mul_pow, ← pow_mul, mul_comm (d + 1) 2] at hsquare
    dsimp [m, b] at hsquare
    exact_mod_cast hsquare

namespace Codex1191

private def base (n : ℕ) : ℕ := 2 ^ (2 ^ n)

private def span (n : ℕ) : ℕ := 2 ^ (2 ^ n - 1)

private def weight (n : ℕ) : ℕ := span n * 128 ^ n

private lemma span_succ (n : ℕ) : span (n + 1) = span n * base n := by
  unfold span base
  rw [← pow_add, pow_succ 2 n]
  congr 1
  have : 0 < (2 : ℕ) ^ n := by positivity
  omega

private lemma weight_succ (n : ℕ) : weight (n + 1) = weight n * (128 * base n) := by
  unfold weight
  rw [span_succ, pow_succ]
  ring

private lemma span_pos (n : ℕ) : 0 < span n := by
  unfold span
  positivity

private lemma weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  exact Nat.mul_pos (span_pos n) (by positivity)

private lemma base_pos (n : ℕ) : 0 < base n := by
  unfold base
  positivity

private def digit (n x y z : ℕ) : ℕ :=
  (y / 4 ^ n % 4) + 8 * (z / 4 ^ n % 4) + 64 * (x / span n % base n)

private def pack : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | n + 1, x, y, z => pack n x y z + weight n * digit n x y z

private lemma digit_sum_lt (n x y z u v w : ℕ) :
    digit n x y z + digit n u v w < 128 * base n - 1 := by
  have hxy := Nat.mod_lt (y / 4 ^ n) (by decide : 0 < 4)
  have hz := Nat.mod_lt (z / 4 ^ n) (by decide : 0 < 4)
  have hv := Nat.mod_lt (v / 4 ^ n) (by decide : 0 < 4)
  have hw := Nat.mod_lt (w / 4 ^ n) (by decide : 0 < 4)
  have hx := Nat.mod_lt (x / span n) (base_pos n)
  have hu := Nat.mod_lt (u / span n) (base_pos n)
  unfold digit
  omega

private lemma pack_sum_lt (n x y z u v w : ℕ) :
    pack n x y z + pack n u v w < weight n := by
  induction n with
  | zero => simp [pack, weight, span]
  | succ n ih =>
    rw [pack, pack, weight_succ]
    have hd := digit_sum_lt n x y z u v w
    have hp := weight_pos n
    have hstep : digit n x y z + digit n u v w + 1 ≤ 128 * base n := by omega
    calc
      _ < weight n * (digit n x y z + digit n u v w + 1) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ hstep

private lemma pack_succ_sum_eq {n x y z u v w a b c d e f : ℕ}
    (h : pack (n + 1) x y z + pack (n + 1) u v w =
         pack (n + 1) a b c + pack (n + 1) d e f) :
    pack n x y z + pack n u v w = pack n a b c + pack n d e f ∧
      digit n x y z + digit n u v w = digit n a b c + digit n d e f := by
  have hl := pack_sum_lt n x y z u v w
  have hr := pack_sum_lt n a b c d e f
  have hmul (l k : ℕ) (hl : l < weight n) :
      (l + weight n * k) % weight n = l := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have h' : (pack n x y z + pack n u v w) + weight n * (digit n x y z + digit n u v w) =
      (pack n a b c + pack n d e f) + weight n * (digit n a b c + digit n d e f) := by
    simp only [pack] at h
    linarith only [h, mul_add (weight n) (digit n x y z) (digit n u v w),
      mul_add (weight n) (digit n a b c) (digit n d e f)]
  have q := congrArg (· % weight n) h'
  rw [hmul _ _ hl, hmul _ _ hr] at q
  refine ⟨q, Nat.eq_of_mul_eq_mul_left (weight_pos n) ?_⟩
  omega

private lemma digit_sum_eq {n x y z u v w a b c d e f : ℕ}
    (h : digit n x y z + digit n u v w = digit n a b c + digit n d e f) :
    x / span n % base n + u / span n % base n =
      a / span n % base n + d / span n % base n ∧
    y / 4 ^ n % 4 + v / 4 ^ n % 4 = b / 4 ^ n % 4 + e / 4 ^ n % 4 ∧
    z / 4 ^ n % 4 + w / 4 ^ n % 4 = c / 4 ^ n % 4 + f / 4 ^ n % 4 := by
  unfold digit at h
  omega

private lemma extend_mod_sum {p q x y u v : ℕ}
    (hlo : x % p + y % p = u % p + v % p)
    (hhi : x / p % q + y / p % q = u / p % q + v / p % q) :
    x % (p * q) + y % (p * q) = u % (p * q) + v % (p * q) := by
  simp only [Nat.mod_mul]
  linarith only [hlo, congrArg (p * ·) hhi,
    mul_add p (x / p % q) (y / p % q), mul_add p (u / p % q) (v / p % q)]

private lemma unpack_sum {n x y z u v w a b c d e f : ℕ}
    (h : pack n x y z + pack n u v w = pack n a b c + pack n d e f) :
    x % span n + u % span n = a % span n + d % span n ∧
    y % 4 ^ n + v % 4 ^ n = b % 4 ^ n + e % 4 ^ n ∧
    z % 4 ^ n + w % 4 ^ n = c % 4 ^ n + f % 4 ^ n := by
  induction n with
  | zero => simp [span, Nat.mod_one]
  | succ n ih =>
    obtain ⟨hlo, hhi⟩ := pack_succ_sum_eq h
    obtain ⟨hlx, hly, hlz⟩ := ih hlo
    obtain ⟨hhx, hhy, hhz⟩ := digit_sum_eq hhi
    rw [span_succ, pow_succ 4 n]
    exact ⟨extend_mod_sum hlx hhx, extend_mod_sum hly hhy, extend_mod_sum hlz hhz⟩

private lemma pack_stable {m n x y z : ℕ} (hmn : m ≤ n)
    (hx : x < span m) (hy : y < 4 ^ m) (hz : z < 4 ^ m) :
    pack n x y z = pack m x y z := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hs : span m ≤ span n := by
      unfold span
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right
        (Nat.pow_le_pow_right (by decide) hmn) 1)
    have ht : (4 : ℕ) ^ m ≤ 4 ^ n := Nat.pow_le_pow_right (by decide) hmn
    simp [pack, digit, Nat.div_eq_of_lt (hx.trans_le hs), Nat.div_eq_of_lt (hy.trans_le ht),
      Nat.div_eq_of_lt (hz.trans_le ht), ih]

private def levels (x : ℕ) : ℕ := Nat.log 2 (Nat.log 2 x + 1) + 1

private lemma levels_fit (x : ℕ) :
    x < span (levels x) ∧ Nat.log 2 x < 4 ^ levels x ∧
      Nat.log 2 x ^ 2 < 4 ^ levels x := by
  let j := Nat.log 2 x
  have hj : j + 1 < 2 ^ levels x := Nat.lt_pow_succ_log_self (by decide) _
  have hjx : x < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have hspan : (2 : ℕ) ^ (j + 1) ≤ span (levels x) := by
    unfold span
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hpow : (2 : ℕ) ^ levels x * 2 ^ levels x = 4 ^ levels x := by rw [← mul_pow]; rfl
  have hj' : j < 2 ^ levels x := by omega
  have hj2 := Nat.mul_lt_mul_of_pos_right hj' (show 0 < (2 : ℕ) ^ levels x by positivity)
  refine ⟨hjx.trans_le hspan, ?_, ?_⟩
  · calc
      j ≤ j * 2 ^ levels x := Nat.le_mul_of_pos_right _ (by positivity)
      _ < _ := hj2.trans_eq hpow
  · rw [pow_two, ← hpow]
    exact (Nat.mul_le_mul_left j hj'.le).trans_lt hj2

private def encode (x : ℕ) : ℕ := pack (levels x) x (Nat.log 2 x) (Nat.log 2 x ^ 2)

private lemma encode_sum_data {a b u v : ℕ} (h : encode a + encode b = encode u + encode v) :
    a + b = u + v ∧
    Nat.log 2 a + Nat.log 2 b = Nat.log 2 u + Nat.log 2 v ∧
    Nat.log 2 a ^ 2 + Nat.log 2 b ^ 2 = Nat.log 2 u ^ 2 + Nat.log 2 v ^ 2 := by
  let n := max (max (levels a) (levels b)) (max (levels u) (levels v))
  have ha : levels a ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have hb : levels b ≤ n := (le_max_right _ _).trans (le_max_left _ _)
  have hu : levels u ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hv : levels v ≤ n := (le_max_right _ _).trans (le_max_right _ _)
  have he (x : ℕ) (hx : levels x ≤ n) :
      pack n x (Nat.log 2 x) (Nat.log 2 x ^ 2) = encode x :=
    pack_stable hx (levels_fit x).1 (levels_fit x).2.1 (levels_fit x).2.2
  have h' := unpack_sum (show
    pack n a (Nat.log 2 a) (Nat.log 2 a ^ 2) + pack n b (Nat.log 2 b) (Nat.log 2 b ^ 2) =
    pack n u (Nat.log 2 u) (Nat.log 2 u ^ 2) + pack n v (Nat.log 2 v) (Nat.log 2 v ^ 2) by
    rw [he a ha, he b hb, he u hu, he v hv]
    exact h)
  have hcap (x : ℕ) (hx : levels x ≤ n) :
      x % span n = x ∧ Nat.log 2 x % 4 ^ n = Nat.log 2 x ∧
        Nat.log 2 x ^ 2 % 4 ^ n = Nat.log 2 x ^ 2 := by
    have hs : span (levels x) ≤ span n := by
      unfold span
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right
        (Nat.pow_le_pow_right (by decide) hx) 1)
    have ht : (4 : ℕ) ^ levels x ≤ 4 ^ n := Nat.pow_le_pow_right (by decide) hx
    obtain ⟨hx₁, hx₂, hx₃⟩ := levels_fit x
    exact ⟨Nat.mod_eq_of_lt (hx₁.trans_le hs), Nat.mod_eq_of_lt (hx₂.trans_le ht),
      Nat.mod_eq_of_lt (hx₃.trans_le ht)⟩
  obtain ⟨ha₁, ha₂, ha₃⟩ := hcap a ha
  obtain ⟨hb₁, hb₂, hb₃⟩ := hcap b hb
  obtain ⟨hu₁, hu₂, hu₃⟩ := hcap u hu
  obtain ⟨hv₁, hv₂, hv₃⟩ := hcap v hv
  simpa only [ha₁, ha₂, ha₃, hb₁, hb₂, hb₃, hu₁, hu₂, hu₃, hv₁, hv₂, hv₃] using h'

private lemma pair_of_sum_and_squares {a b u v : ℕ} (hs : a + b = u + v)
    (hq : a ^ 2 + b ^ 2 = u ^ 2 + v ^ 2) :
    (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  have hp : a * b = u * v := by
    nlinarith only [hq, congrArg (· ^ 2) hs]
  have hsi : (a : ℤ) + b = (u : ℤ) + v := by exact_mod_cast hs
  have hpi : (a : ℤ) * b = (u : ℤ) * v := by exact_mod_cast hp
  have hfact : ((a : ℤ) - u) * ((a : ℤ) - v) = 0 := by
    nlinarith only [hpi, congrArg ((a : ℤ) * ·) hsi]
  rcases mul_eq_zero.mp hfact with h | h
  · left
    have : a = u := by omega
    exact ⟨this, by omega⟩
  · right
    have : a = v := by omega
    exact ⟨this, by omega⟩

private lemma encode_sum {a b u v : ℕ} (h : encode a + encode b = encode u + encode v) :
    a + b = u + v ∧
      ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
        (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)) := by
  obtain ⟨h₁, h₂, h₃⟩ := encode_sum_data h
  exact ⟨h₁, pair_of_sum_and_squares h₂ h₃⟩

private lemma encode_pos {x : ℕ} (hx : 0 < x) : 0 < encode x := by
  have hz : encode 0 = 0 := by decide
  by_contra! h
  have hsum := (encode_sum (a := x) (b := 0) (u := 0) (v := 0) (by omega)).1
  omega

private lemma encode_le {x : ℕ} (hx : 0 < x) :
    encode x ≤ 92 * x * (Nat.log 2 x + 1) ^ 7 := by
  let j := Nat.log 2 x
  let n := Nat.log 2 (j + 1)
  change pack (n + 1) x j (j ^ 2) ≤ 92 * x * (j + 1) ^ 7
  have hpow : (2 : ℕ) ^ n ≤ j + 1 := Nat.pow_log_le_self 2 (by omega)
  have hp : span n ≤ x := by
    have he : 2 ^ n - 1 ≤ j := by omega
    exact (Nat.pow_le_pow_right (by decide) he).trans (Nat.pow_log_le_self 2 hx.ne')
  have hpart : pack n x j (j ^ 2) ≤ weight n :=
    (Nat.le_add_right _ _).trans (pack_sum_lt n x j (j ^ 2) 0 0 0).le
  have hd : digit n x j (j ^ 2) ≤ 27 + 64 * (x / span n) := by
    have ha := Nat.mod_lt (j / 4 ^ n) (by decide : 0 < 4)
    have hb := Nat.mod_lt (j ^ 2 / 4 ^ n) (by decide : 0 < 4)
    have hc := Nat.mod_le (x / span n) (base n)
    unfold digit
    omega
  have hscale : (128 : ℕ) ^ n ≤ (j + 1) ^ 7 := by
    calc
      _ = ((2 : ℕ) ^ n) ^ 7 := by
        rw [show (128 : ℕ) = 2 ^ 7 by decide, ← pow_mul, ← pow_mul, mul_comm]
      _ ≤ _ := Nat.pow_le_pow_left hpow _
  rw [pack]
  calc
    _ ≤ weight n + weight n * (27 + 64 * (x / span n)) :=
      Nat.add_le_add hpart (Nat.mul_le_mul_left _ hd)
    _ = (28 * span n + 64 * (span n * (x / span n))) * 128 ^ n := by
      unfold weight
      ring
    _ ≤ 92 * x * 128 ^ n := by
      apply Nat.mul_le_mul_right
      have hdiv := Nat.mul_div_le x (span n)
      omega
    _ ≤ _ := Nat.mul_le_mul_left _ hscale

/-- Pair sums determine the original sum and the unordered pair of dyadic labels. -/
private theorem dyadic_additive_code :
    ∃ (E : ℕ → ℕ) (e : ℕ),
      (∀ a b u v, E a + E b = E u + E v →
        a + b = u + v ∧
          ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
           (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) ∧
      ∀ j, ∀ a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), 1 ≤ E a ∧ E a ≤ 2 ^ j * (j + 2) ^ e := by
  refine ⟨encode, 15, fun _ _ _ _ ↦ encode_sum, ?_⟩
  intro j a ha
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp ha
  have hlog := Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
  have hapos : 0 < a := (show 0 < (2 : ℕ) ^ j by positivity).trans_le hlo
  have htwo : (184 : ℕ) ≤ (j + 2) ^ 8 :=
    (by decide : 184 ≤ (2 : ℕ) ^ 8).trans (Nat.pow_le_pow_left (by omega) _)
  refine ⟨encode_pos hapos, ?_⟩
  calc
    _ ≤ 92 * a * (j + 1) ^ 7 := by simpa only [hlog] using encode_le hapos
    _ ≤ 92 * 2 ^ (j + 1) * (j + 2) ^ 7 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hhi.le) (Nat.pow_le_pow_left (by omega) _)
    _ = 2 ^ j * (184 * (j + 2) ^ 7) := by rw [pow_succ]; ring
    _ ≤ _ := by
      rw [show (15 : ℕ) = 8 + 7 by decide, pow_add]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ htwo)

end Codex1191

private lemma sidon_positive_difference_unique (S : Finset ℕ) (hS : IsSidon (S : Set ℕ))
    {a b u v : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hba : b < a) (hvu : v < u) (heq : a - b = u - v) : a = u ∧ b = v := by
  have hadd : a + v = u + b := by omega
  rcases hS a ha u hu v hv b hb hadd with h | h
  · exact ⟨h.1, h.2.symm⟩
  · omega

/-- Removing one endpoint for each short positive difference costs at most t points. -/
private lemma prune_short_differences (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (t : ℕ) :
    ∃ T ⊆ S, S.card ≤ T.card + t ∧ ∀ a ∈ T, ∀ b ∈ T, b < a → t ≤ a - b := by
  let bad := (S.product S).filter fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < t
  let drop := bad.image Prod.fst
  have hbad : bad.card ≤ t := by
    rw [← Finset.card_range t]
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ p.1 - p.2)
    · intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2.2
    · intro p hp q hq heq
      obtain ⟨hab, hp₁, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨huv, hq₁, _⟩ := Finset.mem_filter.mp hq
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      obtain ⟨h₁, h₂⟩ := sidon_positive_difference_unique S hS ha hb hu hv hp₁ hq₁ heq
      exact Prod.ext h₁ h₂
  have hsubset : drop ⊆ S := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hdrop : drop.card ≤ t := Finset.card_image_le.trans hbad
  refine ⟨S \ drop, Finset.sdiff_subset, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hsubset]
    omega
  · intro a ha b hb hba
    by_contra! hlt
    obtain ⟨haS, haD⟩ := Finset.mem_sdiff.mp ha
    have hbS := (Finset.mem_sdiff.mp hb).1
    have hp : (a, b) ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haS, hbS⟩, hba, hlt⟩
    exact haD (Finset.mem_image.mpr ⟨(a, b), hp, rfl⟩)

/-- Interactions between dyadic scales with i ≤ j/3 can be removed at low cost. -/
private lemma prune_distant_dyadic_collisions
    (B : ℕ → Finset ℕ) (hpos : ∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hSidon : ∀ j, IsSidon (B j : Set ℕ))
    (hneighbors : ∀ i j, j / 3 < i → i < j →
      ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
        b < a → v < u → a - b ≠ u - v) :
    ∃ C : ℕ → Finset ℕ, (∀ j, C j ⊆ B j ∧ (B j).card ≤ (C j).card + 2 ^ (j / 3)) ∧
      ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
        b < a → v < u → a - b ≠ u - v := by
  choose C hsub hcount hsep using fun j ↦
    prune_short_differences (B j) (hSidon j) (2 ^ (j / 3))
  refine ⟨C, fun j ↦ ⟨hsub j, hcount j⟩, ?_⟩
  intro i j hij a ha b hb u hu v hv hba hvu
  by_cases hnear : j / 3 < i
  · exact hneighbors i j hnear hij a (hsub i ha) b (hsub i hb)
      u (hsub j hu) v (hsub j hv) hba hvu
  · have hcap : (2 : ℕ) ^ i ≤ 2 ^ (j / 3) :=
      pow_le_pow_right₀ (by decide) (le_of_not_gt hnear)
    have htop := (Finset.mem_Ico.mp (hpos i (hsub i ha))).2
    have hbot := (Finset.mem_Ico.mp (hpos i (hsub i hb))).1
    rw [pow_succ] at htop
    have hgap : a - b < (2 : ℕ) ^ i := by omega
    exact ((hgap.trans_le hcap).trans_le (hsep j u hu v hv hvu)).ne

/-- The squared deletion budget times any fixed polynomial is negligible. -/
private lemma eventually_dyadic_pruning_budget (k : ℕ) :
    ∀ᶠ j : ℕ in atTop, 4 * (2 ^ (j / 3)) ^ 2 * (j + 1) ^ k ≤ 2 ^ j := by
  have hdecay := (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ ↦ (8 * 3 ^ k : ℝ) *
      (((n + 1 : ℕ) : ℝ) ^ k / 2 ^ (n + 1))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, mul_zero] using hdecay.const_mul (8 * 3 ^ k : ℝ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  refine (eventually_ge_atTop (3 * N)).mono fun j hj ↦ ?_
  let n := j / 3
  have hn : N ≤ n := by dsimp [n]; omega
  have hpoly : 4 * 3 ^ k * (n + 1) ^ k ≤ (2 : ℕ) ^ n := by
    have hsmall := hN n hn
    rw [Nat.cast_add, Nat.cast_one, pow_succ, ← mul_div_assoc] at hsmall
    have hnum := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * 2)).mp hsmall
    have hcast : (4 : ℝ) * 3 ^ k * ((n : ℝ) + 1) ^ k ≤ 2 ^ n := by linarith
    exact_mod_cast hcast
  have hbound : j + 1 ≤ 3 * (n + 1) := by dsimp [n]; omega
  calc
    _ ≤ 4 * (2 ^ n) ^ 2 * (3 * (n + 1)) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbound _)
    _ = (2 ^ n) ^ 2 * (4 * 3 ^ k * (n + 1) ^ k) := by rw [mul_pow]; ring
    _ ≤ (2 ^ n) ^ 2 * 2 ^ n := Nat.mul_le_mul_left _ hpoly
    _ = 2 ^ (n * 2 + n) := by rw [pow_add, pow_mul]
    _ ≤ 2 ^ j := pow_le_pow_right₀ (by decide) (by dsimp [n]; omega)

/-- A deletion budget at most half the guaranteed size costs one polynomial power. -/
private lemma dyadic_count_after_budget (d j M m t : ℕ) (hj : 1 ≤ j)
    (hbudget : 4 * t ^ 2 * (j + 1) ^ (2 * (d + 1)) ≤ 2 ^ j)
    (hM : 2 ^ j ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1))) (hm : M ≤ m + t) :
    2 ^ j ≤ m ^ 2 * (j + 1) ^ (2 * (d + 2)) := by
  let q : ℝ := (j : ℝ) + 1
  let budget : ℝ := t
  let x : ℝ := (2 : ℝ) ^ j
  have hq : 2 ≤ q := by
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    dsimp [q]
    linarith
  have hq0 : 0 ≤ q := by linarith
  have ht : 0 ≤ budget := by dsimp [budget]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hm' : (M : ℝ) ≤ (m : ℝ) + budget := by dsimp [budget]; exact_mod_cast hm
  have hroot : Real.sqrt x ≤ (M : ℝ) * q ^ (d + 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, ← pow_mul, mul_comm (d + 1) 2]
    dsimp [x, q]
    exact_mod_cast hM
  have hhalf : 2 * budget * q ^ (d + 1) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by positivity) hx).mpr
    rw [mul_pow, mul_pow, ← pow_mul q, mul_comm (d + 1) 2]
    norm_num only
    dsimp [budget, x, q]
    exact_mod_cast hbudget
  have hremaining : Real.sqrt x ≤ 2 * (m : ℝ) * q ^ (d + 1) := by
    have hmul := mul_le_mul_of_nonneg_right hm' (pow_nonneg hq0 (d + 1))
    linarith only [hroot, hhalf, hmul]
  have hweighted : Real.sqrt x ≤ (m : ℝ) * q ^ (d + 2) := by
    apply hremaining.trans
    calc
      _ = ((m : ℝ) * q ^ (d + 1)) * 2 := by ring
      _ ≤ ((m : ℝ) * q ^ (d + 1)) * q := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by rw [mul_assoc, ← pow_succ]
  have hfinal := (Real.sqrt_le_iff.mp hweighted).2
  rw [mul_pow, ← pow_mul, mul_comm (d + 2) 2] at hfinal
  dsimp [x, q] at hfinal
  exact_mod_cast hfinal


/-- After pruning, one extra power of the dyadic index absorbs the loss. -/
private lemma eventually_dyadic_pruning_preserves_count (d : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ M m : ℕ,
      2 ^ j ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1)) →
      M ≤ m + 2 ^ (j / 3) →
      2 ^ j ≤ m ^ 2 * (j + 1) ^ (2 * (d + 2)) := by
  filter_upwards [eventually_dyadic_pruning_budget (2 * (d + 1)), eventually_ge_atTop (1 : ℕ)]
    with j hbudget hj M m hM hm
  exact dyadic_count_after_budget d j M m _ hj hbudget hM hm

/-- Four points from two blocks with equal sums are trivial, given cross-block
difference disjointness and Sidon blocks. -/
private lemma two_block_core (C : ℕ → Finset ℕ) (hS : ∀ j, IsSidon (C j : Set ℕ))
    (hcross : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
      b < a → v < u → a - b ≠ u - v)
    {p r a b u v : ℕ} (ha : a ∈ C p) (hb : b ∈ C r) (hu : u ∈ C p) (hv : v ∈ C r)
    (hs : a + b = u + v) : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  rcases lt_trichotomy p r with hpr | rfl | hpr
  · left
    rcases lt_trichotomy a u with h | h | h
    · exact (hcross p r hpr u hu a ha b hb v hv h (by omega) (by omega)).elim
    · exact ⟨h, by omega⟩
    · exact (hcross p r hpr a ha u hu v hv b hb h (by omega) (by omega)).elim
  · exact hS p a ha u hu b hb v hv hs
  · left
    rcases lt_trichotomy b v with h | h | h
    · exact (hcross r p hpr v hv b hb a ha u hu h (by omega) (by omega)).elim
    · exact ⟨by omega, h⟩
    · exact (hcross r p hpr b hb v hv u hu a ha h (by omega) (by omega)).elim

/-- Encoding a cross-disjoint block family by a label-preserving additive code gives a Sidon set. -/
private lemma coded_union_sidon (C : ℕ → Finset ℕ) (hpos : ∀ j, C j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hS : ∀ j, IsSidon (C j : Set ℕ))
    (hcross : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
      b < a → v < u → a - b ≠ u - v)
    (E : ℕ → ℕ)
    (hsum : ∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)))
    (I : Finset ℕ) : IsSidon ((I.biUnion fun j ↦ (C j).image E : Finset ℕ) : Set ℕ) := by
  have hlog : ∀ j a, a ∈ C j → Nat.log 2 a = j := fun j a ha ↦
    Nat.log_eq_of_pow_le_of_lt_pow (Finset.mem_Ico.mp (hpos j ha)).1
      (Finset.mem_Ico.mp (hpos j ha)).2
  have hmem : ∀ x, x ∈ ((I.biUnion fun j ↦ (C j).image E : Finset ℕ) : Set ℕ) →
      ∃ a, a ∈ C (Nat.log 2 a) ∧ E a = x := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨a, by rw [hlog j a ha]; exact ha, rfl⟩
  intro x hx y hy z hz w hw hxz
  obtain ⟨a, ha, rfl⟩ := hmem x hx
  obtain ⟨u, hu, rfl⟩ := hmem y hy
  obtain ⟨b, hb, rfl⟩ := hmem z hz
  obtain ⟨v, hv, rfl⟩ := hmem w hw
  obtain ⟨hs, hl | hl⟩ := hsum a b u v hxz
  · rw [← hl.1] at hu
    rw [← hl.2] at hv
    rcases two_block_core C hS hcross ha hb hu hv hs with h | h
    · exact Or.inl ⟨by rw [h.1], by rw [h.2]⟩
    · exact Or.inr ⟨by rw [h.1], by rw [h.2]⟩
  · rw [← hl.1] at hv
    rw [← hl.2] at hu
    rcases two_block_core C hS hcross ha hb hv hu (by omega) with h | h
    · exact Or.inr ⟨by rw [h.1], by rw [h.2]⟩
    · exact Or.inl ⟨by rw [h.1], by rw [h.2]⟩

/-- A logarithmic shift is eventually dominated. -/
private lemma eventually_log_shift (c c' : ℕ) :
    ∃ K, ∀ k ≥ K, c' + c * (Nat.log 2 (k + 2) + 1) ≤ k := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  let Q : ℝ := c' + 2 * c + 3
  have hQ : 0 < Q := by positivity
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp
    ((h.eventually_lt_const (inv_pos.mpr hQ)).and (eventually_ge_atTop 1))
  refine ⟨c' + c * (L0 + 1) + 2, fun k hk ↦ ?_⟩
  by_cases hL : L0 ≤ Nat.log 2 (k + 2)
  · obtain ⟨hlt, hL1⟩ := hL0 _ hL
    set L := Nat.log 2 (k + 2)
    have hpow : 2 ^ L ≤ k + 2 := Nat.pow_log_le_self 2 (by omega)
    have hreal : Q * (L : ℝ) < 2 ^ L := by
      rw [pow_one, div_lt_iff₀ (by positivity)] at hlt
      have := mul_lt_mul_of_pos_left hlt hQ
      rwa [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] at this
    have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    have hnat : c' + c * (L + 1) + 2 < 2 ^ L := by
      have : ((c' + c * (L + 1) + 2 : ℕ) : ℝ) < 2 ^ L := by
        push_cast
        refine lt_of_le_of_lt ?_ hreal
        dsimp [Q]
        nlinarith [show (0 : ℝ) ≤ c by positivity, show (0 : ℝ) ≤ c' by positivity]
      exact_mod_cast this
    omega
  · have : c * (Nat.log 2 (k + 2) + 1) ≤ c * (L0 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- Finite Sidon witnesses from pruned dense blocks and a polylogarithmic additive code. -/
private lemma coded_finite_witness (d J : ℕ)
    (hB : ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∀ u ∈ B j, ∀ v ∈ B j,
        a + b = u + v → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
      (∀ j, J ≤ j → j ≤ N → 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧
      ∀ i j, j / 3 < i → i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
        b < a → v < u → a - b ≠ u - v)
    (E : ℕ → ℕ) (e : ℕ)
    (hsum : ∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)))
    (hsize : ∀ j, ∀ a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), 1 ≤ E a ∧ E a ≤ 2 ^ j * (j + 2) ^ e) :
    ∃ D J₀ : ℕ, ∀ N : ℕ, ∃ S : Set ℕ, S ⊆ Icc 1 (2 ^ N) ∧ IsSidon S ∧
      ∀ j, J₀ ≤ j → j ≤ N → 2 ^ j ≤ (S ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (D + 1)) := by
  classical
  obtain ⟨J₁, hJ₁⟩ := eventually_atTop.mp (eventually_dyadic_pruning_preserves_count d)
  obtain ⟨K, hK⟩ := eventually_log_shift e (max J J₁)
  have hEinj : Function.Injective E := by
    intro a b hab
    have h := (hsum a a b b (by rw [hab])).1
    omega
  refine ⟨d + 2 + 3 * e, max K 1, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hBS, hcounts, hnear⟩ := hB N
  have hSid : ∀ j, IsSidon (B j : Set ℕ) := fun j a ha u hu b hb v hv h ↦
    hBS j a ha b hb u hu v hv h
  obtain ⟨C, hC, hcross⟩ := prune_distant_dyadic_collisions B hpos hSid hnear
  have hCpos : ∀ j, C j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) := fun j ↦ (hC j).1.trans (hpos j)
  have hCS : ∀ j, IsSidon (C j : Set ℕ) := fun j a ha u hu b hb v hv h ↦
    hSid j a ((hC j).1 ha) u ((hC j).1 hu) b ((hC j).1 hb) v ((hC j).1 hv) h
  let I := (Finset.range (N + 1)).filter (fun j ↦ 2 ^ j * (j + 2) ^ e ≤ 2 ^ N)
  let T : Finset ℕ := I.biUnion fun j ↦ (C j).image E
  refine ⟨(T : Set ℕ), ?_, coded_union_sidon C hCpos hCS hcross E hsum I, ?_⟩
  · intro x hx
    obtain ⟨j, hj, hjx⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hjx
    have h1 := hsize j a (hCpos j ha)
    exact ⟨h1.1, h1.2.trans (Finset.mem_filter.mp hj).2⟩
  · intro k hk hkN
    let t := e * (Nat.log 2 (k + 2) + 1)
    have hkt := hK k ((le_max_left _ _).trans hk)
    have hk1 : 1 ≤ k := (le_max_right _ _).trans hk
    let j := k - t
    have hjk : j + t = k := by dsimp [j]; omega
    have hJj : J ≤ j := by dsimp [j]; have := le_max_left J J₁; omega
    have hJ₁j : J₁ ≤ j := by dsimp [j]; have := le_max_right J J₁; omega
    have hjN : j ≤ N := by dsimp [j]; omega
    have hlogk : k + 2 < 2 ^ (Nat.log 2 (k + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) _
    have hlogk' : 2 ^ Nat.log 2 (k + 2) ≤ k + 2 := Nat.pow_log_le_self 2 (by omega)
    have ht1 : (k + 2) ^ e ≤ 2 ^ t := by
      rw [show t = (Nat.log 2 (k + 2) + 1) * e by dsimp [t]; ring, pow_mul]
      exact Nat.pow_le_pow_left hlogk.le _
    have ht2 : 2 ^ t ≤ (k + 1) ^ (3 * e) := by
      rw [show t = (Nat.log 2 (k + 2) + 1) * e by dsimp [t]; ring, pow_mul, pow_mul]
      apply Nat.pow_le_pow_left
      rw [pow_succ]
      have h3 : 2 * (k + 2) ≤ (k + 1) ^ 3 := by
        have h2 : 2 ≤ k + 1 := by omega
        have h4 : 2 * 2 * (k + 1) ≤ (k + 1) ^ 3 := by
          rw [pow_succ, pow_two]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h2)
        omega
      omega
    have hjk2 : 2 ^ j * (j + 2) ^ e ≤ 2 ^ k := by
      rw [← hjk, pow_add]
      exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans ht1)
    have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      hjk2.trans (pow_le_pow_right₀ (by decide) hkN)⟩
    have hsub : (((C j).image E : Finset ℕ) : Set ℕ) ⊆ (T : Set ℕ) ∩ Icc 1 (2 ^ k) := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      have h1 := hsize j a (hCpos j ha)
      exact ⟨Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨j, hjI, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩),
        h1.1, h1.2.trans hjk2⟩
    have hcard : (C j).card ≤ ((T : Set ℕ) ∩ Icc 1 (2 ^ k)).ncard := by
      have := Set.ncard_le_ncard hsub ((finite_Icc 1 (2 ^ k)).subset inter_subset_right)
      rwa [Set.ncard_coe_finset, Finset.card_image_of_injective _ hEinj] at this
    have hcount := hJ₁ j hJ₁j _ _ (hcounts j hJj hjN) (hC j).2
    calc
      2 ^ k = 2 ^ j * 2 ^ t := by rw [← pow_add, hjk]
      _ ≤ ((C j).card ^ 2 * (j + 1) ^ (2 * (d + 2))) * (k + 1) ^ (3 * e) :=
        Nat.mul_le_mul hcount ht2
      _ ≤ (((T : Set ℕ) ∩ Icc 1 (2 ^ k)).ncard ^ 2 * (k + 1) ^ (2 * (d + 2))) *
          (k + 1) ^ (3 * e) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left hcard _)
          (Nat.pow_le_pow_left (by omega) _))
      _ = ((T : Set ℕ) ∩ Icc 1 (2 ^ k)).ncard ^ 2 * (k + 1) ^ (2 * (d + 2) + 3 * e) := by
        rw [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by omega) (by omega))

/-- Dense Sidon blocks in all dyadic intervals whose positive differences avoid those of
blocks at nearby scales (j/3 < i < j), with a fixed polylogarithmic loss. -/
private def NearbyDyadicSidon : Prop :=
  ∃ d J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
    (∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∀ u ∈ B j, ∀ v ∈ B j,
      a + b = u + v → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
    (∀ j, J ≤ j → j ≤ N → 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧
    ∀ i j, j / 3 < i → i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
      b < a → v < u → a - b ≠ u - v

/-- The differences that can participate in a nontrivial equality of block sums. -/
private def positiveDifferences (S : Finset ℕ) : Finset ℕ :=
  ((S.product S).filter fun p ↦ p.2 < p.1).image fun p ↦ p.1 - p.2

private lemma mem_positiveDifferences {S : Finset ℕ} {u : ℕ} :
    u ∈ positiveDifferences S ↔ ∃ a ∈ S, ∃ b ∈ S, b < a ∧ a - b = u := by
  constructor
  · intro hu
    obtain ⟨⟨a, b⟩, hp, heq⟩ := Finset.mem_image.mp hu
    obtain ⟨hab, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨a, ha, b, hb, hlt, heq⟩
  · rintro ⟨a, ha, b, hb, hlt, rfl⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hlt⟩, rfl⟩

private def earlierDifferenceConflicts (B : ℕ → Finset ℕ) (j : ℕ) : Finset ℕ :=
  positiveDifferences (B j) ∩ (Finset.range j).biUnion (fun i ↦ positiveDifferences (B i))

/-- Each forbidden positive difference has at most one ordered pair of endpoints. -/
private lemma prune_forbidden_differences (S D : Finset ℕ) (hS : IsSidon (S : Set ℕ)) :
    ∃ T ⊆ S, S.card ≤ T.card + D.card ∧ Disjoint (positiveDifferences T) D := by
  classical
  let pairs := (S.product S).filter fun p ↦ p.2 < p.1 ∧ p.1 - p.2 ∈ D
  let drop := pairs.image Prod.fst
  have hpairs : pairs.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ p.1 - p.2)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.2
    · intro p hp q hq heq
      obtain ⟨hpS, hp_lt, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqS, hq_lt, _⟩ := Finset.mem_filter.mp hq
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hpS
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hqS
      obtain ⟨h₁, h₂⟩ := sidon_positive_difference_unique S hS ha hb hu hv hp_lt hq_lt heq
      exact Prod.ext h₁ h₂
  have hsub : drop ⊆ S := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hdrop : drop.card ≤ D.card := Finset.card_image_le.trans hpairs
  refine ⟨S \ drop, Finset.sdiff_subset, ?_, Finset.disjoint_left.mpr ?_⟩
  · rw [Finset.card_sdiff_of_subset hsub]
    omega
  · intro u hu huD
    obtain ⟨a, ha, b, hb, hlt, rfl⟩ := mem_positiveDifferences.mp hu
    obtain ⟨haS, haDrop⟩ := Finset.mem_sdiff.mp ha
    have hbS := (Finset.mem_sdiff.mp hb).1
    apply haDrop
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haS, hbS⟩, hlt, huD⟩, rfl⟩

/-- Charge deletions in the later block once per shared positive difference. -/
private lemma prune_shared_dyadic_differences
    (B : ℕ → Finset ℕ) (hS : ∀ j, IsSidon (B j : Set ℕ)) :
    ∃ C : ℕ → Finset ℕ,
      (∀ j, C j ⊆ B j ∧ (B j).card ≤ (C j).card + (earlierDifferenceConflicts B j).card) ∧
      ∀ i j, i < j → Disjoint (positiveDifferences (C i)) (positiveDifferences (C j)) := by
  classical
  choose C hsub hcard hdisj using
    fun j ↦ prune_forbidden_differences (B j) (earlierDifferenceConflicts B j) (hS j)
  refine ⟨C, fun j ↦ ⟨hsub j, hcard j⟩, ?_⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro u hui huj
  apply Finset.disjoint_left.mp (hdisj j) huj
  obtain ⟨a, ha, b, hb, hlt, heq⟩ := mem_positiveDifferences.mp hui
  obtain ⟨v, hv, w, hw, hlt', heq'⟩ := mem_positiveDifferences.mp huj
  exact Finset.mem_inter.mpr
    ⟨mem_positiveDifferences.mpr ⟨v, hsub j hv, w, hsub j hw, hlt', heq'⟩,
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hij,
        mem_positiveDifferences.mpr ⟨a, hsub i ha, b, hsub i hb, hlt, heq⟩⟩⟩

/-- With separation at scales above k, all remaining shared differences lie below 2^k. -/
private lemma dyadic_conflicts_card_le
    (B : ℕ → Finset ℕ) (hpos : ∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (j k : ℕ)
    (hsep : ∀ i, k < i → i < j →
      Disjoint (positiveDifferences (B i)) (positiveDifferences (B j))) :
    (earlierDifferenceConflicts B j).card ≤ 2 ^ k := by
  rw [← Finset.card_range (2 ^ k)]
  apply Finset.card_le_card
  intro u hu
  obtain ⟨huj, huEarlier⟩ := Finset.mem_inter.mp hu
  obtain ⟨i, hij, hui⟩ := Finset.mem_biUnion.mp huEarlier
  have hi : i ≤ k := by
    by_contra! hki
    exact Finset.disjoint_left.mp (hsep i hki (Finset.mem_range.mp hij)) hui huj
  obtain ⟨a, ha, b, hb, _, rfl⟩ := mem_positiveDifferences.mp hui
  have htop := (Finset.mem_Ico.mp (hpos i ha)).2
  have hbot := (Finset.mem_Ico.mp (hpos i hb)).1
  rw [pow_succ] at htop
  exact Finset.mem_range.mpr ((show a - b < 2 ^ i by omega).trans_le
    (pow_le_pow_right₀ (by decide) hi))

/-- Turán's theorem gives a lower bound on an independent set from the edge count. -/
private lemma independent_set_from_edge_count {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ T : Finset V, G.IsIndepSet (T : Set V) ∧
      (Fintype.card V) ^ 2 ≤ T.card * (Fintype.card V + 2 * G.edgeFinset.card) := by
  classical
  obtain ⟨T, hT⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  refine ⟨T, hT.isIndepSet, ?_⟩
  let n := Fintype.card V
  let r := T.card
  have hfree : Gᶜ.CliqueFree (r + 1) := by
    intro U hU
    have hUi : G.IsIndepSet (U : Set V) := by
      simpa only [SimpleGraph.isClique_compl] using hU.isClique
    have hle := hT.maximum U hUi
    change U.card ≤ r at hle
    rw [hU.card_eq] at hle
    omega
  by_cases hr : 0 < r
  · have hTur : Gᶜ.edgeFinset.card ≤ (SimpleGraph.turanGraph n r).edgeFinset.card := by
      rw [SimpleGraph.card_edgeFinset_turanGraph]
      exact hfree.card_edgeFinset_le
    have hbound : 2 * r * Gᶜ.edgeFinset.card ≤ (r - 1) * n ^ 2 :=
      (Nat.mul_le_mul_left _ hTur).trans SimpleGraph.mul_card_edgeFinset_turanGraph_le
    have hdisj : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
      apply Finset.disjoint_left.mpr
      intro e
      refine Sym2.ind ?_ e
      intro a b hab hba
      exact ((G.compl_adj a b).mp ((Gᶜ.mem_edgeSet).mp (SimpleGraph.mem_edgeFinset.mp hba))).2
        (G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp hab))
    have hunion : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
      ext e
      refine Sym2.ind ?_ e
      intro a b
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj, SimpleGraph.top_adj]
      exact ⟨fun h ↦ h.elim G.ne_of_adj And.left,
        fun h ↦ (em (G.Adj a b)).imp_right fun hab ↦ ⟨h, hab⟩⟩
    have hcards : G.edgeFinset.card + Gᶜ.edgeFinset.card = n.choose 2 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
      exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    have hchoose : 2 * n.choose 2 + n = n ^ 2 := by
      rw [Nat.choose_two_right, Nat.mul_comm 2, Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd]
      cases n with
      | zero => simp
      | succ n =>
        simp [pow_two, Nat.succ_mul]
        ring
    have hbalance : r * (n + 2 * G.edgeFinset.card) + 2 * r * Gᶜ.edgeFinset.card = r * n ^ 2 := by
      calc
        _ = r * (2 * (G.edgeFinset.card + Gᶜ.edgeFinset.card) + n) := by ring
        _ = _ := by rw [hcards, hchoose]
    have hpred : (r - 1) * n ^ 2 + n ^ 2 = r * n ^ 2 := by
      calc
        _ = (r - 1 + 1) * n ^ 2 := by rw [Nat.add_mul, one_mul]
        _ = _ := by rw [Nat.sub_add_cancel hr]
    change n ^ 2 ≤ r * (n + 2 * G.edgeFinset.card)
    omega
  · have hr0 : r = 0 := by omega
    rw [hr0, zero_add, SimpleGraph.cliqueFree_one] at hfree
    have hn : Fintype.card V = 0 := Fintype.card_eq_zero_iff.mpr hfree
    change n ^ 2 ≤ _
    have hn' : n = 0 := hn
    simp [hn']

/-- Shared differences are edges of a graph, so a sparse conflict graph costs only a
factor of one plus the average degree. -/
private lemma prune_sparse_forbidden_differences (S D : Finset ℕ) (hS : IsSidon (S : Set ℕ)) :
    ∃ T ⊆ S, S.card ^ 2 ≤ T.card * (S.card + 2 * D.card) ∧
      Disjoint (positiveDifferences T) D := by
  classical
  let V := (S : Set ℕ)
  let sep : V → V → ℕ := fun a b ↦ max (a : ℕ) (b : ℕ) - min (a : ℕ) (b : ℕ)
  have hcomm : ∀ a b, sep a b = sep b a := by
    intro a b
    simp only [sep, max_comm, min_comm]
  let G : SimpleGraph V := {
    Adj := fun a b ↦ a ≠ b ∧ sep a b ∈ D
    symm := by
      constructor
      intro a b hab
      exact ⟨hab.1.symm, (hcomm a b) ▸ hab.2⟩
    loopless := ⟨fun a ha ↦ ha.1 rfl⟩ }
  let edgeDifference : Sym2 V → ℕ := Sym2.lift ⟨sep, hcomm⟩
  have hsorted : ∀ e ∈ G.edgeFinset, ∃ a b : V, (b : ℕ) < a ∧ e = s(a, b) := by
    intro e
    refine Sym2.ind ?_ e
    intro a b he
    have hadj := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
    change a ≠ b ∧ sep a b ∈ D at hadj
    rcases lt_or_gt_of_ne (fun eq : (a : ℕ) = b ↦ hadj.1 (Subtype.ext eq)) with h | h
    · exact ⟨b, a, h, Sym2.eq_swap⟩
    · exact ⟨a, b, h, rfl⟩
  have hvalue : ∀ {a b : V}, (b : ℕ) < a → edgeDifference s(a, b) = (a : ℕ) - b := by
    intro a b h
    simp only [edgeDifference, Sym2.lift_mk, sep, max_eq_left h.le, min_eq_right h.le]
  have hcard : G.edgeFinset.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn edgeDifference
    · intro e he
      obtain ⟨a, b, _, rfl⟩ := hsorted e he
      exact (G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)).2
    · intro e he f hf heq
      obtain ⟨a, b, hba, rfl⟩ := hsorted e he
      obtain ⟨u, v, hvu, rfl⟩ := hsorted f hf
      rw [hvalue hba, hvalue hvu] at heq
      obtain ⟨h₁, h₂⟩ := sidon_positive_difference_unique S hS
        a.property b.property u.property v.property hba hvu heq
      rw [Subtype.ext h₁, Subtype.ext h₂]
  obtain ⟨U, hU, hUcard⟩ := independent_set_from_edge_count G
  let T := U.map (Function.Embedding.subtype fun x ↦ x ∈ S)
  refine ⟨T, ?_, ?_, Finset.disjoint_left.mpr ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact a.property
  · rw [Finset.card_map]
    have hsize : Fintype.card V = S.card := Fintype.card_coe S
    rw [← hsize]
    exact hUcard.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hcard) _))
  · intro u hu huD
    obtain ⟨x, hx, y, hy, hyx, rfl⟩ := mem_positiveDifferences.mp hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    change (b : ℕ) < (a : ℕ) at hyx
    change (a : ℕ) - (b : ℕ) ∈ D at huD
    have hab : a ≠ b := fun h ↦ hyx.ne (congrArg Subtype.val h).symm
    apply hU ha hb hab
    exact ⟨hab, by simpa only [sep, max_eq_left hyx.le, min_eq_right hyx.le] using huD⟩

/-- Dense finite blocks with a polynomial bound on the average number of conflicts. -/
private def SparseDyadicSidon : Prop :=
  ∃ d k J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
    (∀ j, IsSidon (B j : Set ℕ)) ∧
    ∀ j, J ≤ j → j ≤ N →
      2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) ∧
      (B j).card + 2 * (earlierDifferenceConflicts B j).card ≤ (B j).card * (j + 1) ^ k

private lemma nearby_of_sparse_dyadic_blocks (h : SparseDyadicSidon) : NearbyDyadicSidon := by
  obtain ⟨d, k, J, hB⟩ := h
  refine ⟨d + k, J, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hSidon, hcounts⟩ := hB N
  choose C hsub hsize havoids using fun j ↦
    prune_sparse_forbidden_differences (B j) (earlierDifferenceConflicts B j) (hSidon j)
  refine ⟨C, fun j ↦ (hsub j).trans (hpos j), ?_, ?_, ?_⟩
  · intro j a ha b hb u hu v hv hs
    exact hSidon j a (hsub j ha) u (hsub j hu) b (hsub j hb) v (hsub j hv) hs
  · intro j hj hjN
    obtain ⟨hdense, hbudget⟩ := hcounts j hj hjN
    have hposB : 0 < (B j).card := by
      by_contra! hzero
      rw [Nat.eq_zero_of_le_zero hzero, zero_pow (by decide), zero_mul] at hdense
      exact (by positivity : 0 < (2 : ℕ) ^ j).not_ge hdense
    have hm : (B j).card ≤ (C j).card * (j + 1) ^ k := by
      apply Nat.le_of_mul_le_mul_right _ hposB
      calc
        _ = (B j).card ^ 2 := by ring
        _ ≤ (C j).card * ((B j).card + 2 * (earlierDifferenceConflicts B j).card) := hsize j
        _ ≤ (C j).card * ((B j).card * (j + 1) ^ k) := Nat.mul_le_mul_left _ hbudget
        _ = _ := by ring
    calc
      _ ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) := hdense
      _ ≤ ((C j).card * (j + 1) ^ k) ^ 2 * (j + 1) ^ (2 * (d + 1)) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm _)
      _ = _ := by
        rw [mul_pow, ← pow_mul, show 2 * (d + k + 1) = k * 2 + 2 * (d + 1) by omega, pow_add]
        ring
  · intro i j _ hij a ha b hb u hu v hv hba hvu heq
    apply Finset.disjoint_left.mp (havoids j) (mem_positiveDifferences.mpr ⟨u, hu, v, hv, hvu, rfl⟩)
    exact Finset.mem_inter.mpr
      ⟨mem_positiveDifferences.mpr ⟨u, hsub j hu, v, hsub j hv, hvu, rfl⟩,
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hij,
          mem_positiveDifferences.mpr ⟨a, hsub i ha, b, hsub i hb, hba, heq⟩⟩⟩

/-- A square-root bound on the number of conflicts fits the average-degree budget. -/
private lemma dyadic_conflict_budget_of_card_le
    (B : ℕ → Finset ℕ) (j d ℓ : ℕ) (hj : 1 ≤ j)
    (hconflicts : (earlierDifferenceConflicts B j).card ≤ 2 ^ (j / 2) * (j + 1) ^ ℓ)
    (hdense : 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    (B j).card + 2 * (earlierDifferenceConflicts B j).card ≤
      (B j).card * (j + 1) ^ (d + ℓ + 3) := by
  let q := j + 1
  let M := (B j).card
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hroot : 2 ^ (j / 2) ≤ M * q ^ (d + 1) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    calc
      (2 ^ (j / 2)) ^ 2 = 2 ^ (j / 2 * 2) := by rw [pow_mul]
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by decide) (by omega)
      _ ≤ M ^ 2 * q ^ (2 * (d + 1)) := hdense
      _ = (M * q ^ (d + 1)) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm 2 (d + 1)]
  have hcount : (earlierDifferenceConflicts B j).card ≤ M * q ^ (d + ℓ + 1) := by
    calc
      _ ≤ 2 ^ (j / 2) * q ^ ℓ := hconflicts
      _ ≤ (M * q ^ (d + 1)) * q ^ ℓ := Nat.mul_le_mul_right _ hroot
      _ = _ := by rw [mul_assoc, ← pow_add, show d + 1 + ℓ = d + ℓ + 1 by omega]
  let R := q ^ (d + ℓ + 1)
  have hR : 1 ≤ R := by
    simpa only [one_pow, R] using Nat.pow_le_pow_left (show 1 ≤ q by omega) (d + ℓ + 1)
  have hq2 : 3 ≤ q ^ 2 := by
    exact (by decide : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left hq 2)
  calc
    _ ≤ M + 2 * (M * R) := Nat.add_le_add_left (Nat.mul_le_mul_left 2 hcount) _
    _ ≤ M * R + 2 * (M * R) := Nat.add_le_add_right
      (by simpa only [mul_one] using Nat.mul_le_mul_left M hR) _
    _ = (M * R) * 3 := by ring
    _ ≤ (M * R) * q ^ 2 := Nat.mul_le_mul_left _ hq2
    _ = _ := by
      dsimp [R]
      rw [mul_assoc, ← pow_add]

/-- Conflicts below the square-root scale, times a polynomial, fit the average-degree budget. -/
private lemma dyadic_conflict_budget_from_scale
    (B : ℕ → Finset ℕ) (hpos : ∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (j s d ℓ : ℕ) (hj : 1 ≤ j)
    (hsep : ∀ i, s < i → i < j →
      Disjoint (positiveDifferences (B i)) (positiveDifferences (B j)))
    (hscale : 2 ^ s ≤ 2 ^ (j / 2) * (j + 1) ^ ℓ)
    (hdense : 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    (B j).card + 2 * (earlierDifferenceConflicts B j).card ≤
      (B j).card * (j + 1) ^ (d + ℓ + 3) :=
  dyadic_conflict_budget_of_card_le B j d ℓ hj
    ((dyadic_conflicts_card_le B hpos j s hsep).trans hscale) hdense

/-- A square-root bound on each overlap with a nearby block also fits the budget. -/
private lemma dyadic_conflict_budget_from_pairwise_overlap
    (B : ℕ → Finset ℕ) (hpos : ∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (j s d ℓ : ℕ) (hj : 1 ≤ j)
    (hscale : 2 ^ s ≤ 2 ^ (j / 2) * (j + 1) ^ ℓ)
    (hpair : ∀ i, s < i → i < j →
      (positiveDifferences (B i) ∩ positiveDifferences (B j)).card ≤
        2 ^ (j / 2) * (j + 1) ^ ℓ)
    (hdense : 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    (B j).card + 2 * (earlierDifferenceConflicts B j).card ≤
      (B j).card * (j + 1) ^ (d + (ℓ + 1) + 3) := by
  classical
  let I := Finset.Ioo s j
  let common := fun i ↦ positiveDifferences (B i) ∩ positiveDifferences (B j)
  let R := 2 ^ (j / 2) * (j + 1) ^ ℓ
  have hsub : earlierDifferenceConflicts B j ⊆ Finset.range (2 ^ s) ∪ I.biUnion common := by
    intro u hu
    obtain ⟨huj, huEarlier⟩ := Finset.mem_inter.mp hu
    obtain ⟨i, hij, hui⟩ := Finset.mem_biUnion.mp huEarlier
    by_cases hi : s < i
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_Ioo.mpr ⟨hi, Finset.mem_range.mp hij⟩, Finset.mem_inter.mpr ⟨hui, huj⟩⟩)
    · apply Finset.mem_union_left
      obtain ⟨a, ha, b, hb, _, rfl⟩ := mem_positiveDifferences.mp hui
      have htop := (Finset.mem_Ico.mp (hpos i ha)).2
      have hbot := (Finset.mem_Ico.mp (hpos i hb)).1
      rw [pow_succ] at htop
      exact Finset.mem_range.mpr ((show a - b < 2 ^ i by omega).trans_le
        (pow_le_pow_right₀ (by decide) (by omega)))
  have hI : I.card ≤ j := by
    rw [← Finset.card_range j]
    exact Finset.card_le_card fun i hi ↦ Finset.mem_range.mpr (Finset.mem_Ioo.mp hi).2
  have hu : (I.biUnion common).card ≤ j * R := by
    refine (Finset.card_biUnion_le_card_mul I common R ?_).trans (Nat.mul_le_mul_right R hI)
    intro i hi
    obtain ⟨hi₁, hi₂⟩ := Finset.mem_Ioo.mp hi
    exact hpair i hi₁ hi₂
  refine dyadic_conflict_budget_of_card_le B j d (ℓ + 1) hj ?_ hdense
  calc
    _ ≤ (Finset.range (2 ^ s) ∪ I.biUnion common).card := Finset.card_le_card hsub
    _ ≤ 2 ^ s + (I.biUnion common).card := by
      simpa only [Finset.card_range] using Finset.card_union_le (Finset.range (2 ^ s)) (I.biUnion common)
    _ ≤ R + j * R := Nat.add_le_add hscale hu
    _ = _ := by dsimp [R]; rw [pow_succ]; ring

private lemma sparse_of_nearby_dyadic_blocks (h : NearbyDyadicSidon) : SparseDyadicSidon := by
  obtain ⟨d, J, hB⟩ := h
  refine ⟨d, d + 3, max J 1, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hSidon, hcounts, hsep⟩ := hB N
  refine ⟨B, hpos, fun j a ha u hu b hb v hv hs ↦ hSidon j a ha b hb u hu v hv hs, ?_⟩
  intro j hj hjN
  have hdense := hcounts j ((le_max_left _ _).trans hj) hjN
  refine ⟨hdense, ?_⟩
  have hbudget := dyadic_conflict_budget_from_scale B hpos j (j / 2) d 0
    ((le_max_right _ _).trans hj) ?_ (by simp) hdense
  · simpa only [add_zero] using hbudget
  · intro i hi hij
    apply Finset.disjoint_left.mpr
    intro t hti htj
    obtain ⟨a, ha, b, hb, hba, heq⟩ := mem_positiveDifferences.mp hti
    obtain ⟨u, hu, v, hv, hvu, heq'⟩ := mem_positiveDifferences.mp htj
    exact hsep i j (by omega) hij a ha b hb u hu v hv hba hvu (heq.trans heq'.symm)

/-- Ordered pairs in S whose positive difference lies in D. -/
private def conflictPairs (S D : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S.product S).filter fun p ↦ p.2 < p.1 ∧ p.1 - p.2 ∈ D

private lemma mem_conflictPairs {S D : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ conflictPairs S D ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ p.2 < p.1 ∧ p.1 - p.2 ∈ D := by
  simp only [conflictPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, and_assoc]

private lemma card_conflictPairs_le_of_isSidon (S D : Finset ℕ) (hS : IsSidon (S : Set ℕ)) :
    (conflictPairs S D).card ≤ (positiveDifferences S ∩ D).card := by
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ p.1 - p.2)
  · intro p hp
    obtain ⟨ha, hb, hlt, hD⟩ := mem_conflictPairs.mp hp
    exact Finset.mem_inter.mpr ⟨mem_positiveDifferences.mpr ⟨p.1, ha, p.2, hb, hlt, rfl⟩, hD⟩
  · intro p hp q hq heq
    obtain ⟨ha, hb, hba, _⟩ := mem_conflictPairs.mp hp
    obtain ⟨hu, hv, hvu, _⟩ := mem_conflictPairs.mp hq
    obtain ⟨h₁, h₂⟩ := sidon_positive_difference_unique S hS ha hb hu hv hba hvu heq
    exact Prod.ext h₁ h₂

/-- Strictly increasing 3-term arithmetic progressions in S. -/
private def threeAPs (S : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (S.product (S.product S)).filter fun t ↦
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 + t.2.2 = 2 * t.2.1

private lemma mem_threeAPs {S : Finset ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ threeAPs S ↔
      t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 + t.2.2 = 2 * t.2.1 := by
  simp only [threeAPs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, and_assoc]

private lemma threeAPs_eq_empty_of_isSidon (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) :
    threeAPs S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨ha, hc, hb, hac, hcb, hsum⟩ := mem_threeAPs.mp ht
  rcases hS t.1 ha t.2.1 hc t.2.2 hb t.2.1 hc (by omega) with h | h <;> omega

/-- Strictly ordered 4-element additive quadruples a + b = c + d in S. -/
private def fourQuadruples (S : Finset ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (S.product (S.product (S.product S))).filter fun t ↦
    t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2 ∧ t.1 + t.2.2.2 = t.2.1 + t.2.2.1

private lemma mem_fourQuadruples {S : Finset ℕ} {t : ℕ × ℕ × ℕ × ℕ} :
    t ∈ fourQuadruples S ↔
      t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2.1 ∈ S ∧ t.2.2.2 ∈ S ∧
        t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2 ∧ t.1 + t.2.2.2 = t.2.1 + t.2.2.1 := by
  simp only [fourQuadruples, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, and_assoc]

private lemma fourQuadruples_eq_empty_of_isSidon (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) :
    fourQuadruples S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨ha, hc, hd, hb, hac, hcd, hdb, hsum⟩ := mem_fourQuadruples.mp ht
  rcases hS t.1 ha t.2.1 hc t.2.2.2 hb t.2.2.1 hd hsum with h | h <;> omega

private lemma no_nontrivial_sum_of_empty (S : Finset ℕ)
    (h3 : threeAPs S = ∅) (h4 : fourQuadruples S = ∅)
    {x y z w : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hw : w ∈ S)
    (hzw : z ≤ w) (hxz : x < z) (hsum : x + y = z + w) : False := by
  have hwy : w < y := by omega
  rcases eq_or_lt_of_le hzw with rfl | hlt
  · have hmem : (x, z, y) ∈ threeAPs S :=
      mem_threeAPs.mpr ⟨hx, hz, hy, hxz, hwy, by dsimp only; omega⟩
    rw [h3] at hmem
    exact Finset.notMem_empty _ hmem
  · have hmem : (x, z, w, y) ∈ fourQuadruples S :=
      mem_fourQuadruples.mpr ⟨hx, hz, hw, hy, hxz, hlt, hwy, hsum⟩
    rw [h4] at hmem
    exact Finset.notMem_empty _ hmem

/-- A finite set without 3-APs or 4-distinct additive quadruples is a Sidon set. -/
private lemma isSidon_of_no_threeAPs_fourQuadruples (S : Finset ℕ)
    (h3 : threeAPs S = ∅) (h4 : fourQuadruples S = ∅) : IsSidon (S : Set ℕ) := by
  intro a ha u hu b hb v hv hsum
  by_contra hnot
  have hne : a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v :=
    ⟨fun h ↦ hnot (Or.inl ⟨h, by omega⟩), fun h ↦ hnot (Or.inr ⟨h, by omega⟩),
     fun h ↦ hnot (Or.inr ⟨by omega, h⟩), fun h ↦ hnot (Or.inl ⟨by omega, h⟩)⟩
  rcases le_total a b with hab | hba <;> rcases le_total u v with huv | hvu
  · rcases lt_or_gt_of_ne hne.1 with h | h
    · exact no_nontrivial_sum_of_empty S h3 h4 ha hb hu hv huv h hsum
    · exact no_nontrivial_sum_of_empty S h3 h4 hu hv ha hb hab h hsum.symm
  · rcases lt_or_gt_of_ne hne.2.1 with h | h
    · exact no_nontrivial_sum_of_empty S h3 h4 ha hb hv hu hvu h (by omega)
    · exact no_nontrivial_sum_of_empty S h3 h4 hv hu ha hb hab h (by omega)
  · rcases lt_or_gt_of_ne hne.2.2.1 with h | h
    · exact no_nontrivial_sum_of_empty S h3 h4 hb ha hu hv huv h (by omega)
    · exact no_nontrivial_sum_of_empty S h3 h4 hu hv hb ha hba h (by omega)
  · rcases lt_or_gt_of_ne hne.2.2.2 with h | h
    · exact no_nontrivial_sum_of_empty S h3 h4 hb ha hv hu hvu h (by omega)
    · exact no_nontrivial_sum_of_empty S h3 h4 hv hu hb ha hba h (by omega)

/-- Deleting one element from each conflict pair, 3-AP, and 4-quadruple yields a clean Sidon subset. -/
private lemma delete_conflicts_and_quadruples (U D : Finset ℕ) :
    ∃ T ⊆ U, IsSidon (T : Set ℕ) ∧ Disjoint (positiveDifferences T) D ∧
      U.card ≤ T.card + (conflictPairs U D).card + (threeAPs U).card + (fourQuadruples U).card := by
  classical
  let d1 := (conflictPairs U D).image Prod.fst
  let d2 := (threeAPs U).image fun t ↦ t.2.2
  let d3 := (fourQuadruples U).image fun t ↦ t.2.2.2
  let drop := (d1 ∪ d2) ∪ d3
  have hsub : drop ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx12 | hx3
    · rcases Finset.mem_union.mp hx12 with hx1 | hx2
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx1
        exact (mem_conflictPairs.mp hp).1
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx2
        exact (mem_threeAPs.mp ht).2.2.1
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx3
      exact (mem_fourQuadruples.mp ht).2.2.2.1
  have hdrop : drop.card ≤
      (conflictPairs U D).card + (threeAPs U).card + (fourQuadruples U).card := by
    calc
      drop.card ≤ (d1 ∪ d2).card + d3.card := Finset.card_union_le _ _
      _ ≤ (d1.card + d2.card) + d3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
        Finset.card_image_le
  let T := U \ drop
  have h3 : threeAPs T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ha, hc, hb, hac, hcb, hsum⟩ := mem_threeAPs.mp ht
    obtain ⟨haU, _⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hcU, _⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨hbU, hbDrop⟩ := Finset.mem_sdiff.mp hb
    apply hbDrop
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨t, mem_threeAPs.mpr ⟨haU, hcU, hbU, hac, hcb, hsum⟩, rfl⟩))
  have h4 : fourQuadruples T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ha, hc, hd, hb, hac, hcd, hdb, hsum⟩ := mem_fourQuadruples.mp ht
    obtain ⟨haU, _⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hcU, _⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨hdU, _⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨hbU, hbDrop⟩ := Finset.mem_sdiff.mp hb
    apply hbDrop
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨t, mem_fourQuadruples.mpr
        ⟨haU, hcU, hdU, hbU, hac, hcd, hdb, hsum⟩, rfl⟩)
  refine ⟨T, Finset.sdiff_subset, isSidon_of_no_threeAPs_fourQuadruples T h3 h4,
    Finset.disjoint_left.mpr ?_, ?_⟩
  · intro u hu huD
    obtain ⟨a, ha, b, hb, hba, rfl⟩ := mem_positiveDifferences.mp hu
    obtain ⟨haU, haDrop⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hbU, _⟩ := Finset.mem_sdiff.mp hb
    apply haDrop
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(a, b), mem_conflictPairs.mpr ⟨haU, hbU, hba, huD⟩, rfl⟩))
  · rw [Finset.card_sdiff_of_subset hsub]
    omega

/-- Number of functions V → Fin q that vanish on a given finset A ⊆ V. -/
private lemma card_fun_zero_on {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 0 < q) (A : Finset V) :
    ((Finset.univ : Finset (V → Fin q)).filter fun f ↦ ∀ v ∈ A, f v = ⟨0, hq⟩).card =
      q ^ (Fintype.card V - A.card) := by
  classical
  let e : {f : V → Fin q // ∀ v ∈ A, f v = ⟨0, hq⟩} ≃ ({v : V // v ∉ A} → Fin q) := {
    toFun := fun f v ↦ f.1 v.1
    invFun := fun g ↦ ⟨fun v ↦ if hv : v ∈ A then ⟨0, hq⟩ else g ⟨v, hv⟩,
      fun v hv ↦ by simp [hv]⟩
    left_inv := fun f ↦ by
      ext v
      by_cases hv : v ∈ A
      · simp [hv, f.2 v hv]
      · simp [hv]
    right_inv := fun g ↦ by
      ext v
      simp [v.2] }
  have h1 : ((Finset.univ : Finset (V → Fin q)).filter fun f ↦ ∀ v ∈ A, f v = ⟨0, hq⟩).card =
      Fintype.card {f : V → Fin q // ∀ v ∈ A, f v = ⟨0, hq⟩} := by
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_subtype_compl, Fintype.card_coe]

/-- Finitary alteration: subsample S by a random coloring S → Fin q and delete remaining
conflict pairs, 3-APs, and 4-quadruples. -/
private lemma alteration_sidon_avoiding (S D : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    ∃ T ⊆ S, IsSidon (T : Set ℕ) ∧ Disjoint (positiveDifferences T) D ∧
      q ^ 3 * S.card ≤
        q ^ 4 * T.card + q ^ 2 * (conflictPairs S D).card +
          q * (threeAPs S).card + (fourQuadruples S).card := by
  classical
  let V := {x : ℕ // x ∈ S}
  let zero : Fin q := ⟨0, hq⟩
  let U (f : V → Fin q) : Finset ℕ :=
    (Finset.univ.filter fun v : V ↦ f v = zero).map (Function.Embedding.subtype fun x ↦ x ∈ S)
  have hU_sub : ∀ f, U f ⊆ S := by
    intro f x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hx
    exact v.2
  have hmemU : ∀ (f : V → Fin q) (x : ℕ) (hx : x ∈ S), x ∈ U f ↔ f ⟨x, hx⟩ = zero := by
    intro f x hx
    simp only [U, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
      exact hfy
    · intro hfx
      exact ⟨⟨x, hx⟩, hfx, rfl⟩
  have hcardV : Fintype.card V = S.card := Fintype.card_coe S
  have hcardF : (Finset.univ : Finset (V → Fin q)).card = q ^ S.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcardV]
  have hcount_set (A : Finset V) (k : ℕ) (hA : A.card = k) (hk : k ≤ 4) :
      q ^ 4 * ((Finset.univ : Finset (V → Fin q)).filter fun f ↦ ∀ v ∈ A, f v = zero).card =
        q ^ (4 - k) * q ^ S.card := by
    have hle : k ≤ S.card := by
      rw [← hcardV, ← hA]
      exact Finset.card_le_univ A
    rw [card_fun_zero_on q hq A, hcardV, hA, ← pow_add, ← pow_add]
    congr 1
    omega
  have hsumU : q ^ 4 * ∑ f : V → Fin q, (U f).card = q ^ 3 * S.card * q ^ S.card := by
    have h1 : ∀ f : V → Fin q, (U f).card = ∑ v : V, if f v = zero then 1 else 0 := by
      intro f
      rw [Finset.card_map, Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    have hterm : ∀ v : V, q ^ 4 * ∑ f : V → Fin q, (if f v = zero then 1 else 0) =
        q ^ 3 * q ^ S.card := by
      intro v
      rw [← Finset.card_filter]
      have hfilt : (Finset.univ.filter fun f : V → Fin q ↦ f v = zero) =
          (Finset.univ.filter fun f : V → Fin q ↦ ∀ w ∈ ({v} : Finset V), f w = zero) := by
        ext f
        simp
      rw [hfilt]
      exact hcount_set {v} 1 (Finset.card_singleton v) (by decide)
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, hcardV]
    ring
  have hsumE : q ^ 4 * ∑ f : V → Fin q, (conflictPairs (U f) D).card =
      q ^ 2 * (conflictPairs S D).card * q ^ S.card := by
    have h1 : ∀ f : V → Fin q, (conflictPairs (U f) D).card =
        ∑ p ∈ conflictPairs S D, if p ∈ conflictPairs (U f) D then 1 else 0 := by
      intro f
      rw [← Finset.card_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter, mem_conflictPairs]
      exact ⟨fun h ↦ ⟨⟨hU_sub f h.1, hU_sub f h.2.1, h.2.2⟩, h⟩, And.right⟩
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    have hterm : ∀ p ∈ conflictPairs S D,
        q ^ 4 * ∑ f : V → Fin q, (if p ∈ conflictPairs (U f) D then 1 else 0) =
          q ^ 2 * q ^ S.card := by
      intro p hp
      obtain ⟨ha, hb, hba, hD⟩ := mem_conflictPairs.mp hp
      let va : V := ⟨p.1, ha⟩
      let vb : V := ⟨p.2, hb⟩
      have hne : va ≠ vb := fun h ↦ hba.ne (congrArg Subtype.val h).symm
      rw [← Finset.card_filter]
      have hfilt : (Finset.univ.filter fun f : V → Fin q ↦ p ∈ conflictPairs (U f) D) =
          (Finset.univ.filter fun f : V → Fin q ↦ ∀ w ∈ ({va, vb} : Finset V), f w = zero) := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_conflictPairs,
          Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
        rw [hmemU f p.1 ha, hmemU f p.2 hb]
        exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, hba, hD⟩⟩
      rw [hfilt]
      exact hcount_set {va, vb} 2 (Finset.card_pair hne) (by decide)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const]
    ring
  have hsum3 : q ^ 4 * ∑ f : V → Fin q, (threeAPs (U f)).card =
      q * (threeAPs S).card * q ^ S.card := by
    have h1 : ∀ f : V → Fin q, (threeAPs (U f)).card =
        ∑ t ∈ threeAPs S, if t ∈ threeAPs (U f) then 1 else 0 := by
      intro f
      rw [← Finset.card_filter]
      congr 1
      ext t
      simp only [Finset.mem_filter, mem_threeAPs]
      exact ⟨fun h ↦ ⟨⟨hU_sub f h.1, hU_sub f h.2.1, hU_sub f h.2.2.1, h.2.2.2⟩, h⟩, And.right⟩
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    have hterm : ∀ t ∈ threeAPs S,
        q ^ 4 * ∑ f : V → Fin q, (if t ∈ threeAPs (U f) then 1 else 0) =
          q * q ^ S.card := by
      intro t ht
      obtain ⟨ha, hc, hb, hac, hcb, hsum⟩ := mem_threeAPs.mp ht
      let va : V := ⟨t.1, ha⟩
      let vc : V := ⟨t.2.1, hc⟩
      let vb : V := ⟨t.2.2, hb⟩
      have hcardA : ({va, vc, vb} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · intro h; exact hcb.ne (congrArg Subtype.val h)
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h ↦ hac.ne (congrArg Subtype.val h),
            fun h ↦ (hac.trans hcb).ne (congrArg Subtype.val h)⟩
      rw [← Finset.card_filter]
      have hfilt : (Finset.univ.filter fun f : V → Fin q ↦ t ∈ threeAPs (U f)) =
          (Finset.univ.filter fun f : V → Fin q ↦
            ∀ w ∈ ({va, vc, vb} : Finset V), f w = zero) := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_threeAPs,
          Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
        rw [hmemU f t.1 ha, hmemU f t.2.1 hc, hmemU f t.2.2 hb]
        exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2, hac, hcb, hsum⟩⟩
      rw [hfilt]
      simpa only [show 4 - 3 = 1 by decide, pow_one] using hcount_set {va, vc, vb} 3 hcardA (by decide)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const]
    ring
  have hsum4 : q ^ 4 * ∑ f : V → Fin q, (fourQuadruples (U f)).card =
      (fourQuadruples S).card * q ^ S.card := by
    have h1 : ∀ f : V → Fin q, (fourQuadruples (U f)).card =
        ∑ t ∈ fourQuadruples S, if t ∈ fourQuadruples (U f) then 1 else 0 := by
      intro f
      rw [← Finset.card_filter]
      congr 1
      ext t
      simp only [Finset.mem_filter, mem_fourQuadruples]
      exact ⟨fun h ↦ ⟨⟨hU_sub f h.1, hU_sub f h.2.1, hU_sub f h.2.2.1,
        hU_sub f h.2.2.2.1, h.2.2.2.2⟩, h⟩, And.right⟩
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    have hterm : ∀ t ∈ fourQuadruples S,
        q ^ 4 * ∑ f : V → Fin q, (if t ∈ fourQuadruples (U f) then 1 else 0) =
          q ^ S.card := by
      intro t ht
      obtain ⟨ha, hc, hd, hb, hac, hcd, hdb, hsum⟩ := mem_fourQuadruples.mp ht
      let va : V := ⟨t.1, ha⟩
      let vc : V := ⟨t.2.1, hc⟩
      let vd : V := ⟨t.2.2.1, hd⟩
      let vb : V := ⟨t.2.2.2, hb⟩
      have hcardA : ({va, vc, vd, vb} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
        · intro h; exact hdb.ne (congrArg Subtype.val h)
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h ↦ hcd.ne (congrArg Subtype.val h),
            fun h ↦ (hcd.trans hdb).ne (congrArg Subtype.val h)⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h ↦ hac.ne (congrArg Subtype.val h),
            fun h ↦ (hac.trans hcd).ne (congrArg Subtype.val h),
            fun h ↦ ((hac.trans hcd).trans hdb).ne (congrArg Subtype.val h)⟩
      rw [← Finset.card_filter]
      have hfilt : (Finset.univ.filter fun f : V → Fin q ↦ t ∈ fourQuadruples (U f)) =
          (Finset.univ.filter fun f : V → Fin q ↦
            ∀ w ∈ ({va, vc, vd, vb} : Finset V), f w = zero) := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_fourQuadruples,
          Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
        rw [hmemU f t.1 ha, hmemU f t.2.1 hc, hmemU f t.2.2.1 hd, hmemU f t.2.2.2 hb]
        exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩,
          fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hac, hcd, hdb, hsum⟩⟩
      rw [hfilt]
      simpa only [show 4 - 4 = 0 by decide, pow_zero, one_mul] using
        hcount_set {va, vc, vd, vb} 4 hcardA (by decide)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const]
    ring
  choose T hTsub hTSid hTdisj hTcard using fun f ↦ delete_conflicts_and_quadruples (U f) D
  have htot : q ^ 3 * S.card * q ^ S.card ≤
      q ^ 4 * (∑ f : V → Fin q, (T f).card) +
        (q ^ 2 * (conflictPairs S D).card + q * (threeAPs S).card +
          (fourQuadruples S).card) * q ^ S.card := by
    have hsum_le : ∑ f : V → Fin q, (U f).card ≤
        ∑ f : V → Fin q, ((T f).card + (conflictPairs (U f) D).card +
          (threeAPs (U f)).card + (fourQuadruples (U f)).card) :=
      Finset.sum_le_sum fun f _ ↦ hTcard f
    have hmul := Nat.mul_le_mul_left (q ^ 4) hsum_le
    simp only [Finset.sum_add_distrib, mul_add] at hmul
    rw [hsumU, hsumE, hsum3, hsum4] at hmul
    linarith only [hmul]
  have hex : ∃ f : V → Fin q,
      q ^ 3 * S.card ≤
        q ^ 4 * (T f).card + q ^ 2 * (conflictPairs S D).card +
          q * (threeAPs S).card + (fourQuadruples S).card := by
    by_contra! hall
    have hnonempty : (Finset.univ : Finset (V → Fin q)).Nonempty :=
      ⟨fun _ ↦ zero, Finset.mem_univ _⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hnonempty fun f _ ↦ hall f
    simp only [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, hcardF, smul_eq_mul] at hlt
    linarith only [htot, hlt]
  obtain ⟨f, hf⟩ := hex
  exact ⟨T f, (hTsub f).trans (hU_sub f), hTSid f, hTdisj f, hf⟩

private lemma positiveDifferences_image_add (S : Finset ℕ) (t : ℕ) :
    positiveDifferences (S.image (· + t)) = positiveDifferences S := by
  ext u
  simp only [mem_positiveDifferences, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hlt, rfl⟩
    exact ⟨a, ha, b, hb, by omega, by omega⟩
  · rintro ⟨a, ha, b, hb, hlt, rfl⟩
    exact ⟨a + t, ⟨a, ha, rfl⟩, b + t, ⟨b, hb, rfl⟩, by omega, by omega⟩

private lemma isSidon_image_add (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (t : ℕ) :
    IsSidon ((S.image (· + t) : Finset ℕ) : Set ℕ) := by
  intro x hx u hu y hy v hv hsum
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
  rcases hS a ha c hc b hb d hd (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

private lemma positiveDifferences_image_sub (S : Finset ℕ) (t : ℕ) (hS : ∀ x ∈ S, t ≤ x) :
    positiveDifferences (S.image (· - t)) = positiveDifferences S := by
  ext u
  simp only [mem_positiveDifferences, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hlt, rfl⟩
    have ha' := hS a ha
    have hb' := hS b hb
    exact ⟨a, ha, b, hb, by omega, by omega⟩
  · rintro ⟨a, ha, b, hb, hlt, rfl⟩
    have ha' := hS a ha
    have hb' := hS b hb
    exact ⟨a - t, ⟨a, ha, rfl⟩, b - t, ⟨b, hb, rfl⟩, by omega, by omega⟩

private lemma isSidon_image_sub (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (t : ℕ)
    (hle : ∀ x ∈ S, t ≤ x) :
    IsSidon ((S.image (· - t) : Finset ℕ) : Set ℕ) := by
  intro x hx u hu y hy v hv hsum
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
  have ha' := hle a ha
  have hc' := hle c hc
  have hb' := hle b hb
  have hd' := hle d hd
  rcases hS a ha c hc b hb d hd (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

private def earlierBlockDifferences (B : ℕ → Finset ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.range j).biUnion fun i ↦ positiveDifferences (B i)

/-- Approximate Sidon blocks in [0, 2^j) with polynomial budgets on cross-block conflict
pairs, 3-APs, and 4-element additive quadruples per element. -/
private def ApproxDyadicSidon : Prop :=
  ∃ d k J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.range (2 ^ j)) ∧
    ∀ j, J ≤ j → j ≤ N →
      2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) ∧
      (conflictPairs (B j) (earlierBlockDifferences B j)).card ≤ (B j).card * (j + 1) ^ k ∧
      (threeAPs (B j)).card ≤ (B j).card * (j + 1) ^ (2 * k) ∧
      (fourQuadruples (B j)).card ≤ (B j).card * (j + 1) ^ (3 * k)

/-- Finitary alteration turns approximate Sidon blocks in [0, 2^j) into exact nearby-disjoint
Sidon blocks in [2^j, 2^(j+1)). -/
private lemma nearby_of_approx_dyadic_blocks (h : ApproxDyadicSidon) : NearbyDyadicSidon := by
  obtain ⟨d, k, J, hB⟩ := h
  refine ⟨d + k + 4, max J 1, fun N ↦ ?_⟩
  obtain ⟨B, hrange, hbounds⟩ := hB N
  choose T hTsub hTSid hTdisj hTcard using fun j ↦
    alteration_sidon_avoiding (B j) (earlierBlockDifferences B j) ((j + 1) ^ (k + 2)) (by positivity)
  let C (j : ℕ) : Finset ℕ := (T j).image (· + 2 ^ j)
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have ha' := Finset.mem_range.mp (hrange j (hTsub j ha))
    rw [Finset.mem_Ico, pow_succ]
    omega
  · intro j a ha b hb u hu v hv hs
    exact isSidon_image_add (T j) (hTSid j) (2 ^ j) a ha u hu b hb v hv hs
  · intro j hj hjN
    obtain ⟨hdense, hE, h3, h4⟩ := hbounds j ((le_max_left _ _).trans hj) hjN
    have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
    let r := j + 1
    let q := r ^ (k + 2)
    let M := (B j).card
    have hr2 : 2 ≤ r := by dsimp [r]; omega
    have h4r : 4 ≤ r ^ 2 := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left hr2 2)
    have hq_ge : 4 * r ^ k ≤ q := by
      dsimp [q]
      rw [show k + 2 = 2 + k by omega, pow_add]
      exact Nat.mul_le_mul_right _ h4r
    have hq_pos : 0 < q := by dsimp [q, r]; positivity
    have hb1 : 4 * (q ^ 2 * (conflictPairs (B j) (earlierBlockDifferences B j)).card) ≤
        q ^ 3 * M := by
      calc
        _ ≤ 4 * (q ^ 2 * (M * r ^ k)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hE)
        _ = q ^ 2 * (4 * r ^ k) * M := by ring
        _ ≤ q ^ 2 * q * M := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq_ge)
        _ = _ := by ring
    have hb2 : 4 * (q * (threeAPs (B j)).card) ≤ q ^ 3 * M := by
      have hq2 : 4 * r ^ (2 * k) ≤ q ^ 2 := by
        calc
          4 * r ^ (2 * k) ≤ 16 * r ^ (2 * k) := Nat.mul_le_mul_right _ (by decide)
          _ = (4 * r ^ k) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm k 2]; norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq_ge 2
      calc
        _ ≤ 4 * (q * (M * r ^ (2 * k))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
        _ = q * (4 * r ^ (2 * k)) * M := by ring
        _ ≤ q * q ^ 2 * M := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq2)
        _ = _ := by ring
    have hb3 : 4 * (fourQuadruples (B j)).card ≤ q ^ 3 * M := by
      have hq3 : 4 * r ^ (3 * k) ≤ q ^ 3 := by
        calc
          4 * r ^ (3 * k) ≤ 64 * r ^ (3 * k) := Nat.mul_le_mul_right _ (by decide)
          _ = (4 * r ^ k) ^ 3 := by rw [mul_pow, ← pow_mul, mul_comm k 3]; norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq_ge 3
      calc
        _ ≤ 4 * (M * r ^ (3 * k)) := Nat.mul_le_mul_left _ h4
        _ = (4 * r ^ (3 * k)) * M := by ring
        _ ≤ q ^ 3 * M := Nat.mul_le_mul_right _ hq3
    have hmain : q ^ 3 * M ≤ 4 * q ^ 4 * (T j).card := by
      have hcard4 := Nat.mul_le_mul_left 4 (hTcard j)
      change 4 * (q ^ 3 * M) ≤
        4 * (q ^ 4 * (T j).card + q ^ 2 * (conflictPairs (B j) (earlierBlockDifferences B j)).card +
          q * (threeAPs (B j)).card + (fourQuadruples (B j)).card) at hcard4
      linarith only [hcard4, hb1, hb2, hb3]
    have hM_le : M ≤ (T j).card * r ^ (k + 4) := by
      have hstep : M ≤ 4 * q * (T j).card := by
        apply Nat.le_of_mul_le_mul_left _ (pow_pos hq_pos 3)
        calc
          q ^ 3 * M ≤ 4 * q ^ 4 * (T j).card := hmain
          _ = q ^ 3 * (4 * q * (T j).card) := by ring
      calc
        M ≤ (4 * q) * (T j).card := hstep
        _ ≤ (r ^ 2 * q) * (T j).card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h4r)
        _ = (T j).card * r ^ (k + 4) := by
          dsimp [q]
          rw [← pow_add, show 2 + (k + 2) = k + 4 by omega, mul_comm]
    have hCcard : (C j).card = (T j).card :=
      Finset.card_image_of_injective _ (add_left_injective (2 ^ j))
    rw [hCcard]
    calc
      2 ^ j ≤ M ^ 2 * r ^ (2 * (d + 1)) := hdense
      _ ≤ ((T j).card * r ^ (k + 4)) ^ 2 * r ^ (2 * (d + 1)) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM_le 2)
      _ = (T j).card ^ 2 * r ^ (2 * (d + k + 4 + 1)) := by
        rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega
  · intro i j _ hij a ha b hb u hu v hv hba hvu heq
    have hmem_i : a - b ∈ positiveDifferences (T i) := by
      rw [← positiveDifferences_image_add (T i) (2 ^ i)]
      exact mem_positiveDifferences.mpr ⟨a, ha, b, hb, hba, rfl⟩
    have hmem_j : u - v ∈ positiveDifferences (T j) := by
      rw [← positiveDifferences_image_add (T j) (2 ^ j)]
      exact mem_positiveDifferences.mpr ⟨u, hu, v, hv, hvu, rfl⟩
    have hmem_B : u - v ∈ earlierBlockDifferences B j := by
      rw [← heq]
      obtain ⟨x, hx, y, hy, hyx, hxy⟩ := mem_positiveDifferences.mp hmem_i
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hij,
        mem_positiveDifferences.mpr ⟨x, hTsub i hx, y, hTsub i hy, hyx, hxy⟩⟩
    exact Finset.disjoint_left.mp (hTdisj j) hmem_j hmem_B

/-- Sparse Sidon blocks immediately give approximate Sidon blocks by shifting down by 2^j. -/
private lemma approx_of_sparse_dyadic_blocks (h : SparseDyadicSidon) : ApproxDyadicSidon := by
  obtain ⟨d, k, J, hB⟩ := h
  refine ⟨d, k, J, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hSidon, hcounts⟩ := hB N
  let A (j : ℕ) : Finset ℕ := (B j).image (· - 2 ^ j)
  have hge : ∀ j, ∀ x ∈ B j, 2 ^ j ≤ x := fun j x hx ↦ (Finset.mem_Ico.mp (hpos j hx)).1
  have hdiff : ∀ j, positiveDifferences (A j) = positiveDifferences (B j) := fun j ↦
    positiveDifferences_image_sub (B j) (2 ^ j) (hge j)
  have hASid : ∀ j, IsSidon (A j : Set ℕ) := fun j ↦
    isSidon_image_sub (B j) (hSidon j) (2 ^ j) (hge j)
  have hAcard : ∀ j, (A j).card = (B j).card := by
    intro j
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := hge j x hx
    have hy' := hge j y hy
    dsimp only at hxy
    omega
  refine ⟨A, ?_, ?_⟩
  · intro j x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have htop := (Finset.mem_Ico.mp (hpos j ha)).2
    rw [pow_succ] at htop
    exact Finset.mem_range.mpr (by omega)
  · intro j hj hjN
    obtain ⟨hdense, hbudget⟩ := hcounts j hj hjN
    have hE_eq : earlierBlockDifferences A j = earlierBlockDifferences B j := by
      ext u
      simp only [earlierBlockDifferences, Finset.mem_biUnion, hdiff]
    refine ⟨by simpa only [hAcard j] using hdense, ?_, ?_, ?_⟩
    · calc
        (conflictPairs (A j) (earlierBlockDifferences A j)).card
            ≤ (positiveDifferences (A j) ∩ earlierBlockDifferences A j).card :=
          card_conflictPairs_le_of_isSidon (A j) _ (hASid j)
        _ = (earlierDifferenceConflicts B j).card := by
          rw [hdiff j, hE_eq]; rfl
        _ ≤ (B j).card * (j + 1) ^ k := by omega
        _ = (A j).card * (j + 1) ^ k := by rw [hAcard j]
    · rw [threeAPs_eq_empty_of_isSidon (A j) (hASid j), Finset.card_empty]
      exact Nat.zero_le _
    · rw [fourQuadruples_eq_empty_of_isSidon (A j) (hASid j), Finset.card_empty]
      exact Nat.zero_le _

/-- Ordered pairs of positive differences matching between two blocks A and B. -/
private def crossDifferenceMatches (A B : Finset ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((A.product A).product (B.product B)).filter fun q ↦
    q.1.2 < q.1.1 ∧ q.2.2 < q.2.1 ∧ q.1.1 - q.1.2 = q.2.1 - q.2.2

/-- Conflict pairs in B against positiveDifferences A are bounded by cross-block matches. -/
private lemma card_conflictPairs_le_crossDifferenceMatches (A B : Finset ℕ) :
    (conflictPairs B (positiveDifferences A)).card ≤ (crossDifferenceMatches A B).card := by
  classical
  have hex : ∀ p : ℕ × ℕ, p ∈ conflictPairs B (positiveDifferences A) →
      ∃ q : ℕ × ℕ, q.1 ∈ A ∧ q.2 ∈ A ∧ q.2 < q.1 ∧ q.1 - q.2 = p.1 - p.2 := by
    intro p hp
    obtain ⟨a, ha, b, hb, hba, heq⟩ := mem_positiveDifferences.mp (mem_conflictPairs.mp hp).2.2.2
    exact ⟨(a, b), ha, hb, hba, heq⟩
  let witness (p : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
    if hp : p ∈ conflictPairs B (positiveDifferences A) then (Classical.choose (hex p hp), p)
    else ((0, 0), p)
  apply Finset.card_le_card_of_injOn witness
  · intro p hp
    have hp' : p ∈ conflictPairs B (positiveDifferences A) := Finset.mem_coe.mp hp
    have hspec := Classical.choose_spec (hex p hp')
    obtain ⟨hu, hv, hvu, _⟩ := mem_conflictPairs.mp hp'
    rcases hch : Classical.choose (hex p hp') with ⟨a, b⟩
    rcases p with ⟨u, v⟩
    rw [hch] at hspec
    have hw : witness (u, v) = ((a, b), (u, v)) := by
      simp only [witness, dif_pos hp', hch]
    rw [Finset.mem_coe, hw]
    simp only [crossDifferenceMatches, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨⟨⟨hspec.1, hspec.2.1⟩, ⟨hu, hv⟩⟩, hspec.2.2.1, hvu, hspec.2.2.2⟩
  · intro p _ q _ heq
    have h2 := congrArg Prod.snd heq
    simp only [witness] at h2
    split_ifs at h2 <;> exact h2

/-- Short differences below 2^s plus pairwise cross-additive energy for s < i < j suffice
for the approximate-Sidon conflict budget. -/
private lemma approx_conflict_budget_from_cross_energy
    (B : ℕ → Finset ℕ) (hrange : ∀ j, B j ⊆ Finset.range (2 ^ j))
    (j s d ℓ : ℕ)
    (hshort : (conflictPairs (B j) (Finset.range (2 ^ s))).card ≤ 2 ^ (j / 2) * (j + 1) ^ ℓ)
    (hcross : ∀ i, s < i → i < j →
      (crossDifferenceMatches (B i) (B j)).card ≤ 2 ^ (j / 2) * (j + 1) ^ ℓ)
    (hdense : 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    (conflictPairs (B j) (earlierBlockDifferences B j)).card ≤
      (B j).card * (j + 1) ^ (d + ℓ + 2) := by
  classical
  let I := Finset.Ioo s j
  let R := 2 ^ (j / 2) * (j + 1) ^ ℓ
  have hsub : conflictPairs (B j) (earlierBlockDifferences B j) ⊆
      conflictPairs (B j) (Finset.range (2 ^ s)) ∪
        I.biUnion fun i ↦ conflictPairs (B j) (positiveDifferences (B i)) := by
    intro p hp
    obtain ⟨hu, hv, hvu, hD⟩ := mem_conflictPairs.mp hp
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hD
    by_cases hsi : s < i
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_Ioo.mpr ⟨hsi, Finset.mem_range.mp hi⟩,
          mem_conflictPairs.mpr ⟨hu, hv, hvu, hui⟩⟩)
    · apply Finset.mem_union_left
      obtain ⟨a, ha, b, _, _, hab⟩ := mem_positiveDifferences.mp hui
      have ha' := Finset.mem_range.mp (hrange i ha)
      have hlt : p.1 - p.2 < 2 ^ s := by
        have hpow : (2 : ℕ) ^ i ≤ 2 ^ s := pow_le_pow_right₀ (by decide) (by omega)
        omega
      exact mem_conflictPairs.mpr ⟨hu, hv, hvu, Finset.mem_range.mpr hlt⟩
  have hI : I.card ≤ j := by
    rw [← Finset.card_range j]
    exact Finset.card_le_card fun i hi ↦ Finset.mem_range.mpr (Finset.mem_Ioo.mp hi).2
  have hbi : (I.biUnion fun i ↦ conflictPairs (B j) (positiveDifferences (B i))).card ≤ j * R := by
    refine (Finset.card_biUnion_le_card_mul I _ R ?_).trans (Nat.mul_le_mul_right R hI)
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ioo.mp hi
    exact (card_conflictPairs_le_crossDifferenceMatches (B i) (B j)).trans (hcross i hi1 hi2)
  have hroot : 2 ^ (j / 2) ≤ (B j).card * (j + 1) ^ (d + 1) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    calc
      (2 ^ (j / 2)) ^ 2 = 2 ^ (j / 2 * 2) := by rw [pow_mul]
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by decide) (by omega)
      _ ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) := hdense
      _ = ((B j).card * (j + 1) ^ (d + 1)) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm 2 (d + 1)]
  calc
    (conflictPairs (B j) (earlierBlockDifferences B j)).card
        ≤ (conflictPairs (B j) (Finset.range (2 ^ s)) ∪
            I.biUnion fun i ↦ conflictPairs (B j) (positiveDifferences (B i))).card :=
      Finset.card_le_card hsub
    _ ≤ (conflictPairs (B j) (Finset.range (2 ^ s))).card +
        (I.biUnion fun i ↦ conflictPairs (B j) (positiveDifferences (B i))).card :=
      Finset.card_union_le _ _
    _ ≤ R + j * R := Nat.add_le_add hshort hbi
    _ = 2 ^ (j / 2) * (j + 1) ^ (ℓ + 1) := by dsimp [R]; rw [pow_succ]; ring
    _ ≤ ((B j).card * (j + 1) ^ (d + 1)) * (j + 1) ^ (ℓ + 1) := Nat.mul_le_mul_right _ hroot
    _ = (B j).card * (j + 1) ^ (d + ℓ + 2) := by
      rw [mul_assoc, ← pow_add, show d + 1 + (ℓ + 1) = d + ℓ + 2 by omega]

/-- Standard additive energy E(S) = |{(a, b, c, d) ∈ S^4 : a + b = c + d}|. -/
private def additiveEnergy (S : Finset ℕ) : ℕ :=
  ((S.product (S.product (S.product S))).filter fun t ↦ t.1 + t.2.1 = t.2.2.1 + t.2.2.2).card

/-- Standard cross-additive energy E(A, B) = |{(a, b, u, v) ∈ A^2 × B^2 : a + v = u + b}|. -/
private def crossAdditiveEnergy (A B : Finset ℕ) : ℕ :=
  (((A.product A).product (B.product B)).filter fun q ↦ q.1.1 + q.2.2 = q.2.1 + q.1.2).card

/-- Additive energy bounds both 3-APs and 4-distinct additive quadruples above the trivial count. -/
private lemma additiveEnergy_lower_bound (S : Finset ℕ) :
    (2 * S.card ^ 2 - S.card) + (threeAPs S).card + (fourQuadruples S).card ≤
      additiveEnergy S := by
  classical
  let E := (S.product (S.product (S.product S))).filter fun t ↦ t.1 + t.2.1 = t.2.2.1 + t.2.2.2
  let t1 : Finset (ℕ × ℕ × ℕ × ℕ) := (S.product S).image fun p ↦ (p.1, p.2, p.1, p.2)
  let t2 : Finset (ℕ × ℕ × ℕ × ℕ) :=
    ((S.product S).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ (p.1, p.2, p.2, p.1)
  let t3 : Finset (ℕ × ℕ × ℕ × ℕ) := (threeAPs S).image fun t ↦ (t.1, t.2.2, t.2.1, t.2.1)
  let t4 : Finset (ℕ × ℕ × ℕ × ℕ) :=
    (fourQuadruples S).image fun t ↦ (t.1, t.2.2.2, t.2.1, t.2.2.1)
  have ht1_sub : t1 ⊆ E := by
    intro x hx
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    simp only [E, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨⟨ha, hb, ha, hb⟩, trivial⟩
  have ht2_sub : t2 ⊆ E := by
    intro x hx
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hab, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    simp only [E, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨⟨ha, hb, hb, ha⟩, by omega⟩
  have ht3_sub : t3 ⊆ E := by
    intro x hx
    obtain ⟨⟨a, c, b⟩, ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hc, hb, _, _, hsum⟩ := mem_threeAPs.mp ht
    dsimp only at hsum
    simp only [E, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨⟨ha, hb, hc, hc⟩, by omega⟩
  have ht4_sub : t4 ⊆ E := by
    intro x hx
    obtain ⟨⟨a, c, d, b⟩, ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hc, hd, hb, _, _, _, hsum⟩ := mem_fourQuadruples.mp ht
    simp only [E, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨⟨ha, hb, hc, hd⟩, hsum⟩
  have ht1_card : t1.card = S.card ^ 2 := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.product_eq_sprod, Finset.card_product, pow_two]
    · intro p q h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 h.2.1
  have ht2_card : t2.card = S.card ^ 2 - S.card := by
    rw [Finset.card_image_of_injective]
    · let diag := S.image fun a ↦ (a, a)
      have hsub : diag ⊆ S.product S := by
        intro p hp
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_product.mpr ⟨ha, ha⟩
      have heq : (S.product S).filter (fun p ↦ p.1 ≠ p.2) = (S.product S) \ diag := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.product_eq_sprod,
          Finset.mem_product, diag, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨ha, hb⟩, hne⟩
          exact ⟨⟨ha, hb⟩, by rintro ⟨x, _, rfl, rfl⟩; exact hne rfl⟩
        · rintro ⟨⟨ha, hb⟩, hnd⟩
          exact ⟨⟨ha, hb⟩, fun heq ↦ hnd ⟨a, ha, rfl, heq⟩⟩
      have hdiag : diag.card = S.card :=
        Finset.card_image_of_injective _ fun a b h ↦ (Prod.mk.inj h).1
      rw [heq, Finset.card_sdiff_of_subset hsub, Finset.product_eq_sprod, Finset.card_product,
        pow_two, hdiag]
    · intro p q h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 h.2.1
  have ht3_card : t3.card = (threeAPs S).card := by
    apply Finset.card_image_of_injective
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.2.1 h.2.1)
  have ht4_card : t4.card = (fourQuadruples S).card := by
    apply Finset.card_image_of_injective
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.2.1 (Prod.ext h.2.2.2 h.2.1))
  have hd12 : Disjoint t1 t2 := by
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨⟨c, d⟩, hc, hcd⟩ := Finset.mem_image.mp hx2
    have hne := (Finset.mem_filter.mp hc).2
    simp only [Prod.mk.injEq] at hcd
    exact hne (by omega)
  have hd12_3 : Disjoint (t1 ∪ t2) t3 := by
    apply Finset.disjoint_left.mpr
    intro x hx12 hx3
    obtain ⟨⟨a, c, b⟩, ht, rfl⟩ := Finset.mem_image.mp hx3
    obtain ⟨_, _, _, hac, hcb, _⟩ := mem_threeAPs.mp ht
    dsimp only at hac hcb
    rcases Finset.mem_union.mp hx12 with hx1 | hx2
    · obtain ⟨⟨u, v⟩, _, huv⟩ := Finset.mem_image.mp hx1
      simp only [Prod.mk.injEq] at huv
      omega
    · obtain ⟨⟨u, v⟩, _, huv⟩ := Finset.mem_image.mp hx2
      simp only [Prod.mk.injEq] at huv
      omega
  have hd123_4 : Disjoint ((t1 ∪ t2) ∪ t3) t4 := by
    apply Finset.disjoint_left.mpr
    intro x hx123 hx4
    obtain ⟨⟨a, c, d, b⟩, ht, rfl⟩ := Finset.mem_image.mp hx4
    obtain ⟨_, _, _, _, hac, hcd, hdb, _⟩ := mem_fourQuadruples.mp ht
    dsimp only at hac hcd hdb
    rcases Finset.mem_union.mp hx123 with hx12 | hx3
    · rcases Finset.mem_union.mp hx12 with hx1 | hx2
      · obtain ⟨⟨u, v⟩, _, huv⟩ := Finset.mem_image.mp hx1
        simp only [Prod.mk.injEq] at huv
        omega
      · obtain ⟨⟨u, v⟩, _, huv⟩ := Finset.mem_image.mp hx2
        simp only [Prod.mk.injEq] at huv
        omega
    · obtain ⟨⟨u, v, w⟩, _, huv⟩ := Finset.mem_image.mp hx3
      simp only [Prod.mk.injEq] at huv
      omega
  have hsub : ((t1 ∪ t2) ∪ t3) ∪ t4 ⊆ E :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset ht1_sub ht2_sub) ht3_sub) ht4_sub
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd123_4, Finset.card_union_of_disjoint hd12_3,
    Finset.card_union_of_disjoint hd12, ht1_card, ht2_card, ht3_card, ht4_card] at hle
  have hsq : S.card ≤ S.card ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_self S.card
  change _ ≤ E.card
  omega

/-- A Sidon set has additive energy at most 2 |S|^2. -/
private lemma additiveEnergy_le_of_isSidon (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) :
    additiveEnergy S ≤ 2 * S.card ^ 2 := by
  classical
  let t1 : Finset (ℕ × ℕ × ℕ × ℕ) := (S.product S).image fun p ↦ (p.1, p.2, p.1, p.2)
  let t2 : Finset (ℕ × ℕ × ℕ × ℕ) := (S.product S).image fun p ↦ (p.1, p.2, p.2, p.1)
  have hsub :
      (S.product (S.product (S.product S))).filter (fun t ↦ t.1 + t.2.1 = t.2.2.1 + t.2.2.2) ⊆
        t1 ∪ t2 := by
    intro ⟨a, b, c, d⟩ hx
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hx
    obtain ⟨⟨ha, hb, hc, hd⟩, hsum⟩ := hx
    rcases hS a ha c hc b hb d hd hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)
  calc
    additiveEnergy S ≤ (t1 ∪ t2).card := Finset.card_le_card hsub
    _ ≤ t1.card + t2.card := Finset.card_union_le _ _
    _ ≤ (S.product S).card + (S.product S).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * S.card ^ 2 := by rw [Finset.product_eq_sprod, Finset.card_product, pow_two]; ring

/-- Exact decomposition of cross-additive energy into diagonal and positive difference matches. -/
private lemma crossAdditiveEnergy_eq (A B : Finset ℕ) :
    crossAdditiveEnergy A B = A.card * B.card + 2 * (crossDifferenceMatches A B).card := by
  classical
  let E := ((A.product A).product (B.product B)).filter fun q ↦ q.1.1 + q.2.2 = q.2.1 + q.1.2
  let diag : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (A.product B).image fun p ↦ ((p.1, p.1), (p.2, p.2))
  let pos := crossDifferenceMatches A B
  let neg : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    pos.image fun q ↦ ((q.1.2, q.1.1), (q.2.2, q.2.1))
  have hEq : E = (diag ∪ pos) ∪ neg := by
    ext ⟨⟨a, b⟩, ⟨u, v⟩⟩
    simp only [E, diag, pos, neg, crossDifferenceMatches, Finset.mem_union, Finset.mem_filter,
      Finset.product_eq_sprod, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, ⟨hu, hv⟩⟩, hsum⟩
      rcases lt_trichotomy b a with hba | rfl | hab
      · exact Or.inl (Or.inr ⟨⟨⟨ha, hb⟩, ⟨hu, hv⟩⟩, hba, by omega, by omega⟩)
      · exact Or.inl (Or.inl ⟨(b, u), ⟨hb, hu⟩, ⟨rfl, rfl⟩, rfl, by omega⟩)
      · exact Or.inr ⟨((b, a), (v, u)),
          ⟨⟨⟨hb, ha⟩, ⟨hv, hu⟩⟩, hab, by dsimp only; omega, by dsimp only; omega⟩,
          ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ((⟨⟨x, y⟩, ⟨hx, hy⟩, ⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨⟨ha, hb⟩, ⟨hu, hv⟩⟩, hba, hvu, heq⟩) |
        ⟨⟨⟨x, y⟩, ⟨z, w⟩⟩, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, hyx, hwz, heq⟩, ⟨rfl, rfl⟩, rfl, rfl⟩)
      · exact ⟨⟨⟨hx, hx⟩, ⟨hy, hy⟩⟩, by omega⟩
      · exact ⟨⟨⟨ha, hb⟩, ⟨hu, hv⟩⟩, by omega⟩
      · exact ⟨⟨⟨hy, hx⟩, ⟨hw, hz⟩⟩, by omega⟩
  have hd1 : Disjoint diag pos := by
    apply Finset.disjoint_left.mpr
    intro q hq1 hq2
    obtain ⟨⟨x, y⟩, _, rfl⟩ := Finset.mem_image.mp hq1
    have hlt := (Finset.mem_filter.mp hq2).2.1
    dsimp only at hlt
    omega
  have hd2 : Disjoint (diag ∪ pos) neg := by
    apply Finset.disjoint_left.mpr
    intro q hq12 hq3
    obtain ⟨⟨⟨x, y⟩, ⟨z, w⟩⟩, hm, rfl⟩ := Finset.mem_image.mp hq3
    have hyx := (Finset.mem_filter.mp hm).2.1
    dsimp only at hyx
    rcases Finset.mem_union.mp hq12 with hq1 | hq2
    · obtain ⟨⟨a, b⟩, _, hab⟩ := Finset.mem_image.mp hq1
      simp only [Prod.mk.injEq] at hab
      omega
    · have hlt := (Finset.mem_filter.mp hq2).2.1
      dsimp only at hlt
      omega
  have hdiag : diag.card = A.card * B.card := by
    rw [Finset.card_image_of_injective, Finset.product_eq_sprod, Finset.card_product]
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.1 h.2.1
  have hneg : neg.card = pos.card := by
    apply Finset.card_image_of_injective
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.1.2 h.1.1) (Prod.ext h.2.2 h.2.1)
  change E.card = _
  rw [hEq, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hdiag, hneg]
  ring

/-- Dyadic blocks in [0, 2^j) specified purely by density, near-minimal internal additive
energy, bounded short-difference pairs, and near-minimal pairwise cross-additive energy
across nearby scales j/2 < i < j. -/
private def AdditiveEnergyDyadicBlocks : Prop :=
  ∃ d k J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.range (2 ^ j)) ∧
    ∀ j, J ≤ j → j ≤ N →
      2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) ∧
      additiveEnergy (B j) ≤ 2 * (B j).card ^ 2 + (B j).card * (j + 1) ^ (2 * k) ∧
      (conflictPairs (B j) (Finset.range (2 ^ (j / 2)))).card ≤ 2 ^ (j / 2) * (j + 1) ^ k ∧
      ∀ i, j / 2 < i → i < j →
        crossAdditiveEnergy (B i) (B j) ≤ (B i).card * (B j).card + 2 ^ (j / 2) * (j + 1) ^ k

/-- Near-minimal internal and cross additive energy implies ApproxDyadicSidon. -/
private lemma approx_of_additiveEnergy_dyadic_blocks (h : AdditiveEnergyDyadicBlocks) :
    ApproxDyadicSidon := by
  obtain ⟨d, k, J, hB⟩ := h
  refine ⟨d, d + k + 2, max J 1, fun N ↦ ?_⟩
  obtain ⟨B, hrange, hbounds⟩ := hB N
  refine ⟨B, hrange, fun j hj hjN ↦ ?_⟩
  obtain ⟨hdense, hE, hshort, hcross⟩ := hbounds j ((le_max_left _ _).trans hj) hjN
  have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
  have hmatch : ∀ i, j / 2 < i → i < j →
      (crossDifferenceMatches (B i) (B j)).card ≤ 2 ^ (j / 2) * (j + 1) ^ k := by
    intro i hi hij
    have hce := hcross i hi hij
    rw [crossAdditiveEnergy_eq] at hce
    omega
  have hconf := approx_conflict_budget_from_cross_energy B hrange j (j / 2) d k hshort hmatch hdense
  have hlow := additiveEnergy_lower_bound (B j)
  have hsq : (B j).card ≤ 2 * (B j).card ^ 2 := by
    have h1 : (B j).card ≤ (B j).card ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_self _
    omega
  have hsum34 : (threeAPs (B j)).card + (fourQuadruples (B j)).card ≤
      (B j).card * (j + 1) ^ (2 * (d + k + 2)) := by
    have h1 : (threeAPs (B j)).card + (fourQuadruples (B j)).card ≤
        (B j).card + (B j).card * (j + 1) ^ (2 * k) := by omega
    have hpos_pow : 1 ≤ (j + 1) ^ (2 * k) := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 ≤ (j + 1) ^ (2 * (d + 2)) := by
      have hr : 2 ≤ j + 1 := by omega
      exact hr.trans (Nat.le_self_pow (by omega) (j + 1))
    calc
      (threeAPs (B j)).card + (fourQuadruples (B j)).card
          ≤ (B j).card * (j + 1) ^ (2 * k) + (B j).card * (j + 1) ^ (2 * k) := by
            have := Nat.mul_le_mul_left (B j).card hpos_pow
            omega
      _ = (B j).card * (2 * (j + 1) ^ (2 * k)) := by ring
      _ ≤ (B j).card * ((j + 1) ^ (2 * (d + 2)) * (j + 1) ^ (2 * k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
      _ = (B j).card * (j + 1) ^ (2 * (d + k + 2)) := by
        rw [← pow_add]
        congr 2
        omega
  have hpow23 : (j + 1) ^ (2 * (d + k + 2)) ≤ (j + 1) ^ (3 * (d + k + 2)) :=
    pow_le_pow_right₀ (by omega) (by omega)
  refine ⟨hdense, hconf, ?_, ?_⟩
  · exact (Nat.le_add_right _ _).trans hsum34
  · exact ((Nat.le_add_left _ _).trans hsum34).trans (Nat.mul_le_mul_left _ hpow23)

/-- Nearby-disjoint Sidon blocks automatically satisfy the additive-energy formulation. -/
private lemma additiveEnergy_of_nearby_dyadic_blocks (h : NearbyDyadicSidon) :
    AdditiveEnergyDyadicBlocks := by
  obtain ⟨d, J, hB⟩ := h
  refine ⟨d, 0, J, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hSidon, hcounts, hsep⟩ := hB N
  let A (j : ℕ) : Finset ℕ := (B j).image (· - 2 ^ j)
  have hge : ∀ j, ∀ x ∈ B j, 2 ^ j ≤ x := fun j x hx ↦ (Finset.mem_Ico.mp (hpos j hx)).1
  have hSid : ∀ j, IsSidon (B j : Set ℕ) := fun j a ha u hu b hb v hv hs ↦
    hSidon j a ha b hb u hu v hv hs
  have hASid : ∀ j, IsSidon (A j : Set ℕ) := fun j ↦
    isSidon_image_sub (B j) (hSid j) (2 ^ j) (hge j)
  have hdiff : ∀ j, positiveDifferences (A j) = positiveDifferences (B j) := fun j ↦
    positiveDifferences_image_sub (B j) (2 ^ j) (hge j)
  have hAcard : ∀ j, (A j).card = (B j).card := by
    intro j
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := hge j x hx
    have hy' := hge j y hy
    dsimp only at hxy
    omega
  refine ⟨A, ?_, ?_⟩
  · intro j x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have htop := (Finset.mem_Ico.mp (hpos j ha)).2
    rw [pow_succ] at htop
    exact Finset.mem_range.mpr (by omega)
  · intro j hj hjN
    refine ⟨by simpa only [hAcard j] using hcounts j hj hjN, ?_, ?_, ?_⟩
    · exact (additiveEnergy_le_of_isSidon (A j) (hASid j)).trans (Nat.le_add_right _ _)
    · simp only [pow_zero, mul_one]
      calc
        (conflictPairs (A j) (Finset.range (2 ^ (j / 2)))).card
            ≤ (positiveDifferences (A j) ∩ Finset.range (2 ^ (j / 2))).card :=
          card_conflictPairs_le_of_isSidon (A j) _ (hASid j)
        _ ≤ (Finset.range (2 ^ (j / 2))).card := Finset.card_le_card Finset.inter_subset_right
        _ = 2 ^ (j / 2) := Finset.card_range _
    · intro i hi hij
      have hempty : crossDifferenceMatches (A i) (A j) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ⟨⟨a, b⟩, ⟨u, v⟩⟩ hq
        simp only [crossDifferenceMatches, Finset.mem_filter, Finset.product_eq_sprod,
          Finset.mem_product] at hq
        obtain ⟨⟨⟨ha, hb⟩, ⟨hu, hv⟩⟩, hba, hvu, heq⟩ := hq
        have hmem_i : a - b ∈ positiveDifferences (B i) := by
          rw [← hdiff i]
          exact mem_positiveDifferences.mpr ⟨a, ha, b, hb, hba, rfl⟩
        have hmem_j : u - v ∈ positiveDifferences (B j) := by
          rw [← hdiff j]
          exact mem_positiveDifferences.mpr ⟨u, hu, v, hv, hvu, rfl⟩
        obtain ⟨a', ha', b', hb', hba', heq'⟩ := mem_positiveDifferences.mp hmem_i
        obtain ⟨u', hu', v', hv', hvu', heq''⟩ := mem_positiveDifferences.mp hmem_j
        exact hsep i j (by omega) hij a' ha' b' hb' u' hu' v' hv' hba' hvu'
          (heq'.trans (heq.trans heq''.symm))
      rw [crossAdditiveEnergy_eq, hempty, Finset.card_empty]
      omega

/-- Alteration applied to internal collisions alone. -/
private lemma sidon_subset_of_small_additiveEnergy (S : Finset ℕ) (r k : ℕ) (hr : 2 ≤ r)
    (hE : additiveEnergy S ≤ 2 * S.card ^ 2 + S.card * r ^ (2 * k)) :
    ∃ T ⊆ S, IsSidon (T : Set ℕ) ∧ S.card ≤ T.card * r ^ (k + 2) := by
  obtain ⟨T, hTS, hT, _, hcard⟩ :=
    alteration_sidon_avoiding S ∅ (r ^ (k + 1)) (by positivity)
  refine ⟨T, hTS, hT, ?_⟩
  have hzero : conflictPairs S ∅ = ∅ := by
    ext p
    simp [mem_conflictPairs]
  rw [hzero, Finset.card_empty, mul_zero, add_zero] at hcard
  let q := r ^ (k + 1)
  let M := S.card
  let e := (threeAPs S).card + (fourQuadruples S).card
  have he : e ≤ 2 * (M * r ^ (2 * k)) := by
    have hlow := additiveEnergy_lower_bound S
    have hpow : 1 ≤ r ^ (2 * k) := Nat.one_le_pow _ _ (by omega)
    have hM := Nat.mul_le_mul_left M hpow
    dsimp [e, M] at *
    omega
  have hq2 : 4 * r ^ (2 * k) ≤ q ^ 2 := by
    have h := Nat.pow_le_pow_left hr 2
    norm_num at h
    dsimp [q]
    rw [← pow_mul, show (k + 1) * 2 = 2 + 2 * k by omega, pow_add]
    exact Nat.mul_le_mul_right _ h
  have hq : 0 < q := by dsimp [q]; positivity
  have herrors : 2 * (q * (threeAPs S).card + (fourQuadruples S).card) ≤ q ^ 3 * M := by
    calc
      _ ≤ 2 * (q * e) := by
        dsimp [e]
        apply Nat.mul_le_mul_left
        rw [Nat.mul_add]
        have hfour := Nat.mul_le_mul_right (fourQuadruples S).card (show 1 ≤ q by omega)
        exact Nat.add_le_add_left (by simpa only [one_mul] using hfour) _
      _ ≤ 2 * (q * (2 * (M * r ^ (2 * k)))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ he)
      _ = q * M * (4 * r ^ (2 * k)) := by ring
      _ ≤ q * M * q ^ 2 := Nat.mul_le_mul_left _ hq2
      _ = q ^ 3 * M := by ring
  have hmain : q ^ 3 * M ≤ 2 * (q ^ 4 * T.card) := by
    change q ^ 3 * M ≤ q ^ 4 * T.card + q * (threeAPs S).card + (fourQuadruples S).card at hcard
    omega
  have hcancel : M ≤ 2 * q * T.card := by
    apply Nat.le_of_mul_le_mul_left _ (pow_pos hq 3)
    calc
      q ^ 3 * M ≤ 2 * (q ^ 4 * T.card) := hmain
      _ = q ^ 3 * (2 * q * T.card) := by ring
  calc
    M ≤ 2 * q * T.card := hcancel
    _ ≤ r * q * T.card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr)
    _ = T.card * r ^ (k + 2) := by dsimp [q]; rw [show k + 2 = k + 1 + 1 by omega, pow_succ]; ring

private lemma crossDifferenceMatches_mono {A A' B B' : Finset ℕ}
    (hA : A' ⊆ A) (hB : B' ⊆ B) :
    crossDifferenceMatches A' B' ⊆ crossDifferenceMatches A B := by
  intro ⟨⟨a,b⟩,⟨x,y⟩⟩ h
  simp only [crossDifferenceMatches, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product] at h ⊢
  exact ⟨⟨⟨hA h.1.1.1, hA h.1.1.2⟩, ⟨hB h.1.2.1, hB h.1.2.2⟩⟩, h.2⟩

/-- The energy conditions suffice without a separate bound on short differences. -/
private def DyadicEnergyBounds : Prop :=
  ∃ d k J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.range (2 ^ j)) ∧
    ∀ j, J ≤ j → j ≤ N →
      2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) ∧
      additiveEnergy (B j) ≤ 2 * (B j).card ^ 2 + (B j).card * (j + 1) ^ (2 * k) ∧
      ∀ i, j / 2 < i → i < j →
        crossAdditiveEnergy (B i) (B j) ≤
          (B i).card * (B j).card + 2 ^ (j / 2) * (j + 1) ^ k

/-- Internal energy can be handled first. Sidon blocks have at most one pair per short difference. -/
private lemma additiveEnergy_of_dyadicEnergyBounds (h : DyadicEnergyBounds) :
    AdditiveEnergyDyadicBlocks := by
  classical
  obtain ⟨d, k, J, hB⟩ := h
  refine ⟨d + k + 2, k, max J 1, fun N ↦ ?_⟩
  obtain ⟨B, hrange, hb⟩ := hB N
  have hex : ∀ j, ∃ T ⊆ B j, IsSidon (T : Set ℕ) ∧
      (max J 1 ≤ j → j ≤ N → (B j).card ≤ T.card * (j + 1) ^ (k + 2)) := by
    intro j
    by_cases hj : max J 1 ≤ j ∧ j ≤ N
    · obtain ⟨T, hsub, hsid, hc⟩ := sidon_subset_of_small_additiveEnergy
        (B j) (j + 1) k (by omega) (hb j (by omega) hj.2).2.1
      exact ⟨T, hsub, hsid, fun _ _ ↦ hc⟩
    · exact ⟨∅, Finset.empty_subset _, by simp [IsSidon], fun h₁ h₂ ↦ (hj ⟨h₁,h₂⟩).elim⟩
  choose T hsub hsid hcard using hex
  refine ⟨T, fun j ↦ (hsub j).trans (hrange j), fun j hj hjN ↦ ?_⟩
  obtain ⟨hdense, _, hcross⟩ := hb j (by omega) hjN
  refine ⟨?_, (additiveEnergy_le_of_isSidon _ (hsid j)).trans (Nat.le_add_right _ _), ?_, ?_⟩
  · calc
      2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) := hdense
      _ ≤ ((T j).card * (j + 1) ^ (k + 2)) ^ 2 * (j + 1) ^ (2 * (d + 1)) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (hcard j hj hjN) 2)
      _ = (T j).card ^ 2 * (j + 1) ^ (2 * (d + k + 2 + 1)) := by
        rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega
  · calc
      _ ≤ (positiveDifferences (T j) ∩ Finset.range (2 ^ (j / 2))).card :=
        card_conflictPairs_le_of_isSidon _ _ (hsid j)
      _ ≤ 2 ^ (j / 2) := by
        simpa only [Finset.card_range] using Finset.card_le_card
          (Finset.inter_subset_right (s₁ := positiveDifferences (T j))
            (s₂ := Finset.range (2 ^ (j / 2))))
      _ ≤ 2 ^ (j / 2) * (j + 1) ^ k := Nat.le_mul_of_pos_right _ (by positivity)
  · intro i hi hij
    have h := hcross i hi hij
    have hm := Finset.card_le_card (crossDifferenceMatches_mono (hsub i) (hsub j))
    rw [crossAdditiveEnergy_eq] at h ⊢
    omega

private lemma dyadicEnergyBounds_of_additiveEnergy (h : AdditiveEnergyDyadicBlocks) :
    DyadicEnergyBounds := by
  obtain ⟨d, k, J, hB⟩ := h
  refine ⟨d, k, J, fun N ↦ ?_⟩
  obtain ⟨B, hrange, hb⟩ := hB N
  refine ⟨B, hrange, fun j hj hjN ↦ ?_⟩
  obtain ⟨hd, hE, _, hcross⟩ := hb j hj hjN
  exact ⟨hd, hE, hcross⟩

private def mixedSumFiber (A B : Finset ℕ) (s : ℕ) : Finset (ℕ × ℕ) :=
  (A.product B).filter fun p ↦ p.1 + p.2 = s

private def mixedRepeatPairs (A B : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A.product B).filter fun p ↦ 1 < (mixedSumFiber A B (p.1 + p.2)).card

/-- The mixed sum multiplicity moment, omitting sums with a unique representation. -/
private def mixedMoment (A B : Finset ℕ) : ℕ :=
  ∑ p ∈ mixedRepeatPairs A B, Nat.sqrt (mixedSumFiber A B (p.1 + p.2)).card

private def heavyMixedPairs (A B : Finset ℕ) (R : ℕ) : Finset (ℕ × ℕ) :=
  (A.product B).filter fun p ↦ R ≤ Nat.sqrt (mixedSumFiber A B (p.1 + p.2)).card

private lemma heavyMixedPairs_card_mul_le (A B : Finset ℕ) (R : ℕ) (hR : 2 ≤ R) :
    (heavyMixedPairs A B R).card * R ≤ mixedMoment A B := by
  have hsub : heavyMixedPairs A B R ⊆ mixedRepeatPairs A B := by
    intro p hp
    obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
    have hpow := Nat.le_sqrt.mp hs
    have hfour := Nat.mul_le_mul hR hR
    exact Finset.mem_filter.mpr ⟨hp, by omega⟩
  calc
    _ = ∑ p ∈ heavyMixedPairs A B R, R := by simp
    _ ≤ ∑ p ∈ heavyMixedPairs A B R, Nat.sqrt (mixedSumFiber A B (p.1 + p.2)).card :=
      Finset.sum_le_sum fun p hp ↦ (Finset.mem_filter.mp hp).2
    _ ≤ mixedMoment A B := Finset.sum_le_sum_of_subset hsub

private lemma mixedRepeatPairs_card_le (A B : Finset ℕ) :
    (mixedRepeatPairs A B).card ≤ mixedMoment A B := by
  calc
    _ = ∑ p ∈ mixedRepeatPairs A B, 1 := by simp
    _ ≤ mixedMoment A B := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.le_sqrt.mpr (by have h := (Finset.mem_filter.mp hp).2; omega)

private lemma crossDifferenceMatches_le_of_no_heavy (A B T : Finset ℕ)
    (hT : T ⊆ B) (R : ℕ)
    (hAvoid : ∀ a ∈ A, ∀ v ∈ T, (a, v) ∉ heavyMixedPairs A B R) :
    (crossDifferenceMatches A T).card ≤ mixedMoment A B * R ^ 2 := by
  classical
  let F (p : ℕ × ℕ) := (mixedSumFiber A T (p.1 + p.2)).image fun q ↦ (p, q)
  let P := (mixedRepeatPairs A B).filter fun p ↦ p.2 ∈ T
  have hmap : (crossDifferenceMatches A T).card ≤ (P.biUnion F).card := by
    apply Finset.card_le_card_of_injOn
      (fun q : (ℕ × ℕ) × (ℕ × ℕ) ↦ ((q.1.1, q.2.2), (q.1.2, q.2.1)))
    · intro ⟨⟨a, b⟩, ⟨u, v⟩⟩ hq
      simp only [Finset.mem_coe, crossDifferenceMatches, Finset.mem_filter,
        Finset.product_eq_sprod, Finset.mem_product] at hq
      obtain ⟨⟨⟨ha, hb⟩, ⟨hu, hv⟩⟩, hab, hvu, he⟩ := hq
      have hsum : b + u = a + v := by omega
      have hne : (a, v) ≠ (b, u) := fun h ↦ (Nat.ne_of_gt hab) (congrArg Prod.fst h)
      have hfirst : (a, v) ∈ mixedSumFiber A B (a + v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hT hv⟩, rfl⟩
      have hsecond : (b, u) ∈ mixedSumFiber A B (a + v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, hT hu⟩, hsum⟩
      have hgt : 1 < (mixedSumFiber A B (a + v)).card :=
        Finset.one_lt_card.mpr ⟨_, hfirst, _, hsecond, hne⟩
      have hre : (a, v) ∈ mixedRepeatPairs A B :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hT hv⟩, hgt⟩
      exact Finset.mem_biUnion.mpr ⟨(a, v), Finset.mem_filter.mpr ⟨hre, hv⟩,
        Finset.mem_image.mpr ⟨(b, u),
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, hu⟩, hsum⟩, rfl⟩⟩
    · intro ⟨⟨a,b⟩,⟨u,v⟩⟩ _ ⟨⟨a',b'⟩,⟨u',v'⟩⟩ _ h
      simp_all only [Prod.mk.injEq]
  have hF : ∀ p ∈ P, (F p).card ≤ R ^ 2 := by
    intro ⟨a, v⟩ hp
    obtain ⟨hp', hv⟩ := Finset.mem_filter.mp hp
    have ha := (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).1
    have hs : Nat.sqrt (mixedSumFiber A B (a + v)).card < R := by
      apply Nat.lt_of_not_ge
      intro h
      exact hAvoid a ha v hv (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hT hv⟩, h⟩)
    have hsub : mixedSumFiber A T (a + v) ⊆ mixedSumFiber A B (a + v) := by
      intro q hq
      obtain ⟨hq, hsum⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqa, hqv⟩ := Finset.mem_product.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hqa, hT hqv⟩, hsum⟩
    exact Finset.card_image_le.trans ((Finset.card_le_card hsub).trans (Nat.sqrt_lt'.mp hs).le)
  calc
    _ ≤ (P.biUnion F).card := hmap
    _ ≤ P.card * R ^ 2 := Finset.card_biUnion_le_card_mul P F _ hF
    _ ≤ _ := Nat.mul_le_mul_right _ ((Finset.card_le_card (Finset.filter_subset _ _)).trans
      (mixedRepeatPairs_card_le A B))

/-- A bound on the mixed sum moment of order 3/2 suffices across nearby scales. -/
private def DyadicMixedMomentBounds : Prop :=
  ∃ d k J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.range (2 ^ j)) ∧
    ∀ j, J ≤ j → j ≤ N →
      2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) ∧
      additiveEnergy (B j) ≤ 2 * (B j).card ^ 2 + (B j).card * (j + 1) ^ (2 * k) ∧
      ∀ i, j / 2 < i → i < j →
        mixedMoment (B i) (B j) ≤ 2 ^ (j / 2) * (j + 1) ^ k

private lemma dyadic_energy_count_transfer (j d k M m : ℕ)
    (hcount : 2 ^ j ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1)))
    (hcard : M ≤ m * (j + 1) ^ k) :
    2 ^ j ≤ m ^ 2 * (j + 1) ^ (2 * (d + k + 1)) := by
  calc
    _ ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1)) := hcount
    _ ≤ (m * (j + 1) ^ k) ^ 2 * (j + 1) ^ (2 * (d + 1)) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcard 2)
    _ = _ := by
      rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
      congr 2
      omega

private lemma trim_heavyMixedPairs
    (B : ℕ → Finset ℕ) (j d k : ℕ) (hj : 1 ≤ j)
    (T : Finset ℕ) (hT : T ⊆ B j)
    (hdense : 2 ^ j ≤ T.card ^ 2 * (j + 1) ^ (2 * (d + 1)))
    (hbudget : ∀ i, j / 2 < i → i < j →
      mixedMoment (B i) (B j) ≤ 2 ^ (j / 2) * (j + 1) ^ k) :
    ∃ U ⊆ T, 2 ^ j ≤ U.card ^ 2 * (j + 1) ^ (2 * (d + 2)) ∧
      ∀ i, j / 2 < i → i < j →
        (crossDifferenceMatches (B i) U).card ≤
          2 ^ (j / 2) * (j + 1) ^ (k + 2 * (d + k + 3)) := by
  classical
  let r := j + 1
  let R := r ^ (d + k + 3)
  let Q := 2 ^ (j / 2) * r ^ k
  let I := Finset.Ioo (j / 2) j
  let D (i : ℕ) := (heavyMixedPairs (B i) (B j) R).image Prod.snd
  let F := I.biUnion D
  let U := T \ F
  have hr : 2 ≤ r := by dsimp [r]; omega
  have hR : 2 ≤ R := hr.trans (Nat.le_self_pow (by omega) r)
  have hF : F.card * R ≤ I.card * Q := by
    calc
      _ ≤ (∑ i ∈ I, (D i).card) * R := Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ i ∈ I, (D i).card * R := Finset.sum_mul _ _ _
      _ ≤ ∑ _i ∈ I, Q := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hi₁, hi₂⟩ := Finset.mem_Ioo.mp hi
        exact (Nat.mul_le_mul_right _ Finset.card_image_le).trans
          ((heavyMixedPairs_card_mul_le _ _ R hR).trans (hbudget i hi₁ hi₂))
      _ = I.card * Q := by simp
  have hI : I.card ≤ j := by
    calc
      _ ≤ (Finset.range j).card :=
        Finset.card_le_card fun i hi ↦ Finset.mem_range.mpr (Finset.mem_Ioo.mp hi).2
      _ = j := Finset.card_range _
  have hroot : 2 ^ (j / 2) ≤ T.card * r ^ (d + 1) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    calc
      (2 ^ (j / 2)) ^ 2 = 2 ^ (j / 2 * 2) := by rw [pow_mul]
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by decide) (by omega)
      _ ≤ T.card ^ 2 * r ^ (2 * (d + 1)) := hdense
      _ = (T.card * r ^ (d + 1)) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm 2 (d + 1)]
  have hcost : 2 * F.card ≤ T.card := by
    apply Nat.le_of_mul_le_mul_left _ (show 0 < R by omega)
    calc
      R * (2 * F.card) = 2 * (F.card * R) := by ring
      _ ≤ 2 * (I.card * Q) := Nat.mul_le_mul_left _ hF
      _ ≤ r * (r * Q) := Nat.mul_le_mul hr (Nat.mul_le_mul_right Q (hI.trans (by dsimp [r]; omega)))
      _ = 2 ^ (j / 2) * r ^ (k + 2) := by dsimp [Q]; rw [show k + 2 = k + 1 + 1 by omega, pow_succ, pow_succ]; ring
      _ ≤ (T.card * r ^ (d + 1)) * r ^ (k + 2) := Nat.mul_le_mul_right _ hroot
      _ = R * T.card := by rw [mul_assoc, ← pow_add, show d + 1 + (k + 2) = d + k + 3 by omega, mul_comm]
  have hUT : U ⊆ T := Finset.sdiff_subset
  have hcard : T.card ≤ U.card * r := by
    have hsplit : U.card + (T ∩ F).card = T.card := Finset.card_sdiff_add_card_inter _ _
    have hinter := Finset.card_le_card (Finset.inter_subset_right (s₁ := T) (s₂ := F))
    have htwo : T.card ≤ U.card * 2 := by omega
    exact htwo.trans (Nat.mul_le_mul_left _ hr)
  refine ⟨U, hUT, dyadic_energy_count_transfer j d 1 _ _ hdense (by simpa [r] using hcard), ?_⟩
  intro i hi hij
  have havoid : ∀ a ∈ B i, ∀ v ∈ U, (a, v) ∉ heavyMixedPairs (B i) (B j) R := by
    intro a _ v hv hheavy
    have hiI : i ∈ I := Finset.mem_Ioo.mpr ⟨hi, hij⟩
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_biUnion.mpr ⟨i, hiI, Finset.mem_image.mpr ⟨(a, v), hheavy, rfl⟩⟩)
  calc
    _ ≤ mixedMoment (B i) (B j) * R ^ 2 :=
      crossDifferenceMatches_le_of_no_heavy _ _ _ (hUT.trans hT) R havoid
    _ ≤ Q * R ^ 2 := Nat.mul_le_mul_right _ (hbudget i hi hij)
    _ = _ := by dsimp [Q, R, r]; rw [mul_assoc, ← pow_mul, ← pow_add, mul_comm 2 (d + k + 3)]

/-- Clip heavy mixed sum fibers after extracting Sidon subsets from each block. -/
private lemma dyadicEnergyBounds_of_mixedMoment (h : DyadicMixedMomentBounds) :
    DyadicEnergyBounds := by
  classical
  obtain ⟨d, k, J, hB⟩ := h
  let D := d + k + 2
  let K := k + 2 * (D + k + 3)
  refine ⟨D + 1, K + 1, max J 1, fun N ↦ ?_⟩
  obtain ⟨B, hrange, hb⟩ := hB N
  have hex : ∀ j, ∃ U ⊆ B j, IsSidon (U : Set ℕ) ∧
      (max J 1 ≤ j → j ≤ N →
        2 ^ j ≤ U.card ^ 2 * (j + 1) ^ (2 * (D + 2)) ∧
        ∀ i, j / 2 < i → i < j →
          (crossDifferenceMatches (B i) U).card ≤ 2 ^ (j / 2) * (j + 1) ^ K) := by
    intro j
    by_cases hj : max J 1 ≤ j ∧ j ≤ N
    · obtain ⟨hdense, hE, hmoment⟩ := hb j (by omega) hj.2
      obtain ⟨T, hTB, hT, hcard⟩ :=
        sidon_subset_of_small_additiveEnergy (B j) (j + 1) k (by omega) hE
      have hTdense : 2 ^ j ≤ T.card ^ 2 * (j + 1) ^ (2 * (D + 1)) :=
        dyadic_energy_count_transfer j d (k + 2) _ _ hdense hcard
      obtain ⟨U, hUT, hUdense, hUcross⟩ := trim_heavyMixedPairs B j D k (by omega) T hTB hTdense hmoment
      refine ⟨U, hUT.trans hTB, ?_, fun _ _ ↦ ⟨hUdense, hUcross⟩⟩
      intro a ha b hb c hc e he hsum
      exact hT a (hUT ha) b (hUT hb) c (hUT hc) e (hUT he) hsum
    · exact ⟨∅, Finset.empty_subset _, by simp [IsSidon], fun h₁ h₂ ↦ (hj ⟨h₁, h₂⟩).elim⟩
  choose U hUsub hUsid hU using hex
  refine ⟨U, fun j ↦ (hUsub j).trans (hrange j), fun j hj hjN ↦ ?_⟩
  obtain ⟨hdense, hcross⟩ := hU j hj hjN
  refine ⟨hdense, (additiveEnergy_le_of_isSidon _ (hUsid j)).trans (Nat.le_add_right _ _), ?_⟩
  intro i hi hij
  rw [crossAdditiveEnergy_eq]
  have hmono := Finset.card_le_card (crossDifferenceMatches_mono (hUsub i) (show U j ⊆ U j from fun _ h ↦ h))
  apply Nat.add_le_add_left
  calc
    _ ≤ 2 * (2 ^ (j / 2) * (j + 1) ^ K) :=
      Nat.mul_le_mul_left _ (hmono.trans (hcross i hi hij))
    _ ≤ (j + 1) * (2 ^ (j / 2) * (j + 1) ^ K) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [pow_succ]; ring

/-- Conditioning two different coordinates of a finite product leaves the other coordinates free. -/
private lemma card_two_choice_fiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (i j : ι) (hij : i ≠ j) (a : Fin (q i)) (b : Fin (q j)) :
    ((Finset.univ : Finset (∀ x, Fin (q x))).filter fun f ↦ f i = a ∧ f j = b).card *
      (q i * q j) = Fintype.card (∀ x, Fin (q x)) := by
  classical
  let S : ∀ x, Finset (Fin (q x)) := fun x ↦
    if hi : x = i then {hi.symm ▸ a} else if hj : x = j then {hj.symm ▸ b} else Finset.univ
  have heq : ((Finset.univ : Finset (∀ x, Fin (q x))).filter fun f ↦ f i = a ∧ f j = b) =
      Fintype.piFinset S := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨ha, hb⟩ x
      by_cases hx : x = i
      · subst x
        simpa [S] using ha
      by_cases hx' : x = j
      · subst x
        simpa [S, hij.symm] using hb
      simp [S, hx, hx']
    · intro h
      exact ⟨by simpa [S] using h i, by simpa [S, hij.symm] using h j⟩
  rw [heq, Fintype.card_piFinset, Fintype.card_pi]
  simp only [Fintype.card_fin]
  let R := (Finset.univ.erase i).erase j
  have hj : j ∈ (Finset.univ : Finset ι).erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hS : (∏ x ∈ R, (S x).card) = ∏ x ∈ R, q x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    simp [S, hx'.1, (Finset.mem_erase.mp hx'.2).1]
  rw [← Finset.prod_erase_mul _ (fun x ↦ (S x).card) hi,
    ← Finset.prod_erase_mul _ (fun x ↦ (S x).card) hj,
    ← Finset.prod_erase_mul _ q hi, ← Finset.prod_erase_mul _ q hj]
  change ((∏ x ∈ R, (S x).card) * (S j).card * (S i).card) * (q i * q j) =
    (∏ x ∈ R, q x) * q j * q i
  rw [hS]
  simp [S, hij.symm, mul_comm, mul_left_comm]

/-- A finite set can supply equally sized disjoint choices after dropping its remainder. -/
private lemma balanced_finset_choices (T : Finset ℕ) (q : ℕ) :
    ∃ C : Fin q → Finset ℕ,
      (∀ a, C a ⊆ T ∧ (C a).card = T.card / q) ∧
      ∀ a b, a ≠ b → Disjoint (C a) (C b) := by
  classical
  let m := T.card / q
  obtain ⟨U, hUT, hU⟩ := Finset.exists_subset_card_eq (s := T) (Nat.mul_div_le T.card q)
  let e : U ≃ Fin q × Fin m := (Finset.equivFinOfCardEq hU).trans finProdFinEquiv.symm
  let C (a : Fin q) : Finset ℕ := (Finset.univ : Finset (Fin m)).map
    ⟨fun b ↦ (e.symm (a, b)).1, fun b c h ↦ congrArg Prod.snd (e.symm.injective (Subtype.ext h))⟩
  refine ⟨C, ?_, ?_⟩
  · intro a
    refine ⟨?_, by simp [C, m]⟩
    intro x hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hx
    exact hUT (e.symm (a, b)).2
  · intro a b hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨c, _, hc⟩ := Finset.mem_map.mp hx
    obtain ⟨d, _, hd⟩ := Finset.mem_map.mp hy
    exact hab (congrArg Prod.fst (e.symm.injective (Subtype.ext (hc.trans hd.symm))))

private def selectedEdges {ι : Type*} (q : ι → ℕ)
    (C : ∀ i, Fin (q i) → Finset ℕ) (D : ι × ι → Finset (ℕ × ℕ))
    (f : ∀ i, Fin (q i)) (ij : ι × ι) : Finset (ℕ × ℕ) :=
  (D ij).filter fun p ↦ p.1 ∈ C ij.1 (f ij.1) ∧ p.2 ∈ C ij.2 (f ij.2)

/-- Weighted edge counts are bounded by their mean under the independent choices. -/
private lemma exists_choices_le_weighted_edges {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (hq : ∀ i, 0 < q i)
    (C : ∀ i, Fin (q i) → Finset ℕ)
    (hC : ∀ i a b, a ≠ b → Disjoint (C i a) (C i b))
    (F : Finset (ι × ι)) (hF : ∀ ij ∈ F, ij.1 ≠ ij.2)
    (D : ι × ι → Finset (ℕ × ℕ)) (w : ι → ℚ) (hw : ∀ j, 0 ≤ w j) :
    ∃ f : ∀ i, Fin (q i),
      (∑ ij ∈ F, ((selectedEdges q C D f ij).card : ℚ) * w ij.2) ≤
        ∑ ij ∈ F, (D ij).card * (w ij.2 / ((q ij.1 : ℚ) * q ij.2)) := by
  classical
  let Ω := ∀ i, Fin (q i)
  let A : Finset Ω := Finset.univ
  let K : ℚ := ∑ ij ∈ F, (D ij).card * (w ij.2 / ((q ij.1 : ℚ) * q ij.2))
  have hne : A.Nonempty := ⟨fun i ↦ ⟨0, hq i⟩, Finset.mem_univ _⟩
  have hunique : ∀ i (a b : Fin (q i)) x, x ∈ C i a → x ∈ C i b → a = b := by
    intro i a b x ha hb
    by_contra hab
    exact Finset.disjoint_left.mp (hC i a b hab) ha hb
  have hsingle (ij : ι × ι) (hij : ij ∈ F) (p : ℕ × ℕ) :
      ((A.filter fun f ↦ p.1 ∈ C ij.1 (f ij.1) ∧ p.2 ∈ C ij.2 (f ij.2)).card : ℚ) *
          w ij.2 ≤
        A.card * (w ij.2 / ((q ij.1 : ℚ) * q ij.2)) := by
    let H := A.filter fun f ↦ p.1 ∈ C ij.1 (f ij.1) ∧ p.2 ∈ C ij.2 (f ij.2)
    change (H.card : ℚ) * _ ≤ _
    have hq1 : (0 : ℚ) < q ij.1 := by exact_mod_cast hq ij.1
    have hq2 : (0 : ℚ) < q ij.2 := by exact_mod_cast hq ij.2
    by_cases hH : H.Nonempty
    · obtain ⟨f, hf⟩ := hH
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hf).2
      have hEq : H = A.filter fun g ↦ g ij.1 = f ij.1 ∧ g ij.2 = f ij.2 := by
        ext g
        simp only [H, Finset.mem_filter]
        refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
        · exact fun ⟨g1, g2⟩ ↦ ⟨hunique _ _ _ _ g1 h1, hunique _ _ _ _ g2 h2⟩
        · rintro ⟨g1, g2⟩
          simpa only [g1, g2] using And.intro h1 h2
      have hcard : H.card * (q ij.1 * q ij.2) = A.card := by
        rw [hEq]
        simpa only [A, Finset.card_univ] using
          card_two_choice_fiber q ij.1 ij.2 (hF ij hij) (f ij.1) (f ij.2)
      have hc : (H.card : ℚ) * ((q ij.1 : ℚ) * q ij.2) = A.card := by exact_mod_cast hcard
      rw [← hc]
      field_simp
      rfl
    · have hempty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
      rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg (hw _) (mul_nonneg hq1.le hq2.le))
  have htotal :
      (∑ f ∈ A, ∑ ij ∈ F, ((selectedEdges q C D f ij).card : ℚ) * w ij.2) ≤
        ∑ _f ∈ A, K := by
    rw [Finset.sum_const, nsmul_eq_mul, show (A.card : ℚ) * K = ∑ ij ∈ F,
      A.card * ((D ij).card * (w ij.2 / ((q ij.1 : ℚ) * q ij.2))) by
        dsimp [K]; rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro ij hij
    calc
      _ = ∑ f ∈ A, ∑ p ∈ D ij,
          if p.1 ∈ C ij.1 (f ij.1) ∧ p.2 ∈ C ij.2 (f ij.2) then w ij.2 else 0 := by
        apply Finset.sum_congr rfl
        intro f _
        rw [← Finset.sum_filter]
        simp [selectedEdges, nsmul_eq_mul]
      _ = ∑ p ∈ D ij, ((A.filter fun f ↦ p.1 ∈ C ij.1 (f ij.1) ∧
          p.2 ∈ C ij.2 (f ij.2)).card : ℚ) * w ij.2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [← Finset.sum_filter]
        simp [nsmul_eq_mul]
      _ ≤ ∑ _p ∈ D ij, (A.card : ℚ) * (w ij.2 / ((q ij.1 : ℚ) * q ij.2)) :=
        Finset.sum_le_sum fun p _ ↦ hsingle ij hij p
      _ = _ := by simp [nsmul_eq_mul, mul_left_comm]
  obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le hne htotal
  exact ⟨f, hf⟩

/-- Count only representations of nonunique mixed sums. -/
private def DyadicRepeatPairBounds : Prop :=
  ∃ d k J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.range (2 ^ j)) ∧
    ∀ j, J ≤ j → j ≤ N →
      2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) ∧
      additiveEnergy (B j) ≤ 2 * (B j).card ^ 2 + (B j).card * (j + 1) ^ (2 * k) ∧
      ∀ i, j / 2 < i → i < j →
        (mixedRepeatPairs (B i) (B j)).card ≤ 2 ^ (j / 2) * (j + 1) ^ k

private lemma sum_reciprocal_steps (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 / ((j : ℚ) + 1) - 1 / ((j : ℚ) + 2))) =
      1 - 1 / ((N : ℚ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_succ]
    ring

/-- Weighted deletion only needs a density and repetition budget on the designated scales. -/
private lemma dyadicBlocks_on_support_avoiding_repeatPairs
    (d k N : ℕ) (S : Finset ℕ)
    (hS₁ : ∀ j ∈ S, 1 ≤ j) (hSN : ∀ j ∈ S, j ≤ N)
    (T B : ℕ → Finset ℕ) (hT : ∀ j, T j ⊆ B j)
    (hdense : ∀ j ∈ S, 2 ^ j ≤ (T j).card ^ 2 * (j + 1) ^ (2 * (d + 1)))
    (hlarge : ∀ j ∈ S, 2 * (2 * (j + 1)) ^ (d + k + 7) ≤ (T j).card)
    (hrep : ∀ j ∈ S, ∀ i ∈ S, j / 2 < i → i < j →
      (mixedRepeatPairs (B i) (B j)).card ≤ 2 ^ (j / 2) * (j + 1) ^ k) :
    ∃ U : ℕ → Finset ℕ, (∀ j, U j ⊆ T j) ∧
      (∀ j ∈ S, 2 ^ j ≤ (U j).card ^ 2 * (j + 1) ^ (2 * (d + (2 * (d + k + 7) + 2) + 1))) ∧
      ∀ i j, j / 2 < i → i < j → (crossDifferenceMatches (U i) (U j)).card = 0 := by
  classical
  let ι := {j : ℕ // j ∈ S}
  let e := d + k + 7
  let r (j : ι) := j.1 + 1
  let q (j : ι) := (2 * r j) ^ e
  let m (j : ι) := (T j.1).card / q j
  let w (j : ι) : ℚ := 2 / (m j : ℚ)
  let F : Finset (ι × ι) := Finset.univ.filter fun ij ↦ ij.2.1 / 2 < ij.1.1 ∧ ij.1.1 < ij.2.1
  let D (ij : ι × ι) := mixedRepeatPairs (B ij.1.1) (B ij.2.1)
  have hr (j : ι) : 2 ≤ r j := by have := hS₁ j.1 j.2; dsimp [r]; omega
  have hq (j : ι) : 0 < q j := by dsimp [q, r]; positivity
  have hm (j : ι) : 0 < m j := by
    have h := hlarge j.1 j.2
    change 2 * q j ≤ (T j.1).card at h
    exact Nat.div_pos (by omega) (hq j)
  have hM (j : ι) : (T j.1).card ≤ 2 * (m j * q j) := by
    have hdiv := Nat.div_add_mod (T j.1).card (q j)
    have hmod := Nat.mod_lt (T j.1).card (hq j)
    have hmul := Nat.mul_le_mul_right (q j) (show 1 ≤ m j from hm j)
    simp only [one_mul] at hmul
    change q j * m j + (T j.1).card % q j = (T j.1).card at hdiv
    rw [mul_comm (q j) (m j)] at hdiv
    omega
  have hpos (j : ι) : (0 : ℚ) < w j := by
    have hp : (0 : ℚ) < m j := by exact_mod_cast hm j
    exact div_pos (by norm_num) hp
  have hdiff (ij : ι × ι) (hij : ij ∈ F) :
      ij.2.1 / 2 < ij.1.1 ∧ ij.1.1 < ij.2.1 := (Finset.mem_filter.mp hij).2
  choose C hC hdisj using fun j : ι ↦ balanced_finset_choices (T j.1) (q j)
  obtain ⟨f, hf⟩ := exists_choices_le_weighted_edges q hq C hdisj F
    (fun ij hij heq ↦ (hdiff ij hij).2.ne (congrArg Subtype.val heq)) D w (fun j ↦ (hpos j).le)
  let E := selectedEdges q C D f
  have hterm (ij : ι × ι) (hij : ij ∈ F) :
      ((D ij).card : ℚ) * (w ij.2 / ((q ij.1 : ℚ) * q ij.2)) ≤ 1 / (r ij.2 : ℚ) ^ 4 := by
    obtain ⟨i, j⟩ := ij
    obtain ⟨hi, hij⟩ := hdiff (i,j) hij
    change j.1 / 2 < i.1 at hi
    have hroot : 2 ^ (j.1 / 2) ≤ (T j.1).card * (r j) ^ (d + 1) := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      calc
        (2 ^ (j.1 / 2)) ^ 2 = 2 ^ (j.1 / 2 * 2) := by rw [pow_mul]
        _ ≤ 2 ^ j.1 := pow_le_pow_right₀ (by decide) (by omega)
        _ ≤ (T j.1).card ^ 2 * (r j) ^ (2 * (d + 1)) := hdense j.1 j.2
        _ = _ := by rw [mul_pow, ← pow_mul, mul_comm 2 (d + 1)]
    have hD : (D (i,j)).card ≤ (T j.1).card * (r j) ^ (d + k + 1) := by
      calc
        _ ≤ 2 ^ (j.1 / 2) * (r j) ^ k := hrep j.1 j.2 i.1 i.2 hi hij
        _ ≤ ((T j.1).card * (r j) ^ (d + 1)) * (r j) ^ k := Nat.mul_le_mul_right _ hroot
        _ = _ := by rw [mul_assoc, ← pow_add, show d + 1 + k = d + k + 1 by omega]
    have hqi : r j ^ e ≤ q i := Nat.pow_le_pow_left (by dsimp [r]; omega) _
    have hqr : (0 : ℚ) < r j := by exact_mod_cast (show 0 < r j from by have := hr j; omega)
    have hqi' : (0 : ℚ) < q i := by exact_mod_cast hq i
    have hqj' : (0 : ℚ) < q j := by exact_mod_cast hq j
    have hm' : (0 : ℚ) < m j := by exact_mod_cast hm j
    have hD' : ((D (i,j)).card : ℚ) ≤ (T j.1).card * (r j : ℚ) ^ (d + k + 1) := by exact_mod_cast hD
    have hM' : ((T j.1).card : ℚ) ≤ 2 * ((m j : ℚ) * q j) := by exact_mod_cast hM j
    have hqi'' : (r j : ℚ) ^ e ≤ q i := by exact_mod_cast hqi
    have hfour : (4 : ℚ) ≤ (r j : ℚ) ^ 2 := by
      exact_mod_cast (show 4 ≤ r j ^ 2 from Nat.pow_le_pow_left (hr j) 2)
    change ((D (i,j)).card : ℚ) * ((2 / m j) / ((q i : ℚ) * q j)) ≤ _
    calc
      _ ≤ (2 * ((m j : ℚ) * q j) * (r j : ℚ) ^ (d + k + 1)) *
          ((2 / m j) / ((q i : ℚ) * q j)) := by
        gcongr
        exact hD'.trans (mul_le_mul_of_nonneg_right hM' (by positivity))
      _ = 4 * (r j : ℚ) ^ (d + k + 1) / q i := by field_simp; norm_num
      _ ≤ (r j : ℚ) ^ 2 * (r j : ℚ) ^ (d + k + 1) / (r j : ℚ) ^ e := by gcongr
      _ = _ := by
        have he : (r j : ℚ) ^ e =
            (r j : ℚ) ^ 2 * (r j : ℚ) ^ (d + k + 1) * (r j : ℚ) ^ 4 := by
          rw [← pow_add, ← pow_add]
          congr 1
          dsimp [e]
          omega
        rw [he]
        field_simp
  have hsum :
      (∑ ij ∈ F, (1 : ℚ) / (r ij.2 : ℚ) ^ 4) ≤ 1 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := Finset.univ)
      (g := Prod.snd) (fun _ _ ↦ Finset.mem_univ _) _]
    calc
      _ ≤ ∑ j : ι, (1 / ((j.1 : ℚ) + 1) - 1 / ((j.1 : ℚ) + 2)) := by
        apply Finset.sum_le_sum
        intro j _
        let H := F.filter (fun ij ↦ ij.2 = j)
        have hH : H.card ≤ j.1 := by
          rw [← Finset.card_range j.1]
          apply Finset.card_le_card_of_injOn (fun ij : ι × ι ↦ ij.1.1)
          · intro ij hij
            obtain ⟨hp, hj⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hij)
            exact Finset.mem_range.mpr (by simpa only [hj] using (hdiff ij hp).2)
          · intro a ha b hb he
            apply Prod.ext (Subtype.ext he)
            exact (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2.trans
              (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.symm
        have hs : (0 : ℚ) < r j := by exact_mod_cast (show 0 < r j from by have := hr j; omega)
        have hr' : (2 : ℚ) ≤ r j := by exact_mod_cast hr j
        have hrval : (r j : ℚ) = (j.1 : ℚ) + 1 := by simp [r]
        have hpow : (r j : ℚ) + 1 ≤ (r j : ℚ) ^ 2 := by nlinarith
        calc
          _ = (H.card : ℚ) * (1 / (r j : ℚ) ^ 4) := by
            change (∑ ij ∈ H, (1 : ℚ) / (r ij.2 : ℚ) ^ 4) = _
            have hcon : ∀ ij ∈ H, (1 : ℚ) / (r ij.2 : ℚ) ^ 4 = 1 / (r j : ℚ) ^ 4 :=
              fun ij hij ↦ by rw [(Finset.mem_filter.mp hij).2]
            rw [Finset.sum_congr rfl hcon, Finset.sum_const, nsmul_eq_mul]
          _ ≤ (r j : ℚ) / (r j : ℚ) ^ 4 := by
            simp only [div_eq_mul_inv, one_mul]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hH.trans (Nat.le_succ _)
          _ ≤ 1 / ((r j : ℚ) * ((r j : ℚ) + 1)) := by
            apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
            calc
              _ ≤ (r j : ℚ) * ((r j : ℚ) * (r j : ℚ) ^ 2) := by gcongr
              _ = _ := by ring
          _ = _ := by rw [show (j.1 : ℚ) + 2 = (j.1 : ℚ) + 1 + 1 by ring, ← hrval]; field_simp; ring
      _ ≤ ∑ j ∈ Finset.range (N + 1), (1 / ((j : ℚ) + 1) - 1 / ((j : ℚ) + 2)) := by
        rw [Finset.sum_coe_sort S (fun j : ℕ ↦ (1 / ((j : ℚ) + 1) - 1 / ((j : ℚ) + 2)))]
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hSN j hj))
          · intro j _ _
            apply sub_nonneg.mpr
            gcongr
            norm_num
      _ ≤ _ := by rw [sum_reciprocal_steps]; exact sub_le_self _ (by positivity)
  have htotal : (∑ ij ∈ F, ((E ij).card : ℚ) * w ij.2) ≤ 1 :=
    hf.trans ((Finset.sum_le_sum hterm).trans hsum)
  let I (j : ι) := F.filter fun ij ↦ ij.2 = j
  let H (j : ι) := (I j).biUnion fun ij ↦ (E ij).image Prod.snd
  let V (j : ι) := C j (f j) \ H j
  have hH (j : ι) : 2 * (H j).card ≤ m j := by
    have hcard : (H j).card ≤ ∑ ij ∈ I j, (E ij).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le)
    have hlocal : ((H j).card : ℚ) * w j ≤ 1 := by
      calc
        _ ≤ (∑ ij ∈ I j, ((E ij).card : ℚ)) * w j := by
          gcongr
          exact_mod_cast hcard
        _ = ∑ ij ∈ I j, ((E ij).card : ℚ) * w ij.2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun ij hij ↦ by rw [(Finset.mem_filter.mp hij).2]
        _ ≤ ∑ ij ∈ F, ((E ij).card : ℚ) * w ij.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity
        _ ≤ _ := htotal
    have hm' : (0 : ℚ) < m j := by exact_mod_cast hm j
    have hdiv : (2 * (H j).card : ℚ) / m j ≤ 1 := by
      simpa only [w, mul_div_assoc, mul_comm (2 : ℚ)] using hlocal
    have hc := (div_le_iff₀ hm').mp hdiv
    rw [one_mul] at hc
    exact_mod_cast hc
  let U (j : ℕ) : Finset ℕ := if hj : j ∈ S then V ⟨j, hj⟩ else ∅
  have hV (j : ι) : V j ⊆ C j (f j) := Finset.sdiff_subset
  have hsub (j : ℕ) : U j ⊆ T j := by
    by_cases hj : j ∈ S
    · simpa [U, hj] using (hV ⟨j,hj⟩).trans (hC ⟨j,hj⟩ (f ⟨j,hj⟩)).1
    · simp [U, hj]
  refine ⟨U, hsub, ?_, ?_⟩
  · intro j hj
    let x : ι := ⟨j, hj⟩
    have hU : U j = V x := dif_pos x.2
    have hcard := Finset.card_sdiff_add_card_inter (C x (f x)) (H x)
    have hcap := Finset.card_le_card (Finset.inter_subset_right (s₁ := C x (f x)) (s₂ := H x))
    have hfcard : (C x (f x)).card = m x := (hC x (f x)).2
    have hHalf := hH x
    have hsize : m x ≤ 2 * (U j).card := by
      rw [hU]
      change (V x).card + ((C x (f x)) ∩ H x).card = (C x (f x)).card at hcard
      omega
    have hqcap : q x ≤ (j + 1) ^ (2 * e) := by
      dsimp [q, r, x]
      rw [pow_mul]
      apply Nat.pow_le_pow_left
      calc
        2 * (j + 1) ≤ (j + 1) * (j + 1) := Nat.mul_le_mul_right _ (hr x)
        _ = _ := (pow_two _).symm
    apply dyadic_energy_count_transfer j d (2 * e + 2) _ _ (hdense j hj)
    calc
      _ ≤ 2 * (m x * q x) := hM x
      _ ≤ 2 * ((2 * (U j).card) * ((j + 1) ^ (2 * e))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hsize hqcap)
      _ ≤ ((j + 1) ^ 2) * ((U j).card * ((j + 1) ^ (2 * e))) := by
        rw [show (2 : ℕ) * ((2 * (U j).card) * (j + 1) ^ (2 * e)) =
          4 * ((U j).card * (j + 1) ^ (2 * e)) by ring]
        apply Nat.mul_le_mul_right
        exact Nat.pow_le_pow_left (hr x) 2
      _ = _ := by rw [pow_add]; ring
  · intro i j hi hij
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ⟨⟨a,b⟩,⟨u,v⟩⟩ hm
    simp only [crossDifferenceMatches, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hm
    obtain ⟨⟨⟨ha,hb⟩,⟨hu,hv⟩⟩, hab, _, heq⟩ := hm
    have hiS : i ∈ S := by by_contra hn; simp [U, hn] at ha
    have hjS : j ∈ S := by by_contra hn; simp [U, hn] at hu
    let x : ι := ⟨i,hiS⟩
    let y : ι := ⟨j,hjS⟩
    have hua : U i = V x := dif_pos hiS
    have huv : U j = V y := dif_pos hjS
    have haB : a ∈ B i := hT i (hsub i ha)
    have hbB : b ∈ B i := hT i (hsub i hb)
    have huB : u ∈ B j := hT j (hsub j hu)
    have hvB : v ∈ B j := hT j (hsub j hv)
    have hp : (a,v) ∈ D (x,y) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨haB,hvB⟩, Finset.one_lt_card.mpr ⟨(a,v), ?_, (b,u), ?_, ?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haB,hvB⟩, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hbB,huB⟩, by dsimp only; omega⟩
      · exact fun he ↦ hab.ne' (congrArg Prod.fst he)
    rw [hua] at ha
    rw [huv] at hv
    have he : (a,v) ∈ E (x,y) :=
      Finset.mem_filter.mpr ⟨hp, hV x ha, hV y hv⟩
    have hxy : (x,y) ∈ I y :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hij⟩, rfl⟩
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_biUnion.mpr ⟨(x,y), hxy, Finset.mem_image.mpr ⟨(a,v), he, rfl⟩⟩)


private lemma dyadicBlocks_avoiding_repeatPairs
    (d k J N : ℕ) (hJ : 1 ≤ J)
    (T B : ℕ → Finset ℕ) (hT : ∀ j, T j ⊆ B j)
    (hdense : ∀ j, J ≤ j → j ≤ N → 2 ^ j ≤ (T j).card ^ 2 * (j + 1) ^ (2 * (d + 1)))
    (hlarge : ∀ j, J ≤ j → j ≤ N → 2 * (2 * (j + 1)) ^ (d + k + 7) ≤ (T j).card)
    (hrep : ∀ j, J ≤ j → j ≤ N → ∀ i, j / 2 < i → i < j →
      (mixedRepeatPairs (B i) (B j)).card ≤ 2 ^ (j / 2) * (j + 1) ^ k) :
    ∃ U : ℕ → Finset ℕ, (∀ j, U j ⊆ T j) ∧
      (∀ j, J ≤ j → j ≤ N →
        2 ^ j ≤ (U j).card ^ 2 * (j + 1) ^ (2 * (d + (2 * (d + k + 7) + 2) + 1))) ∧
      ∀ i j, j / 2 < i → i < j → (crossDifferenceMatches (U i) (U j)).card = 0 := by
  let S := Finset.Icc J N
  have hmem j (hj : j ∈ S) : J ≤ j ∧ j ≤ N := Finset.mem_Icc.mp hj
  obtain ⟨U, hU, hc, hd⟩ := dyadicBlocks_on_support_avoiding_repeatPairs d k N S
    (fun j hj ↦ hJ.trans (hmem j hj).1) (fun j hj ↦ (hmem j hj).2) T B hT
    (fun j hj ↦ hdense j (hmem j hj).1 (hmem j hj).2)
    (fun j hj ↦ hlarge j (hmem j hj).1 (hmem j hj).2)
    (fun j hj i _ hi hij ↦ hrep j (hmem j hj).1 (hmem j hj).2 i hi hij)
  exact ⟨U, hU, fun j hj hjN ↦ hc j (Finset.mem_Icc.mpr ⟨hj, hjN⟩), hd⟩


private lemma eventually_large_dyadic_counts (d e : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ M : ℕ,
      2 ^ j ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1)) → 2 * (2 * (j + 1)) ^ e ≤ M := by
  filter_upwards [eventually_dyadic_pruning_budget (4 * e + 2 * (d + 1)),
    eventually_ge_atTop 1] with j h hj M hM
  let r := j + 1
  have hq : (2 * r) ^ e ≤ r ^ (2 * e) := by
    rw [pow_mul]
    apply Nat.pow_le_pow_left
    calc
      2 * r ≤ r * r := Nat.mul_le_mul_right _ (by dsimp [r]; omega)
      _ = _ := (pow_two _).symm
  have hs : (2 * (2 * r) ^ e) ^ 2 * r ^ (2 * (d + 1)) ≤ 2 ^ j := by
    calc
      _ ≤ (2 * r ^ (2 * e)) ^ 2 * r ^ (2 * (d + 1)) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hq) 2)
      _ = 4 * r ^ (4 * e + 2 * (d + 1)) := by
        rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega
      _ ≤ 4 * (2 ^ (j / 3)) ^ 2 * r ^ (4 * e + 2 * (d + 1)) := by
        have hpos : 1 ≤ (2 ^ (j / 3) : ℕ) ^ 2 := Nat.one_le_pow _ _ (by positivity)
        calc
          _ = 4 * 1 * r ^ (4 * e + 2 * (d + 1)) := by simp
          _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpos)
      _ ≤ 2 ^ j := h
  have hle : (2 * (2 * r) ^ e) ^ 2 * r ^ (2 * (d + 1)) ≤ M ^ 2 * r ^ (2 * (d + 1)) :=
    hs.trans hM
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    (Nat.le_of_mul_le_mul_right hle (by dsimp [r]; positivity))

/-- Independent balanced choices and deletion handle an unweighted count of repeated representations. -/
private lemma dyadicEnergyBounds_of_repeatPairs (h : DyadicRepeatPairBounds) :
    DyadicEnergyBounds := by
  classical
  obtain ⟨d, k, J, hB⟩ := h
  let D := d + k + 2
  let e := D + k + 7
  obtain ⟨J₁, h₁⟩ := eventually_atTop.mp (eventually_large_dyadic_counts D e)
  let J₀ := max J (max 1 J₁)
  refine ⟨D + (2 * e + 2), 0, J₀, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hB⟩ := hB N
  have hJ (j : ℕ) (hj : J₀ ≤ j) : J ≤ j ∧ 1 ≤ j ∧ J₁ ≤ j := by
    dsimp [J₀] at hj
    omega
  have hex : ∀ j, ∃ T ⊆ B j, IsSidon (T : Set ℕ) ∧
      (J₀ ≤ j → j ≤ N → 2 ^ j ≤ T.card ^ 2 * (j + 1) ^ (2 * (D + 1))) := by
    intro j
    by_cases hj : J₀ ≤ j ∧ j ≤ N
    · obtain ⟨hdense, hE, _⟩ := hB j (hJ j hj.1).1 hj.2
      obtain ⟨T, hTB, hT, hcard⟩ :=
        sidon_subset_of_small_additiveEnergy (B j) (j + 1) k (by have := (hJ j hj.1).2.1; omega) hE
      exact ⟨T, hTB, hT, fun _ _ ↦ dyadic_energy_count_transfer j d (k + 2) _ _ hdense hcard⟩
    · exact ⟨∅, Finset.empty_subset _, by simp [IsSidon], fun a b ↦ (hj ⟨a,b⟩).elim⟩
  choose T hT hsid hcount using hex
  have hlarge j (hj : J₀ ≤ j) (hjN : j ≤ N) : 2 * (2 * (j + 1)) ^ e ≤ (T j).card :=
    h₁ j (hJ j hj).2.2 _ (hcount j hj hjN)
  obtain ⟨U, hUT, hUcard, hUdiff⟩ := dyadicBlocks_avoiding_repeatPairs D k J₀ N
    (by dsimp [J₀]; omega) T B hT hcount hlarge
    fun j hj hjN ↦ (hB j (hJ j hj).1 hjN).2.2
  refine ⟨U, fun j ↦ (hUT j).trans ((hT j).trans (hpos j)), fun j hj hjN ↦ ?_⟩
  have hUsidon : IsSidon (U j : Set ℕ) := by
    intro a ha b hb c hc f hf hsum
    exact hsid j a (hUT j ha) b (hUT j hb) c (hUT j hc) f (hUT j hf) hsum
  refine ⟨hUcard j hj hjN, (additiveEnergy_le_of_isSidon _ hUsidon).trans (Nat.le_add_right _ _), ?_⟩
  intro i hi hij
  rw [crossAdditiveEnergy_eq, hUdiff i j hi hij, mul_zero, add_zero]
  exact Nat.le_add_right _ _

private lemma repeatPairs_of_mixedMoment (h : DyadicMixedMomentBounds) : DyadicRepeatPairBounds := by
  obtain ⟨d, k, J, hB⟩ := h
  refine ⟨d, k, J, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hB⟩ := hB N
  refine ⟨B, hpos, fun j hj hjN ↦ ?_⟩
  obtain ⟨hd, hE, hcross⟩ := hB j hj hjN
  exact ⟨hd, hE, fun i hi hij ↦ (mixedRepeatPairs_card_le _ _).trans (hcross i hi hij)⟩

private def repeatedArguments {α β : Type*} [DecidableEq β] (P : Finset α) (f : α → β) : Finset α :=
  P.filter fun p ↦ 1 < (P.filter fun q ↦ f q = f p).card

/-- The number of arguments with a repeated image is at most twice the loss of image size. -/
private lemma repeatedArguments_card_le {α β : Type*} [DecidableEq β] (P : Finset α) (f : α → β) :
    (repeatedArguments P f).card + 2 * (P.image f).card ≤ 2 * P.card := by
  let R := repeatedArguments P f
  let S := P.image f
  have hR : ∀ p ∈ R, f p ∈ S := fun p hp ↦
    Finset.mem_image_of_mem f (Finset.mem_filter.mp hp).1
  have hP : ∀ p ∈ P, f p ∈ S := fun _ hp ↦ Finset.mem_image_of_mem f hp
  change R.card + 2 * S.card ≤ 2 * P.card
  rw [Finset.card_eq_sum_card_fiberwise hR, Finset.card_eq_sum_card_fiberwise hP]
  simp only [Finset.mul_sum]
  have hs : 2 * S.card = ∑ _s ∈ S, (2 : ℕ) := by simp [mul_comm]
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s hs
  let F := P.filter fun p ↦ f p = s
  let H := R.filter fun p ↦ f p = s
  change H.card + 2 ≤ 2 * F.card
  have hsub : H ⊆ F := by
    intro p hp
    obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, heq⟩
  have hle := Finset.card_le_card hsub
  by_cases h : 1 < F.card
  · omega
  have hF : F.Nonempty := by
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hs
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, heq⟩⟩
  have hempty : H = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hr, heq⟩ := Finset.mem_filter.mp hp
    have hlarge := (Finset.mem_filter.mp hr).2
    rw [heq] at hlarge
    exact h hlarge
  have hpos := hF.card_pos
  rw [hempty, Finset.card_empty]
  omega

private def finiteSumset (A B : Finset ℕ) : Finset ℕ :=
  (A.product B).image fun p ↦ p.1 + p.2

private def unorderedSumArguments (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S.product S).filter fun p ↦ p.1 ≤ p.2

private lemma unorderedSumArguments_image (S : Finset ℕ) :
    (unorderedSumArguments S).image (fun p ↦ p.1 + p.2) = finiteSumset S S := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hp).1
  · intro hx
    obtain ⟨⟨a,b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    rcases le_total a b with hab | hba
    · exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp, hab⟩)
    · exact Finset.mem_image.mpr ⟨(b,a),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb,ha⟩, hba⟩, add_comm _ _⟩

/-- A small deficit in the self-sumset gives a large Sidon subset. -/
private lemma sidon_subset_of_self_sumset (S : Finset ℕ) (r k : ℕ) (hr : 2 ≤ r)
    (hsize : (unorderedSumArguments S).card ≤ (finiteSumset S S).card + S.card * r ^ k) :
    ∃ T ⊆ S, IsSidon (T : Set ℕ) ∧ S.card ≤ T.card * r ^ (k + 3) := by
  classical
  let V := {x : ℕ // x ∈ S}
  let P := unorderedSumArguments S
  let R := repeatedArguments P (fun p ↦ p.1 + p.2)
  let pair (a b : V) : ℕ × ℕ := (min a.1 b.1, max a.1 b.1)
  have hcomm : ∀ a b, pair a b = pair b a := by intro a b; simp [pair, min_comm, max_comm]
  let G : SimpleGraph V :=
    { Adj := fun a b ↦ a ≠ b ∧ pair a b ∈ R
      symm := by constructor; intro a b h; exact ⟨h.1.symm, (hcomm a b) ▸ h.2⟩
      loopless := ⟨fun a ha ↦ ha.1 rfl⟩ }
  let liftPair : Sym2 V → ℕ × ℕ := Sym2.lift ⟨pair, hcomm⟩
  have hsorted : ∀ e ∈ G.edgeFinset, ∃ a b : V, a.1 < b.1 ∧ e = s(a,b) := by
    intro e
    refine Sym2.ind ?_ e
    intro a b he
    have hadj := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
    rcases lt_or_gt_of_ne (fun eq : a.1 = b.1 ↦ hadj.1 (Subtype.ext eq)) with hab | hba
    · exact ⟨a,b,hab,rfl⟩
    · exact ⟨b,a,hba,Sym2.eq_swap⟩
  have hcard : G.edgeFinset.card ≤ R.card := by
    apply Finset.card_le_card_of_injOn liftPair
    · intro e he
      obtain ⟨a,b,_,rfl⟩ := hsorted e he
      exact (G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)).2
    · intro e he f hf hef
      obtain ⟨a,b,hab,rfl⟩ := hsorted e he
      obtain ⟨c,d,hcd,rfl⟩ := hsorted f hf
      simp only [liftPair, Sym2.lift_mk, pair, min_eq_left hab.le, max_eq_right hab.le,
        min_eq_left hcd.le, max_eq_right hcd.le, Prod.mk.injEq] at hef
      rw [Subtype.ext hef.1, Subtype.ext hef.2]
  obtain ⟨U, hU, hUc⟩ := independent_set_from_edge_count G
  let T := U.map (Function.Embedding.subtype fun x ↦ x ∈ S)
  have hsub : T ⊆ S := by
    intro x hx
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hx
    exact a.2
  refine ⟨T, hsub, ?_, ?_⟩
  · have hextract {a b c d : V} (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hd : d ∈ U)
        (hab : a.1 ≤ b.1) (hcd : c.1 ≤ d.1) (hsum : a.1 + b.1 = c.1 + d.1) :
        a = c ∧ b = d := by
      have hPab : (a.1,b.1) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨a.2,b.2⟩, hab⟩
      have hPcd : (c.1,d.1) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨c.2,d.2⟩, hcd⟩
      by_contra! hn
      have hpair_ne : (a.1,b.1) ≠ (c.1,d.1) := by
        intro heq
        exact hn (Subtype.ext (congrArg Prod.fst heq)) (Subtype.ext (congrArg Prod.snd heq))
      have hbad {p q : ℕ × ℕ} (hp : p ∈ P) (hq : q ∈ P)
          (heq : p.1 + p.2 = q.1 + q.2) (hne : p ≠ q) : p ∈ R := by
        apply Finset.mem_filter.mpr
        refine ⟨hp, Finset.one_lt_card.mpr ⟨p, ?_, q, ?_, hne⟩⟩
        · exact Finset.mem_filter.mpr ⟨hp, rfl⟩
        · exact Finset.mem_filter.mpr ⟨hq, heq.symm⟩
      by_cases hab' : a.1 < b.1
      · have hne : a ≠ b := fun heq ↦ hab'.ne (congrArg Subtype.val heq)
        apply hU ha hb hne
        exact ⟨hne, by simpa only [pair, min_eq_left hab, max_eq_right hab] using hbad hPab hPcd hsum hpair_ne⟩
      · have hcd' : c.1 < d.1 := by
          by_contra h
          exact hpair_ne (Prod.ext (by omega) (by omega))
        have hne : c ≠ d := fun heq ↦ hcd'.ne (congrArg Subtype.val heq)
        apply hU hc hd hne
        exact ⟨hne, by simpa only [pair, min_eq_left hcd, max_eq_right hcd] using hbad hPcd hPab hsum.symm hpair_ne.symm⟩
    intro a ha c hc b hb d hd hsum
    obtain ⟨a,haU,rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp ha)
    obtain ⟨b,hbU,rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hb)
    obtain ⟨c,hcU,rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hc)
    obtain ⟨d,hdU,rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hd)
    change a.1 + b.1 = c.1 + d.1 at hsum
    rcases le_total a.1 b.1 with hab | hba <;> rcases le_total c.1 d.1 with hcd | hdc
    · obtain ⟨rfl,rfl⟩ := hextract haU hbU hcU hdU hab hcd hsum
      exact Or.inl ⟨rfl,rfl⟩
    · obtain ⟨rfl,rfl⟩ := hextract haU hbU hdU hcU hab hdc (by simpa only [add_comm d.1 c.1] using hsum)
      exact Or.inr ⟨rfl,rfl⟩
    · obtain ⟨rfl,rfl⟩ := hextract hbU haU hcU hdU hba hcd (by simpa only [add_comm b.1 a.1] using hsum)
      exact Or.inr ⟨rfl,rfl⟩
    · obtain ⟨rfl,rfl⟩ := hextract hbU haU hdU hcU hba hdc (by simpa only [add_comm b.1 a.1, add_comm d.1 c.1] using hsum)
      exact Or.inl ⟨rfl,rfl⟩
  · have hR : R.card ≤ 2 * (S.card * r ^ k) := by
      have h := repeatedArguments_card_le P (fun p ↦ p.1 + p.2)
      rw [unorderedSumArguments_image] at h
      change R.card + 2 * (finiteSumset S S).card ≤ 2 * P.card at h
      change P.card ≤ _ at hsize
      omega
    have hcard' : T.card = U.card := Finset.card_map _
    have hV : Fintype.card V = S.card := Fintype.card_coe S
    rw [hV, ← hcard'] at hUc
    by_cases hzero : S.card = 0
    · simp [hzero]
    apply Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hzero)
    have hp : 1 ≤ r ^ k := Nat.one_le_pow _ _ (by omega)
    have h8 : 8 ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
    calc
      S.card * S.card = S.card ^ 2 := (pow_two _).symm
      _ ≤ T.card * (S.card + 2 * G.edgeFinset.card) := hUc
      _ ≤ T.card * (S.card + 2 * (2 * (S.card * r ^ k))) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hcard.trans hR)) _)
      _ = T.card * (S.card * (1 + 4 * r ^ k)) := by ring
      _ ≤ T.card * (S.card * (r ^ 3 * r ^ k)) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        have h := Nat.mul_le_mul_right (r ^ k) h8
        omega
      _ = S.card * (T.card * r ^ (k + 3)) := by rw [pow_add]; ring

/-- Both the internal and the mixed hypotheses can be stated using sizes of sumsets. -/
private def DyadicSumsetBounds : Prop :=
  ∃ d k J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.range (2 ^ j)) ∧
    ∀ j, J ≤ j → j ≤ N →
      2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) ∧
      (unorderedSumArguments (B j)).card ≤
        (finiteSumset (B j) (B j)).card + (B j).card * (j + 1) ^ k ∧
      ∀ i, j / 2 < i → i < j →
        (B i).card * (B j).card ≤ (finiteSumset (B i) (B j)).card + 2 ^ (j / 2) * (j + 1) ^ k

private lemma repeatPairs_of_sumsetBounds (h : DyadicSumsetBounds) : DyadicRepeatPairBounds := by
  classical
  obtain ⟨d, k, J, hB⟩ := h
  refine ⟨d + k + 3, k + 1, max J 1, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hb⟩ := hB N
  have hex : ∀ j, ∃ T ⊆ B j, IsSidon (T : Set ℕ) ∧
      (max J 1 ≤ j → j ≤ N → (B j).card ≤ T.card * (j + 1) ^ (k + 3)) := by
    intro j
    by_cases hj : max J 1 ≤ j ∧ j ≤ N
    · obtain ⟨T, hsub, hsid, hcard⟩ :=
        sidon_subset_of_self_sumset (B j) (j + 1) k (by omega) (hb j (by omega) hj.2).2.1
      exact ⟨T,hsub,hsid,fun _ _ ↦ hcard⟩
    · exact ⟨∅, Finset.empty_subset _, by simp [IsSidon], fun a b ↦ (hj ⟨a,b⟩).elim⟩
  choose T hsub hs hc using hex
  refine ⟨T, fun j ↦ (hsub j).trans (hpos j), fun j hj hjN ↦ ?_⟩
  obtain ⟨hdense, _, hcross⟩ := hb j (by omega) hjN
  refine ⟨dyadic_energy_count_transfer j d (k + 3) _ _ hdense (hc j hj hjN),
    (additiveEnergy_le_of_isSidon _ (hs j)).trans (Nat.le_add_right _ _), ?_⟩
  intro i hi hij
  have hmon : mixedRepeatPairs (T i) (T j) ⊆ mixedRepeatPairs (B i) (B j) := by
    intro p hp
    obtain ⟨hp, hcard⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsub i ha, hsub j hb⟩, ?_⟩
    exact hcard.trans_le (Finset.card_le_card (by
      intro q hq
      obtain ⟨hq, hsum⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsub i hq₁, hsub j hq₂⟩, hsum⟩))
  have hbound : (mixedRepeatPairs (B i) (B j)).card ≤ 2 * (2 ^ (j / 2) * (j + 1) ^ k) := by
    have hh := repeatedArguments_card_le ((B i).product (B j)) (fun p ↦ p.1 + p.2)
    rw [Finset.product_eq_sprod, Finset.card_product] at hh
    change (mixedRepeatPairs (B i) (B j)).card + 2 * (finiteSumset (B i) (B j)).card ≤
      2 * ((B i).card * (B j).card) at hh
    have hh' := hcross i hi hij
    omega
  calc
    _ ≤ (mixedRepeatPairs (B i) (B j)).card := Finset.card_le_card hmon
    _ ≤ 2 * (2 ^ (j / 2) * (j + 1) ^ k) := hbound
    _ ≤ (j + 1) * (2 ^ (j / 2) * (j + 1) ^ k) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [pow_succ]; ring

private lemma self_sumset_full (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) :
    (finiteSumset S S).card = (unorderedSumArguments S).card := by
  rw [← unorderedSumArguments_image]
  apply Finset.card_image_of_injOn
  intro ⟨a,b⟩ ha ⟨u,v⟩ hu hsum
  obtain ⟨hmab, hab⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
  obtain ⟨hmuv, huv⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hu)
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hmab
  obtain ⟨hu,hv⟩ := Finset.mem_product.mp hmuv
  rcases hS a ha u hu b hb v hv hsum with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact Prod.ext (by dsimp at hab huv; omega) (by dsimp at hab huv; omega)

private lemma mixed_sumset_full (A B : Finset ℕ) (h : Disjoint (positiveDifferences A) (positiveDifferences B)) :
    (finiteSumset A B).card = A.card * B.card := by
  unfold finiteSumset
  rw [Finset.card_image_of_injOn, Finset.product_eq_sprod, Finset.card_product]
  intro ⟨a,u⟩ hau ⟨b,v⟩ hbv hsum
  obtain ⟨ha,hu⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hau)
  obtain ⟨hb,hv⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hbv)
  change a + u = b + v at hsum
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have haD : b - a ∈ positiveDifferences A := mem_positiveDifferences.mpr ⟨b,hb,a,ha,hlt,rfl⟩
    have hbD : b - a ∈ positiveDifferences B := mem_positiveDifferences.mpr ⟨u,hu,v,hv,by omega,by omega⟩
    exact (Finset.disjoint_left.mp h haD hbD).elim
  · exact Prod.ext heq (by dsimp; omega)
  · have haD : a - b ∈ positiveDifferences A := mem_positiveDifferences.mpr ⟨a,ha,b,hb,hgt,rfl⟩
    have hbD : a - b ∈ positiveDifferences B := mem_positiveDifferences.mpr ⟨v,hv,u,hu,by omega,by omega⟩
    exact (Finset.disjoint_left.mp h haD hbD).elim

/-- Clean Sidon blocks have no deficit in either type of sumset. -/
private lemma sumsetBounds_of_nearby (h : NearbyDyadicSidon) : DyadicSumsetBounds := by
  obtain ⟨d,J,hB⟩ := h
  refine ⟨d,0,J,fun N ↦ ?_⟩
  obtain ⟨B,hpos,hsid,hcount,hsep⟩ := hB N
  let A (j : ℕ) := (B j).image (· - 2 ^ j)
  have hlo j x (hx : x ∈ B j) : 2 ^ j ≤ x := (Finset.mem_Ico.mp (hpos j hx)).1
  have ha j : (A j).card = (B j).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy he
    have hx' := hlo j x hx
    have hy' := hlo j y hy
    dsimp only at he
    omega
  have hs j : IsSidon (A j : Set ℕ) :=
    isSidon_image_sub _ (fun a ha c hc b hb e he hs ↦ hsid j a ha b hb c hc e he hs) _ (hlo j)
  have hdiff j : positiveDifferences (A j) = positiveDifferences (B j) :=
    positiveDifferences_image_sub _ _ (hlo j)
  refine ⟨A, ?_, fun j hj hjN ↦ ⟨by simpa only [ha] using hcount j hj hjN, ?_, ?_⟩⟩
  · intro j x hx
    obtain ⟨a, hm, rfl⟩ := Finset.mem_image.mp hx
    have hlt := (Finset.mem_Ico.mp (hpos j hm)).2
    rw [pow_succ] at hlt
    exact Finset.mem_range.mpr (by omega)
  · rw [self_sumset_full _ (hs j)]
    exact Nat.le_add_right _ _
  · intro i hi hij
    have hd : Disjoint (positiveDifferences (A i)) (positiveDifferences (A j)) := by
      rw [hdiff i, hdiff j]
      apply Finset.disjoint_left.mpr
      intro v hvi hvj
      obtain ⟨a,ha,b,hb,hab,he⟩ := mem_positiveDifferences.mp hvi
      obtain ⟨u,hu,w,hw,huw,hf⟩ := mem_positiveDifferences.mp hvj
      exact hsep i j (by omega) hij a ha b hb u hu w hw hab huw (he.trans hf.symm)
    rw [mixed_sumset_full _ _ hd]
    exact Nat.le_add_right _ _

private lemma nearby_iff_sumsetBounds : NearbyDyadicSidon ↔ DyadicSumsetBounds :=
  ⟨sumsetBounds_of_nearby, fun h ↦ nearby_of_approx_dyadic_blocks (approx_of_additiveEnergy_dyadic_blocks
    (additiveEnergy_of_dyadicEnergyBounds (dyadicEnergyBounds_of_repeatPairs (repeatPairs_of_sumsetBounds h))))⟩

/-- Select a large part of a set inside one interval of length `q` and translate it into
`[q, 2*q)`. The subfinset records the original positions of the selected points. -/
private lemma localize_finset (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (q L : ℕ)
    (hq : 0 < q) (hL : 0 < L) (hrange : ∀ x ∈ S, x < L * q) :
    ∃ T ⊆ S, ∃ U ⊆ Finset.Ico q (2 * q), IsSidon (U : Set ℕ) ∧
      positiveDifferences U = positiveDifferences T ∧ S.card ≤ L * U.card := by
  classical
  let fiber (i : ℕ) := S.filter (fun x ↦ x / q = i)
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image (Finset.range L) (fun k ↦ (fiber k).card)
    ⟨0, Finset.mem_range.mpr hL⟩
  let T := fiber i
  have hsub : T ⊆ S := Finset.filter_subset _ _
  have hlo x (hx : x ∈ T) : i * q ≤ x := by
    have he := (Finset.mem_filter.mp hx).2
    have h := Nat.div_mul_le_self x q
    rwa [he] at h
  have hhi x (hx : x ∈ T) : x < i * q + q := by
    have he := (Finset.mem_filter.mp hx).2
    simpa only [he] using Nat.lt_div_mul_add (a := x) hq
  let V := T.image (· - i * q)
  let U := V.image (· + q)
  have hv : V.card = T.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    have h₁ := hlo a ha
    have h₂ := hlo b hb
    change a - i * q = b - i * q at he
    omega
  have hu : U.card = V.card := by
    apply Finset.card_image_of_injective
    exact fun a b h ↦ Nat.add_right_cancel h
  refine ⟨T, hsub, U, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    have h₁ := hlo t ht
    have h₂ := hhi t ht
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · have hT : IsSidon (T : Set ℕ) :=
      fun a ha b hb u hu v hv h ↦ hS a (hsub ha) b (hsub hb) u (hsub hu) v (hsub hv) h
    exact isSidon_image_add _ (isSidon_image_sub _ hT _ hlo) _
  · exact (positiveDifferences_image_add V q).trans (positiveDifferences_image_sub T _ hlo)
  · rw [hu, hv]
    have hmaps : Set.MapsTo (fun x : ℕ ↦ x / q) (S : Set ℕ) (Finset.range L : Set ℕ) :=
      fun x hx ↦ Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr (hrange x hx))
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      _ ≤ ∑ _ ∈ Finset.range L, T.card := Finset.sum_le_sum (fun k hk ↦ hmax k hk)
      _ = L * T.card := by simp

private lemma positiveDifferences_subset {A B : Finset ℕ} (hAB : A ⊆ B) :
    positiveDifferences A ⊆ positiveDifferences B := by
  intro x hx
  obtain ⟨a, ha, b, hb, hab, h⟩ := mem_positiveDifferences.mp hx
  exact mem_positiveDifferences.mpr ⟨a, hAB ha, b, hAB hb, hab, h⟩

/-- Disjoint parts of one Sidon set have disjoint positive differences. -/
private lemma disjoint_positiveDifferences_of_subsets {S A B : Finset ℕ}
    (hS : IsSidon (S : Set ℕ)) (hA : A ⊆ S) (hB : B ⊆ S) (hAB : Disjoint A B) :
    Disjoint (positiveDifferences A) (positiveDifferences B) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, ha, b, hb, hab, he⟩ := mem_positiveDifferences.mp hx
  obtain ⟨u, hu, v, hv, huv, hf⟩ := mem_positiveDifferences.mp hy
  obtain ⟨rfl, _⟩ := sidon_positive_difference_unique S hS (hA ha) (hA hb) (hB hu) (hB hv)
    hab huv (he.trans hf.symm)
  exact Finset.disjoint_left.mp hAB ha hu

private lemma eventually_dyadic_card_ge_twice_index (d : ℕ) :
    ∀ᶠ s : ℕ in atTop, ∀ M : ℕ, 2 ^ s ≤ M ^ 2 * (s + 1) ^ (2 * (d + 1)) →
      2 * (s + 1) ≤ M := by
  filter_upwards [eventually_dyadic_pruning_budget (2 * (d + 1) + 2)] with s hs M hM
  apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
  apply Nat.le_of_mul_le_mul_right _ (show 0 < (s + 1) ^ (2 * (d + 1)) by positivity)
  have h1 : 1 ≤ ((2 : ℕ) ^ (s / 3)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  calc
    _ = 4 * (s + 1) ^ (2 * (d + 1) + 2) := by rw [pow_add]; ring
    _ ≤ 4 * (2 ^ (s / 3)) ^ 2 * (s + 1) ^ (2 * (d + 1) + 2) := by
      simpa only [mul_one] using Nat.mul_le_mul_right ((s + 1) ^ (2 * (d + 1) + 2))
        (Nat.mul_le_mul_left 4 h1)
    _ ≤ 2 ^ s := hs
    _ ≤ _ := hM

/-- The dense parent of block `j` may be chosen slightly above `j`. Several blocks
may use the same parent, and different finite horizons may use different checkpoints. -/
private def CheckpointDyadicSidon : Prop :=
  ∃ d e k J : ℕ, ∀ N : ℕ, ∃ (B : ℕ → Finset ℕ) (σ : ℕ → ℕ),
    (∀ s, B s ⊆ Finset.Ico (2 ^ s) (2 ^ (s + 1))) ∧
    (∀ s, IsSidon (B s : Set ℕ)) ∧
    (∀ r s, s / 2 < r → r < s →
      (positiveDifferences (B r) ∩ positiveDifferences (B s)).card ≤ 2 ^ (s / 2) * (s + 1) ^ k) ∧
    ∀ j, J ≤ j → j ≤ N →
      j ≤ σ j ∧ σ j ≤ j + j / 2 ∧ 2 ^ (σ j - j) ≤ (j + 1) ^ e ∧
      2 ^ σ j ≤ (B (σ j)).card ^ 2 * (σ j + 1) ^ (2 * (d + 1))

/-- Split each parent into disjoint bins and localize each bin at its target scale.
For distinct parents, the nearby overlaps of the children are bounded by those of the parents. -/
private lemma sparse_of_checkpoint_dyadic_sidon (h : CheckpointDyadicSidon) : SparseDyadicSidon := by
  classical
  obtain ⟨d, e, k, J, hB⟩ := h
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_dyadic_card_ge_twice_index d)
  let J₀ := max (max J K) 1
  let D := 2 * d + 1 + (e + 4)
  let ℓ := e + 2 * k
  refine ⟨D, D + (ℓ + 1) + 3, J₀, fun N ↦ ?_⟩
  obtain ⟨B, σ, hpos, hsid, hsep, hparent⟩ := hB N
  choose P hP hPdisj using fun s ↦ balanced_finset_choices (B s) (s + 1)
  let active (j : ℕ) := J₀ ≤ j ∧ j ≤ N
  let slot (j : ℕ) : Fin (σ j + 1) := ⟨min j (σ j), by omega⟩
  have hex j : ∃ T C : Finset ℕ,
      T ⊆ P (σ j) (slot j) ∧ C ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∧
      IsSidon (C : Set ℕ) ∧ positiveDifferences C = positiveDifferences T ∧
      (active j → 2 ^ j ≤ C.card ^ 2 * (j + 1) ^ (2 * (D + 1))) ∧
      (¬ active j → C = ∅) := by
    by_cases ha : active j
    · have hjJ : J ≤ j := (le_max_left J K).trans ((le_max_left _ _).trans ha.1)
      have hjK : K ≤ j := (le_max_right J K).trans ((le_max_left _ _).trans ha.1)
      have hj1 : 1 ≤ j := (le_max_right _ _).trans ha.1
      obtain ⟨hjs, hsj, hgap, hdense⟩ := hparent j hjJ ha.2
      let s := σ j
      let Q := P s (slot j)
      let L := 2 ^ (s - j + 1)
      have hsub : Q ⊆ B s := (hP s (slot j)).1
      have hQ : Q.card = (B s).card / (s + 1) := (hP s (slot j)).2
      have hQsid : IsSidon (Q : Set ℕ) :=
        fun a ha b hb u hu v hv hs ↦ hsid s a (hsub ha) b (hsub hb) u (hsub hu) v (hsub hv) hs
      have htop x (hx : x ∈ Q) : x < L * 2 ^ j := by
        have h := (Finset.mem_Ico.mp (hpos s (hsub hx))).2
        dsimp [L]
        rw [← pow_add, show s - j + 1 + j = s + 1 by dsimp [s]; omega]
        exact h
      obtain ⟨T, hT, C, hC, hCs, hCD, hCl⟩ :=
        localize_finset Q hQsid (2 ^ j) L (by positivity) (by positivity) htop
      refine ⟨T, C, hT, ?_, hCs, hCD, fun _ ↦ ?_, fun hna ↦ (hna ha).elim⟩
      · simpa only [pow_succ, mul_comm] using hC
      have hsize : 2 * (s + 1) ≤ (B s).card := hK s (hjK.trans hjs) _ hdense
      have hQpos : 0 < Q.card := by
        rw [hQ]
        exact Nat.div_pos (by omega) (by omega)
      have hsizeQ : (B s).card ≤ (2 * (s + 1)) * Q.card := by
        have h := Nat.lt_div_mul_add (a := (B s).card) (b := s + 1) (by omega)
        rw [← hQ] at h
        have hh : s + 1 ≤ (s + 1) * Q.card := by
          simpa only [mul_one] using Nat.mul_le_mul_left (s + 1) (show 1 ≤ Q.card from hQpos)
        calc
          _ ≤ Q.card * (s + 1) + (s + 1) := h.le
          _ ≤ Q.card * (s + 1) + (s + 1) * Q.card := Nat.add_le_add_left hh _
          _ = _ := by ring
      have hscale : s + 1 ≤ (j + 1) ^ 2 := by
        calc
          _ ≤ 2 * (j + 1) := by dsimp [s]; omega
          _ ≤ (j + 1) ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
      have hL : L ≤ (j + 1) ^ (e + 1) := by
        dsimp [L, s]
        rw [pow_succ, pow_succ]
        exact Nat.mul_le_mul hgap (by omega)
      have hcount : 2 ^ j ≤ (B s).card ^ 2 * (j + 1) ^ (2 * (2 * d + 1 + 1)) := by
        calc
          _ ≤ 2 ^ s := pow_le_pow_right₀ (by decide) hjs
          _ ≤ _ := hdense
          _ ≤ (B s).card ^ 2 * ((j + 1) ^ 2) ^ (2 * (d + 1)) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hscale _)
          _ = _ := by rw [← pow_mul]; congr 2
      refine dyadic_energy_count_transfer j (2 * d + 1) (e + 4) (B s).card C.card hcount ?_
      calc
        _ ≤ (2 * (s + 1)) * Q.card := hsizeQ
        _ ≤ (2 * (s + 1)) * (L * C.card) := Nat.mul_le_mul_left _ hCl
        _ ≤ ((j + 1) * (j + 1) ^ 2) * ((j + 1) ^ (e + 1) * C.card) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) hscale) (Nat.mul_le_mul_right _ hL)
        _ = _ := by rw [show e + 4 = 1 + 2 + (e + 1) by omega, pow_add, pow_add, pow_one]; ring
    · exact ⟨∅, ∅, Finset.empty_subset _, Finset.empty_subset _, by simp [IsSidon],
        rfl, fun h ↦ (ha h).elim, fun _ ↦ rfl⟩
  choose T C hT hC hCs hCD hcount hzero using hex
  have hscale j (hj : active j) :
      2 ^ (σ j / 2) ≤ 2 ^ (j / 2) * (j + 1) ^ e := by
    have hjJ : J ≤ j := (le_max_left J K).trans ((le_max_left _ _).trans hj.1)
    obtain ⟨hjs, _, hgap, _⟩ := hparent j hjJ hj.2
    calc
      _ ≤ 2 ^ (j / 2 + (σ j - j)) := pow_le_pow_right₀ (by decide) (by omega)
      _ ≤ _ := by rw [pow_add]; exact Nat.mul_le_mul_left _ hgap
  have hparentCap i j (hai : active i) (hij : i ≤ j) (hj1 : 1 ≤ j) :
      2 ^ (σ i / 2) * (σ i + 1) ^ k ≤ 2 ^ (j / 2) * (j + 1) ^ ℓ := by
    have hiJ : J ≤ i := (le_max_left J K).trans ((le_max_left _ _).trans hai.1)
    have hsi := (hparent i hiJ hai.2).2.1
    have hpow : 2 ^ (i / 2) ≤ (2 : ℕ) ^ (j / 2) := pow_le_pow_right₀ (by decide) (by omega)
    have hindex : σ i + 1 ≤ (j + 1) ^ 2 := by
      rw [pow_two]
      exact (show σ i + 1 ≤ 2 * (j + 1) by omega).trans (Nat.mul_le_mul_right _ (by omega))
    calc
      _ ≤ (2 ^ (i / 2) * (i + 1) ^ e) * ((j + 1) ^ 2) ^ k :=
        Nat.mul_le_mul (hscale i hai) (Nat.pow_le_pow_left hindex _)
      _ ≤ (2 ^ (j / 2) * (j + 1) ^ e) * ((j + 1) ^ 2) ^ k :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hpow (Nat.pow_le_pow_left (by omega) _))
      _ = _ := by rw [← pow_mul, mul_assoc, ← pow_add]
  have hCpair i j (haj : active j) (hi : σ j / 2 < i) (hij : i < j) :
      (positiveDifferences (C i) ∩ positiveDifferences (C j)).card ≤ 2 ^ (j / 2) * (j + 1) ^ ℓ := by
    by_cases hai : active i
    swap
    · simp [hzero i hai, positiveDifferences]
    have hiJ : J ≤ i := (le_max_left J K).trans ((le_max_left _ _).trans hai.1)
    have hjJ : J ≤ j := (le_max_left J K).trans ((le_max_left _ _).trans haj.1)
    have hj1 : 1 ≤ j := (le_max_right _ _).trans haj.1
    obtain ⟨his, hsi, _, _⟩ := hparent i hiJ hai.2
    obtain ⟨hjs, _, _, _⟩ := hparent j hjJ haj.2
    rw [hCD, hCD]
    have hI : (positiveDifferences (T i) ∩ positiveDifferences (T j)).card ≤
        (positiveDifferences (B (σ i)) ∩ positiveDifferences (B (σ j))).card := by
      apply Finset.card_le_card
      exact Finset.inter_subset_inter
        (positiveDifferences_subset ((hT i).trans (hP _ _).1))
        (positiveDifferences_subset ((hT j).trans (hP _ _).1))
    rcases lt_trichotomy (σ i) (σ j) with hlt | heq | hgt
    · exact hI.trans ((hsep _ _ (by omega) hlt).trans (hparentCap j j haj le_rfl hj1))
    · have hdisj : Disjoint (positiveDifferences (T i)) (positiveDifferences (T j)) := by
        apply disjoint_positiveDifferences_of_subsets (S := B (σ j)) (hsid _)
        · simpa only [heq] using (hT i).trans (hP _ _).1
        · exact (hT j).trans (hP _ _).1
        · have hPne : ∀ (s : ℕ) (a b : Fin (s + 1)), a.val ≠ b.val →
              Disjoint (P s a) (P s b) := fun s a b hab ↦ hPdisj s a b (fun h ↦ hab (congrArg Fin.val h))
          have hPi (s : ℕ) (hes : σ i = s) (his' : i ≤ s) : T i ⊆ P s ⟨i, by omega⟩ := by
            subst s
            have he : slot i = ⟨i, by omega⟩ := Fin.ext (min_eq_left his)
            rw [← he]
            exact hT _
          have hPj : T j ⊆ P (σ j) ⟨j, by omega⟩ := by
            have he : slot j = ⟨j, by omega⟩ := Fin.ext (min_eq_left hjs)
            rw [← he]
            exact hT _
          exact (hPne _ _ _ hij.ne).mono (hPi _ heq (by omega)) hPj
      simp [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
    · apply hI.trans
      rw [Finset.inter_comm]
      exact (hsep _ _ (by omega) hgt).trans (hparentCap i j hai hij.le hj1)
  refine ⟨C, hC, hCs, fun j hj hjN ↦ ?_⟩
  have ha : active j := ⟨hj, hjN⟩
  have hd := hcount j ha
  refine ⟨hd, dyadic_conflict_budget_from_pairwise_overlap C hC j (σ j / 2) D ℓ
    ((le_max_right _ _).trans hj) ?_ (fun i ↦ hCpair i j ha) hd⟩
  exact (hscale j ha).trans (Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by omega) (by dsimp [ℓ]; omega)))

private lemma checkpoint_dyadic_sidon_of_nearby (h : NearbyDyadicSidon) : CheckpointDyadicSidon := by
  obtain ⟨d, J, hB⟩ := h
  refine ⟨d, 0, 0, J, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hsid, hcount, hsep⟩ := hB N
  refine ⟨B, id, hpos, fun j a ha u hu b hb v hv hs ↦ hsid j a ha b hb u hu v hv hs,
    ?_, fun j hj hjN ↦ ⟨le_rfl, Nat.le_add_right _ _, by simp, hcount j hj hjN⟩⟩
  intro r s hr hrs
  have h : Disjoint (positiveDifferences (B r)) (positiveDifferences (B s)) := by
    apply Finset.disjoint_left.mpr
    intro t ht₁ ht₂
    obtain ⟨a, ha, b, hb, hab, he⟩ := mem_positiveDifferences.mp ht₁
    obtain ⟨u, hu, v, hv, huv, hf⟩ := mem_positiveDifferences.mp ht₂
    exact hsep r s (by omega) hrs a ha b hb u hu v hv hab huv (he.trans hf.symm)
  simp [Finset.disjoint_iff_inter_eq_empty.mp h]

private lemma nearby_iff_checkpoint_dyadic_sidon : NearbyDyadicSidon ↔ CheckpointDyadicSidon :=
  ⟨checkpoint_dyadic_sidon_of_nearby, fun h ↦ nearby_of_sparse_dyadic_blocks (sparse_of_checkpoint_dyadic_sidon h)⟩

/-- The parent index exceeds its child's index by at most half the child's index
once the polynomial gap bound holds at a sufficiently large scale. -/
private lemma eventually_checkpoint_index_close (e : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ s ≥ j, 2 ^ (s - j) ≤ (j + 1) ^ e → s ≤ j + j / 2 := by
  obtain ⟨K, hK⟩ := eventually_log_shift (2 * e) 0
  refine (eventually_ge_atTop K).mono fun j hj s hjs hgap ↦ ?_
  let L := Nat.log 2 (j + 2) + 1
  have hL : j + 1 ≤ 2 ^ L :=
    (Nat.le_succ _).trans (Nat.lt_pow_succ_log_self (by decide) _).le
  have hg : s - j ≤ L * e := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hgap.trans (by rw [pow_mul]; exact Nat.pow_le_pow_left hL _))
  have hs := hK j hj
  change 0 + 2 * e * L ≤ j at hs
  have hsize : 2 * (L * e) ≤ j := by simpa only [zero_add, mul_assoc, mul_comm e L] using hs
  omega

/-- A family of parent blocks at adaptive checkpoints can be specified by
cardinality bounds for self-sumsets and mixed sumsets. -/
private def CheckpointDyadicSumsetBounds : Prop :=
  ∃ d e k J : ℕ, ∀ N : ℕ, ∃ (P : Finset ℕ) (B : ℕ → Finset ℕ),
    (∀ s, B s ⊆ Finset.Ico (2 ^ s) (2 ^ (s + 1))) ∧
    (∀ j, J ≤ j → j ≤ N → ∃ s ∈ P, j ≤ s ∧ 2 ^ (s - j) ≤ (j + 1) ^ e) ∧
    ∀ s ∈ P,
      2 ^ s ≤ (B s).card ^ 2 * (s + 1) ^ (2 * (d + 1)) ∧
      (unorderedSumArguments (B s)).card ≤
        (finiteSumset (B s) (B s)).card + (B s).card * (s + 1) ^ k ∧
      ∀ r ∈ P, s / 2 < r → r < s →
        (B r).card * (B s).card ≤ (finiteSumset (B r) (B s)).card + 2 ^ (s / 2) * (s + 1) ^ k

/-- Apply the two deletion steps to the parent blocks, then use the cleaned
parents for all children that chose them. -/
private lemma checkpoint_dyadic_sidon_of_checkpoint_sumset_bounds
    (h : CheckpointDyadicSumsetBounds) : CheckpointDyadicSidon := by
  classical
  obtain ⟨d, e, k, J, hB⟩ := h
  let D := d + k + 3
  let E := D + (k + 1) + 7
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_large_dyadic_counts D E)
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp (eventually_checkpoint_index_close e)
  let J₀ := max (max J 1) (max K K₁)
  refine ⟨D + (2 * E + 2), e, 0, J₀, fun N ↦ ?_⟩
  obtain ⟨P, B, hpos, hcover, hB⟩ := hB N
  let S := P.filter (J₀ ≤ ·)
  have hPS s (hs : s ∈ S) : s ∈ P := (Finset.mem_filter.mp hs).1
  have hS₁ s (hs : s ∈ S) : 1 ≤ s := by
    have hs' := (Finset.mem_filter.mp hs).2
    dsimp [J₀] at hs'
    omega
  have hex s : ∃ T ⊆ B s, IsSidon (T : Set ℕ) ∧
      (s ∈ S → 2 ^ s ≤ T.card ^ 2 * (s + 1) ^ (2 * (D + 1))) := by
    by_cases hs : s ∈ S
    · obtain ⟨hdense, hself, _⟩ := hB s (hPS s hs)
      obtain ⟨T, hT, hsid, hcard⟩ :=
        sidon_subset_of_self_sumset (B s) (s + 1) k (by have := hS₁ s hs; omega) hself
      exact ⟨T, hT, hsid, fun _ ↦ dyadic_energy_count_transfer s d (k + 3) _ _ hdense hcard⟩
    · exact ⟨∅, Finset.empty_subset _, by simp [IsSidon], fun h ↦ (hs h).elim⟩
  choose T hT hTs hTc using hex
  have hlarge s (hs : s ∈ S) : 2 * (2 * (s + 1)) ^ E ≤ (T s).card := by
    have hs' := (Finset.mem_filter.mp hs).2
    exact hK s (by dsimp [J₀] at hs'; omega) _ (hTc s hs)
  have hrep s (hs : s ∈ S) r (hr : r ∈ S) (hnear : s / 2 < r) (hlt : r < s) :
      (mixedRepeatPairs (B r) (B s)).card ≤ 2 ^ (s / 2) * (s + 1) ^ (k + 1) := by
    have hcross := (hB s (hPS s hs)).2.2 r (hPS r hr) hnear hlt
    have hcount := repeatedArguments_card_le ((B r).product (B s)) (fun p ↦ p.1 + p.2)
    rw [Finset.product_eq_sprod, Finset.card_product] at hcount
    change (mixedRepeatPairs (B r) (B s)).card + 2 * (finiteSumset (B r) (B s)).card ≤
      2 * ((B r).card * (B s).card) at hcount
    have hr : 2 ≤ s + 1 := by have := hS₁ s hs; omega
    calc
      _ ≤ 2 * (2 ^ (s / 2) * (s + 1) ^ k) := by omega
      _ ≤ (s + 1) * (2 ^ (s / 2) * (s + 1) ^ k) := Nat.mul_le_mul_right _ hr
      _ = _ := by rw [pow_succ]; ring
  obtain ⟨U, hUT, hUcard, hdiff⟩ := dyadicBlocks_on_support_avoiding_repeatPairs D (k + 1)
    (S.sup id) S hS₁ (fun s hs ↦ Finset.le_sup (f := id) hs) T B hT hTc hlarge hrep
  have hchoice j (hj : J₀ ≤ j ∧ j ≤ N) :
      ∃ s ∈ S, j ≤ s ∧ s ≤ j + j / 2 ∧ 2 ^ (s - j) ≤ (j + 1) ^ e := by
    have hjJ : J ≤ j := by have := hj.1; dsimp [J₀] at this; omega
    have hjK : K₁ ≤ j := by have := hj.1; dsimp [J₀] at this; omega
    obtain ⟨s, hs, hjs, hg⟩ := hcover j hjJ hj.2
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, hj.1.trans hjs⟩, hjs, hK₁ j hjK s hjs hg, hg⟩
  let σ (j : ℕ) := if hj : J₀ ≤ j ∧ j ≤ N then Classical.choose (hchoice j hj) else 0
  refine ⟨U, σ, fun s ↦ (hUT s).trans ((hT s).trans (hpos s)), ?_, ?_, ?_⟩
  · intro s a ha b hb u hu v hv
    exact hTs s a (hUT s ha) b (hUT s hb) u (hUT s hu) v (hUT s hv)
  · intro r s hr hrs
    have hempty := Finset.card_eq_zero.mp (hdiff r s hr hrs)
    suffices h : Disjoint (positiveDifferences (U r)) (positiveDifferences (U s)) by
      simp [Finset.disjoint_iff_inter_eq_empty.mp h]
    apply Finset.disjoint_left.mpr
    intro t ht hts
    obtain ⟨a, ha, b, hb, hab, he⟩ := mem_positiveDifferences.mp ht
    obtain ⟨u, hu, v, hv, huv, hf⟩ := mem_positiveDifferences.mp hts
    have hm : ((a,b),(u,v)) ∈ crossDifferenceMatches (U r) (U s) := by
      simp only [crossDifferenceMatches, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
      exact ⟨⟨⟨ha,hb⟩,⟨hu,hv⟩⟩, hab, huv, he.trans hf.symm⟩
    rw [hempty] at hm
    exact Finset.notMem_empty _ hm
  · intro j hj hjN
    have haj : J₀ ≤ j ∧ j ≤ N := ⟨hj, hjN⟩
    have he : σ j = Classical.choose (hchoice j haj) := dif_pos haj
    rw [he]
    obtain ⟨hs, hjs, hclose, hg⟩ := Classical.choose_spec (hchoice j haj)
    exact ⟨hjs, hclose, hg, hUcard _ hs⟩

private lemma checkpoint_sumset_bounds_of_nearby (h : NearbyDyadicSidon) : CheckpointDyadicSumsetBounds := by
  obtain ⟨d, J, hB⟩ := h
  refine ⟨d, 0, 0, J, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hsid, hcount, hsep⟩ := hB N
  have hS s : IsSidon (B s : Set ℕ) := fun a ha u hu b hb v hv h ↦ hsid s a ha b hb u hu v hv h
  refine ⟨Finset.Icc J N, B, hpos, fun j hj hjN ↦ ⟨j, Finset.mem_Icc.mpr ⟨hj,hjN⟩, le_rfl, by simp⟩, ?_⟩
  intro s hs
  obtain ⟨hsJ, hsN⟩ := Finset.mem_Icc.mp hs
  refine ⟨hcount s hsJ hsN, ?_, ?_⟩
  · rw [self_sumset_full _ (hS s)]
    exact Nat.le_add_right _ _
  · intro r _ hr hrs
    have h : Disjoint (positiveDifferences (B r)) (positiveDifferences (B s)) := by
      apply Finset.disjoint_left.mpr
      intro t ht₁ ht₂
      obtain ⟨a, ha, b, hb, hab, he⟩ := mem_positiveDifferences.mp ht₁
      obtain ⟨u, hu, v, hv, huv, hf⟩ := mem_positiveDifferences.mp ht₂
      exact hsep r s (by omega) hrs a ha b hb u hu v hv hab huv (he.trans hf.symm)
    rw [mixed_sumset_full _ _ h]
    exact Nat.le_add_right _ _

private lemma nearby_iff_checkpoint_sumset_bounds : NearbyDyadicSidon ↔ CheckpointDyadicSumsetBounds :=
  ⟨checkpoint_sumset_bounds_of_nearby,
    fun h ↦ nearby_iff_checkpoint_dyadic_sidon.mpr
      (checkpoint_dyadic_sidon_of_checkpoint_sumset_bounds h)⟩

theorem OMA.solution : type_of% @Erdos1191.erdos_1191.parts.ii := by
  have hpacking : CheckpointDyadicSumsetBounds := by
    sorry
  obtain ⟨d, J, hB⟩ := nearby_iff_checkpoint_sumset_bounds.mpr hpacking
  obtain ⟨E, e, hsum, hsize⟩ := Codex1191.dyadic_additive_code
  obtain ⟨D, J₀, hfinite⟩ := coded_finite_witness d J hB E e hsum hsize
  obtain ⟨A, hSidon, hcount⟩ := sidon_of_finite_dyadic_witnesses D J₀ hfinite
  exact ⟨A, infinite_of_dyadic_counts A D J₀ hcount, hSidon, density_from_dyadic_counts A D J₀ hcount⟩
