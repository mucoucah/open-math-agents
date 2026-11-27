import FormalConjectures.ErdosProblems.«78»

-- Problem: Erdős Problem 78 — li
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/78.lean:138 (declaration Erdos78.erdos_78.variants.li)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Reduction from a two-source disperser to the weakly explicit Ramsey bound. -/

open Erdos78 Filter ComplexityTheory

namespace Erdos78Li

/-- Every rectangle of the indicated size contains both output values. -/
def Disperses {d : ℕ} (color : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (k : ℕ) : Prop :=
  ∀ A B : Finset (Fin d → Bool), k ≤ A.card → k ≤ B.card →
    ∀ b : Bool, ∃ x ∈ A, ∃ y ∈ B, color x y = b

def bits (d n : ℕ) : Fin d → Bool := fun i => n.testBit i

lemma encodeNat_eq_bits (n : ℕ) : Computability.encodeNat n = n.bits := by
  have hpos (p : PosNum) : Computability.encodePosNum p = (p : ℕ).bits := by
    induction p with
    | one => simp [Computability.encodePosNum]
    | bit0 p ih =>
      have hp : (p : ℕ) ≠ 0 := (PosNum.cast_pos p).ne'
      have hcast : (p.bit0 : ℕ) = 2 * (p : ℕ) := by
        rw [PosNum.cast_bit0, two_mul]
      rw [hcast, Nat.bit0_bits _ hp, Computability.encodePosNum, ih]
    | bit1 p ih =>
      have hcast : (p.bit1 : ℕ) = 2 * (p : ℕ) + 1 := by
        rw [PosNum.cast_bit1, two_mul]
      rw [hcast, Nat.bit1_bits, Computability.encodePosNum, ih]
  have hnum (p : Num) : Computability.encodeNum p = (p : ℕ).bits := by
    cases p with
    | zero => rfl
    | pos p => exact hpos p
  simpa only [Computability.encodeNat, Num.to_of_nat] using hnum (n : Num)

lemma bits_eq_getD_encodeNat {d : ℕ} (n : ℕ) (i : Fin d) :
    bits d n i = (Computability.encodeNat n)[i.val]?.getD false := by
  rw [bits, encodeNat_eq_bits, Nat.testBit_eq_inth, List.getI_eq_getElem?_getD]
  rfl

lemma encode_query (s : List Bool) (u v : ℕ) :
    BitstringEncoding.bitEncode (s, u, v) =
      BitstringEncoding.delimit (s.flatMap fun b => [true, b, false]) ++
        (BitstringEncoding.delimit u.bits ++ v.bits) := by
  have h (s : List Bool) :
      BitstringEncoding.bitEncode s = s.flatMap fun b => [true, b, false] := by
    induction s with
    | nil => rfl
    | cons b s ih =>
      change true :: b :: false :: BitstringEncoding.bitEncode s =
        true :: b :: false :: (s.flatMap fun b => [true, b, false])
      rw [ih]
  change BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++
    (BitstringEncoding.delimit (Computability.encodeNat u) ++ Computability.encodeNat v) = _
  rw [h, encodeNat_eq_bits, encodeNat_eq_bits]

def width (n : ℕ) : ℕ := n.log2 + 1

def orderedAdj (color : (d : ℕ) → (Fin d → Bool) → (Fin d → Bool) → Bool) :
    List Bool × ℕ × ℕ → Bool :=
  fun (s, u, v) =>
    color (width s.length) (bits _ (min u v)) (bits _ (max u v))

lemma lt_two_pow_width (n : ℕ) : n < 2 ^ width n := by
  rw [width, Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by decide) n

lemma two_pow_width_le (n : ℕ) : 2 ^ width n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n
    decide
  · rw [width, Nat.log2_eq_log_two, pow_succ']
    exact Nat.mul_le_mul_left 2 ((Nat.pow_log_le_self 2 hn).trans (Nat.le_succ n))

lemma length_encode_query (s : List Bool) (u v : ℕ) :
    (BitstringEncoding.bitEncode (s, u, v)).length =
      6 * s.length + 2 * u.bits.length + v.bits.length + 2 := by
  have hs (s : List Bool) : (s.flatMap fun b => [true, b, false]).length = 3 * s.length := by
    induction s with
    | nil => rfl
    | cons b l ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
      simp
      omega
  rw [encode_query]
  simp only [List.length_append, BitstringEncoding.length_delimit, hs]
  omega

/-- A runtime exponential in the vertex bit width is permitted by the unary input. -/
lemma orderedAdj_isPolyTime_of_runtime
    (color : (d : ℕ) → (Fin d → Bool) → (Fin d → Bool) → Bool)
    (machine : Turing.TM2ComputableAux Bool Bool) (C E : ℕ)
    (h : ∀ (s : List Bool) (u v : ℕ),
      Turing.TM2OutputsInTime machine.tm
        ((BitstringEncoding.bitEncode (s, u, v)).map machine.inputAlphabet.invFun)
        (some [machine.outputAlphabet.invFun (orderedAdj color (s, u, v))])
        (C * (2 ^ width s.length + u.bits.length + v.bits.length + 1) ^ E)) :
    IsPolyTime (orderedAdj color) := by
  let p : Polynomial ℕ := Polynomial.C C * (Polynomial.X + 1) ^ E
  refine ⟨⟨machine, p, ?_⟩⟩
  rintro ⟨s, u, v⟩
  have hle : 2 ^ width s.length + u.bits.length + v.bits.length + 1 ≤
      (BitstringEncoding.bitEncode (s, u, v)).length + 1 := by
    rw [length_encode_query]
    have hwidth := two_pow_width_le s.length
    omega
  have heval : p.eval (BitstringEncoding.bitEncode (s, u, v)).length =
      C * ((BitstringEncoding.bitEncode (s, u, v)).length + 1) ^ E := by
    simp [p]
  have hbound : C * (2 ^ width s.length + u.bits.length + v.bits.length + 1) ^ E ≤
      p.eval (BitstringEncoding.bitEncode (s, u, v)).length := by
    rw [heval]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle _)
  exact ⟨(h s u v).toEvalsTo, (h s u v).steps_le_m.trans hbound⟩

lemma bits_injective_on {d n : ℕ} (h : n ≤ 2 ^ d) :
    Function.Injective (fun v : Fin n => bits d v.val) := by
  intro u v huv
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < d
  · exact congrFun huv ⟨i, hi⟩
  · have hp : n ≤ 2 ^ i := h.trans (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_eq_false_of_lt (u.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (v.isLt.trans_le hp)]

/-- Two consecutive blocks in the ordered enumeration of a sufficiently large set. -/
lemma exists_separated_blocks {α : Type*} [LinearOrder α] (s : Finset α) {k : ℕ}
    (h : 2 * k ≤ s.card) :
    ∃ A B : Finset α, A ⊆ s ∧ B ⊆ s ∧ A.card = k ∧ B.card = k ∧
      ∀ x ∈ A, ∀ y ∈ B, x < y := by
  let e := s.orderEmbOfFin rfl
  let first : Fin k ↪ Fin s.card :=
    ⟨fun i => ⟨i.val, by omega⟩,
      fun i j hij => Fin.ext (congrArg (fun x : Fin s.card => x.val) hij)⟩
  let second : Fin k ↪ Fin s.card :=
    ⟨fun i => ⟨k + i.val, by omega⟩, fun i j hij => by
      apply Fin.ext
      have heq : k + i.val = k + j.val := congrArg Fin.val hij
      omega⟩
  refine ⟨Finset.univ.map (first.trans e.toEmbedding),
    Finset.univ.map (second.trans e.toEmbedding), ?_, ?_, by simp, by simp, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact s.orderEmbOfFin_mem rfl (first i)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact s.orderEmbOfFin_mem rfl (second i)
  · intro x hx y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
    apply e.strictMono
    change i.val < k + j.val
    omega

lemma orderedAdj_adj_iff
    (color : (d : ℕ) → (Fin d → Bool) → (Fin d → Bool) → Bool)
    {n : ℕ} {u v : Fin n} (huv : u < v) :
    (explicitGraph (orderedAdj color) n).Adj u v ↔
      color (width n) (bits _ u.val) (bits _ v.val) = true := by
  have hval : u.val ≤ v.val := huv.le
  simp [explicitGraph, orderedAdj, huv.ne, min_eq_left hval, max_eq_right hval,
    min_eq_right hval, max_eq_left hval]
  exact congrArg (fun d => color (width d) (bits _ u.val) (bits _ v.val))
    List.length_replicate

lemma noHomogeneousSet_of_disperses
    (color : (d : ℕ) → (Fin d → Bool) → (Fin d → Bool) → Bool)
    {n k m : ℕ} (hm : 2 * k ≤ m)
    (hcolor : Disperses (color (width n)) k) :
    NoHomogeneousSet (explicitGraph (orderedAdj color) n) m := by
  let f : Fin n ↪ (Fin (width n) → Bool) :=
    ⟨fun v => bits _ v.val, bits_injective_on (lt_two_pow_width n).le⟩
  have witness (s : Finset (Fin n)) (hs : s.card = m) (b : Bool) :
      ∃ u ∈ s, ∃ v ∈ s, u < v ∧
        color (width n) (bits _ u.val) (bits _ v.val) = b := by
    obtain ⟨A, B, hAs, hBs, hA, hB, hlt⟩ := exists_separated_blocks s (hs ▸ hm)
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      hcolor (A.map f) (B.map f) (by simp [hA]) (by simp [hB]) b
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact ⟨u, hAs hu, v, hBs hv, hlt u hu v hv, hxy⟩
  constructor
  · intro s hs
    obtain ⟨u, hu, v, hv, huv, hcoloruv⟩ := witness s hs.card_eq false
    have hadj := (orderedAdj_adj_iff color huv).mp (hs.isClique hu hv huv.ne)
    rw [hcoloruv] at hadj
    contradiction
  · intro s hs
    obtain ⟨u, hu, v, hv, huv, hcoloruv⟩ := witness s hs.card_eq true
    have hnon := (SimpleGraph.compl_adj _ _ _).mp (hs.isClique hu hv huv.ne)
    exact hnon.2 ((orderedAdj_adj_iff color huv).mpr hcoloruv)

lemma tendsto_width_atTop : Tendsto width atTop atTop := by
  refine tendsto_atTop.2 fun d => ?_
  filter_upwards [eventually_ge_atTop (2 ^ d : ℕ)] with n hn
  have hnpos : n ≠ 0 := (Nat.pow_pos (by decide : 0 < 2)).trans_le hn |>.ne'
  have hd := (Nat.le_log_iff_pow_le (by decide : 1 < 2) hnpos).2 hn
  rw [width, Nat.log2_eq_log_two]
  omega

lemma eventually_width_pow_le (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2 * width n ^ D ≤ ⌈(Real.log n) ^ (D + 1)⌉₊ := by
  let K : ℝ := 1 / Real.log 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), (tendsto_atTop.1 hlog) 1,
    (tendsto_atTop.1 hlog) (2 * K ^ D)] with n hn hnlog hlarge
  have hnpos : n ≠ 0 := by omega
  have hpow : (2 : ℝ) ^ n.log2 ≤ (n : ℝ) := by
    rw [Nat.log2_eq_log_two]
    exact_mod_cast Nat.pow_log_le_self 2 hnpos
  have hmul : (n.log2 : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h
  have hwidth : (width n : ℝ) ≤ K * Real.log n := by
    have h := (le_div_iff₀ hlog2).2 hmul
    have hdiv : Real.log n / Real.log 2 = (1 / Real.log 2) * Real.log n := by ring
    rw [hdiv] at h
    simp only [width, Nat.cast_add, Nat.cast_one, K, add_mul, one_mul]
    exact add_le_add h hnlog
  have hbound : ((2 * width n ^ D : ℕ) : ℝ) ≤ (Real.log n) ^ (D + 1) := by
    push_cast
    calc
      2 * (width n : ℝ) ^ D ≤ 2 * (K * Real.log n) ^ D :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hwidth _) (by norm_num)
      _ = (2 * K ^ D) * (Real.log n) ^ D := by rw [mul_pow, mul_assoc]
      _ ≤ Real.log n * (Real.log n) ^ D :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = (Real.log n) ^ (D + 1) := by rw [pow_succ']
  exact_mod_cast hbound.trans (Nat.le_ceil _)

theorem from_disperser (D : ℕ)
    (color : (d : ℕ) → (Fin d → Bool) → (Fin d → Bool) → Bool)
    (htime : IsPolyTime (orderedAdj color))
    (hcolor : ∀ᶠ d in atTop, Disperses (color d) (d ^ D)) :
    ∃ C > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (explicitGraph adj n) ⌈(Real.log n) ^ C⌉₊ := by
  refine ⟨((D + 1 : ℕ) : ℝ), by positivity, orderedAdj color, htime, ?_⟩
  filter_upwards [tendsto_width_atTop.eventually hcolor, eventually_width_pow_le D]
    with n hn hthreshold
  rw [Real.rpow_natCast]
  exact noHomogeneousSet_of_disperses color hthreshold hn

/-- The probability of a true output for independent uniform inputs from A and B. -/
noncomputable def trueProbability {d : ℕ}
    (color : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (A B : Finset (Fin d → Bool)) : ℝ := by
  classical
  exact (((A ×ˢ B).filter fun p => color p.1 p.2 = true).card : ℝ) /
    ((A.card : ℝ) * (B.card : ℝ))

lemma disperses_of_bias_bound {d k : ℕ}
    (color : (Fin d → Bool) → (Fin d → Bool) → Bool)
    (hbias : ∀ A B, k ≤ A.card → k ≤ B.card →
      |trueProbability color A B - 1 / 2| < 1 / 2) :
    Disperses color k := by
  classical
  intro A B hA hB b
  let S := A ×ˢ B
  let T := S.filter fun p => color p.1 p.2 = true
  have hb := abs_lt.mp (hbias A B hA hB)
  have hprob : trueProbability color A B = (T.card : ℝ) / (S.card : ℝ) := by
    simp [trueProbability, T, S]
  rw [hprob] at hb
  have hprobPos : 0 < (T.card : ℝ) / (S.card : ℝ) := by linarith [hb.1]
  have hprobLt : (T.card : ℝ) / (S.card : ℝ) < 1 := by linarith [hb.2]
  have hS : 0 < (S.card : ℝ) := by
    by_contra! h
    have heq : (S.card : ℝ) = 0 := le_antisymm h (by positivity)
    simp [heq] at hprobPos
  have hTpos : 0 < T.card := by
    have h := (lt_div_iff₀ hS).mp hprobPos
    simpa using h
  have hTlt : T.card < S.card := by
    have h := (div_lt_iff₀ hS).mp hprobLt
    simpa using h
  cases b
  · obtain ⟨p, hp, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hTlt
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hp
    refine ⟨p.1, hpA, p.2, hpB, ?_⟩
    exact Bool.eq_false_iff.mpr fun htrue => hnot (Finset.mem_filter.mpr ⟨hp, htrue⟩)
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp hTpos
    obtain ⟨hpS, hptrue⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hpS
    exact ⟨p.1, hpA, p.2, hpB, hptrue⟩

/-- A one-bit extractor guarantee for flat sources with min-entropy measured in nats. -/
def ExtractsFromFlatSources {d : ℕ}
    (color : (Fin d → Bool) → (Fin d → Bool) → Bool) (entropy : ℝ) : Prop :=
  ∀ A B : Finset (Fin d → Bool), A.Nonempty → B.Nonempty →
    entropy ≤ Real.log A.card → entropy ≤ Real.log B.card →
    |trueProbability color A B - 1 / 2| < 1 / 2

lemma eventually_disperses_of_flat_extractor (K : ℝ)
    (color : (d : ℕ) → (Fin d → Bool) → (Fin d → Bool) → Bool)
    (h : ∀ᶠ d in atTop, ExtractsFromFlatSources (color d) (K * Real.log d)) :
    ∃ D : ℕ, ∀ᶠ d in atTop, Disperses (color d) (d ^ D) := by
  obtain ⟨D, hD⟩ := exists_nat_ge K
  refine ⟨D, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with d hd hpos
  apply disperses_of_bias_bound
  intro A B hA hB
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hpowPos : 0 < d ^ D := Nat.pow_pos (by omega)
  have hlog {m : ℕ} (hm : d ^ D ≤ m) : K * Real.log d ≤ Real.log m := by
    have hm' : (d : ℝ) ^ D ≤ (m : ℝ) := by exact_mod_cast hm
    calc
      K * Real.log d ≤ (D : ℝ) * Real.log d :=
        mul_le_mul_of_nonneg_right hD (Real.log_natCast_nonneg _)
      _ = Real.log ((d : ℝ) ^ D) := (Real.log_pow _ _).symm
      _ ≤ Real.log m := Real.log_le_log (pow_pos hdpos _) hm'
  exact hd A B (Finset.card_pos.mp (hpowPos.trans_le hA))
    (Finset.card_pos.mp (hpowPos.trans_le hB)) (hlog hA) (hlog hB)

end Erdos78Li

theorem OMA.solution : type_of% @Erdos78.erdos_78.variants.li := by
  obtain ⟨K, color, htime, hextract⟩ :
      ∃ (K : ℝ) (color : (d : ℕ) → (Fin d → Bool) → (Fin d → Bool) → Bool),
        IsPolyTime (Erdos78Li.orderedAdj color) ∧
        ∀ᶠ d in atTop, Erdos78Li.ExtractsFromFlatSources (color d) (K * Real.log d) := by
    sorry
  obtain ⟨D, hdisperse⟩ := Erdos78Li.eventually_disperses_of_flat_extractor K color hextract
  exact Erdos78Li.from_disperser D color htime hdisperse
