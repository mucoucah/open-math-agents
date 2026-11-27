import FormalConjectures.ErdosProblems.«161»
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.Fin.Tuple
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

-- Problem: Erdős Problem 161 — i (it asks for a value)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/161.lean:50 (declaration Erdos161.erdos_161.parts.i; placeholder Erdos161.erdos_161.parts.i.answer := sorry)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Give the value explicitly as OMA.answer (same type as the placeholder; not built from Erdos161.…,
-- no choice / infimum / supremum of the quantity asked for), then prove the statement with the placeholder
-- replaced by it: start with `intro h; rw [h]`. No sorry, no axiom, no native_decide. A person checks the answer.

/-! Elementary bounds for the balanced coloring thresholds. -/

namespace OMA.BalancedColoring

open Filter Asymptotics Finset

open scoped Classical in
private def Feasible (n t : ℕ) (α : ℝ) (m : ℕ) : Prop :=
  ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
    0 < count ∧ α * (X.card.choose t : ℝ) ≤ count

private lemma feasible_succ (n t : ℕ) (α : ℝ) : Feasible n t α (n + 1) := by
  refine ⟨fun _ ↦ false, fun X hX ↦ ?_⟩
  have hcard : X.card ≤ n := by simpa using Finset.card_le_univ X
  omega

private lemma threshold_feasible (n t : ℕ) (α : ℝ) :
    Feasible n t α (Hypergraph.balancedColoringThreshold n t α) := by
  change sInf {m | Feasible n t α m} ∈ {m | Feasible n t α m}
  exact Nat.sInf_mem ⟨n + 1, feasible_succ n t α⟩

private lemma threshold_le {n t m : ℕ} {α : ℝ} (h : Feasible n t α m) :
    Hypergraph.balancedColoringThreshold n t α ≤ m := by
  exact Nat.sInf_le (show m ∈ {m | Feasible n t α m} from h)

private lemma threshold_mono (n t : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    Hypergraph.balancedColoringThreshold n t α ≤
      Hypergraph.balancedColoringThreshold n t β := by
  classical
  obtain ⟨c, hc⟩ := threshold_feasible n t β
  apply threshold_le
  refine ⟨c, fun X hX b ↦ ?_⟩
  obtain ⟨hpos, hdensity⟩ := hc X hX b
  exact ⟨hpos, (mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg _)).trans hdensity⟩

private lemma threshold_one_lower (n : ℕ) (α : ℝ) :
    n < 2 * Hypergraph.balancedColoringThreshold n 1 α := by
  classical
  obtain ⟨c, hc⟩ := threshold_feasible n 1 α
  let X := (univ : Finset (Fin n)).filter (fun v ↦ c {v} = true)
  let Y := (univ : Finset (Fin n)).filter (fun v ↦ c {v} ≠ true)
  have hsum : X.card + Y.card = n := by
    simpa [X, Y] using
      (Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
        (p := fun v ↦ c {v} = true))
  have small (Z : Finset (Fin n)) (b : Bool) (hz : ∀ v ∈ Z, c {v} ≠ b) :
      Z.card < Hypergraph.balancedColoringThreshold n 1 α := by
    by_contra! h
    have hp := (hc Z h b).1
    obtain ⟨e, he⟩ := Finset.card_pos.mp hp
    obtain ⟨heZ, he1⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp he1
    exact hz v (heZ (Finset.mem_singleton_self v)) (Finset.mem_filter.mp he).2
  have hx := small X false (by
    intro v hv
    have h := (Finset.mem_filter.mp hv).2
    simp [h])
  have hy := small Y true (fun v hv ↦ (Finset.mem_filter.mp hv).2)
  omega

private lemma threshold_one_theta (α β : ℝ) :
    (fun n ↦ (Hypergraph.balancedColoringThreshold n 1 α : ℝ)) =Θ[atTop]
      (fun n ↦ (Hypergraph.balancedColoringThreshold n 1 β : ℝ)) := by
  have bound (a b : ℝ) : (fun n ↦ (Hypergraph.balancedColoringThreshold n 1 a : ℝ))
      =O[atTop] (fun n ↦ (Hypergraph.balancedColoringThreshold n 1 b : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 2 (Filter.Eventually.of_forall fun n ↦ ?_)
    have h : Hypergraph.balancedColoringThreshold n 1 a ≤
        2 * Hypergraph.balancedColoringThreshold n 1 b :=
      (threshold_le (feasible_succ n 1 a)).trans (threshold_one_lower n b)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
      (show (Hypergraph.balancedColoringThreshold n 1 a : ℝ) ≤
          2 * (Hypergraph.balancedColoringThreshold n 1 b : ℝ) by exact_mod_cast h)
  exact ⟨bound α β, bound β α⟩

private def GraphMono {V : Type*} [DecidableEq V]
    (c : Finset V → Bool) (X : Finset V) (b : Bool) : Prop :=
  ∀ e ∈ X.powersetCard 2, c e = b

private lemma graphMono_insert {V : Type*} [DecidableEq V] {c : Finset V → Bool}
    {X : Finset V} {v : V} {b : Bool} (hX : GraphMono c X b)
    (hstar : ∀ w ∈ X, c {v, w} = b) : GraphMono c (insert v X) b := by
  intro e he
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
  by_cases hve : v ∈ e
  · have herase : (e.erase v).card = 1 := by
      rw [Finset.card_erase_of_mem hve, hcard]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp herase
    have hw' : w ∈ e.erase v := by simp [hw]
    have hwX : w ∈ X :=
      ((Finset.mem_insert.mp (hsub (Finset.mem_of_mem_erase hw'))).resolve_left
        (Finset.ne_of_mem_erase hw'))
    have heq : insert v (e.erase v) = e := Finset.insert_erase hve
    rw [hw] at heq
    rw [← heq]
    exact hstar w hwX
  · apply hX
    exact Finset.mem_powersetCard.mpr ⟨fun w hw ↦
      (Finset.mem_insert.mp (hsub hw)).resolve_left (fun h ↦ hve (h ▸ hw)), hcard⟩

private lemma graph_ramsey {V : Type*} [DecidableEq V] (c : Finset V → Bool)
    (a b : ℕ) (X : Finset V) (hX : 2 ^ (a + b) ≤ X.card) :
    (∃ Y ⊆ X, Y.card = a ∧ GraphMono c Y false) ∨
      (∃ Y ⊆ X, Y.card = b ∧ GraphMono c Y true) := by
  classical
  by_cases ha : a = 0
  · exact Or.inl ⟨∅, empty_subset _, by simp [ha], by simp [GraphMono]⟩
  by_cases hb : b = 0
  · exact Or.inr ⟨∅, empty_subset _, by simp [hb], by simp [GraphMono]⟩
  have hpos : 0 < X.card := (pow_pos (by decide) _).trans_le hX
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  let U := (X.erase v).filter (fun w ↦ c {v, w} = false)
  let W := (X.erase v).filter (fun w ↦ c {v, w} ≠ false)
  have hsplit : U.card + W.card = X.card - 1 := by
    rw [← Finset.card_erase_of_mem hv]
    exact Finset.card_filter_add_card_filter_not (fun w ↦ c {v, w} = false)
  have hpow : 2 ^ (a + b) = 2 ^ (a + b - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hlarge : 2 ^ (a + b - 1) ≤ U.card ∨ 2 ^ (a + b - 1) ≤ W.card := by
    omega
  rcases hlarge with hU | hW
  · have hU' : 2 ^ ((a - 1) + b) ≤ U.card := by
      convert hU using 2
      all_goals omega
    rcases graph_ramsey c (a - 1) b U hU' with ⟨Y, hYU, hYa, hY⟩ | ⟨Y, hYU, hYb, hY⟩
    · have hvY : v ∉ Y := fun h ↦ Finset.notMem_erase v X
          (Finset.mem_filter.mp (hYU h)).1
      refine Or.inl ⟨insert v Y, insert_subset hv ?_, ?_, graphMono_insert hY ?_⟩
      · exact hYU.trans (Finset.filter_subset _ _ |>.trans (Finset.erase_subset _ _))
      · rw [Finset.card_insert_of_notMem hvY, hYa]
        omega
      · exact fun w hw ↦ (Finset.mem_filter.mp (hYU hw)).2
    · exact Or.inr ⟨Y, hYU.trans (Finset.filter_subset _ _ |>.trans
        (Finset.erase_subset _ _)), hYb, hY⟩
  · have hW' : 2 ^ (a + (b - 1)) ≤ W.card := by
      convert hW using 2
      all_goals omega
    rcases graph_ramsey c a (b - 1) W hW' with ⟨Y, hYW, hYa, hY⟩ | ⟨Y, hYW, hYb, hY⟩
    · exact Or.inl ⟨Y, hYW.trans (Finset.filter_subset _ _ |>.trans
        (Finset.erase_subset _ _)), hYa, hY⟩
    · have hvY : v ∉ Y := fun h ↦ Finset.notMem_erase v X
          (Finset.mem_filter.mp (hYW h)).1
      refine Or.inr ⟨insert v Y, insert_subset hv ?_, ?_, graphMono_insert hY ?_⟩
      · exact hYW.trans (Finset.filter_subset _ _ |>.trans (Finset.erase_subset _ _))
      · rw [Finset.card_insert_of_notMem hvY, hYb]
        omega
      · intro w hw
        have hn := (Finset.mem_filter.mp (hYW hw)).2
        exact Bool.eq_true_of_not_eq_false hn
termination_by a + b
decreasing_by all_goals omega

private lemma threshold_two_lower_exp (n : ℕ) (α : ℝ) :
    n < 4 ^ Hypergraph.balancedColoringThreshold n 2 α := by
  classical
  let m := Hypergraph.balancedColoringThreshold n 2 α
  by_contra! hn
  obtain ⟨c, hc⟩ := threshold_feasible n 2 α
  have hs : 2 ^ (m + m) ≤ (univ : Finset (Fin n)).card := by
    simpa [pow_add, ← mul_pow] using hn
  have impossible (Y : Finset (Fin n)) (hY : Y.card = m) (b : Bool)
      (hm : GraphMono c Y b) : False := by
    have hp := (hc Y hY.ge (!b)).1
    obtain ⟨e, he⟩ := Finset.card_pos.mp hp
    have h1 := hm e (Finset.mem_filter.mp he).1
    have h2 := (Finset.mem_filter.mp he).2
    rw [h1] at h2
    cases b <;> cases h2
  rcases graph_ramsey c m m univ hs with ⟨Y, _, he, hm⟩ | ⟨Y, _, he, hm⟩
  · exact impossible Y he false hm
  · exact impossible Y he true hm

private lemma exists_tilt (α : ℝ) (hα : α < 1 / 2) :
    ∃ θ : ℝ, 0 < θ ∧
      (Real.exp (θ * α) + Real.exp (θ * (α - 1))) / 2 < 1 := by
  let f (x : ℝ) := (Real.exp (x * α) + Real.exp (x * (α - 1))) / 2
  have h0 : f 0 = 1 := by norm_num [f]
  have hd : HasDerivAt f ((α + (α - 1)) / 2) 0 := by
    have h₁ := ((hasDerivAt_id (0 : ℝ)).mul_const α).exp
    have h₂ := ((hasDerivAt_id (0 : ℝ)).mul_const (α - 1)).exp
    simpa [f] using (h₁.add h₂).div_const 2
  by_contra! h
  have hmin : IsMinOn f (Set.Ici 0) 0 := by
    intro x hx
    rcases (show 0 ≤ x from hx).eq_or_lt with he | hp
    · simp [← he]
    · rw [h0]
      exact h x hp
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Set.Ici 0) (0 : ℝ) := by
    apply one_mem_posTangentConeAt_iff_mem_closure.mpr
    rw [Set.inter_eq_left.mpr Set.Ioi_subset_Ici_self, closure_Ioi]
    exact (show (0 : ℝ) ≤ 0 from le_rfl)
  have hn : 0 ≤ (α + (α - 1)) / 2 := by
    simpa using hmin.localize.hasFDerivWithinAt_nonneg
      hd.hasFDerivAt.hasFDerivWithinAt hcone
  linarith

open scoped Classical in
private noncomputable def tilt {E : Type*}
    (S : Finset E) (c : E → Bool) (b : Bool) (α θ : ℝ) : ℝ :=
  Real.exp (θ * (α * (S.card : ℝ) - ((S.filter fun e ↦ c e = b).card : ℝ)))

private lemma tilt_sum {E : Type*} [Fintype E] [DecidableEq E] (S : Finset E) (b : Bool) (α θ : ℝ) :
    ∑ c : E → Bool, tilt S c b α θ =
      (Fintype.card (E → Bool) : ℝ) *
        ((Real.exp (θ * α) + Real.exp (θ * (α - 1))) / 2) ^ S.card := by
  classical
  let q := (Real.exp (θ * α) + Real.exp (θ * (α - 1))) / 2
  let w (e : E) (v : Bool) : ℝ :=
    if e ∈ S then Real.exp (θ * (α - if v = b then 1 else 0)) else 1
  have hweight (c : E → Bool) : tilt S c b α θ = ∏ e : E, w e (c e) := by
    rw [show (∏ e : E, w e (c e)) =
      ∏ e : E, if e ∈ S then Real.exp (θ * (α - if c e = b then 1 else 0)) else 1
      from rfl]
    rw [Finset.prod_ite_mem_eq, ← Real.exp_sum]
    unfold tilt
    congr 1
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  have hsite (e : E) : (∑ v : Bool, w e v) = 2 * (if e ∈ S then q else 1) := by
    by_cases he : e ∈ S
    · cases b <;> simp [w, he, q] <;> ring
    · simp [w, he]
  simp_rw [hweight]
  rw [← Fintype.prod_sum]
  simp_rw [hsite]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
  simp [q, div_pow]

private lemma exists_coloring_of_tilt {I E : Type*} [Fintype E] [DecidableEq E]
    (A : Finset I) (F : I → Finset E) {α θ : ℝ} (hθ : 0 < θ)
    (h : 2 * (∑ X ∈ A,
      ((Real.exp (θ * α) + Real.exp (θ * (α - 1))) / 2) ^ (F X).card) < 1) :
    ∃ c : E → Bool, ∀ X ∈ A, ∀ b : Bool,
      α * ((F X).card : ℝ) < (((F X).filter fun e ↦ c e = b).card : ℝ) := by
  classical
  let q := (Real.exp (θ * α) + Real.exp (θ * (α - 1))) / 2
  let N : ℝ := Fintype.card (E → Bool)
  let P (c : E → Bool) := ∑ X ∈ A, ∑ b : Bool, tilt (F X) c b α θ
  have hsum : (∑ c, P c) = N * (2 * ∑ X ∈ A, q ^ (F X).card) := by
    unfold P
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro X _
    rw [Finset.sum_comm]
    simp only [tilt_sum, Fintype.sum_bool]
    change N * q ^ (F X).card + N * q ^ (F X).card = N * (2 * q ^ (F X).card)
    ring
  have hN : 0 < N := by
    have : Nonempty (E → Bool) := ⟨fun _ ↦ true⟩
    exact Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨c, hc⟩ : ∃ c, P c < 1 := by
    by_contra! h'
    have hbig : N ≤ ∑ c, P c := by
      simpa [N] using (Finset.sum_le_sum (s := univ) (f := fun _ ↦ (1 : ℝ))
        (g := P) (fun c _ ↦ h' c))
    rw [hsum] at hbig
    exact (not_le_of_gt (by simpa using mul_lt_mul_of_pos_left h hN)) hbig
  refine ⟨c, fun X hX b ↦ ?_⟩
  have hterm : tilt (F X) c b α θ < 1 := calc
    _ ≤ ∑ b' : Bool, tilt (F X) c b' α θ :=
      Finset.single_le_sum (fun _ _ ↦ Real.exp_nonneg _) (mem_univ b)
    _ ≤ P c :=
      Finset.single_le_sum (f := fun Y ↦ ∑ b' : Bool, tilt (F Y) c b' α θ)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Real.exp_nonneg _) hX
    _ < 1 := hc
  unfold tilt at hterm
  rw [← Real.exp_zero, Real.exp_lt_exp] at hterm
  exact sub_neg.mp (neg_of_mul_neg_right hterm hθ.le)

private lemma choose_two_real {k : ℕ} (hk : 1 ≤ k) :
    (k.choose 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h := Nat.add_one_mul_choose_eq j 1
  simp only [Nat.choose_one_right, Nat.reduceAdd] at h
  have hr : ((j : ℝ) + 1) * j = (((j + 1).choose 2 : ℕ) : ℝ) * 2 := by
    exact_mod_cast h
  push_cast
  linarith

private lemma graph_tilt_power {n k : ℕ} {q : ℝ} (hn : 4 ≤ n) (hk : 2 ≤ k)
    (hq : 0 < q) (hbound : 4 * Real.log (n : ℝ) ≤ ((k : ℝ) - 1) * (-Real.log q)) :
    (n : ℝ) ^ k * q ^ k.choose 2 ≤ ((n : ℝ) ^ 2)⁻¹ := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog := Real.log_nonneg hn1
  have hprod := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg (α := ℝ) k)
  have hsmall := mul_le_mul_of_nonneg_right hk2 hlog
  calc
    (n : ℝ) ^ k * q ^ k.choose 2
      = Real.exp ((k : ℝ) * Real.log n + (k.choose 2 : ℝ) * Real.log q) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hn0, Real.exp_log hq]
    _ ≤ Real.exp (-((2 : ℕ) : ℝ) * Real.log n) := by
      apply Real.exp_le_exp.mpr
      rw [choose_two_real (by omega)]
      push_cast
      nlinarith only [hprod, hsmall]
    _ = ((n : ℝ) ^ 2)⁻¹ := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0]

private lemma tilt_bound_of_powers {n m t : ℕ} (hn : 4 ≤ n) {q : ℝ} (hq : 0 < q)
    (hbound : ∀ k : ℕ, m ≤ k → (n : ℝ) ^ k * q ^ k.choose t ≤ ((n : ℝ) ^ 2)⁻¹) :
    2 * (∑ X ∈ (univ : Finset (Finset (Fin n))).filter (fun X ↦ m ≤ X.card),
      q ^ (X.powersetCard t).card) < 1 := by
  classical
  let A := (univ : Finset (Finset (Fin n))).filter (fun X ↦ m ≤ X.card)
  let T := range (n + 1)
  have hmaps : ∀ X ∈ A, X.card ∈ T := by
    intro X _
    have hcard : X.card ≤ n := by simpa using Finset.card_le_univ X
    simpa [T]
  have hsum (k : ℕ) :
      (∑ X ∈ A.filter (fun X ↦ X.card = k), q ^ (X.powersetCard t).card) ≤
        ((n : ℝ) ^ 2)⁻¹ := by
    by_cases hk : m ≤ k
    · have hA : A.filter (fun X ↦ X.card = k) =
          (univ : Finset (Fin n)).powersetCard k := by
        ext X
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
          Finset.subset_univ]
        exact ⟨And.right, fun h ↦ ⟨h ▸ hk, h⟩⟩
      rw [hA]
      calc
        _ = ∑ _X ∈ (univ : Finset (Fin n)).powersetCard k, q ^ k.choose t := by
          apply Finset.sum_congr rfl
          intro X hX
          rw [Finset.card_powersetCard, (Finset.mem_powersetCard.mp hX).2]
        _ = (n.choose k : ℝ) * q ^ k.choose t := by simp
        _ ≤ (n : ℝ) ^ k * q ^ k.choose t :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow n k) (by positivity)
        _ ≤ _ := hbound k hk
    · have hA : A.filter (fun X ↦ X.card = k) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro X hX
        have hX1 := (Finset.mem_filter.mp hX).2
        have hX2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hX).1).2
        exact hk (hX1 ▸ hX2)
      rw [hA, Finset.sum_empty]
      positivity
  have htotal : (∑ X ∈ A, q ^ (X.powersetCard t).card) ≤
      (n + 1 : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    simpa [T] using (Finset.sum_le_sum (s := T) (fun k _ ↦ hsum k))
  change 2 * (∑ X ∈ A, q ^ (X.powersetCard t).card) < 1
  refine (mul_le_mul_of_nonneg_left htotal (by norm_num)).trans_lt ?_
  have hn' : 4 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) ^ 2 := by positivity
  rw [← mul_assoc, ← div_eq_mul_inv, div_lt_iff₀ hpos]
  nlinarith [sq_nonneg ((n : ℝ) - 4)]

private lemma graph_tilt_bound {n m : ℕ} (hn : 4 ≤ n) (hm : 2 ≤ m) {q : ℝ}
    (hq : 0 < q) (hq' : q < 1)
    (hbound : 4 * Real.log (n : ℝ) ≤ ((m : ℝ) - 1) * (-Real.log q)) :
    2 * (∑ X ∈ (univ : Finset (Finset (Fin n))).filter (fun X ↦ m ≤ X.card),
      q ^ (X.powersetCard 2).card) < 1 := by
  have hlog : 0 ≤ -Real.log q := neg_nonneg.mpr (Real.log_neg hq hq').le
  apply tilt_bound_of_powers hn hq
  intro k hk
  exact graph_tilt_power hn (hm.trans hk) hq (hbound.trans (mul_le_mul_of_nonneg_right
    (sub_le_sub_right (by exact_mod_cast hk) 1) hlog))

private lemma threshold_two_isBigO_log {α : ℝ} (ha : 0 ≤ α) (ha' : α < 1 / 2) :
    (fun n ↦ (Hypergraph.balancedColoringThreshold n 2 α : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  classical
  obtain ⟨θ, hθ, hq'⟩ := exists_tilt α ha'
  let q := (Real.exp (θ * α) + Real.exp (θ * (α - 1))) / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hd : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq')
  let K := 4 / (-Real.log q)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have htend : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine Asymptotics.IsBigO.of_bound (K + 3) ?_
  filter_upwards [eventually_ge_atTop (4 : ℕ), htend.eventually_ge_atTop 1] with n hn hlog
  let x := K * Real.log (n : ℝ)
  have hx : 0 ≤ x := mul_nonneg hK (le_trans zero_le_one hlog)
  let m := ⌈x⌉₊ + 2
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmx : x ≤ (m : ℝ) - 1 := by
    have hceil := Nat.le_ceil x
    simp [m]
    linarith
  have hdecay : 4 * Real.log (n : ℝ) ≤ ((m : ℝ) - 1) * (-Real.log q) := by
    calc
      _ = x * (-Real.log q) := by
        dsimp [x, K]
        rw [mul_right_comm, div_mul_cancel₀ _ hd.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hmx hd.le
  let A := (univ : Finset (Finset (Fin n))).filter (fun X ↦ m ≤ X.card)
  obtain ⟨col, hcol⟩ := exists_coloring_of_tilt A (fun X ↦ X.powersetCard 2)
    hθ (graph_tilt_bound hn hm hq hq' hdecay)
  have hfeas : Feasible n 2 α m := by
    refine ⟨col, fun X hX b ↦ ?_⟩
    have hX' : X ∈ A := by simp [A, hX]
    have hgood := hcol X hX' b
    rw [Finset.card_powersetCard] at hgood
    refine ⟨?_, hgood.le⟩
    exact_mod_cast (mul_nonneg ha (Nat.cast_nonneg _)).trans_lt hgood
  have hth : (Hypergraph.balancedColoringThreshold n 2 α : ℝ) ≤ (m : ℝ) :=
    Nat.cast_le.mpr (threshold_le hfeas)
  have hm' : (m : ℝ) ≤ x + 3 := by
    have hceil := Nat.ceil_lt_add_one hx
    simp [m]
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (le_trans zero_le_one hlog)]
  exact hth.trans (hm'.trans (by dsimp [x]; linarith))

private lemma log_isBigO_threshold_two (α : ℝ) :
    (fun n : ℕ ↦ Real.log (n : ℝ)) =O[atTop]
      (fun n ↦ (Hypergraph.balancedColoringThreshold n 2 α : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (Real.log 4) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn'
  have hexp : (n : ℝ) < (4 : ℝ) ^ Hypergraph.balancedColoringThreshold n 2 α := by
    exact_mod_cast threshold_two_lower_exp n α
  have hlog := Real.log_lt_log hn0 hexp
  rw [Real.log_pow] at hlog
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn'),
    abs_of_nonneg (Nat.cast_nonneg _), mul_comm]
  exact hlog.le

private lemma threshold_two_theta {α β : ℝ} (ha : α ∈ Set.Ico (0 : ℝ) (1 / 2))
    (hb : β ∈ Set.Ico (0 : ℝ) (1 / 2)) :
    (fun n ↦ (Hypergraph.balancedColoringThreshold n 2 α : ℝ)) =Θ[atTop]
      (fun n ↦ (Hypergraph.balancedColoringThreshold n 2 β : ℝ)) := by
  exact ⟨(threshold_two_isBigO_log ha.1 ha.2).trans (log_isBigO_threshold_two β),
    (threshold_two_isBigO_log hb.1 hb.2).trans (log_isBigO_threshold_two α)⟩

private lemma choose_lower {k t : ℕ} (hk : 2 * t ≤ k) :
    (k : ℝ) ^ t / ((2 : ℝ) ^ t * (t.factorial : ℝ)) ≤ (k.choose t : ℝ) := by
  have hkt : t ≤ k + 1 := by omega
  have hhalf : (k : ℝ) / 2 ≤ ((k + 1 - t : ℕ) : ℝ) := by
    rw [Nat.cast_sub hkt, Nat.cast_add, Nat.cast_one]
    have h : 2 * (t : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ (k : ℝ) / 2 by positivity) hhalf t
  have hfac : ((k + 1 - t : ℕ) : ℝ) ^ t ≤ (t.factorial : ℝ) * (k.choose t : ℝ) := by
    have h := Nat.pow_sub_le_descFactorial k t
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast h
  rw [← div_div, ← div_pow, div_le_iff₀ (by positivity)]
  simpa [mul_comm] using hpow.trans hfac

private lemma hypergraph_tilt_power {n k t : ℕ} {q : ℝ} (hn : 4 ≤ n) (hk : 2 ≤ k)
    (hq : 0 < q) (hbound : 2 * (k : ℝ) * Real.log n ≤ (k.choose t : ℝ) * (-Real.log q)) :
    (n : ℝ) ^ k * q ^ k.choose t ≤ ((n : ℝ) ^ 2)⁻¹ := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hsmall := mul_le_mul_of_nonneg_right hk2 (Real.log_nonneg hn1)
  calc
    _ = Real.exp ((k : ℝ) * Real.log n + (k.choose t : ℝ) * Real.log q) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hn0, Real.exp_log hq]
    _ ≤ Real.exp (-((2 : ℕ) : ℝ) * Real.log n) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith only [hbound, hsmall]
    _ = _ := by rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0]

private lemma threshold_isBigO_log_rpow {t : ℕ} (ht : 2 ≤ t) {α : ℝ}
    (ha : 0 ≤ α) (ha' : α < 1 / 2) :
    (fun n ↦ (Hypergraph.balancedColoringThreshold n t α : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ (((t - 1 : ℕ) : ℝ)⁻¹)) := by
  classical
  obtain ⟨θ, hθ, hq'⟩ := exists_tilt α ha'
  let q := (Real.exp (θ * α) + Real.exp (θ * (α - 1))) / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hd : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq')
  let D := (2 : ℝ) ^ t * (t.factorial : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  let d := -Real.log q / D
  have hd' : 0 < d := div_pos hd hD
  let r := ((t - 1 : ℕ) : ℝ)⁻¹
  let C := (2 / d) ^ r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht1 : 0 < ((t - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < t - 1 by omega)
  have htend : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine Asymptotics.IsBigO.of_bound (C + 1 + 2 * (t : ℝ)) ?_
  filter_upwards [eventually_ge_atTop (4 : ℕ), htend.eventually_ge_atTop 1] with n hn hlog
  let y := (Real.log (n : ℝ)) ^ r
  have hy : 1 ≤ y := Real.one_le_rpow hlog (inv_nonneg.mpr ht1.le)
  let x := C * y
  have hx : 0 ≤ x := mul_nonneg hC (zero_le_one.trans hy)
  let m := ⌈x⌉₊ + 2 * t
  have hc : ∀ k : ℕ, m ≤ k → (n : ℝ) ^ k * q ^ k.choose t ≤ ((n : ℝ) ^ 2)⁻¹ := by
    intro k hk
    have hkt : 2 * t ≤ k := by dsimp [m] at hk; omega
    have hxk : x ≤ (k : ℝ) :=
      (Nat.le_ceil x).trans (Nat.cast_le.mpr (by dsimp [m] at hk; omega))
    have hxp : x ^ (t - 1) = 2 / d * Real.log n := by
      have hnonneg : 0 ≤ 2 / d * Real.log (n : ℝ) := by positivity
      dsimp [x, C, y]
      rw [← Real.mul_rpow (by positivity) (zero_le_one.trans hlog),
        ← Real.rpow_natCast, ← Real.rpow_mul hnonneg]
      rw [show r * ((t - 1 : ℕ) : ℝ) = 1 from inv_mul_cancel₀ ht1.ne', Real.rpow_one]
    have hkp := pow_le_pow_left₀ hx hxk (t - 1)
    rw [hxp, div_mul_eq_mul_div, div_le_iff₀ hd'] at hkp
    have hmul := mul_le_mul_of_nonneg_left hkp (Nat.cast_nonneg (α := ℝ) k)
    have hchoose := mul_le_mul_of_nonneg_right (choose_lower hkt) hd.le
    change (k : ℝ) ^ t / D * (-Real.log q) ≤ _ at hchoose
    have heq : (k : ℝ) * ((k : ℝ) ^ (t - 1) * d) =
        (k : ℝ) ^ t / D * (-Real.log q) := by
      dsimp [d]
      rw [← mul_assoc, ← pow_succ' (k : ℝ) (t - 1), show t - 1 + 1 = t by omega]
      ring
    rw [heq] at hmul
    apply hypergraph_tilt_power hn (by omega) hq
    calc
      2 * (k : ℝ) * Real.log n = (k : ℝ) * (2 * Real.log n) := by ring
      _ ≤ (k.choose t : ℝ) * (-Real.log q) := hmul.trans hchoose
  let A := (univ : Finset (Finset (Fin n))).filter fun X ↦ m ≤ X.card
  obtain ⟨col, hcol⟩ := exists_coloring_of_tilt A (fun X ↦ X.powersetCard t) hθ
    (tilt_bound_of_powers hn hq hc)
  have hfeas : Feasible n t α m := by
    refine ⟨col, fun X hX b ↦ ?_⟩
    have hX' : X ∈ A := by simp [A, hX]
    have hgood := hcol X hX' b
    rw [Finset.card_powersetCard] at hgood
    refine ⟨?_, hgood.le⟩
    exact_mod_cast (mul_nonneg ha (Nat.cast_nonneg _)).trans_lt hgood
  have hth : (Hypergraph.balancedColoringThreshold n t α : ℝ) ≤ (m : ℝ) :=
    Nat.cast_le.mpr (threshold_le hfeas)
  have hm : (m : ℝ) ≤ x + 1 + 2 * (t : ℝ) := by
    have hceil := Nat.ceil_lt_add_one hx
    simp [m]
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change (Hypergraph.balancedColoringThreshold n t α : ℝ) ≤ (C + 1 + 2 * t) * |y|
  rw [abs_of_nonneg (zero_le_one.trans hy)]
  apply hth.trans (hm.trans ?_)
  dsimp [x]
  nlinarith only [hy, Nat.cast_nonneg (α := ℝ) t,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) t) (sub_nonneg.mpr hy)]

private noncomputable abbrev thresholdReal (t : ℕ) (α : ℝ) (n : ℕ) : ℝ :=
  Hypergraph.balancedColoringThreshold n t α

private lemma threshold_isBigO_mono {t : ℕ} {α β : ℝ} (h : α ≤ β) :
    thresholdReal t α =O[atTop] thresholdReal t β := by
  refine Asymptotics.IsBigO.of_bound' (Filter.Eventually.of_forall fun n ↦ ?_)
  change ‖(Hypergraph.balancedColoringThreshold n t α : ℝ)‖ ≤
    ‖(Hypergraph.balancedColoringThreshold n t β : ℝ)‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
    using (show (Hypergraph.balancedColoringThreshold n t α : ℝ) ≤
      Hypergraph.balancedColoringThreshold n t β by exact_mod_cast threshold_mono n t h)

private lemma threshold_theta_iff_of_anchor {t : ℕ} {α β : ℝ}
    (ha : α ∈ Set.Ico (0 : ℝ) (1 / 2)) (hb : β ∈ Set.Ico (0 : ℝ) (1 / 2))
    (hpos : ∀ a : ℝ, 0 < a → a < 1 / 2 →
      thresholdReal t a =Θ[atTop] thresholdReal t (1 / 4))
    (hzero : ¬ (thresholdReal t (1 / 4) =O[atTop] thresholdReal t 0)) :
    (thresholdReal t α =Θ[atTop] thresholdReal t β) ↔ (α = 0 ↔ β = 0) := by
  rcases ha.1.eq_or_lt with ha0 | ha0 <;> rcases hb.1.eq_or_lt with hb0 | hb0
  · subst α
    subst β
    exact ⟨fun _ ↦ Iff.rfl, fun _ ↦ Asymptotics.isTheta_refl _ _⟩
  · subst α
    constructor
    · intro h
      exact (hzero ((hpos β hb0 hb.2).2.trans h.2)).elim
    · intro h
      exact (hb0.ne' (h.mp rfl)).elim
  · subst β
    constructor
    · intro h
      exact (hzero ((hpos α ha0 ha.2).2.trans h.1)).elim
    · intro h
      exact (ha0.ne' (h.mpr rfl)).elim
  · have heq : (α = 0 ↔ β = 0) := by simp [ha0.ne', hb0.ne']
    exact ⟨fun _ ↦ heq, fun _ ↦ (hpos α ha0 ha.2).trans (hpos β hb0 hb.2).symm⟩

private lemma threshold_ge_of_sparse {n t : ℕ} {α B : ℝ}
    (hsparse : ∀ c : Finset (Fin n) → Bool,
      ∃ X : Finset (Fin n), B ≤ (X.card : ℝ) ∧ ∃ b : Bool,
        (((X.powersetCard t).filter (fun e ↦ c e = b)).card : ℝ) <
          α * (X.card.choose t : ℝ)) :
    B ≤ thresholdReal t α n := by
  classical
  obtain ⟨c, hc⟩ := threshold_feasible n t α
  obtain ⟨X, hX, b, hb⟩ := hsparse c
  have hsmall : X.card < Hypergraph.balancedColoringThreshold n t α :=
    lt_of_not_ge fun hsize ↦ hb.not_ge (hc X hsize b).2
  exact hX.trans (Nat.cast_le.mpr hsmall.le)

private noncomputable abbrev logScale (t n : ℕ) : ℝ :=
  (Real.log (n : ℝ)) ^ (((t - 1 : ℕ) : ℝ)⁻¹)

private lemma logScale_isBigO_of_sparse {t : ℕ} {α : ℝ}
    (hsparse : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ col : Finset (Fin n) → Bool,
        ∃ X : Finset (Fin n), c * logScale t n ≤ (X.card : ℝ) ∧ ∃ b : Bool,
          (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) <
            α * (X.card.choose t : ℝ)) :
    logScale t =O[atTop] thresholdReal t α := by
  classical
  obtain ⟨c, hc, hev⟩ := hsparse
  refine Asymptotics.IsBigO.of_bound (1 / c) ?_
  filter_upwards [hev, eventually_ge_atTop (1 : ℕ)] with n hn hn'
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn')
  have hscale : 0 ≤ logScale t n := Real.rpow_nonneg hlog _
  change ‖logScale t n‖ ≤ 1 / c * ‖(Hypergraph.balancedColoringThreshold n t α : ℝ)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale,
    abs_of_nonneg (Nat.cast_nonneg _), div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]
  exact threshold_ge_of_sparse hn

private lemma threshold_anchor_of_logScale_lower {t : ℕ} (ht : 2 ≤ t)
    (hlower : ∀ a : ℝ, 0 < a → a < 1 / 2 → logScale t =O[atTop] thresholdReal t a) :
    (∀ a : ℝ, 0 < a → a < 1 / 2 → thresholdReal t a =Θ[atTop] thresholdReal t (1 / 4)) ∧
    ((¬ (thresholdReal t (1 / 4) =O[atTop] thresholdReal t 0)) ↔
      ¬ (logScale t =O[atTop] thresholdReal t 0)) := by
  have href_upper : thresholdReal t (1 / 4) =O[atTop] logScale t :=
    threshold_isBigO_log_rpow ht (by norm_num) (by norm_num)
  have href_lower := hlower (1 / 4) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · intro a ha ha'
    exact ⟨(threshold_isBigO_log_rpow ht ha.le ha').trans href_lower,
      href_upper.trans (hlower a ha ha')⟩
  · exact ⟨fun h h' ↦ h (href_upper.trans h'), fun h h' ↦ h (href_lower.trans h')⟩

private lemma threshold_classes_iff {t : ℕ} :
    (∀ α β : ℝ, α ∈ Set.Ico (0 : ℝ) (1 / 2) → β ∈ Set.Ico (0 : ℝ) (1 / 2) →
      ((thresholdReal t α =Θ[atTop] thresholdReal t β) ↔ (α = 0 ↔ β = 0))) ↔
    ((∀ a : ℝ, 0 < a → a < 1 / 2 → thresholdReal t a =Θ[atTop] thresholdReal t (1 / 4)) ∧
      ¬ (thresholdReal t (1 / 4) =O[atTop] thresholdReal t 0)) := by
  constructor
  · intro h
    have href : (1 / 4 : ℝ) ∈ Set.Ico 0 (1 / 2) := by
      rw [Set.mem_Ico]
      constructor <;> norm_num
    refine ⟨fun a ha ha' ↦ ?_, fun hO ↦ ?_⟩
    · apply (h a (1 / 4) ⟨ha.le, ha'⟩ href).mpr
      simp [ha.ne']
    · have hz : (0 : ℝ) ∈ Set.Ico 0 (1 / 2) := by
        rw [Set.mem_Ico]
        constructor <;> norm_num
      have ht : thresholdReal t (1 / 4) =Θ[atTop] thresholdReal t 0 :=
        ⟨hO, threshold_isBigO_mono (by norm_num)⟩
      have heq := (h (1 / 4) 0 href hz).mp ht
      norm_num at heq
  · intro h α β ha hb
    exact threshold_theta_iff_of_anchor ha hb h.1 h.2

private def AvoidMono (n t m : ℕ) : Prop :=
  ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), X.card = m →
    ∀ b : Bool, ∃ e ∈ X.powersetCard t, c e = b

private lemma threshold_zero_le_iff {n t m : ℕ} :
    Hypergraph.balancedColoringThreshold n t 0 ≤ m ↔ AvoidMono n t m := by
  classical
  constructor
  · intro h
    obtain ⟨c, hc⟩ := threshold_feasible n t 0
    refine ⟨c, fun X hX b ↦ ?_⟩
    obtain ⟨e, he⟩ := card_pos.mp (hc X (h.trans hX.ge) b).1
    exact ⟨e, (mem_filter.mp he).1, (mem_filter.mp he).2⟩
  · rintro ⟨c, hc⟩
    apply threshold_le
    refine ⟨c, fun X hX b ↦ ?_⟩
    obtain ⟨Y, hY, hcard⟩ := exists_subset_card_eq hX
    obtain ⟨e, he, hcol⟩ := hc Y hcard b
    exact ⟨card_pos.mpr ⟨e, mem_filter.mpr ⟨powersetCard_mono hY he, hcol⟩⟩, by simp⟩

private lemma logScale_not_isBigO_zero_iff {t : ℕ} :
    (¬ (logScale t =O[atTop] thresholdReal t 0)) ↔
    ∀ C : ℝ, 0 < C → ∀ N : ℕ,
      ∃ n ≥ N, ∃ m : ℕ, C * (m : ℝ) < logScale t n ∧ AvoidMono n t m := by
  have ht_nonneg (n : ℕ) : 0 ≤ thresholdReal t 0 n := Nat.cast_nonneg _
  have hl_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ logScale t n :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hn)) _
  constructor
  · intro h C _ N
    have hh : ¬ ∀ n : ℕ, N ≤ n → logScale t n ≤ C * thresholdReal t 0 n := by
      intro hb
      apply h
      refine Asymptotics.IsBigO.of_bound C ?_
      filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with n hN h1
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ht_nonneg n), abs_of_nonneg (hl_nonneg h1)]
        using hb n hN
    push Not at hh
    obtain ⟨n, hn, hlt⟩ := hh
    exact ⟨n, hn, _, hlt, threshold_zero_le_iff.mp le_rfl⟩
  · intro h hO
    obtain ⟨C, hC, hCbound⟩ := hO.exists_pos
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hCbound.bound
    obtain ⟨n, hn, m, hlt, hc⟩ := h C hC (max N 1)
    have hb := hN n ((le_max_left N 1).trans hn)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (ht_nonneg n),
      abs_of_nonneg (hl_nonneg ((le_max_right N 1).trans hn))] at hb
    have hm : thresholdReal t 0 n ≤ (m : ℝ) :=
      Nat.cast_le.mpr (threshold_zero_le_iff.mpr hc)
    exact hlt.not_ge (hb.trans (mul_le_mul_of_nonneg_left hm hC.le))

private def MonoOn {V : Type*} [DecidableEq V] (t : ℕ)
    (col : Finset V → Bool) (S : Finset V) (b : Bool) : Prop :=
  ∀ e ∈ S.powersetCard t, col e = b

private lemma monoOn_insert {V : Type*} [DecidableEq V] {t : ℕ}
    {col : Finset V → Bool} {S : Finset V} {v : V} {b : Bool}
    (hS : MonoOn (t + 1) col S b)
    (hlink : MonoOn t (fun e ↦ col (insert v e)) S b) :
    MonoOn (t + 1) col (insert v S) b := by
  intro e he
  obtain ⟨heS, hec⟩ := mem_powersetCard.mp he
  by_cases hv : v ∈ e
  · have hsub : e.erase v ⊆ S := fun x hx ↦
      (mem_insert.mp (heS (mem_of_mem_erase hx))).resolve_left (ne_of_mem_erase hx)
    have hcard : (e.erase v).card = t := by rw [card_erase_of_mem hv, hec]; omega
    simpa only [insert_erase hv] using hlink (e.erase v) (mem_powersetCard.mpr ⟨hsub, hcard⟩)
  · exact hS e (mem_powersetCard.mpr
      ⟨fun x hx ↦ (mem_insert.mp (heS hx)).resolve_left (fun heq ↦ hv (heq ▸ hx)), hec⟩)

private def RamseyBound (t a b R : ℕ) : Prop :=
  ∀ (V : Type) [DecidableEq V], ∀ X : Finset V, R ≤ X.card → ∀ col : Finset V → Bool,
    (∃ S ⊆ X, S.card = a ∧ MonoOn t col S false) ∨
      (∃ S ⊆ X, S.card = b ∧ MonoOn t col S true)

private lemma exists_ramseyBound (t : ℕ) :
    ∀ a b : ℕ, ∃ R : ℕ, RamseyBound t a b R := by
  induction t with
  | zero =>
    intro a b
    refine ⟨max a b, fun V _ X hX col ↦ ?_⟩
    have hmono (S : Finset V) : MonoOn 0 col S (col ∅) := fun e he ↦ by
      rw [card_eq_zero.mp (mem_powersetCard.mp he).2]
    cases hcol : col ∅
    · obtain ⟨S, hSX, hS⟩ := exists_subset_card_eq ((le_max_left a b).trans hX)
      exact Or.inl ⟨S, hSX, hS, hcol ▸ hmono S⟩
    · obtain ⟨S, hSX, hS⟩ := exists_subset_card_eq ((le_max_right a b).trans hX)
      exact Or.inr ⟨S, hSX, hS, hcol ▸ hmono S⟩
  | succ t ih =>
    suffices ∀ k a b : ℕ, a + b = k →
        ∃ R : ℕ, RamseyBound (t + 1) a b R by
      exact fun a b ↦ this (a + b) a b rfl
    intro k
    induction k using Nat.strong_induction_on with
    | h k hk =>
      intro a b hab
      by_cases ha : a = 0
      · exact ⟨0, fun V _ X _ col ↦ Or.inl ⟨∅, empty_subset X, ha.symm, by simp [MonoOn]⟩⟩
      by_cases hb : b = 0
      · exact ⟨0, fun V _ X _ col ↦ Or.inr ⟨∅, empty_subset X, hb.symm, by simp [MonoOn]⟩⟩
      obtain ⟨Ra, hRa⟩ := hk ((a - 1) + b) (by omega) (a - 1) b rfl
      obtain ⟨Rb, hRb⟩ := hk (a + (b - 1)) (by omega) a (b - 1) rfl
      let K := max Ra Rb
      obtain ⟨R, hR⟩ := ih K K
      refine ⟨R + 1, fun V _ X hX col ↦ ?_⟩
      obtain ⟨v, hv⟩ := card_pos.mp (show 0 < X.card by omega)
      have hsize : R ≤ (X.erase v).card := by rw [card_erase_of_mem hv]; omega
      have extend {Y S : Finset V} {b : Bool} (hYX : Y ⊆ X.erase v) (hSY : S ⊆ Y)
          (hS : MonoOn (t + 1) col S b) (hlink : MonoOn t (fun e ↦ col (insert v e)) Y b) :
          insert v S ⊆ X ∧ (insert v S).card = S.card + 1 ∧
            MonoOn (t + 1) col (insert v S) b := by
        have hsub := hSY.trans hYX
        refine ⟨insert_subset hv (hsub.trans (erase_subset _ _)), ?_, monoOn_insert hS ?_⟩
        · exact card_insert_of_notMem (fun h ↦ notMem_erase _ _ (hsub h))
        · exact fun e he ↦ hlink e (powersetCard_mono hSY he)
      rcases hR V (X.erase v) hsize (fun e ↦ col (insert v e)) with
        ⟨Y, hYX, hYK, hlink⟩ | ⟨Y, hYX, hYK, hlink⟩
      · have hY : Ra ≤ Y.card := hYK ▸ le_max_left Ra Rb
        rcases hRa V Y hY col with ⟨S, hSY, hSc, hS⟩ | ⟨S, hSY, hSc, hS⟩
        · obtain ⟨hsub, hcard, hmono⟩ := extend hYX hSY hS hlink
          exact Or.inl ⟨insert v S, hsub, by omega, hmono⟩
        · exact Or.inr ⟨S, hSY.trans (hYX.trans (erase_subset _ _)), hSc, hS⟩
      · have hY : Rb ≤ Y.card := hYK ▸ le_max_right Ra Rb
        rcases hRb V Y hY col with ⟨S, hSY, hSc, hS⟩ | ⟨S, hSY, hSc, hS⟩
        · exact Or.inl ⟨S, hSY.trans (hYX.trans (erase_subset _ _)), hSc, hS⟩
        · obtain ⟨hsub, hcard, hmono⟩ := extend hYX hSY hS hlink
          exact Or.inr ⟨insert v S, hsub, by omega, hmono⟩

private lemma exists_not_avoidMono (t m : ℕ) : ∃ n : ℕ, ¬ AvoidMono n t m := by
  obtain ⟨R, hR⟩ := exists_ramseyBound t m m
  refine ⟨R, ?_⟩
  rintro ⟨col, hcol⟩
  have bad (S : Finset (Fin R)) (hS : S.card = m) {b : Bool}
      (hm : MonoOn t col S b) : False := by
    obtain ⟨e, he, hb⟩ := hcol S hS (!b)
    rw [hm e he] at hb
    cases b <;> cases hb
  rcases hR (Fin R) univ (by simp) col with ⟨S, _, hS, hm⟩ | ⟨S, _, hS, hm⟩
  · exact bad S hS hm
  · exact bad S hS hm

private lemma avoidMono_restrict {n N t m : ℕ} (hn : n ≤ N) (h : AvoidMono N t m) :
    AvoidMono n t m := by
  classical
  obtain ⟨col, hc⟩ := h
  let f := Fin.castLEEmb hn
  refine ⟨fun e ↦ col (e.map f), fun X hX b ↦ ?_⟩
  obtain ⟨e, he, heb⟩ := hc (X.map f) (by rwa [card_map]) b
  obtain ⟨hes, het⟩ := mem_powersetCard.mp he
  obtain ⟨d, hdX, rfl⟩ := subset_map_iff.mp hes
  rw [card_map] at het
  exact ⟨d, mem_powersetCard.mpr ⟨hdX, het⟩, heb⟩

private noncomputable def diagonalRamsey (t m : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_not_avoidMono t m)

private lemma avoidMono_iff_lt_diagonalRamsey {n t m : ℕ} :
    AvoidMono n t m ↔ n < diagonalRamsey t m := by
  classical
  constructor
  · intro h
    by_contra! hge
    exact Nat.find_spec (exists_not_avoidMono t m) (avoidMono_restrict hge h)
  · intro h
    exact not_not.mp (Nat.find_min (exists_not_avoidMono t m) h)

private lemma le_diagonalRamsey (t m : ℕ) : m ≤ diagonalRamsey t m := by
  by_contra! h
  have hv : AvoidMono (diagonalRamsey t m) t m := by
    refine ⟨fun _ ↦ false, fun X hX ↦ ?_⟩
    have hx : X.card ≤ diagonalRamsey t m := by simpa using card_le_univ X
    omega
  exact (avoidMono_iff_lt_diagonalRamsey.mp hv).false

private lemma logScale_pow {t n : ℕ} (ht : 2 ≤ t) (hn : 1 ≤ n) :
    logScale t n ^ (t - 1) = Real.log (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hne : ((t - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show t - 1 ≠ 0 by omega)
  unfold logScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul hlog, inv_mul_cancel₀ hne, Real.rpow_one]

/-- The zero-density threshold falls below the logarithmic scale along a subsequence
exactly when the normalized log of the diagonal Ramsey number is unbounded on every tail. -/
private lemma logScale_not_isBigO_zero_iff_diagonalRamsey {t : ℕ} (ht : 2 ≤ t) :
    (¬ (logScale t =O[atTop] thresholdReal t 0)) ↔
      ∀ A : ℝ, 0 < A → ∀ K : ℕ, ∃ m ≥ K,
        A * (m : ℝ) ^ (t - 1) < Real.log (diagonalRamsey t m : ℝ) := by
  have hd : t - 1 ≠ 0 := by omega
  have hd' : ((t - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [logScale_not_isBigO_zero_iff]
  constructor
  · intro h A hA K
    let C := A ^ (((t - 1 : ℕ) : ℝ)⁻¹)
    have hC : 0 < C := Real.rpow_pos_of_pos hA _
    have hCA : C ^ (t - 1) = A := by
      dsimp [C]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le, inv_mul_cancel₀ hd', Real.rpow_one]
    obtain ⟨n, hn, m, hnm, ha⟩ := h C hC (max 1 (diagonalRamsey t K))
    have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
    have hKn : diagonalRamsey t K ≤ n := (le_max_right _ _).trans hn
    have hKm : K ≤ m := by
      by_contra! hm
      have hshort := threshold_zero_le_iff.mp
        ((threshold_zero_le_iff.mpr ha).trans hm.le)
      exact (avoidMono_iff_lt_diagonalRamsey.mp hshort).not_ge hKn
    refine ⟨m, hKm, ?_⟩
    have hpow := pow_lt_pow_left₀ hnm (mul_nonneg hC.le (Nat.cast_nonneg _)) hd
    rw [mul_pow, hCA, logScale_pow ht hn1] at hpow
    exact hpow.trans (Real.log_lt_log (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast avoidMono_iff_lt_diagonalRamsey.mp ha))
  · intro h C hC N
    obtain ⟨m, hm, hlarge⟩ := h (2 * C ^ (t - 1)) (by positivity) (max 3 (N + 1))
    let R := diagonalRamsey t m
    let n := R - 1
    have hmr : m ≤ R := le_diagonalRamsey t m
    have hn2 : 2 ≤ n := by
      have := (le_max_left 3 (N + 1)).trans hm
      dsimp [n]
      omega
    have hnN : N ≤ n := by
      have := (le_max_right 3 (N + 1)).trans hm
      dsimp [n]
      omega
    have hnr : n < R := by dsimp [n]; omega
    have hab : R ≤ n ^ 2 := by
      have heq : R = n + 1 := by dsimp [n]; omega
      rw [heq, pow_two]
      nlinarith [Nat.mul_le_mul_right n hn2]
    have hlog : Real.log (R : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      calc
        Real.log (R : ℝ) ≤ Real.log ((n : ℝ) ^ (2 : ℕ)) :=
          Real.log_le_log (by exact_mod_cast (show 0 < R by omega)) (by exact_mod_cast hab)
        _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
    refine ⟨n, hnN, m, ?_, avoidMono_iff_lt_diagonalRamsey.mpr hnr⟩
    apply lt_of_pow_lt_pow_left₀ (t - 1)
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) _)
    rw [mul_pow, logScale_pow ht (by omega)]
    linarith [hlarge.trans_le hlog]

/-- The most significant bit at which two vertices differ. -/
private def bitDiff (x y : ℕ) : ℕ := (x ^^^ y).log2

private lemma bitDiff_above {x y j : ℕ} (hj : bitDiff x y < j) :
    x.testBit j = y.testBit j := by
  have hz : (x ^^^ y).testBit j = false := by
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) (by simpa [bitDiff] using hj))
  rw [Nat.testBit_xor] at hz
  cases h1 : x.testBit j <;> cases h2 : y.testBit j <;> simp_all

private lemma bitDiff_xor_ne {x y : ℕ} (h : x ≠ y) : x ^^^ y ≠ 0 := by
  intro hz
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  have hx := congrArg (fun z : ℕ ↦ z.testBit i) hz
  rw [Nat.testBit_xor, Nat.zero_testBit] at hx
  cases h1 : x.testBit i <;> cases h2 : y.testBit i <;> simp_all

private lemma bitDiff_bits {x y : ℕ} (hxy : x < y) :
    x.testBit (bitDiff x y) = false ∧ y.testBit (bitDiff x y) = true := by
  have hx := Nat.testBit_log2 (bitDiff_xor_ne hxy.ne)
  change (x ^^^ y).testBit (bitDiff x y) = true at hx
  rw [Nat.testBit_xor] at hx
  cases h1 : x.testBit (bitDiff x y) <;> cases h2 : y.testBit (bitDiff x y) <;>
    simp [h1, h2] at hx ⊢
  exact hxy.not_gt (Nat.lt_of_testBit _ h2 h1 (fun j hj ↦ (bitDiff_above hj).symm))

private lemma bitDiff_lt {n x y : ℕ} (hxy : x < y) (hy : y < 2 ^ n) :
    bitDiff x y < n :=
  (Nat.log2_lt (bitDiff_xor_ne hxy.ne)).2 (Nat.xor_lt_two_pow (hxy.trans hy) hy)

private lemma bitDiff_ne {x y z : ℕ} (hxy : x < y) (hyz : y < z) :
    bitDiff x y ≠ bitDiff y z := by
  intro h
  have h1 := (bitDiff_bits hxy).2
  rw [h, (bitDiff_bits hyz).1] at h1
  cases h1

private lemma bitDiff_max {x y z : ℕ} (hxy : x < y) (hyz : y < z) :
    bitDiff x z = max (bitDiff x y) (bitDiff y z) := by
  have unique {j : ℕ} (hj : x.testBit j ≠ z.testBit j)
      (habove : ∀ k, j < k → x.testBit k = z.testBit k) : bitDiff x z = j := by
    rcases lt_trichotomy (bitDiff x z) j with h | h | h
    · exact (hj (bitDiff_above h)).elim
    · exact h
    · have heq := habove _ h
      rw [(bitDiff_bits (hxy.trans hyz)).1, (bitDiff_bits (hxy.trans hyz)).2] at heq
      cases heq
  apply unique
  · rcases lt_or_gt_of_ne (bitDiff_ne hxy hyz) with h | h
    · rw [max_eq_right h.le, bitDiff_above h, (bitDiff_bits hyz).1, (bitDiff_bits hyz).2]
      decide
    · rw [max_eq_left h.le, ← bitDiff_above h, (bitDiff_bits hxy).1, (bitDiff_bits hxy).2]
      decide
  · exact fun k hk ↦ (bitDiff_above ((le_max_left _ _).trans_lt hk)).trans
      (bitDiff_above ((le_max_right _ _).trans_lt hk))

private def quadColor (g : Finset ℕ → Bool) (a b c : ℕ) : Bool :=
  if (a < b ∧ b < c) ∨ (c < b ∧ b < a) then g {a, b, c} else decide (b < a)

private lemma quadColor_peak (g : Finset ℕ → Bool) {a b c : ℕ} (h₁ : a < b) (h₂ : c < b) :
    quadColor g a b c = false := by
  simp [quadColor, h₁, h₂.not_gt, h₁.not_gt]

private lemma quadColor_valley (g : Finset ℕ → Bool) {a b c : ℕ} (h₁ : b < a) (h₂ : b < c) :
    quadColor g a b c = true := by
  simp [quadColor, h₁, h₂.not_gt, h₁.not_gt]

private lemma ordered_interval_rel {A : Type*} {r : A → A → Prop} [IsTrans A r]
    {f : ℕ → A} {l u : ℕ} (h : ∀ i, l ≤ i → i + 1 < u → r (f i) (f (i + 1)))
    {i j : ℕ} (hli : l ≤ i) (hij : i < j) (hju : j < u) : r (f i) (f j) := by
  induction hij with
  | refl => exact h _ hli hju
  | step hij ih =>
    exact _root_.trans (ih (Nat.lt_of_succ_lt hju)) (h _ (Nat.le_trans (Nat.le_trans hli (Nat.le_succ i)) hij) hju)

private lemma quad_mono_block {x : ℕ → ℕ} (hx : StrictMono x)
    (g : Finset ℕ → Bool) (b : Bool) {m : ℕ} (hm : 3 ≤ m)
    (hquad : ∀ i, i + 3 ≤ 2 * m →
      quadColor g (bitDiff (x i) (x (i + 1))) (bitDiff (x (i + 1)) (x (i + 2)))
          (bitDiff (x (i + 2)) (x (i + 3))) = b) :
    ∃ l, l + m ≤ 2 * m ∧
      (StrictMonoOn (fun i ↦ bitDiff (x i) (x (i + 1))) (Set.Ico l (l + m)) ∨
       StrictAntiOn (fun i ↦ bitDiff (x i) (x (i + 1))) (Set.Ico l (l + m))) := by
  let d (i : ℕ) := bitDiff (x i) (x (i + 1))
  let s (i : ℕ) : Bool := decide (d i < d (i + 1)) == b
  have hne (i : ℕ) : d i ≠ d (i + 1) := bitDiff_ne (hx (by omega)) (hx (by omega))
  have hs (i : ℕ) (hi : i + 1 < 2 * m - 1) : s i ≤ s (i + 1) := by
    by_cases h₁ : d i < d (i + 1) <;> by_cases h₂ : d (i + 1) < d (i + 2)
    · simp [s, h₁, h₂]
    · have hdec : d (i + 2) < d (i + 1) :=
        (lt_or_gt_of_ne (hne (i + 1))).resolve_left h₂
      have hcb : quadColor g (d i) (d (i + 1)) (d (i + 2)) = b := hquad i (by omega)
      rw [quadColor_peak g h₁ hdec] at hcb
      simp [s, hcb.symm, h₁, h₂]
    · have hdec : d (i + 1) < d i := (lt_or_gt_of_ne (hne i)).resolve_left h₁
      have hcb : quadColor g (d i) (d (i + 1)) (d (i + 2)) = b := hquad i (by omega)
      rw [quadColor_valley g hdec h₂] at hcb
      simp [s, hcb.symm, h₁, h₂]
    · simp [s, h₁, h₂]
  obtain ⟨l, hl, hconst⟩ : ∃ l, l + m ≤ 2 * m ∧
      ∀ i, l ≤ i → i + 1 < l + m → s i = s (m - 1) := by
    cases hc : s (m - 1)
    · refine ⟨0, by omega, fun i _ hi ↦ ?_⟩
      have hle := ordered_interval_rel (r := (· ≤ ·)) (fun i (_ : 0 ≤ i) ↦ hs i)
        (Nat.zero_le i) (show i < m - 1 by omega) (show m - 1 < 2 * m - 1 by omega)
      cases hi' : s i <;> simp [hc, hi'] at hle ⊢
      exact (by decide : ¬ true ≤ false) hle
    · refine ⟨m, by omega, fun i hli hi ↦ ?_⟩
      have hle := ordered_interval_rel (r := (· ≤ ·)) (fun i (_ : 0 ≤ i) ↦ hs i)
        (Nat.zero_le (m - 1)) (show m - 1 < i by omega) (show i < 2 * m - 1 by omega)
      cases hi' : s i <;> simp [hc, hi'] at hle ⊢
      exact (by decide : ¬ true ≤ false) hle
  refine ⟨l, hl, ?_⟩
  have hsdec (i : ℕ) (hi : l ≤ i) (hi' : i + 1 < l + m) :
      decide (d i < d (i + 1)) = decide (d (m - 1) < d ((m - 1) + 1)) := by
    have hc := hconst i hi hi'
    cases hb : b <;> simpa [s, hb] using hc
  by_cases hmid : d (m - 1) < d ((m - 1) + 1)
  · left
    intro i hi j hj hij
    apply ordered_interval_rel (r := (· < ·)) (l := l) (u := l + m) ?_ hi.1 hij hj.2
    intro k hk hk'
    simpa [hmid] using hsdec k hk hk'
  · right
    intro i hi j hj hij
    apply ordered_interval_rel (r := (· > ·)) (l := l) (u := l + m) ?_ hi.1 hij hj.2
    intro k hk hk'
    have hnot : ¬ d k < d (k + 1) := by simpa [hmid] using hsdec k hk hk'
    exact (lt_or_gt_of_ne (hne k)).resolve_left hnot

private lemma bitDiff_of_mono_block {x : ℕ → ℕ} (hx : StrictMono x) {i j : ℕ} (hij : i ≤ j)
    (hmono : MonotoneOn (fun k ↦ bitDiff (x k) (x (k + 1))) (Set.Icc i j)) :
    bitDiff (x i) (x (j + 1)) = bitDiff (x j) (x (j + 1)) := by
  induction hij with
  | refl => rfl
  | @step k hik ih =>
    rw [bitDiff_max (y := x (k + 1)) (hx (Nat.lt_succ_of_le hik)) (hx (Nat.lt_succ_self _))]
    rw [ih (hmono.mono (fun v hv ↦ ⟨hv.1, hv.2.trans (Nat.le_succ k)⟩))]
    exact max_eq_right (hmono (a := k) (b := k + 1)
      ⟨hik, Nat.le_succ _⟩ ⟨Nat.le_trans hik (Nat.le_succ _), le_rfl⟩ (Nat.le_succ _))

private lemma bitDiff_of_anti_block {x : ℕ → ℕ} (hx : StrictMono x) {i j : ℕ} (hij : i ≤ j)
    (hanti : AntitoneOn (fun k ↦ bitDiff (x k) (x (k + 1))) (Set.Icc i j)) :
    bitDiff (x i) (x (j + 1)) = bitDiff (x i) (x (i + 1)) := by
  induction hij with
  | refl => rfl
  | @step k hik ih =>
    rw [bitDiff_max (y := x (k + 1)) (hx (Nat.lt_succ_of_le hik)) (hx (Nat.lt_succ_self _))]
    rw [ih (hanti.mono (fun v hv ↦ ⟨hv.1, hv.2.trans (Nat.le_succ k)⟩))]
    have hiks : i ≤ k + 1 := Nat.le_trans hik (Nat.le_succ _)
    exact max_eq_left (hanti (a := i) (b := k + 1) ⟨le_rfl, hiks⟩ ⟨hiks, le_rfl⟩ hiks)

private lemma quad_lift_mono {x : ℕ → ℕ} (hx : StrictMono x) {g : Finset ℕ → Bool}
    {b : Bool} {n m : ℕ} (hm : 3 ≤ m) (hsize : x (2 * m) < 2 ^ n)
    (hquad : ∀ i j k v, i < j → j < k → k < v → v ≤ 2 * m →
      quadColor g (bitDiff (x i) (x j)) (bitDiff (x j) (x k)) (bitDiff (x k) (x v)) = b) :
    ∃ S : Finset ℕ, S.card = m ∧ (∀ y ∈ S, y < n) ∧ MonoOn 3 g S b := by
  classical
  let d (i : ℕ) := bitDiff (x i) (x (i + 1))
  obtain ⟨l, hl, hdir⟩ := quad_mono_block hx g b hm
    (fun i hi ↦ hquad i (i + 1) (i + 2) (i + 3) (by omega) (by omega) (by omega) hi)
  have hmem (i : Fin m) : l + (i : ℕ) ∈ Set.Ico l (l + m) :=
    ⟨by omega, Nat.add_lt_add_left i.isLt l⟩
  let f : Fin m ↪ ℕ := ⟨fun i ↦ d (l + i), by
    intro i j heq
    rcases lt_trichotomy i j with h | h | h
    · have h' : l + (i : ℕ) < l + (j : ℕ) := Nat.add_lt_add_left h l
      exact (hdir.elim (fun H ↦ (H (hmem i) (hmem j) h').ne heq)
        (fun H ↦ (H (hmem i) (hmem j) h').ne heq.symm)).elim
    · exact h
    · have h' : l + (j : ℕ) < l + (i : ℕ) := Nat.add_lt_add_left h l
      exact (hdir.elim (fun H ↦ (H (hmem j) (hmem i) h').ne heq.symm)
        (fun H ↦ (H (hmem j) (hmem i) h').ne heq)).elim⟩
  refine ⟨univ.map f, by simp, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy
    change bitDiff (x (l + (i : ℕ))) (x (l + (i : ℕ) + 1)) < n
    have hi := i.isLt
    exact bitDiff_lt (hx (by omega)) ((hx.monotone (by omega)).trans_lt hsize)
  · intro E hE
    obtain ⟨hES, hEcard⟩ := mem_powersetCard.mp hE
    obtain ⟨U, _, rfl⟩ := subset_map_iff.mp hES
    rw [card_map] at hEcard
    let e := U.orderEmbOfFin hEcard
    let i : ℕ := l + ((e 0 : Fin m) : ℕ)
    let j : ℕ := l + ((e 1 : Fin m) : ℕ)
    let k : ℕ := l + ((e 2 : Fin m) : ℕ)
    have hi : i ∈ Set.Ico l (l + m) := hmem (e 0)
    have hj : j ∈ Set.Ico l (l + m) := hmem (e 1)
    have hk : k ∈ Set.Ico l (l + m) := hmem (e 2)
    have hij : i < j := Nat.add_lt_add_left (e.strictMono (by decide : (0 : Fin 3) < 1)) l
    have hjk : j < k := Nat.add_lt_add_left (e.strictMono (by decide : (1 : Fin 3) < 2)) l
    have hku : k + 1 ≤ 2 * m := (Nat.succ_le_of_lt hk.2).trans hl
    have hU : U.map f = {d i, d j, d k} := by
      rw [← map_orderEmbOfFin_univ U hEcard, Finset.map_map]
      have huniv : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [huniv]
      simp only [map_insert, map_singleton]
      rfl
    rw [hU]
    have sub {a c : ℕ} (ha : l ≤ a) (hc : c < l + m) :
        Set.Icc a c ⊆ Set.Ico l (l + m) :=
      fun _ hv ↦ ⟨ha.trans hv.1, hv.2.trans_lt hc⟩
    rcases hdir with hinc | hdec
    · have h₁ := hinc hi hj hij
      have h₂ := hinc hj hk hjk
      have hq := hquad i (i + 1) (j + 1) (k + 1) (by omega) (by omega) (by omega) hku
      rw [bitDiff_of_mono_block hx (show i + 1 ≤ j by omega) (hinc.monotoneOn.mono (sub (by
        have := hi.1
        omega) hj.2)), bitDiff_of_mono_block hx (show j + 1 ≤ k by omega)
          (hinc.monotoneOn.mono (sub (by have := hj.1; omega) hk.2))] at hq
      simpa [quadColor, d, h₁, h₂] using hq
    · have h₁ := hdec hi hj hij
      have h₂ := hdec hj hk hjk
      have hq := hquad i j k (k + 1) hij hjk (by omega) hku
      have hj' : j - 1 + 1 = j := by omega
      have hk' : k - 1 + 1 = k := by omega
      have ha := bitDiff_of_anti_block hx (show i ≤ j - 1 by omega)
        (hdec.antitoneOn.mono (sub hi.1 (by have := hj.2; omega)))
      have hb := bitDiff_of_anti_block hx (show j ≤ k - 1 by omega)
        (hdec.antitoneOn.mono (sub hj.1 (by have := hk.2; omega)))
      rw [hj'] at ha
      rw [hk'] at hb
      rw [ha, hb] at hq
      simpa [quadColor, d, h₁, h₂] using hq

private def stepColor {n : ℕ} (g : Finset ℕ → Bool) (E : Finset (Fin (2 ^ n))) : Bool :=
  if h : E.card = 4 then
    let a := E.orderEmbOfFin h
    quadColor g (bitDiff (a 0) (a 1)) (bitDiff (a 1) (a 2)) (bitDiff (a 2) (a 3))
  else false

private lemma stepColor_quad {n : ℕ} (g : Finset ℕ → Bool) {X : Finset (Fin (2 ^ n))}
    {a b c d : Fin (2 ^ n)} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) (hd : d ∈ X)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ E ∈ X.powersetCard 4,
      stepColor g E = quadColor g (bitDiff a b) (bitDiff b c) (bitDiff c d) := by
  let v : Fin 4 → Fin (2 ^ n) := ![a, b, c, d]
  have hv : StrictMono v :=
    (((strictMono_vecEmpty.vecCons (by simpa using hcd)).vecCons
      (by simpa using hbc)).vecCons (by simpa using hab))
  let f : Fin 4 ↪ Fin (2 ^ n) := ⟨v, hv.injective⟩
  let E : Finset (Fin (2 ^ n)) := univ.map f
  have hE : E.card = 4 := by simp [E]
  have hvE (i : Fin 4) : v i ∈ E := mem_map_of_mem f (mem_univ i)
  have hsort := orderEmbOfFin_unique hE hvE hv
  refine ⟨E, mem_powersetCard.mpr ⟨?_, hE⟩, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    fin_cases i <;> assumption
  · unfold stepColor
    rw [dif_pos hE]
    change quadColor g
      (bitDiff (E.orderEmbOfFin hE 0) (E.orderEmbOfFin hE 1))
      (bitDiff (E.orderEmbOfFin hE 1) (E.orderEmbOfFin hE 2))
      (bitDiff (E.orderEmbOfFin hE 2) (E.orderEmbOfFin hE 3)) = _
    rw [← hsort]
    rfl

private lemma avoidMono_step_three_four {n m : ℕ} (hm : 3 ≤ m)
    (havoid : AvoidMono n 3 m) : AvoidMono (2 ^ n) 4 (2 * m + 1) := by
  classical
  obtain ⟨col, hcol⟩ := havoid
  let enc : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let g (S : Finset ℕ) : Bool := col (S.preimage enc enc.injective.injOn)
  refine ⟨stepColor g, fun X hX b ↦ ?_⟩
  by_contra! hb
  have hmono (E : Finset (Fin (2 ^ n))) (hE : E ∈ X.powersetCard 4) : stepColor g E = !b := by
    have h := hb E hE
    cases b <;> cases hp : stepColor g E <;> simp [hp] at h ⊢
  let x (i : ℕ) : ℕ := if hi : i < X.card then (X.orderEmbOfFin rfl ⟨i, hi⟩).val else 2 ^ n + i
  have hx : StrictMono x := by
    intro i j hij
    dsimp [x]
    split <;> split
    · exact (X.orderEmbOfFin rfl).strictMono (show (⟨i, ‹_›⟩ : Fin X.card) <
        (⟨j, ‹_›⟩ : Fin X.card) from hij)
    · exact (Fin.isLt _).trans_le (Nat.le_add_right _ _)
    · omega
    · exact Nat.add_lt_add_left hij _
  have hquad (i j k v : ℕ) (hij : i < j) (hjk : j < k) (hkv : k < v) (hv : v ≤ 2 * m) :
      quadColor g (bitDiff (x i) (x j)) (bitDiff (x j) (x k)) (bitDiff (x k) (x v)) = !b := by
    have he (r : ℕ) (hr : r ≤ v) :
        ∃ w : Fin (2 ^ n), w ∈ X ∧ w.val = x r := by
      have hr' : r < X.card := by omega
      exact ⟨X.orderEmbOfFin rfl ⟨r, hr'⟩, X.orderEmbOfFin_mem rfl _, by simp [x, hr']⟩
    obtain ⟨a, ha, hva⟩ := he i (by omega)
    obtain ⟨b', hb', hvb⟩ := he j (by omega)
    obtain ⟨c, hc, hvc⟩ := he k hkv.le
    obtain ⟨d, hd, hvd⟩ := he v le_rfl
    obtain ⟨E, hE, heq⟩ := stepColor_quad g ha hb' hc hd
      (show a.val < b'.val by simpa only [hva, hvb] using hx hij)
      (show b'.val < c.val by simpa only [hvb, hvc] using hx hjk)
      (show c.val < d.val by simpa only [hvc, hvd] using hx hkv)
    simpa only [hva, hvb, hvc, hvd] using heq.symm.trans (hmono E hE)
  have hsize : x (2 * m) < 2 ^ n := by
    dsimp [x]
    rw [dif_pos (by omega)]
    exact Fin.isLt _
  obtain ⟨S, hS, hbnd, hSm⟩ := quad_lift_mono hx hm hsize hquad
  obtain ⟨T, _, hT⟩ := (subset_map_iff (s := S) (f := enc) (t := univ)).1 (by
    intro y hy
    exact Finset.mem_map.mpr ⟨⟨y, hbnd y hy⟩, mem_univ _, rfl⟩)
  have hTc : T.card = m := by simpa [hT] using hS
  obtain ⟨e, he, heb⟩ := hcol T hTc b
  obtain ⟨hes, het⟩ := mem_powersetCard.mp he
  have hE : e.map enc ∈ S.powersetCard 3 :=
    mem_powersetCard.mpr ⟨hT ▸ map_subset_map.mpr hes, (card_map _).trans het⟩
  have hcontra : col e = !b := by simpa only [g, preimage_map] using hSm _ hE
  rw [heb] at hcontra
  cases b <;> cases hcontra

private lemma diagonalRamsey_step_three_four {m : ℕ} (hm : 3 ≤ m) :
    2 ^ (diagonalRamsey 3 m - 1) < diagonalRamsey 4 (2 * m + 1) := by
  have h := le_diagonalRamsey 3 m
  exact avoidMono_iff_lt_diagonalRamsey.mp (avoidMono_step_three_four hm
    (avoidMono_iff_lt_diagonalRamsey.mpr (by omega)))

private def IsInitialSegment {V : Type*} [LinearOrder V] (m : ℕ)
    (X Y : Finset V) : Prop :=
  Y ⊆ X ∧ Y.card = m ∧ ∀ y ∈ Y, ∀ z ∈ X, z ∉ Y → y < z

private lemma initialSegment_exists {V : Type*} [LinearOrder V] {m : ℕ}
    (X : Finset V) (hm : m ≤ X.card) : ∃ Y, IsInitialSegment m X Y := by
  induction m generalizing X with
  | zero => exact ⟨∅, empty_subset _, rfl, by simp⟩
  | succ m ih =>
    have hX := card_pos.mp (show 0 < X.card by omega)
    let a := X.min' hX
    have ha : a ∈ X := X.min'_mem hX
    have hcard : m ≤ (X.erase a).card := by rw [card_erase_of_mem ha]; omega
    obtain ⟨Y, hYX, hc, hlt⟩ := ih (X.erase a) hcard
    have haY : a ∉ Y := fun h ↦ notMem_erase _ _ (hYX h)
    refine ⟨insert a Y, insert_subset ha (hYX.trans (erase_subset _ _)), ?_, ?_⟩
    · rw [card_insert_of_notMem haY, hc]
    · intro y hy z hz hz'
      have hza : z ≠ a := fun h ↦ hz' (h ▸ mem_insert_self _ _)
      rcases mem_insert.mp hy with rfl | hy
      · exact (X.min'_le z hz).lt_of_ne hza.symm
      · exact hlt y hy z (mem_erase.mpr ⟨hza, hz⟩) (fun h ↦ hz' (mem_insert_of_mem h))

private lemma initialSegment_unique {V : Type*} [LinearOrder V] {m : ℕ}
    {X Y Z : Finset V} (hY : IsInitialSegment m X Y) (hZ : IsInitialSegment m X Z) :
    Y = Z := by
  classical
  have hc : Y.card = Z.card := hY.2.1.trans hZ.2.1.symm
  apply eq_of_subset_of_card_le _ hc.ge
  intro y hy
  by_contra! hny
  have hnsub : ¬ Z ⊆ Y := fun h ↦ hny ((eq_of_subset_of_card_le h hc.le) ▸ hy)
  obtain ⟨z, hz, hnz⟩ := Finset.not_subset.mp hnsub
  exact (hY.2.2 y hy z (hZ.1 hz) hnz).not_gt (hZ.2.2 z hz y (hY.1 hy) hny)

private noncomputable def firstVertices {V : Type*} [LinearOrder V] (m : ℕ) (X : Finset V) :
    Finset V := by
  classical
  exact if h : ∃ Y, IsInitialSegment m X Y then h.choose else ∅

private lemma firstVertices_eq {V : Type*} [LinearOrder V] {m : ℕ} {X Y : Finset V}
    (hY : IsInitialSegment m X Y) : firstVertices m X = Y := by
  classical
  unfold firstVertices
  rw [dif_pos (show ∃ Z, IsInitialSegment m X Z from ⟨Y, hY⟩)]
  exact initialSegment_unique (Exists.choose_spec _) hY

private lemma avoidMono_raise_uniformity {n r m q : ℕ} (h : AvoidMono n r m) :
    AvoidMono n (r + q) (m + q) := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨fun E ↦ c (firstVertices r E), fun X hX b ↦ ?_⟩
  obtain ⟨Y, hYX, hYc, hYlt⟩ := initialSegment_exists X (show m ≤ X.card by omega)
  obtain ⟨e, he, heb⟩ := hc Y hYc b
  obtain ⟨heY, hec⟩ := mem_powersetCard.mp he
  let Z := X \ Y
  have hZc : Z.card = q := by
    simp only [Z, card_sdiff_of_subset hYX, hX, hYc, Nat.add_sub_cancel_left]
  have hd : Disjoint e Z := Finset.disjoint_left.mpr fun y hy hz ↦
    (mem_sdiff.mp hz).2 (heY hy)
  refine ⟨e ∪ Z, mem_powersetCard.mpr ⟨Finset.union_subset (heY.trans hYX)
    (sdiff_subset : Z ⊆ X), by rw [card_union_of_disjoint hd, hec, hZc]⟩, ?_⟩
  have hinit : IsInitialSegment r (e ∪ Z) e := by
    refine ⟨subset_union_left, hec, fun x hx y hy hny ↦ ?_⟩
    have hyZ := (mem_union.mp hy).resolve_left hny
    exact hYlt x (heY hx) y (mem_sdiff.mp hyZ).1 (mem_sdiff.mp hyZ).2
  change c (firstVertices r (e ∪ Z)) = b
  rwa [firstVertices_eq hinit]

private lemma eventually_avoidMono_pow_three (d : ℕ) (hd : 1 ≤ d) :
    ∀ᶠ m : ℕ in atTop, AvoidMono (m ^ d) 3 m := by
  obtain ⟨C, hC, hCbound⟩ :=
    (threshold_isBigO_log_rpow (t := 3) (α := 0) (by decide) le_rfl (by norm_num)).exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hCbound.bound
  obtain ⟨M, hM⟩ := exists_nat_ge (C ^ 2 * (d : ℝ))
  filter_upwards [eventually_ge_atTop (max 1 (max N M))] with m hm
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hmN : N ≤ m := (le_max_left N M).trans ((le_max_right 1 _).trans hm)
  have hmM : M ≤ m := (le_max_right N M).trans ((le_max_right 1 _).trans hm)
  have hpow : m ≤ m ^ d := by
    calc m = m ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ m ^ d := Nat.pow_le_pow_right (by omega) hd
  have hlog0 : 0 ≤ Real.log ((m ^ d : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm1.trans hpow)
  have hscale0 := Real.rpow_nonneg hlog0 (((3 - 1 : ℕ) : ℝ)⁻¹)
  have hbound := hN (m ^ d) (hmN.trans hpow)
  change ‖thresholdReal 3 0 (m ^ d)‖ ≤ C * ‖logScale 3 (m ^ d)‖ at hbound
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg hscale0] at hbound
  apply threshold_zero_le_iff.mp
  apply (Nat.cast_le (α := ℝ)).mp
  apply hbound.trans
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Nat.cast_nonneg _)
  rw [mul_pow, show (2 : ℕ) = 3 - 1 by decide, logScale_pow (by decide : 2 ≤ 3)
    (hm1.trans hpow), Nat.cast_pow, Real.log_pow]
  norm_num
  rw [← mul_assoc]
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  calc C ^ 2 * (d : ℝ) * Real.log (m : ℝ)
    _ ≤ C ^ 2 * (d : ℝ) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity) |>.trans (by linarith))
        (by positivity)
    _ ≤ (m : ℝ) ^ 2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right
        (hM.trans (Nat.cast_le.mpr hmM)) (Nat.cast_nonneg (α := ℝ) m)

private lemma threshold_zero_le_step_high {n t : ℕ} (ht : 4 ≤ t) :
    Hypergraph.balancedColoringThreshold (2 ^ n) t 0 ≤
      2 * max 3 (Hypergraph.balancedColoringThreshold n 3 0) + 1 + (t - 4) := by
  let m := max 3 (Hypergraph.balancedColoringThreshold n 3 0)
  have havoid : AvoidMono n 3 m := threshold_zero_le_iff.mp (le_max_right _ _)
  apply threshold_zero_le_iff.mpr
  have h := avoidMono_raise_uniformity (q := t - 4)
    (avoidMono_step_three_four (le_max_left _ _) havoid)
  rwa [Nat.add_sub_cancel' ht] at h

private lemma threshold_zero_mono_vertices {n N t : ℕ} (hn : n ≤ N) :
    Hypergraph.balancedColoringThreshold n t 0 ≤ Hypergraph.balancedColoringThreshold N t 0 :=
  threshold_zero_le_iff.mpr (avoidMono_restrict hn (threshold_zero_le_iff.mp le_rfl))

private lemma threshold_zero_isBigO_log_log_high {t : ℕ} (ht : 4 ≤ t) :
    thresholdReal t 0 =O[atTop]
      (fun n : ℕ ↦ (Real.log (Real.log (n : ℝ))) ^ ((2 : ℝ)⁻¹)) := by
  obtain ⟨C, hC, hCb⟩ :=
    (threshold_isBigO_log_rpow (t := 3) (α := 0) (by decide) le_rfl (by norm_num)).exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hCb.bound
  let B : ℝ := 2 / Real.log 2
  let Q : ℝ := max 1 (Real.log B)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hB : 0 < B := div_pos (by norm_num) hlog2
  have hQ : ∀ᶠ n : ℕ in atTop, Q ≤ Real.log (Real.log (n : ℝ)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).eventually (eventually_ge_atTop Q)
  let r : ℝ := (2 : ℝ)⁻¹
  refine Asymptotics.IsBigO.of_bound (2 * C * (2 : ℝ) ^ r + (7 + (t : ℝ))) ?_
  filter_upwards [hQ, eventually_ge_atTop (max 2 (2 ^ N))] with n hnQ hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnN : 2 ^ N ≤ n := (le_max_right _ _).trans hn
  let L := n.log2 + 1
  have hLN : N ≤ L := ((Nat.le_log2 (by omega)).mpr hnN).trans (Nat.le_succ _)
  have hL1 : 1 ≤ L := by dsimp [L]; omega
  have hnL : n ≤ 2 ^ L := Nat.lt_log2_self.le
  have htbound := (threshold_zero_mono_vertices (t := t) hnL).trans
    (threshold_zero_le_step_high ht)
  have hcast : thresholdReal t 0 n ≤ 2 * thresholdReal 3 0 L + (7 + (t : ℝ)) := by
    have hmax : max 3 (Hypergraph.balancedColoringThreshold L 3 0) ≤
        3 + Hypergraph.balancedColoringThreshold L 3 0 := max_le (by omega) (by omega)
    exact_mod_cast (show Hypergraph.balancedColoringThreshold n t 0 ≤
      2 * Hypergraph.balancedColoringThreshold L 3 0 + (7 + t) by omega)
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL1)
  have hL : (L : ℝ) ≤ B * Real.log (n : ℝ) := by
    have h₁ : (n.log2 : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.log2_self_le (by omega : n ≠ 0))
    have h₂ : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hsum : (L : ℝ) * Real.log 2 ≤ 2 * Real.log (n : ℝ) := by
      dsimp [L]
      push_cast
      linarith
    dsimp [B]
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact hsum
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hloglog1 : 1 ≤ Real.log (Real.log (n : ℝ)) := (le_max_left _ _).trans hnQ
  have hlogL : Real.log (L : ℝ) ≤ 2 * Real.log (Real.log (n : ℝ)) := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < L by omega)) hL
    rw [Real.log_mul hB.ne' hlogn.ne'] at h
    linarith [(le_max_right 1 (Real.log B)).trans hnQ]
  let y := (Real.log (Real.log (n : ℝ))) ^ r
  have hY : 1 ≤ y := by
    rw [← Real.one_rpow r]
    exact Real.rpow_le_rpow zero_le_one hloglog1 (by positivity)
  have hscale : logScale 3 L ≤ (2 : ℝ) ^ r * y := by
    change Real.log (L : ℝ) ^ r ≤ _
    calc
      _ ≤ (2 * Real.log (Real.log (n : ℝ))) ^ r :=
        Real.rpow_le_rpow hlogL0 hlogL (by positivity)
      _ = _ := Real.mul_rpow (by norm_num) (zero_le_one.trans hloglog1)
  have h := hN L hLN
  change ‖thresholdReal 3 0 L‖ ≤ C * ‖logScale 3 L‖ at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hlogL0 _)] at h
  change ‖thresholdReal t 0 n‖ ≤ _ * ‖y‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (zero_le_one.trans hY)]
  nlinarith only [hcast, mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hscale hC.le))
    (show (0 : ℝ) ≤ 2 by norm_num),
    mul_nonneg (show (0 : ℝ) ≤ 7 + (t : ℝ) by positivity) (sub_nonneg.mpr hY)]

private lemma threshold_zero_isLittleO_log_rpow_high {t : ℕ} (ht : 4 ≤ t)
    {s : ℝ} (hs : 0 < s) :
    thresholdReal t 0 =o[atTop] (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ s) :=
  (threshold_zero_isBigO_log_log_high ht).trans_isLittleO
    ((isLittleO_log_rpow_rpow_atTop ((2 : ℝ)⁻¹) hs).comp_tendsto
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

private lemma log_rpow_not_isBigO_zero_high_uniformity {t : ℕ} (ht : 4 ≤ t)
    {s : ℝ} (hs : 0 < s) :
    ¬ ((fun n : ℕ ↦ (Real.log (n : ℝ)) ^ s) =O[atTop] thresholdReal t 0) := by
  intro h
  apply isLittleO_irrefl ?_ (h.trans_isLittleO (threshold_zero_isLittleO_log_rpow_high ht hs))
  apply Eventually.frequently
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  exact (Real.rpow_pos_of_pos hlog s).ne'

private lemma logScale_not_isBigO_zero_high_uniformity {t : ℕ} (ht : 4 ≤ t) :
    ¬ (logScale t =O[atTop] thresholdReal t 0) :=
  log_rpow_not_isBigO_zero_high_uniformity ht
    (inv_pos.mpr (by exact_mod_cast (show 0 < t - 1 by omega)))

private lemma threshold_classes_iff_diagonalRamsey_of_logScale_lower {t : ℕ} (ht : 2 ≤ t)
    (hlower : ∀ a : ℝ, 0 < a → a < 1 / 2 → logScale t =O[atTop] thresholdReal t a) :
    (∀ α β : ℝ, α ∈ Set.Ico (0 : ℝ) (1 / 2) → β ∈ Set.Ico (0 : ℝ) (1 / 2) →
      ((thresholdReal t α =Θ[atTop] thresholdReal t β) ↔ (α = 0 ↔ β = 0))) ↔
      ∀ A : ℝ, 0 < A → ∀ K : ℕ, ∃ m ≥ K,
        A * (m : ℝ) ^ (t - 1) < Real.log (diagonalRamsey t m : ℝ) := by
  obtain ⟨hpos, hzero⟩ := threshold_anchor_of_logScale_lower ht hlower
  rw [threshold_classes_iff, hzero, logScale_not_isBigO_zero_iff_diagonalRamsey ht]
  exact and_iff_right hpos

private lemma threshold_jump_of_power_lower {t : ℕ} (ht : 4 ≤ t) {α s : ℝ}
    (hs : 0 < s)
    (hlower : (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ s) =O[atTop] thresholdReal t α) :
    ¬ (thresholdReal t α =O[atTop] thresholdReal t 0) :=
  fun h ↦ log_rpow_not_isBigO_zero_high_uniformity ht hs (hlower.trans h)

private lemma threshold_classes_high_of_power_lower {t : ℕ} (ht : 4 ≤ t) {s : ℝ}
    (hs : 0 < s)
    (hlower : (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ s) =O[atTop] thresholdReal t (1 / 4))
    (hpos : ∀ a : ℝ, 0 < a → a < 1 / 2 →
      thresholdReal t a =Θ[atTop] thresholdReal t (1 / 4)) :
    ∀ α β : ℝ, α ∈ Set.Ico (0 : ℝ) (1 / 2) → β ∈ Set.Ico (0 : ℝ) (1 / 2) →
      ((thresholdReal t α =Θ[atTop] thresholdReal t β) ↔ (α = 0 ↔ β = 0)) :=
  threshold_classes_iff.mpr ⟨hpos, threshold_jump_of_power_lower ht hs hlower⟩

open scoped BigOperators

private noncomputable def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

private lemma indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  classical
  unfold indicator
  split <;> norm_num

private lemma indicator_le_one (p : Prop) : indicator p ≤ 1 := by
  classical
  unfold indicator
  split <;> norm_num

private lemma indicator_mono {p q : Prop} (h : p → q) : indicator p ≤ indicator q := by
  classical
  by_cases hp : p
  · simp [indicator, hp, h hp]
  · simpa [indicator, hp] using indicator_nonneg q

private lemma expect_pair {A B : Type} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← Finset.expect_product, Finset.univ_product_univ]

private lemma expect_fin_cons {V : Type} [Fintype V] {d : ℕ} (f : (Fin (d + 1) → V) → ℝ) :
    (𝔼 x, f x) = 𝔼 v, 𝔼 x, f (Fin.cons v x) := by
  rw [← expect_pair (fun p : V × (Fin d → V) ↦ f (Fin.cons p.1 p.2))]
  exact Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (d + 1) ↦ V)).symm _ _ (by simp)

private lemma expect_pow_le {V : Type} [Fintype V] [Nonempty V] (f : V → ℝ)
    (hf : ∀ v, 0 ≤ f v) (s : ℕ) :
    (𝔼 v, f v) ^ s ≤ 𝔼 v, f v ^ s := by
  have hV : (Fintype.card V : ℝ) ≠ 0 := by positivity
  simpa only [Fintype.expect_eq_sum_div_card, div_eq_inv_mul, Finset.mul_sum, smul_eq_mul] using
    (convexOn_pow s).map_sum_le (t := (univ : Finset V))
      (w := fun _ ↦ (Fintype.card V : ℝ)⁻¹) (p := f)
      (fun _ _ ↦ by positivity) (by simp [hV]) (fun v _ ↦ hf v)

private lemma expect_all_samples {V : Type} [Fintype V] (P : V → Prop) (s : ℕ) :
    (𝔼 u : Fin s → V, indicator (∀ j, P (u j))) = (𝔼 v, indicator (P v)) ^ s := by
  classical
  induction s with
  | zero => simp [indicator]
  | succ s ih =>
    rw [expect_fin_cons, pow_succ']
    have hcons (v : V) (u : Fin s → V) :
        indicator (∀ j, P (Fin.cons (α := fun _ ↦ V) v u j)) = indicator (P v) * indicator (∀ j, P (u j)) := by
      simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
      by_cases hv : P v <;> simp [indicator, hv]
    simp only [hcons, ← Finset.mul_expect, ih, ← Finset.expect_mul]

/-- Repeated sampling in each coordinate preserves a quantitative density bound by Jensen. -/
private lemma expect_box {V : Type} [Fintype V] [Nonempty V] (s d : ℕ)
    (P : (Fin d → V) → Prop) :
    (𝔼 x, indicator (P x)) ^ (s ^ d) ≤
      𝔼 a : Fin d → Fin s → V, indicator (∀ u : Fin d → Fin s, P (fun i ↦ a i (u i))) := by
  classical
  induction d with
  | zero =>
    rw [pow_zero, pow_one]
    let x₀ : Fin 0 → V := fun i ↦ Fin.elim0 i
    have hleft (x : Fin 0 → V) : indicator (P x) = indicator (P x₀) := by
      rw [Subsingleton.elim x x₀]
    have hright (a : Fin 0 → Fin s → V) :
        indicator (∀ u : Fin 0 → Fin s, P (fun i ↦ a i (u i))) = indicator (P x₀) := by
      congr 1
      apply propext
      constructor
      · intro h
        simpa only [Subsingleton.elim (fun i ↦ a i ((fun j ↦ Fin.elim0 j : Fin 0 → Fin s) i)) x₀] using
          h (fun j ↦ Fin.elim0 j)
      · intro h u
        rwa [Subsingleton.elim (fun i ↦ a i (u i)) x₀]
    simp only [hleft, hright, Fintype.expect_const, le_refl]
  | succ d ih =>
    let Q (v : Fin s → V) (x : Fin d → V) := ∀ j, P (Fin.cons (α := fun _ ↦ V) (v j) x)
    have hcons (v : Fin s → V) (a : Fin d → Fin s → V) :
        (∀ u : Fin (d + 1) → Fin s, P (fun i ↦ Fin.cons (α := fun _ ↦ Fin s → V) v a i (u i))) ↔
          ∀ u : Fin d → Fin s, Q v (fun i ↦ a i (u i)) := by
      constructor
      · intro h u j
        convert h (Fin.cons (α := fun _ ↦ Fin s) j u) using 2
        rename_i i
        exact Fin.cases rfl (fun _ ↦ rfl) i
      · intro h u
        convert h (fun i ↦ u i.succ) (u 0) using 2
        rename_i i
        exact Fin.cases rfl (fun _ ↦ rfl) i
    rw [expect_fin_cons (V := Fin s → V), pow_succ', pow_mul]
    simp_rw [hcons]
    calc
      ((𝔼 x, indicator (P x)) ^ s) ^ (s ^ d)
        ≤ (𝔼 v, 𝔼 x, indicator (Q v x)) ^ (s ^ d) := by
          apply pow_le_pow_left₀ (pow_nonneg (Finset.expect_nonneg (fun _ _ ↦ indicator_nonneg _)) _)
          have hsample (x : Fin d → V) :
              (𝔼 v, indicator (Q v x)) =
                (𝔼 w : V, indicator (P (Fin.cons (α := fun _ ↦ V) w x))) ^ s :=
            expect_all_samples (fun w : V ↦ P (Fin.cons (α := fun _ ↦ V) w x)) s
          rw [Finset.expect_comm]
          simp only [hsample]
          have hmean : (𝔼 x : Fin d → V, 𝔼 w : V, indicator (P (Fin.cons (α := fun _ ↦ V) w x))) =
              𝔼 x, indicator (P x) := by
            rw [Finset.expect_comm]
            exact (expect_fin_cons (fun x ↦ indicator (P x))).symm
          rw [← hmean]
          exact expect_pow_le _ (fun _ ↦ Finset.expect_nonneg (fun _ _ ↦ indicator_nonneg _)) _
      _ ≤ 𝔼 v, (𝔼 x, indicator (Q v x)) ^ (s ^ d) :=
        expect_pow_le _ (fun _ ↦ Finset.expect_nonneg (fun _ _ ↦ indicator_nonneg _)) _
      _ ≤ _ := Finset.expect_le_expect fun v _ ↦ ih (Q v)

private lemma expect_precomp {I J V : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype V] [Nonempty V]
    (e : I → J) (he : Function.Injective e) (F : (I → V) → ℝ) :
    (𝔼 x : J → V, F (x ∘ e)) = 𝔼 y : I → V, F y := by
  classical
  let split := Equiv.piEquivPiSubtypeProd (fun j ↦ j ∈ Set.range e) (fun _ ↦ V)
  have h := Fintype.expect_equiv split (fun x : J → V ↦ F (x ∘ e))
    (fun p ↦ F (p.1 ∘ Equiv.ofInjective e he)) (fun _ ↦ rfl)
  rw [h, expect_pair]
  simp only [Fintype.expect_const]
  exact Fintype.expect_equiv (Equiv.piCongrLeft (fun _ ↦ V) (Equiv.ofInjective e he)).symm
    _ _ (fun _ ↦ rfl)

private lemma expect_eq_at_pair {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [Nonempty V]
    {i j : I} (hij : i ≠ j) :
    (𝔼 x : I → V, indicator (x i = x j)) = (Fintype.card V : ℝ)⁻¹ := by
  classical
  let e : Bool → I := fun b ↦ if b then i else j
  have he : Function.Injective e := by
    intro a b hab
    cases a <;> cases b <;> simp_all [e, eq_comm]
  calc
    _ = 𝔼 y : Bool → V, indicator (y true = y false) := by
      simpa [e, Function.comp_def] using expect_precomp e he
        (fun y : Bool → V ↦ indicator (y true = y false))
    _ = 𝔼 p : V × V, indicator (p.1 = p.2) :=
      Fintype.expect_equiv (Equiv.boolArrowEquivProd V) _ _ (fun y ↦ by
        simp [Equiv.boolArrowEquivProd, eq_comm])
    _ = _ := by
      rw [expect_pair]
      simp [indicator]

private lemma expect_noninjective {I V : Type} [Fintype I] [DecidableEq I] [Fintype V] [Nonempty V] :
    (𝔼 x : I → V, indicator (¬ Function.Injective x)) ≤
      (Fintype.card I : ℝ) ^ 2 / Fintype.card V := by
  classical
  let F (x : I → V) (i j : I) := indicator (i ≠ j ∧ x i = x j)
  calc
    _ ≤ 𝔼 x : I → V, ∑ i : I, ∑ j : I, F x i j := by
      apply Finset.expect_le_expect
      intro x _
      by_cases hx : Function.Injective x
      · rw [show indicator (¬ Function.Injective x) = 0 by simp [indicator, hx]]
        exact sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ indicator_nonneg _
      · have hx' : ∃ i j, x i = x j ∧ i ≠ j := by
          by_contra h
          exact hx (fun i j heq ↦ by_contra fun hij ↦ h ⟨i, j, heq, hij⟩)
        obtain ⟨i, j, heq, hij⟩ := hx'
        have hF : F x i j = 1 := by simp [F, indicator, hij, heq]
        rw [show indicator (¬ Function.Injective x) = 1 by simp [indicator, hx], ← hF]
        exact (single_le_sum (f := F x i) (fun _ _ ↦ indicator_nonneg _) (mem_univ j)).trans
          (single_le_sum (f := fun i ↦ ∑ j, F x i j)
            (fun _ _ ↦ sum_nonneg fun _ _ ↦ indicator_nonneg _) (mem_univ i))
    _ = ∑ i : I, ∑ j : I, 𝔼 x : I → V, F x i j := by
      simp_rw [Finset.expect_sum_comm]
    _ ≤ ∑ _i : I, ∑ _j : I, (Fintype.card V : ℝ)⁻¹ := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp [F, indicator, hij]
      · simpa [F, hij] using (expect_eq_at_pair (V := V) hij).le
    _ = _ := by simp [pow_two, div_eq_mul_inv, mul_assoc]

private lemma exists_injective_box {V : Type} [Fintype V] [Nonempty V] {s d : ℕ}
    (P : (Fin d → V) → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdense : δ ≤ 𝔼 x, indicator (P x))
    (hlarge : ((d * s : ℕ) : ℝ) ^ 2 / Fintype.card V < δ ^ (s ^ d)) :
    ∃ a : Fin d × Fin s → V, Function.Injective a ∧
      ∀ u : Fin d → Fin s, P (fun i ↦ a (i, u i)) := by
  classical
  have hgood := (pow_le_pow_left₀ hδ hdense _).trans (expect_box s d P)
  let e : (Fin d → Fin s → V) ≃ (Fin d × Fin s → V) :=
    ⟨Function.uncurry, Function.curry, fun _ ↦ rfl, fun _ ↦ by funext ⟨_, _⟩; rfl⟩
  have hchange := Fintype.expect_equiv e
    (fun a ↦ indicator (∀ u : Fin d → Fin s, P (fun i ↦ a i (u i))))
    (fun a ↦ indicator (∀ u : Fin d → Fin s, P (fun i ↦ a (i, u i)))) (fun _ ↦ rfl)
  rw [hchange] at hgood
  by_contra h
  have hbad := expect_noninjective (I := Fin d × Fin s) (V := V)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hbad
  exact (hgood.trans ((Finset.expect_le_expect fun a _ ↦ indicator_mono fun ha hi ↦ h ⟨a, hi, ha⟩).trans hbad)).not_gt hlarge

private def MonoTuple {V : Type} [DecidableEq V] {d : ℕ} (t : ℕ)
    (col : Finset V → Bool) (b : Bool) (x : Fin d → V) : Prop :=
  Function.Injective x ∧ MonoOn t col (univ.image x) b

/-- Applying Ramsey on random injections yields a uniform density of ordered cliques. -/
private lemma exists_dense_monoTuple (t d : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ col : Finset (Fin n) → Bool,
      ∃ b : Bool, δ ≤ 𝔼 x : Fin d → Fin n, indicator (MonoTuple t col b x) := by
  classical
  obtain ⟨R, hR⟩ := exists_ramseyBound t d d
  let E := {e : Fin d → Fin R // Function.Injective e}
  let C : ℝ := Fintype.card (Bool × E)
  let δ := (2 * max 1 C)⁻¹
  have hC : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  refine ⟨δ, by dsimp [δ]; positivity, ?_, max 1 (2 * R ^ 2), fun n hn col ↦ ?_⟩
  · dsimp [δ]
    rw [inv_lt_one_iff₀]
    right
    linarith
  have hnpos : 0 < n := (le_max_left _ _).trans hn
  let : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  have hbad := expect_noninjective (I := Fin R) (V := Fin n)
  simp only [Fintype.card_fin] at hbad
  have hbad' : (𝔼 y : Fin R → Fin n, indicator (¬ Function.Injective y)) ≤ 1 / 2 := by
    apply hbad.trans
    rw [div_le_iff₀ (by exact_mod_cast hnpos)]
    have hc : (2 : ℝ) * (R : ℝ) ^ 2 ≤ (n : ℝ) := by
      exact_mod_cast (le_max_right 1 (2 * R ^ 2)).trans hn
    linarith
  have hinj : (1 : ℝ) / 2 ≤ 𝔼 y : Fin R → Fin n, indicator (Function.Injective y) := by
    have hsum :
        (𝔼 y : Fin R → Fin n, indicator (Function.Injective y)) +
          (𝔼 y : Fin R → Fin n, indicator (¬ Function.Injective y)) = 1 := by
      rw [← Finset.expect_add_distrib]
      have hpoint (y : Fin R → Fin n) :
          indicator (Function.Injective y) + indicator (¬ Function.Injective y) = 1 := by
        by_cases hy : Function.Injective y <;> simp [indicator, hy]
      simp only [hpoint, Fintype.expect_const]
    linarith
  have hfind (y : Fin R → Fin n) (hy : Function.Injective y) :
      ∃ p : Bool × E, MonoTuple t col p.1 (y ∘ p.2.val) := by
    have hsize : (univ.image y).card = R := by simp [card_image_of_injective _ hy]
    have hmono : ∃ b S, S ⊆ univ.image y ∧ S.card = d ∧ MonoOn t col S b := by
      rcases hR (Fin n) (univ.image y) hsize.ge col with h | h
      · obtain ⟨S, hs, hc, hm⟩ := h
        exact ⟨false, S, hs, hc, hm⟩
      · obtain ⟨S, hs, hc, hm⟩ := h
        exact ⟨true, S, hs, hc, hm⟩
    obtain ⟨b, S, hS, hc, hm⟩ := hmono
    let f := (S.equivFinOfCardEq hc).symm
    have hf (i : Fin d) : ∃ j, y j = (f i).val := by
      simpa only [mem_image, mem_univ, true_and] using hS (f i).property
    choose e he using hf
    have hei : Function.Injective e := by
      intro i j hij
      apply f.injective
      apply Subtype.ext
      rw [← he i, ← he j, hij]
    refine ⟨(b, ⟨e, hei⟩), hy.comp hei, ?_⟩
    intro edge hedge
    apply hm edge (mem_powersetCard.mpr ⟨?_, (mem_powersetCard.mp hedge).2⟩)
    intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp ((mem_powersetCard.mp hedge).1 hv)
    change y (e i) ∈ S
    rw [he i]
    exact (f i).property
  have htot :
      (1 : ℝ) / 2 ≤ ∑ p : Bool × E, 𝔼 x : Fin d → Fin n, indicator (MonoTuple t col p.1 x) := by
    apply hinj.trans
    calc
      _ ≤ 𝔼 y : Fin R → Fin n,
          ∑ p : Bool × E, indicator (MonoTuple t col p.1 (y ∘ p.2.val)) := by
        apply Finset.expect_le_expect
        intro y _
        by_cases hy : Function.Injective y
        · obtain ⟨p, hp⟩ := hfind y hy
          simpa only [indicator, if_pos hy, if_pos hp] using
            (single_le_sum (s := (univ : Finset (Bool × E)))
              (f := fun p ↦ indicator (MonoTuple t col p.1 (y ∘ p.2.val)))
              (fun _ _ ↦ indicator_nonneg _) (mem_univ p))
        · rw [show indicator (Function.Injective y) = 0 by simp [indicator, hy]]
          exact sum_nonneg fun _ _ ↦ indicator_nonneg _
      _ = _ := by
        rw [Finset.expect_sum_comm]
        exact sum_congr rfl fun p _ ↦ expect_precomp p.2.val p.2.property (fun x ↦ indicator (MonoTuple t col p.1 x))
  let D (b : Bool) : ℝ := 𝔼 x : Fin d → Fin n, indicator (MonoTuple t col b x)
  have hmax : (1 : ℝ) / 2 ≤ max 1 C * max (D false) (D true) := by
    apply htot.trans
    calc
      _ ≤ ∑ _p : Bool × E, max (D false) (D true) :=
        sum_le_sum fun p _ ↦ by change D p.1 ≤ _; cases p.1
                                · exact le_max_left _ _
                                · exact le_max_right _ _
      _ = C * max (D false) (D true) := by simp [C, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
        ((Finset.expect_nonneg fun _ _ ↦ indicator_nonneg _).trans (le_max_left _ _))
  have hδ : δ ≤ max (D false) (D true) := by
    dsimp [δ]
    rw [← one_div, div_le_iff₀ (by positivity)]
    linarith
  rcases le_max_iff.mp hδ with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

private lemma expect_indicator_card {V : Type} [Fintype V] (P : V → Prop) [DecidablePred P] :
    (𝔼 v, indicator (P v)) = ((univ.filter P).card : ℝ) / Fintype.card V := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  rw [show (∑ v, indicator (P v)) = ∑ v ∈ univ.filter P, (1 : ℝ) by
    rw [Finset.sum_filter]
    apply sum_congr rfl
    intro v _
    by_cases hv : P v <;> simp [indicator, hv]]
  simp

private lemma expect_colliding_parts {t d s : ℕ} (hd : 0 < d) (hs : 0 < s) :
    (𝔼 f : Fin t → Fin d × Fin s, indicator (¬ Function.Injective (Prod.fst ∘ f))) ≤
      (t : ℝ) ^ 2 / (d : ℝ) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  have he := Fintype.expect_equiv
    (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ ↦ Fin d) (fun _ ↦ Fin s))
    (fun f ↦ indicator (¬ Function.Injective (Prod.fst ∘ f)))
    (fun p ↦ indicator (¬ Function.Injective p.1)) (fun _ ↦ rfl)
  rw [he, expect_pair]
  simp only [Fintype.expect_const]
  simpa only [Fintype.card_fin] using (expect_noninjective (I := Fin t) (V := Fin d))

/-- Every opposite-color edge uses two vertices from the same part. -/
private lemma sparse_of_mono_box {n t d s : ℕ} {col : Finset (Fin n) → Bool} {b : Bool}
    {α : ℝ} (hα : 0 < α) (hs : 0 < s) (hd : 2 * t ≤ d) (hd0 : 0 < d)
    (hratio : (t : ℝ) ^ 2 * ((2 : ℝ) ^ t * (t.factorial : ℝ)) < α * (d : ℝ))
    (a : Fin d × Fin s ↪ Fin n)
    (hbox : ∀ u : Fin d → Fin s, MonoTuple t col b (fun i ↦ a (i, u i))) :
    ∃ X : Finset (Fin n), X.card = d * s ∧
      (((X.powersetCard t).filter (fun e ↦ col e = !b)).card : ℝ) <
        α * (X.card.choose t : ℝ) := by
  classical
  let X : Finset (Fin n) := univ.map a
  have hX : X.card = d * s := by simp [X]
  refine ⟨X, hX, ?_⟩
  let Bad := (X.powersetCard t).filter (fun e ↦ col e = !b)
  let Coll := (univ : Finset (Fin t → Fin d × Fin s)).filter
    (fun f ↦ ¬ Function.Injective (Prod.fst ∘ f))
  have represent (e : Bad) : ∃ f : Fin t → Fin d × Fin s, univ.image (a ∘ f) = e.val := by
    have he := mem_powersetCard.mp (mem_filter.mp e.property).1
    let g := (e.val.equivFinOfCardEq he.2).symm
    have hu (i : Fin t) : ∃ v, a v = (g i).val := by
      simpa only [X, Finset.mem_map, mem_univ, true_and] using he.1 (g i).property
    choose f hf using hu
    refine ⟨f, ?_⟩
    ext v
    constructor
    · intro hv
      obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      simpa only [Function.comp_apply, hf] using (g i).property
    · intro hv
      obtain ⟨i, hi⟩ := g.surjective ⟨v, hv⟩
      exact mem_image.mpr ⟨i, mem_univ _, (hf i).trans (congrArg Subtype.val hi)⟩
  choose f hf using represent
  have hcoll (e : Bad) : f e ∈ Coll := by
    rw [mem_filter]
    refine ⟨mem_univ _, fun h ↦ ?_⟩
    let u : Fin d → Fin s :=
      Function.extend (Prod.fst ∘ f e) (Prod.snd ∘ f e) (fun _ ↦ ⟨0, hs⟩)
    have hsub : e.val ⊆ univ.image (fun i ↦ a (i, u i)) := by
      rw [← hf e]
      intro v hv
      obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      refine mem_image.mpr ⟨(f e i).1, mem_univ _, ?_⟩
      have hui : u ((f e i).1) = (f e i).2 :=
        h.extend_apply (Prod.snd ∘ f e) _ i
      simp only [Function.comp_apply, hui, Prod.eta]
    have he := mem_filter.mp e.property
    have hb := (hbox u).2 e.val (mem_powersetCard.mpr
      ⟨hsub, (mem_powersetCard.mp he.1).2⟩)
    rw [he.2] at hb
    cases b <;> cases hb
  have hcount : Bad.card ≤ Coll.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective (fun e : Bad ↦ (⟨f e, hcoll e⟩ : Coll)) (by
        intro e g heg
        apply Subtype.ext
        have heq : f e = f g := congrArg Subtype.val heg
        rw [← hf e, ← hf g, heq])
  have hprob := expect_colliding_parts (t := t) hd0 hs
  rw [expect_indicator_card] at hprob
  change (Coll.card : ℝ) / (Fintype.card (Fin t → Fin d × Fin s) : ℝ) ≤ _ at hprob
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Nat.cast_pow] at hprob
  have hpos : (0 : ℝ) < ((d * s : ℕ) : ℝ) ^ t := by positivity
  have hfac : (0 : ℝ) < (2 : ℝ) ^ t * (t.factorial : ℝ) := by positivity
  have hratio' : (t : ℝ) ^ 2 / (d : ℝ) < α / ((2 : ℝ) ^ t * (t.factorial : ℝ)) :=
    (div_lt_div_iff₀ (by exact_mod_cast hd0) hfac).mpr hratio
  change (Bad.card : ℝ) < α * (X.card.choose t : ℝ)
  calc
    _ ≤ (Coll.card : ℝ) := by exact_mod_cast hcount
    _ ≤ (t : ℝ) ^ 2 / (d : ℝ) * ((d * s : ℕ) : ℝ) ^ t := (div_le_iff₀ hpos).mp hprob
    _ < α / ((2 : ℝ) ^ t * (t.factorial : ℝ)) * ((d * s : ℕ) : ℝ) ^ t :=
      mul_lt_mul_of_pos_right hratio' hpos
    _ = α * ((X.card : ℝ) ^ t / ((2 : ℝ) ^ t * (t.factorial : ℝ))) := by rw [hX]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (choose_lower (hX ▸ Nat.le_mul_of_pos_right d hs |>.trans' hd)) hα.le

private lemma eventually_log_box_size {d : ℕ} (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∃ s : ℕ, 0 < s ∧
      K * (Real.log (n : ℝ)) ^ ((d : ℝ)⁻¹) ≤ (s : ℝ) ∧
      ((d * s : ℕ) : ℝ) ^ 2 / (n : ℝ) < δ ^ (s ^ d) := by
  let r : ℝ := (d : ℝ)⁻¹
  let A := (-2 : ℝ) * Real.log δ
  have hlogδ := Real.log_neg hδ hδ'
  have hA : 0 < A := by dsimp [A]; linarith
  let C := (1 / A) ^ r
  have hC : 0 < C := by dsimp [C]; positivity
  let x (n : ℕ) := C * (Real.log (n : ℝ)) ^ r
  have hr : 0 < r := inv_pos.mpr (Nat.cast_pos.mpr hd)
  have htend : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hxtend : Tendsto x atTop atTop :=
    Tendsto.const_mul_atTop hC ((tendsto_rpow_atTop hr).comp htend)
  have hlo := isLittleO_log_rpow_rpow_atTop (r * 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have hloN := hlo.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := (hloN.const_mul_left (((d : ℝ) * C) ^ 2)).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨C / 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hxtend.eventually_ge_atTop 2, hsmall] with n hn hx hsmall'
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  let s := ⌊x n⌋₊
  have hle : (s : ℝ) ≤ x n := Nat.floor_le (by positivity)
  have hfloor : x n < (s : ℝ) + 1 := Nat.lt_floor_add_one _
  have hs : 0 < s := by
    have : (0 : ℝ) < (s : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨s, hs, ?_, ?_⟩
  · have : x n / 2 ≤ (s : ℝ) := by linarith
    exact (show C / 2 * Real.log (n : ℝ) ^ r = x n / 2 by dsimp [x]; ring).le.trans this
  have hxp : x n ^ d = Real.log (n : ℝ) / A := by
    dsimp [x, C]
    rw [← Real.mul_rpow (by positivity) hlogn, ← Real.rpow_mul_natCast (by positivity),
      show r * (d : ℝ) = 1 from inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'),
      Real.rpow_one]
    ring
  have hs_pow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) s) hle d
  rw [hxp] at hs_pow
  have hexp : (n : ℝ) ^ (-(1 / 2) : ℝ) ≤ δ ^ (s ^ d) := by
    rw [Real.rpow_def_of_pos hnR, ← Real.exp_log hδ, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_right hs_pow hlogδ.le
    have hEq : Real.log (n : ℝ) / A * Real.log δ = Real.log (n : ℝ) * (-(1 / 2)) := by
      dsimp [A]
      field_simp [hlogδ.ne]
    rw [hEq] at hh
    push_cast
    exact hh
  have hs_mul : ((d * s : ℕ) : ℝ) ^ 2 ≤ ((d : ℝ) * x n) ^ 2 := by
    push_cast
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hle (by positivity)) _
  have hsmall'' : ((d : ℝ) * x n) ^ 2 ≤ 1 / 2 * (n : ℝ) ^ ((1 / 2) : ℝ) := by
    change ‖(((d : ℝ) * C) ^ 2 * (Real.log (n : ℝ)) ^ (r * 2))‖ ≤
      1 / 2 * ‖(n : ℝ) ^ ((1 / 2) : ℝ)‖ at hsmall'
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ ((1 / 2) : ℝ))] at hsmall'
    dsimp [x]
    rw [← mul_assoc, mul_pow, ← Real.rpow_mul_natCast hlogn, Nat.cast_ofNat]
    exact hsmall'
  apply lt_of_lt_of_le _ hexp
  rw [div_lt_iff₀ hnR]
  have hsplit : (n : ℝ) ^ (-(1 / 2) : ℝ) * (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hnR.ne', show (-(1 / 2) + 1 : ℝ) = 1 / 2 by norm_num]
  rw [hsplit]
  exact (hs_mul.trans hsmall'').trans_lt (by
    have hp := Real.rpow_pos_of_pos hnR (1 / 2 : ℝ)
    linarith)

private lemma positive_threshold_log_power (t : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ r : ℝ, 0 < r ∧
      (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ r) =O[atTop] thresholdReal t α := by
  classical
  obtain ⟨D, hD⟩ := exists_nat_gt ((t : ℝ) ^ 2 * ((2 : ℝ) ^ t * (t.factorial : ℝ)) / α)
  let d := max (2 * t + 1) D
  have hd : 0 < d := by dsimp [d]; omega
  have htd : 2 * t ≤ d := (Nat.le_succ _).trans (le_max_left _ _)
  have hratio : (t : ℝ) ^ 2 * ((2 : ℝ) ^ t * (t.factorial : ℝ)) < α * (d : ℝ) := by
    rw [mul_comm α, ← div_lt_iff₀ hα]
    exact hD.trans_le (Nat.cast_le.mpr (le_max_right _ _))
  obtain ⟨δ, hδ, hδ', N, hN⟩ := exists_dense_monoTuple t d
  obtain ⟨K, hK, hsize⟩ := eventually_log_box_size hd hδ hδ'
  refine ⟨(d : ℝ)⁻¹, inv_pos.mpr (Nat.cast_pos.mpr hd), Asymptotics.IsBigO.of_bound (1 / K) ?_⟩
  filter_upwards [eventually_ge_atTop (max N 1), hsize] with n hn hsize'
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨s, hs, hsmall, hlarge⟩ := hsize'
  have hmain : K * (Real.log (n : ℝ)) ^ ((d : ℝ)⁻¹) ≤ thresholdReal t α n := by
    apply threshold_ge_of_sparse
    intro col
    obtain ⟨b, hb⟩ := hN n ((le_max_left _ _).trans hn) col
    obtain ⟨a, ha, hbox⟩ := exists_injective_box (MonoTuple t col b) hδ.le hb
      (by simpa only [Fintype.card_fin] using hlarge)
    obtain ⟨X, hX, hXbad⟩ := sparse_of_mono_box hα hs htd hd hratio ⟨a, ha⟩ hbox
    refine ⟨X, hsmall.trans ?_, !b, hXbad⟩
    exact_mod_cast (Nat.le_mul_of_pos_left s hd).trans_eq hX.symm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
    (Real.log_nonneg (by exact_mod_cast hn1)) _), abs_of_nonneg (Nat.cast_nonneg _),
    div_mul_eq_mul_div, one_mul, le_div_iff₀ hK, mul_comm]
  exact hmain

private lemma threshold_jump_high {t : ℕ} (ht : 4 ≤ t) {α : ℝ} (hα : 0 < α) :
    ¬ (thresholdReal t α =O[atTop] thresholdReal t 0) := by
  obtain ⟨r, hr, hlo⟩ := positive_threshold_log_power t hα
  exact threshold_jump_of_power_lower ht hr hlo

private lemma threshold_zero_isLittleO_positive_high {t : ℕ} (ht : 4 ≤ t)
    {α : ℝ} (hα : 0 < α) :
    thresholdReal t 0 =o[atTop] thresholdReal t α := by
  obtain ⟨r, hr, hlo⟩ := positive_threshold_log_power t hα
  exact (threshold_zero_isLittleO_log_rpow_high ht hr).trans_isBigO hlo

private lemma exists_complete_bipartite {V : Type} [Fintype V] [Nonempty V]
    (P : V → V → Prop) {s : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hdense : δ ≤ 𝔼 x : V, 𝔼 y : V, indicator (P x y))
    (hcard : 2 * (s : ℝ) ^ 2 / Fintype.card V ≤ δ ^ s) :
    ∃ u : Fin s → V, Function.Injective u ∧
      δ ^ s / 2 ≤ 𝔼 y : V, indicator (∀ i, P (u i) y) := by
  classical
  let F (u : Fin s → V) : ℝ := 𝔼 y : V, indicator (∀ i, P (u i) y)
  have hF : δ ^ s ≤ 𝔼 u, F u := by
    calc
      _ ≤ (𝔼 x : V, 𝔼 y : V, indicator (P x y)) ^ s := pow_le_pow_left₀ hδ.le hdense _
      _ ≤ 𝔼 y : V, (𝔼 x : V, indicator (P x y)) ^ s := by
        rw [Finset.expect_comm]
        exact expect_pow_le _ (fun _ ↦ Finset.expect_nonneg (fun _ _ ↦ indicator_nonneg _)) _
      _ = _ := by
        have he (y : V) : (𝔼 x : V, indicator (P x y)) ^ s =
            𝔼 u : Fin s → V, indicator (∀ i, P (u i) y) :=
          (expect_all_samples (fun x ↦ P x y) s).symm
        simp only [he, F]
        exact Finset.expect_comm _ _ _
  let G (u : Fin s → V) := if Function.Injective u then F u else 0
  have hpoint (u : Fin s → V) : F u ≤ G u + indicator (¬ Function.Injective u) := by
    by_cases hu : Function.Injective u
    · simp [G, indicator, hu]
    · have hF_le : F u ≤ 1 :=
        Finset.expect_le (univ_nonempty : (univ : Finset V).Nonempty)
          (fun _ _ ↦ indicator_le_one _)
      simpa [G, indicator, hu] using hF_le
  have hac := expect_noninjective (I := Fin s) (V := V)
  simp only [Fintype.card_fin] at hac
  have hG : δ ^ s / 2 ≤ 𝔼 u, G u := by
    have hw := (hF.trans (Finset.expect_le_expect (fun u _ ↦ hpoint u)))
    rw [Finset.expect_add_distrib] at hw
    rw [mul_div_assoc] at hcard
    linarith
  obtain ⟨u, _, hu⟩ := Finset.exists_le_of_le_expect univ_nonempty hG
  have hu' : Function.Injective u := by
    by_contra h
    simp only [G, if_neg h] at hu
    exact (show (0 : ℝ) < δ ^ s / 2 by positivity).not_ge hu
  exact ⟨u, hu', by simpa only [G, if_pos hu'] using hu⟩

private lemma exists_constant_pattern {V E : Type} [DecidableEq V] [DecidableEq E]
    (G : Finset E) (hG : G.Nonempty) (A : Finset V) {s : ℕ} (hs : 2 * s ≤ A.card)
    (c : V → E → Bool) :
    ∃ U ⊆ A, U.card = s ∧ ∃ b : Bool, ∃ H ⊆ G,
      G.card ≤ 2 ^ (A.card + 1) * H.card ∧ ∀ v ∈ U, ∀ e ∈ H, c v e = b := by
  classical
  have hcolor (e : E) : ∃ b : Bool, ∃ U ⊆ A, U.card = s ∧ ∀ v ∈ U, c v e = b := by
    let B₁ := A.filter (fun v ↦ c v e = true)
    let B₂ := A.filter (fun v ↦ c v e ≠ true)
    have hsum : B₁.card + B₂.card = A.card := card_filter_add_card_filter_not (s := A) _
    by_cases h₁ : s ≤ B₁.card
    · obtain ⟨U, hU, hc⟩ := exists_subset_card_eq h₁
      exact ⟨true, U, hU.trans (filter_subset _ _), hc, fun v hv ↦ (mem_filter.mp (hU hv)).2⟩
    · obtain ⟨U, hU, hc⟩ := exists_subset_card_eq (show s ≤ B₂.card by omega)
      refine ⟨false, U, hU.trans (filter_subset _ _), hc, fun v hv ↦ ?_⟩
      have h := (mem_filter.mp (hU hv)).2
      cases hc' : c v e
      · rfl
      · exact (h hc').elim
  choose b U hU hsize hmono using hcolor
  let P := (univ : Finset Bool) ×ˢ A.powerset
  let pairs (e : E) := (b e, U e)
  have hp (e : E) (_ : e ∈ G) : pairs e ∈ P := mem_product.mpr ⟨mem_univ _, mem_powerset.mpr (hU e)⟩
  have hP : P.card = 2 ^ (A.card + 1) := by simp [P, pow_succ, mul_comm]
  have hsum := Finset.sum_card_fiberwise_eq_card_filter (s := G) (t := P) pairs
  have hall : G.filter (fun e ↦ pairs e ∈ P) = G :=
    filter_eq_self.mpr hp
  rw [hall] at hsum
  obtain ⟨p, hpP, hpmax⟩ := exists_max_image P
    (fun p ↦ (G.filter (fun e ↦ pairs e = p)).card)
    (by obtain ⟨e, he⟩ := hG; exact ⟨pairs e, hp e he⟩)
  let H := G.filter (fun e ↦ pairs e = p)
  have hbound : G.card ≤ P.card * H.card := by
    calc
      G.card = _ := hsum.symm
      _ ≤ ∑ _q ∈ P, H.card := sum_le_sum (fun q hq ↦ hpmax q hq)
      _ = _ := by simp
  have hH : H.Nonempty := by
    apply card_pos.mp
    by_contra! h
    have := hG.card_pos
    rw [show H.card = 0 by omega, mul_zero] at hbound
    omega
  obtain ⟨e, he⟩ := hH
  have hep : pairs e = p := (mem_filter.mp he).2
  refine ⟨p.2, mem_powerset.mp (mem_product.mp hpP).2, ?_, p.1, H,
    filter_subset _ _, hP ▸ hbound, ?_⟩
  · rw [← hep]
    exact hsize e
  · intro v hv e he
    have hep' : pairs e = p := (mem_filter.mp he).2
    rw [← hep'] at hv ⊢
    exact hmono e v hv


private lemma focus_patterns {V E : Type} [DecidableEq V] [DecidableEq E]
    (A : ℕ → Finset V) (c : V → E → Bool) (G : Finset E) (hG : G.Nonempty) (s : ℕ) :
    ∀ r, (∀ i < r, (A i).card = 2 * s) →
      ∃ U : ℕ → Finset V, ∃ b : ℕ → Bool, ∃ H ⊆ G,
        G.card ≤ 2 ^ (r * (2 * s + 1)) * H.card ∧
        ∀ i < r, U i ⊆ A i ∧ (U i).card = s ∧
          ∀ v ∈ U i, ∀ e ∈ H, c v e = b i := by
  intro r
  induction r with
  | zero => exact fun _ ↦ ⟨A, fun _ ↦ false, G, Subset.rfl, by simp⟩
  | succ r ih =>
    intro hA
    obtain ⟨U, b, H, hHG, hHsize, hH⟩ := ih (fun i hi ↦ hA i (by omega))
    have hHpos : H.Nonempty := card_pos.mp (by
      by_contra! h
      rw [show H.card = 0 by omega, mul_zero] at hHsize
      have := hG.card_pos
      omega)
    obtain ⟨W, hWA, hWsize, z, T, hTH, hTsize, hT⟩ :=
      exists_constant_pattern H hHpos (A r) (hA r (by omega)).ge c
    refine ⟨Function.update U r W, Function.update b r z, T, hTH.trans hHG, ?_, ?_⟩
    · calc
        _ ≤ 2 ^ (r * (2 * s + 1)) * H.card := hHsize
        _ ≤ 2 ^ (r * (2 * s + 1)) * (2 ^ ((A r).card + 1) * T.card) :=
          Nat.mul_le_mul_left _ hTsize
        _ = _ := by rw [← mul_assoc, ← pow_add, hA r (by omega), Nat.add_mul, one_mul]
    · intro i hi
      by_cases heq : i = r
      · subst i
        simpa only [Function.update_self] using And.intro hWA (And.intro hWsize hT)
      · rw [Function.update_of_ne heq, Function.update_of_ne heq]
        obtain ⟨hsub, hc, he⟩ := hH i (by omega)
        exact ⟨hsub, hc, fun v hv e he' ↦ he v hv e (hTH he')⟩

open scoped Classical in
private lemma graph_density_ge {V : Type} [DecidableEq V] {S : Finset V} {G : Finset (Finset V)}
    (hG : G ⊆ S.powersetCard 2) :
    (G.card : ℝ) / (S.card : ℝ) ^ 2 ≤
      𝔼 u : S, 𝔼 v : S, indicator ({u.val, v.val} ∈ G) := by
  classical
  let P (p : S × S) : Prop := {p.1.val, p.2.val} ∈ G
  have hp (e : G) : ∃ p : S × S, {p.1.val, p.2.val} = e.val := by
    have he := mem_powersetCard.mp (hG e.property)
    let f := (e.val.equivFinOfCardEq he.2).symm
    refine ⟨(⟨(f 0).val, he.1 (f 0).property⟩, ⟨(f 1).val, he.1 (f 1).property⟩), ?_⟩
    ext w
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact (f 0).property
      · exact (f 1).property
    · intro hw
      obtain ⟨i, hi⟩ := f.surjective ⟨w, hw⟩
      have hi' := (congrArg Subtype.val hi).symm
      fin_cases i
      · exact Or.inl hi'
      · exact Or.inr hi'
  choose p hp using hp
  have hcount : G.card ≤ (univ.filter P).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective (fun e : G ↦ (⟨p e, mem_filter.mpr ⟨mem_univ _, by
        change {(p e).1.val, (p e).2.val} ∈ G
        rw [hp e]
        exact e.property⟩⟩ : (univ.filter P : Finset (S × S)))) (by
        intro e e' he
        have h := congrArg Subtype.val he
        change p e = p e' at h
        apply Subtype.ext
        rw [← hp e, ← hp e', h])
  change _ ≤ 𝔼 u : S, 𝔼 v : S, indicator (P (u, v))
  rw [← expect_pair (fun p ↦ indicator (P p)), expect_indicator_card, Fintype.card_prod,
    Fintype.card_coe, Nat.cast_mul, ← pow_two]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)



open scoped Classical in
private lemma graph_biclique {V : Type} [DecidableEq V] {S : Finset V} {G : Finset (Finset V)}
    (hG : G ⊆ S.powersetCard 2) (hS : S.Nonempty) {s : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hdense : δ ≤ (G.card : ℝ) / (S.card : ℝ) ^ 2)
    (hcard : 2 * (s : ℝ) ^ 2 / (S.card : ℝ) ≤ δ ^ s) :
    ∃ X ⊆ S, ∃ Y ⊆ S, X.card = s ∧ Disjoint X Y ∧
      δ ^ s / 2 * (S.card : ℝ) ≤ (Y.card : ℝ) ∧
      ∀ x ∈ X, ∀ y ∈ Y, {x, y} ∈ G := by
  classical
  have hSpos : 0 < S.card := hS.card_pos
  let : Nonempty (Fin S.card) := ⟨⟨0, hSpos⟩⟩
  let e : Fin S.card ≃ ↥S := (S.equivFinOfCardEq rfl).symm
  let P (x y : Fin S.card) : Prop := {(e x).val, (e y).val} ∈ G
  have hden : δ ≤ 𝔼 x : Fin S.card, 𝔼 y : Fin S.card, indicator (P x y) := by
    have hrow (x : Fin S.card) : (𝔼 y : Fin S.card, indicator (P x y)) =
        𝔼 y : S, indicator ({(e x).val, y.val} ∈ G) :=
      Fintype.expect_equiv e _ _ (fun _ ↦ rfl)
    simp only [hrow]
    rw [Fintype.expect_equiv e _ (fun x : S ↦ 𝔼 y : S,
      indicator ({x.val, y.val} ∈ G)) (fun _ ↦ rfl)]
    exact hdense.trans (graph_density_ge hG)
  have hbound : 2 * (s : ℝ) ^ 2 / (Fintype.card (Fin S.card) : ℝ) ≤ δ ^ s := by
    simpa only [Fintype.card_fin] using hcard
  obtain ⟨u, hu, hY⟩ := exists_complete_bipartite P hδ hden hbound
  let Y₀ : Finset (Fin S.card) := univ.filter (fun y ↦ ∀ i, P (u i) y)
  let X : Finset V := univ.image (fun i ↦ (e (u i)).val)
  let Y : Finset V := Y₀.map (e.toEmbedding.trans (Function.Embedding.subtype (fun v : V ↦ v ∈ S)))
  have hXsub : X ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact (e (u i)).property
  have hYsub : Y ⊆ S := by
    intro y hy
    obtain ⟨x, _, hxy⟩ := Finset.mem_map.mp hy
    change (e x).val = y at hxy
    rw [← hxy]
    exact (e x).property
  have hxy (x : V) (hx : x ∈ X) (y : V) (hy : y ∈ Y) : {x, y} ∈ G := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, hvy⟩ := Finset.mem_map.mp hy
    change (e v).val = y at hvy
    rw [← hvy]
    exact (mem_filter.mp hv).2 i
  refine ⟨X, hXsub, Y, hYsub, ?_, ?_, ?_, hxy⟩
  · change (univ.image (fun i ↦ (e (u i)).val)).card = s
    have hinj : Function.Injective (fun i ↦ (e (u i)).val) :=
      Subtype.val_injective.comp (e.injective.comp hu)
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  · rw [Finset.disjoint_left]
    intro x hx hy
    have he := (mem_powersetCard.mp (hG (hxy x hx x hy))).2
    simp at he
  · rw [expect_indicator_card, Fintype.card_fin] at hY
    change _ ≤ ((Y₀.map _).card : ℝ)
    rw [card_map]
    exact (le_div_iff₀ (by exact_mod_cast hSpos)).mp hY


private structure TriplesFocused {V : Type} [DecidableEq V] (col : Finset V → Bool)
    (r s : ℕ) (A : ℕ → Finset V) (S : Finset V) (χ : ℕ → ℕ → Bool) : Prop where
  size : ∀ i < r, (A i).card = s
  disjoint : ∀ i j, i < j → j < r → Disjoint (A i) (A j)
  outside : ∀ i < r, Disjoint (A i) S
  colors : ∀ i j, i < j → j < r → ∀ x ∈ A i, ∀ y ∈ A j,
    (∀ z ∈ S, col {x, y, z} = χ i j) ∧
    ∀ k, j < k → k < r → ∀ z ∈ A k, col {x, y, z} = χ i j

private lemma focus_triples_round {V : Type} [DecidableEq V] (col : Finset V → Bool)
    {r s : ℕ} {A : ℕ → Finset V} {S : Finset V} {χ : ℕ → ℕ → Bool}
    (hA : TriplesFocused col r (2 * s) A S χ) (hS : 2 ≤ S.card)
    {δ : ℝ} (hδ : 0 < δ) (hδ_le : δ ≤ ((4 : ℝ) * 2 ^ (r * (2 * s + 1)))⁻¹)
    (hlarge : 2 * (s : ℝ) ^ 2 / (S.card : ℝ) ≤ δ ^ s) :
    ∃ A' S' χ', S' ⊆ S ∧ (δ ^ s / 2) * (S.card : ℝ) ≤ (S'.card : ℝ) ∧
      TriplesFocused col (r + 1) s A' S' χ' := by
  classical
  have hSnonempty : S.Nonempty := card_pos.mp (by omega)
  let G := S.powersetCard 2
  have hG : G.Nonempty := card_pos.mp (by simpa [G] using Nat.choose_pos hS)
  obtain ⟨U, b, H, hHG, hH, hU⟩ :=
    focus_patterns A (fun x e ↦ col (insert x e)) G hG s r hA.size
  let L : ℝ := 2 ^ (r * (2 * s + 1))
  have hL : 0 < L := by dsimp [L]; positivity
  have hScard : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS
  have hGreal : (S.card : ℝ) ^ 2 / 4 ≤ (G.card : ℝ) := by
    dsimp [G]
    rw [card_powersetCard, choose_two_real (by omega)]
    nlinarith only [mul_nonneg (show (0 : ℝ) ≤ (S.card : ℝ) by positivity)
      (sub_nonneg.mpr hScard)]
  have hHreal : (G.card : ℝ) ≤ L * (H.card : ℝ) := by dsimp [L]; exact_mod_cast hH
  have hdense : δ ≤ (H.card : ℝ) / (S.card : ℝ) ^ 2 := by
    apply hδ_le.trans
    change (4 * L)⁻¹ ≤ _
    rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hGreal.trans hHreal]
  obtain ⟨X, hXS, Y, hYS, hX, hXY, hY, hgraph⟩ :=
    graph_biclique hHG hSnonempty hδ hdense hlarge
  let A' := Function.update U r X
  let χ' (i j : ℕ) := if j = r then b i else χ i j
  have hAnew : A' r = X := Function.update_self _ _ _
  have hAold (i : ℕ) (hi : i < r) : A' i = U i :=
    Function.update_of_ne hi.ne _ _
  have hsub (i : ℕ) (hi : i < r) : A' i ⊆ A i := by
    rw [hAold i hi]
    exact (hU i hi).1
  have hres (i : ℕ) (hi : i < r) : Disjoint (A' i) S :=
    (hA.outside i hi).mono_left (hsub i hi)
  refine ⟨A', Y, χ', hYS, hY, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro i hi
    rcases (show i ≤ r by omega).eq_or_lt with rfl | hi'
    · rw [hAnew, hX]
    · rw [hAold i hi']
      exact (hU i hi').2.1
  · intro i j hij hj
    rcases (show j ≤ r by omega).eq_or_lt with rfl | hj'
    · rw [hAnew]
      exact (hres i hij).mono_right hXS
    · exact (hA.disjoint i j hij hj').mono (hsub i (hij.trans hj')) (hsub j hj')
  · intro i hi
    rcases (show i ≤ r by omega).eq_or_lt with rfl | hi'
    · rw [hAnew]
      exact hXY
    · exact (hres i hi').mono_right hYS
  · intro i j hij hj x hx y hy
    rcases (show j ≤ r by omega).eq_or_lt with rfl | hj'
    · constructor
      · intro z hz
        simpa only [χ', if_pos rfl] using (hU i hij).2.2 x (hAold i hij ▸ hx)
          {y, z} (hgraph y (hAnew ▸ hy) z hz)
      · intro k hjk hk
        omega
    · have hprev := hA.colors i j hij hj' x (hsub i (hij.trans hj') hx) y (hsub j hj' hy)
      simp only [χ', if_neg hj'.ne]
      refine ⟨fun z hz ↦ hprev.1 z (hYS hz), fun k hjk hk z hz ↦ ?_⟩
      rcases (show k ≤ r by omega).eq_or_lt with rfl | hk'
      · exact hprev.1 z (hXS (hAnew ▸ hz))
      · exact hprev.2 k hjk hk' z (hsub k hk' hz)


private lemma focus_triples_many :
    ∀ r : ℕ, ∃ C : ℕ, ∀ (V : Type) [DecidableEq V] (col : Finset V → Bool) (s : ℕ), 0 < s → ∀ S : Finset V,
      (2 : ℝ) ^ (C * s ^ 2) ≤ (S.card : ℝ) →
      ∃ A Y χ, Y ⊆ S ∧ (S.card : ℝ) ≤ (2 : ℝ) ^ (C * s ^ 2) * (Y.card : ℝ) ∧
        TriplesFocused col r s A Y χ := by
  intro r
  induction r with
  | zero =>
    refine ⟨0, fun V _ col s _ S _ ↦ ⟨fun _ ↦ ∅, S, fun _ _ ↦ false, Subset.rfl, by simp, ⟨?_, ?_, ?_, ?_⟩⟩⟩
    · intro i hi
      omega
    · intro i j hij hj
      omega
    · intro i hi
      omega
    · intro i j hij hj
      omega
  | succ r ih =>
    obtain ⟨C, hC⟩ := ih
    let K := 3 * r + 2
    refine ⟨4 * C + (K + 3), fun V _ col s hs S hS ↦ ?_⟩
    have htrade : (4 * C + (K + 3)) * s ^ 2 = C * (2 * s) ^ 2 + (K + 3) * s ^ 2 := by ring
    rw [htrade, pow_add] at hS
    have hpower (k l : ℕ) (h : k ≤ l) : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l :=
      pow_le_pow_right₀ (by norm_num) h
    have hpow1 (k : ℕ) : 1 ≤ (2 : ℝ) ^ k := by simpa using hpower 0 k (Nat.zero_le _)
    have hCS : (2 : ℝ) ^ (C * (2 * s) ^ 2) ≤ (S.card : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left (hpow1 ((K + 3) * s ^ 2))
        (show 0 ≤ (2 : ℝ) ^ (C * (2 * s) ^ 2) by positivity)
      exact (by simpa only [mul_one] using hh.trans hS)
    obtain ⟨A, X, χ, hXS, hSX, hA⟩ := hC V col (2 * s) (by omega) S hCS
    have hX : (2 : ℝ) ^ ((K + 3) * s ^ 2) ≤ (X.card : ℝ) :=
      le_of_mul_le_mul_left (hS.trans hSX) (by positivity)
    have hX2 : 2 ≤ X.card := by
      have hk : 1 ≤ (K + 3) * s ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast (show (2 : ℝ) ≤ (X.card : ℝ) from (by simpa using hpower 1 _ hk |>.trans hX))
    let δ : ℝ := ((2 : ℝ) ^ (K * s))⁻¹
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδ_le : δ ≤ ((4 : ℝ) * 2 ^ (r * (2 * s + 1)))⁻¹ := by
      dsimp [δ]
      apply inv_anti₀ (by positivity)
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_add]
      apply hpower
      dsimp [K]
      have h1 : r ≤ r * s := Nat.le_mul_of_pos_right r hs
      nlinarith
    have hδpow : δ ^ s = ((2 : ℝ) ^ (K * s ^ 2))⁻¹ := by
      dsimp [δ]
      rw [inv_pow, ← pow_mul, pow_two, mul_assoc]
    have hsq : (2 : ℝ) * (s : ℝ) ^ 2 ≤ (2 : ℝ) ^ (3 * s ^ 2) := by
      exact_mod_cast (show 2 * s ^ 2 ≤ 2 ^ (3 * s ^ 2) from
        (show 2 * s ^ 2 ≤ 3 * s ^ 2 by omega).trans Nat.lt_two_pow_self.le)
    have hlarge : 2 * (s : ℝ) ^ 2 / (X.card : ℝ) ≤ δ ^ s := by
      rw [hδpow, ← one_div, div_le_div_iff₀ (by exact_mod_cast (show 0 < X.card by omega)) (by positivity),
        one_mul]
      calc
        _ ≤ (2 : ℝ) ^ (3 * s ^ 2) * (2 : ℝ) ^ (K * s ^ 2) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = (2 : ℝ) ^ ((K + 3) * s ^ 2) := by rw [← pow_add, add_comm (3 * s ^ 2), ← Nat.add_mul]
        _ ≤ (X.card : ℝ) := hX
    obtain ⟨B, Y, ψ, hYX, hY, hB⟩ := focus_triples_round col hA hX2 hδ hδ_le hlarge
    refine ⟨B, Y, ψ, hYX.trans hXS, hSX.trans ?_, hB⟩
    rw [htrade, pow_add, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hY' : (X.card : ℝ) ≤ (2 : ℝ) ^ (K * s ^ 2 + 1) * (Y.card : ℝ) := by
      rw [hδpow, inv_eq_one_div, div_div, pow_add, pow_one] at *
      rwa [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity), mul_comm] at hY
    exact hY'.trans (mul_le_mul_of_nonneg_right (hpower _ _ (by
      have h1 : 1 ≤ s ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc
        _ ≤ K * s ^ 2 + 3 * s ^ 2 := by omega
        _ = _ := (Nat.add_mul K 3 (s ^ 2)).symm)) (by positivity))


private lemma sorted_triple {V : Type} [LinearOrder V] (T : Finset V) (hT : T.card = 3) :
    ∃ i j k : V, i < j ∧ j < k ∧ T = {i, j, k} := by
  let e := T.orderEmbOfFin hT
  refine ⟨e 0, e 1, e 2, e.strictMono (by decide), e.strictMono (by decide), ?_⟩
  rw [← map_orderEmbOfFin_univ T hT]
  ext v
  simp only [Finset.mem_map, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [e]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private lemma focused_triples_mono_box {V : Type} [DecidableEq V] {col : Finset V → Bool}
    {r d s : ℕ} {A : ℕ → Finset V} {S : Finset V} {χ : ℕ → ℕ → Bool}
    (hA : TriplesFocused col r s A S χ) (hr : 2 ^ (d + d) ≤ r) :
    ∃ b : Bool, ∃ a : Fin d × Fin s ↪ V,
      ∀ u : Fin d → Fin s, MonoTuple 3 col b (fun i ↦ a (i, u i)) := by
  classical
  let c (E : Finset ℕ) : Bool :=
    if h : E.card = 2 then χ (E.orderEmbOfFin h 0) (E.orderEmbOfFin h 1) else false
  have hc {i j : ℕ} (hij : i < j) : c {i, j} = χ i j := by
    let f : Fin 2 → ℕ := ![i, j]
    have hf : StrictMono f := by
      exact strictMono_vecEmpty.vecCons hij
    have hcard : ({i, j} : Finset ℕ).card = 2 := card_pair hij.ne
    have hmem (k : Fin 2) : f k ∈ ({i, j} : Finset ℕ) := by
      fin_cases k <;> simp [f]
    simp only [c, dif_pos hcard, ← orderEmbOfFin_unique hcard hmem hf]
    rfl
  have h := graph_ramsey c d d (range r) (by simpa using hr)
  obtain ⟨b, T, hTr, hT, hTc⟩ :
      ∃ b : Bool, ∃ T ⊆ range r, T.card = d ∧ GraphMono c T b := by
    rcases h with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  let idx := T.orderEmbOfFin hT
  have hidx (i : Fin d) : idx i < r := mem_range.mp (hTr (T.orderEmbOfFin_mem hT i))
  let v (i : Fin d) : Fin s ≃ ↥(A (idx i)) :=
    ((A (idx i)).equivFinOfCardEq (hA.size _ (hidx i))).symm
  let f (p : Fin d × Fin s) : V := (v p.1 p.2).val
  have hf : Function.Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    have hdis {i j : Fin d} (hij : i < j) (x y : Fin s) : f (i, x) ≠ f (j, y) := by
      intro he'
      have hD := Finset.disjoint_left.mp (hA.disjoint _ _ (idx.strictMono hij) (hidx j))
      have hx : f (i, x) ∈ A (idx i) := (v i x).property
      have hy : f (j, y) ∈ A (idx j) := (v j y).property
      exact hD hx (he'.symm ▸ hy)
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hdis hij x y he).elim
    · exact congrArg (Prod.mk i) ((v i).injective (Subtype.ext he))
    · exact (hdis hji y x he.symm).elim
  refine ⟨b, ⟨f, hf⟩, fun u ↦ ⟨?_, ?_⟩⟩
  · intro i j h
    exact congrArg Prod.fst (hf h)
  · let g : Fin d ↪ V := ⟨fun i ↦ f (i, u i), fun i j h ↦ congrArg Prod.fst (hf h)⟩
    intro E hE
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hE
    have he : E ⊆ univ.map g := by
      rw [map_eq_image]
      exact hsub
    obtain ⟨U, _, hU⟩ := subset_map_iff.mp he
    have hUcard : U.card = 3 := by simpa only [hU, card_map] using hcard
    obtain ⟨i, j, k, hij, hjk, rfl⟩ := sorted_triple U hUcard
    have hp : {idx i, idx j} ∈ T.powersetCard 2 :=
      mem_powersetCard.mpr ⟨by
        intro l hl
        simp only [mem_insert, mem_singleton] at hl
        rcases hl with rfl | rfl <;> exact T.orderEmbOfFin_mem hT _, card_pair (idx.strictMono hij).ne⟩
    have hb : χ (idx i) (idx j) = b := (hc (idx.strictMono hij)).symm.trans (hTc _ hp)
    have hmono := (hA.colors _ _ (idx.strictMono hij) (hidx j)
      _ (v i (u i)).property _ (v j (u j)).property).2 _ (idx.strictMono hjk) (hidx k)
        _ (v k (u k)).property
    rw [hU, map_insert, map_insert, map_singleton]
    exact hmono.trans hb

private lemma logScale_isBigO_positive_three {α : ℝ} (hα : 0 < α) :
    logScale 3 =O[atTop] thresholdReal 3 α := by
  classical
  obtain ⟨D, hD⟩ := exists_nat_gt ((3 : ℝ) ^ 2 * ((2 : ℝ) ^ 3 * (3 : ℕ).factorial) / α)
  let d := max 6 D
  have hd : 0 < d := (by decide : 0 < 6).trans_le (le_max_left _ _)
  have htd : 2 * 3 ≤ d := le_max_left _ _
  have hratio : (3 : ℝ) ^ 2 * ((2 : ℝ) ^ 3 * ((3 : ℕ).factorial : ℝ)) < α * (d : ℝ) := by
    rw [mul_comm α, ← div_lt_iff₀ hα]
    exact hD.trans_le (Nat.cast_le.mpr (le_max_right _ _))
  let r := 2 ^ (d + d)
  obtain ⟨C, hC⟩ := show ∃ C : ℕ, 0 < C ∧ ∀ (V : Type) [DecidableEq V]
      (col : Finset V → Bool) (s : ℕ), 0 < s → ∀ S : Finset V,
      (2 : ℝ) ^ (C * s ^ 2) ≤ (S.card : ℝ) →
      ∃ A Y χ, TriplesFocused col r s A Y χ from by
    obtain ⟨C, hC⟩ := focus_triples_many r
    refine ⟨C + 1, by omega, fun V _ col s hs S hS ↦ ?_⟩
    have hc : C * s ^ 2 ≤ (C + 1) * s ^ 2 := Nat.mul_le_mul_right _ (Nat.le_succ _)
    obtain ⟨A, Y, χ, _, _, hA⟩ := hC V col s hs S
      ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hc).trans hS)
    exact ⟨A, Y, χ, hA⟩
  let δ : ℝ := ((2 : ℝ) ^ C)⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ < 1 := by
    dsimp [δ]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) hC.1.ne')
  obtain ⟨K, hK, hsize⟩ := eventually_log_box_size (d := 2) (by decide) hδ hδ'
  apply logScale_isBigO_of_sparse
  refine ⟨K, hK, ?_⟩
  filter_upwards [hsize, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro col
  obtain ⟨s, hs, hsmall, hlarge⟩ := hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbound : (2 : ℝ) ^ (C * s ^ 2) ≤ (n : ℝ) := by
    have hge : (1 : ℝ) ≤ ((2 * s : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast (show 1 ≤ (2 * s) ^ 2 from Nat.one_le_iff_ne_zero.mpr (by positivity))
    have h := (div_le_div_of_nonneg_right hge hnpos.le).trans hlarge.le
    rw [show δ ^ (s ^ 2) = ((2 : ℝ) ^ (C * s ^ 2))⁻¹ by
      dsimp [δ]
      rw [inv_pow, pow_mul]]
      at h
    exact (inv_le_inv₀ hnpos (by positivity)).1 (by simpa only [one_div] using h)
  obtain ⟨A, Y, χ, hA⟩ := hC.2 (Fin n) col s hs univ (by simpa using hbound)
  obtain ⟨b, a, ha⟩ := focused_triples_mono_box hA (show 2 ^ (d + d) ≤ r from le_rfl)
  obtain ⟨X, hX, hbad⟩ := sparse_of_mono_box hα hs htd hd hratio a ha
  refine ⟨X, hsmall.trans ?_, !b, hbad⟩
  exact_mod_cast (Nat.le_mul_of_pos_left s hd).trans_eq hX.symm

private lemma threshold_three_positive_theta {α : ℝ} (hα : 0 < α) (hα' : α < 1 / 2) :
    thresholdReal 3 α =Θ[atTop] thresholdReal 3 (1 / 4) :=
  (threshold_anchor_of_logScale_lower (by decide : 2 ≤ 3)
    (fun a ha _ ↦ logScale_isBigO_positive_three ha)).1 α hα hα'

private lemma threshold_three_jump_iff :
    (¬ (thresholdReal 3 (1 / 4) =O[atTop] thresholdReal 3 0)) ↔
      ∀ C : ℝ, 0 < C → ∀ N : ℕ, ∃ m ≥ N,
        C * (m : ℝ) ^ (3 - 1 : ℕ) < Real.log (diagonalRamsey 3 m : ℝ) := by
  exact (threshold_anchor_of_logScale_lower (by decide : 2 ≤ 3)
    (fun a ha _ ↦ logScale_isBigO_positive_three ha)).2.trans
      (logScale_not_isBigO_zero_iff_diagonalRamsey (by decide))

/-- Sample all but the first part of a box, then choose the first part
inside a common neighborhood. -/
private lemma exists_injective_box_last {V : Type} [Fintype V] [Nonempty V]
    {s d : ℕ} (hs : 0 < s) (hd : 0 < d) (P : (Fin (d + 1) → V) → Prop)
    {δ : ℝ} (hδ : 0 < δ) (hdense : δ ≤ 𝔼 x, indicator (P x))
    (hlarge : 4 * ((d * s : ℕ) : ℝ) ^ 2 / Fintype.card V ≤ δ ^ (s ^ d)) :
    ∃ a : Fin (d + 1) × Fin s ↪ V,
      ∀ u : Fin (d + 1) → Fin s, P (fun i ↦ a (i, u i)) := by
  classical
  let Q (y : V) (a : Fin d × Fin s → V) : Prop :=
    ∀ u : Fin d → Fin s, P (Fin.cons (α := fun _ ↦ V) y (fun i ↦ a (i, u i)))
  let F (a : Fin d × Fin s → V) : ℝ := 𝔼 y : V, indicator (Q y a)
  let μ (y : V) : ℝ := 𝔼 x : Fin d → V, indicator (P (Fin.cons (α := fun _ ↦ V) y x))
  have hF : δ ^ (s ^ d) ≤ 𝔼 a, F a := by
    have hbox (y : V) : μ y ^ (s ^ d) ≤ 𝔼 a : Fin d × Fin s → V, indicator (Q y a) := by
      let e : (Fin d → Fin s → V) ≃ (Fin d × Fin s → V) :=
        ⟨Function.uncurry, Function.curry, fun _ ↦ rfl, fun _ ↦ by funext ⟨_, _⟩; rfl⟩
      have h := expect_box s d (fun x ↦ P (Fin.cons (α := fun _ ↦ V) y x))
      have he := Fintype.expect_equiv e
        (fun a ↦ indicator (∀ u : Fin d → Fin s, P (Fin.cons (α := fun _ ↦ V) y (fun i ↦ a i (u i)))))
        (fun a ↦ indicator (Q y a)) (fun _ ↦ rfl)
      exact h.trans_eq he
    calc
      _ ≤ (𝔼 y, μ y) ^ (s ^ d) := by
        have he := expect_fin_cons (fun x ↦ indicator (P x))
        exact pow_le_pow_left₀ hδ.le (he ▸ hdense) _
      _ ≤ 𝔼 y, μ y ^ (s ^ d) :=
        expect_pow_le _ (fun _ ↦ Finset.expect_nonneg (fun _ _ ↦ indicator_nonneg _)) _
      _ ≤ 𝔼 y : V, 𝔼 a : Fin d × Fin s → V, indicator (Q y a) :=
        Finset.expect_le_expect (fun y _ ↦ hbox y)
      _ = _ := Finset.expect_comm _ _ _
  let G (a : Fin d × Fin s → V) : ℝ := if Function.Injective a then F a else 0
  have hpoint (a : Fin d × Fin s → V) : F a ≤ G a + indicator (¬ Function.Injective a) := by
    by_cases ha : Function.Injective a
    · simp [G, indicator, ha]
    · have hle : F a ≤ 1 :=
        Finset.expect_le (univ_nonempty : (univ : Finset V).Nonempty) (fun _ _ ↦ indicator_le_one _)
      simpa [G, indicator, ha] using hle
  have hinj := expect_noninjective (I := Fin d × Fin s) (V := V)
  simp only [Fintype.card_prod, Fintype.card_fin] at hinj
  have hG : δ ^ (s ^ d) / 2 ≤ 𝔼 a, G a := by
    have hh := hF.trans (Finset.expect_le_expect (fun a _ ↦ hpoint a))
    rw [Finset.expect_add_distrib] at hh
    rw [mul_div_assoc] at hlarge
    have h0 : 0 ≤ 𝔼 a : Fin d × Fin s → V, indicator (¬ Function.Injective a) :=
      Finset.expect_nonneg (fun _ _ ↦ indicator_nonneg _)
    linarith only [hh, hlarge, hinj, h0]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect univ_nonempty hG
  have hai : Function.Injective a := by
    by_contra h
    simp only [G, if_neg h] at ha
    exact (show (0 : ℝ) < δ ^ (s ^ d) / 2 by positivity).not_ge ha
  simp only [G, if_pos hai, F, expect_indicator_card] at ha
  let Y : Finset V := univ.filter (Q · a)
  let A : Finset V := univ.image a
  have hcard' : (0 : ℝ) < Fintype.card V := by positivity
  have hY : 2 * ((d * s : ℕ) : ℝ) ^ 2 ≤ (Y.card : ℝ) := by
    change δ ^ (s ^ d) / 2 ≤ (Y.card : ℝ) / Fintype.card V at ha
    rw [← div_mul_cancel₀ (2 * ((d * s : ℕ) : ℝ) ^ 2) hcard'.ne']
    apply (le_div_iff₀ hcard').1
    calc
      _ = (4 * ((d * s : ℕ) : ℝ) ^ 2 / Fintype.card V) / 2 := by ring
      _ ≤ _ := (div_le_div_iff_of_pos_right (by norm_num)).mpr hlarge
      _ ≤ _ := ha
  have hA : A.card = d * s := by
    simp [A, card_image_of_injective _ hai]
  have hY' : A.card + s ≤ Y.card := by
    rw [hA]
    have hsq : d * s ≤ (d * s) ^ 2 := by
      rw [pow_two]
      exact (Nat.le_mul_of_pos_right _ (by positivity))
    have hss : s ≤ d * s := Nat.le_mul_of_pos_left _ hd
    have hnat : 2 * (d * s) ^ 2 ≤ Y.card := by exact_mod_cast hY
    omega
  have hdiff : s ≤ (Y \ A).card := by
    have h := Finset.card_le_card (Finset.inter_subset_right (s₁ := Y) (s₂ := A))
    have h' := Finset.card_sdiff_add_card_inter Y A
    omega
  obtain ⟨Z, hZ, hZcard⟩ := exists_subset_card_eq hdiff
  let z := (Z.equivFinOfCardEq hZcard).symm
  let g (i : Fin (d + 1)) : Fin s → V :=
    Fin.cons (α := fun _ ↦ Fin s → V) (fun j ↦ (z j).val) (fun k j ↦ a (k, j)) i
  have hgi : Function.Injective (fun p : Fin (d + 1) × Fin s ↦ g p.1 p.2) := by
    rintro ⟨i, p⟩ ⟨j, q⟩ he
    refine Fin.cases (fun he ↦ ?_) (fun i he ↦ ?_) i he <;>
      refine Fin.cases (fun he ↦ ?_) (fun j he ↦ ?_) j he
    · exact congrArg (Prod.mk 0) (z.injective (Subtype.ext he))
    · have hz := mem_sdiff.mp (hZ (z p).property)
      change (z p).val = a (j, q) at he
      exact (hz.2 (he.symm ▸ mem_image_of_mem a (mem_univ (j, q)))).elim
    · have hz := mem_sdiff.mp (hZ (z q).property)
      change a (i, p) = (z q).val at he
      exact (hz.2 (he ▸ mem_image_of_mem a (mem_univ (i, p)))).elim
    · exact congrArg (fun w : Fin d × Fin s ↦ (w.1.succ, w.2)) (hai he)
  refine ⟨⟨fun p ↦ g p.1 p.2, hgi⟩, fun u ↦ ?_⟩
  have hy : (z (u 0)).val ∈ Y := (mem_sdiff.mp (hZ (z (u 0)).property)).1
  have hp := (mem_filter.mp hy).2 (fun i ↦ u i.succ)
  convert hp using 2
  rename_i i
  exact Fin.cases rfl (fun _ ↦ rfl) i

private lemma eventually_mono_box_on_logScale (d : ℕ) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∃ s : ℕ, 0 < s ∧
      K * logScale (d + 1) n ≤ (s : ℝ) ∧
      ∀ col : Finset (Fin n) → Bool, ∃ b : Bool, ∃ a : Fin (d + 1) × Fin s ↪ Fin n,
        ∀ u : Fin (d + 1) → Fin s, MonoTuple (d + 1) col b (fun i ↦ a (i, u i)) := by
  obtain ⟨δ, hδ, hδ1, N, hN⟩ := exists_dense_monoTuple (d + 1) (d + 1)
  obtain ⟨K, hK, hsize⟩ := eventually_log_box_size hd
    (show 0 < δ / 4 by positivity) (show δ / 4 < 1 by linarith)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hsize, eventually_ge_atTop (max N 1)] with n hn hNn
  obtain ⟨s, hs, hsmall, hlarge⟩ := hn
  refine ⟨s, hs, ?_, fun col ↦ ?_⟩
  · simpa only [logScale, Nat.add_sub_cancel] using hsmall
  · let : Nonempty (Fin n) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hNn)⟩⟩
    obtain ⟨b, hb⟩ := hN n ((le_max_left _ _).trans hNn) col
    refine ⟨b, exists_injective_box_last hs hd (MonoTuple (d + 1) col b) hδ hb ?_⟩
    rw [Fintype.card_fin]
    rw [div_pow] at hlarge
    have hp : (4 : ℝ) ≤ 4 ^ (s ^ d) := by
      simpa only [pow_one] using
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
          (Nat.one_le_iff_ne_zero.mpr (by positivity) : 1 ≤ s ^ d))
    rw [mul_div_assoc]
    calc
      _ ≤ (4 : ℝ) * (δ ^ (s ^ d) / 4 ^ (s ^ d)) :=
        mul_le_mul_of_nonneg_left hlarge.le (by norm_num)
      _ ≤ 4 ^ (s ^ d) * (δ ^ (s ^ d) / 4 ^ (s ^ d)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by rw [mul_comm, div_mul_cancel₀ _ (by positivity)]

private noncomputable def imbalance {V : Type} (col : Finset V → Bool)
    (b : Bool) (X : Finset V) (t : ℕ) : ℝ :=
  ∑ e ∈ X.powersetCard t, (if col e = b then 1 else -1)

private lemma imbalance_eq {V : Type} (col : Finset V → Bool) (b : Bool)
    (Y : Finset V) (t : ℕ) :
    imbalance col b Y t =
      2 * (((Y.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) - (Y.card.choose t : ℝ) := by
  unfold imbalance
  let E := Y.powersetCard t
  let p (e : Finset V) := col e = b
  change (∑ e ∈ E, (if p e then (1 : ℝ) else -1)) = 2 * ((E.filter p).card : ℝ) - (Y.card.choose t : ℝ)
  have hcount : (((E.filter p).card + (E.filter (fun e ↦ ¬ p e)).card : ℕ) : ℝ) =
      (Y.card.choose t : ℝ) := by
    rw [card_filter_add_card_filter_not, card_powersetCard]
  rw [← sum_filter_add_sum_filter_not E p]
  have hp : (∑ e ∈ E.filter p, (if p e then (1 : ℝ) else -1)) = ((E.filter p).card : ℝ) := by
    calc
      _ = ∑ _e ∈ E.filter p, (1 : ℝ) :=
        sum_congr rfl fun e he ↦ if_pos (mem_filter.mp he).2
      _ = _ := by simp
  have hn : (∑ e ∈ E.filter (fun e ↦ ¬ p e), (if p e then (1 : ℝ) else -1)) =
      -((E.filter (fun e ↦ ¬ p e)).card : ℝ) := by
    calc
      _ = ∑ _e ∈ E.filter (fun e ↦ ¬ p e), (-1 : ℝ) :=
        sum_congr rfl fun e he ↦ if_neg (mem_filter.mp he).2
      _ = _ := by simp
  rw [hp, hn, Nat.cast_add] at *
  linarith

private lemma imbalance_neg {V : Type} (col : Finset V → Bool) (b : Bool)
    (Y : Finset V) (t : ℕ) : imbalance col (!b) Y t = -imbalance col b Y t := by
  unfold imbalance
  rw [← Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro e _
  cases b <;> cases col e <;> norm_num

private lemma imbalance_of_mono_box {V : Type} [Fintype V] [DecidableEq V] {t s : ℕ}
    (ht : 0 < t) (hs : 0 < s) {col : Finset V → Bool} {b : Bool}
    (a : Fin t × Fin s ↪ V)
    (hbox : ∀ u : Fin t → Fin s, MonoTuple t col b (fun i ↦ a (i, u i))) :
    ∃ Y : Finset V, s ≤ Y.card ∧ Y.card ≤ t * s ∧
      (s : ℝ) ^ t / (2 : ℝ) ^ t ≤ |imbalance col b Y t| := by
  classical
  let A (i : Fin t) : Finset V := univ.image (fun j : Fin s ↦ a (i, j))
  let X := univ.map a
  let Y (T : Finset (Fin t)) := X.filter (fun x ↦ ∀ i ∈ T, x ∉ A i)
  let E := X.powersetCard t
  let W (i : Fin t) : Finset (Finset V) := univ.filter (fun e ↦ Disjoint e (A i))
  let edge (u : Fin t → Fin s) : Finset V := univ.image (fun i ↦ a (i, u i))
  let H : Finset (Finset V) := univ.image edge
  let z (e : Finset V) : ℝ := if col e = b then 1 else -1
  let f (e : Finset V) := if e ∈ E then z e else 0
  have hAcard (i : Fin t) : (A i).card = s := by
    have ha : Function.Injective (fun j : Fin s ↦ a (i, j)) := fun p q h ↦
      congrArg Prod.snd (a.injective h)
    simp [A, card_image_of_injective _ ha]
  have hXcard : X.card = t * s := by simp [X]
  have hedge (u : Fin t → Fin s) : (edge u).card = t := by
    simp [edge, card_image_of_injective _ (hbox u).1]
  have hE (u : Fin t → Fin s) : edge u ∈ E := by
    refine mem_powersetCard.mpr ⟨?_, hedge u⟩
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact mem_map_of_mem _ (mem_univ (i, u i))
  have hinj : Function.Injective edge := by
    intro u v huv
    funext i
    have hi : a (i, u i) ∈ edge v := huv ▸ mem_image_of_mem _ (mem_univ i)
    obtain ⟨j, _, hj⟩ := mem_image.mp hi
    have h := a.injective hj
    obtain rfl := congrArg Prod.fst h
    exact (congrArg Prod.snd h).symm
  have hHcard : H.card = s ^ t := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hH : (univ.inf (fun i ↦ (W i)ᶜ)) ∩ E = H := by
    ext e
    simp only [mem_inter, mem_inf, mem_univ, true_implies, mem_compl, W, mem_filter, true_and,
      not_disjoint_iff]
    constructor
    · rintro ⟨h, he⟩
      have hh (i : Fin t) : ∃ j : Fin s, a (i, j) ∈ e := by
        obtain ⟨x, hxe, hx⟩ := h i
        obtain ⟨j, _, rfl⟩ := mem_image.mp hx
        exact ⟨j, hxe⟩
      choose u hu using hh
      have hsub : edge u ⊆ e := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := mem_image.mp hx
        exact hu i
      exact mem_image.mpr ⟨u, mem_univ _, eq_of_subset_of_card_le hsub
        ((mem_powersetCard.mp he).2.trans (hedge u).symm).le⟩
    · intro he
      obtain ⟨u, _, rfl⟩ := mem_image.mp he
      exact ⟨fun i ↦ ⟨a (i, u i), mem_image_of_mem _ (mem_univ i),
        mem_image_of_mem _ (mem_univ (u i))⟩, hE u⟩
  have hY (T : Finset (Fin t)) : T.inf W ∩ E = (Y T).powersetCard t := by
    ext e
    simp only [mem_inter, mem_inf, W, mem_filter, mem_univ, true_and, E, mem_powersetCard, Y]
    constructor
    · rintro ⟨h, hsub, hcard⟩
      exact ⟨fun x hx ↦ mem_filter.mpr ⟨hsub hx, fun i hi ↦ disjoint_left.mp (h i hi) hx⟩, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨fun i hi ↦ disjoint_left.mpr (fun x hx ↦ (mem_filter.mp (hsub hx)).2 i hi),
        fun x hx ↦ (mem_filter.mp (hsub hx)).1, hcard⟩
  have hsum (R Z : Finset (Finset V)) (hz : R ∩ E = Z) :
      (∑ e ∈ R, f e) = ∑ e ∈ Z, z e := by
    subst Z
    rw [← sum_subset (inter_subset_left : R ∩ E ⊆ R) (f := f)]
    · apply sum_congr rfl
      intro e he
      exact if_pos (mem_inter.mp he).2
    · intro e he he'
      exact if_neg (fun heE ↦ he' (mem_inter.mpr ⟨he, heE⟩))
  have hmain := Finset.inclusion_exclusion_sum_inf_compl (univ : Finset (Fin t)) W f
  rw [hsum _ H hH] at hmain
  simp_rw [hsum _ _ (hY _)] at hmain
  have hsumH : (∑ e ∈ H, z e) = (s : ℝ) ^ t := by
    calc
      _ = ∑ _e ∈ H, (1 : ℝ) := by
        apply sum_congr rfl
        intro e he
        obtain ⟨u, _, rfl⟩ := mem_image.mp he
        apply if_pos
        exact (hbox u).2 _ (mem_powersetCard.mpr ⟨Subset.rfl, hedge u⟩)
      _ = _ := by simp [hHcard]
  rw [hsumH] at hmain
  have hmain' : (s : ℝ) ^ t = ∑ T : Finset (Fin t), (-1 : ℝ) ^ T.card * imbalance col b (Y T) t := by
    simpa only [powerset_univ, zpow_natCast, Int.cast_pow, Int.cast_neg, Int.cast_one, zsmul_eq_mul, imbalance, z] using hmain
  let L : ℝ := (s : ℝ) ^ t / (2 : ℝ) ^ t
  have hL : 0 < L := by dsimp [L]; positivity
  have hbound : ∃ T : Finset (Fin t), L ≤ |imbalance col b (Y T) t| := by
    by_contra! h
    have hsumlt : (∑ T : Finset (Fin t), |imbalance col b (Y T) t|) <
        ∑ _T : Finset (Fin t), L :=
      sum_lt_sum_of_nonempty univ_nonempty (fun T _ ↦ h T)
    have habs := abs_sum_le_sum_abs
      (fun T : Finset (Fin t) ↦ (-1 : ℝ) ^ T.card * imbalance col b (Y T) t) univ
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
    rw [← hmain', abs_of_nonneg (by positivity)] at habs
    have hconst : (∑ _T : Finset (Fin t), L) = (s : ℝ) ^ t := by
      simp only [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      dsimp [L]
      rw [mul_comm, div_mul_cancel₀ _ (by positivity)]
    exact (habs.trans_lt hsumlt).not_ge hconst.le
  obtain ⟨T, hT⟩ := hbound
  refine ⟨Y T, ?_, (card_le_card (filter_subset _ _)).trans_eq hXcard, hT⟩
  have hnonempty : (Y T).Nonempty := by
    by_contra h
    have hsel : Y T = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [hsel] at hT
    have hzero : imbalance col b ∅ t = 0 := by
      rw [imbalance]
      rw [powersetCard_eq_empty.mpr (by simpa using ht), sum_empty]
    exact hL.not_ge (by simpa only [hzero, abs_zero] using hT)
  obtain ⟨x, hx⟩ := hnonempty
  obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_map.mp (mem_filter.mp hx).1
  have hi : i ∉ T := fun hi ↦ (mem_filter.mp hx).2 _ hi (mem_image_of_mem _ (mem_univ j))
  have hsub : A i ⊆ Y T := by
    intro y hy
    obtain ⟨j', _, rfl⟩ := mem_image.mp hy
    refine mem_filter.mpr ⟨mem_map_of_mem _ (mem_univ (i, j')), fun k hk hAk ↦ ?_⟩
    obtain ⟨l, _, hl⟩ := mem_image.mp hAk
    have hki := congrArg Prod.fst (a.injective hl)
    change k = i at hki
    exact hi (hki ▸ hk)
  exact (hAcard i).symm.trans_le (card_le_card hsub)

private noncomputable def nearHalf (t : ℕ) : ℝ := 1 / 2 - ((2 * (t : ℝ)) ^ t)⁻¹ / 4

private lemma nearHalf_bounds {t : ℕ} (ht : 0 < t) :
    0 < nearHalf t ∧ nearHalf t < 1 / 2 := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hp : 0 < (2 * (t : ℝ)) ^ t := by positivity
  have hq : ((2 * (t : ℝ)) ^ t)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith) : 1 ≤ (2 * (t : ℝ)) ^ t)
  have hp' := inv_pos.mpr hp
  unfold nearHalf
  constructor <;> linarith

private lemma sparse_nearHalf_of_mono_box {n t s : ℕ} (ht : 0 < t) (hs : 0 < s)
    {col : Finset (Fin n) → Bool} {b : Bool} (a : Fin t × Fin s ↪ Fin n)
    (hbox : ∀ u : Fin t → Fin s, MonoTuple t col b (fun i ↦ a (i, u i))) :
    ∃ Y : Finset (Fin n), s ≤ Y.card ∧ ∃ c : Bool,
      (((Y.powersetCard t).filter (fun e ↦ col e = c)).card : ℝ) <
        nearHalf t * (Y.card.choose t : ℝ) := by
  obtain ⟨Y, hYs, hYt, hY⟩ := imbalance_of_mono_box ht hs a hbox
  let η : ℝ := ((2 * (t : ℝ)) ^ t)⁻¹
  have hη : 0 < η := by dsimp [η]; positivity
  have hpos : 0 < (Y.card.choose t : ℝ) := by
    apply Nat.cast_pos.mpr
    by_contra! h
    have hempty : Y.powersetCard t = ∅ := by
      exact card_eq_zero.mp (by rw [card_powersetCard]; omega)
    have hz : imbalance col b Y t = 0 := by rw [imbalance, hempty, sum_empty]
    rw [hz, abs_zero] at hY
    exact (show (0 : ℝ) < (s : ℝ) ^ t / (2 : ℝ) ^ t by positivity).not_ge hY
  have hYchoose : (Y.card.choose t : ℝ) ≤ ((t : ℝ) * (s : ℝ)) ^ t := by
    have hN := (Nat.choose_le_pow Y.card t).trans (Nat.pow_le_pow_left hYt t)
    exact_mod_cast hN
  have hle : η * (Y.card.choose t : ℝ) ≤ (s : ℝ) ^ t / (2 : ℝ) ^ t := by
    refine (mul_le_mul_of_nonneg_left hYchoose hη.le).trans_eq ?_
    dsimp [η]
    have htp : (t : ℝ) ^ t ≠ 0 := by positivity
    rw [mul_pow, mul_pow, mul_inv, div_eq_inv_mul]
    calc
      _ = ((t : ℝ) ^ t)⁻¹ * (t : ℝ) ^ t * (((2 : ℝ) ^ t)⁻¹ * (s : ℝ) ^ t) := by ring
      _ = _ := by rw [inv_mul_cancel₀ htp, one_mul]
  obtain ⟨c, hc⟩ : ∃ c, imbalance col c Y t = -|imbalance col b Y t| := by
    by_cases h : 0 ≤ imbalance col b Y t
    · exact ⟨!b, by rw [imbalance_neg, abs_of_nonneg h]⟩
    · exact ⟨b, by rw [abs_of_neg (lt_of_not_ge h), neg_neg]⟩
  refine ⟨Y, hYs, c, ?_⟩
  rw [imbalance_eq] at hc
  have hh := hle.trans hY
  have hgap : 0 < η * (Y.card.choose t : ℝ) := mul_pos hη hpos
  change _ < (1 / 2 - η / 4) * (Y.card.choose t : ℝ)
  nlinarith only [hh, hc, hgap]

private lemma threshold_nearHalf_theta {t : ℕ} (ht : 2 ≤ t) :
    thresholdReal t (nearHalf t) =Θ[atTop] logScale t := by
  have ht' := nearHalf_bounds (show 0 < t by omega)
  refine ⟨threshold_isBigO_log_rpow ht ht'.1.le ht'.2, logScale_isBigO_of_sparse ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, t = d + 1 := ⟨t - 1, by omega⟩
  obtain ⟨K, hK, hsize⟩ := eventually_mono_box_on_logScale d (by omega)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hsize] with n hn
  intro col
  obtain ⟨s, hs, hsmall, hboxes⟩ := hn
  obtain ⟨b, a, hbox⟩ := hboxes col
  obtain ⟨Y, hY, c, hc⟩ := sparse_nearHalf_of_mono_box (by omega) hs a hbox
  exact ⟨Y, hsmall.trans (by exact_mod_cast hY), c, hc⟩

private lemma threshold_positive_anchor_iff_logScale {t : ℕ} (ht : 2 ≤ t) :
    (∀ a : ℝ, 0 < a → a < 1 / 2 →
      thresholdReal t a =Θ[atTop] thresholdReal t (1 / 4)) ↔
    (∀ a : ℝ, 0 < a → a < 1 / 2 →
      logScale t =O[atTop] thresholdReal t a) := by
  constructor
  · intro h a ha ha'
    have hb := nearHalf_bounds (show 0 < t by omega)
    exact (threshold_nearHalf_theta ht).2.trans ((h _ hb.1 hb.2).1.trans (h a ha ha').2)
  · exact fun h ↦ (threshold_anchor_of_logScale_lower ht h).1

private lemma threshold_theta_near_half_interval {t : ℕ} (ht : 2 ≤ t) {α : ℝ}
    (hα : nearHalf t ≤ α) (hα' : α < 1 / 2) :
    thresholdReal t α =Θ[atTop] logScale t := by
  have hα0 := (nearHalf_bounds (show 0 < t by omega)).1.le.trans hα
  exact ⟨threshold_isBigO_log_rpow ht hα0 hα',
    (threshold_nearHalf_theta ht).2.trans (threshold_isBigO_mono hα)⟩

open scoped Classical in
private def HasSparseSubsetsAtLogScale (t : ℕ) (α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ col : Finset (Fin n) → Bool,
      ∃ X : Finset (Fin n), c * logScale t n ≤ (X.card : ℝ) ∧ ∃ b : Bool,
        (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) <
          α * (X.card.choose t : ℝ)

private lemma logScale_isBigO_iff_sparse {t : ℕ} (ht : 2 ≤ t) {α : ℝ} (hα : 0 < α) :
    (logScale t =O[atTop] thresholdReal t α) ↔ HasSparseSubsetsAtLogScale t α := by
  classical
  refine ⟨?_, logScale_isBigO_of_sparse⟩
  intro h
  obtain ⟨C, hC, hbound⟩ := h.exists_pos
  let x (n : ℕ) := (1 / (2 * C)) * logScale t n
  have hr : 0 < (((t - 1 : ℕ) : ℝ)⁻¹) := inv_pos.mpr (by
    exact_mod_cast (show 0 < t - 1 by omega))
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hx : Tendsto x atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      ((tendsto_rpow_atTop hr).comp hlog)
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  filter_upwards [hbound.bound, hx.eventually_ge_atTop ((t : ℝ) + 2),
    eventually_ge_atTop (1 : ℕ)] with n hn hxn hn1
  intro col
  let m := ⌊x n⌋₊
  have hx0 : 0 ≤ x n := by linarith only [hxn, Nat.cast_nonneg (α := ℝ) t]
  have hfloor : (m : ℝ) ≤ x n := Nat.floor_le hx0
  have hfloort : x n < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmt : t ≤ m := by
    exact_mod_cast (show (t : ℝ) ≤ (m : ℝ) by linarith only [hxn, hfloort])
  have hsmall : 1 / (4 * C) * logScale t n ≤ (m : ℝ) := by
    have hx2 : 1 / (4 * C) * logScale t n = x n / 2 := by dsimp [x]; ring
    rw [hx2]
    linarith only [hxn, hfloort, Nat.cast_nonneg (α := ℝ) t]
  have hscale : 0 ≤ logScale t n := Real.rpow_nonneg
    (Real.log_nonneg (by exact_mod_cast hn1)) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale,
    abs_of_nonneg (Nat.cast_nonneg _)] at hn
  have hlarge : (m : ℝ) < thresholdReal t α n := by
    have h2x : 2 * x n ≤ thresholdReal t α n := by
      rw [show 2 * x n = logScale t n / C by dsimp [x]; ring, div_le_iff₀ hC, mul_comm]
      exact hn
    exact hfloor.trans_lt (by linarith only [h2x, hxn, Nat.cast_nonneg (α := ℝ) t])
  by_contra! hcol
  apply hlarge.not_ge
  apply Nat.cast_le.mpr
  apply threshold_le
  refine ⟨col, fun X hX b ↦ ?_⟩
  have hsize : 1 / (4 * C) * logScale t n ≤ (X.card : ℝ) :=
    hsmall.trans (Nat.cast_le.mpr hX)
  have hden := hcol X hsize b
  have hp : 0 < (X.card.choose t : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (hmt.trans hX))
  exact ⟨by exact_mod_cast (mul_pos hα hp).trans_le hden, hden⟩

private lemma threshold_positive_anchor_iff_sparse_below_nearHalf {t : ℕ} (ht : 2 ≤ t) :
    (∀ a : ℝ, 0 < a → a < 1 / 2 →
      thresholdReal t a =Θ[atTop] thresholdReal t (1 / 4)) ↔
    (∀ a : ℝ, 0 < a → a < nearHalf t → HasSparseSubsetsAtLogScale t a) := by
  rw [threshold_positive_anchor_iff_logScale ht]
  constructor
  · intro h a ha ha'
    exact (logScale_isBigO_iff_sparse ht ha).mp
      (h a ha (ha'.trans (nearHalf_bounds (show 0 < t by omega)).2))
  · intro h a ha ha'
    by_cases hsmall : a < nearHalf t
    · exact (logScale_isBigO_iff_sparse ht ha).mpr (h a ha hsmall)
    · exact (threshold_theta_near_half_interval ht (le_of_not_gt hsmall) ha').2

private lemma descFactorial_le_pow_nat (m t : ℕ) :
    m.descFactorial t ≤ m ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.descFactorial_succ, pow_succ']
    exact Nat.mul_le_mul (Nat.sub_le m t) ih

private lemma factorial_mul_choose_le_pow (m t : ℕ) :
    t.factorial * m.choose t ≤ m ^ t := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact descFactorial_le_pow_nat m t

private lemma descFactorial_lt_pow_nat {m t : ℕ} (hm : 1 ≤ m) (ht : 2 ≤ t) :
    m.descFactorial t < m ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases (show t = 1 ∨ 2 ≤ t by omega) with rfl | ht2
    · rw [Nat.descFactorial_succ, Nat.descFactorial_one, pow_two]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    · rw [Nat.descFactorial_succ, pow_succ']
      calc
        (m - t) * m.descFactorial t ≤ m * m.descFactorial t :=
          Nat.mul_le_mul_right _ (Nat.sub_le m t)
        _ < m * m ^ t := Nat.mul_lt_mul_of_pos_left (ih ht2) (by omega)

private lemma factorial_mul_choose_lt_pow {m t : ℕ} (hm : 1 ≤ m) (ht : 2 ≤ t) :
    t.factorial * m.choose t < m ^ t := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact descFactorial_lt_pow_nat hm ht

private noncomputable def sharpNearHalfDenom (t : ℕ) : ℝ :=
  ∑ k ∈ range (t + 1), (t.choose k : ℝ) * (k : ℝ) ^ t

private noncomputable def sharpNearHalf (t : ℕ) : ℝ :=
  1 / 2 - (t.factorial : ℝ) / (2 * sharpNearHalfDenom t)

private lemma sum_finset_card_compl_pow (t : ℕ) :
    (∑ T : Finset (Fin t), ((t - T.card : ℕ) : ℝ) ^ t) = sharpNearHalfDenom t := by
  classical
  have hcompl :
      (∑ T : Finset (Fin t), ((t - T.card : ℕ) : ℝ) ^ t) =
        ∑ T : Finset (Fin t), (T.card : ℝ) ^ t := by
    refine Finset.sum_bij (fun T _ ↦ Tᶜ) (fun _ _ ↦ mem_univ _) ?_ ?_ ?_
    · intro T₁ _ T₂ _ h
      simpa only [compl_compl] using congrArg compl h
    · intro T _
      exact ⟨Tᶜ, mem_univ _, compl_compl T⟩
    · intro T _
      rw [card_compl, Fintype.card_fin]
  rw [hcompl]
  have hmaps : ∀ T ∈ (univ : Finset (Finset (Fin t))), T.card ∈ range (t + 1) := by
    intro T _
    have hle : T.card ≤ t := by simpa using card_le_univ T
    exact mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  unfold sharpNearHalfDenom
  apply sum_congr rfl
  intro k hk
  have hfilt :
      (univ : Finset (Finset (Fin t))).filter (fun T ↦ T.card = k) =
        (univ : Finset (Fin t)).powersetCard k := by
    ext T
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
  rw [hfilt]
  calc
    (∑ T ∈ (univ : Finset (Fin t)).powersetCard k, (T.card : ℝ) ^ t)
      = ∑ _T ∈ (univ : Finset (Fin t)).powersetCard k, (k : ℝ) ^ t := by
        apply sum_congr rfl
        intro T hT
        rw [(mem_powersetCard.mp hT).2]
    _ = (t.choose k : ℝ) * (k : ℝ) ^ t := by
        simp only [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma sharpNearHalfDenom_le (t : ℕ) :
    sharpNearHalfDenom t ≤ (2 * (t : ℝ)) ^ t := by
  unfold sharpNearHalfDenom
  calc
    (∑ k ∈ range (t + 1), (t.choose k : ℝ) * (k : ℝ) ^ t)
      ≤ ∑ k ∈ range (t + 1), (t.choose k : ℝ) * (t : ℝ) ^ t := by
        apply sum_le_sum
        intro k hk
        have hkt : k ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hk)
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hkt) t)
          (Nat.cast_nonneg _)
    _ = (∑ k ∈ range (t + 1), (t.choose k : ℝ)) * (t : ℝ) ^ t := by
        rw [← sum_mul]
    _ = (2 : ℝ) ^ t * (t : ℝ) ^ t := by
        have hsum : (∑ k ∈ range (t + 1), (t.choose k : ℝ)) = (2 : ℝ) ^ t := by
          exact_mod_cast Nat.sum_range_choose t
        rw [hsum]
    _ = (2 * (t : ℝ)) ^ t := by rw [mul_pow]

private lemma factorial_lt_sharpNearHalfDenom {t : ℕ} (ht : 2 ≤ t) :
    (t.factorial : ℝ) < sharpNearHalfDenom t := by
  have hfac_le : t.factorial ≤ t ^ t := by
    simpa only [Nat.choose_self, mul_one] using factorial_mul_choose_le_pow t t
  have hsub : ({1, t} : Finset ℕ) ⊆ range (t + 1) := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact mem_range.mpr (by omega)
  have hne : (1 : ℕ) ≠ t := by omega
  have hsum :
      (t.choose 1 : ℝ) * (1 : ℝ) ^ t + (t.choose t : ℝ) * (t : ℝ) ^ t ≤
        sharpNearHalfDenom t := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun k : ℕ ↦ (t.choose k : ℝ) * (k : ℝ) ^ t) hsub (fun k _ _ ↦ by positivity)
    simpa only [sharpNearHalfDenom, sum_pair hne, Nat.cast_one] using hle
  simp only [Nat.choose_one_right, one_pow, mul_one, Nat.choose_self, Nat.cast_one, one_mul] at hsum
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hfacR : (t.factorial : ℝ) ≤ (t : ℝ) ^ t := by exact_mod_cast hfac_le
  linarith

private lemma sharpNearHalf_bounds {t : ℕ} (ht : 2 ≤ t) :
    0 < sharpNearHalf t ∧ sharpNearHalf t < 1 / 2 := by
  have hfac : (0 : ℝ) < (t.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos t)
  have hlt := factorial_lt_sharpNearHalfDenom ht
  have hden : 0 < sharpNearHalfDenom t := hfac.trans hlt
  have hdiv_pos : 0 < (t.factorial : ℝ) / (2 * sharpNearHalfDenom t) := by positivity
  have hdiv_lt : (t.factorial : ℝ) / (2 * sharpNearHalfDenom t) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  unfold sharpNearHalf
  constructor <;> linarith

private lemma sharpNearHalf_lt_nearHalf {t : ℕ} (ht : 2 ≤ t) :
    sharpNearHalf t < nearHalf t := by
  have hfac_ge : (2 : ℝ) ≤ (t.factorial : ℝ) := by
    exact_mod_cast (show 2 ≤ t.factorial from by
      simpa only [Nat.factorial_two] using Nat.factorial_le ht)
  have hfac_pos : (0 : ℝ) < (t.factorial : ℝ) := by linarith
  have hden_pos : 0 < sharpNearHalfDenom t := hfac_pos.trans (factorial_lt_sharpNearHalfDenom ht)
  have hden_le := sharpNearHalfDenom_le t
  have hpow_pos : 0 < (2 * (t : ℝ)) ^ t := by
    have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
    positivity
  have hcmp : ((2 * (t : ℝ)) ^ t)⁻¹ / 4 < (t.factorial : ℝ) / (2 * sharpNearHalfDenom t) := by
    rw [inv_eq_one_div, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hfac_ge, hden_le, hpow_pos, hden_pos]
  unfold sharpNearHalf nearHalf
  linarith

private lemma sharpNearHalf_two : sharpNearHalf 2 = 1 / 3 := by
  unfold sharpNearHalf sharpNearHalfDenom
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.factorial]

private lemma sharpNearHalf_three : sharpNearHalf 3 = 4 / 9 := by
  unfold sharpNearHalf sharpNearHalfDenom
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.factorial]

private lemma sharpNearHalf_four : sharpNearHalf 4 = 41 / 85 := by
  unfold sharpNearHalf sharpNearHalfDenom
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.factorial]

private lemma imbalance_sum_mono_box {V : Type} [Fintype V] [DecidableEq V] {t s : ℕ}
    {col : Finset V → Bool} {b : Bool} (a : Fin t × Fin s ↪ V)
    (hbox : ∀ u : Fin t → Fin s, MonoTuple t col b (fun i ↦ a (i, u i))) :
    (s : ℝ) ^ t =
      ∑ T : Finset (Fin t),
        (-1 : ℝ) ^ T.card *
          imbalance col b ((Tᶜ ×ˢ (univ : Finset (Fin s))).map a) t := by
  classical
  let A (i : Fin t) : Finset V := univ.image (fun j : Fin s ↦ a (i, j))
  let X := univ.map a
  let Y (T : Finset (Fin t)) := (Tᶜ ×ˢ (univ : Finset (Fin s))).map a
  let E := X.powersetCard t
  let W (i : Fin t) : Finset (Finset V) := univ.filter (fun e ↦ Disjoint e (A i))
  let edge (u : Fin t → Fin s) : Finset V := univ.image (fun i ↦ a (i, u i))
  let H : Finset (Finset V) := univ.image edge
  let z (e : Finset V) : ℝ := if col e = b then 1 else -1
  let f (e : Finset V) := if e ∈ E then z e else 0
  have hedge (u : Fin t → Fin s) : (edge u).card = t := by
    simp [edge, card_image_of_injective _ (hbox u).1]
  have hE (u : Fin t → Fin s) : edge u ∈ E := by
    refine mem_powersetCard.mpr ⟨?_, hedge u⟩
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact mem_map_of_mem _ (mem_univ (i, u i))
  have hinj : Function.Injective edge := by
    intro u v huv
    funext i
    have hi : a (i, u i) ∈ edge v := huv ▸ mem_image_of_mem _ (mem_univ i)
    obtain ⟨j, _, hj⟩ := mem_image.mp hi
    have h := a.injective hj
    obtain rfl := congrArg Prod.fst h
    exact (congrArg Prod.snd h).symm
  have hHcard : H.card = s ^ t := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
  have hH : (univ.inf (fun i ↦ (W i)ᶜ)) ∩ E = H := by
    ext e
    simp only [mem_inter, mem_inf, mem_univ, true_implies, mem_compl, W, mem_filter, true_and,
      not_disjoint_iff]
    constructor
    · rintro ⟨h, he⟩
      have hh (i : Fin t) : ∃ j : Fin s, a (i, j) ∈ e := by
        obtain ⟨x, hxe, hx⟩ := h i
        obtain ⟨j, _, rfl⟩ := mem_image.mp hx
        exact ⟨j, hxe⟩
      choose u hu using hh
      have hsub : edge u ⊆ e := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := mem_image.mp hx
        exact hu i
      exact mem_image.mpr ⟨u, mem_univ _, eq_of_subset_of_card_le hsub
        ((mem_powersetCard.mp he).2.trans (hedge u).symm).le⟩
    · intro he
      obtain ⟨u, _, rfl⟩ := mem_image.mp he
      exact ⟨fun i ↦ ⟨a (i, u i), mem_image_of_mem _ (mem_univ i),
        mem_image_of_mem _ (mem_univ (u i))⟩, hE u⟩
  have hY (T : Finset (Fin t)) : T.inf W ∩ E = (Y T).powersetCard t := by
    ext e
    simp only [mem_inter, mem_inf, W, mem_filter, mem_univ, true_and, E, mem_powersetCard, Y, X]
    constructor
    · rintro ⟨h, hsub, hcard⟩
      refine ⟨fun x hx ↦ ?_, hcard⟩
      obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_map.mp (hsub hx)
      refine Finset.mem_map.mpr ⟨(i, j), mem_product.mpr ⟨mem_compl.mpr ?_, mem_univ j⟩, rfl⟩
      intro hi
      exact disjoint_left.mp (h i hi) hx (mem_image_of_mem _ (mem_univ j))
    · rintro ⟨hsub, hcard⟩
      refine ⟨fun i hi ↦ disjoint_left.mpr (fun x hx hxA ↦ ?_), fun x hx ↦ ?_, hcard⟩
      · obtain ⟨⟨i', j'⟩, hp, rfl⟩ := Finset.mem_map.mp (hsub hx)
        obtain ⟨j, _, hj⟩ := mem_image.mp hxA
        have heq := congrArg Prod.fst (a.injective hj)
        exact (mem_compl.mp (mem_product.mp hp).1) (heq ▸ hi)
      · obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp (hsub hx)
        exact mem_map_of_mem a (mem_univ p)
  have hsum (R Z : Finset (Finset V)) (hz : R ∩ E = Z) :
      (∑ e ∈ R, f e) = ∑ e ∈ Z, z e := by
    subst Z
    rw [← sum_subset (inter_subset_left : R ∩ E ⊆ R) (f := f)]
    · apply sum_congr rfl
      intro e he
      exact if_pos (mem_inter.mp he).2
    · intro e he he'
      exact if_neg (fun heE ↦ he' (mem_inter.mpr ⟨he, heE⟩))
  have hmain := Finset.inclusion_exclusion_sum_inf_compl (univ : Finset (Fin t)) W f
  rw [hsum _ H hH] at hmain
  simp_rw [hsum _ _ (hY _)] at hmain
  have hsumH : (∑ e ∈ H, z e) = (s : ℝ) ^ t := by
    calc
      _ = ∑ _e ∈ H, (1 : ℝ) := by
        apply sum_congr rfl
        intro e he
        obtain ⟨u, _, rfl⟩ := mem_image.mp he
        apply if_pos
        exact (hbox u).2 _ (mem_powersetCard.mpr ⟨Subset.rfl, hedge u⟩)
      _ = _ := by simp [hHcard]
  rw [hsumH] at hmain
  simpa only [powerset_univ, zpow_natCast, Int.cast_pow, Int.cast_neg, Int.cast_one,
    zsmul_eq_mul, imbalance, z, Y] using hmain

private lemma sharp_sparse_of_mono_box {n t s : ℕ} (ht : 2 ≤ t) (hs : 0 < s)
    {col : Finset (Fin n) → Bool} {b : Bool} (a : Fin t × Fin s ↪ Fin n)
    (hbox : ∀ u : Fin t → Fin s, MonoTuple t col b (fun i ↦ a (i, u i))) :
    ∃ Y : Finset (Fin n), s ≤ Y.card ∧ ∃ c : Bool,
      (((Y.powersetCard t).filter (fun e ↦ col e = c)).card : ℝ) <
        sharpNearHalf t * (Y.card.choose t : ℝ) := by
  classical
  let Y (T : Finset (Fin t)) : Finset (Fin n) := (Tᶜ ×ˢ (univ : Finset (Fin s))).map a
  have hYcard (T : Finset (Fin t)) : (Y T).card = (t - T.card) * s := by
    simp only [Y, card_map, card_product, card_compl, Fintype.card_fin, card_univ]
  by_contra! hbal
  have himb_le (T : Finset (Fin t)) :
      |imbalance col b (Y T) t| ≤ (1 - 2 * sharpNearHalf t) * ((Y T).card.choose t : ℝ) := by
    by_cases hT : T = univ
    · subst hT
      have hYc : (Y univ).card = 0 := by simp [hYcard]
      have hemp : (Y univ).powersetCard t = ∅ :=
        powersetCard_eq_empty.mpr (by rw [hYc]; omega)
      have hzero : imbalance col b (Y univ) t = 0 := by rw [imbalance, hemp, sum_empty]
      have hch : (Y univ).card.choose t = 0 := by rw [hYc]; exact Nat.choose_eq_zero_of_lt (by omega)
      simp [hzero, hch]
    · have hlt : T.card < t := by
        simpa only [card_univ, Fintype.card_fin] using card_lt_card (ssubset_univ_iff.mpr hT)
      have hge : s ≤ (Y T).card := by
        rw [hYcard]
        exact Nat.le_mul_of_pos_left s (by omega)
      have h1 := hbal (Y T) hge b
      have h2 := hbal (Y T) hge (!b)
      have heq1 := imbalance_eq col b (Y T) t
      have heq2 := imbalance_eq col (!b) (Y T) t
      rw [imbalance_neg] at heq2
      rw [abs_le]
      constructor <;> linarith
  have hsum := imbalance_sum_mono_box a hbox
  have habs := abs_sum_le_sum_abs
    (fun T : Finset (Fin t) ↦ (-1 : ℝ) ^ T.card * imbalance col b (Y T) t) univ
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
  rw [← hsum, abs_of_nonneg (by positivity)] at habs
  have hcoeff : 1 - 2 * sharpNearHalf t = (t.factorial : ℝ) / sharpNearHalfDenom t := by
    unfold sharpNearHalf
    ring
  have hfac_pos : (0 : ℝ) < (t.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos t)
  have hden_pos : 0 < sharpNearHalfDenom t := hfac_pos.trans (factorial_lt_sharpNearHalfDenom ht)
  have hcoeff_pos : 0 < 1 - 2 * sharpNearHalf t := by
    rw [hcoeff]
    positivity
  have hterm_le (T : Finset (Fin t)) :
      ((Y T).card.choose t : ℝ) ≤
        ((t - T.card : ℕ) : ℝ) ^ t * ((s : ℝ) ^ t / (t.factorial : ℝ)) := by
    rw [hYcard, mul_div_assoc', le_div_iff₀ hfac_pos, mul_comm _ (t.factorial : ℝ), ← mul_pow]
    exact_mod_cast factorial_mul_choose_le_pow ((t - T.card) * s) t
  have hterm_lt :
      ((Y ∅).card.choose t : ℝ) <
        ((t - (∅ : Finset (Fin t)).card : ℕ) : ℝ) ^ t * ((s : ℝ) ^ t / (t.factorial : ℝ)) := by
    rw [hYcard, mul_div_assoc', lt_div_iff₀ hfac_pos, mul_comm _ (t.factorial : ℝ), ← mul_pow]
    have hpos : 1 ≤ (t - (∅ : Finset (Fin t)).card) * s := by
      simp only [card_empty, Nat.sub_zero]
      exact Nat.mul_pos (by omega) hs
    exact_mod_cast factorial_mul_choose_lt_pow hpos ht
  have hchoose_lt :
      (∑ T : Finset (Fin t), ((Y T).card.choose t : ℝ)) <
        sharpNearHalfDenom t * ((s : ℝ) ^ t / (t.factorial : ℝ)) := by
    calc
      (∑ T : Finset (Fin t), ((Y T).card.choose t : ℝ))
        < ∑ T : Finset (Fin t),
            ((t - T.card : ℕ) : ℝ) ^ t * ((s : ℝ) ^ t / (t.factorial : ℝ)) :=
          Finset.sum_lt_sum (fun T _ ↦ hterm_le T) ⟨∅, mem_univ _, hterm_lt⟩
      _ = (∑ T : Finset (Fin t), ((t - T.card : ℕ) : ℝ) ^ t) *
            ((s : ℝ) ^ t / (t.factorial : ℝ)) := by rw [← sum_mul]
      _ = sharpNearHalfDenom t * ((s : ℝ) ^ t / (t.factorial : ℝ)) := by
          rw [sum_finset_card_compl_pow]
  have hstrict : (s : ℝ) ^ t < (s : ℝ) ^ t := calc
    (s : ℝ) ^ t
      ≤ ∑ T : Finset (Fin t), |imbalance col b (Y T) t| := habs
    _ ≤ ∑ T : Finset (Fin t), (1 - 2 * sharpNearHalf t) * ((Y T).card.choose t : ℝ) :=
        sum_le_sum fun T _ ↦ himb_le T
    _ = (1 - 2 * sharpNearHalf t) * ∑ T : Finset (Fin t), ((Y T).card.choose t : ℝ) := by
        rw [← mul_sum]
    _ < (1 - 2 * sharpNearHalf t) * (sharpNearHalfDenom t * ((s : ℝ) ^ t / (t.factorial : ℝ))) :=
        mul_lt_mul_of_pos_left hchoose_lt hcoeff_pos
    _ = (s : ℝ) ^ t := by
        rw [hcoeff]
        field_simp [hden_pos.ne', hfac_pos.ne']
  exact lt_irrefl _ hstrict

private lemma threshold_sharpNearHalf_theta {t : ℕ} (ht : 2 ≤ t) :
    thresholdReal t (sharpNearHalf t) =Θ[atTop] logScale t := by
  have ht' := sharpNearHalf_bounds ht
  refine ⟨threshold_isBigO_log_rpow ht ht'.1.le ht'.2, logScale_isBigO_of_sparse ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, t = d + 1 := ⟨t - 1, by omega⟩
  obtain ⟨K, hK, hsize⟩ := eventually_mono_box_on_logScale d (by omega)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hsize] with n hn
  intro col
  obtain ⟨s, hs, hsmall, hboxes⟩ := hn
  obtain ⟨b, a, hbox⟩ := hboxes col
  obtain ⟨Y, hY, c, hc⟩ := sharp_sparse_of_mono_box ht hs a hbox
  exact ⟨Y, hsmall.trans (by exact_mod_cast hY), c, hc⟩

private lemma threshold_theta_sharpNearHalf_interval {t : ℕ} (ht : 2 ≤ t) {α : ℝ}
    (hα : sharpNearHalf t ≤ α) (hα' : α < 1 / 2) :
    thresholdReal t α =Θ[atTop] logScale t := by
  have hα0 := (sharpNearHalf_bounds ht).1.le.trans hα
  exact ⟨threshold_isBigO_log_rpow ht hα0 hα',
    (threshold_sharpNearHalf_theta ht).2.trans (threshold_isBigO_mono hα)⟩

private lemma hasSparseSubsetsAtLogScale_mono {t : ℕ} {α β : ℝ} (h : α ≤ β)
    (hα : HasSparseSubsetsAtLogScale t α) : HasSparseSubsetsAtLogScale t β := by
  obtain ⟨c, hc, hev⟩ := hα
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev] with n hn col
  obtain ⟨X, hX, b, hb⟩ := hn col
  exact ⟨X, hX, b, hb.trans_le (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))⟩

private lemma threshold_positive_anchor_iff_sparse_below_sharpNearHalf {t : ℕ} (ht : 2 ≤ t) :
    (∀ a : ℝ, 0 < a → a < 1 / 2 →
      thresholdReal t a =Θ[atTop] thresholdReal t (1 / 4)) ↔
    (∀ a : ℝ, 0 < a → a < sharpNearHalf t → HasSparseSubsetsAtLogScale t a) := by
  rw [threshold_positive_anchor_iff_logScale ht]
  constructor
  · intro h a ha ha'
    exact (logScale_isBigO_iff_sparse ht ha).mp
      (h a ha (ha'.trans (sharpNearHalf_bounds ht).2))
  · intro h a ha ha'
    by_cases hsmall : a < sharpNearHalf t
    · exact (logScale_isBigO_iff_sparse ht ha).mpr (h a ha hsmall)
    · exact (threshold_theta_sharpNearHalf_interval ht (le_of_not_gt hsmall) ha').2

private lemma threshold_positive_anchor_iff_sparse_inv {t : ℕ} (ht : 2 ≤ t) :
    (∀ a : ℝ, 0 < a → a < 1 / 2 →
      thresholdReal t a =Θ[atTop] thresholdReal t (1 / 4)) ↔
    (∀ k : ℕ, HasSparseSubsetsAtLogScale t (1 / ((k : ℝ) + 3))) := by
  rw [threshold_positive_anchor_iff_sparse_below_sharpNearHalf ht]
  constructor
  · intro h k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 3) := by positivity
    by_cases hsmall : 1 / ((k : ℝ) + 3) < sharpNearHalf t
    · exact h _ hpos hsmall
    · exact (logScale_isBigO_iff_sparse ht hpos).mp
        (threshold_theta_sharpNearHalf_interval ht (le_of_not_gt hsmall) (by
          rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
          linarith [Nat.cast_nonneg (α := ℝ) k])).2
  · intro h a ha _
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / a)
    have hle : 1 / ((k : ℝ) + 3) ≤ a := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 1 < (k : ℝ) * a := (div_lt_iff₀ ha).mp hk
      linarith
    exact hasSparseSubsetsAtLogScale_mono hle (h k)

private lemma exists_pow_le_log_diagonalRamsey {t : ℕ} (ht : 2 ≤ t) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      c * (m : ℝ) ^ (t - 1) ≤ Real.log (diagonalRamsey t m : ℝ) := by
  obtain ⟨C, hC, hCb⟩ :=
    (threshold_isBigO_log_rpow ht le_rfl (by norm_num)).exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hCb.bound
  refine ⟨(C ^ (t - 1))⁻¹, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with m hm
  have hmN : N ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  let n := diagonalRamsey t m
  have hmn : m ≤ n := le_diagonalRamsey t m
  have hnN : N ≤ n := hmN.trans hmn
  have hn1 : 1 ≤ n := hm1.trans hmn
  have hnot_le : ¬ Hypergraph.balancedColoringThreshold n t 0 ≤ m := by
    intro hle
    exact (avoidMono_iff_lt_diagonalRamsey.mp (threshold_zero_le_iff.mp hle)).false
  have hlt : (m : ℝ) ≤ thresholdReal t 0 n := by
    exact_mod_cast (show m ≤ Hypergraph.balancedColoringThreshold n t 0 by omega)
  have hbound := hN n hnN
  change ‖thresholdReal t 0 n‖ ≤ C * ‖logScale t n‖ at hbound
  have hscale0 : 0 ≤ logScale t n :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg hscale0] at hbound
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m) (hlt.trans hbound) (t - 1)
  rw [mul_pow, logScale_pow ht hn1] at hpow
  rw [inv_mul_le_iff₀ (by positivity)]
  exact hpow

private lemma exists_sq_le_log_diagonalRamsey_three :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      c * (m : ℝ) ^ 2 ≤ Real.log (diagonalRamsey 3 m : ℝ) :=
  exists_pow_le_log_diagonalRamsey (by decide : 2 ≤ 3)


private def deltaWord {r : ℕ} (v : Fin (r + 1) → ℕ) (i : Fin r) : ℕ :=
  bitDiff (v i.castSucc) (v i.succ)

private noncomputable def wordColor {k : ℕ} (g : Finset ℕ → Bool)
    (d : Fin (k + 3) → ℕ) : Bool := by
  classical
  exact if StrictMono d ∨ StrictAnti d then g (univ.image d)
    else decide (d ⟨1, by omega⟩ < d ⟨0, by omega⟩)

private noncomputable def stepColorGeneral {n : ℕ} (k : ℕ) (g : Finset ℕ → Bool)
    (E : Finset (Fin (2 ^ n))) : Bool :=
  if h : E.card = (k + 3) + 1 then
    wordColor g (deltaWord (fun i ↦ (E.orderEmbOfFin h i).val))
  else false

private lemma stepColorGeneral_word {n k : ℕ} (g : Finset ℕ → Bool)
    {X : Finset (Fin (2 ^ n))} {v : Fin ((k + 3) + 1) → Fin (2 ^ n)}
    (hv : StrictMono v) (hvX : ∀ i, v i ∈ X) :
    ∃ E ∈ X.powersetCard ((k + 3) + 1),
      stepColorGeneral k g E = wordColor g (deltaWord (fun i ↦ (v i).val)) := by
  let f : Fin ((k + 3) + 1) ↪ Fin (2 ^ n) := ⟨v, hv.injective⟩
  let E := univ.map f
  have hE : E.card = (k + 3) + 1 := by simp [E]
  have hvE (i : Fin ((k + 3) + 1)) : v i ∈ E := mem_map_of_mem f (mem_univ i)
  refine ⟨E, mem_powersetCard.mpr ⟨?_, hE⟩, ?_⟩
  · intro j hj
    obtain ⟨i, _, rfl⟩ := mem_map.mp hj
    exact hvX i
  · unfold stepColorGeneral
    rw [dif_pos hE]
    rw [← orderEmbOfFin_unique hE hvE hv]

private lemma local_quad_of_word {k : ℕ} (g : Finset ℕ → Bool) (b : Bool)
    (d : Fin (k + 3) → ℕ) (h₁ : d ⟨0, by omega⟩ ≠ d ⟨1, by omega⟩)
    (h₂ : d ⟨1, by omega⟩ ≠ d ⟨2, by omega⟩)
    (hb : wordColor g d = b) :
    quadColor (fun _ ↦ b) (d ⟨0, by omega⟩) (d ⟨1, by omega⟩) (d ⟨2, by omega⟩) = b := by
  classical
  let i : Fin (k + 3) := ⟨0, by omega⟩
  let j : Fin (k + 3) := ⟨1, by omega⟩
  let l : Fin (k + 3) := ⟨2, by omega⟩
  have hij : i < j := by change (0 : ℕ) < 1; omega
  have hjl : j < l := by change (1 : ℕ) < 2; omega
  change d i ≠ d j at h₁
  change d j ≠ d l at h₂
  change quadColor (fun _ ↦ b) (d i) (d j) (d l) = b
  rcases lt_or_gt_of_ne h₁ with hinc | hdec <;> rcases lt_or_gt_of_ne h₂ with hincr | hdecr
  · simp [quadColor, hinc, hincr]
  · have hturn : ¬ (StrictMono d ∨ StrictAnti d) :=
      fun h ↦ h.elim (fun h ↦ hdecr.not_gt (h hjl)) (fun h ↦ hinc.not_gt (h hij))
    rw [quadColor_peak _ hinc hdecr]
    simpa [wordColor, hturn, ← show j = ⟨1, by omega⟩ from rfl,
      ← show i = ⟨0, by omega⟩ from rfl, hinc.not_gt] using hb
  · have hturn : ¬ (StrictMono d ∨ StrictAnti d) :=
      fun h ↦ h.elim (fun h ↦ hdec.not_gt (h hij)) (fun h ↦ hincr.not_gt (h hjl))
    rw [quadColor_valley _ hdec hincr]
    simpa [wordColor, hturn, ← show j = ⟨1, by omega⟩ from rfl,
      ← show i = ⟨0, by omega⟩ from rfl, hdec] using hb
  · simp [quadColor, hdec, hdecr]

private lemma step_general_mono_block {x : ℕ → ℕ} (hx : StrictMono x)
    {k m : ℕ} (hm : 3 ≤ m) (g : Finset ℕ → Bool) (b : Bool)
    (hword : ∀ v : Fin ((k + 3) + 1) → ℕ, StrictMono v →
      (∀ i, v i ≤ 2 * m + k) → wordColor g (deltaWord (x ∘ v)) = b) :
    ∃ l, l + m ≤ 2 * m ∧
      (StrictMonoOn (fun i ↦ bitDiff (x i) (x (i + 1))) (Set.Ico l (l + m)) ∨
       StrictAntiOn (fun i ↦ bitDiff (x i) (x (i + 1))) (Set.Ico l (l + m))) := by
  apply quad_mono_block hx (fun _ ↦ b) b hm
  intro i hi
  let v (j : Fin ((k + 3) + 1)) : ℕ := i + j.val
  have hv : StrictMono v := fun _ _ h ↦ Nat.add_lt_add_left h _
  have hb := hword v hv (fun j ↦ by have := j.isLt; dsimp [v]; omega)
  have hne (j : ℕ) : bitDiff (x (i + j)) (x (i + j + 1)) ≠
      bitDiff (x (i + j + 1)) (x (i + j + 1 + 1)) :=
    bitDiff_ne (hx (by omega)) (hx (by omega))
  have hh := local_quad_of_word g b (deltaWord (x ∘ v))
    (by simpa only [deltaWord, Function.comp_apply, v, Fin.val_castSucc, Fin.val_succ, Nat.add_zero] using hne 0)
    (by simpa only [deltaWord, Function.comp_apply, v, Fin.val_castSucc, Fin.val_succ, Nat.add_assoc] using hne 1) hb
  simpa only [deltaWord, Function.comp_apply, v, Fin.val_castSucc, Fin.val_succ, Nat.add_zero, Nat.add_assoc] using hh

private lemma realize_deltaWord_mono {x : ℕ → ℕ} (hx : StrictMono x)
    {r l m : ℕ} (hr : 0 < r) {u : Fin r → ℕ} (hu : StrictMono u)
    (hul : ∀ i, u i ∈ Set.Ico l (l + m))
    (hinc : StrictMonoOn (fun i ↦ bitDiff (x i) (x (i + 1))) (Set.Ico l (l + m))) :
    ∃ v : Fin (r + 1) → ℕ, StrictMono v ∧ (∀ i, v i ≤ l + m) ∧
      deltaWord (x ∘ v) = fun i ↦ bitDiff (x (u i)) (x (u i + 1)) := by
  let a : Fin r := ⟨0, hr⟩
  let v : Fin (r + 1) → ℕ := Fin.cases (u a) (fun j ↦ u j + 1)
  have hright (i : Fin r) : v i.succ = u i + 1 := Fin.cases_succ i
  have hleft (i : Fin r) (hi : 0 < i.val) :
      v i.castSucc = u ⟨i.val - 1, by omega⟩ + 1 := by
    let j : Fin r := ⟨i.val - 1, by omega⟩
    have he : j.succ = i.castSucc := Fin.ext (by simp [j]; omega)
    rw [← he, hright]
  have hinterval (i : Fin r) : l ≤ v i.castSucc ∧ v i.castSucc ≤ u i := by
    by_cases hi : i.val = 0
    · have he : i = a := Fin.ext hi
      subst i
      change l ≤ u a ∧ u a ≤ u a
      exact ⟨(hul a).1, le_rfl⟩
    · rw [hleft i (by omega)]
      exact ⟨by have := (hul ⟨i.val - 1, by omega⟩).1; omega,
        hu (show (⟨i.val - 1, by omega⟩ : Fin r) < i from by change i.val - 1 < i.val; omega)⟩
  refine ⟨v, Fin.strictMono_iff_lt_succ.mpr ?_, ?_, ?_⟩
  · intro i
    rw [hright]
    exact (hinterval i).2.trans_lt (Nat.lt_succ_self _)
  · refine Fin.cases ?_ ?_
    · exact (hul a).2.le
    · intro i
      exact (hul i).2
  · funext i
    change bitDiff (x (v i.castSucc)) (x (v i.succ)) = _
    rw [hright]
    exact bitDiff_of_mono_block hx (hinterval i).2
      (hinc.monotoneOn.mono (fun _ hw ↦
        ⟨(hinterval i).1.trans hw.1, hw.2.trans_lt (hul i).2⟩))

private lemma realize_deltaWord_anti {x : ℕ → ℕ} (hx : StrictMono x)
    {r l m : ℕ} (hr : 0 < r) {u : Fin r → ℕ} (hu : StrictMono u)
    (hul : ∀ i, u i ∈ Set.Ico l (l + m))
    (hdec : StrictAntiOn (fun i ↦ bitDiff (x i) (x (i + 1))) (Set.Ico l (l + m))) :
    ∃ v : Fin (r + 1) → ℕ, StrictMono v ∧ (∀ i, v i ≤ l + m) ∧
      deltaWord (x ∘ v) = fun i ↦ bitDiff (x (u i)) (x (u i + 1)) := by
  let a : Fin r := ⟨r - 1, by omega⟩
  let v : Fin (r + 1) → ℕ := Fin.lastCases (u a + 1) u
  have hleft (i : Fin r) : v i.castSucc = u i := Fin.lastCases_castSucc i
  have hright (i : Fin r) : u i < v i.succ ∧ v i.succ ≤ l + m := by
    by_cases hi : i.val + 1 < r
    · let j : Fin r := ⟨i.val + 1, hi⟩
      have he : i.succ = j.castSucc := Fin.ext rfl
      rw [he, hleft]
      exact ⟨hu (show i < j from Nat.lt_succ_self _), (hul j).2.le⟩
    · have he : i = a := Fin.ext (by have := i.isLt; dsimp [a]; omega)
      subst i
      have ha : a.succ = Fin.last r := Fin.ext (by simp [a]; omega)
      rw [ha, show v (Fin.last r) = u a + 1 from Fin.lastCases_last]
      exact ⟨Nat.lt_succ_self _, (hul a).2⟩
  refine ⟨v, Fin.strictMono_iff_lt_succ.mpr ?_, ?_, ?_⟩
  · intro i
    rw [hleft]
    exact (hright i).1
  · refine Fin.lastCases ?_ ?_
    · simpa only [v, Fin.lastCases_last] using (Nat.succ_le_of_lt (hul a).2)
    · intro i
      simpa only [v, Fin.lastCases_castSucc] using (hul i).2.le
  · funext i
    change bitDiff (x (v i.castSucc)) (x (v i.succ)) = _
    rw [hleft]
    have hR := hright i
    have h := bitDiff_of_anti_block hx (i := u i) (j := v i.succ - 1) (by omega)
      (hdec.antitoneOn.mono (fun _ hw ↦ ⟨(hul i).1.trans hw.1, by have := hw.2; omega⟩))
    rwa [show v i.succ - 1 + 1 = v i.succ by omega] at h

private lemma step_general_lift_mono {x : ℕ → ℕ} (hx : StrictMono x)
    {n k m : ℕ} (hm : 3 ≤ m) (g : Finset ℕ → Bool) (b : Bool)
    (hsize : x (2 * m) < 2 ^ n)
    (hword : ∀ v : Fin ((k + 3) + 1) → ℕ, StrictMono v →
      (∀ i, v i ≤ 2 * m + k) → wordColor g (deltaWord (x ∘ v)) = b) :
    ∃ S : Finset ℕ, S.card = m ∧ (∀ y ∈ S, y < n) ∧ MonoOn (k + 3) g S b := by
  classical
  let d (i : ℕ) := bitDiff (x i) (x (i + 1))
  obtain ⟨l, hl, hdir⟩ := step_general_mono_block hx hm g b hword
  have hmem (i : Fin m) : l + i.val ∈ Set.Ico l (l + m) :=
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt l⟩
  let f : Fin m ↪ ℕ := ⟨fun i ↦ d (l + i.val), by
    have hadd : StrictMono (fun i : Fin m ↦ l + i.val) := fun _ _ h ↦ Nat.add_lt_add_left h _
    rcases hdir with hinc | hdec
    · exact (show StrictMono (fun i : Fin m ↦ d (l + i.val)) from
        fun i j hij ↦ hinc (hmem i) (hmem j) (hadd hij)).injective
    · exact (show StrictAnti (fun i : Fin m ↦ d (l + i.val)) from
        fun i j hij ↦ hdec (hmem i) (hmem j) (hadd hij)).injective⟩
  refine ⟨univ.map f, by simp, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, _, rfl⟩ := mem_map.mp hy
    exact bitDiff_lt (hx (Nat.lt_succ_self _))
      ((hx.monotone ((hmem i).2.trans_le hl)).trans_lt hsize)
  · intro E hE
    obtain ⟨hES, hEc⟩ := mem_powersetCard.mp hE
    obtain ⟨U, _, rfl⟩ := subset_map_iff.mp hES
    rw [card_map] at hEc
    let e := U.orderEmbOfFin hEc
    let u (i : Fin (k + 3)) : ℕ := l + (e i).val
    have hu : StrictMono u := fun _ _ hij ↦ Nat.add_lt_add_left (e.strictMono hij) _
    have hul (i : Fin (k + 3)) : u i ∈ Set.Ico l (l + m) := hmem (e i)
    have hw : StrictMono (d ∘ u) ∨ StrictAnti (d ∘ u) :=
      hdir.imp (fun h i j hij ↦ h (hul i) (hul j) (hu hij))
        (fun h i j hij ↦ h (hul i) (hul j) (hu hij))
    obtain ⟨v, hv, hvl, hdelta⟩ :=
      hdir.elim (realize_deltaWord_mono hx (by omega) hu hul)
        (realize_deltaWord_anti hx (by omega) hu hul)
    have hcolor := hword v hv (fun i ↦ (hvl i).trans (hl.trans (Nat.le_add_right _ _)))
    change deltaWord (x ∘ v) = d ∘ u at hdelta
    rw [hdelta, wordColor, if_pos hw] at hcolor
    rw [← map_orderEmbOfFin_univ U hEc, Finset.map_map, Finset.map_eq_image]
    exact hcolor

private lemma avoidMono_step_general {n k m : ℕ} (hm : 3 ≤ m)
    (havoid : AvoidMono n (k + 3) m) :
    AvoidMono (2 ^ n) (k + 3 + 1) (2 * m + k + 1) := by
  classical
  obtain ⟨col, hcol⟩ := havoid
  let enc : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let g (S : Finset ℕ) : Bool := col (S.preimage enc enc.injective.injOn)
  refine ⟨stepColorGeneral k g, fun X hX b ↦ ?_⟩
  by_contra! hb
  have hmono (E : Finset (Fin (2 ^ n))) (hE : E ∈ X.powersetCard (k + 3 + 1)) :
      stepColorGeneral k g E = !b := by
    have h := hb E hE
    cases b <;> cases hp : stepColorGeneral k g E <;> simp [hp] at h ⊢
  let x (i : ℕ) : ℕ := if hi : i < X.card then (X.orderEmbOfFin rfl ⟨i, hi⟩).val else 2 ^ n + i
  have hx : StrictMono x := by
    intro i j hij
    dsimp [x]
    split <;> split
    · exact (X.orderEmbOfFin rfl).strictMono (show (⟨i, ‹_›⟩ : Fin X.card) <
        (⟨j, ‹_›⟩ : Fin X.card) from hij)
    · exact (Fin.isLt _).trans_le (Nat.le_add_right _ _)
    · omega
    · exact Nat.add_lt_add_left hij _
  have hword (v : Fin (k + 3 + 1) → ℕ) (hv : StrictMono v)
      (hmax : ∀ i, v i ≤ 2 * m + k) :
      wordColor g (deltaWord (x ∘ v)) = !b := by
    have hvX (i : Fin (k + 3 + 1)) : v i < X.card := by have := hmax i; omega
    let w (i : Fin (k + 3 + 1)) := X.orderEmbOfFin rfl ⟨v i, hvX i⟩
    have hw : StrictMono w := fun _ _ hij ↦ (X.orderEmbOfFin rfl).strictMono (hv hij)
    obtain ⟨E, hE, heq⟩ := stepColorGeneral_word g hw (fun i ↦ X.orderEmbOfFin_mem rfl _)
    have hcast : (fun i ↦ (w i).val) = x ∘ v := by
      funext i
      simp [w, x, hvX]
    rw [← hcast, ← heq]
    exact hmono E hE
  have hsize : x (2 * m) < 2 ^ n := by
    dsimp [x]
    rw [dif_pos (by omega)]
    exact Fin.isLt _
  obtain ⟨S, hS, hbnd, hSm⟩ := step_general_lift_mono hx hm g (!b) hsize hword
  obtain ⟨T, _, hT⟩ := (subset_map_iff (s := S) (f := enc) (t := univ)).1 (by
    intro y hy
    exact mem_map.mpr ⟨⟨y, hbnd y hy⟩, mem_univ _, rfl⟩)
  have hTc : T.card = m := by simpa [hT] using hS
  obtain ⟨e, he, heb⟩ := hcol T hTc b
  obtain ⟨hes, het⟩ := mem_powersetCard.mp he
  have hE : e.map enc ∈ S.powersetCard (k + 3) :=
    mem_powersetCard.mpr ⟨hT ▸ map_subset_map.mpr hes, (card_map _).trans het⟩
  have hcontra : col e = !b := by simpa only [g, preimage_map] using hSm _ hE
  rw [heb] at hcontra
  cases b <;> cases hcontra

private lemma diagonalRamsey_step_general {r m : ℕ} (hr : 3 ≤ r) (hm : 3 ≤ m) :
    2 ^ (diagonalRamsey r m - 1) < diagonalRamsey (r + 1) (2 * m + (r - 3) + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
  rw [Nat.add_sub_cancel]
  have h := le_diagonalRamsey (k + 3) m
  exact avoidMono_iff_lt_diagonalRamsey.mp (avoidMono_step_general hm
    (avoidMono_iff_lt_diagonalRamsey.mpr (by omega)))

private def binaryLogCeil (n : ℕ) : ℕ := n.log2 + 1

private lemma tendsto_binaryLogCeil : Tendsto binaryLogCeil atTop atTop := by
  refine tendsto_atTop.2 fun N ↦ ?_
  filter_upwards [eventually_ge_atTop (2 ^ N : ℕ)] with n hn
  have hp : 0 < (2 ^ N : ℕ) := by positivity
  exact ((Nat.le_log2 (hp.trans_le hn).ne').mpr hn).trans (Nat.le_succ _)

private lemma threshold_zero_le_step_binary (n k : ℕ) :
    Hypergraph.balancedColoringThreshold n (3 + (k + 1)) 0 ≤
      2 * Hypergraph.balancedColoringThreshold (binaryLogCeil n) (3 + k) 0 + (k + 7) := by
  let L := binaryLogCeil n
  let m := max 3 (Hypergraph.balancedColoringThreshold L (3 + k) 0)
  have havoid : AvoidMono L (3 + k) m := threshold_zero_le_iff.mp (le_max_right _ _)
  rw [Nat.add_comm 3 k] at havoid
  have hf := threshold_zero_le_iff.mpr (avoidMono_step_general (le_max_left _ _) havoid)
  have hn : n ≤ 2 ^ L := Nat.lt_log2_self.le
  have hbound := (threshold_zero_mono_vertices (t := k + 3 + 1) hn).trans hf
  rw [Nat.add_comm k 3, Nat.add_assoc] at hbound
  have hm : m ≤ 3 + Hypergraph.balancedColoringThreshold L (3 + k) 0 :=
    max_le (by omega) (by omega)
  dsimp [L] at hbound hm
  omega

private lemma threshold_zero_le_iterated_binary (k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ n,
      Hypergraph.balancedColoringThreshold n (3 + k) 0 ≤
        C * (Hypergraph.balancedColoringThreshold (binaryLogCeil^[k] n) 3 0 + 1) := by
  induction k with
  | zero =>
    exact ⟨1, Nat.one_pos, fun n ↦ by simp⟩
  | succ k ih =>
    obtain ⟨C, hC, ih⟩ := ih
    refine ⟨2 * C + (k + 7), by omega, fun n ↦ ?_⟩
    rw [Function.iterate_succ_apply]
    let q := Hypergraph.balancedColoringThreshold (binaryLogCeil^[k] (binaryLogCeil n)) 3 0 + 1
    have hq : 1 ≤ q := by dsimp [q]; omega
    calc
      Hypergraph.balancedColoringThreshold n (3 + (k + 1)) 0 ≤
          2 * Hypergraph.balancedColoringThreshold (binaryLogCeil n) (3 + k) 0 + (k + 7) :=
        threshold_zero_le_step_binary n k
      _ ≤ (2 * C) * q + (k + 7) := by
        rw [mul_assoc]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (ih _)) _
      _ ≤ (2 * C + (k + 7)) * q := by
        rw [Nat.add_mul]
        exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left (k + 7) hq) _

private lemma tendsto_iterated_binaryLogCeil (k : ℕ) :
    Tendsto (binaryLogCeil^[k]) atTop atTop := by
  induction k with
  | zero => exact tendsto_id
  | succ k ih =>
    simpa only [Function.iterate_succ] using ih.comp tendsto_binaryLogCeil

private lemma threshold_zero_isBigO_iterated_binary (k : ℕ) :
    thresholdReal (3 + k) 0 =O[atTop] (logScale 3 ∘ binaryLogCeil^[k]) := by
  obtain ⟨D, _, hD⟩ := threshold_zero_le_iterated_binary k
  have ht := tendsto_iterated_binaryLogCeil k
  have hlower := threshold_isBigO_log_rpow (t := 3) (α := 0) (by decide) le_rfl (by norm_num)
  obtain ⟨C, hC, hbound⟩ := (hlower.comp_tendsto ht).exists_pos
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ logScale 3 (binaryLogCeil^[k] n) := by
    have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log ((binaryLogCeil^[k] n : ℕ) : ℝ) :=
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp ht)).eventually
        (eventually_ge_atTop 1)
    filter_upwards [hlog] with n hn
    rw [logScale, ← Real.one_rpow (((3 - 1 : ℕ) : ℝ)⁻¹)]
    exact Real.rpow_le_rpow zero_le_one hn (by positivity)
  refine IsBigO.of_bound ((D : ℝ) * (C + 1)) ?_
  filter_upwards [hbound.bound, hlarge] with n hn hlarge'
  let z := logScale 3 (binaryLogCeil^[k] n)
  have hz : 1 ≤ z := hlarge'
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  change ‖thresholdReal 3 0 (binaryLogCeil^[k] n)‖ ≤ C * ‖z‖ at hn
  change ‖thresholdReal (3 + k) 0 n‖ ≤ _ * ‖z‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg hz0] at hn ⊢
  have hDn : thresholdReal (3 + k) 0 n ≤
      (D : ℝ) * (thresholdReal 3 0 (binaryLogCeil^[k] n) + 1) := by
    exact_mod_cast hD n
  calc
    _ ≤ _ := hDn
    _ ≤ (D : ℝ) * (C * z + z) :=
      mul_le_mul_of_nonneg_left (add_le_add hn hz) (Nat.cast_nonneg _)
    _ = _ := by ring



private lemma thin_constant_colors {V E : Type} [DecidableEq V] [DecidableEq E]
    (P : Finset E) (R : Finset V) (c : E → V → Bool) :
    ∃ S ⊆ R, R.card ≤ 2 ^ P.card * S.card ∧
      ∃ f : E → Bool, ∀ e ∈ P, ∀ v ∈ S, c e v = f e := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    exact ⟨R, Subset.rfl, by simp, fun _ ↦ false, by simp⟩
  | @insert a P ha ih =>
    obtain ⟨S, hSR, hS, f, hf⟩ := ih
    let A := S.filter (fun v ↦ c a v = true)
    let B := S.filter (fun v ↦ ¬ c a v = true)
    have hAB : A.card + B.card = S.card := card_filter_add_card_filter_not _
    obtain ⟨T, hTS, hT, b, hb⟩ :
        ∃ T ⊆ S, S.card ≤ 2 * T.card ∧ ∃ b, ∀ v ∈ T, c a v = b := by
      by_cases h : A.card ≤ B.card
      · refine ⟨B, filter_subset _ _, by omega, false, fun v hv ↦ ?_⟩
        have hne := (mem_filter.mp hv).2
        cases hz : c a v <;> simp_all
      · exact ⟨A, filter_subset _ _, by omega, true, fun v hv ↦ (mem_filter.mp hv).2⟩
    refine ⟨T, hTS.trans hSR, ?_, Function.update f a b, ?_⟩
    · rw [card_insert_of_notMem ha, pow_succ, mul_assoc]
      exact hS.trans (Nat.mul_le_mul_left _ hT)
    · intro e he v hv
      rcases mem_insert.mp he with rfl | he
      · simpa only [Function.update_self] using hb v hv
      · have hne : e ≠ a := fun h ↦ ha (h ▸ he)
        rw [Function.update_of_ne hne]
        exact hf e he v (hTS hv)

private def LastUniform {V : Type} [LinearOrder V] (r : ℕ) (col : Finset V → Bool)
    (P S : Finset V) (f : Finset V → Bool) : Prop :=
  ∀ E ∈ P.powersetCard (r + 1), ∀ v ∈ P ∪ S, (∀ x ∈ E, x < v) →
    col (insert v E) = f E

private lemma lastUniform_extend {V : Type} [LinearOrder V] {r : ℕ} {col : Finset V → Bool}
    {P R : Finset V} {f : Finset V → Bool}
    (hsep : ∀ x ∈ P, ∀ y ∈ R, x < y) (hR : R.Nonempty)
    (hf : LastUniform r col P R f) :
    ∃ v ∈ R, ∃ S ⊆ R.erase v, ∃ g : Finset V → Bool,
      (R.erase v).card ≤ 2 ^ (P.card.choose r) * S.card ∧
      (∀ x ∈ insert v P, ∀ y ∈ S, x < y) ∧
      LastUniform r col (insert v P) S g := by
  classical
  let v := R.min' hR
  have hv : v ∈ R := min'_mem _ _
  obtain ⟨S, hSR, hS, g, hg⟩ :=
    thin_constant_colors (P.powersetCard r) (R.erase v)
      (fun E y ↦ col (insert y (insert v E)))
  refine ⟨v, hv, S, hSR, fun E ↦ if v ∈ E then g (E.erase v) else f E,
    by simpa only [card_powersetCard] using hS, ?_, ?_⟩
  · intro x hx y hy
    have hyR := mem_erase.mp (hSR hy)
    rcases mem_insert.mp hx with rfl | hx
    · exact (R.min'_le y hyR.2).lt_of_ne hyR.1.symm
    · exact hsep x hx y hyR.2
  · intro E hE y hy hlt
    change col (insert y E) = (if v ∈ E then g (E.erase v) else f E)
    obtain ⟨hEP, hc⟩ := mem_powersetCard.mp hE
    by_cases hve : v ∈ E
    · rw [if_pos hve]
      have hE' : E.erase v ∈ P.powersetCard r := by
        refine mem_powersetCard.mpr ⟨fun x hx ↦ ?_, ?_⟩
        · exact (mem_insert.mp (hEP (mem_of_mem_erase hx))).resolve_left (ne_of_mem_erase hx)
        · rw [card_erase_of_mem hve, hc, Nat.add_sub_cancel]
      have hyS : y ∈ S := by
        rcases mem_union.mp hy with hyp | hys
        · rcases mem_insert.mp hyp with rfl | hyp
          · exact ((hlt v hve).false).elim
          · exact ((hlt v hve).not_gt (hsep y hyp v hv)).elim
        · exact hys
      simpa only [insert_erase hve] using hg _ hE' y hyS
    · rw [if_neg hve]
      have hsub : E ⊆ P := fun x hx ↦
        (mem_insert.mp (hEP hx)).resolve_left (fun h ↦ hve (h ▸ hx))
      apply hf E (mem_powersetCard.mpr ⟨hsub, hc⟩) y _ hlt
      rcases mem_union.mp hy with hyP | hyS
      · rcases mem_insert.mp hyP with rfl | hyP
        · exact mem_union_right _ hv
        · exact mem_union_left _ hyP
      · exact mem_union_right _ (mem_of_mem_erase (hSR hyS))

private lemma lastUniform_build {V : Type} [LinearOrder V] (r M : ℕ)
    (col : Finset V → Bool) (k : ℕ) {P R : Finset V} {f : Finset V → Bool}
    (hP : P.card + k ≤ M) (hsep : ∀ x ∈ P, ∀ y ∈ R, x < y)
    (hR : (k + 1) * (2 ^ (M ^ r)) ^ k ≤ R.card) (hf : LastUniform r col P R f) :
    ∃ Q ⊆ P ∪ R, Q.card = P.card + k ∧ ∃ S ⊆ R, S.Nonempty ∧
      (∀ x ∈ Q, ∀ y ∈ S, x < y) ∧ ∃ g, LastUniform r col Q S g := by
  classical
  induction k generalizing P R f with
  | zero =>
    have hRp : 0 < R.card := by simpa using hR
    exact ⟨P, subset_union_left, by simp, R, Subset.rfl, card_pos.mp hRp, hsep, f, hf⟩
  | succ k ih =>
    let D : ℕ := 2 ^ (M ^ r)
    have hDp : 0 < D := by dsimp [D]; positivity
    have hpow : 0 < D ^ (k + 1) := pow_pos hDp _
    have hRbound : 0 < (k + 1 + 1) * D ^ (k + 1) := by positivity
    have hRp : R.Nonempty := card_pos.mp (hRbound.trans_le hR)
    obtain ⟨v, hv, S, hSR, g, hS, hsep', hg⟩ := lastUniform_extend hsep hRp hf
    have hvP : v ∉ P := fun h ↦ (hsep v h v hv).false
    have hc : (insert v P).card = P.card + 1 := card_insert_of_notMem hvP
    have hfactor : 2 ^ (P.card.choose r) ≤ D := Nat.pow_le_pow_right (by decide) <|
      (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
    have hsmall : (k + 1) * D ^ k ≤ S.card := by
      apply Nat.le_of_mul_le_mul_left ?_ hDp
      calc
        D * ((k + 1) * D ^ k) = (k + 1) * D ^ (k + 1) := by rw [pow_succ]; ac_rfl
        _ ≤ (R.erase v).card := by
          rw [card_erase_of_mem hv]
          change (k + 1 + 1) * D ^ (k + 1) ≤ R.card at hR
          rw [Nat.add_mul, one_mul] at hR
          omega
        _ ≤ 2 ^ (P.card.choose r) * S.card := hS
        _ ≤ D * S.card := Nat.mul_le_mul_right _ hfactor
    obtain ⟨Q, hQ, hQc, T, hTS, hTne, hQT, w, hw⟩ :=
      ih (P := insert v P) (R := S) (f := g) (by rw [hc]; omega) hsep' hsmall hg
    have hSR' : S ⊆ R := hSR.trans (erase_subset _ _)
    refine ⟨Q, hQ.trans (union_subset ?_ (hSR'.trans subset_union_right)), by omega,
      T, hTS.trans hSR', hTne, hQT, w, hw⟩
    exact insert_subset (mem_union_right _ hv) subset_union_left

private lemma exists_mono_at_diagonalRamsey {V : Type} [DecidableEq V] {P : Finset V}
    {t m : ℕ} (hP : P.card = diagonalRamsey t m) (col : Finset V → Bool) :
    ∃ S ⊆ P, S.card = m ∧ ∃ b, MonoOn t col S b := by
  classical
  by_contra! hno
  have hn : ¬ AvoidMono (diagonalRamsey t m) t m :=
    fun h ↦ (avoidMono_iff_lt_diagonalRamsey.mp h).false
  apply hn
  let a := (P.equivFinOfCardEq hP).symm
  let f : Fin (diagonalRamsey t m) ↪ V := a.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨fun e ↦ col (e.map f), fun X hX b ↦ ?_⟩
  have hf (i : Fin (diagonalRamsey t m)) : f i ∈ P := (a i).property
  have hsub : X.map f ⊆ P := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    exact hf i
  have hc : (X.map f).card = m := by simpa using hX
  have hnot := hno (X.map f) hsub hc (!b)
  unfold MonoOn at hnot
  push Not at hnot
  obtain ⟨E, hE, hcol⟩ := hnot
  obtain ⟨hEX, hEc⟩ := mem_powersetCard.mp hE
  obtain ⟨e, heX, rfl⟩ := subset_map_iff.mp hEX
  refine ⟨e, mem_powersetCard.mpr ⟨heX, by simpa using hEc⟩, ?_⟩
  cases b <;> cases hz : col (e.map f) <;> simp_all

private lemma diagonalRamsey_upper_step (r m : ℕ) :
    let M := diagonalRamsey (r + 1) m
    diagonalRamsey (r + 2) (m + 1) ≤ (M + 1) * (2 ^ (M ^ r)) ^ M := by
  classical
  dsimp only
  let M := diagonalRamsey (r + 1) m
  let N := (M + 1) * (2 ^ (M ^ r)) ^ M
  change diagonalRamsey (r + 2) (m + 1) ≤ N
  by_contra! hN
  obtain ⟨col, hcol⟩ := avoidMono_iff_lt_diagonalRamsey.mpr hN
  obtain ⟨Q, _, hQc, T, _, hTne, hQT, g, hg⟩ :=
    lastUniform_build r M col M (P := ∅) (R := (univ : Finset (Fin N)))
      (f := fun _ ↦ false) (by simp) (by simp) (by simp [N])
      (by simp [LastUniform, powersetCard_eq_empty.mpr (show (∅ : Finset (Fin N)).card < r + 1 by simp)])
  have hQ : Q.card = M := by simpa using hQc
  obtain ⟨U, hUQ, hU, b, hb⟩ := exists_mono_at_diagonalRamsey hQ g
  obtain ⟨z, hz⟩ := hTne
  have hzU : z ∉ U := fun h ↦ (hQT z (hUQ h) z hz).false
  have hcard : (insert z U).card = m + 1 := by rw [card_insert_of_notMem hzU, hU]
  have hmono : MonoOn (r + 2) col (insert z U) b := by
    intro E hE
    obtain ⟨hE, hEc⟩ := mem_powersetCard.mp hE
    have hEne : E.Nonempty := card_pos.mp (by omega)
    let w := E.max' hEne
    have hw : w ∈ E := max'_mem _ _
    have hlt (x : Fin N) (hx : x ∈ E.erase w) : x < w :=
      (E.le_max' x (mem_of_mem_erase hx)).lt_of_ne (ne_of_mem_erase hx)
    have hsub : E.erase w ⊆ U := by
      intro x hx
      rcases mem_insert.mp (hE (mem_of_mem_erase hx)) with hxz | hx
      · rw [hxz] at hx
        rcases mem_insert.mp (hE hw) with hwz | hwU
        · exact ((hlt z hx).ne hwz.symm).elim
        · exact ((hlt z hx).not_gt (hQT w (hUQ hwU) z hz)).elim
      · exact hx
    have hec : (E.erase w).card = r + 1 := by rw [card_erase_of_mem hw, hEc]; omega
    have hw' : w ∈ Q ∪ T := by
      rcases mem_insert.mp (hE hw) with rfl | hw'
      · exact mem_union_right _ hz
      · exact mem_union_left _ (hUQ hw')
    have heQ := mem_powersetCard.mpr ⟨hsub.trans hUQ, hec⟩
    rw [← insert_erase hw, hg _ heQ w hw' hlt]
    exact hb (E.erase w) (mem_powersetCard.mpr ⟨hsub, hec⟩)
  obtain ⟨E, hE, hEb⟩ := hcol _ hcard (!b)
  rw [hmono E hE] at hEb
  cases b <;> cases hEb

private lemma diagonalRamsey_two_upper (m : ℕ) : diagonalRamsey 2 m ≤ 2 ^ (m + m) := by
  by_contra! h
  obtain ⟨col, hcol⟩ := avoidMono_iff_lt_diagonalRamsey.mpr h
  suffices ∃ S : Finset (Fin (2 ^ (m + m))), S.card = m ∧ ∃ b, GraphMono col S b by
    obtain ⟨S, hS, b, hb⟩ := this
    obtain ⟨E, hE, hEb⟩ := hcol S hS (!b)
    rw [hb E hE] at hEb
    cases b <;> cases hEb
  rcases graph_ramsey col m m univ (by simp) with ⟨S, _, hS, hb⟩ | ⟨S, _, hS, hb⟩
  · exact ⟨S, hS, false, hb⟩
  · exact ⟨S, hS, true, hb⟩

private lemma diagonalRamsey_mono_clique (t : ℕ) : Monotone (diagonalRamsey t) := by
  intro m m' hmm
  by_contra! h
  have havoid := avoidMono_iff_lt_diagonalRamsey.mpr h
  have hle := threshold_zero_le_iff.mpr havoid
  exact (avoidMono_iff_lt_diagonalRamsey.mp (threshold_zero_le_iff.mp (hle.trans hmm))).false

private lemma diagonalRamsey_upper_step_pow (r m : ℕ) :
    diagonalRamsey (r + 2) (m + 1) ≤ 2 ^ (2 * (diagonalRamsey (r + 1) m) ^ (r + 1)) := by
  let M := diagonalRamsey (r + 1) m
  have hM : M ≤ M ^ (r + 1) := by
    by_cases h : M = 0
    · simp [h]
    · simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < M by omega)
        (show 1 ≤ r + 1 by omega)
  calc
    diagonalRamsey (r + 2) (m + 1) ≤ (M + 1) * (2 ^ (M ^ r)) ^ M :=
      diagonalRamsey_upper_step r m
    _ ≤ (2 ^ M) * (2 ^ (M ^ r)) ^ M :=
      Nat.mul_le_mul_right _ (show M + 1 ≤ 2 ^ M from Nat.lt_two_pow_self)
    _ = 2 ^ (M + M ^ (r + 1)) := by rw [← pow_mul, ← pow_add, pow_succ]
    _ ≤ 2 ^ (2 * M ^ (r + 1)) := Nat.pow_le_pow_right (by decide) (by omega)

private lemma diagonalRamsey_three_upper (m : ℕ) :
    diagonalRamsey 3 m ≤ 2 ^ (2 ^ (4 * m + 1)) := by
  have h := diagonalRamsey_upper_step_pow 1 m
  change diagonalRamsey 3 (m + 1) ≤ 2 ^ (2 * diagonalRamsey 2 m ^ 2) at h
  apply ((diagonalRamsey_mono_clique 3) (Nat.le_succ m)).trans (h.trans ?_)
  apply Nat.pow_le_pow_right (by decide)
  calc
    2 * diagonalRamsey 2 m ^ 2 ≤ 2 * (2 ^ (m + m)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (diagonalRamsey_two_upper m) _)
    _ = 2 ^ (4 * m + 1) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      omega

private lemma log_log_isBigO_threshold_three_zero :
    (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) =O[atTop] thresholdReal 3 0 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C := 5 * Real.log 2 + |Real.log (Real.log 2)|
  refine IsBigO.of_bound C ?_
  have hT := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (Real.log (n : ℝ)) :=
    hT.eventually (eventually_ge_atTop 0)
  filter_upwards [eventually_ge_atTop 2, hev] with n hn hnlog
  let m := Hypergraph.balancedColoringThreshold n 3 0
  have hm : 1 ≤ m := by
    by_contra! h
    have hzero : m = 0 := by omega
    obtain ⟨col, hc⟩ := (show Feasible n 3 0 m from threshold_feasible n 3 0)
    have hbad := (hc ∅ (by simp [hzero]) false).1
    simp [powersetCard_eq_empty.mpr (show (∅ : Finset (Fin n)).card < 3 by simp)] at hbad
  have havoid : AvoidMono n 3 m := threshold_zero_le_iff.mp le_rfl
  have hnr := (avoidMono_iff_lt_diagonalRamsey.mp havoid).le.trans (diagonalRamsey_three_upper m)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h1 : Real.log (n : ℝ) ≤ (2 : ℝ) ^ (4 * m + 1) * Real.log 2 := by
    have hh := Real.log_le_log (show 0 < (n : ℝ) by positivity)
      (show (n : ℝ) ≤ (2 : ℝ) ^ (2 ^ (4 * m + 1) : ℕ) by exact_mod_cast hnr)
    rwa [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat] at hh
  have h2 := Real.log_le_log hlogn h1
  rw [Real.log_mul (by positivity) hlog2.ne', Real.log_pow] at h2
  change ‖Real.log (Real.log (n : ℝ))‖ ≤ C * ‖(m : ℝ)‖
  rw [Real.norm_of_nonneg hnlog, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  push_cast at h2
  dsimp [C]
  nlinarith only [h2, le_abs_self (Real.log (Real.log 2)),
    mul_nonneg hlog2.le (sub_nonneg.mpr hm'),
    mul_nonneg (abs_nonneg (Real.log (Real.log 2))) (sub_nonneg.mpr hm')]

private lemma threshold_zero_four_isLittleO_three :
    thresholdReal 4 0 =o[atTop] thresholdReal 3 0 := by
  have hT := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  let y (n : ℕ) := Real.log (Real.log (n : ℝ))
  let s : ℝ := (2 : ℝ)⁻¹
  have ht : Tendsto (fun n ↦ y n ^ s) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < s)).comp hT
  have hsqrt : (fun n : ℕ ↦ y n ^ s) =o[atTop] y := by
    refine IsLittleO.of_bound fun c hc ↦ ?_
    filter_upwards [hT.eventually (eventually_ge_atTop 0),
      ht.eventually (eventually_ge_atTop c⁻¹)] with n hn hc'
    have hn' : 0 ≤ y n := hn
    have hp : 0 ≤ y n ^ s := Real.rpow_nonneg hn' _
    rw [Real.norm_of_nonneg hp, Real.norm_of_nonneg hn']
    have hmul : 1 ≤ c * y n ^ s := by
      have h := (div_le_iff₀ hc).mp (show 1 / c ≤ y n ^ s by simpa only [one_div] using hc')
      rwa [mul_comm] at h
    have hsq : (y n ^ s) ^ (2 : ℕ) = y n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn']
      norm_num [s]
    calc
      y n ^ s ≤ (c * y n ^ s) * y n ^ s := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hmul hp
      _ = c * y n := by rw [mul_assoc, ← pow_two, hsq]
  have h := (threshold_zero_isBigO_log_log_high (by decide : 4 ≤ 4)).trans_isLittleO hsqrt
  exact h.trans_isBigO log_log_isBigO_threshold_three_zero

private lemma threshold_three_theta_zero_iff_ramsey_upper_quadratic {a : ℝ}
    (ha : 0 < a) (ha' : a < 1 / 2) :
    (thresholdReal 3 a =Θ[atTop] thresholdReal 3 0) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
        Real.log (diagonalRamsey 3 m : ℝ) ≤ C * (m : ℝ) ^ 2 := by
  have habig : (thresholdReal 3 a =O[atTop] thresholdReal 3 0) ↔
      (thresholdReal 3 (1 / 4) =O[atTop] thresholdReal 3 0) :=
    let h := threshold_three_positive_theta ha ha'
    ⟨h.2.trans, h.1.trans⟩
  have hatheta : (thresholdReal 3 a =Θ[atTop] thresholdReal 3 0) ↔
      (thresholdReal 3 a =O[atTop] thresholdReal 3 0) :=
    ⟨fun h ↦ h.1, fun h ↦ ⟨h, threshold_isBigO_mono ha.le⟩⟩
  rw [hatheta, habig, ← not_iff_not, threshold_three_jump_iff]
  simp only [eventually_atTop, Nat.reduceSub]
  push Not
  rfl

private lemma threshold_classes_three_iff_diagonalRamsey :
    (∀ a b : ℝ, a ∈ Set.Ico (0 : ℝ) (1 / 2) → b ∈ Set.Ico (0 : ℝ) (1 / 2) →
      ((thresholdReal 3 a =Θ[atTop] thresholdReal 3 b) ↔ (a = 0 ↔ b = 0))) ↔
    (∀ C : ℝ, 0 < C → ∀ N : ℕ, ∃ m ≥ N,
      C * (m : ℝ) ^ (3 - 1 : ℕ) < Real.log (diagonalRamsey 3 m : ℝ)) := by
  rw [threshold_classes_iff, threshold_three_jump_iff]
  exact and_iff_right (fun _ ↦ threshold_three_positive_theta)

private lemma threshold_classes_high_iff_sparse {t : ℕ} (ht : 4 ≤ t) :
    (∀ a b : ℝ, a ∈ Set.Ico (0 : ℝ) (1 / 2) → b ∈ Set.Ico (0 : ℝ) (1 / 2) →
      ((thresholdReal t a =Θ[atTop] thresholdReal t b) ↔ (a = 0 ↔ b = 0))) ↔
    (∀ a : ℝ, 0 < a → a < sharpNearHalf t → HasSparseSubsetsAtLogScale t a) := by
  rw [threshold_classes_iff,
    threshold_positive_anchor_iff_sparse_below_sharpNearHalf (by omega : 2 ≤ t)]
  exact and_iff_left (threshold_jump_high ht (by norm_num))

private lemma sum_erase_edge_counts {V : Type} [DecidableEq V] (X : Finset V) (t : ℕ)
    (p : Finset V → Prop) [DecidablePred p] :
    ∑ v ∈ X, (((X.erase v).powersetCard t).filter p).card =
      (X.card - t) * ((X.powersetCard t).filter p).card := by
  classical
  let A := (X.powersetCard t).filter p
  have hrow (v : V) :
      ((X.erase v).powersetCard t).filter p = A.filter (fun E ↦ v ∉ E) := by
    ext E
    simp only [A, mem_filter, mem_powersetCard]
    exact ⟨fun ⟨⟨he, hc⟩, hp⟩ ↦
        ⟨⟨⟨he.trans (erase_subset _ _), hc⟩, hp⟩, fun hv ↦ notMem_erase _ _ (he hv)⟩,
      fun ⟨⟨⟨he, hc⟩, hp⟩, hv⟩ ↦
        ⟨⟨fun x hx ↦ mem_erase.mpr ⟨fun h ↦ hv (h ▸ hx), he hx⟩, hc⟩, hp⟩⟩
  have hcol (E : Finset V) (hE : E ∈ A) :
      ∑ v ∈ X, (if v ∉ E then 1 else 0 : ℕ) = X.card - t := by
    obtain ⟨hsub, hc⟩ := mem_powersetCard.mp (mem_filter.mp hE).1
    rw [sum_boole, Nat.cast_id]
    have hfilter : X.filter (fun v ↦ v ∉ E) = X \ E := by
      ext v
      simp
    rw [hfilter, card_sdiff_of_subset hsub, hc]
  calc
    _ = ∑ v ∈ X, ∑ E ∈ A, (if v ∉ E then 1 else 0 : ℕ) := by
      apply sum_congr rfl
      intro v _
      rw [hrow, sum_boole, Nat.cast_id]
    _ = ∑ E ∈ A, ∑ v ∈ X, (if v ∉ E then 1 else 0 : ℕ) := sum_comm
    _ = ∑ _E ∈ A, (X.card - t) := sum_congr rfl hcol
    _ = _ := by simp [A, mul_comm]

private lemma exists_erase_sparse {V : Type} [DecidableEq V] {X : Finset V} {t : ℕ}
    (p : Finset V → Prop) [DecidablePred p] {a : ℝ} (ht : t < X.card)
    (h : (((X.powersetCard t).filter p).card : ℝ) < a * (X.card.choose t : ℝ)) :
    ∃ v ∈ X, ((((X.erase v).powersetCard t).filter p).card : ℝ) <
      a * ((X.erase v).card.choose t : ℝ) := by
  classical
  by_contra! hall
  have hcount : ∑ v ∈ X, ((((X.erase v).powersetCard t).filter p).card : ℝ) =
      ((X.card - t : ℕ) : ℝ) * (((X.powersetCard t).filter p).card : ℝ) := by
    exact_mod_cast sum_erase_edge_counts X t p
  have htotal : ∑ v ∈ X, ((X.erase v).card.choose t : ℝ) =
      ((X.card - t : ℕ) : ℝ) * (X.card.choose t : ℝ) := by
    exact_mod_cast (show ∑ v ∈ X, (X.erase v).card.choose t =
        (X.card - t) * X.card.choose t from by
      simpa only [filter_true, card_powersetCard] using sum_erase_edge_counts X t (fun _ ↦ True))
  have hsum := sum_le_sum hall
  rw [← mul_sum, hcount, htotal, mul_left_comm] at hsum
  exact h.not_ge (le_of_mul_le_mul_left hsum (by exact_mod_cast Nat.sub_pos_of_lt ht))

private lemma exists_sparse_of_card {V : Type} [DecidableEq V] {X : Finset V} {t m : ℕ}
    (p : Finset V → Prop) [DecidablePred p] {a : ℝ} (ht : t ≤ m) (hm : m ≤ X.card)
    (h : (((X.powersetCard t).filter p).card : ℝ) < a * (X.card.choose t : ℝ)) :
    ∃ Y ⊆ X, Y.card = m ∧
      (((Y.powersetCard t).filter p).card : ℝ) < a * (Y.card.choose t : ℝ) := by
  induction hcard : X.card using Nat.strong_induction_on generalizing X with
  | h k ih =>
    by_cases hk : X.card = m
    · exact ⟨X, Subset.rfl, hk, h⟩
    obtain ⟨v, hv, hthin⟩ := exists_erase_sparse p (ht.trans_lt (lt_of_le_of_ne hm (Ne.symm hk))) h
    have hcard' : (X.erase v).card = X.card - 1 := card_erase_of_mem hv
    have hle : m ≤ (X.erase v).card := by omega
    obtain ⟨Y, hYX, hY, hbad⟩ := ih (X.erase v).card (by omega) hle hthin rfl
    exact ⟨Y, hYX.trans (erase_subset _ _), hY, hbad⟩

private lemma hasSparseSubsetsAtLogScale_iff_exact {t : ℕ} (ht : 2 ≤ t) (a : ℝ) :
    HasSparseSubsetsAtLogScale t a ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
        ∀ col : Finset (Fin n) → Bool, ∃ X : Finset (Fin n),
          X.card = ⌊c * logScale t n⌋₊ ∧ ∃ b : Bool,
            (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) <
              a * (X.card.choose t : ℝ) := by
  classical
  have hT : Tendsto (logScale t) atTop atTop := by
    exact (tendsto_rpow_atTop (by
      apply inv_pos.mpr
      exact_mod_cast (show 0 < t - 1 by omega))).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  constructor
  · rintro ⟨c, hc, hmain⟩
    refine ⟨c, hc, ?_⟩
    have hT' : Tendsto (fun n ↦ c * logScale t n) atTop atTop := hT.const_mul_atTop hc
    filter_upwards [hmain, hT'.eventually (eventually_ge_atTop (t : ℝ))] with n hn htn
    intro col
    obtain ⟨X, hX, b, hb⟩ := hn col
    have ht' : t ≤ ⌊c * logScale t n⌋₊ := Nat.le_floor htn
    obtain ⟨Y, _, hY, hbad⟩ := exists_sparse_of_card (fun E ↦ col E = b) ht'
      (Nat.floor_le_of_le hX) hb
    exact ⟨Y, hY, b, hbad⟩
  · rintro ⟨c, hc, hmain⟩
    refine ⟨c / 2, by positivity, ?_⟩
    have hT' : Tendsto (fun n ↦ c * logScale t n) atTop atTop := hT.const_mul_atTop hc
    filter_upwards [hmain, hT'.eventually (eventually_ge_atTop (2 : ℝ))] with n hn hlarge
    intro col
    obtain ⟨Y, hY, b, hb⟩ := hn col
    have hfloor := Nat.lt_floor_add_one (c * logScale t n)
    refine ⟨Y, ?_, b, hb⟩
    rw [hY, div_mul_eq_mul_div]
    linarith



open scoped Classical in
private def HasSparseAtSize (n t m : ℕ) (a : ℝ) : Prop :=
  ∀ col : Finset (Fin n) → Bool, ∃ X : Finset (Fin n), X.card = m ∧ ∃ b : Bool,
    (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) <
      a * (X.card.choose t : ℝ)

private lemma hasSparseAtSize_mono_vertices {n N t m : ℕ} {a : ℝ}
    (h : n ≤ N) (hn : HasSparseAtSize n t m a) : HasSparseAtSize N t m a := by
  classical
  intro col
  let f := Fin.castLEEmb h
  obtain ⟨X, hc, b, hb⟩ := hn (fun E ↦ col (E.map f))
  refine ⟨X.map f, (card_map _).trans hc, b, ?_⟩
  rw [powersetCard_map, filter_map, card_map, card_map]
  exact hb

private lemma log_binary_exponential (K m d : ℕ) :
    Real.log ((2 ^ (K * m ^ d) : ℕ) : ℝ) =
      ((K : ℝ) * Real.log 2) * (m : ℝ) ^ d := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul, Nat.cast_pow]
  ring

private lemma hasSparseSubsetsAtLogScale_iff_binary_exponential {t : ℕ} (ht : 2 ≤ t) (a : ℝ) :
    HasSparseSubsetsAtLogScale t a ↔
      ∃ K : ℕ, 0 < K ∧ ∀ᶠ m : ℕ in atTop, HasSparseAtSize (2 ^ (K * m ^ (t - 1))) t m a := by
  classical
  let d := t - 1
  have hd : 0 < d := by dsimp [d]; omega
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  constructor
  · rintro ⟨c, hc, hlarge⟩
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / (c ^ d * Real.log 2))
    have hK' : 1 < (K : ℝ) * (c ^ d * Real.log 2) :=
      (div_lt_iff₀ (by positivity)).mp hK
    have hKpos : 0 < K := by
      by_contra! h
      rw [show K = 0 by omega] at hK'
      norm_num at hK'
    obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
    refine ⟨K, hKpos, ?_⟩
    filter_upwards [eventually_ge_atTop (max t (max N 1))] with m hm
    let n := 2 ^ (K * m ^ d)
    have hm1 : 1 ≤ m := by omega
    have hmn : m ≤ n := by
      have hp : m ≤ m ^ d := by
        simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < m by omega) hd
      exact hp.trans ((Nat.le_mul_of_pos_left _ hKpos).trans Nat.lt_two_pow_self.le)
    have hn1 : 1 ≤ n := hm1.trans hmn
    have hsize : (m : ℝ) ≤ c * logScale t n := by
      apply le_of_pow_le_pow_left₀ hd.ne'
        (mul_nonneg hc.le (Real.rpow_nonneg
          (Real.log_nonneg (by exact_mod_cast hn1)) _))
      rw [mul_pow, show d = t - 1 by rfl, logScale_pow ht hn1, log_binary_exponential]
      change (m : ℝ) ^ d ≤ c ^ d * (((K : ℝ) * Real.log 2) * (m : ℝ) ^ d)
      calc
        _ = 1 * (m : ℝ) ^ d := (one_mul _).symm
        _ ≤ ((K : ℝ) * (c ^ d * Real.log 2)) * (m : ℝ) ^ d :=
          mul_le_mul_of_nonneg_right hK'.le (by positivity)
        _ = _ := by ring
    intro col
    obtain ⟨X, hX, b, hb⟩ := hN n ((by omega : N ≤ m).trans hmn) col
    obtain ⟨Y, _, hY, hbad⟩ := exists_sparse_of_card (fun e ↦ col e = b)
      (by omega : t ≤ m) (by exact_mod_cast hsize.trans hX) hb
    exact ⟨Y, hY, b, hbad⟩
  · rintro ⟨K, hK, hlarge⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
    let B : ℝ := (K : ℝ) * Real.log 2
    let c := (1 + B)⁻¹
    have hB : 0 < B := mul_pos (Nat.cast_pos.mpr hK) hlog2
    have hc : 0 < c := by dsimp [c]; positivity
    have hc1 : c ≤ 1 := by
      dsimp [c]
      rw [inv_le_one₀ (by positivity)]
      linarith
    have hcoef : B * c ^ d ≤ 1 := by
      have hp : c ^ d ≤ c := by
        simpa only [pow_one] using pow_le_pow_of_le_one hc.le hc1 hd
      calc
        B * c ^ d ≤ B * c := mul_le_mul_of_nonneg_left hp hB.le
        _ ≤ 1 := by
          dsimp [c]
          rw [mul_inv_le_iff₀ (by positivity)]
          linarith
    apply (hasSparseSubsetsAtLogScale_iff_exact ht a).mpr
    refine ⟨c, hc, ?_⟩
    have hT : Tendsto (fun n ↦ c * logScale t n) atTop atTop :=
      Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop (by
        apply inv_pos.mpr
        exact_mod_cast hd)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    filter_upwards [eventually_ge_atTop 1, hT.eventually (eventually_ge_atTop (N : ℝ))]
      with n hn hNn
    let m := ⌊c * logScale t n⌋₊
    have hmN : N ≤ m := Nat.le_floor hNn
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hmc : (m : ℝ) ≤ c * logScale t n :=
      Nat.floor_le (mul_nonneg hc.le (Real.rpow_nonneg hlogn _))
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m) hmc d
    rw [mul_pow, show d = t - 1 by rfl, logScale_pow ht hn] at hpow
    have hlog_le : Real.log ((2 ^ (K * m ^ d) : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
      rw [log_binary_exponential]
      calc
        _ ≤ B * (c ^ d * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hpow hB.le
        _ = (B * c ^ d) * Real.log (n : ℝ) := (mul_assoc _ _ _).symm
        _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hlogn
    have hle : 2 ^ (K * m ^ d) ≤ n := by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      exact_mod_cast (Real.log_le_log_iff
        (by positivity : 0 < ((2 ^ (K * m ^ d) : ℕ) : ℝ)) hnpos).mp hlog_le
    exact hasSparseAtSize_mono_vertices hle (hN m hmN)

private lemma threshold_classes_high_iff_binary_exponential {t : ℕ} (ht : 4 ≤ t) :
    (∀ a b : ℝ, a ∈ Set.Ico (0 : ℝ) (1 / 2) → b ∈ Set.Ico (0 : ℝ) (1 / 2) →
      ((thresholdReal t a =Θ[atTop] thresholdReal t b) ↔ (a = 0 ↔ b = 0))) ↔
    (∀ k : ℕ, ∃ K : ℕ, 0 < K ∧ ∀ᶠ m : ℕ in atTop,
      HasSparseAtSize (2 ^ (K * m ^ (t - 1))) t m (1 / ((k : ℝ) + 3))) := by
  rw [threshold_classes_iff, threshold_positive_anchor_iff_sparse_inv (by omega : 2 ≤ t),
    and_iff_left (threshold_jump_high ht (by norm_num))]
  exact forall_congr' (fun k ↦ hasSparseSubsetsAtLogScale_iff_binary_exponential
    (by omega : 2 ≤ t) (1 / ((k : ℝ) + 3)))

private lemma threshold_three_full_square_iff_quadratic :
    (∀ a b : ℝ, a ∈ Set.Ico (0 : ℝ) (1 / 2) → b ∈ Set.Ico (0 : ℝ) (1 / 2) →
      thresholdReal 3 a =Θ[atTop] thresholdReal 3 b) ↔
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      Real.log (diagonalRamsey 3 m : ℝ) ≤ C * (m : ℝ) ^ 2) := by
  constructor
  · intro h
    exact (threshold_three_theta_zero_iff_ramsey_upper_quadratic (by norm_num)
      (by norm_num : (1 / 4 : ℝ) < 1 / 2)).mp
      (h (1 / 4) 0 (by norm_num [Set.mem_Ico]) (by norm_num [Set.mem_Ico]))
  · intro h a b ha hb
    have anchor (q : ℝ) (hq : q ∈ Set.Ico (0 : ℝ) (1 / 2)) :
        thresholdReal 3 q =Θ[atTop] thresholdReal 3 0 := by
      rcases hq.1.eq_or_lt with hq0 | hq0
      · subst q
        exact isTheta_refl _ _
      · exact (threshold_three_theta_zero_iff_ramsey_upper_quadratic hq0 hq.2).mpr h
    exact (anchor a ha).trans (anchor b hb).symm


end OMA.BalancedColoring

def OMA.answer (t : ℕ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ico 0 (1 / 2) ∧ p.2 ∈ Set.Ico 0 (1 / 2) ∧
    (t ≤ 2 ∨ (p.1 = 0 ↔ p.2 = 0))}

open Asymptotics in
theorem OMA.solution : Erdos161.erdos_161.parts.i.answer = OMA.answer → type_of% @Erdos161.erdos_161.parts.i := by
  intro h
  rw [h]
  intro t ht
  by_cases h1 : t = 1
  · subst t
    ext p
    simp [OMA.answer, OMA.BalancedColoring.threshold_one_theta]
  · by_cases h2 : t = 2
    · subst t
      ext p
      simp only [OMA.answer, Set.mem_ofPred_eq, le_refl, true_or, and_true]
      exact ⟨fun hp ↦ ⟨hp.1, hp.2.1⟩,
        fun hp ↦ ⟨hp.1, hp.2, OMA.BalancedColoring.threshold_two_theta hp.1 hp.2⟩⟩
    · have ht3 : 3 ≤ t := by omega
      have hremaining :
          (4 ≤ t → ∀ a : ℝ, 0 < a → a < OMA.BalancedColoring.sharpNearHalf t →
            OMA.BalancedColoring.HasSparseSubsetsAtLogScale t a) ∧
          (t = 3 → ∀ C : ℝ, 0 < C → ∀ N : ℕ, ∃ m ≥ N,
            C * (m : ℝ) ^ (3 - 1 : ℕ) <
              Real.log (OMA.BalancedColoring.diagonalRamsey 3 m : ℝ)) := by
        sorry
      have hh (a b : ℝ) (ha : a ∈ Set.Ico 0 (1 / 2)) (hb : b ∈ Set.Ico 0 (1 / 2)) :
          ((OMA.BalancedColoring.thresholdReal t a =Θ[Filter.atTop]
            OMA.BalancedColoring.thresholdReal t b) ↔ (a = 0 ↔ b = 0)) := by
        by_cases ht4 : 4 ≤ t
        · exact (OMA.BalancedColoring.threshold_classes_high_iff_sparse ht4).mpr (hremaining.1 ht4) a b ha hb
        · have heq : t = 3 := by omega
          have hR := hremaining.2 heq
          subst t
          exact OMA.BalancedColoring.threshold_classes_three_iff_diagonalRamsey.mpr hR a b ha hb
      ext p
      simp only [OMA.answer, Set.mem_ofPred_eq, show ¬ t ≤ 2 by omega, false_or]
      exact ⟨fun hp ↦ ⟨hp.1, hp.2.1, (hh p.1 p.2 hp.1 hp.2.1).mp hp.2.2⟩,
        fun hp ↦ ⟨hp.1, hp.2.1, (hh p.1 p.2 hp.1 hp.2.1).mpr hp.2.2⟩⟩

