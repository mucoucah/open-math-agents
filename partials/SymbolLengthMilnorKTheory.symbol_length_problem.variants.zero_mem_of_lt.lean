import FormalConjectures.Other.SymbolLengthMilnorKTheory

-- Problem: The symbol length of $K^M_n(\mathbb{C}(x_1, \dots, x_m))/p$ — zero mem of lt
-- Upstream: formal-conjectures FormalConjectures/Other/SymbolLengthMilnorKTheory.lean:217 (declaration SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open MilnorK

namespace OMA.ZML

/-- If degree `n` vanishes then so does degree `n + 1`. -/
theorem grade_succ_eq_bot {F : Type*} [Field F] (p n : ℕ) (h : MilnorK.grade F p n = ⊥) :
    MilnorK.grade F p (n + 1) = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  have hr : symbol p (fun i : Fin n => a i.succ) = 0 := by
    have := symbol_mem_grade F p (fun i : Fin n => a i.succ)
    rw [h, AddSubgroup.mem_bot] at this
    exact this
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ, hr, mul_zero]

theorem grade_eq_bot_of_le {F : Type*} [Field F] (p k : ℕ) (h : MilnorK.grade F p k = ⊥) :
    ∀ n, k ≤ n → MilnorK.grade F p n = ⊥ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact grade_succ_eq_bot p n ih

/-- Every element of `C(x_1, ..., x_0)` is a constant. -/
theorem fin0_const (x : MvRatFunc (Fin 0) ℂ) :
    ∃ z : ℂ, algebraMap ℂ (MvRatFunc (Fin 0) ℂ) z = x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin 0) ℂ) x
  have ha : a = MvPolynomial.C (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0) a) := by
    apply (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).injective
    rw [show MvPolynomial.C (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0) a) = algebraMap ℂ (MvPolynomial (Fin 0) ℂ) (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0) a) from rfl, AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hb : b = MvPolynomial.C (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0) b) := by
    apply (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).injective
    rw [show MvPolynomial.C (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0) b) = algebraMap ℂ (MvPolynomial (Fin 0) ℂ) (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0) b) from rfl, AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0) a / MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0) b, ?_⟩
  rw [map_div₀]
  conv_rhs => rw [ha, hb]
  simp [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin 0) ℂ) (MvRatFunc (Fin 0) ℂ),
    MvPolynomial.algebraMap_eq]

theorem m_zero (p : ℕ) (hp : 0 < p) : MilnorK.grade (MvRatFunc (Fin 0) ℂ) p 1 = ⊥ := by
  refine grade_eq_bot_of_forall_exists_pow_eq _ p (fun a => ?_) one_ne_zero
  obtain ⟨z, hz⟩ := fin0_const (a : MvRatFunc (Fin 0) ℂ)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z hp
  have hw0 : algebraMap ℂ (MvRatFunc (Fin 0) ℂ) w ≠ 0 := by
    intro h0
    apply a.ne_zero
    rw [← hz, ← hw, map_pow, h0, zero_pow hp.ne']
  exact ⟨Units.mk0 _ hw0, Units.ext (by simp [← hz, ← hw])⟩

/-- The remaining hard core: `K^M_{m+1}(C(x_1, ..., x_m))/p = 0` for `m ≥ 1`
(Tsen for m = 1; for m ≥ 2 and odd p this needs Bass-Tate norms or cd = m plus
the norm residue isomorphism). -/
theorem core (m p : ℕ) (hm : 1 ≤ m) (hp : p.Prime) :
    MilnorK.grade (MvRatFunc (Fin m) ℂ) p (m + 1) = ⊥ := by
  sorry

end OMA.ZML

theorem OMA.solution : type_of% @SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt := by
  intro m n p hmn hp
  rw [MilnorK.zero_mem_symbolLengthBounds_iff]
  refine OMA.ZML.grade_eq_bot_of_le p (m + 1) ?_ n hmn
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact OMA.ZML.m_zero p hp.pos
  · exact OMA.ZML.core m p hm hp
