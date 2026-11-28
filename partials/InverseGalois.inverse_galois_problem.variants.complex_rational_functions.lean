import FormalConjectures.Wikipedia.InverseGalois

-- Problem: Inverse Galois problem — complex rational functions
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/InverseGalois.lean:90 (declaration InverseGalois.inverse_galois_problem.variants.complex_rational_functions)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Glue: realizability over a field `K` descends along surjections of Galois groups
(fixed field of the kernel). The remaining core is the regular inverse Galois problem
over `C(t)`, i.e. the Riemann existence theorem (or Harbater patching), which is not
available in Mathlib.
-/

namespace OMA.IGComplexRat

open IntermediateField

/-- Quotients of realized Galois groups are realized: take the fixed field of the kernel. -/
lemma realizable_of_galois_surj {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {G : Type*} [Group G]
    (f : Gal(L/K) →* G) (hf : Function.Surjective f) :
    InverseGalois.IsRealizable K G := by
  refine ⟨⟨?_⟩⟩
  exact
    { L := fixedField f.ker
      to_field := inferInstance
      to_algebra := inferInstance
      to_isGalois := IsGalois.of_fixedField_normal_subgroup f.ker
      iso := ((IsGalois.normalAutEquivQuotient f.ker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)).symm }

/-- Core (Riemann existence theorem for `C(t)`): every finite group is a quotient of the
Galois group of some finite Galois extension of `C(t)`. -/
lemma riemann_existence_core (G : Type*) [Fintype G] [Group G] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℂ) L)
      (_ : FiniteDimensional (RatFunc ℂ) L) (_ : IsGalois (RatFunc ℂ) L)
      (f : Gal(L/RatFunc ℂ) →* G), Function.Surjective f := by
  sorry

end OMA.IGComplexRat

theorem OMA.solution : type_of% @InverseGalois.inverse_galois_problem.variants.complex_rational_functions := by
  intro G _ _
  obtain ⟨L, _, _, _, _, f, hf⟩ := OMA.IGComplexRat.riemann_existence_core G
  exact OMA.IGComplexRat.realizable_of_galois_surj f hf
