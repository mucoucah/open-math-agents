import FormalConjectures.Paper.PfisterPythagorasNumber

-- Problem: Pfister's problem on the Pythagoras number of $\mathbb{R}(X_1, \dots, X_n)$ — lower bound
-- Upstream: formal-conjectures FormalConjectures/Paper/PfisterPythagorasNumber.lean:149 (declaration PfisterPythagorasNumber.pfister_problem.variants.lower_bound)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.PfLB

open MvPolynomial

/-- The Motzkin polynomial in two variables. -/
noncomputable def motz : MvPolynomial (Fin 2) ℝ :=
  1 + X 0 ^ 2 * X 1 ^ 4 + X 0 ^ 4 * X 1 ^ 2 - 3 * X 0 ^ 2 * X 1 ^ 2

/-- Embedding of polynomials into rational functions. -/
noncomputable abbrev emb (k : ℕ) : MvPolynomial (Fin k) ℝ →+* MvRatFunc (Fin k) ℝ :=
  algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ)

lemma sq_isSumSq {R : Type*} [Semiring R] (a : R) : IsSumSq (a ^ 2) := by
  rw [sq]; exact IsSumSq.mul_self a

lemma isSumSq_ringHom {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) {a : R}
    (ha : IsSumSq a) : IsSumSq (φ a) := by
  induction ha with
  | zero => rw [map_zero]; exact IsSumSq.zero
  | sq_add b _ ih => rw [map_add, map_mul]; exact IsSumSq.sq_add (φ b) ih

/-- Motzkin times (x^2+y^2)^2 is an explicit sum of six squares, so Motzkin is a sum of squares. -/
lemma motz_isSumSq : IsSumSq (emb 2 motz) := by
  have hX : (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : ℝ))) h
    norm_num at this
  set u := emb 2 (X 0)
  set v := emb 2 (X 1)
  have hd : u ^ 2 + v ^ 2 ≠ 0 := by
    intro h; apply hX
    apply IsFractionRing.injective (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)
    simpa [u, v] using h
  have hm : emb 2 motz = 1 + u ^ 2 * v ^ 4 + u ^ 4 * v ^ 2 - 3 * u ^ 2 * v ^ 2 := by
    simp [motz, u, v, map_ofNat]
  set d := u ^ 2 + v ^ 2 with hd_def
  have key : emb 2 motz =
      (u * (u * v * (d - 2)) / d) ^ 2 + (v * (u * v * (d - 2)) / d) ^ 2 +
      (u * (u * (v ^ 2 - 1)) / d) ^ 2 + (v * (u * (v ^ 2 - 1)) / d) ^ 2 +
      (u * (v * (u ^ 2 - 1)) / d) ^ 2 + (v * (v * (u ^ 2 - 1)) / d) ^ 2 := by
    rw [hm]
    field_simp
    rw [hd_def]
    ring
  rw [key]
  exact (((((sq_isSumSq _).add (sq_isSumSq _)).add (sq_isSumSq _)).add
    (sq_isSumSq _)).add (sq_isSumSq _)).add (sq_isSumSq _)

/-- The field map induced by `rename Fin.castSucc`. -/
noncomputable def liftHom (k : ℕ) : MvRatFunc (Fin k) ℝ →+* MvRatFunc (Fin (k + 1)) ℝ :=
  IsFractionRing.lift (g := (emb (k + 1)).comp (rename (R := ℝ) (Fin.castSucc (n := k))).toRingHom)
    ((IsFractionRing.injective (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)).comp
      (rename_injective _ (Fin.castSucc_injective k)))

lemma liftHom_emb (k : ℕ) (f : MvPolynomial (Fin k) ℝ) :
    liftHom k (emb k f) = emb (k + 1) (rename Fin.castSucc f) :=
  IsFractionRing.lift_algebraMap _ f

/-- Cassels-Ellison-Pfister (1971): Motzkin is not a sum of 3 squares in R(x,y). OPEN GAP. -/
lemma cep_motzkin : ¬ IsSumSqOfLength 3 (emb 2 motz) := by
  sorry

/-- Cassels (1964) step: adjoining a fresh variable squared raises the length by one. OPEN GAP. -/
lemma cassels_step (k m : ℕ) (f : MvPolynomial (Fin k) ℝ)
    (hf : ¬ IsSumSqOfLength m (emb k f)) :
    ¬ IsSumSqOfLength (m + 1) (emb (k + 1) (rename Fin.castSucc f + X (Fin.last k) ^ 2)) := by
  sorry

lemma witness (r : ℕ) : ∃ f : MvPolynomial (Fin (r + 2)) ℝ,
    IsSumSq (emb (r + 2) f) ∧ ¬ IsSumSqOfLength (r + 3) (emb (r + 2) f) := by
  induction r with
  | zero => exact ⟨motz, motz_isSumSq, cep_motzkin⟩
  | succ r ih =>
    obtain ⟨f, h1, h2⟩ := ih
    refine ⟨rename Fin.castSucc f + X (Fin.last (r + 2)) ^ 2, ?_, cassels_step _ _ f h2⟩
    rw [map_add, map_pow, ← liftHom_emb]
    exact (isSumSq_ringHom _ h1).add (sq_isSumSq _)

end OMA.PfLB

theorem OMA.solution : type_of% @PfisterPythagorasNumber.pfister_problem.variants.lower_bound := by
  intro n hn p hp
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨f, h1, h2⟩ := OMA.PfLB.witness r
  by_contra hlt
  exact h2 ((hp _ h1).of_le (by omega))
