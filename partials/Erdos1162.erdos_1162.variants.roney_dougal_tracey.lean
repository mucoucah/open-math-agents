import FormalConjectures.ErdosProblems.«1162»

-- Problem: Erdős Problem 1162 — roney dougal tracey
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1162.lean:80 (declaration Erdos1162.erdos_1162.variants.roney_dougal_tracey)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Plan. Lower bound (proved here): the kernels of the maps
`v ↦ v_B - M v_A` on `𝔽₂^(A ⊕ B)` are `2^(|A| |B|)` distinct subgroups of an elementary abelian
2-group acting on `(A ⊕ B) × 𝔽₂` by translation, which embeds in `S_n`.
Upper bound: Roney-Dougal and Tracey 2025 (the only open part, `rotr_upper`).
-/

open Filter Asymptotics Equiv

namespace OMA.E1162RT

/-- The additive map `v ↦ (j ↦ v (inr j) - ∑ i, M j i * v (inl i))`. -/
def defect (a b : ℕ) (M : Fin b → Fin a → ZMod 2) :
    (Fin a ⊕ Fin b → ZMod 2) →+ (Fin b → ZMod 2) where
  toFun v j := v (Sum.inr j) - ∑ i, M j i * v (Sum.inl i)
  map_zero' := by funext j; simp
  map_add' v w := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring

lemma defect_ker_injective (a b : ℕ) :
    Function.Injective (fun M => (defect a b M).ker) := by
  intro M N h
  funext j i
  let v : Fin a ⊕ Fin b → ZMod 2 := Sum.elim (fun i' => if i' = i then 1 else 0) (fun j' => M j' i)
  have hv : v ∈ (defect a b M).ker := by
    rw [AddMonoidHom.mem_ker]
    funext j'
    simp [defect, v]
  have hv' : v ∈ (defect a b N).ker := by
    have := h
    simp only at this
    rw [← this]; exact hv
  rw [AddMonoidHom.mem_ker] at hv'
  have := congrFun hv' j
  simp [defect, v] at this
  exact (sub_eq_zero.mp this)

/-- Translation action of `𝔽₂^ι` on `ι × 𝔽₂`. -/
def transl (ι : Type*) : Multiplicative (ι → ZMod 2) →* Perm (ι × ZMod 2) where
  toFun c := Equiv.prodCongrRight (fun i => Equiv.addLeft (Multiplicative.toAdd c i))
  map_one' := by ext p <;> simp
  map_mul' c d := by ext p <;> simp [Perm.mul_apply]

lemma transl_injective (ι : Type*) : Function.Injective (transl ι) := by
  intro c d h
  apply Multiplicative.toAdd.injective
  funext i
  have := congrArg (fun g : Perm (ι × ZMod 2) => (g (i, 0)).2) h
  simpa [transl] using this

lemma lower (n : ℕ) : 2 ^ ((n / 4) * (n / 2 - n / 4)) ≤ Erdos1162.f n := by
  set a := n / 4
  set b := n / 2 - n / 4
  have hcard : Fintype.card ((Fin a ⊕ Fin b) × ZMod 2) ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, ZMod.card]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let F : (Fin b → Fin a → ZMod 2) → Subgroup (Perm (Fin n)) := fun M =>
    ((AddSubgroup.toSubgroup (defect a b M).ker).map (transl _)).map (Perm.viaEmbeddingHom e)
  have hF : Function.Injective F := by
    intro M N h
    apply defect_ker_injective
    apply AddSubgroup.toSubgroup.injective
    apply Subgroup.map_injective (transl_injective _)
    exact Subgroup.map_injective (Perm.viaEmbeddingHom_injective e) h
  have : Finite (Subgroup (Perm (Fin n))) :=
    Finite.of_injective (fun H : Subgroup (Perm (Fin n)) => (H : Set (Perm (Fin n))))
      SetLike.coe_injective
  have hle := Nat.card_le_card_of_injective F hF
  have hc : Nat.card (Fin b → Fin a → ZMod 2) = 2 ^ (a * b) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]
  unfold Erdos1162.f
  rw [← hc]; exact hle

lemma sq_bound (n : ℕ) : n ^ 2 ≤ 16 * ((n / 4) * (n / 2 - n / 4)) + 8 * n := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have h4 : (4 * q + r) / 4 = q := by omega
  interval_cases r <;> simp only [h4] <;>
    · have h2 : ∀ s, s < 4 → (4 * q + s) / 2 - q ≥ q := fun s hs => by omega
      nlinarith [h2 0 (by norm_num), h2 1 (by norm_num), h2 2 (by norm_num), h2 3 (by norm_num)]

/-- Roney-Dougal and Tracey 2025, the upper bound (the only open part). -/
lemma rotr_upper (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
    Real.logb 2 (Erdos1162.f n : ℝ) ≤ (1 / 16 + ε) * (n : ℝ) ^ 2 := by
  sorry

end OMA.E1162RT

theorem OMA.solution : type_of% @Erdos1162.erdos_1162.variants.roney_dougal_tracey := by
  rw [IsEquivalent, isLittleO_iff]
  intro c hc
  filter_upwards [OMA.E1162RT.rotr_upper (c / 16) (by positivity),
    eventually_ge_atTop ⌈8 / c⌉₊] with n hup hnc
  have hf0 : (0 : ℝ) < Erdos1162.f n := by exact_mod_cast Erdos1162.f_pos n
  set m := (n / 4) * (n / 2 - n / 4)
  have hlow : (m : ℝ) ≤ Real.logb 2 (Erdos1162.f n : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hf0, Real.rpow_natCast]
    exact_mod_cast OMA.E1162RT.lower n
  have hsq : (n : ℝ) ^ 2 ≤ 16 * (m : ℝ) + 8 * n := by exact_mod_cast OMA.E1162RT.sq_bound n
  have hn8 : 8 / c ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnc)
  have h8 : 8 * (n : ℝ) ≤ c * (n : ℝ) ^ 2 := by
    have : 8 ≤ c * n := by rw [div_le_iff₀ hc] at hn8; linarith
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  simp only [Pi.sub_apply]
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 16), Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith
