import FormalConjectures.ErdosProblems.«707»

-- Problem: Erdős Problem 707: Embedding Sidon Sets in Perfect Difference Sets — small sidon sets
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/707.lean:221 (declaration Erdos707.erdos_707.variants.small_sidon_sets)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Singer construction adapted from the local proof of the sibling variant. -/

namespace OMA707Singer

lemma cube_sub_one (q : ℕ) (hq : 1 ≤ q) : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hq
  apply Nat.sub_eq_of_eq_add
  simp only [Nat.add_sub_cancel_left]
  ring

/-- An element fixed by the `q`-th power map lies in the subfield with `q` elements. -/
lemma mem_range_of_pow_card_eq {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F]
    (x : K) (hx : x ^ Nat.card F = x) : ∃ a : F, algebraMap F K a = x := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at hx
  have hP0 : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hdeg : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).natDegree
      = Fintype.card F := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  have hroot : ∀ y : K, y ^ Fintype.card F = y →
      y ∈ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hy, sub_self]
  have hsub : (Finset.univ.image (algebraMap F K)) ⊆
      (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset := by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
    apply hroot
    rw [← map_pow, FiniteField.pow_card]
  have hcard : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset.card
      ≤ (Finset.univ.image (algebraMap F K)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap F K).injective, Finset.card_univ]
    calc (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset.card
        ≤ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.card :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).natDegree :=
          Polynomial.card_roots' _
      _ = Fintype.card F := hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hxmem := hroot x hx
  rw [← heq] at hxmem
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hxmem
  exact ⟨a, ha⟩

/-- A generator of the multiplicative group of a finite field, as an element of the field. -/
lemma exists_gen (K : Type*) [Field K] [Finite K] :
    ∃ γ : K, γ ≠ 0 ∧ (∀ x : K, x ≠ 0 → ∃ i : ℕ, γ ^ i = x) ∧
      (∀ m : ℕ, γ ^ m = 1 → (Nat.card K - 1) ∣ m) ∧ γ ^ (Nat.card K - 1) = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  have hord : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_powers hg, Nat.card_units]
  refine ⟨(g : K), g.ne_zero, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (hg (Units.mk0 x hx))
    exact ⟨i, by rw [← Units.val_pow_eq_pow_val, hi, Units.val_mk0]⟩
  · intro m hm
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hm, Units.val_one]
  · rw [← hord, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]

lemma exists_plane {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) : ∃ W : Submodule F K, Module.finrank F W = 2 := by
  have hli : LinearIndependent F
      (fun i : Fin 2 => (Module.finBasisOfFinrankEq F K h3) (Fin.castSucc i)) :=
    (Module.finBasisOfFinrankEq F K h3).linearIndependent.comp _ (Fin.castSucc_injective 2)
  exact ⟨Submodule.span F
    (Set.range (fun i : Fin 2 => (Module.finBasisOfFinrankEq F K h3) (Fin.castSucc i))), by
      rw [finrank_span_eq_card hli, Fintype.card_fin]⟩

/-- A plane is not stable under multiplication by an element outside the base field. -/
lemma not_stable {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) (W : Submodule F K) (hW : Module.finrank F W = 2)
    (c : K) (hc : c ∉ (algebraMap F K).range) : ¬ ∀ w ∈ W, c * w ∈ W := by
  intro hst
  have hpos : 0 < Module.finrank F W := by omega
  obtain ⟨⟨w, hwW⟩, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hw : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hint : IsIntegral F c := IsIntegral.of_finite F c
  have hdeg : (minpoly F c).natDegree = 3 := by
    have hdvd := minpoly.degree_dvd hint
    rw [h3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
    · exact absurd (minpoly.natDegree_eq_one_iff.1 h1) hc
    · exact h3'
  have hli := linearIndependent_pow (K := F) c
  rw [hdeg] at hli
  have hli2 : LinearIndependent F (fun i : Fin 3 => c ^ (i : ℕ) * w) := by
    have hker : LinearMap.ker (LinearMap.mulRight F w) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      exact mul_right_cancel₀ hw hxy
    exact hli.map' (LinearMap.mulRight F w) hker
  have hmem : ∀ i : ℕ, c ^ i * w ∈ W := by
    intro i
    induction i with
    | zero => simpa using hwW
    | succ k ih =>
      rw [pow_succ', mul_assoc]
      exact hst _ ih
  have hspan : Submodule.span F (Set.range (fun i : Fin 3 => c ^ (i : ℕ) * w)) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hle := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli2, Fintype.card_fin, hW] at hle
  omega

/-- Two planes in a three-dimensional space meet: some nonzero `y ∈ W` has `c * y ∈ W`. -/
lemma key_exists {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) (W : Submodule F K) (hW : Module.finrank F W = 2)
    (c : K) (hc0 : c ≠ 0) : ∃ y ∈ W, y ≠ 0 ∧ c * y ∈ W := by
  have hinj : Function.Injective (LinearMap.mulLeft F c) := by
    intro x y hxy
    exact mul_left_cancel₀ hc0 hxy
  have h1 : Module.finrank F
      (W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
        K →ₗ[F] K)) = 2 := by
    rw [LinearEquiv.finrank_map_eq, hW]
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq W
    (W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
      K →ₗ[F] K))
  have h4 : Module.finrank F
      ↥(W ⊔ W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
        K →ₗ[F] K)) ≤ 3 := by
    rw [← h3]
    exact Submodule.finrank_le _
  have hpos : 0 < Module.finrank F
      ↥(W ⊓ W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
        K →ₗ[F] K)) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hx' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  rw [Submodule.mem_inf, Submodule.mem_map] at hx
  obtain ⟨hxW, y, hyW, hyx⟩ := hx
  have hcy : c * y = x := by
    rw [← hyx]
    rfl
  refine ⟨y, hyW, ?_, ?_⟩
  · rintro rfl
    exact hx' (by rw [← hcy, mul_zero])
  · rw [hcy]
    exact hxW

/-- For `c` outside the base field, the solutions `y ∈ W` of `c * y ∈ W` form a line. -/
lemma key_unique {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) (W : Submodule F K) (hW : Module.finrank F W = 2)
    (c : K) (hc : c ∉ (algebraMap F K).range) {y y' : K} (hy : y ∈ W) (hy0 : y ≠ 0)
    (hcy : c * y ∈ W) (hy' : y' ∈ W) (hcy' : c * y' ∈ W) : ∃ a : F, y' = a • y := by
  have hne : W ⊓ W.comap (LinearMap.mulLeft F c) ≠ W := by
    intro h
    apply not_stable h3 W hW c hc
    intro w hw
    rw [← h] at hw
    exact (Submodule.mem_inf.1 hw).2
  have hlt : W ⊓ W.comap (LinearMap.mulLeft F c) < W := lt_of_le_of_ne inf_le_left hne
  have hfr := Submodule.finrank_lt_finrank_of_lt hlt
  have hle1 : Module.finrank F ↥(W ⊓ W.comap (LinearMap.mulLeft F c)) ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hle1
  have hyU : y ∈ W ⊓ W.comap (LinearMap.mulLeft F c) := Submodule.mem_inf.2 ⟨hy, hcy⟩
  have hyU' : y' ∈ W ⊓ W.comap (LinearMap.mulLeft F c) := Submodule.mem_inf.2 ⟨hy', hcy'⟩
  obtain ⟨t, ht⟩ := hv ⟨y, hyU⟩
  obtain ⟨t', ht'⟩ := hv ⟨y', hyU'⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact hy0 (congrArg Subtype.val ht).symm
  have e1 : t • (v : K) = y := congrArg Subtype.val ht
  have e2 : t' • (v : K) = y' := congrArg Subtype.val ht'
  refine ⟨t' * t⁻¹, ?_⟩
  rw [← e1, ← e2, smul_smul, inv_mul_cancel_right₀ ht0]

/-- The Singer construction with a specified generator and plane. -/
theorem core_with_plane {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    (γ : K) (hγ0 : γ ≠ 0) (hγsurj : ∀ x : K, x ≠ 0 → ∃ i : ℕ, γ ^ i = x)
    (hγord : ∀ m : ℕ, γ ^ m = 1 → (Nat.card K - 1) ∣ m)
    (hγpow : γ ^ (Nat.card K - 1) = 1)
    (W : Submodule F K) (hW : Module.finrank F W = 2) :
    ∃ B : Set ℕ, IsPerfectDifferenceSet B (Nat.card F ^ 2 + Nat.card F + 1) ∧
      B.ncard = Nat.card F + 1 ∧
      ∀ a : ℕ, a % (Nat.card F ^ 2 + Nat.card F + 1) ∈ B ↔ γ ^ a ∈ W := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨q, hqdef⟩ : ∃ q, q = Nat.card F := ⟨_, rfl⟩
  rw [← hqdef]
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    exact Finite.one_lt_card
  obtain ⟨n, hn⟩ : ∃ n, n = q ^ 2 + q + 1 := ⟨_, rfl⟩
  rw [← hn]
  have hnpos : 0 < n := by omega
  have : NeZero n := ⟨hnpos.ne'⟩
  have hcardK : Nat.card K = q ^ 3 := by
    rw [hqdef, ← h3]
    exact Module.natCard_eq_pow_finrank
  have hN : Nat.card K - 1 = (q - 1) * n := by
    rw [hcardK, hn]
    exact cube_sub_one q (by omega)
  rw [hN] at hγord hγpow
  -- powers of `γ` in the base field
  have hA1 : ∀ (i : ℕ) (a : F), algebraMap F K a = γ ^ i → n ∣ i := by
    intro i a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact pow_ne_zero i hγ0 ha.symm
    have h1 : a ^ (q - 1) = 1 := by
      rw [hqdef, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one a ha0
    have h2 : γ ^ (i * (q - 1)) = 1 := by
      rw [pow_mul, ← ha, ← map_pow, h1, map_one]
    have h3' := hγord _ h2
    rw [mul_comm i] at h3'
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) h3'
  have hA2 : ∀ i : ℕ, n ∣ i → ∃ a : F, algebraMap F K a = γ ^ i := by
    rintro i ⟨m, rfl⟩
    apply mem_range_of_pow_card_eq
    have h1 : (γ ^ (n * m)) ^ (q - 1) = 1 := by
      rw [← pow_mul, show n * m * (q - 1) = (q - 1) * n * m by ring, pow_mul, hγpow, one_pow]
    rw [← hqdef]
    calc (γ ^ (n * m)) ^ q = (γ ^ (n * m)) ^ (q - 1 + 1) := by
          rw [Nat.sub_add_cancel (by omega)]
      _ = γ ^ (n * m) := by rw [pow_succ, h1, one_mul]
  -- the exponent `M'` acts as `-1`
  obtain ⟨M', hM'⟩ : ∃ M', (q - 1) * n = M' + 1 :=
    ⟨(q - 1) * n - 1, by
      have : 0 < (q - 1) * n := Nat.mul_pos (by omega) hnpos
      omega⟩
  have hM'cast : (M' : ZMod n) = -1 := by
    have h : ((M' + 1 : ℕ) : ZMod n) = 0 := by
      rw [← hM', Nat.cast_mul, ZMod.natCast_self, mul_zero]
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have hrel1 : ∀ i j : ℕ, γ ^ (j + M' * i) * γ ^ i = γ ^ j := by
    intro i j
    rw [← pow_add, show j + M' * i + i = j + (M' + 1) * i by ring, ← hM', pow_add, pow_mul,
      hγpow, one_pow, mul_one]
  have hrel2 : ∀ i j : ℕ, ((j + M' * i : ℕ) : ZMod n) = (j : ZMod n) - (i : ZMod n) := by
    intro i j
    push_cast
    rw [hM'cast]
    ring
  -- proportional powers have congruent exponents, and conversely
  have hP : ∀ (i j : ℕ) (a : F), γ ^ j = algebraMap F K a * γ ^ i →
      (j : ZMod n) = (i : ZMod n) := by
    intro i j a h
    have h1 : algebraMap F K a = γ ^ (j + M' * i) := by
      have h' := hrel1 i j
      rw [h] at h'
      exact (mul_right_cancel₀ (pow_ne_zero i hγ0) h').symm
    have h2 := hA1 _ a h1
    have h3' : ((j + M' * i : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
    rw [hrel2] at h3'
    exact sub_eq_zero.1 h3'
  have hQ : ∀ i j : ℕ, (j : ZMod n) = (i : ZMod n) →
      ∃ a : F, γ ^ j = algebraMap F K a * γ ^ i := by
    intro i j h
    have h1 : ((j + M' * i : ℕ) : ZMod n) = 0 := by rw [hrel2, h, sub_self]
    obtain ⟨a, ha⟩ := hA2 _ ((ZMod.natCast_eq_zero_iff _ _).1 h1)
    exact ⟨a, by rw [ha, hrel1]⟩
  have hWmod : ∀ i j : ℕ, (j : ZMod n) = (i : ZMod n) → γ ^ i ∈ W → γ ^ j ∈ W := by
    intro i j h hi
    obtain ⟨a, ha⟩ := hQ i j h
    rw [ha, ← Algebra.smul_def]
    exact W.smul_mem a hi
  have hcast : ∀ a b : ℕ, a < n → b < n → (a : ZMod n) = (b : ZMod n) → a = b := by
    intro a b ha hb h
    have h' := (ZMod.natCast_eq_natCast_iff' a b n).1 h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  -- the difference set
  obtain ⟨B, hB⟩ : ∃ B : Set ℕ, B = {i : ℕ | i < n ∧ γ ^ i ∈ W} := ⟨_, rfl⟩
  have hBmem : ∀ i : ℕ, i ∈ B ↔ i < n ∧ γ ^ i ∈ W := by
    intro i
    rw [hB]
    rfl
  have hpds : IsPerfectDifferenceSet B n := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb, hne⟩ := hab
      show (a : ZMod n) - (b : ZMod n) ≠ 0
      intro h
      exact hne (hcast a b ((hBmem a).1 ha).1 ((hBmem b).1 hb).1 (sub_eq_zero.1 h))
    · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
      obtain ⟨ha, hb, hne⟩ := hab
      obtain ⟨ha', hb', hne'⟩ := hab'
      have heq' : (a : ZMod n) - (b : ZMod n) = (a' : ZMod n) - (b' : ZMod n) := heq
      obtain ⟨han, haW⟩ := (hBmem a).1 ha
      obtain ⟨hbn, hbW⟩ := (hBmem b).1 hb
      obtain ⟨han', haW'⟩ := (hBmem a').1 ha'
      obtain ⟨hbn', hbW'⟩ := (hBmem b').1 hb'
      -- `c = γ ^ a / γ ^ b`, written as a power of `γ`
      have hc : γ ^ (a + M' * b) ∉ (algebraMap F K).range := by
        rintro ⟨t, ht⟩
        have h1 := hA1 _ t ht
        have h2 : ((a + M' * b : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h1
        rw [hrel2] at h2
        exact hne (hcast a b han hbn (sub_eq_zero.1 h2))
      have hcy : γ ^ (a + M' * b) * γ ^ b ∈ W := by
        rw [hrel1]
        exact haW
      have hcy' : γ ^ (a + M' * b) * γ ^ b' ∈ W := by
        rw [← pow_add]
        refine hWmod a' _ ?_ haW'
        push_cast
        rw [hM'cast]
        linear_combination heq'
      obtain ⟨s, hs⟩ := key_unique h3 W hW _ hc hbW (pow_ne_zero b hγ0) hcy hbW' hcy'
      rw [Algebra.smul_def] at hs
      have hbb : b' = b := hcast b' b hbn' hbn (hP b b' s hs)
      subst hbb
      have haa : (a : ZMod n) = (a' : ZMod n) := by linear_combination heq'
      have haa' : a = a' := hcast a a' han han' haa
      subst haa'
      rfl
    · intro x hx
      have hx0 : x ≠ 0 := hx
      obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ZMod n) = x := ⟨x.val, ZMod.natCast_zmod_val x⟩
      obtain ⟨y, hyW, hy0, hcy⟩ := key_exists h3 W hW (γ ^ d) (pow_ne_zero d hγ0)
      obtain ⟨j, rfl⟩ := hγsurj y hy0
      rw [← pow_add] at hcy
      refine ⟨((d + j) % n, j % n), ⟨?_, ?_, ?_⟩, ?_⟩
      · exact (hBmem _).2 ⟨Nat.mod_lt _ hnpos, hWmod (d + j) _ (ZMod.natCast_mod _ _) hcy⟩
      · exact (hBmem _).2 ⟨Nat.mod_lt _ hnpos, hWmod j _ (ZMod.natCast_mod _ _) hyW⟩
      · intro h
        apply hx0
        have h' : ((d + j : ℕ) : ZMod n) = (j : ZMod n) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).2 h
        push_cast at h'
        rw [← hd]
        linear_combination h'
      · show (((d + j) % n : ℕ) : ZMod n) - ((j % n : ℕ) : ZMod n) = x
        rw [ZMod.natCast_mod, ZMod.natCast_mod, ← hd]
        push_cast
        ring
  -- counting the differences gives the size
  have hfin : B.Finite := (Set.finite_Iio n).subset (fun i hi => ((hBmem i).1 hi).1)
  have hcard : B.ncard = q + 1 := by
    have h1 : B.offDiag.ncard = n - 1 := by
      have h' := hpds.injOn.ncard_image
      rw [hpds.image_eq] at h'
      rw [← h']
      have h0 : {x : ZMod n | x ≠ 0} = ({0} : Set (ZMod n))ᶜ := by
        ext x
        simp
      rw [h0, Set.ncard_compl, Set.ncard_singleton, Nat.card_zmod]
    clear hB hBmem
    lift B to Finset ℕ using hfin
    rw [← Finset.coe_offDiag, Set.ncard_coe_finset, Finset.offDiag_card] at h1
    rw [Set.ncard_coe_finset]
    have hk : B.card * B.card = q ^ 2 + q + B.card := by
      have := Nat.le_mul_self B.card
      omega
    have hz : ((B.card : ℤ) - (q + 1)) * ((B.card : ℤ) + q) = 0 := by
      have hk' : (B.card : ℤ) * B.card = q ^ 2 + q + B.card := by exact_mod_cast hk
      linear_combination hk'
    rcases mul_eq_zero.1 hz with h | h
    · omega
    · omega
  refine ⟨B, hpds, hcard, ?_⟩
  intro a
  constructor
  · intro ha
    exact hWmod (a % n) a (ZMod.natCast_mod a n).symm ((hBmem _).1 ha).2
  · intro ha
    exact (hBmem _).2 ⟨Nat.mod_lt _ hnpos, hWmod a (a % n) (ZMod.natCast_mod a n) ha⟩

/-- The Singer construction for a field `F` with a cubic extension `K`. -/
theorem core {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3) :
    ∃ B : Set ℕ, IsPerfectDifferenceSet B (Nat.card F ^ 2 + Nat.card F + 1) ∧
      B.ncard = Nat.card F + 1 := by
  obtain ⟨γ, hγ0, hγsurj, hγord, hγpow⟩ := exists_gen K
  obtain ⟨W, hW⟩ := exists_plane (F := F) (K := K) h3
  obtain ⟨B, hB, hcard, _⟩ := core_with_plane h3 γ hγ0 hγsurj hγord hγpow W hW
  exact ⟨B, hB, hcard⟩

end OMA707Singer

namespace OMA707

/-- Shifting a perfect difference set by a map that acts as a translation on residues. -/
lemma pds_shift (D : Set ℕ) (n : ℕ) (f : ℕ → ℕ) (c : ZMod n)
    (hf : ∀ x ∈ D, ((f x : ℕ) : ZMod n) = (x : ZMod n) + c)
    (h : IsPerfectDifferenceSet D n) : IsPerfectDifferenceSet (f '' D) n := by
  have key : ∀ x ∈ D, ∀ y ∈ D,
      ((f x : ℕ) : ZMod n) - ((f y : ℕ) : ZMod n) = (x : ZMod n) - (y : ZMod n) := by
    intro x hx y hy; rw [hf x hx, hf y hy]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, v⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hne⟩
    have hab : (a, b) ∈ D.offDiag := ⟨ha, hb, fun e => hne (by simp only at e ⊢; rw [e])⟩
    have := h.mapsTo hab
    simp only [Set.mem_ofPred_eq] at this ⊢
    rw [key a ha b hb]; exact this
  · rintro ⟨u, v⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hne⟩ ⟨u', v'⟩ ⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩, hne'⟩ heq
    have hab : (a, b) ∈ D.offDiag := ⟨ha, hb, fun e => hne (by simp only at e ⊢; rw [e])⟩
    have hab' : (a', b') ∈ D.offDiag := ⟨ha', hb', fun e => hne' (by simp only at e ⊢; rw [e])⟩
    simp only at heq
    rw [key a ha b hb, key a' ha' b' hb'] at heq
    have := h.injOn hab hab' heq
    simp only [Prod.mk.injEq] at this ⊢
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨rfl, rfl⟩
  · intro z hz
    obtain ⟨⟨a, b⟩, ⟨ha, hb, hne⟩, hz'⟩ := h.surjOn hz
    refine ⟨(f a, f b), ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_⟩, ?_⟩
    · intro e
      have h1 := key a ha b hb
      simp only at e
      rw [e, sub_self] at h1
      have := h.mapsTo (show (a, b) ∈ D.offDiag from ⟨ha, hb, hne⟩)
      simp only [Set.mem_ofPred_eq] at this
      exact this h1.symm
    · simp only at hz' ⊢
      rw [key a ha b hb]; exact hz'

lemma pds7 : IsPerfectDifferenceSet ({1, 2, 4} : Set ℕ) 7 := by
  unfold IsPerfectDifferenceSet
  refine ⟨?mapsTo, ?injOn, ?surjOn⟩
  · intro ⟨a, b⟩ hab; simp only [Set.mem_offDiag, Set.mem_insert_iff, Set.mem_singleton_iff] at hab
    obtain ⟨ha, hb, hne⟩ := hab
    simp only [Set.mem_ofPred]
    rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    simp_all <;> decide
  · intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
    simp only [Set.mem_offDiag, Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
    obtain ⟨ha1, hb1, hne1⟩ := h1; obtain ⟨ha2, hb2, hne2⟩ := h2
    rcases ha1 with rfl | rfl | rfl <;>
    rcases hb1 with rfl | rfl | rfl <;>
    rcases ha2 with rfl | rfl | rfl <;>
    rcases hb2 with rfl | rfl | rfl <;>
    first
      | rfl
      | exact absurd rfl hne1
      | exact absurd rfl hne2
      | exact absurd heq (by decide)
  · intro x hx
    simp only [Set.mem_ofPred] at hx
    fin_cases x
    · exact absurd rfl hx
    · refine ⟨(2, 1), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(4, 2), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(4, 1), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(1, 4), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(2, 4), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(1, 2), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩

/-- Any set with at most one element embeds in a perfect difference set modulo 7. -/
lemma small_le_one (A : Set ℕ) (a : ℕ) (hA : A ⊆ {a}) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ A ⊆ B ∧ IsPerfectDifferenceSet B (p^2 + p + 1) := by
  refine ⟨(fun x => x - 1 + a) '' ({1, 2, 4} : Set ℕ), 2, Nat.prime_two.isPrimePow, ?_, ?_⟩
  · intro x hx
    rw [hA hx]
    exact ⟨1, by simp, by simp⟩
  · have : (2 : ℕ) ^ 2 + 2 + 1 = 7 := by norm_num
    rw [this]
    refine pds_shift _ 7 _ ((a : ZMod 7) - 1) ?_ pds7
    intro x hx
    have hx1 : 1 ≤ x := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> norm_num
    push_cast [Nat.cast_sub hx1]
    ring

/-- Choose representatives of a translate of a perfect difference set that contain A. -/
lemma lift_pds {A D : Set ℕ} {n : ℕ} [NeZero n] (c : ZMod n)
    (hD : IsPerfectDifferenceSet D n)
    (hA : Set.InjOn (fun a : ℕ => (a : ZMod n)) A)
    (hcover : ∀ a ∈ A, ∃ d ∈ D, (a : ZMod n) = (d : ZMod n) + c) :
    ∃ B : Set ℕ, A ⊆ B ∧ IsPerfectDifferenceSet B n := by
  classical
  let f (d : ℕ) : ℕ :=
    if h : ∃ a ∈ A, (a : ZMod n) = (d : ZMod n) + c then h.choose
    else ((d : ZMod n) + c).val
  refine ⟨f '' D, ?_, pds_shift D n f c ?_ hD⟩
  · intro a ha
    obtain ⟨d, hd, had⟩ := hcover a ha
    have h : ∃ x ∈ A, (x : ZMod n) = (d : ZMod n) + c := ⟨a, ha, had⟩
    refine ⟨d, hd, ?_⟩
    dsimp only [f]
    rw [dif_pos h]
    exact hA h.choose_spec.1 ha (h.choose_spec.2.trans had.symm)
  · intro d _
    dsimp only [f]
    split
    · rename_i h
      exact h.choose_spec.2
    · exact ZMod.natCast_zmod_val _

/-- Embed a set whose exponents in a Singer construction give points on a single line. -/
lemma embed_singer {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    (γ : K) (hγ0 : γ ≠ 0) (hγsurj : ∀ x : K, x ≠ 0 → ∃ i : ℕ, γ ^ i = x)
    (hγord : ∀ m : ℕ, γ ^ m = 1 → (Nat.card K - 1) ∣ m)
    (hγpow : γ ^ (Nat.card K - 1) = 1)
    (W : Submodule F K) (hW : Module.finrank F W = 2)
    (A : Set ℕ) (hn : Set.InjOn (fun a : ℕ => (a : ZMod (Nat.card F ^ 2 + Nat.card F + 1))) A)
    (hA : ∀ a ∈ A, γ ^ a ∈ W) :
    ∃ B : Set ℕ, A ⊆ B ∧ IsPerfectDifferenceSet B (Nat.card F ^ 2 + Nat.card F + 1) := by
  obtain ⟨D, hD, _, hmem⟩ := OMA707Singer.core_with_plane h3 γ hγ0 hγsurj hγord hγpow W hW
  have : NeZero (Nat.card F ^ 2 + Nat.card F + 1) := ⟨by omega⟩
  apply lift_pds 0 hD hn
  intro a ha
  exact ⟨a % (Nat.card F ^ 2 + Nat.card F + 1), (hmem a).2 (hA a ha), by
    rw [ZMod.natCast_mod, add_zero]⟩

lemma embed_pair {D : Set ℕ} {n : ℕ} [NeZero n] (hD : IsPerfectDifferenceSet D n)
    {a b : ℕ} (hab : (a : ZMod n) ≠ (b : ZMod n)) :
    ∃ B : Set ℕ, {a, b} ⊆ B ∧ IsPerfectDifferenceSet B n := by
  obtain ⟨⟨x, y⟩, ⟨hx, hy, _⟩, hxy⟩ := hD.surjOn
    (show (a : ZMod n) - (b : ZMod n) ∈ {z : ZMod n | z ≠ 0} from sub_ne_zero.mpr hab)
  change (x : ZMod n) - (y : ZMod n) = (a : ZMod n) - (b : ZMod n) at hxy
  apply lift_pds ((b : ZMod n) - (y : ZMod n)) hD
  · intro u hu v hv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact (hab huv).elim
    · exact (hab huv.symm).elim
    · rfl
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact ⟨x, hx, by linear_combination -hxy⟩
    · exact ⟨y, hy, by ring⟩

lemma singer_prime_power (p : ℕ) (hp : IsPrimePow p) :
    ∃ D : Set ℕ, IsPerfectDifferenceSet D (p ^ 2 + p + 1) := by
  obtain ⟨r, k, hr, hk, rfl⟩ := hp
  have : Fact r.Prime := ⟨Nat.prime_iff.2 hr⟩
  obtain ⟨D, hD, _⟩ := OMA707Singer.core (F := GaloisField r k)
    (K := FiniteField.Extension (GaloisField r k) r 3)
    (FiniteField.finrank_extension (GaloisField r k) r 3)
  rw [GaloisField.card r k hk.ne'] at hD
  exact ⟨D, hD⟩

lemma small_pair (a b : ℕ) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ {a, b} ⊆ B ∧
      IsPerfectDifferenceSet B (p ^ 2 + p + 1) := by
  by_cases hab : a = b
  · subst b
    exact small_le_one {a, a} a (by simp)
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max a b + 1)
  obtain ⟨D, hD⟩ := singer_prime_power p hprime.isPrimePow
  let n := p ^ 2 + p + 1
  have ha : a < n := by
    have := le_max_left a b
    dsimp [n]
    omega
  have hb : b < n := by
    have := le_max_right a b
    dsimp [n]
    omega
  have : NeZero n := ⟨(Nat.zero_lt_of_lt ha).ne'⟩
  have hab' : (a : ZMod n) ≠ (b : ZMod n) := by
    intro he
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at he
    exact hab he
  obtain ⟨B, hAB, hB⟩ := embed_pair hD hab'
  exact ⟨B, p, hprime.isPrimePow, hAB, hB⟩

/-- Write a three-element set in increasing order. -/
lemma ordered_triple {A : Set ℕ} (hA : A.ncard = 3) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ A = {a, b, c} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.mp hA
  rcases lt_or_gt_of_ne hab with hab | hba <;>
    rcases lt_or_gt_of_ne hac with hac | hca <;>
    rcases lt_or_gt_of_ne hbc with hbc | hcb
  · exact ⟨a, b, c, hab, hbc, rfl⟩
  · exact ⟨a, c, b, hac, hcb, by ext; simp [or_comm]⟩
  · omega
  · exact ⟨c, a, b, hca, hab, by ext; simp [or_comm, or_left_comm]⟩
  · exact ⟨b, a, c, hba, hac, by ext; simp [or_left_comm]⟩
  · omega
  · exact ⟨b, c, a, hbc, hca, by ext; simp [or_comm, or_left_comm]⟩
  · exact ⟨c, b, a, hcb, hba, by ext; simp [or_comm, or_left_comm]⟩

lemma translate_triple {a b c : ℕ} (hab : a ≤ b) (hac : a ≤ c)
    (hD : ∃ (D : Set ℕ) (p : ℕ), IsPrimePow p ∧ {0, b - a, c - a} ⊆ D ∧
      IsPerfectDifferenceSet D (p ^ 2 + p + 1)) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ {a, b, c} ⊆ B ∧
      IsPerfectDifferenceSet B (p ^ 2 + p + 1) := by
  obtain ⟨D, p, hp, hD, hpds⟩ := hD
  refine ⟨(fun x : ℕ => x + a) '' D, p, hp, ?_, pds_shift D _ _ (a : ZMod _) ?_ hpds⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, hD (by simp), Nat.zero_add _⟩
    · exact ⟨x - a, hD (by simp), Nat.sub_add_cancel hab⟩
    · exact ⟨x - a, hD (by simp), Nat.sub_add_cancel hac⟩
  · intro x _
    exact Nat.cast_add x a

/-- For a normalized triple, a plane containing its powers suffices once the modulus exceeds b. -/
lemma normalized_of_singer {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    (γ : K) (hγ0 : γ ≠ 0) (hγsurj : ∀ x : K, x ≠ 0 → ∃ i : ℕ, γ ^ i = x)
    (hγord : ∀ m : ℕ, γ ^ m = 1 → (Nat.card K - 1) ∣ m)
    (hγpow : γ ^ (Nat.card K - 1) = 1)
    (W : Submodule F K) (hW : Module.finrank F W = 2)
    {a b : ℕ} (hab : a < b) (hb : b < Nat.card F ^ 2 + Nat.card F + 1)
    (h0 : 1 ∈ W) (haW : γ ^ a ∈ W) (hbW : γ ^ b ∈ W) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ {0, a, b} ⊆ B ∧
      IsPerfectDifferenceSet B (p ^ 2 + p + 1) := by
  have : Fintype F := Fintype.ofFinite F
  have hp : IsPrimePow (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card F
  have hbound : ∀ x ∈ ({0, a, b} : Set ℕ), x < Nat.card F ^ 2 + Nat.card F + 1 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod (Nat.card F ^ 2 + Nat.card F + 1)))
      {0, a, b} := by
    intro x hx y hy he
    rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hbound x hx),
      Nat.mod_eq_of_lt (hbound y hy)] at he
  obtain ⟨D, hDA, hD⟩ := embed_singer h3 γ hγ0 hγsurj hγord hγpow W hW {0, a, b} hinj (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · simpa using h0
    · exact haW
    · exact hbW)
  exact ⟨D, Nat.card F, hp, hDA, hD⟩

/-- A primitive root of a trinomial with the prescribed exponents gives an embedding. -/
lemma normalized_of_primitive_relation {F K : Type*}
    [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b < Nat.card F ^ 2 + Nat.card F + 1)
    {γ : K} (hγ : IsPrimitiveRoot γ (Nat.card K - 1)) (s t : F)
    (hrel : γ ^ b = algebraMap F K s + algebraMap F K t * γ ^ a) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ {0, a, b} ⊆ B ∧
      IsPerfectDifferenceSet B (p ^ 2 + p + 1) := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype K := Fintype.ofFinite K
  have hF : 1 < Nat.card F := Finite.one_lt_card
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have : NeZero (Nat.card K - 1) := ⟨by omega⟩
  have hγ0 : γ ≠ 0 := hγ.ne_zero NeZero.out
  have hγsurj (x : K) (hx : x ≠ 0) : ∃ i : ℕ, γ ^ i = x := by
    have hxpow : x ^ (Nat.card K - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one x hx
    obtain ⟨i, _, hi⟩ := hγ.eq_pow_of_pow_eq_one hxpow
    exact ⟨i, hi⟩
  have hcardK : Nat.card K - 1 = (Nat.card F - 1) * (Nat.card F ^ 2 + Nat.card F + 1) := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), h3]
    exact OMA707Singer.cube_sub_one _ hF.le
  have hli : LinearIndependent F ![(1 : K), γ ^ a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro c hc
    rw [Algebra.smul_def, mul_one] at hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact pow_ne_zero a hγ0 hc.symm
    have hpow : γ ^ (a * (Nat.card F - 1)) = 1 := by
      rw [pow_mul, ← hc, ← map_pow, Nat.card_eq_fintype_card,
        FiniteField.pow_card_sub_one_eq_one c hc0, map_one]
    have hd := hγ.dvd_of_pow_eq_one _ hpow
    rw [hcardK, mul_comm a] at hd
    have hd' := Nat.dvd_of_mul_dvd_mul_left (show 0 < Nat.card F - 1 by omega) hd
    exact (not_le_of_gt (lt_trans hab hb)) (Nat.le_of_dvd ha hd')
  let W := Submodule.span F ({(1 : K), γ ^ a} : Set K)
  have hW : Module.finrank F W = 2 := by
    have hspan : Submodule.span F (Set.range ![(1 : K), γ ^ a]) = W :=
      congrArg (Submodule.span F) (Matrix.range_cons_cons_empty _ _ _)
    exact (congrArg (fun V : Submodule F K => Module.finrank F V) hspan).symm.trans
      (by simpa only [Fintype.card_fin] using finrank_span_eq_card hli)
  have h1 : (1 : K) ∈ W := Submodule.subset_span (by simp)
  have haW : γ ^ a ∈ W := Submodule.subset_span (by simp)
  have hbW : γ ^ b ∈ W := by
    rw [hrel, ← Algebra.smul_def, ← mul_one (algebraMap F K s), ← Algebra.smul_def]
    exact W.add_mem (W.smul_mem s h1) (W.smul_mem t haW)
  exact normalized_of_singer h3 γ hγ0 hγsurj hγ.dvd_of_pow_eq_one hγ.pow_eq_one
    W hW hab hb h1 haW hbW

/-- An element generating the group modulo base-field scalars has a primitive representative. -/
lemma rescale_projective_generator {F K : Type*}
    [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3) {α : K}
    (hα : IsPrimitiveRoot (α ^ (Nat.card F - 1)) (Nat.card F ^ 2 + Nat.card F + 1)) :
    ∃ (β : K) (c : F), IsPrimitiveRoot β (Nat.card K - 1) ∧
      β = algebraMap F K c * α := by
  let q := Nat.card F
  let n := q ^ 2 + q + 1
  let N := Nat.card K - 1
  change IsPrimitiveRoot (α ^ (q - 1)) n at hα
  have hq : 1 < q := Finite.one_lt_card
  have hn : 0 < n := by dsimp [n]; omega
  have hq1 : 0 < q - 1 := by omega
  have hN : N = (q - 1) * n := by
    dsimp [N, n, q]
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), h3]
    exact OMA707Singer.cube_sub_one _ hq.le
  have : NeZero N := ⟨by rw [hN]; exact (Nat.mul_pos hq1 hn).ne'⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hα.ne_zero hn.ne' (zero_pow hq1.ne')
  obtain ⟨g, _, hgSurj, hgDvd, hgPow⟩ := OMA707Singer.exists_gen K
  have hg : IsPrimitiveRoot g N := ⟨hgPow, hgDvd⟩
  have hg' : IsPrimitiveRoot (g ^ (q - 1)) n := by
    constructor
    · rw [← pow_mul, ← hN]
      exact hg.pow_eq_one
    · intro i hi
      rw [← pow_mul] at hi
      have hd := hg.dvd_of_pow_eq_one _ hi
      rw [hN] at hd
      exact Nat.dvd_of_mul_dvd_mul_left hq1 hd
  obtain ⟨j, hj⟩ := hgSurj α hα0
  have hα' : (g ^ (q - 1)) ^ j = α ^ (q - 1) := by
    rw [← pow_mul, mul_comm, pow_mul, hj]
  have hj' : j.Coprime n := (hg'.pow_iff_coprime hn j).mp (by rw [hα']; exact hα)
  have hd : n ∣ N := by rw [hN]; exact dvd_mul_left _ _
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd (ZMod.unitOfCoprime j hj')
  let k := (u : ZMod N).val
  have hk : k.Coprime N := ZMod.val_coe_unit_coprime u
  have hcast : (k : ZMod n) = (j : ZMod n) := by
    have hu' := congrArg (fun x : (ZMod n)ˣ => (x : ZMod n)) hu
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (u : ZMod N),
      ZMod.cast_natCast hd] at hu'
    exact hu'
  have hmod : k ≡ j [MOD n] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  let β := g ^ k
  have hβ : IsPrimitiveRoot β N := hg.pow_of_coprime k hk
  have hpow : β ^ (q - 1) = α ^ (q - 1) := by
    calc
      β ^ (q - 1) = (g ^ (q - 1)) ^ k := by dsimp [β]; rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (g ^ (q - 1)) ^ j := pow_eq_pow_of_modEq hmod hg'.pow_eq_one
      _ = α ^ (q - 1) := hα'
  have hratio : (β / α) ^ (q - 1) = 1 := by
    rw [div_pow, hpow, div_self (pow_ne_zero _ hα0)]
  obtain ⟨c, hc⟩ := OMA707Singer.mem_range_of_pow_card_eq (F := F) (β / α) (by
    change (β / α) ^ q = β / α
    calc
      (β / α) ^ q = (β / α) ^ (q - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = β / α := by rw [pow_succ, hratio, one_mul])
  exact ⟨β, c, hβ, ((eq_div_iff hα0).mp hc).symm⟩

lemma normalized_of_projective_relation {F K : Type*}
    [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b < Nat.card F ^ 2 + Nat.card F + 1)
    {α : K} (hα : IsPrimitiveRoot (α ^ (Nat.card F - 1)) (Nat.card F ^ 2 + Nat.card F + 1))
    (s t : F) (hrel : α ^ b = algebraMap F K s + algebraMap F K t * α ^ a) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ {0, a, b} ⊆ B ∧
      IsPerfectDifferenceSet B (p ^ 2 + p + 1) := by
  obtain ⟨β, c, hβ, hc⟩ := rescale_projective_generator h3 hα
  apply normalized_of_primitive_relation h3 ha hab hb hβ (c ^ b * s) (c ^ (b - a) * t)
  rw [hc, mul_pow, mul_pow, map_mul, map_mul, map_pow, map_pow, hrel]
  have hcb : (algebraMap F K c) ^ b =
      (algebraMap F K c) ^ (b - a) * (algebraMap F K c) ^ a := by
    rw [← pow_add, Nat.sub_add_cancel hab.le]
  rw [mul_add, hcb]
  ring

end OMA707

theorem OMA.solution : type_of% @Erdos707.erdos_707.variants.small_sidon_sets := by
  intro A hA h hSidon
  by_cases h1 : A.ncard ≤ 1
  · rcases (Set.ncard_le_one_iff_eq hA).mp h1 with rfl | ⟨a, rfl⟩
    · exact OMA707.small_le_one ∅ 0 (Set.empty_subset _)
    · exact OMA707.small_le_one {a} a le_rfl
  · by_cases h2 : A.ncard = 2
    · obtain ⟨a, b, _, rfl⟩ := Set.ncard_eq_two.mp h2
      exact OMA707.small_pair a b
    · have h3 : A.ncard = 3 := by omega
      obtain ⟨a, b, c, hab, hbc, rfl⟩ := OMA707.ordered_triple h3
      have hnonAP : b + b ≠ a + c := by
        intro he
        have hs := hSidon b (by simp) a (by simp) b (by simp) c (by simp) he
        omega
      apply OMA707.translate_triple hab.le (hab.trans hbc).le
      generalize hu : b - a = u
      generalize hv : c - a = v
      have hu0 : 0 < u := by omega
      have huv : u < v := by omega
      have hv2 : v ≠ 2 * u := by omega
      clear * - hu0 huv hv2
      sorry
