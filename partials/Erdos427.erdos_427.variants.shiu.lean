import FormalConjectures.ErdosProblems.«427»

-- Problem: Shiu's theorem
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/427.lean:64 (declaration Erdos427.erdos_427.variants.shiu)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- Every prime of index at least one is odd. -/
lemma OMA.nth_prime_odd {i : ℕ} (hi : 1 ≤ i) : Odd (Nat.nth Nat.Prime i) := by
  have hp : (Nat.nth Nat.Prime i).Prime := Nat.prime_nth_prime i
  have h3 : 3 ≤ Nat.nth Nat.Prime i := by
    rw [← Nat.nth_prime_one_eq_three]
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hi
  exact hp.odd_of_ne_two (by omega)

/-- The easy moduli q = 1 and q = 2. -/
lemma OMA.shiu_small (k a q : ℕ) (hq : 1 ≤ q) (hq2 : q ≤ 2) (hcop : a.gcd q = 1) :
    { m : ℕ | ∀ p ∈ (Finset.Ico m (m + k)).image (Nat.nth Nat.Prime), p ≡ a [MOD q]}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ⟨N + 1, ?_, by omega⟩
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  have hi1 : 1 ≤ i := by simp at hi; omega
  interval_cases q
  · exact Nat.modEq_one
  · have ha : Odd a := by
      rcases Nat.even_or_odd a with h | h
      · exfalso
        have : 2 ∣ a.gcd 2 := Nat.dvd_gcd (even_iff_two_dvd.mp h) dvd_rfl
        omega
      · exact h
    have hp := OMA.nth_prime_odd hi1
    unfold Nat.ModEq
    rw [Nat.odd_iff.mp hp, Nat.odd_iff.mp ha]


lemma OMA.card_split (P : ℕ → Prop) [DecidablePred P] {l j r : ℕ} (hlj : l ≤ j) (hjr : j < r) :
    ((Finset.Ico l r).filter P).card =
      ((Finset.Ico l j).filter P).card + (if P j then 1 else 0) +
        ((Finset.Ico (j + 1) r).filter P).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_Ico_consecutive _ hlj hjr.le, Finset.sum_eq_sum_Ico_succ_bot hjr]
  ring

lemma OMA.run_of_excess (good : ℕ → Bool) (k : ℕ) (hk : 1 ≤ k) : ∀ n l : ℕ,
    (k - 1) * (((Finset.Ico l (l + n)).filter (fun i => good i = false)).card + 1) <
        ((Finset.Ico l (l + n)).filter (fun i => good i = true)).card →
    ∃ m : ℕ, l ≤ m ∧ m + k ≤ l + n ∧ ∀ i ∈ Finset.Ico m (m + k), good i = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hex
  by_cases hall : ∀ i ∈ Finset.Ico l (l + n), good i = true
  · by_cases hn : k ≤ n
    · exact ⟨l, le_rfl, by omega, fun i hi => hall i (by simp at hi ⊢; omega)⟩
    · exfalso
      have h1 : ((Finset.Ico l (l + n)).filter (fun i => good i = true)).card ≤ n := by
        calc _ ≤ (Finset.Ico l (l + n)).card := Finset.card_filter_le _ _
          _ = n := by simp
      have h2 : k - 1 ≤ (k - 1) * (((Finset.Ico l (l + n)).filter
          (fun i => good i = false)).card + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  · push Not at hall
    obtain ⟨j, hj, hjb⟩ := hall
    simp only [Finset.mem_Ico] at hj
    have hjf : good j = false := by simpa using hjb
    by_contra hno
    push Not at hno
    have A := ih (j - l) (by omega) l
    have B := ih (l + n - (j + 1)) (by omega) (j + 1)
    have hA : ¬ (k - 1) * (((Finset.Ico l (l + (j - l))).filter (fun i => good i = false)).card + 1) <
        ((Finset.Ico l (l + (j - l))).filter (fun i => good i = true)).card := by
      intro h
      obtain ⟨m, hm1, hm2, hm3⟩ := A h
      obtain ⟨i, hi, hgi⟩ := hno m hm1 (by omega)
      exact hgi (hm3 i hi)
    have hB : ¬ (k - 1) * (((Finset.Ico (j + 1) (j + 1 + (l + n - (j + 1)))).filter
          (fun i => good i = false)).card + 1) <
        ((Finset.Ico (j + 1) (j + 1 + (l + n - (j + 1)))).filter (fun i => good i = true)).card := by
      intro h
      obtain ⟨m, hm1, hm2, hm3⟩ := B h
      obtain ⟨i, hi, hgi⟩ := hno m (by omega) (by omega)
      exact hgi (hm3 i hi)
    have e1 : l + (j - l) = j := by omega
    have e2 : j + 1 + (l + n - (j + 1)) = l + n := by omega
    rw [e1] at hA
    rw [e2] at hB
    rw [OMA.card_split _ hj.1 hj.2, OMA.card_split (fun i => good i = true) hj.1 hj.2] at hex
    simp only [hjf, if_true, Bool.false_eq_true, if_false, add_zero] at hex
    push Not at hA hB
    set c := k - 1
    nlinarith

/-- Every prime of index i is at least i + 2. -/
lemma OMA.nth_prime_ge_add_two (i : ℕ) : i + 2 ≤ Nat.nth Nat.Prime i := by
  induction i with
  | zero =>
    have h2 : 2 ≤ Nat.nth Nat.Prime 0 := (Nat.prime_nth_prime 0).two_le
    omega
  | succ i ih =>
    have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self i)
    omega

/-- Maynard-Tao in arithmetic progressions (matches the conclusion of
Erdos6.erdos_6.variants.decreasing.R1.H2). -/
def OMA.MaynardAffine : Prop :=
  ∀ r : ℕ, ∃ k : ℕ, ∀ (H : Finset ℕ) (M b : ℕ), k ≤ H.card → 0 < M →
    (∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a) →
    ∀ N : ℕ, ∃ x, N < x ∧ r ≤ (H.filter fun a => (M * x + b + a).Prime).card

/-- CRT construction for Banks-Freiberg-Turnage-Butterbaugh: forces b ≡ a [MOD q]
and assigns a distinct large prime divisor ℓ_j to b + j for every j ∈ S. -/
lemma OMA.exists_bftb_crt (a q U : ℕ) (hq : 1 ≤ q) (S : Finset ℕ) :
    ∃ M b : ℕ, 0 < M ∧ q ∣ M ∧
      (∀ j ∈ S, Nat.nth Nat.Prime (U + q + j) ∣ M) ∧
      (∀ p, p.Prime → p ∣ M → p ∣ q ∨ ∃ j ∈ S, p = Nat.nth Nat.Prime (U + q + j)) ∧
      b ≡ a [MOD q] ∧
      ∀ j ∈ S, Nat.nth Nat.Prime (U + q + j) ∣ (b + j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨q, a, by omega, dvd_rfl, by simp, fun p _ hp => Or.inl hp, Nat.ModEq.refl a, by simp⟩
  | @insert j S hj ih =>
    obtain ⟨M, b, hMpos, hqM, hSM, hMfac, hba, hSb⟩ := ih
    set ℓ := Nat.nth Nat.Prime (U + q + j) with hℓ_def
    have hℓp : ℓ.Prime := Nat.prime_nth_prime (U + q + j)
    have hℓgt : U + q + j + 2 ≤ ℓ := OMA.nth_prime_ge_add_two (U + q + j)
    have hndvd : ¬ ℓ ∣ M := by
      intro hdiv
      rcases hMfac ℓ hℓp hdiv with hqdiv | ⟨j', hj'S, heq⟩
      · have hle : ℓ ≤ q := Nat.le_of_dvd (by omega) hqdiv
        omega
      · have hinj := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective heq
        have : j = j' := by omega
        exact hj (this ▸ hj'S)
    have hcop : Nat.Coprime M ℓ := (hℓp.coprime_iff_not_dvd.mpr hndvd).symm
    let t : ℕ := (ℓ - 1) * j
    let cr := Nat.chineseRemainder hcop b t
    refine ⟨M * ℓ, cr.val, Nat.mul_pos hMpos hℓp.pos, dvd_mul_of_dvd_left hqM ℓ, ?_, ?_, ?_, ?_⟩
    · intro j' hj'
      rcases Finset.mem_insert.mp hj' with rfl | hmem
      · exact dvd_mul_left ℓ M
      · exact dvd_mul_of_dvd_left (hSM j' hmem) ℓ
    · intro p hp hpM
      rcases hp.dvd_mul.mp hpM with h1 | h2
      · rcases hMfac p hp h1 with hqdiv | ⟨j', hj'S, rfl⟩
        · exact Or.inl hqdiv
        · exact Or.inr ⟨j', Finset.mem_insert_of_mem hj'S, rfl⟩
      · exact Or.inr ⟨j, Finset.mem_insert_self j S, (Nat.prime_dvd_prime_iff_eq hp hℓp).mp h2⟩
    · exact (cr.property.1.of_dvd hqM).trans hba
    · intro j' hj'
      rcases Finset.mem_insert.mp hj' with rfl | hmem
      · have hmod : cr.val + j' ≡ t + j' [MOD ℓ] := cr.property.2.add_right j'
        have ht : t + j' = ℓ * j' := by
          dsimp [t]
          rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left j' hℓp.pos)]
        rw [ht] at hmod
        exact Nat.dvd_of_mod_eq_zero (by
          change (cr.val + j') % ℓ = 0
          rw [hmod, Nat.mul_mod_right])
      · have hdivM : Nat.nth Nat.Prime (U + q + j') ∣ M := hSM j' hmem
        have hmod : cr.val + j' ≡ b + j' [MOD Nat.nth Nat.Prime (U + q + j')] :=
          (cr.property.1.of_dvd hdivM).add_right j'
        exact Nat.dvd_of_mod_eq_zero (by
          rw [hmod, Nat.mod_eq_zero_of_dvd (hSb j' hmem)])

/-- Solving M * x + b ≡ r (mod p) when p is prime and p ∤ M. -/
lemma OMA.exists_mul_add_zmod {M b p : ℕ} (hp : p.Prime) (hndvd : ¬ p ∣ M) (r : ZMod p) :
    ∃ x : ℕ, ((M * x + b : ℕ) : ZMod p) = r := by
  have : Fact p.Prime := ⟨hp⟩
  have hM0 : (M : ZMod p) ≠ 0 := by
    intro h
    exact hndvd ((ZMod.natCast_eq_zero_iff M p).mp h)
  let z : ZMod p := (M : ZMod p)⁻¹ * (r - (b : ZMod p))
  refine ⟨z.val, ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  dsimp [z]
  rw [← mul_assoc, mul_inv_cancel₀ hM0, one_mul, sub_add_cancel]

/-- Banks-Freiberg-Turnage-Butterbaugh (2015) reduction: Maynard-Tao in arithmetic progressions
implies arbitrarily far out blocks of k consecutive primes congruent to a mod q, hence density_excess. -/
lemma OMA.density_excess_of_maynard_affine (hMaynard : OMA.MaynardAffine)
    (k a q N : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) (hcop : a.gcd q = 1) :
    ∃ l n : ℕ, N < l ∧
      (k - 1) * (((Finset.Ico l (l + n)).filter
          (fun i => decide (Nat.nth Nat.Prime i ≡ a [MOD q]) = false)).card + 1) <
        ((Finset.Ico l (l + n)).filter
          (fun i => decide (Nat.nth Nat.Prime i ≡ a [MOD q]) = true)).card := by
  classical
  obtain ⟨K0, hK0⟩ := hMaynard k
  let K : ℕ := max K0 1
  have hKpos : 1 ≤ K := le_max_right _ _
  have hKge : K0 ≤ K := le_max_left _ _
  let g : ℕ → ℕ := fun i => q * Nat.nth Nat.Prime (K + i)
  have hg_inj : Function.Injective g := by
    intro i₁ i₂ heq
    have h1 : Nat.nth Nat.Prime (K + i₁) = Nat.nth Nat.Prime (K + i₂) :=
      Nat.eq_of_mul_eq_mul_left (by omega) heq
    have h2 : K + i₁ = K + i₂ := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h1
    omega
  let H : Finset ℕ := (Finset.range K).image g
  have hHcard : H.card = K := by
    rw [Finset.card_image_of_injective _ hg_inj, Finset.card_range]
  have hHne : H.Nonempty := by
    rw [← Finset.card_pos, hHcard]
    omega
  let hmin : ℕ := H.min' hHne
  let hmax : ℕ := H.max' hHne
  let J : Finset ℕ := (Finset.Icc hmin hmax) \ H
  obtain ⟨M, b, hMpos, hqM, hJM, hMfac, hba, hJb⟩ := OMA.exists_bftb_crt a q hmax hq J
  have hadm : ∀ p, p.Prime → ∃ x, ∀ h ∈ H, ¬ p ∣ M * x + b + h := by
    intro p hp
    by_cases hpM : p ∣ M
    · rcases hMfac p hp hpM with hpq | ⟨j, hjJ, rfl⟩
      · refine ⟨0, fun h hh hdiv => ?_⟩
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
        have hph : p ∣ q * Nat.nth Nat.Prime (K + i) := dvd_mul_of_dvd_left hpq _
        have hpb : p ∣ b := by
          have : p ∣ b + g i := by simpa using hdiv
          exact (Nat.dvd_add_left hph).mp this
        have hpa : p ∣ a := Nat.dvd_of_mod_eq_zero (by
          have h1 : b ≡ a [MOD p] := hba.of_dvd hpq
          change a % p = 0
          rw [← h1, Nat.mod_eq_zero_of_dvd hpb])
        have hp1 : p ∣ 1 := by
          rw [← hcop]
          exact Nat.dvd_gcd hpa hpq
        exact hp.not_dvd_one hp1
      · refine ⟨0, fun h hh hdiv => ?_⟩
        set ℓ := Nat.nth Nat.Prime (hmax + q + j)
        have hℓgt : hmax + q + j + 2 ≤ ℓ := OMA.nth_prime_ge_add_two (hmax + q + j)
        have hℓj : ℓ ∣ b + j := hJb j hjJ
        have hℓh : ℓ ∣ b + h := by simpa using hdiv
        have hjIcc : j ∈ Finset.Icc hmin hmax := (Finset.mem_sdiff.mp hjJ).1
        have hjnotH : j ∉ H := (Finset.mem_sdiff.mp hjJ).2
        have hne : h ≠ j := fun heq => hjnotH (heq ▸ hh)
        have hhle : h ≤ hmax := Finset.le_max' H h hh
        have hjle : j ≤ hmax := (Finset.mem_Icc.mp hjIcc).2
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hd : ℓ ∣ j - h := by
            have heq : b + j = (b + h) + (j - h) := by omega
            rw [heq] at hℓj
            exact (Nat.dvd_add_right hℓh).mp hℓj
          have hle : ℓ ≤ j - h := Nat.le_of_dvd (by omega) hd
          omega
        · have hd : ℓ ∣ h - j := by
            have heq : b + h = (b + j) + (h - j) := by omega
            rw [heq] at hℓh
            exact (Nat.dvd_add_right hℓj).mp hℓh
          have hle : ℓ ≤ h - j := Nat.le_of_dvd (by omega) hd
          omega
    · by_cases hpk : p ≤ K
      · obtain ⟨x, hx⟩ := OMA.exists_mul_add_zmod (M := M) (b := b) hp hpM 0
        have hpx : p ∣ M * x + b := (ZMod.natCast_eq_zero_iff (M * x + b) p).mp hx
        refine ⟨x, fun h hh hdiv => ?_⟩
        have hph : p ∣ h := (Nat.dvd_add_right hpx).mp hdiv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
        rcases hp.dvd_mul.mp hph with hpq | hpp
        · exact hpM (dvd_trans hpq hqM)
        · have hpi : (Nat.nth Nat.Prime (K + i)).Prime := Nat.prime_nth_prime (K + i)
          have heq : p = Nat.nth Nat.Prime (K + i) := (Nat.prime_dvd_prime_iff_eq hp hpi).mp hpp
          have hgt : K + i + 2 ≤ Nat.nth Nat.Prime (K + i) := OMA.nth_prime_ge_add_two (K + i)
          omega
      · have : Fact p.Prime := ⟨hp⟩
        let fT : ℕ → ZMod p := fun h => -((h : ℕ) : ZMod p)
        let T : Finset (ZMod p) := H.image fT
        have hTlt : T.card < (Finset.univ : Finset (ZMod p)).card := by
          have h1 : T.card ≤ H.card := Finset.card_image_le
          rw [Finset.card_univ, ZMod.card]
          omega
        obtain ⟨r, _, hrnotT⟩ := Finset.exists_mem_notMem_of_card_lt_card hTlt
        obtain ⟨x, hx⟩ := OMA.exists_mul_add_zmod (M := M) (b := b) hp hpM r
        refine ⟨x, fun h hh hdiv => ?_⟩
        have h0 : ((M * x + b + h : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff (M * x + b + h) p).mpr hdiv
        have hsum : r + ((h : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_add, hx] at h0
          exact h0
        have hr_eq : fT h = r := (eq_neg_of_add_eq_zero_left hsum).symm
        exact hrnotT (Finset.mem_image.mpr ⟨h, hh, hr_eq⟩)
  let N' : ℕ := max (Nat.nth Nat.Prime N) 2
  obtain ⟨x, hxgt, hrcard⟩ := hK0 H M b (by rw [hHcard]; exact hKge) hMpos hadm N'
  have hx2 : 2 < x := lt_of_le_of_lt (le_max_right _ _) hxgt
  have hxN : Nat.nth Nat.Prime N < x := lt_of_le_of_lt (le_max_left _ _) hxgt
  let S_p : Finset ℕ := (H.filter fun h => (M * x + b + h).Prime).image (fun h => M * x + b + h)
  have hshift_inj : Function.Injective (fun h => M * x + b + h) := by
    intro h₁ h₂ heq
    dsimp only at heq
    omega
  have hSpcard : k ≤ S_p.card := by
    rw [Finset.card_image_of_injective _ hshift_inj]
    exact hrcard
  have hSpne : S_p.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hSp_prime : ∀ p ∈ S_p, p.Prime := by
    intro p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hh).2
  have hSp_mod : ∀ p ∈ S_p, p ≡ a [MOD q] := by
    intro p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hp
    have hhH : h ∈ H := (Finset.mem_filter.mp hh).1
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hhH
    have hM0 : M * x ≡ 0 [MOD q] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact dvd_mul_of_dvd_left hqM x
    have hh0 : q * Nat.nth Nat.Prime (K + i) ≡ 0 [MOD q] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact dvd_mul_right q _
    have hcomb : M * x + b + g i ≡ 0 + a + 0 [MOD q] := (hM0.add hba).add hh0
    simpa only [zero_add, add_zero] using hcomb
  have hSp_bounds : ∀ p ∈ S_p, M * x + b + hmin ≤ p ∧ p ≤ M * x + b + hmax := by
    intro p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hp
    have hhH : h ∈ H := (Finset.mem_filter.mp hh).1
    exact ⟨by linarith [Finset.min'_le H h hhH], by linarith [Finset.le_max' H h hhH]⟩
  have hprime_in_Sp : ∀ p : ℕ, p.Prime → M * x + b + hmin ≤ p → p ≤ M * x + b + hmax → p ∈ S_p := by
    intro p hp hlo hhi
    let j : ℕ := p - (M * x + b)
    have hjp : M * x + b + j = p := by omega
    have hjIcc : j ∈ Finset.Icc hmin hmax := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hjH : j ∈ H := by
      by_contra hjnotH
      have hjJ : j ∈ J := Finset.mem_sdiff.mpr ⟨hjIcc, hjnotH⟩
      set ℓ := Nat.nth Nat.Prime (hmax + q + j)
      have hℓp : ℓ.Prime := Nat.prime_nth_prime (hmax + q + j)
      have hℓM : ℓ ∣ M := hJM j hjJ
      have hℓb : ℓ ∣ b + j := hJb j hjJ
      have hℓdiv : ℓ ∣ p := by
        rw [← hjp, add_assoc]
        exact dvd_add (dvd_mul_of_dvd_left hℓM x) hℓb
      have hℓleM : ℓ ≤ M := Nat.le_of_dvd hMpos hℓM
      have hℓlt : ℓ < p := by nlinarith
      have heq : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓp hp).mp hℓdiv
      omega
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hjH, hjp.symm ▸ hp⟩, hjp⟩
  let pmin : ℕ := S_p.min' hSpne
  let pmax : ℕ := S_p.max' hSpne
  let l : ℕ := Nat.count Nat.Prime pmin
  let lmax : ℕ := Nat.count Nat.Prime pmax
  have hl_eq : Nat.nth Nat.Prime l = pmin := Nat.nth_count (hSp_prime pmin (Finset.min'_mem S_p hSpne))
  have hlmax_eq : Nat.nth Nat.Prime lmax = pmax := Nat.nth_count (hSp_prime pmax (Finset.max'_mem S_p hSpne))
  have hNl : N < l := by
    have hlt : Nat.nth Nat.Prime N < Nat.nth Nat.Prime l := by
      rw [hl_eq]
      have hge := (hSp_bounds pmin (Finset.min'_mem S_p hSpne)).1
      nlinarith
    by_contra hle
    push Not at hle
    have hle' : Nat.nth Nat.Prime l ≤ Nat.nth Nat.Prime N :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hle
    exact absurd hle' (not_le.mpr hlt)
  have hlmax_ge : l + k - 1 ≤ lmax := by
    have hsub : S_p.image (Nat.count Nat.Prime) ⊆ Finset.Icc l lmax := by
      intro idx hidx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hidx
      exact Finset.mem_Icc.mpr
        ⟨Nat.count_monotone Nat.Prime (Finset.min'_le S_p p hp),
         Nat.count_monotone Nat.Prime (Finset.le_max' S_p p hp)⟩
    have hinj : Set.InjOn (Nat.count Nat.Prime) (S_p : Set ℕ) := by
      intro p₁ hp₁ p₂ hp₂ heq
      have h1 := Nat.nth_count (hSp_prime p₁ hp₁)
      have h2 := Nat.nth_count (hSp_prime p₂ hp₂)
      rw [← h1, ← h2, heq]
    have hcard_le : S_p.card ≤ (Finset.Icc l lmax).card := by
      calc S_p.card = (S_p.image (Nat.count Nat.Prime)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Icc l lmax).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard_le
    omega
  have hall : ∀ i ∈ Finset.Ico l (l + k), Nat.nth Nat.Prime i ≡ a [MOD q] := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hlo : pmin ≤ Nat.nth Nat.Prime i := by
      rw [← hl_eq]
      exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hi'.1
    have hhi : Nat.nth Nat.Prime i ≤ pmax := by
      rw [← hlmax_eq]
      exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
    have hmem : Nat.nth Nat.Prime i ∈ S_p :=
      hprime_in_Sp _ (Nat.prime_nth_prime i)
        ((hSp_bounds pmin (Finset.min'_mem S_p hSpne)).1.trans hlo)
        (hhi.trans (hSp_bounds pmax (Finset.max'_mem S_p hSpne)).2)
    exact hSp_mod _ hmem
  refine ⟨l, k, hNl, ?_⟩
  have hfalse : ((Finset.Ico l (l + k)).filter
      (fun i => decide (Nat.nth Nat.Prime i ≡ a [MOD q]) = false)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    simp [hall i hi]
  have htrue : ((Finset.Ico l (l + k)).filter
      (fun i => decide (Nat.nth Nat.Prime i ≡ a [MOD q]) = true)).card = k := by
    have hfilt : (Finset.Ico l (l + k)).filter
        (fun i => decide (Nat.nth Nat.Prime i ≡ a [MOD q]) = true) = Finset.Ico l (l + k) := by
      rw [Finset.filter_eq_self]
      intro i hi
      simp [hall i hi]
    rw [hfilt, Nat.card_Ico]
    omega
  rw [hfalse, htrue]
  omega

/-- Open core: Maynard-Tao in arithmetic progressions (already proved from Bombieri-Vinogradov
in proofs/Erdos6.erdos_6.variants.decreasing.R1.H2.lean; BV is proved across 4 leaves under
ElliottHalberstamConjecture.elliott_halberstam.variants.bombieri_vinogradov, totaling ~804 KiB). -/
lemma OMA.maynard_affine : OMA.MaynardAffine := by
  sorry

/-- Open core (Shiu-strength density excess): arbitrarily far out there is a block of
prime indices where the class a mod q beats all other classes by a factor k - 1. -/
lemma OMA.density_excess (k a q N : ℕ) (hk : 1 ≤ k) (hq : 3 ≤ q) (hcop : a.gcd q = 1) :
    ∃ l n : ℕ, N < l ∧
      (k - 1) * (((Finset.Ico l (l + n)).filter
          (fun i => decide (Nat.nth Nat.Prime i ≡ a [MOD q]) = false)).card + 1) <
        ((Finset.Ico l (l + n)).filter
          (fun i => decide (Nat.nth Nat.Prime i ≡ a [MOD q]) = true)).card :=
  OMA.density_excess_of_maynard_affine OMA.maynard_affine k a q N hk (by omega) hcop

theorem OMA.solution : type_of% @Erdos427.erdos_427.variants.shiu := by
  intro k a q hk hq hcop
  by_cases hq2 : q ≤ 2
  · exact OMA.shiu_small k a q hq hq2 hcop
  · refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨l, n, hl, h⟩ := OMA.density_excess k a q N hk (by omega) hcop
    obtain ⟨m, hm, _, hrun⟩ := OMA.run_of_excess _ k hk n l h
    refine ⟨m, ?_, lt_of_lt_of_le hl hm⟩
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact of_decide_eq_true (hrun i hi)
