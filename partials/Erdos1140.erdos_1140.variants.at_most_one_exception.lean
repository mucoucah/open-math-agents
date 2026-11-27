import FormalConjectures.ErdosProblems.«1140»

-- Problem: Erdős Problem 1140 — at most one exception
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1140.lean:79 (declaration Erdos1140.erdos_1140.variants.at_most_one_exception)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- STATUS: UNFINISHED. Everything in namespace OMA1140 is proved; OMA.solution is not.
-- Proved: every n with the property other than 2 is 2k^2 - 1 or 2k^2 - 2k + 1 (structure_of_prop),
-- none of these with 10 < k ≤ 3000 has the property (fin_A, fin_B), so any n outside the known
-- list lies in one of the two families with k > 3000 (large_family); and every odd prime q with
-- q^2 + 1 < 2n has Jacobi symbol (2n / q) = -1 (jacobi_eq_neg_one).
-- Missing: the analytic input. Two verified conditional versions are given,
-- reduction_tatuzawa (Tatuzawa plus class number formula bounds, the literature route) and
-- reduction_families (the two families separately). Neither set of hypotheses is in Mathlib.

namespace OMA1140

open Erdos1140

lemma prime_of_prop {n : ℕ} (h : Erdos1140Prop n) : n.Prime := by
  have h0 := h.2 0 (by simpa using h.1)
  simpa using h0

lemma not_prop_of_factor {n y a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : n = 2 * y ^ 2 + a * b) : ¬ Erdos1140Prop n := by
  intro hP
  have hpos : 0 < a * b := Nat.mul_pos (by omega) (by omega)
  have hlt : 2 * y ^ 2 < n := by omega
  have hpr := hP.2 y hlt
  have hsub : n - 2 * y ^ 2 = a * b := by omega
  rw [hsub] at hpr
  exact Nat.not_prime_mul (by omega) (by omega) hpr

lemma not_prop_of_dvd {n y a : ℕ} (ha : 2 ≤ a) (hle : 2 * y ^ 2 + 2 * a ≤ n)
    (hmod : (n - 2 * y ^ 2) % a = 0) : ¬ Erdos1140Prop n := by
  obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hb2 : 2 ≤ b := by
    by_contra hcon
    have hb1 : b ≤ 1 := by omega
    have hmul : a * b ≤ a * 1 := Nat.mul_le_mul_left a hb1
    omega
  exact not_prop_of_factor (y := y) ha hb2 (by omega)

-- Finite verification, family 2k^2 - 1, for 11 ≤ k ≤ 3010 (k = 1000 c + i + 11), in three
-- kernel-checked blocks of 1000: an explicit proper divisor a of n - 2y^2.
lemma fin_B0 : ∀ i < 1000, ∃ a < 44, ∃ y < a, 2 ≤ a ∧
    2 * y ^ 2 + 2 * a ≤ 2 * (i + 11) ^ 2 - 1 ∧
    (2 * (i + 11) ^ 2 - 1 - 2 * y ^ 2) % a = 0 := by
  decide +kernel

lemma fin_B1 : ∀ i < 1000, ∃ a < 44, ∃ y < a, 2 ≤ a ∧
    2 * y ^ 2 + 2 * a ≤ 2 * (i + 1011) ^ 2 - 1 ∧
    (2 * (i + 1011) ^ 2 - 1 - 2 * y ^ 2) % a = 0 := by
  decide +kernel

lemma fin_B2 : ∀ i < 1000, ∃ a < 44, ∃ y < a, 2 ≤ a ∧
    2 * y ^ 2 + 2 * a ≤ 2 * (i + 2011) ^ 2 - 1 ∧
    (2 * (i + 2011) ^ 2 - 1 - 2 * y ^ 2) % a = 0 := by
  decide +kernel

lemma fin_B : ∀ c < 3, ∀ i < 1000, ∃ a < 44, ∃ y < a, 2 ≤ a ∧
    2 * y ^ 2 + 2 * a ≤ 2 * (1000 * c + i + 11) ^ 2 - 1 ∧
    (2 * (1000 * c + i + 11) ^ 2 - 1 - 2 * y ^ 2) % a = 0 := by
  intro c hc i hi
  interval_cases c
  · have h : 1000 * 0 + i + 11 = i + 11 := by omega
    rw [h]; exact fin_B0 i hi
  · have h : 1000 * 1 + i + 11 = i + 1011 := by omega
    rw [h]; exact fin_B1 i hi
  · have h : 1000 * 2 + i + 11 = i + 2011 := by omega
    rw [h]; exact fin_B2 i hi

-- Finite verification, family 2k^2 - 2k + 1, for 11 ≤ k ≤ 3010, in three blocks.
lemma fin_A0 : ∀ i < 1000, ∃ a < 38, ∃ y < a, 2 ≤ a ∧
    2 * y ^ 2 + 2 * a ≤ 2 * (i + 11) ^ 2 - 2 * (i + 11) + 1 ∧
    (2 * (i + 11) ^ 2 - 2 * (i + 11) + 1 - 2 * y ^ 2) % a = 0 := by
  decide +kernel

lemma fin_A1 : ∀ i < 1000, ∃ a < 38, ∃ y < a, 2 ≤ a ∧
    2 * y ^ 2 + 2 * a ≤ 2 * (i + 1011) ^ 2 - 2 * (i + 1011) + 1 ∧
    (2 * (i + 1011) ^ 2 - 2 * (i + 1011) + 1 - 2 * y ^ 2) % a = 0 := by
  decide +kernel

lemma fin_A2 : ∀ i < 1000, ∃ a < 38, ∃ y < a, 2 ≤ a ∧
    2 * y ^ 2 + 2 * a ≤ 2 * (i + 2011) ^ 2 - 2 * (i + 2011) + 1 ∧
    (2 * (i + 2011) ^ 2 - 2 * (i + 2011) + 1 - 2 * y ^ 2) % a = 0 := by
  decide +kernel

lemma fin_A : ∀ c < 3, ∀ i < 1000, ∃ a < 38, ∃ y < a, 2 ≤ a ∧
    2 * y ^ 2 + 2 * a ≤ 2 * (1000 * c + i + 11) ^ 2 - 2 * (1000 * c + i + 11) + 1 ∧
    (2 * (1000 * c + i + 11) ^ 2 - 2 * (1000 * c + i + 11) + 1 - 2 * y ^ 2) % a = 0 := by
  intro c hc i hi
  interval_cases c
  · have h : 1000 * 0 + i + 11 = i + 11 := by omega
    rw [h]; exact fin_A0 i hi
  · have h : 1000 * 1 + i + 11 = i + 1011 := by omega
    rw [h]; exact fin_A1 i hi
  · have h : 1000 * 2 + i + 11 = i + 2011 := by omega
    rw [h]; exact fin_A2 i hi

lemma exists_sqrt_half (n : ℕ) : ∃ j : ℕ, 2 * j ^ 2 ≤ n ∧ n < 2 * (j + 1) ^ 2 := by
  have h1 : Nat.sqrt (n / 2) ^ 2 ≤ n / 2 := Nat.sqrt_le' (n / 2)
  have h2 : n / 2 < (Nat.sqrt (n / 2) + 1) ^ 2 := Nat.lt_succ_sqrt' (n / 2)
  exact ⟨Nat.sqrt (n / 2), by omega, by omega⟩

-- The elementary structure lemma.
lemma structure_of_prop {n : ℕ} (hP : Erdos1140Prop n) (h2 : n ≠ 2) :
    ∃ j : ℕ, n + 1 = 2 * (j + 1) ^ 2 ∨ n + (2 * j + 1) = 2 * (j + 1) ^ 2 := by
  have hpr := prime_of_prop hP
  have hodd : n % 2 = 1 := by
    rcases hpr.eq_two_or_odd with h | h
    · exact absurd h h2
    · exact h
  obtain ⟨j, hj1, hj2⟩ := exists_sqrt_half n
  obtain ⟨r, hr⟩ : ∃ r, n = 2 * j ^ 2 + r := ⟨n - 2 * j ^ 2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, n + t = 2 * (j + 1) ^ 2 := ⟨2 * (j + 1) ^ 2 - n, by omega⟩
  have hexp : 2 * (j + 1) ^ 2 = 2 * j ^ 2 + 4 * j + 2 := by ring
  have hrt : r + t = 4 * j + 2 := by omega
  have hrodd : r % 2 = 1 := by omega
  have htodd : t % 2 = 1 := by omega
  have hrprime : r.Prime := by
    have hlt : 2 * j ^ 2 < n := by omega
    have h := hP.2 j hlt
    have hsub : n - 2 * j ^ 2 = r := by omega
    rwa [hsub] at h
  have hr2 : 2 ≤ r := hrprime.two_le
  -- Claim 1: r ≥ 2j + 1
  have hr_ge : 2 * j + 1 ≤ r := by
    by_contra hcon
    have hr_le : r + 1 ≤ 2 * j := by omega
    rcases Nat.le_total r j with hrj | hjr
    · obtain ⟨y, hy⟩ : ∃ y, j = r + y := ⟨j - r, by omega⟩
      refine not_prop_of_factor (y := y) (a := r) (b := 2 * r + 4 * y + 1) hr2 (by omega) ?_ hP
      rw [hr, hy]; ring
    · obtain ⟨y, hy⟩ : ∃ y, r = j + y := ⟨r - j, by omega⟩
      obtain ⟨z, hz⟩ : ∃ z, j = y + z := ⟨j - y, by omega⟩
      refine not_prop_of_factor (y := y) (a := 2 * y + z) (b := 2 * z + 1) (by omega) (by omega)
        ?_ hP
      rw [hr, hy, hz]; ring
  -- Claim 2: t = 1 or t ≥ 2j + 1
  have ht_cases : t = 1 ∨ 2 * j + 1 ≤ t := by
    by_contra hcon
    have ht3 : 3 ≤ t := by omega
    have ht_le : t + 1 ≤ 2 * j := by omega
    rcases Nat.le_total t (j + 1) with htj | hjt
    · obtain ⟨y, hy⟩ : ∃ y, j + 1 = t + y := ⟨j + 1 - t, by omega⟩
      obtain ⟨u, hu⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      refine not_prop_of_factor (y := y) (a := u + 1) (b := 2 * u + 4 * y + 1) (by omega)
        (by omega) ?_ hP
      have h3 : n + (u + 1) = 2 * (u + 1 + y) ^ 2 := by rw [← hu, ← hy]; exact ht
      have h4 : n + (u + 1) = 2 * y ^ 2 + (u + 1) * (2 * u + 4 * y + 1) + (u + 1) := by
        rw [h3]; ring
      exact Nat.add_right_cancel h4
    · obtain ⟨y, hy⟩ : ∃ y, t = j + 1 + y := ⟨t - (j + 1), by omega⟩
      obtain ⟨z, hz⟩ : ∃ z, j = y + z := ⟨j - y, by omega⟩
      refine not_prop_of_factor (y := y) (a := 2 * y + z + 1) (b := 2 * z + 1) (by omega)
        (by omega) ?_ hP
      have h3 : n + (2 * y + z + 1) = 2 * (y + z + 1) ^ 2 := by
        have h5 : t = 2 * y + z + 1 := by omega
        rw [← h5, ← hz]; exact ht
      have h4 : n + (2 * y + z + 1) = 2 * y ^ 2 + (2 * y + z + 1) * (2 * z + 1) + (2 * y + z + 1) := by
        rw [h3]; ring
      exact Nat.add_right_cancel h4
  refine ⟨j, ?_⟩
  rcases ht_cases with h | h
  · left; rw [← ht, h]
  · right
    have : t = 2 * j + 1 := by omega
    rw [← ht, this]

-- If 2n is a square modulo an odd prime q with q^2 + 1 < 2n, the property fails.
lemma no_square_mod {n q c : ℕ} (hP : Erdos1140Prop n) (hq : q.Prime) (hq2 : q ≠ 2)
    (hlt : q ^ 2 + 1 < 2 * n) (hcq : c < q) (hc : (c * c) % q = (2 * n) % q) : False := by
  have hodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · exact absurd h hq2
    · exact h
  have hdvd : (q : ℤ) ∣ (2 * (n : ℤ)) - (c : ℤ) * c := by
    have h := (Nat.modEq_iff_dvd (n := q) (a := c * c) (b := 2 * n)).mp hc
    push_cast at h
    exact h
  obtain ⟨y, hy1, hy2⟩ : ∃ y : ℕ, 2 * y + 1 ≤ q ∧ (q : ℤ) ∣ 2 * (n : ℤ) - 4 * (y : ℤ) ^ 2 := by
    rcases Nat.even_or_odd' c with ⟨y, hy | hy⟩
    · refine ⟨y, by omega, ?_⟩
      have h3 : 2 * (n : ℤ) - 4 * (y : ℤ) ^ 2 = 2 * (n : ℤ) - (c : ℤ) * c := by
        rw [hy]; push_cast; ring
      rw [h3]; exact hdvd
    · obtain ⟨z, hz⟩ : ∃ z, q = c + 2 * z := ⟨(q - c) / 2, by omega⟩
      refine ⟨z, by omega, ?_⟩
      have h3 : 2 * (n : ℤ) - 4 * (z : ℤ) ^ 2 =
          (2 * (n : ℤ) - (c : ℤ) * c) + (q : ℤ) * ((c : ℤ) - 2 * z) := by
        rw [hz]; push_cast; ring
      rw [h3]; exact dvd_add hdvd (dvd_mul_right _ _)
  obtain ⟨d, hd⟩ : ∃ d, q = 2 * y + 1 + d := ⟨q - (2 * y + 1), by omega⟩
  have hy3 : 4 * y ^ 2 + 2 * q + (4 * d * y + d ^ 2) = q ^ 2 + 1 := by rw [hd]; ring
  obtain ⟨w, hw⟩ : ∃ w, n = 2 * y ^ 2 + w := ⟨n - 2 * y ^ 2, by omega⟩
  have hwq : q < w := by omega
  have hdvd2 : q ∣ 2 * w := by
    have h4 : (q : ℤ) ∣ ((2 * w : ℕ) : ℤ) := by
      have h5 : ((2 * w : ℕ) : ℤ) = 2 * (n : ℤ) - 4 * (y : ℤ) ^ 2 := by
        rw [hw]; push_cast; ring
      rw [h5]; exact hy2
    exact_mod_cast h4
  rcases (Nat.Prime.dvd_mul hq).mp hdvd2 with h | h
  · have h6 := Nat.le_of_dvd (by norm_num) h
    have h7 := hq.two_le
    omega
  · obtain ⟨b, hb⟩ := h
    have hb2 : 2 ≤ b := by
      by_contra hcon
      have hb1 : b ≤ 1 := by omega
      have hmul : q * b ≤ q * 1 := Nat.mul_le_mul_left q hb1
      omega
    exact not_prop_of_factor (y := y) hq.two_le hb2 (by rw [hw, hb]) hP

-- Every odd prime q with q^2 + 1 < 2n is inert in Q(sqrt(2n)): the symbol (2n / q) is -1.
lemma jacobi_eq_neg_one {n q : ℕ} (hP : Erdos1140Prop n) (hq : q.Prime) (hq2 : q ≠ 2)
    (hlt : q ^ 2 + 1 < 2 * n) : jacobiSym (2 * (n : ℤ)) q = -1 := by
  have hfact : Fact q.Prime := ⟨hq⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  by_contra hne
  have hex : ∃ c : ZMod q, ((2 * n : ℕ) : ZMod q) = c * c := by
    have e : (((2 * (n : ℤ)) : ℤ) : ZMod q) = ((2 * n : ℕ) : ZMod q) := by simp
    by_cases h0 : (((2 * (n : ℤ)) : ℤ) : ZMod q) = 0
    · exact ⟨0, by rw [← e, h0]; simp⟩
    · rcases legendreSym.eq_one_or_neg_one q h0 with h1 | h1
      · obtain ⟨c, hc⟩ := (legendreSym.eq_one_iff q h0).mp h1
        exact ⟨c, by rw [← e, hc]⟩
      · exact absurd h1 hne
  obtain ⟨c, hc⟩ := hex
  have hc' : ((2 * n : ℕ) : ZMod q) = ((c.val * c.val : ℕ) : ZMod q) := by
    rw [hc]; push_cast; rw [ZMod.natCast_zmod_val]
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hc'
  exact no_square_mod hP hq hq2 hlt (ZMod.val_lt c) hmod.symm

-- Every n with the property outside the known list lies in one of two families with k > 3000.
lemma large_family {n : ℕ} (hP : Erdos1140Prop n)
    (hn : n ∉ ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ)) :
    ∃ k, 3000 < k ∧ (n = 2 * k ^ 2 - 1 ∨ n = 2 * k ^ 2 - 2 * k + 1) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn
  have hn2 : 2 ≤ n := (prime_of_prop hP).two_le
  obtain ⟨j, hj⟩ := structure_of_prop hP hn.1
  obtain ⟨k, hk⟩ : ∃ k, k = j + 1 := ⟨j + 1, rfl⟩
  rw [← hk] at hj
  rcases hj with hj | hj
  · have hn' : n = 2 * k ^ 2 - 1 := by omega
    by_cases hkK : 3000 < k
    · exact ⟨k, hkK, Or.inl hn'⟩
    · exfalso
      by_cases hk10 : 10 < k
      · obtain ⟨a, -, y, -, ha2, hle, hmod⟩ :=
          fin_B ((k - 11) / 1000) (by omega) ((k - 11) % 1000) (by omega)
        have hk_eq : 1000 * ((k - 11) / 1000) + (k - 11) % 1000 + 11 = k := by omega
        rw [hk_eq] at hle hmod
        rw [hn'] at hP
        exact not_prop_of_dvd ha2 hle hmod hP
      · have hk' : k ≤ 10 := by omega
        have hk1 : 1 ≤ k := by omega
        clear hn'
        interval_cases k
        all_goals first
          | omega
          | exact not_prop_of_factor (y := 1) (a := 3) (b := 5) (by omega) (by omega) (by omega) hP
          | exact not_prop_of_factor (y := 0) (a := 7) (b := 7) (by omega) (by omega) (by omega) hP
          | exact not_prop_of_factor (y := 1) (a := 3) (b := 23) (by omega) (by omega) (by omega) hP
          | exact not_prop_of_factor (y := 1) (a := 5) (b := 19) (by omega) (by omega) (by omega) hP
          | exact not_prop_of_factor (y := 1) (a := 5) (b := 25) (by omega) (by omega) (by omega) hP
          | exact not_prop_of_factor (y := 0) (a := 7) (b := 23) (by omega) (by omega) (by omega) hP
  · have hexp : 2 * k ^ 2 = 2 * j ^ 2 + 4 * j + 2 := by rw [hk]; ring
    have hn' : n = 2 * k ^ 2 - 2 * k + 1 := by omega
    by_cases hkK : 3000 < k
    · exact ⟨k, hkK, Or.inr hn'⟩
    · exfalso
      by_cases hk10 : 10 < k
      · obtain ⟨a, -, y, -, ha2, hle, hmod⟩ :=
          fin_A ((k - 11) / 1000) (by omega) ((k - 11) % 1000) (by omega)
        have hk_eq : 1000 * ((k - 11) / 1000) + (k - 11) % 1000 + 11 = k := by omega
        rw [hk_eq] at hle hmod
        rw [hn'] at hP
        exact not_prop_of_dvd ha2 hle hmod hP
      · have hk' : k ≤ 10 := by omega
        have hk1 : 1 ≤ k := by omega
        clear hn' hexp
        interval_cases k
        all_goals first
          | omega
          | exact not_prop_of_factor (y := 0) (a := 5) (b := 5) (by omega) (by omega) (by omega) hP
          | exact not_prop_of_factor (y := 1) (a := 3) (b := 13) (by omega) (by omega) (by omega) hP
          | exact not_prop_of_factor (y := 0) (a := 5) (b := 17) (by omega) (by omega) (by omega) hP
          | exact not_prop_of_factor (y := 1) (a := 3) (b := 37) (by omega) (by omega) (by omega) hP
          | exact not_prop_of_factor (y := 0) (a := 5) (b := 29) (by omega) (by omega) (by omega) hP

-- h1: family n = 2k^2 - 2k + 1 (n = 1 mod 4, 2n = (2k-1)^2 + 1): no member with k > 3000 has the
-- property (Epure and Gica, Theorem 4.1, resting on Byeon and Lee).
-- h2: family n = 2k^2 - 1 (2n = (2k)^2 - 2): at most one member with k > 3000 has the property
-- (Mollin and Williams, resting on Tatuzawa).
lemma reduction_families
    (h1 : ∀ k : ℕ, 3000 < k → ¬ Erdos1140Prop (2 * k ^ 2 - 2 * k + 1))
    (h2 : {k : ℕ | 3000 < k ∧ Erdos1140Prop (2 * k ^ 2 - 1)}.Subsingleton) :
    ({n : ℕ | Erdos1140Prop n} \ {2, 5, 7, 13, 31, 61, 181, 199}).Subsingleton := by
  have key : ∀ n : ℕ, Erdos1140Prop n → n ∉ ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ) →
      ∃ k, (3000 < k ∧ Erdos1140Prop (2 * k ^ 2 - 1)) ∧ n = 2 * k ^ 2 - 1 := by
    intro n hP hn
    obtain ⟨k, hk, hB | hA⟩ := large_family hP hn
    · exact ⟨k, ⟨hk, hB ▸ hP⟩, hB⟩
    · exact absurd (hA ▸ hP) (h1 k hk)
  intro a ha b hb
  obtain ⟨ka, hka, rfl⟩ := key a ha.1 ha.2
  obtain ⟨kb, hkb, rfl⟩ := key b hb.1 hb.2
  have hkk : ka = kb := h2 hka hkb
  rw [hkk]

-- h1: Tatuzawa for the characters (2p / .), h2 and h3: class number formula bounds for the
-- two families, assuming only that the odd primes q with q^2 + 1 < 2n are inert (which the
-- property gives by jacobi_eq_neg_one). L(1, chi) is the limit of the partial sums of chi(m) / m.
lemma reduction_tatuzawa
    (h1 : ∀ p q : ℕ, p.Prime → q.Prime → 18000000 < p → 18000000 < q →
    ∀ L M : ℝ,
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N,
        ((jacobiSym (2 * (p : ℤ)) (m + 1) : ℤ) : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds L) →
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N,
        ((jacobiSym (2 * (q : ℤ)) (m + 1) : ℤ) : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds M) →
      L ≤ 4 * Real.log (8 * (p : ℝ)) / Real.sqrt (8 * (p : ℝ)) →
      M ≤ 4 * Real.log (8 * (q : ℝ)) / Real.sqrt (8 * (q : ℝ)) →
      p = q)
    (h2 : ∀ k n : ℕ, 3000 < k → n = 2 * k ^ 2 - 1 → n.Prime →
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ^ 2 + 1 < 2 * n → jacobiSym (2 * (n : ℤ)) q = -1) →
    ∃ L : ℝ,
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N,
        ((jacobiSym (2 * (n : ℤ)) (m + 1) : ℤ) : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds L) ∧
      L ≤ 4 * Real.log (8 * (n : ℝ)) / Real.sqrt (8 * (n : ℝ)))
    (h3 : ∀ k n : ℕ, 3000 < k → n = 2 * k ^ 2 - 2 * k + 1 → n.Prime →
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ^ 2 + 1 < 2 * n → jacobiSym (2 * (n : ℤ)) q = -1) →
    ∃ L : ℝ,
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N,
        ((jacobiSym (2 * (n : ℤ)) (m + 1) : ℤ) : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds L) ∧
      L ≤ 4 * Real.log (8 * (n : ℝ)) / Real.sqrt (8 * (n : ℝ))) :
    ({n : ℕ | Erdos1140Prop n} \ {2, 5, 7, 13, 31, 61, 181, 199}).Subsingleton := by
  have key : ∀ n : ℕ, Erdos1140Prop n → n ∉ ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ) →
      18000000 < n ∧ ∃ L : ℝ,
        Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N,
          ((jacobiSym (2 * (n : ℤ)) (m + 1) : ℤ) : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds L) ∧
        L ≤ 4 * Real.log (8 * (n : ℝ)) / Real.sqrt (8 * (n : ℝ)) := by
    intro n hP hn
    obtain ⟨k, hk, hB | hA⟩ := large_family hP hn
    · have hsq : 3001 ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left (by omega) 2
      exact ⟨by omega, h2 k n hk hB (prime_of_prop hP)
        (fun q hq hq2 hlt => jacobi_eq_neg_one hP hq hq2 hlt)⟩
    · have hsq : 3001 * k ≤ k ^ 2 := by
        rw [pow_two]; exact Nat.mul_le_mul_right k (by omega)
      exact ⟨by omega, h3 k n hk hA (prime_of_prop hP)
        (fun q hq hq2 hlt => jacobi_eq_neg_one hP hq hq2 hlt)⟩
  intro a ha b hb
  obtain ⟨ha1, La, hLa, hLa'⟩ := key a ha.1 ha.2
  obtain ⟨hb1, Lb, hLb, hLb'⟩ := key b hb.1 hb.2
  exact h1 a b (prime_of_prop ha.1) (prime_of_prop hb.1) ha1 hb1 La Lb hLa hLb hLa' hLb'

end OMA1140

theorem OMA.solution : type_of% @Erdos1140.erdos_1140.variants.at_most_one_exception := by
  sorry
