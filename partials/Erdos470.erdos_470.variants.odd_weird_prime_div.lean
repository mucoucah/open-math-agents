import FormalConjectures.ErdosProblems.«470»

-- Problem: Erdős Problem 470 — odd weird prime div
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/470.lean:121 (declaration Erdos470.erdos_470.variants.odd_weird_prime_div)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- A positive multiple of a pseudoperfect number is pseudoperfect. -/
lemma OMA.pp_of_dvd {d n : ℕ} (hdn : d ∣ n) (hn : 0 < n) (hd : d.Pseudoperfect) :
    n.Pseudoperfect := by
  obtain ⟨k, rfl⟩ := hdn
  obtain ⟨_, s, hs, hsum⟩ := hd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  refine ⟨hn, s.image (fun i => i * k), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' := hs hi
    rw [Nat.mem_properDivisors] at hi' ⊢
    exact ⟨Nat.mul_dvd_mul_right hi'.1 k, Nat.mul_lt_mul_of_pos_right hi'.2 hk⟩
  · rw [Finset.sum_image]
    · rw [← Finset.sum_mul, hsum]
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_right hk hab

/-- The set in the target is the finset of prime factors. -/
lemma OMA.ncard_eq (n : ℕ) (hn : n ≠ 0) :
    {m | m ∈ n.divisors ∧ m.Prime}.ncard = n.primeFactors.card := by
  have h : {m | m ∈ n.divisors ∧ m.Prime} = ↑n.primeFactors := by
    ext m
    simp only [Set.mem_setOf_eq, Nat.mem_divisors, Finset.mem_coe, Nat.mem_primeFactors]
    tauto
  rw [h, Set.ncard_coe_finset]

/-- Abundance criterion: if the excess of the proper divisor sum over `n` is a sum of distinct
proper divisors, then `n` is pseudoperfect (take the complementary set). -/
lemma OMA.pp_of_excess {n : ℕ} (hn : 0 < n) (t : Finset ℕ) (ht : t ⊆ n.properDivisors)
    (hsum : ∑ i ∈ t, i + n = ∑ i ∈ n.properDivisors, i) : n.Pseudoperfect := by
  refine ⟨hn, n.properDivisors \ t, Finset.sdiff_subset, ?_⟩
  have h := Finset.sum_sdiff (f := fun i => i) ht
  omega

/-- Certificate form for a concrete number: a strictly increasing list of proper divisors with
sum `n`. All three hypotheses are decidable for numerals (divisibility is a kernel `Nat.mod`). -/
lemma OMA.pp_of_list {n : ℕ} (hn : 0 < n) (l : List ℕ) (hl : l.Pairwise (· < ·))
    (hd : ∀ d ∈ l, d ∣ n ∧ d < n) (hs : l.sum = n) : n.Pseudoperfect := by
  refine ⟨hn, l.toFinset, ?_, ?_⟩
  · intro x hx
    rw [List.mem_toFinset] at hx
    rw [Nat.mem_properDivisors]
    exact hd x hx
  · have hnd : l.Nodup := hl.imp (fun h => Nat.ne_of_lt h)
    rw [List.sum_toFinset _ hnd]
    simpa using hs

/-- Sanity check of the certificate mechanism on the smallest odd abundant number. -/
lemma OMA.pp_945 : (945 : ℕ).Pseudoperfect :=
  OMA.pp_of_list (by norm_num) [1, 5, 7, 9, 15, 21, 35, 45, 63, 105, 135, 189, 315]
    (by decide) (by decide) (by decide)

/-- Prime step: if `q > 1` is coprime to `m` and `m * q = (sum of distinct divisors of m) +
q * (sum of distinct proper divisors of m)`, then `m * q` is pseudoperfect. -/
lemma OMA.pp_mul_step {m q : ℕ} (hm : 0 < m) (hq : 1 < q) (hc : Nat.Coprime q m)
    (s t : Finset ℕ) (hs : s ⊆ m.divisors) (ht : t ⊆ m.properDivisors)
    (hsum : ∑ i ∈ s, i + q * ∑ i ∈ t, i = m * q) : (m * q).Pseudoperfect := by
  have hinj : ∀ a ∈ t, ∀ b ∈ t, q * a = q * b → a = b := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  have hdisj : Disjoint s (t.image (fun i => q * i)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_image] at hx'
    obtain ⟨i, _, rfl⟩ := hx'
    have hdvd : q * i ∣ m := (Nat.mem_divisors.mp (hs hx)).1
    have hqm : q ∣ m := dvd_trans (dvd_mul_right q i) hdvd
    have hq1 : q = 1 := Nat.Coprime.eq_one_of_dvd hc hqm
    omega
  refine ⟨Nat.mul_pos hm (by omega), s ∪ t.image (fun i => q * i), ?_, ?_⟩
  · intro x hx
    rw [Nat.mem_properDivisors]
    rcases Finset.mem_union.mp hx with hx | hx
    · have hxm := Nat.mem_divisors.mp (hs hx)
      refine ⟨dvd_mul_of_dvd_left hxm.1 q, ?_⟩
      have hle : x ≤ m := Nat.le_of_dvd hm hxm.1
      nlinarith
    · rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have him := Nat.mem_properDivisors.mp (ht hi)
      refine ⟨?_, ?_⟩
      · rw [Nat.mul_comm m q]
        exact Nat.mul_dvd_mul_left q him.1
      · nlinarith [him.2]
  · rw [Finset.sum_union hdisj, Finset.sum_image hinj, ← Finset.mul_sum]
    exact hsum

/-- Prime power step: `m ∣ d` (think `d = m * q ^ k`), `q > 1` coprime to `m`. If
`d * q = (sum of distinct divisors of m) + q * (sum of distinct proper divisors of d)`, then
`d * q` is pseudoperfect. -/
lemma OMA.pp_mul_step_pow {m d q : ℕ} (hd : 0 < d) (hmd : m ∣ d) (hq : 1 < q)
    (hc : Nat.Coprime q m) (s t : Finset ℕ) (hs : s ⊆ m.divisors) (ht : t ⊆ d.properDivisors)
    (hsum : ∑ i ∈ s, i + q * ∑ i ∈ t, i = d * q) : (d * q).Pseudoperfect := by
  have hinj : ∀ a ∈ t, ∀ b ∈ t, q * a = q * b → a = b := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  have hdisj : Disjoint s (t.image (fun i => q * i)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_image] at hx'
    obtain ⟨i, _, rfl⟩ := hx'
    have hdvd : q * i ∣ m := (Nat.mem_divisors.mp (hs hx)).1
    have hqm : q ∣ m := dvd_trans (dvd_mul_right q i) hdvd
    have hq1 : q = 1 := Nat.Coprime.eq_one_of_dvd hc hqm
    omega
  refine ⟨Nat.mul_pos hd (by omega), s ∪ t.image (fun i => q * i), ?_, ?_⟩
  · intro x hx
    rw [Nat.mem_properDivisors]
    rcases Finset.mem_union.mp hx with hx | hx
    · have hxm := Nat.mem_divisors.mp (hs hx)
      refine ⟨dvd_mul_of_dvd_left (dvd_trans hxm.1 hmd) q, ?_⟩
      have hle : x ≤ d := Nat.le_of_dvd hd (dvd_trans hxm.1 hmd)
      nlinarith
    · rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have him := Nat.mem_properDivisors.mp (ht hi)
      refine ⟨?_, ?_⟩
      · rw [Nat.mul_comm d q]
        exact Nat.mul_dvd_mul_left q him.1
      · nlinarith [him.2]
  · rw [Finset.sum_union hdisj, Finset.sum_image hinj, ← Finset.mul_sum]
    exact hsum

/-- CORE GAP: an odd primitive abundant number (abundant, all proper divisors deficient) with at
most five prime factors is pseudoperfect. -/
lemma OMA.core (n : ℕ) (hodd : Odd n) (hab : n.Abundant)
    (hprim : ∀ d ∈ n.properDivisors, d.Deficient) (h5 : n.primeFactors.card ≤ 5) :
    n.Pseudoperfect := by
  sorry

/-- Reduction to the primitive abundant case. -/
lemma OMA.all_pp :
    ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 → n.Pseudoperfect := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hodd hab h5
    by_cases hprim : ∀ d ∈ n.properDivisors, d.Deficient
    · exact OMA.core n hodd hab hprim h5
    · simp only [not_forall] at hprim
      obtain ⟨d, hd, hdef⟩ := hprim
      rw [Nat.mem_properDivisors] at hd
      have hnpos : 0 < n := hab.pos
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hnpos
      have hdodd : Odd d := hodd.of_dvd_nat hd.1
      have hd5 : d.primeFactors.card ≤ 5 :=
        le_trans (Finset.card_le_card (Nat.primeFactors_mono hd.1 (by omega))) h5
      rcases Nat.deficient_or_perfect_or_abundant (n := d) (by omega) with h | h | h
      · exact absurd h hdef
      · exact OMA.pp_of_dvd hd.1 hnpos (ih d hd.2 hdodd h hd5)
      · exact OMA.pp_of_dvd hd.1 hnpos h.pseudoperfect

theorem OMA.solution : type_of% @Erdos470.erdos_470.variants.odd_weird_prime_div := by
  intro n hodd hw
  have hn : n ≠ 0 := by
    have := hw.1.pos
    omega
  rw [OMA.ncard_eq n hn]
  by_contra hlt
  exact hw.2 (OMA.all_pp n hodd hw.1 (by omega))
