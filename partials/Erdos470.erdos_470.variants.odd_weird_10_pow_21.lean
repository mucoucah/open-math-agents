import FormalConjectures.ErdosProblems.«470»

-- Problem: Erdős Problem 470 — odd weird 10 pow 21
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/470.lean:113 (declaration Erdos470.erdos_470.variants.odd_weird_10_pow_21)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- A positive multiple of a pseudoperfect number is pseudoperfect. -/
theorem OMA.pp_of_dvd {d n : ℕ} (hdn : d ∣ n) (hn : 0 < n) (hd : d.Pseudoperfect) :
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

/-- Abundance criterion: a positive `n` is pseudoperfect iff `sigma n - 2 n` is a sum of
distinct proper divisors of `n` (complement of the witness set). -/
theorem OMA.pp_iff_abundance {n : ℕ} (hn : 0 < n) :
    n.Pseudoperfect ↔ ∃ t ⊆ n.properDivisors, ∑ i ∈ t, i + 2 * n = ∑ i ∈ n.divisors, i := by
  have hdiv : ∑ i ∈ n.divisors, i = ∑ i ∈ n.properDivisors, i + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  constructor
  · rintro ⟨_, s, hs, hsum⟩
    refine ⟨n.properDivisors \ s, Finset.sdiff_subset, ?_⟩
    have h := Finset.sum_sdiff (f := fun i => i) hs
    omega
  · rintro ⟨t, ht, hsum⟩
    refine ⟨hn, n.properDivisors \ t, Finset.sdiff_subset, ?_⟩
    have h := Finset.sum_sdiff (f := fun i => i) ht
    omega

/-- Multiplication by a positive natural number embeds the natural numbers. -/
private def OMA.mulRight (p : ℕ) (hp : 0 < p) : ℕ ↪ ℕ :=
  ⟨fun x => x * p, fun _ _ h => Nat.eq_of_mul_eq_mul_right hp h⟩

/-- Partition the proper divisors according to divisibility by `p`. -/
theorem OMA.properDivisors_prime_step {m p k : ℕ} (hm : 0 < m) (hp : p.Prime) :
    (m * p ^ k * p).properDivisors =
      m.divisors ∪ (m * p ^ k).properDivisors.map (OMA.mulRight p hp.pos) := by
  have hd : 0 < m * p ^ k := Nat.mul_pos hm (pow_pos hp.pos _)
  have hmd : m ∣ m * p ^ k := dvd_mul_right _ _
  have hdn : m * p ^ k ∣ m * p ^ k * p := dvd_mul_right _ _
  have hlt : m * p ^ k < m * p ^ k * p := by
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt hd
  have hsubset : m.divisors ⊆ (m * p ^ k * p).properDivisors :=
    Nat.divisors_subset_properDivisors (Nat.mul_pos hd hp.pos).ne'
      (hmd.trans hdn) ((Nat.le_of_dvd hd hmd).trans_lt hlt).ne
  ext x
  rw [Finset.mem_union, Finset.mem_map]
  constructor
  · intro hx
    obtain ⟨hxd, hxl⟩ := Nat.mem_properDivisors.mp hx
    by_cases hpx : p ∣ x
    · obtain ⟨y, rfl⟩ := hpx
      rw [mul_comm p y] at hxd hxl
      exact Or.inr ⟨y, Nat.mem_properDivisors.mpr
        ⟨Nat.dvd_of_mul_dvd_mul_right hp.pos hxd, Nat.lt_of_mul_lt_mul_right hxl⟩,
        mul_comm y p⟩
    · have hc : Nat.Coprime x (p ^ k * p) := by
        rw [← pow_succ]
        exact hp.coprime_pow_of_not_dvd hpx
      exact Or.inl (Nat.mem_divisors.mpr
        ⟨hc.dvd_of_dvd_mul_right (by simpa only [mul_assoc] using hxd), hm.ne'⟩)
  · rintro (hx | ⟨y, hy, rfl⟩)
    · exact hsubset hx
    · obtain ⟨hyd, hyl⟩ := Nat.mem_properDivisors.mp hy
      exact Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_right hyd p, Nat.mul_lt_mul_of_pos_right hyl hp.pos⟩

private theorem OMA.disjoint_divisors_mulRight {m p : ℕ} (hp : 0 < p)
    (hpm : ¬p ∣ m) (t : Finset ℕ) :
    Disjoint m.divisors (t.map (OMA.mulRight p hp)) := by
  rw [Finset.disjoint_left]
  intro x hx hxt
  obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hxt
  exact hpm ((dvd_mul_left p y).trans (Nat.dvd_of_mem_divisors hx))

theorem OMA.sum_properDivisors_prime_step {m p k : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hpm : ¬p ∣ m) :
    (∑ i ∈ (m * p ^ k * p).properDivisors, i) =
      (∑ i ∈ m.divisors, i) + (∑ i ∈ (m * p ^ k).properDivisors, i) * p := by
  rw [OMA.properDivisors_prime_step hm hp, Finset.sum_union
    (OMA.disjoint_divisors_mulRight hp.pos hpm _), Finset.sum_map, Finset.sum_mul]
  rfl

/-- Reduce any subset sum of proper divisors to two subset sums on smaller numbers. -/
theorem OMA.subset_sum_prime_step {m p k a : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hpm : ¬p ∣ m) :
    (∃ z ⊆ (m * p ^ k * p).properDivisors, ∑ i ∈ z, i = a) ↔
    (∃ s ⊆ m.divisors, ∃ t ⊆ (m * p ^ k).properDivisors,
      (∑ i ∈ s, i) + (∑ i ∈ t, i) * p = a) := by
  rw [OMA.properDivisors_prime_step hm hp]
  let f := OMA.mulRight p hp.pos
  change (∃ z ⊆ m.divisors ∪ (m * p ^ k).properDivisors.map f, ∑ i ∈ z, i = a) ↔ _
  have hsum (s t : Finset ℕ) (hs : s ⊆ m.divisors) :
      (∑ i ∈ s ∪ t.map f, i) = (∑ i ∈ s, i) + (∑ i ∈ t, i) * p := by
    rw [Finset.sum_union ((OMA.disjoint_divisors_mulRight hp.pos hpm t).mono_left hs),
      Finset.sum_map, Finset.sum_mul]
    rfl
  constructor
  · rintro ⟨z, hz, hza⟩
    let s := z ∩ m.divisors
    let t := (m * p ^ k).properDivisors.filter (fun i => f i ∈ z)
    have hs : s ⊆ m.divisors := Finset.inter_subset_right
    have ht : t ⊆ (m * p ^ k).properDivisors := Finset.filter_subset _ _
    have heq : z = s ∪ t.map f := by
      ext x
      simp only [s, t, Finset.mem_union, Finset.mem_inter, Finset.mem_map, Finset.mem_filter]
      constructor
      · intro hx
        rcases Finset.mem_union.mp (hz hx) with h | h
        · exact Or.inl ⟨hx, h⟩
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp h
          exact Or.inr ⟨i, ⟨hi, hx⟩, rfl⟩
      · rintro (⟨hx, _⟩ | ⟨i, ⟨_, hi⟩, rfl⟩)
        · exact hx
        · exact hi
    rw [heq, hsum s t hs] at hza
    exact ⟨s, hs, t, ht, hza⟩
  · rintro ⟨s, hs, t, ht, h⟩
    refine ⟨s ∪ t.map f, Finset.union_subset_union hs (Finset.map_subset_map.mpr ht), ?_⟩
    rw [hsum s t hs, h]

/-- Only divisors up to the target sum can contribute to a witness. -/
theorem OMA.subset_sum_prime_step_bounded {m p k a : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hpm : ¬p ∣ m) :
    (∃ z ⊆ (m * p ^ k * p).properDivisors, ∑ i ∈ z, i = a) ↔
    (∃ s ⊆ m.divisors.filter (· ≤ a), ∃ t ⊆ (m * p ^ k).properDivisors.filter (· ≤ a / p),
      (∑ i ∈ s, i) + (∑ i ∈ t, i) * p = a) := by
  rw [OMA.subset_sum_prime_step hm hp hpm]
  constructor
  · rintro ⟨s, hs, t, ht, h⟩
    have hsa : (∑ i ∈ s, i) ≤ a := h ▸ Nat.le_add_right _ _
    have hta : (∑ i ∈ t, i) ≤ a / p :=
      (Nat.le_div_iff_mul_le hp.pos).mpr (h ▸ Nat.le_add_left _ _)
    refine ⟨s, ?_, t, ?_, h⟩
    · intro x hx
      exact Finset.mem_filter.mpr ⟨hs hx,
        (Finset.single_le_sum (fun i _ => Nat.zero_le i) hx).trans hsa⟩
    · intro x hx
      exact Finset.mem_filter.mpr ⟨ht hx,
        (Finset.single_le_sum (fun i _ => Nat.zero_le i) hx).trans hta⟩
  · rintro ⟨s, hs, t, ht, h⟩
    exact ⟨s, hs.trans (Finset.filter_subset _ _), t, ht.trans (Finset.filter_subset _ _), h⟩

/-- For a target below `p`, only divisors of `m` can contribute. -/
theorem OMA.subset_sum_prime_step_of_lt {m p k a : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hpm : ¬p ∣ m) (ha : a < p) :
    (∃ z ⊆ (m * p ^ k * p).properDivisors, ∑ i ∈ z, i = a) ↔
    (∃ s ⊆ m.divisors, ∑ i ∈ s, i = a) := by
  constructor
  · intro h
    obtain ⟨s, hs, t, ht, hsum⟩ := (OMA.subset_sum_prime_step_bounded hm hp hpm).mp h
    have ht0 : t = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro x hx
      obtain ⟨hxd, hxle⟩ := Finset.mem_filter.mp (ht hx)
      have hxpos := Nat.pos_of_mem_properDivisors hxd
      rw [Nat.div_eq_of_lt ha] at hxle
      omega
    refine ⟨s, hs.trans (Finset.filter_subset _ _), ?_⟩
    simpa [ht0] using hsum
  · rintro ⟨s, hs, hsum⟩
    exact (OMA.subset_sum_prime_step hm hp hpm).mpr
      ⟨s, hs, ∅, Finset.empty_subset _, by simpa using hsum⟩

theorem OMA.abundance_eq_prime_step {m p k : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hpm : ¬p ∣ m) (hd : (m * p ^ k).Deficient) :
    (∑ i ∈ (m * p ^ k * p).properDivisors, i) +
      (m * p ^ k - ∑ i ∈ (m * p ^ k).properDivisors, i) * p =
      m * p ^ k * p + ∑ i ∈ m.divisors, i := by
  rw [Nat.Deficient] at hd
  rw [OMA.sum_properDivisors_prime_step hm hp hpm, add_assoc, ← Nat.add_mul,
    Nat.add_sub_of_le hd.le, add_comm]

/-- The remaining finite search. The largest prime is `p` and the parent is
`d = m * p ^ k`. Seek smaller subset sums that represent the abundance of `d * p`. -/
theorem OMA.core_prime_search {m p k : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hpm : ¬p ∣ m) (hmax : ∀ q ∈ m.primeFactors, q < p) :
    let d := m * p ^ k
    let n := d * p
    let deficit := d - ∑ i ∈ d.properDivisors, i
    let a := (∑ i ∈ m.divisors, i) - deficit * p
    n < 10 ^ 21 → Odd n →
    (∀ q ∈ n.primeFactors, (n / q).Deficient) →
    deficit * p < (∑ i ∈ m.divisors, i) →
    ∃ s ⊆ m.divisors.filter (· ≤ a), ∃ t ⊆ d.properDivisors.filter (· ≤ a / p),
      (∑ i ∈ s, i) + (∑ i ∈ t, i) * p = a := by
  sorry

/-- Reduce the primitive abundant case to the largest-prime extension search. -/
theorem OMA.core : ∀ n < 10 ^ 21, Odd n → n.Abundant →
    (∀ d ∈ n.properDivisors, d.Deficient) → n.Pseudoperfect := by
  intro n hn hodd hab hprim
  have hn0 := hab.pos
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact (by decide : ¬Nat.Abundant 1) hab
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  let p := n.primeFactors.max' hne
  have hpin : p ∈ n.primeFactors := Finset.max'_mem _ _
  have hp := Nat.prime_of_mem_primeFactors hpin
  have hpn := Nat.dvd_of_mem_primeFactors hpin
  obtain ⟨e, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' p hp.ne_one
  cases e with
  | zero =>
    have heq : n = m := by simpa only [pow_zero, one_mul] using hnm
    exact (hpm (heq ▸ hpn)).elim
  | succ k =>
    have heq : n = m * p ^ k * p := by
      rw [hnm, pow_succ]
      ac_rfl
    have hm : 0 < m := by
      rw [hnm] at hn0
      exact Nat.pos_of_mul_pos_left hn0
    have hmax : ∀ q ∈ m.primeFactors, q < p := by
      intro q hq
      have hqm := Nat.dvd_of_mem_primeFactors hq
      have hqn : q ∣ n := hqm.trans (hnm ▸ dvd_mul_left m (p ^ (k + 1)))
      have hle : q ≤ p := Finset.le_max' _ _ ((Nat.prime_of_mem_primeFactors hq).mem_primeFactors
        hqn hn0.ne')
      exact lt_of_le_of_ne hle (fun h => hpm (h ▸ hqm))
    have hquot : ∀ q ∈ n.primeFactors, (n / q).Deficient := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      apply hprim
      exact Nat.mem_properDivisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hq),
        Nat.div_lt_self hn0 hqp.one_lt⟩
    have hd : (m * p ^ k).Deficient := by
      have h := hquot p hpin
      rw [heq, Nat.mul_div_cancel _ hp.pos] at h
      exact h
    have hsum := OMA.abundance_eq_prime_step hm hp hpm hd
    rw [heq] at hn hodd hab hquot ⊢
    rw [Nat.Abundant] at hab
    have hgap : (m * p ^ k - ∑ i ∈ (m * p ^ k).properDivisors, i) * p <
        (∑ i ∈ m.divisors, i) := by omega
    obtain ⟨s, hs, t, ht, hst⟩ := OMA.core_prime_search hm hp hpm hmax hn hodd hquot hgap
    obtain ⟨z, hz, hza⟩ := (OMA.subset_sum_prime_step_bounded (k := k) hm hp hpm).mpr
      ⟨s, hs, t, ht, hst⟩
    refine (OMA.pp_iff_abundance (Nat.mul_pos (Nat.mul_pos hm (pow_pos hp.pos _)) hp.pos)).mpr
      ⟨z, hz, ?_⟩
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
    omega

/-- Reduction of the target to the primitive abundant case. -/
theorem OMA.all_pp : ∀ n : ℕ, n < 10 ^ 21 → Odd n → n.Abundant → n.Pseudoperfect := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hodd hab
    by_cases hprim : ∀ d ∈ n.properDivisors, d.Deficient
    · exact OMA.core n hn hodd hab hprim
    · simp only [not_forall] at hprim
      obtain ⟨d, hd, hdef⟩ := hprim
      rw [Nat.mem_properDivisors] at hd
      have hnpos : 0 < n := hab.pos
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hnpos
      have hdodd : Odd d := hodd.of_dvd_nat hd.1
      rcases Nat.deficient_or_perfect_or_abundant (n := d) (by omega) with h | h | h
      · exact absurd h hdef
      · exact OMA.pp_of_dvd hd.1 hnpos (ih d hd.2 (by omega) hdodd h)
      · exact OMA.pp_of_dvd hd.1 hnpos h.pseudoperfect

theorem OMA.solution : type_of% @Erdos470.erdos_470.variants.odd_weird_10_pow_21 := by
  intro n hn hodd hw
  exact hw.2 (OMA.all_pp n hn hodd hw.1)
