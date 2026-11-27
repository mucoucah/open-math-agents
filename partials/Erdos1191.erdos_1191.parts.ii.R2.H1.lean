import OMAReductions.R_Erdos1191_erdos_1191_parts_ii_R2

-- Step Erdos1191.erdos_1191.parts.ii.R2.H1: hypothesis H1 of reduction Erdos1191.erdos_1191.parts.ii.R2
-- Credit: @<handle>
-- H1 := ∃ d J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,     (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧     (∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∀ u ∈ B j, ∀ v ∈ B j,       a + b = u + v → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧     (∀ j, J ≤ j → j ≤ N → 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧     ∀ i j, j / 3 < i → i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,       b < a → v < u → a - b ≠ u - v  /-- An integer code whose pair sums determine the original sum and the unordered pair of dyadic labels, moving each dyadic block up by at most a polynomial in the label. -/

/-! Cluster localization for the nearby-scale packing hypothesis. -/

namespace Erdos1191HostPacking

open OMA.R_Erdos1191_erdos_1191_parts_ii_R2
open Filter
open scoped BigOperators

/-- A single finite Sidon set may witness all scales by clusters at arbitrary locations. -/
private def SidonClusterProfile : Prop :=
  ∃ d J : ℕ, ∀ N : ℕ, ∃ S : Finset ℕ, IsSidon (S : Set ℕ) ∧
    ∀ j, J ≤ j → j ≤ N → ∃ t : ℕ,
      2 ^ j ≤ (S.filter fun x ↦ t ≤ x ∧ x < t + 2 ^ j).card ^ 2 *
        (j + 1) ^ (2 * (d + 1))

private lemma reciprocal_weight_sum_le (I : Finset ℕ) :
    ∑ j ∈ I, (1 : ℚ) / ((j + 1) * (j + 2)) ≤ 1 := by
  have hsum (N : ℕ) :
      ∑ j ∈ Finset.range N, (1 : ℚ) / ((j + 1) * (j + 2)) =
        1 - 1 / (N + 1) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      have h₁ : (N : ℚ) + 1 ≠ 0 := by positivity
      have h₂ : (N : ℚ) + 2 ≠ 0 := by positivity
      field_simp
      ring
  calc
    _ ≤ ∑ j ∈ Finset.range (I.sup id + 1), (1 : ℚ) / ((j + 1) * (j + 2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)))
        (fun j _ _ ↦ by positivity)
    _ ≤ 1 := by rw [hsum]; exact sub_le_self _ (by positivity)

/-- Allocate disjoint subfinsets even when the available pools overlap completely. -/
private lemma disjoint_cluster_allocation (I : Finset ℕ) (A : ℕ → Finset ℕ) :
    ∃ T : ℕ → Finset ℕ, (∀ j, T j ⊆ A j) ∧
      (∀ j ∈ I, (T j).card = (A j).card / ((j + 1) * (j + 2))) ∧
      ∀ i j, i ≠ j → Disjoint (T i) (T j) := by
  classical
  let q (j : ℕ) := (A j).card / ((j + 1) * (j + 2))
  let ι := (j : ↥I) × Fin (q j.1)
  let pool (p : ι) := A p.1.1
  have hall (s : Finset ι) : s.card ≤ (s.biUnion pool).card := by
    let U := s.biUnion pool
    let P := s.image fun p ↦ p.1.1
    let fibers (j : ℕ) := (Finset.range (q j)).image fun k ↦ (j,k)
    have hfcard j : (fibers j).card = q j := by
      rw [Finset.card_image_of_injective, Finset.card_range]
      exact fun _ _ h ↦ congrArg Prod.snd h
    have hleft : s.card ≤ ∑ j ∈ P, q j := by
      calc
        _ ≤ (P.biUnion fibers).card := by
          apply Finset.card_le_card_of_injOn (fun p : ι ↦ (p.1.1, p.2.val))
          · intro p hp
            exact Finset.mem_biUnion.mpr ⟨p.1.1, Finset.mem_image_of_mem _ hp,
              Finset.mem_image_of_mem _ (Finset.mem_range.mpr p.2.isLt)⟩
          · rintro ⟨a,k⟩ _ ⟨b,l⟩ _ h
            have hab : a = b := Subtype.ext (congrArg Prod.fst h)
            subst b
            have hkl : k = l := Fin.ext (congrArg Prod.snd h)
            subst l
            rfl
        _ ≤ _ := by simpa only [hfcard] using (Finset.card_biUnion_le (s := P) (t := fibers))
    have hpool j (hj : j ∈ P) : (A j).card ≤ U.card := by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.card_le_card fun x hx ↦ Finset.mem_biUnion.mpr ⟨p, hp, hx⟩
    have hright : ∑ j ∈ P, q j ≤ U.card := by
      have hdiv j (hj : j ∈ P) :
          (q j : ℚ) ≤ (U.card : ℚ) * (1 / ((j + 1) * (j + 2))) := by
        rw [mul_one_div]
        apply (le_div_iff₀ (by positivity)).mpr
        have hnat : q j * ((j + 1) * (j + 2)) ≤ U.card :=
          (Nat.div_mul_le_self _ _).trans (hpool j hj)
        exact_mod_cast hnat
      have hcast : (∑ j ∈ P, (q j : ℚ)) ≤ U.card := calc
        _ ≤ ∑ j ∈ P, (U.card : ℚ) * (1 / ((j + 1) * (j + 2))) := Finset.sum_le_sum hdiv
        _ = _ := (Finset.mul_sum ..).symm
        _ ≤ (U.card : ℚ) * 1 := mul_le_mul_of_nonneg_left (reciprocal_weight_sum_le P) (by positivity)
        _ = _ := mul_one _
      exact_mod_cast hcast
    exact hleft.trans hright
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' pool).mp hall
  let T (j : ℕ) := if hj : j ∈ I then Finset.univ.image (fun k : Fin (q j) ↦ f ⟨⟨j,hj⟩,k⟩)
    else ∅
  refine ⟨T, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases hj : j ∈ I
    · rw [show T j = _ by exact dif_pos hj] at hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact hmem ⟨⟨j,hj⟩,k⟩
    · simp [T, hj] at hx
  · intro j hj
    rw [show T j = _ by exact dif_pos hj, Finset.card_image_of_injective]
    · simp [q]
    · intro k l he
      have he' := hf he
      cases he'
      rfl
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    by_cases hi : i ∈ I
    swap
    · simp [T, hi] at hxi
    by_cases hj : j ∈ I
    swap
    · simp [T, hj] at hxj
    rw [show T i = _ by exact dif_pos hi] at hxi
    rw [show T j = _ by exact dif_pos hj] at hxj
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hxi
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hxj
    exact hij (congrArg (fun p : ι ↦ p.1.1) (hf (hk.trans hl.symm)))

private lemma dyadic_energy_count_transfer (j d k M m : ℕ)
    (hcount : 2 ^ j ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1)))
    (hcard : M ≤ m * (j + 1) ^ k) :
    2 ^ j ≤ m ^ 2 * (j + 1) ^ (2 * (d + k + 1)) := by
  calc
    _ ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1)) := hcount
    _ ≤ (m * (j + 1) ^ k) ^ 2 * (j + 1) ^ (2 * (d + 1)) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcard 2)
    _ = _ := by
      rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
      congr 2
      omega

private lemma eventually_large_dyadic_counts (d e : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ M : ℕ,
      2 ^ j ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1)) → 2 * (2 * (j + 1)) ^ e ≤ M := by
  filter_upwards [eventually_dyadic_pruning_budget (4 * e + 2 * (d + 1)),
    eventually_ge_atTop 1] with j h hj M hM
  let r := j + 1
  have hq : (2 * r) ^ e ≤ r ^ (2 * e) := by
    rw [pow_mul]
    apply Nat.pow_le_pow_left
    calc
      2 * r ≤ r * r := Nat.mul_le_mul_right _ (by dsimp [r]; omega)
      _ = _ := (pow_two _).symm
  have hs : (2 * (2 * r) ^ e) ^ 2 * r ^ (2 * (d + 1)) ≤ 2 ^ j := by
    calc
      _ ≤ (2 * r ^ (2 * e)) ^ 2 * r ^ (2 * (d + 1)) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hq) 2)
      _ = 4 * r ^ (4 * e + 2 * (d + 1)) := by
        rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega
      _ ≤ 4 * (2 ^ (j / 3)) ^ 2 * r ^ (4 * e + 2 * (d + 1)) := by
        have hpos : 1 ≤ (2 ^ (j / 3) : ℕ) ^ 2 := Nat.one_le_pow _ _ (by positivity)
        calc
          _ = 4 * 1 * r ^ (4 * e + 2 * (d + 1)) := by simp
          _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpos)
      _ ≤ 2 ^ j := h
  have hle : (2 * (2 * r) ^ e) ^ 2 * r ^ (2 * (d + 1)) ≤ M ^ 2 * r ^ (2 * (d + 1)) :=
    hs.trans hM
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    (Nat.le_of_mul_le_mul_right hle (by dsimp [r]; positivity))

/-- Localize a common host to any finite collection of requested scales. -/
private lemma cluster_packing_on_scales (d : ℕ) :
    ∃ J₀ : ℕ, ∀ (I : Finset ℕ) (S : Finset ℕ), IsSidon (S : Set ℕ) →
      (∀ j ∈ I, J₀ ≤ j) →
      (∀ j ∈ I, ∃ t : ℕ,
        2 ^ j ≤ (S.filter fun x ↦ t ≤ x ∧ x < t + 2 ^ j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) →
      ∃ B : ℕ → Finset ℕ,
        (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
        (∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∀ u ∈ B j, ∀ v ∈ B j,
          a + b = u + v → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
        (∀ j ∈ I, 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 4 + 1))) ∧
        ∀ i j, i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
          b < a → v < u → a - b ≠ u - v := by
  classical
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_large_dyadic_counts d 2)
  refine ⟨max 1 K, fun I S hsid hmin hS ↦ ?_⟩
  choose center hcenter using hS
  let t (j : ℕ) := if hj : j ∈ I then center j hj else 0
  let A (j : ℕ) := if j ∈ I then S.filter (fun x ↦ t j ≤ x ∧ x < t j + 2 ^ j) else ∅
  obtain ⟨T, hT, hcard, hdisj⟩ := disjoint_cluster_allocation I A
  have hloc j x (hx : x ∈ T j) : x ∈ S ∧ t j ≤ x ∧ x < t j + 2 ^ j := by
    have hm := hT j hx
    by_cases hj : j ∈ I
    · exact Finset.mem_filter.mp (by simpa only [A, if_pos hj] using hm)
    · simp [A, hj] at hm
  let f (j x : ℕ) := x - t j + 2 ^ j
  let B (j : ℕ) := (T j).image (f j)
  have hBcard j : (B j).card = (T j).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy he
    have hx' := (hloc j x hx).2.1
    have hy' := (hloc j y hy).2.1
    dsimp [f] at he
    omega
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := (hloc j y hy).2
    apply Finset.mem_Ico.mpr
    rw [pow_succ]
    dsimp [f]
    omega
  · intro j x hx y hy z hz w hw he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨haS, haL, _⟩ := hloc j a ha
    obtain ⟨hbS, hbL, _⟩ := hloc j b hb
    obtain ⟨huS, huL, _⟩ := hloc j u hu
    obtain ⟨hvS, hvL, _⟩ := hloc j v hv
    have he' : a + b = u + v := by dsimp [f] at he; omega
    rcases hsid a haS u huS b hbS v hvS he' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  · intro j hji
    have hj := hmin j hji
    have hcount : 2 ^ j ≤ (A j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) := by
      simpa only [A, if_pos hji, t, dif_pos hji] using hcenter j hji
    have hjK : K ≤ j := (le_max_right _ _).trans hj
    have hj₁ : 1 ≤ j := (le_max_left _ _).trans hj
    let D := (j + 1) * (j + 2)
    have hD : 0 < D := by dsimp [D]; positivity
    have hD₂ : D ≤ (2 * (j + 1)) ^ 2 := by
      dsimp [D]
      rw [pow_two]
      exact Nat.mul_le_mul (by omega) (by omega)
    have hsize : 2 * D ≤ (A j).card :=
      (Nat.mul_le_mul_left _ hD₂).trans (hK j hjK _ hcount)
    have hc := hcard j hji
    change (T j).card = (A j).card / D at hc
    have hq : 1 ≤ (T j).card := by
      rw [hc, Nat.le_div_iff_mul_le hD, one_mul]
      omega
    have hfloor := (Nat.lt_div_mul_add (a := (A j).card) hD).le
    rw [← hc] at hfloor
    have hfactor : 2 * D ≤ (j + 1) ^ 4 := by
      have hj₂ : 2 ≤ j + 1 := by omega
      calc
        _ ≤ (j + 1) * (j + 1) * (2 * 2) := by
          dsimp [D]
          calc
            _ ≤ 2 * ((j + 1) * (2 * (j + 1))) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
            _ = _ := by ring
        _ ≤ (j + 1) * (j + 1) * ((j + 1) * (j + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hj₂ hj₂)
        _ = _ := by ring
    rw [hBcard]
    refine dyadic_energy_count_transfer j d 4 _ _ hcount ?_
    calc
      _ ≤ (T j).card * D + D := hfloor
      _ ≤ (T j).card * D + (T j).card * D := Nat.add_le_add_left
        (by simpa only [one_mul] using Nat.mul_le_mul_right D hq) _
      _ = (T j).card * (2 * D) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hfactor
  · intro i j hij x hx y hy z hz w hw hba hvu he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨haS, haL, _⟩ := hloc i a ha
    obtain ⟨hbS, hbL, _⟩ := hloc i b hb
    obtain ⟨huS, huL, _⟩ := hloc j u hu
    obtain ⟨hvS, hvL, _⟩ := hloc j v hv
    dsimp [f] at hba hvu he
    obtain ⟨rfl, _⟩ := sidon_positive_difference_unique S hsid haS hbS huS hvS
      (by omega) (by omega) (by omega)
    exact Finset.disjoint_left.mp (hdisj i j hij.ne) ha hu


private lemma nearby_of_sidon_cluster_profile (h : SidonClusterProfile) : H1 := by
  obtain ⟨d, J, hS⟩ := h
  obtain ⟨J₀, hpack⟩ := cluster_packing_on_scales d
  refine ⟨d + 4, max J J₀, fun N ↦ ?_⟩
  obtain ⟨S, hsid, hcl⟩ := hS N
  let I := Finset.Icc (max J J₀) N
  obtain ⟨B, hpos, hBsid, hc, hsep⟩ := hpack I S hsid
    (fun j hj ↦ (le_max_right _ _).trans (Finset.mem_Icc.mp hj).1)
    (fun j hj ↦ hcl j ((le_max_left _ _).trans (Finset.mem_Icc.mp hj).1) (Finset.mem_Icc.mp hj).2)
  exact ⟨B, hpos, hBsid, fun j hj hjN ↦ hc j (Finset.mem_Icc.mpr ⟨hj, hjN⟩),
    fun i j _ hij ↦ hsep i j hij⟩

private lemma pair_of_sum_and_squares {a b u v : ℕ} (hs : a + b = u + v)
    (hq : a ^ 2 + b ^ 2 = u ^ 2 + v ^ 2) :
    (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  have hp : a * b = u * v := by
    nlinarith only [hq, congrArg (· ^ 2) hs]
  have hsi : (a : ℤ) + b = (u : ℤ) + v := by exact_mod_cast hs
  have hpi : (a : ℤ) * b = (u : ℤ) * v := by exact_mod_cast hp
  have hfact : ((a : ℤ) - u) * ((a : ℤ) - v) = 0 := by
    nlinarith only [hpi, congrArg ((a : ℤ) * ·) hsi]
  rcases mul_eq_zero.mp hfact with h | h
  · left
    have : a = u := by omega
    exact ⟨this, by omega⟩
  · right
    have : a = v := by omega
    exact ⟨this, by omega⟩

private def clusterTag (N j : ℕ) : ℕ := j + (2 * N + 1) * j ^ 2

private lemma clusterTag_sum {N i j k l : ℕ} (hi : i ≤ N) (hj : j ≤ N)
    (hk : k ≤ N) (hl : l ≤ N)
    (he : clusterTag N i + clusterTag N j = clusterTag N k + clusterTag N l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  let R := 2 * N + 1
  have hsplit (a b : ℕ) :
      clusterTag N a + clusterTag N b = (a + b) + R * (a ^ 2 + b ^ 2) := by
    dsimp [clusterTag, R]
    ring
  rw [hsplit, hsplit] at he
  have h₁ : i + j < R := by dsimp [R]; omega
  have h₂ : k + l < R := by dsimp [R]; omega
  have hs := congrArg (· % R) he
  have hq := congrArg (· / R) he
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hs
  have hR : 0 < R := by dsimp [R]; positivity
  rw [Nat.add_mul_div_left _ _ hR, Nat.add_mul_div_left _ _ hR,
    Nat.div_eq_of_lt h₁, Nat.div_eq_of_lt h₂, zero_add, zero_add] at hq
  exact pair_of_sum_and_squares hs hq

private def clusterCapacity (N : ℕ) : ℕ := 2 ^ (N + 2) * (clusterTag N N + 1)

private lemma clusterCapacity_ge (N : ℕ) : 2 ^ (N + 2) ≤ clusterCapacity N := by
  unfold clusterCapacity
  simpa only [mul_one] using Nat.mul_le_mul_left (2 ^ (N + 2)) (show 1 ≤ clusterTag N N + 1 by omega)

private lemma clusterTag_mono (N : ℕ) : Monotone (clusterTag N) :=
  fun _ _ h ↦ Nat.add_le_add h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2))

private def hostEncoding (N j x : ℕ) : ℕ := x + 2 ^ (N + 2) * clusterTag N j

private def translatedHost (N : ℕ) (C : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).biUnion fun j ↦ (C j).image (hostEncoding N j)

private lemma host_encoding_lt_capacity (N j a : ℕ) (hj : j ≤ N)
    (ha : a < 2 ^ (N + 2)) : hostEncoding N j a < clusterCapacity N := by
  unfold hostEncoding clusterCapacity
  rw [Nat.mul_succ]
  have htag := Nat.mul_le_mul_left (2 ^ (N + 2)) (clusterTag_mono N hj)
  omega

/-- Translate and assemble a finite family with pairwise disjoint positive differences. -/
private lemma translated_host_of_separated_blocks (N : ℕ) (C : ℕ → Finset ℕ)
    (hpos : ∀ j, C j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hCsid : ∀ j, IsSidon (C j : Set ℕ))
    (hsep : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
      b < a → v < u → a - b ≠ u - v) :
    translatedHost N C ⊆ Finset.range (clusterCapacity N) ∧
      IsSidon (translatedHost N C : Set ℕ) := by
  have hp (r s x : ℕ) (hx : x ∈ C r) (hy : x ∈ C s) : r = s := by
    have hlog t (ht : x ∈ C t) : Nat.log 2 x = t := by
      obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp (hpos t ht)
      exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
    exact (hlog r hx).symm.trans (hlog s hy)
  let M : ℕ := 2 ^ (N + 2)
  let E (j x : ℕ) := hostEncoding N j x
  let S := translatedHost N C
  have hmem {x : ℕ} (hx : x ∈ S) : ∃ j ≤ N, ∃ a ∈ C j, E j a = x := by
    obtain ⟨j, hj, hx'⟩ := Finset.mem_biUnion.mp hx
    exact ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), Finset.mem_image.mp hx'⟩
  have hbound {j x : ℕ} (hj : j ≤ N) (hx : x ∈ C j) :
      x < 2 ^ (N + 1) :=
    (Finset.mem_Ico.mp (hpos j hx)).2.trans_le
      (pow_le_pow_right₀ (by decide) (by omega))
  have hHalf : (2 : ℕ) ^ (N + 1) ≤ M := pow_le_pow_right₀ (by decide) (by omega)
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, a, ha, rfl⟩ := hmem hx
    exact Finset.mem_range.mpr (host_encoding_lt_capacity N j a hj ((hbound hj ha).trans_le hHalf))
  · intro x hx y hy z hz w hw h
    obtain ⟨i, hi, a, ha, rfl⟩ := hmem hx
    obtain ⟨j, hj, b, hb, rfl⟩ := hmem hz
    obtain ⟨k, hk, u, hu, rfl⟩ := hmem hy
    obtain ⟨l, hl, v, hv, rfl⟩ := hmem hw
    have hsplit (r s m n : ℕ) :
        E r m + E s n = (m + n) + M * (clusterTag N r + clusterTag N s) := by
      dsimp [E, hostEncoding, M]
      ring
    rw [hsplit, hsplit] at h
    have hlt₁ : a + b < M := by
      have := hbound hi ha
      have := hbound hj hb
      dsimp [M]
      rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
      omega
    have hlt₂ : u + v < M := by
      have := hbound hk hu
      have := hbound hl hv
      dsimp [M]
      rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
      omega
    have hadd := congrArg (· % M) h
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] at hadd
    have hlabels := congrArg (· / M) h
    have hM : 0 < M := by dsimp [M]; positivity
    rw [Nat.add_mul_div_left _ _ hM, Nat.add_mul_div_left _ _ hM,
      Nat.div_eq_of_lt hlt₁, Nat.div_eq_of_lt hlt₂, zero_add, zero_add] at hlabels
    rcases clusterTag_sum hi hj hk hl hlabels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases two_block_core C hCsid hsep ha hb hu hv hadd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · by_cases hij : i = j
        · subst j
          exact Or.inr ⟨rfl,rfl⟩
        · exact (hij (hp i j _ ha hv)).elim
    · rcases two_block_core C hCsid hsep ha hb hv hu (by omega) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,rfl⟩
      · by_cases hij : i = j
        · subst j
          exact Or.inl ⟨rfl,rfl⟩
        · exact (hij (hp i j _ ha hu)).elim
/-- For a fixed horizon, constant translations with separated pair-sum tags
assemble the pruned blocks into a common ambient Sidon set. -/
private lemma bounded_sidon_cluster_profile_of_nearby (h : H1) :
    ∃ d J : ℕ, ∀ N : ℕ, ∃ S : Finset ℕ, S ⊆ Finset.range (clusterCapacity N) ∧ IsSidon (S : Set ℕ) ∧
      ∀ j, J ≤ j → j ≤ N → ∃ t < clusterCapacity N,
        2 ^ j ≤ (S.filter fun x ↦ t ≤ x ∧ x < t + 2 ^ j).card ^ 2 * (j + 1) ^ (2 * (d + 1)) := by
  obtain ⟨d, J, hB⟩ := h
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_dyadic_pruning_preserves_count d)
  refine ⟨d + 1, max J K, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hsid, hdense, hnear⟩ := hB N
  have hBsid j : IsSidon (B j : Set ℕ) := fun a ha u hu b hb v hv hs ↦ hsid j a ha b hb u hu v hv hs
  obtain ⟨C, hC, hsep⟩ := prune_distant_dyadic_collisions B hpos hBsid hnear
  have hCsid j : IsSidon (C j : Set ℕ) :=
    fun a ha u hu b hb v hv hs ↦ hBsid j a ((hC j).1 ha) u ((hC j).1 hu)
      b ((hC j).1 hb) v ((hC j).1 hv) hs
  let M : ℕ := 2 ^ (N + 2)
  let E (j x : ℕ) := hostEncoding N j x
  let S := translatedHost N C
  obtain ⟨hSpos, hSsid⟩ := translated_host_of_separated_blocks N C
    (fun j ↦ (hC j).1.trans (hpos j)) hCsid hsep
  refine ⟨S, hSpos, hSsid, ?_⟩
  intro j hj hjN
  let t := M * clusterTag N j + 2 ^ j
  have ht : t < clusterCapacity N := by
    have hpow : (2 : ℕ) ^ j < M :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
    simpa only [t, E, hostEncoding, M, Nat.add_comm] using host_encoding_lt_capacity N j (2 ^ j) hjN hpow
  refine ⟨t, ht, ?_⟩
  have hs : (C j).image (E j) ⊆ S.filter (fun x ↦ t ≤ x ∧ x < t + 2 ^ j) := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), hx⟩, ?_⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp (hpos j ((hC j).1 ha))
    rw [pow_succ] at hhi
    dsimp [t, E, M, hostEncoding]
    omega
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective] at hc
  swap
  · exact fun a b he ↦ Nat.add_right_cancel he
  exact (hK j ((le_max_right _ _).trans hj) _ _
    (hdense j ((le_max_left _ _).trans hj) hjN) (hC j).2).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc 2))

private lemma sidon_cluster_profile_of_nearby (h : H1) : SidonClusterProfile := by
  obtain ⟨d, J, hS⟩ := bounded_sidon_cluster_profile_of_nearby h
  refine ⟨d, J, fun N ↦ ?_⟩
  obtain ⟨S, _, hs, hclusters⟩ := hS N
  exact ⟨S, hs, fun j hj hjN ↦ by
    obtain ⟨t, _, ht⟩ := hclusters j hj hjN
    exact ⟨t, ht⟩⟩

private lemma nearby_iff_sidon_cluster_profile : H1 ↔ SidonClusterProfile :=
  ⟨sidon_cluster_profile_of_nearby, nearby_of_sidon_cluster_profile⟩

/-- Residues in an arc beginning at `t`. The second clause is the part across zero. -/
private def cyclicCluster (q t width : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter fun x ↦ (t ≤ x ∧ x < t + width) ∨ x < t + width - q

/-- One prime cycle with locally dense Sidon arcs suffices at each horizon. -/
private def PrimeCyclicSidonProfile : Prop :=
  ∃ d J : ℕ, ∀ N : ℕ, ∃ (q : ℕ) (S : Finset ℕ),
    Nat.Prime q ∧ 2 ^ N < q ∧ q ≤ 4 * clusterCapacity N ∧ S ⊆ Finset.range q ∧
    (∀ a ∈ S, ∀ b ∈ S, ∀ u ∈ S, ∀ v ∈ S, (a + b) % q = (u + v) % q →
      (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
    ∀ j, J ≤ j → j ≤ N → ∃ t < q,
      2 ^ j ≤ (cyclicCluster q t (2 ^ j) S).card ^ 2 * (j + 1) ^ (2 * (d + 1))

private lemma prime_cyclic_sidon_profile_of_nearby (h : H1) : PrimeCyclicSidonProfile := by
  obtain ⟨d, J, hS⟩ := bounded_sidon_cluster_profile_of_nearby h
  refine ⟨d, J, fun N ↦ ?_⟩
  obtain ⟨S, hsub, hsid, hclusters⟩ := hS N
  let P := clusterCapacity N
  have hP : 0 < P := (by positivity : 0 < (2 : ℕ) ^ (N + 2)).trans_le (clusterCapacity_ge N)
  obtain ⟨q, hq, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * P) (by omega)
  have hN : (2 : ℕ) ^ N < P :=
    ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega : N < N + 2)).trans_le
      (clusterCapacity_ge N)
  refine ⟨q, S, hq, by omega, by omega, ?_, ?_, ?_⟩
  · intro x hx
    apply Finset.mem_range.mpr
    have hx' := Finset.mem_range.mp (hsub hx)
    omega
  · intro a ha b hb u hu v hv he
    have ha' := Finset.mem_range.mp (hsub ha)
    have hb' := Finset.mem_range.mp (hsub hb)
    have hu' := Finset.mem_range.mp (hsub hu)
    have hv' := Finset.mem_range.mp (hsub hv)
    rw [Nat.mod_eq_of_lt (by omega : a + b < q), Nat.mod_eq_of_lt (by omega : u + v < q)] at he
    exact hsid a ha u hu b hb v hv he
  · intro j hj hjN
    obtain ⟨t, ht, hc⟩ := hclusters j hj hjN
    refine ⟨t, by omega, hc.trans ?_⟩
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_left
    apply Finset.card_le_card
    exact fun x hx ↦ Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, Or.inl (Finset.mem_filter.mp hx).2⟩

/-- Cutting a cyclic cluster at zero yields an ordinary interval of the same width
containing at least half its points. -/
private lemma linear_cluster_of_cyclic (q t w : ℕ) (S : Finset ℕ) (ht : t < q) :
    ∃ u : ℕ, (cyclicCluster q t w S).card ≤
      2 * (S.filter fun x ↦ u ≤ x ∧ x < u + w).card := by
  classical
  let A := S.filter (fun x ↦ t ≤ x ∧ x < t + w)
  let B := S.filter (fun x ↦ x < t + w - q)
  let C := S.filter (fun x ↦ 0 ≤ x ∧ x < 0 + w)
  have hBC : B ⊆ C := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, Nat.zero_le _, by omega⟩
  have hsum : (cyclicCluster q t w S).card ≤ A.card + C.card := by
    rw [cyclicCluster, Finset.filter_or]
    exact (Finset.card_union_le A B).trans (Nat.add_le_add_left (Finset.card_le_card hBC) _)
  by_cases hAC : A.card ≤ C.card
  · exact ⟨0, hsum.trans (by omega : A.card + C.card ≤ 2 * C.card)⟩
  · exact ⟨t, hsum.trans (by omega : A.card + C.card ≤ 2 * A.card)⟩

private lemma sidon_cluster_profile_of_prime_cyclic (h : PrimeCyclicSidonProfile) : SidonClusterProfile := by
  obtain ⟨d, J, hS⟩ := h
  refine ⟨d + 1, max 1 J, fun N ↦ ?_⟩
  obtain ⟨q, S, _, _, _, _, hsid, hclusters⟩ := hS N
  refine ⟨S, ?_, ?_⟩
  · exact fun a ha u hu b hb v hv he ↦ hsid a ha b hb u hu v hv (congrArg (· % q) he)
  intro j hj hjN
  obtain ⟨t, ht, ho⟩ := hclusters j ((le_max_right _ _).trans hj) hjN
  obtain ⟨u, hU⟩ := linear_cluster_of_cyclic q t (2 ^ j) S ht
  refine ⟨u, dyadic_energy_count_transfer j d 1 _ _ ho ?_⟩
  rw [pow_one]
  have hj₁ := (le_max_left 1 J).trans hj
  refine hU.trans ?_
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

private lemma nearby_iff_prime_cyclic_sidon_profile : H1 ↔ PrimeCyclicSidonProfile :=
  ⟨prime_cyclic_sidon_profile_of_nearby, fun h ↦
    nearby_of_sidon_cluster_profile (sidon_cluster_profile_of_prime_cyclic h)⟩

private lemma eventually_checkpoint_index_close (e : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ s ≥ j, 2 ^ (s - j) ≤ (j + 1) ^ e → s ≤ j + j / 2 := by
  obtain ⟨K, hK⟩ := eventually_log_shift (2 * e) 0
  refine (eventually_ge_atTop K).mono fun j hj s hjs hgap ↦ ?_
  let L := Nat.log 2 (j + 2) + 1
  have hL : j + 1 ≤ 2 ^ L :=
    (Nat.le_succ _).trans (Nat.lt_pow_succ_log_self (by decide) _).le
  have hg : s - j ≤ L * e := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hgap.trans (by rw [pow_mul]; exact Nat.pow_le_pow_left hL _))
  have hs := hK j hj
  change 0 + 2 * e * L ≤ j at hs
  have hsize : 2 * (L * e) ≤ j := by simpa only [zero_add, mul_assoc, mul_comm e L] using hs
  omega

/-- From a cluster at a larger dyadic width, retain the largest of its equal pieces. -/
private lemma localize_cluster (S : Finset ℕ) (t j s : ℕ) (hjs : j ≤ s) :
    ∃ u : ℕ,
      (S.filter fun x ↦ t ≤ x ∧ x < t + 2 ^ s).card ≤
        2 ^ (s - j) * (S.filter fun x ↦ u ≤ x ∧ x < u + 2 ^ j).card := by
  let Q : ℕ := 2 ^ j
  let L : ℕ := 2 ^ (s - j)
  let A := S.filter (fun x ↦ t ≤ x ∧ x < t + 2 ^ s)
  let f (x : ℕ) := (x - t) / Q
  let fiber (k : ℕ) := A.filter (fun x ↦ f x = k)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hpow : L * Q = 2 ^ s := by
    dsimp [L, Q]
    rw [← pow_add, Nat.sub_add_cancel hjs]
  have hmap : Set.MapsTo f (A : Set ℕ) (Finset.range L : Set ℕ) := by
    intro x hx
    have hb := (Finset.mem_filter.mp hx).2
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hQ).mpr
    rw [hpow]
    omega
  obtain ⟨k, _, hmax⟩ := Finset.exists_max_image (Finset.range L) (fun k ↦ (fiber k).card)
    ⟨0, Finset.mem_range.mpr hL⟩
  let u := t + k * Q
  refine ⟨u, ?_⟩
  have hsub : fiber k ⊆ S.filter (fun x ↦ u ≤ x ∧ x < u + 2 ^ j) := by
    intro x hx
    obtain ⟨hxA, hxf⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxS, hxt, _⟩ := Finset.mem_filter.mp hxA
    have hlo := Nat.div_mul_le_self (x - t) Q
    have hhi := Nat.lt_div_mul_add (a := x - t) hQ
    change (x - t) / Q = k at hxf
    rw [hxf] at hlo hhi
    apply Finset.mem_filter.mpr
    refine ⟨hxS, ?_⟩
    dsimp [u]
    change t + k * Q ≤ x ∧ x < t + k * Q + Q
    omega
  change A.card ≤ L * _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ _ ∈ Finset.range L, (fiber k).card :=
      Finset.sum_le_sum (fun i hi ↦ hmax i hi)
    _ = L * (fiber k).card := by simp
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)

/-- The occupied arc widths can be chosen after the Sidon set, with a polynomial
ratio to any required width. The witness prime may be arbitrarily large. -/
private def AdaptiveCyclicSidonProfile : Prop :=
  ∃ d e J : ℕ, ∀ N : ℕ, ∃ (q : ℕ) (S : Finset ℕ),
    Nat.Prime q ∧ S ⊆ Finset.range q ∧
    (∀ a ∈ S, ∀ b ∈ S, ∀ u ∈ S, ∀ v ∈ S, (a + b) % q = (u + v) % q →
      (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
    ∀ j, J ≤ j → j ≤ N → ∃ s ≥ j, 2 ^ (s - j) ≤ (j + 1) ^ e ∧ 2 ^ s ≤ q ∧ ∃ t < q,
      2 ^ s ≤ (cyclicCluster q t (2 ^ s) S).card ^ 2 * (s + 1) ^ (2 * (d + 1))

private lemma adaptive_cyclic_sidon_profile_of_prime_cyclic (h : PrimeCyclicSidonProfile) :
    AdaptiveCyclicSidonProfile := by
  obtain ⟨d, J, hS⟩ := h
  refine ⟨d, 0, J, fun N ↦ ?_⟩
  obtain ⟨q, S, hq, hqN, _, hsub, hsid, hcl⟩ := hS N
  refine ⟨q, S, hq, hsub, hsid, fun j hj hjN ↦ ⟨j, le_rfl, by simp, ?_, hcl j hj hjN⟩⟩
  exact (pow_le_pow_right₀ (by decide) hjN).trans hqN.le

private lemma sidon_cluster_profile_of_adaptive_cyclic (h : AdaptiveCyclicSidonProfile) :
    SidonClusterProfile := by
  obtain ⟨d, e, J, hS⟩ := h
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_checkpoint_index_close e)
  let J₀ := max 1 (max J K)
  let D := 2 * d + 1
  refine ⟨D + (e + 1), J₀, fun N ↦ ?_⟩
  obtain ⟨q, S, _, _, hsid, hcl⟩ := hS N
  refine ⟨S, ?_, ?_⟩
  · exact fun a ha u hu b hb v hv he ↦ hsid a ha b hb u hu v hv (congrArg (· % q) he)
  intro j hj hjN
  have hjJ : J ≤ j := (le_max_left _ _).trans ((le_max_right _ _).trans hj)
  have hjK : K ≤ j := (le_max_right _ _).trans ((le_max_right _ _).trans hj)
  have hj₁ : 1 ≤ j := (le_max_left _ _).trans hj
  obtain ⟨s, hjs, hgap, _, t, ht, hC⟩ := hcl j hjJ hjN
  obtain ⟨u, hU⟩ := linear_cluster_of_cyclic q t (2 ^ s) S ht
  obtain ⟨v, hV⟩ := localize_cluster S u j s hjs
  let A := cyclicCluster q t (2 ^ s) S
  let B := S.filter (fun x ↦ v ≤ x ∧ x < v + 2 ^ j)
  have hs := hK j hjK s hjs hgap
  have hj₂ : 2 ≤ j + 1 := by omega
  have hscale : s + 1 ≤ (j + 1) ^ 2 := by
    rw [pow_two]
    exact (show s + 1 ≤ 2 * (j + 1) by omega).trans (Nat.mul_le_mul_right _ hj₂)
  have hcount : 2 ^ j ≤ A.card ^ 2 * (j + 1) ^ (2 * (D + 1)) :=
    calc
      _ ≤ 2 ^ s := pow_le_pow_right₀ (by decide) hjs
      _ ≤ A.card ^ 2 * (s + 1) ^ (2 * (d + 1)) := hC
      _ ≤ A.card ^ 2 * ((j + 1) ^ 2) ^ (2 * (d + 1)) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hscale _)
      _ = _ := by rw [← pow_mul]; congr 2
  refine ⟨v, dyadic_energy_count_transfer j D (e + 1) _ _ hcount ?_⟩
  calc
    A.card ≤ 2 * (S.filter fun x ↦ u ≤ x ∧ x < u + 2 ^ s).card := hU
    _ ≤ 2 * (2 ^ (s - j) * B.card) := Nat.mul_le_mul_left _ hV
    _ ≤ (j + 1) * ((j + 1) ^ e * B.card) :=
      Nat.mul_le_mul hj₂ (Nat.mul_le_mul_right _ hgap)
    _ = B.card * (j + 1) ^ (e + 1) := by rw [pow_succ]; ring

private lemma nearby_iff_adaptive_cyclic_sidon_profile : H1 ↔ AdaptiveCyclicSidonProfile :=
  ⟨fun h ↦ adaptive_cyclic_sidon_profile_of_prime_cyclic (prime_cyclic_sidon_profile_of_nearby h),
    fun h ↦ nearby_of_sidon_cluster_profile (sidon_cluster_profile_of_adaptive_cyclic h)⟩

/-- The quadratic residue construction gives a ruler of size `p` in a
range of length `2*p^2`. -/
private lemma quadratic_residue_sidon_with_gap (p : ℕ) (hp : p.Prime) (hp₂ : 2 < p) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (2 * p ^ 2) ∧ IsSidon (S : Set ℕ) ∧ S.card = p ∧
      ∀ a ∈ S, ∀ b ∈ S, b < a → p ≤ a - b := by
  let F := ZMod p
  let : Fact p.Prime := ⟨hp⟩
  let R := 2 * p
  let f (x : ℕ) := x ^ 2 % p + R * x
  let S := (Finset.range p).image f
  have hR : 0 < R := by dsimp [R]; omega
  have hrem (x : ℕ) : x ^ 2 % p < p := Nat.mod_lt _ hp.pos
  have hfdiv (x : ℕ) : f x / R = x := by
    unfold f
    rw [Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt (by have := hrem x; dsimp [R]; omega), zero_add]
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    have hx' := Finset.mem_range.mp hx
    have hb : R * (x + 1) ≤ 2 * p ^ 2 := by
      have hm := Nat.mul_le_mul_left R (show x + 1 ≤ p by omega)
      simpa only [R, mul_assoc, pow_two] using hm
    have hfx : f x < R * (x + 1) := by
      rw [Nat.mul_succ]
      have := hrem x
      dsimp [f]
      have : p ≤ R := by dsimp [R]; omega
      omega
    exact Finset.mem_range.mpr (hfx.trans_le hb)
  · intro a ha u hu b hb v hv he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    have hsplit (m n : ℕ) : f m + f n = (m ^ 2 % p + n ^ 2 % p) + R * (m + n) := by
      dsimp [f]
      ring
    rw [hsplit, hsplit] at he
    have hsmall (m n : ℕ) : m ^ 2 % p + n ^ 2 % p < R := by
      have := hrem m
      have := hrem n
      dsimp [R]
      omega
    have hs := congrArg (· / R) he
    rw [Nat.add_mul_div_left _ _ hR, Nat.add_mul_div_left _ _ hR,
      Nat.div_eq_of_lt (hsmall x y), Nat.div_eq_of_lt (hsmall z w), zero_add, zero_add] at hs
    have hq := congrArg (· % R) he
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hsmall x y), Nat.mod_eq_of_lt (hsmall z w)] at hq
    have hsF : (x : F) + y = (z : F) + w := by
      simpa only [Nat.cast_add] using congrArg (fun t : ℕ ↦ (t : ZMod p)) hs
    have hqF : (x : F) ^ 2 + (y : F) ^ 2 = (z : F) ^ 2 + (w : F) ^ 2 := by
      have hh := congrArg (fun t : ℕ ↦ (t : ZMod p)) hq
      simpa only [Nat.cast_add, ZMod.natCast_mod, Nat.cast_pow] using hh
    have htwo : (2 : F) ≠ 0 := by
      change ((2 : ℕ) : ZMod p) ≠ 0
      intro he
      have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp he
      exact hp₂.not_ge (Nat.le_of_dvd (by decide) hdvd)
    have hprod : (x : F) * y = (z : F) * w := by
      apply mul_left_cancel₀ htwo
      linear_combination (congrArg (· ^ 2) hsF) - hqF
    have hpairs : ((x : F) - z) * ((x : F) - w) = 0 := by
      linear_combination (x : F) * hsF - hprod
    have hinj {m n : ℕ} (hm : m ∈ Finset.range p) (hn : n ∈ Finset.range p)
        (heq : (m : F) = (n : F)) : m = n := by
      exact (Nat.mod_eq_of_lt (Finset.mem_range.mp hm)).symm.trans
        (((ZMod.natCast_eq_natCast_iff' m n p).mp heq).trans (Nat.mod_eq_of_lt (Finset.mem_range.mp hn)))
    rcases mul_eq_zero.mp hpairs with h | h
    · have h' := hinj hx hz (sub_eq_zero.mp h)
      have : y = w := by omega
      exact Or.inl ⟨congrArg f h', congrArg f this⟩
    · have h' := hinj hx hw (sub_eq_zero.mp h)
      have : y = z := by omega
      exact Or.inr ⟨congrArg f h', congrArg f this⟩
  · rw [Finset.card_image_of_injective, Finset.card_range]
    exact fun a b he ↦ (hfdiv a).symm.trans ((congrArg (· / R) he).trans (hfdiv b))

  · intro a ha b hb hlt
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    have hgap {m n : ℕ} (h : m < n) : f m + p ≤ f n := by
      have hm := Nat.mul_le_mul_left R (show m + 1 ≤ n by omega)
      rw [Nat.mul_succ] at hm
      have hR' : R = 2 * p := rfl
      have := hrem m
      dsimp [f]
      omega
    have hxy : y < x := by
      rcases lt_trichotomy y x with h | rfl | h
      · exact h
      · omega
      · have := hgap h
        omega
    have := hgap hxy
    omega

private lemma quadratic_residue_sidon (p : ℕ) (hp : p.Prime) (hp₂ : 2 < p) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (2 * p ^ 2) ∧ IsSidon (S : Set ℕ) ∧ S.card = p := by
  obtain ⟨S, hs, hsid, hcard, _⟩ := quadratic_residue_sidon_with_gap p hp hp₂
  exact ⟨S, hs, hsid, hcard⟩

/-- At a single sufficiently large scale a finite Sidon set attains the desired
count up to a constant. -/
private lemma exists_dense_sidon_range_with_gap (N : ℕ) (hN : 6 ≤ N) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (2 ^ N) ∧ IsSidon (S : Set ℕ) ∧
      2 ^ N ≤ 32 * S.card ^ 2 ∧ ∀ a ∈ S, ∀ b ∈ S, b < a → 2 ^ (N / 2 - 2) < a - b := by
  let k := N / 2 - 2
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hpow : 0 < (2 : ℕ) ^ k := by positivity
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ k) hpow.ne'
  have hp₂ : 2 < p :=
    (show (2 : ℕ) ^ 1 ≤ 2 ^ k from pow_le_pow_right₀ (by decide) hk).trans_lt hlo
  obtain ⟨S, hsub, hsid, hcard, hgap⟩ := quadratic_residue_sidon_with_gap p hp hp₂
  refine ⟨S, ?_, hsid, ?_, fun a ha b hb hba ↦ hlo.trans_le (hgap a ha b hb hba)⟩
  · have hfit : 2 * p ^ 2 ≤ 2 ^ N := calc
      _ ≤ 2 * (2 * 2 ^ k) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hhi _)
      _ = 2 ^ (1 + (k + 1) * 2) := by rw [pow_add, pow_mul, pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ (by decide) (by dsimp [k]; omega)
    exact fun x hx ↦ Finset.mem_range.mpr ((Finset.mem_range.mp (hsub hx)).trans_le hfit)
  · rw [hcard]
    calc
      _ ≤ 2 ^ (5 + k * 2) := pow_le_pow_right₀ (by decide) (by dsimp [k]; omega)
      _ = 32 * (2 ^ k) ^ 2 := by rw [pow_add, pow_mul]; rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlo.le _)

private lemma exists_dense_sidon_range (N : ℕ) (hN : 6 ≤ N) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (2 ^ N) ∧ IsSidon (S : Set ℕ) ∧
      2 ^ N ≤ 32 * S.card ^ 2 := by
  obtain ⟨S, hsub, hsid, hcard, _⟩ := exists_dense_sidon_range_with_gap N hN
  exact ⟨S, hsub, hsid, hcard⟩

private lemma dense_cluster_in_terminal_window (S : Finset ℕ) (N j : ℕ)
    (hsub : S ⊆ Finset.range (2 ^ N)) (hdense : 2 ^ N ≤ 32 * S.card ^ 2)
    (hj : 5 ≤ j) (hjN : j ≤ N) (hgap : 2 ^ (N - j) ≤ j + 1) :
    ∃ t : ℕ, 2 ^ j ≤ (S.filter fun x ↦ t ≤ x ∧ x < t + 2 ^ j).card ^ 2 * (j + 1) ^ 4 := by
  obtain ⟨t, ht⟩ := localize_cluster S 0 j N hjN
  have he : (S.filter fun x ↦ 0 ≤ x ∧ x < 0 + 2 ^ N) = S := by
    apply Finset.filter_eq_self.mpr
    exact fun x hx ↦ ⟨Nat.zero_le _, by simpa only [zero_add] using Finset.mem_range.mp (hsub hx)⟩
  rw [he] at ht
  have hpoly : 32 ≤ (j + 1) ^ 2 :=
    (show 32 ≤ (6 : ℕ) ^ 2 by decide).trans (Nat.pow_le_pow_left (by omega) 2)
  have hcount : 2 ^ j ≤ S.card ^ 2 * (j + 1) ^ (2 * (0 + 1)) := calc
    _ ≤ 2 ^ N := pow_le_pow_right₀ (by decide) hjN
    _ ≤ _ := hdense
    _ ≤ _ := by rw [mul_comm 32]; exact Nat.mul_le_mul_left _ hpoly
  refine ⟨t, dyadic_energy_count_transfer j 0 1 _ _ hcount ?_⟩
  rw [pow_one, mul_comm]
  exact ht.trans (Nat.mul_le_mul_right _ hgap)

/-- A common host is constructible at every width within a logarithmic distance
of the horizon. -/
private lemma sidon_cluster_profile_top_window (N : ℕ) (hN : 6 ≤ N) :
    ∃ S : Finset ℕ, IsSidon (S : Set ℕ) ∧
      ∀ j, 5 ≤ j → j ≤ N → 2 ^ (N - j) ≤ j + 1 → ∃ t : ℕ,
        2 ^ j ≤ (S.filter fun x ↦ t ≤ x ∧ x < t + 2 ^ j).card ^ 2 * (j + 1) ^ 4 := by
  obtain ⟨S, hsub, hsid, hdense⟩ := exists_dense_sidon_range N hN
  refine ⟨S, hsid, fun j hj hjN hgap ↦ ?_⟩
  exact dense_cluster_in_terminal_window S N j hsub hdense hj hjN hgap

/-- The original packing and separation conclusions hold simultaneously on a
logarithmic terminal window. -/
private lemma nearby_packing_top_window :
    ∃ J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∀ u ∈ B j, ∀ v ∈ B j,
        a + b = u + v → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
      (∀ j, J ≤ j → j ≤ N → 2 ^ (N - j) ≤ j + 1 →
        2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ 12) ∧
      ∀ i j, i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
        b < a → v < u → a - b ≠ u - v := by
  obtain ⟨J₀, hpack⟩ := cluster_packing_on_scales 1
  let J := max 6 J₀
  refine ⟨J, fun N ↦ ?_⟩
  by_cases hN : 6 ≤ N
  · obtain ⟨S, hsid, hcl⟩ := sidon_cluster_profile_top_window N hN
    let I := (Finset.Icc J N).filter (fun j ↦ 2 ^ (N - j) ≤ j + 1)
    obtain ⟨B, hpos, hBsid, hc, hBsep⟩ := hpack I S hsid
      (fun j hj ↦ (le_max_right _ _).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1)
      (fun j hj ↦ by
        obtain ⟨hj', hg⟩ := Finset.mem_filter.mp hj
        obtain ⟨hjo, hjN⟩ := Finset.mem_Icc.mp hj'
        have hj₆ : 6 ≤ j := (le_max_left _ _).trans hjo
        exact hcl j (by omega) hjN hg)
    exact ⟨B, hpos, hBsid, fun j hj hjN hg ↦
      hc j (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj, hjN⟩, hg⟩), hBsep⟩
  · refine ⟨fun _ ↦ ∅, fun _ ↦ Finset.empty_subset _, by simp, ?_, by simp⟩
    intro j hj hjN _
    have hj₆ : 6 ≤ j := (le_max_left _ _).trans hj
    omega

/-- Separated anchor scales can use independent quadratic rulers in one host.
The separation is on the exponents: the smaller scale must lie below half the
larger scale, up to the fixed gap in the ruler construction. -/
private lemma sidon_cluster_profile_separated_windows (N : ℕ) (I : Finset ℕ)
    (hI : ∀ n ∈ I, 6 ≤ n ∧ n ≤ N)
    (hsep : ∀ m ∈ I, ∀ n ∈ I, m < n → m ≤ n / 2 - 2) :
    ∃ S : Finset ℕ, IsSidon (S : Set ℕ) ∧
      ∀ n ∈ I, ∀ j, 5 ≤ j → j ≤ n → 2 ^ (n - j) ≤ j + 1 → ∃ t : ℕ,
        2 ^ j ≤ (S.filter fun x ↦ t ≤ x ∧ x < t + 2 ^ j).card ^ 2 * (j + 1) ^ 4 := by
  classical
  have hex n (hn : n ∈ I) := exists_dense_sidon_range_with_gap n (hI n hn).1
  choose R hRpos hRsid hRsize hRgap using hex
  let C (n : ℕ) := if hn : n ∈ I then (R n hn).image (· + 2 ^ n) else ∅
  have hpos n : C n ⊆ Finset.Ico (2 ^ n) (2 ^ (n + 1)) := by
    by_cases hn : n ∈ I
    · intro a ha
      rw [show C n = _ by exact dif_pos hn] at ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      have h := Finset.mem_range.mp (hRpos n hn hx)
      apply Finset.mem_Ico.mpr
      rw [pow_succ]
      omega
    · simp [C, hn]
  have hsid n : IsSidon (C n : Set ℕ) := by
    by_cases hn : n ∈ I
    · intro a ha u hu b hb v hv he
      simp only [C, dif_pos hn, Finset.mem_coe] at ha hu hb hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      rcases hRsid n hn x hx z hz y hy w hw (by omega) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,rfl⟩
    · simp [C, hn, IsSidon]
  have hlarge n {a b : ℕ} (ha : a ∈ C n) (hb : b ∈ C n) (hba : b < a) :
      2 ^ (n / 2 - 2) < a - b := by
    by_cases hn : n ∈ I
    · simp only [C, dif_pos hn] at ha hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      have h := hRgap n hn x hx y hy (by omega)
      omega
    · simp [C, hn] at ha
  have hcross m n (hmn : m < n) a (ha : a ∈ C m) b (hb : b ∈ C m)
      u (hu : u ∈ C n) v (hv : v ∈ C n) (hab : b < a) (hvu : v < u) :
      a - b ≠ u - v := by
    have hm : m ∈ I := by by_contra h; simp [C, h] at ha
    have hn : n ∈ I := by by_contra h; simp [C, h] at hu
    have hsmall : a - b < 2 ^ m := by
      have h₁ := (Finset.mem_Ico.mp (hpos m ha)).2
      have h₂ := (Finset.mem_Ico.mp (hpos m hb)).1
      rw [pow_succ] at h₁
      omega
    have hcap : (2 : ℕ) ^ m ≤ 2 ^ (n / 2 - 2) :=
      pow_le_pow_right₀ (by decide) (hsep m hm n hn hmn)
    exact (hsmall.trans (hcap.trans_lt (hlarge n hu hv hvu))).ne
  let S := translatedHost N C
  refine ⟨S, (translated_host_of_separated_blocks N C hpos hsid hcross).2, ?_⟩
  intro n hn j hj hjn hgap
  obtain ⟨t, ht⟩ := dense_cluster_in_terminal_window (R n hn) n j
    (hRpos n hn) (hRsize n hn) hj hjn hgap
  let shift := 2 ^ n + 2 ^ (N + 2) * clusterTag N n
  let T := (R n hn).filter (fun x ↦ t ≤ x ∧ x < t + 2 ^ j)
  refine ⟨t + shift, ht.trans ?_⟩
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_left
  calc
    _ = (T.image (· + shift)).card := by
      rw [Finset.card_image_of_injective]
      exact fun a b he ↦ Nat.add_right_cancel he
    _ ≤ _ := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨haR, haRange⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (by have := (hI n hn).2; omega), ?_⟩, ?_⟩
      · have haC : a + 2 ^ n ∈ C n := by
          rw [show C n = _ by exact dif_pos hn]
          exact Finset.mem_image_of_mem _ haR
        apply Finset.mem_image.mpr
        exact ⟨a + 2 ^ n, haC, by simp only [hostEncoding, shift, Nat.add_assoc]⟩
      · omega

/-- The packing conclusion is attainable on a family of separated logarithmic windows. -/
private lemma nearby_packing_separated_windows :
    ∃ J : ℕ, ∀ N : ℕ, ∀ I : Finset ℕ,
      (∀ n ∈ I, 6 ≤ n ∧ n ≤ N) →
      (∀ m ∈ I, ∀ n ∈ I, m < n → m ≤ n / 2 - 2) →
      ∃ B : ℕ → Finset ℕ,
        (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
        (∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∀ u ∈ B j, ∀ v ∈ B j,
          a + b = u + v → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
        (∀ n ∈ I, ∀ j, J ≤ j → j ≤ n → 2 ^ (n - j) ≤ j + 1 →
          2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ 12) ∧
        ∀ i j, i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
          b < a → v < u → a - b ≠ u - v := by
  classical
  obtain ⟨J₀, hpack⟩ := cluster_packing_on_scales 1
  let J := max 5 J₀
  refine ⟨J, fun N I hI hsep ↦ ?_⟩
  obtain ⟨S, hsid, hcl⟩ := sidon_cluster_profile_separated_windows N I hI hsep
  let W := (Finset.Icc J N).filter (fun j ↦ ∃ n ∈ I, j ≤ n ∧ 2 ^ (n - j) ≤ j + 1)
  obtain ⟨B, hpos, hBsid, hc, hBsep⟩ := hpack W S hsid
    (fun j hj ↦ (le_max_right _ _).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1)
    (fun j hj ↦ by
      obtain ⟨hj', n, hn, hjn, hg⟩ := Finset.mem_filter.mp hj
      have hj₅ : 5 ≤ j := (le_max_left _ _).trans (Finset.mem_Icc.mp hj').1
      exact hcl n hn j hj₅ hjn hg)
  refine ⟨B, hpos, hBsid, ?_, hBsep⟩
  intro n hn j hj hjn hg
  exact hc j (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj, hjn.trans (hI n hn).2⟩, n, hn, hjn, hg⟩)

/-- Compactness gives one sequence of dense rulers with disjoint positive
differences, even though the finite witnesses may change at every horizon. -/
private lemma nearby_iff_infinite_separated_packing :
    H1 ↔ ∃ d J : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, IsSidon (B j : Set ℕ)) ∧
      (∀ j, J ≤ j → 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧
      ∀ i j, i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
        b < a → v < u → a - b ≠ u - v := by
  classical
  constructor
  swap
  · rintro ⟨d, J, B, hpos, hsid, hcount, hsep⟩
    exact ⟨d, J, fun _ ↦ ⟨B, hpos,
      fun j a ha b hb u hu v hv he ↦ hsid j a ha u hu b hb v hv he,
      fun j hj _ ↦ hcount j hj, fun i j _ hij ↦ hsep i j hij⟩⟩
  intro h
  obtain ⟨d, J, hB⟩ := h
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_dyadic_pruning_preserves_count d)
  let L := max J K
  let D (j : ℕ) := Finset.Ico (2 ^ j) (2 ^ (j + 1))
  let cut (f : ℕ → Bool) (j : ℕ) := (D j).filter fun a ↦ f a = true
  let P (n : ℕ) (f : ℕ → Bool) : Prop :=
    (∀ j, 2 ^ (j + 1) ≤ n → IsSidon (cut f j : Set ℕ)) ∧
    (∀ j, L ≤ j → 2 ^ (j + 1) ≤ n →
      2 ^ j ≤ (cut f j).card ^ 2 * (j + 1) ^ (2 * (d + 2))) ∧
    ∀ i j, i < j → 2 ^ (j + 1) ≤ n →
      ∀ a ∈ cut f i, ∀ b ∈ cut f i, ∀ u ∈ cut f j, ∀ v ∈ cut f j,
        b < a → v < u → a - b ≠ u - v
  obtain ⟨f, hf⟩ : ∃ f, ∀ n, P n f := by
    apply compact_prefix_conditions P
    · intro n f g hagree hf
      have hc j (hj : 2 ^ (j + 1) ≤ n) : cut f j = cut g j := by
        ext a
        simp only [cut, Finset.mem_filter]
        by_cases ha : a ∈ D j
        · have han : a ≤ n := ((Finset.mem_Ico.mp ha).2.le).trans hj
          rw [hagree a han]
        · simp [ha]
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        rw [← hc j hj]
        exact (hf.1 j hj)
      · intro j hj hn
        rw [← hc j hn]
        exact hf.2.1 j hj hn
      · intro i j hij hj
        have hi : 2 ^ (i + 1) ≤ n :=
          (pow_le_pow_right₀ (by decide) (by omega)).trans hj
        rw [← hc i hi, ← hc j hj]
        exact hf.2.2 i j hij hj
    · intro N
      obtain ⟨B, hpos, hsid, hcount, hsep⟩ := hB N
      have hBs j : IsSidon (B j : Set ℕ) :=
        fun a ha u hu b hb v hv he ↦ hsid j a ha b hb u hu v hv he
      obtain ⟨C, hC, hCs⟩ := prune_distant_dyadic_collisions B hpos hBs hsep
      let U := (Finset.range (N + 1)).biUnion C
      let f (a : ℕ) : Bool := decide (a ∈ U)
      have hc j (hj : 2 ^ (j + 1) ≤ N) : cut f j = C j := by
        have hjN : j ≤ N := (show j ≤ j + 1 by omega).trans (Nat.lt_two_pow_self.le.trans hj)
        have hposC k : C k ⊆ D k := (hC k).1.trans (hpos k)
        ext a
        simp only [cut, Finset.mem_filter, f, decide_eq_true_eq, U, Finset.mem_biUnion]
        constructor
        · rintro ⟨haj, k, _, hak⟩
          have he : j = k := by
            have hlog l (ha : a ∈ D l) : Nat.log 2 a = l := by
              obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp ha
              exact le_antisymm (Nat.log_lt_of_lt_pow ((lt_of_lt_of_le (by positivity) hlo).ne') hhi |> Nat.le_of_lt_succ)
                (Nat.le_log_of_pow_le (by decide) hlo)
            exact (hlog j haj).symm.trans (hlog k (hposC k hak))
          simpa only [he] using hak
        · intro ha
          exact ⟨hposC j ha, j, Finset.mem_range.mpr (by omega), ha⟩
      refine ⟨f, fun n hn ↦ ⟨?_, ?_, ?_⟩⟩
      · intro j hj
        rw [hc j (hj.trans hn)]
        intro a ha u hu b hb v hv he
        exact hBs j a ((hC j).1 ha) u ((hC j).1 hu) b ((hC j).1 hb) v ((hC j).1 hv) he
      · intro j hj hjn
        rw [hc j (hjn.trans hn)]
        have hjN : j ≤ N := (show j ≤ j + 1 by omega).trans (Nat.lt_two_pow_self.le.trans (hjn.trans hn))
        exact hK j ((le_max_right _ _).trans hj) _ _
          (hcount j ((le_max_left _ _).trans hj) hjN) (hC j).2
      · intro i j hij hj
        have hi : 2 ^ (i + 1) ≤ n :=
          (pow_le_pow_right₀ (by decide) (by omega)).trans hj
        rw [hc i (hi.trans hn), hc j (hj.trans hn)]
        exact hCs i j hij
  refine ⟨d + 1, L, cut f, fun j ↦ Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · intro j
    exact (hf (2 ^ (j + 1))).1 j le_rfl
  · intro j hj
    exact (hf (2 ^ (j + 1))).2.1 j hj le_rfl
  · intro i j hij
    exact (hf (2 ^ (j + 1))).2.2 i j hij le_rfl

/-- An edge budget proportional to the vertex count allows thinning by only a
factor proportional to that budget ratio. Edges may be listed in either order. -/
private lemma thin_avoiding_pairs (S : Finset ℕ) (E : Finset (ℕ × ℕ)) (P : ℕ)
    (hloop : ∀ e ∈ E, e.1 ≠ e.2) (hE : E.card ≤ S.card * P) :
    ∃ T ⊆ S, S.card ≤ T.card * (2 * (4 * P + 1)) ∧
      ∀ e ∈ E, e.1 ∈ T → e.2 ∉ T := by
  classical
  let inc (a : ℕ) := E.filter fun e ↦ e.1 = a ∨ e.2 = a
  let deg (a : ℕ) := (inc a).card
  have hfiber (f : ℕ × ℕ → ℕ) :
      ∑ a ∈ S, (E.filter fun e ↦ f e = a).card ≤ E.card := by
    let E' := E.filter fun e ↦ f e ∈ S
    have hmap : Set.MapsTo f (E' : Set (ℕ × ℕ)) (S : Set ℕ) :=
      fun e he ↦ (Finset.mem_filter.mp he).2
    calc
      _ = ∑ a ∈ S, (E'.filter fun e ↦ f e = a).card := by
        apply Finset.sum_congr rfl
        intro a ha
        congr 1
        ext e
        simp only [E', Finset.mem_filter]
        constructor
        · rintro ⟨he, rfl⟩
          exact ⟨⟨he, ha⟩, rfl⟩
        · rintro ⟨⟨he, _⟩, h⟩
          exact ⟨he, h⟩
      _ = E'.card := (Finset.card_eq_sum_card_fiberwise hmap).symm
      _ ≤ E.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hsum : ∑ a ∈ S, deg a ≤ 2 * E.card := by
    calc
      _ ≤ ∑ a ∈ S, ((E.filter (fun e ↦ e.1 = a)).card +
          (E.filter (fun e ↦ e.2 = a)).card) := by
        apply Finset.sum_le_sum
        intro a _
        simp only [deg, inc, Finset.filter_or]
        exact Finset.card_union_le _ _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, two_mul]
        exact Nat.add_le_add (hfiber Prod.fst) (hfiber Prod.snd)
  let G := S.filter fun a ↦ deg a ≤ 4 * P
  let D := S.filter fun a ↦ 4 * P < deg a
  have hhalf : S.card ≤ 2 * G.card := by
    have hpartition : G.card + D.card = S.card := by
      simpa only [G, D, not_le] using
        (Finset.card_filter_add_card_filter_not (s := S) (p := fun a ↦ deg a ≤ 4 * P))
    have hdeg : D.card * (4 * P + 1) ≤ 2 * (S.card * P) := by
      calc
        _ = ∑ _ ∈ D, (4 * P + 1) := by simp
        _ ≤ ∑ a ∈ D, deg a :=
          Finset.sum_le_sum (fun a ha ↦ (Finset.mem_filter.mp ha).2)
        _ ≤ ∑ a ∈ S, deg a :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
        _ ≤ _ := hsum.trans (Nat.mul_le_mul_left _ hE)
    have hD : 2 * D.card ≤ S.card := by
      by_contra! hc
      have hm := Nat.mul_le_mul_right (2 * P) hc.le
      have hpos : 0 < D.card := by omega
      nlinarith only [hm, hdeg, hpos]
    omega
  let ok (T : Finset ℕ) := ∀ e ∈ E, e.1 ∈ T → e.2 ∉ T
  let candidates := G.powerset.filter ok
  have hex : candidates.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [ok]⟩⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image candidates Finset.card hex
  obtain ⟨hsub, hfree⟩ := Finset.mem_filter.mp hT
  have hTG := Finset.mem_powerset.mp hsub
  refine ⟨T, hTG.trans (Finset.filter_subset _ _), ?_, hfree⟩
  let neighbor (a : ℕ) := (inc a).image fun e ↦ if e.1 = a then e.2 else e.1
  have hcover : G ⊆ T ∪ T.biUnion neighbor := by
    intro a ha
    by_cases haT : a ∈ T
    · exact Finset.mem_union_left _ haT
    · apply Finset.mem_union_right
      have hbad : ¬ ok (insert a T) := by
        intro hi
        have hm := hmax (insert a T) (Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.insert_subset ha hTG), hi⟩)
        rw [Finset.card_insert_of_notMem haT] at hm
        omega
      dsimp only [ok] at hbad
      push Not at hbad
      obtain ⟨e, he, h₁, h₂⟩ := hbad
      rcases Finset.mem_insert.mp h₁ with h₁ | h₁ <;>
        rcases Finset.mem_insert.mp h₂ with h₂ | h₂
      · exact (hloop e he (h₁.trans h₂.symm)).elim
      · apply Finset.mem_biUnion.mpr
        refine ⟨e.2, h₂, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, Or.inr rfl⟩, ?_⟩⟩
        rw [if_neg (hloop e he), h₁]
      · apply Finset.mem_biUnion.mpr
        exact ⟨e.1, h₁, Finset.mem_image.mpr
          ⟨e, Finset.mem_filter.mpr ⟨he, Or.inl rfl⟩, (if_pos rfl).trans h₂⟩⟩
      · exact (hfree e he h₁ h₂).elim
  have hG : G.card ≤ T.card * (4 * P + 1) := by
    calc
      _ ≤ (T ∪ T.biUnion neighbor).card := Finset.card_le_card hcover
      _ ≤ T.card + (T.biUnion neighbor).card := Finset.card_union_le _ _
      _ ≤ T.card + ∑ a ∈ T, (neighbor a).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ T.card + ∑ _ ∈ T, (4 * P) := by
        apply Nat.add_le_add_left
        exact Finset.sum_le_sum fun a ha ↦
          Finset.card_image_le.trans (Finset.mem_filter.mp (hTG ha)).2
      _ = _ := by simp [Nat.mul_add, Nat.add_comm]
  calc
    _ ≤ 2 * G.card := hhalf
    _ ≤ 2 * (T.card * (4 * P + 1)) := Nat.mul_le_mul_left _ hG
    _ = _ := by ring

private def positiveDifferences (S : Finset ℕ) : Finset ℕ :=
  ((S ×ˢ S).filter fun e ↦ e.2 < e.1).image fun e ↦ e.1 - e.2

private lemma mem_positiveDifferences {S : Finset ℕ} {r : ℕ} :
    r ∈ positiveDifferences S ↔
      ∃ a ∈ S, ∃ b ∈ S, b < a ∧ a - b = r := by
  constructor
  · intro hr
    obtain ⟨⟨a,b⟩, h, he⟩ := Finset.mem_image.mp hr
    obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp h
    exact ⟨a, (Finset.mem_product.mp hmem).1, b, (Finset.mem_product.mp hmem).2, hlt, he⟩
  · rintro ⟨a, ha, b, hb, hlt, he⟩
    exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hlt⟩, he⟩

private def nearbyDifferenceConflicts (B : ℕ → Finset ℕ) (j : ℕ) : Finset (ℕ × ℕ) :=
  (B j ×ˢ B j).filter fun e ↦ e.2 < e.1 ∧
    e.1 - e.2 ∈ (Finset.Ioo (j / 3) j).biUnion (fun i ↦ positiveDifferences (B i))

private lemma nearbyDifferenceConflicts_card (B : ℕ → Finset ℕ) (j : ℕ)
    (hS : IsSidon (B j : Set ℕ)) :
    (nearbyDifferenceConflicts B j).card =
      (positiveDifferences (B j) ∩
        (Finset.Ioo (j / 3) j).biUnion (fun i ↦ positiveDifferences (B i))).card := by
  let E := nearbyDifferenceConflicts B j
  let f (e : ℕ × ℕ) := e.1 - e.2
  have himage : E.image f = positiveDifferences (B j) ∩
      (Finset.Ioo (j / 3) j).biUnion (fun i ↦ positiveDifferences (B i)) := by
    ext r
    rw [Finset.mem_image, Finset.mem_inter, mem_positiveDifferences]
    constructor
    · rintro ⟨⟨a,b⟩, hab, rfl⟩
      obtain ⟨hmem, hlt, hnear⟩ := Finset.mem_filter.mp hab
      exact ⟨⟨a, (Finset.mem_product.mp hmem).1, b,
        (Finset.mem_product.mp hmem).2, hlt, rfl⟩, hnear⟩
    · rintro ⟨⟨a, ha, b, hb, hlt, rfl⟩, hnear⟩
      exact ⟨(a,b), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hlt, hnear⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injOn]
  intro ⟨a,b⟩ hab ⟨u,v⟩ huv he
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hab).1
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp (Finset.mem_filter.mp huv).1
  obtain ⟨h₁,h₂⟩ := sidon_positive_difference_unique (B j) hS ha hb hu hv
    (Finset.mem_filter.mp hab).2.1 (Finset.mem_filter.mp huv).2.1 he
  exact Prod.ext h₁ h₂

/-- It suffices to bound the average number of earlier conflicts per vertex by
a fixed polynomial in the index. The earlier rulers can be left arbitrary. -/
private lemma nearby_iff_polynomial_conflict_budget :
    H1 ↔ ∃ d e J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, IsSidon (B j : Set ℕ)) ∧
      (∀ j, J ≤ j → j ≤ N →
        2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧
      ∀ j, J ≤ j → j ≤ N →
        (nearbyDifferenceConflicts B j).card ≤ (B j).card * (j + 1) ^ e := by
  constructor
  · rintro ⟨d, J, hB⟩
    refine ⟨d, 0, J, fun N ↦ ?_⟩
    obtain ⟨B, hpos, hsid, hdense, hsep⟩ := hB N
    refine ⟨B, hpos, fun j a ha u hu b hb v hv he ↦ hsid j a ha b hb u hu v hv he, hdense, ?_⟩
    intro j _ _
    have hnone : nearbyDifferenceConflicts B j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ⟨u,v⟩ he
      obtain ⟨he, hlt, hd⟩ := Finset.mem_filter.mp he
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp he
      obtain ⟨i, hi, hd⟩ := Finset.mem_biUnion.mp hd
      obtain ⟨a, ha, b, hb, hab, heq⟩ := mem_positiveDifferences.mp hd
      exact hsep i j (Finset.mem_Ioo.mp hi).1 (Finset.mem_Ioo.mp hi).2 a ha b hb u hu v hv hab hlt heq
    rw [hnone, Finset.card_empty]
    exact Nat.zero_le _
  · rintro ⟨d, e, J, hB⟩
    let J₀ := max 1 J
    refine ⟨d + (e + 4), J₀, fun N ↦ ?_⟩
    obtain ⟨B, hpos, hsid, hdense, hbudget⟩ := hB N
    have hthin j (hj : J₀ ≤ j ∧ j ≤ N) :=
      thin_avoiding_pairs (B j) (nearbyDifferenceConflicts B j) ((j + 1) ^ e)
        (fun x hx ↦ (Finset.mem_filter.mp hx).2.1.ne') (hbudget j ((le_max_right _ _).trans hj.1) hj.2)
    choose T hsub hcard hfree using hthin
    let C (j : ℕ) := if hj : J₀ ≤ j ∧ j ≤ N then T j hj else ∅
    have hC j : C j ⊆ B j := by
      by_cases hj : J₀ ≤ j ∧ j ≤ N
      · simpa only [C, dif_pos hj] using hsub j hj
      · simp only [C, dif_neg hj, Finset.empty_subset]
    refine ⟨C, fun j ↦ (hC j).trans (hpos j), ?_, ?_, ?_⟩
    · intro j a ha b hb u hu v hv he
      exact hsid j a (hC j ha) u (hC j hu) b (hC j hb) v (hC j hv) he
    · intro j hj hjN
      have hP : 1 ≤ (j + 1) ^ e := Nat.one_le_pow _ _ (by positivity)
      have hfactor : 2 * (4 * (j + 1) ^ e + 1) ≤ (j + 1) ^ (e + 4) := by
        have hj₂ : 2 ≤ j + 1 := by have := (le_max_left _ _).trans hj; omega
        calc
          _ ≤ 10 * (j + 1) ^ e := by omega
          _ ≤ (j + 1) ^ 4 * (j + 1) ^ e :=
            Nat.mul_le_mul_right _ ((by decide : 10 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hj₂ _))
          _ = _ := by rw [← pow_add]; congr 1; omega
      apply dyadic_energy_count_transfer j d (e + 4) (B j).card (C j).card
        (hdense j ((le_max_right _ _).trans hj) hjN)
      rw [show C j = T j ⟨hj,hjN⟩ by exact dif_pos ⟨hj,hjN⟩]
      exact (hcard j ⟨hj,hjN⟩).trans (Nat.mul_le_mul_left _ hfactor)
    · intro i j hnear hij a ha b hb u hu v hv hab huv he
      by_cases hj : J₀ ≤ j ∧ j ≤ N
      · have hc : (u,v) ∈ nearbyDifferenceConflicts B j := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hC j hu, hC j hv⟩, huv,
            Finset.mem_biUnion.mpr ⟨i, Finset.mem_Ioo.mpr ⟨hnear,hij⟩,
              mem_positiveDifferences.mpr ⟨a, hC i ha, b, hC i hb, hab, he⟩⟩⟩
        exact hfree j hj (u,v) hc (by simpa only [C, dif_pos hj] using hu)
          (by simpa only [C, dif_pos hj] using hv)
      · simp [C,hj] at hu

/-- Differences from any block whose width is at most the cutoff contribute
at most the cutoff in total. Only the wider predecessors need pairwise bounds. -/
private lemma nearby_conflict_budget_of_wide_overlaps
    (B : ℕ → Finset ℕ) (j t M : ℕ)
    (hpos : ∀ i, B i ⊆ Finset.Ico (2 ^ i) (2 ^ (i + 1)))
    (hsid : IsSidon (B j : Set ℕ))
    (hoverlap : ∀ i, j / 3 < i → i < j → t < 2 ^ i →
      (positiveDifferences (B j) ∩ positiveDifferences (B i)).card ≤ M) :
    (nearbyDifferenceConflicts B j).card ≤ t + j * M := by
  let I := (Finset.Ioo (j / 3) j).filter fun i ↦ t < 2 ^ i
  let overlap i := positiveDifferences (B j) ∩ positiveDifferences (B i)
  have hcover :
      positiveDifferences (B j) ∩
        (Finset.Ioo (j / 3) j).biUnion (fun i ↦ positiveDifferences (B i)) ⊆
        Finset.range t ∪ I.biUnion overlap := by
    intro r hr
    obtain ⟨hrj, hrprev⟩ := Finset.mem_inter.mp hr
    obtain ⟨i, hi, hri⟩ := Finset.mem_biUnion.mp hrprev
    by_cases ht : t < 2 ^ i
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, ht⟩, Finset.mem_inter.mpr ⟨hrj, hri⟩⟩)
    · obtain ⟨a, ha, b, hb, _, rfl⟩ := mem_positiveDifferences.mp hri
      have hlo := (Finset.mem_Ico.mp (hpos i hb)).1
      have hhi := (Finset.mem_Ico.mp (hpos i ha)).2
      rw [pow_succ] at hhi
      exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
  rw [nearbyDifferenceConflicts_card B j hsid]
  have hsize : I.card ≤ j := by
    rw [← Finset.card_range j]
    exact Finset.card_le_card fun i hi ↦
      Finset.mem_range.mpr (Finset.mem_Ioo.mp (Finset.mem_filter.mp hi).1).2
  calc
    _ ≤ (Finset.range t ∪ I.biUnion overlap).card := Finset.card_le_card hcover
    _ ≤ (Finset.range t).card + (I.biUnion overlap).card := Finset.card_union_le _ _
    _ ≤ t + ∑ i ∈ I, (overlap i).card := by
      rw [Finset.card_range]
      exact Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ t + ∑ _ ∈ I, M := by
      refine Nat.add_le_add_left (Finset.sum_le_sum fun i hi ↦ ?_) _
      obtain ⟨hi, ht⟩ := Finset.mem_filter.mp hi
      exact hoverlap i (Finset.mem_Ioo.mp hi).1 (Finset.mem_Ioo.mp hi).2 ht
    _ ≤ _ := by
      simpa [nsmul_eq_mul] using
        Nat.add_le_add_left (Nat.mul_le_mul_right M hsize) t

private lemma dyadic_half_power_le_weighted_card (j d M : ℕ)
    (hdense : 2 ^ j ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    2 ^ (j / 2) ≤ M * (j + 1) ^ (d + 1) := by
  apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
  calc
    (2 ^ (j / 2)) ^ 2 = 2 ^ ((j / 2) * 2) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ j := pow_le_pow_right₀ (by decide) (by omega)
    _ ≤ _ := by simpa only [mul_pow, ← pow_mul, mul_comm (d + 1) 2] using hdense

/-- Polynomial pairwise overlap bounds suffice above the half-scale cutoff,
which may itself be increased by any fixed polynomial in the index. -/
private lemma nearby_iff_wide_overlap_budget (k : ℕ) :
    H1 ↔ ∃ d e J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, IsSidon (B j : Set ℕ)) ∧
      (∀ j, J ≤ j → j ≤ N →
        2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧
      ∀ j, J ≤ j → j ≤ N → ∀ i, j / 3 < i → i < j →
        2 ^ (j / 2) * (j + 1) ^ k < 2 ^ i →
        (positiveDifferences (B j) ∩ positiveDifferences (B i)).card ≤
          2 ^ (j / 2) * (j + 1) ^ e := by
  constructor
  · intro h
    obtain ⟨d, J, B, hpos, hsid, hcount, hsep⟩ :=
      nearby_iff_infinite_separated_packing.mp h
    refine ⟨d, 0, J, fun N ↦ ⟨B, hpos, hsid, fun j hj _ ↦ hcount j hj, ?_⟩⟩
    intro j _ _ i _ hij _
    have he : positiveDifferences (B j) ∩ positiveDifferences (B i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hjr, hir⟩ := Finset.mem_inter.mp hr
      obtain ⟨u, hu, v, hv, hvu, heqj⟩ := mem_positiveDifferences.mp hjr
      obtain ⟨a, ha, b, hb, hba, heqi⟩ := mem_positiveDifferences.mp hir
      exact hsep i j hij a ha b hb u hu v hv hba hvu (heqi.trans heqj.symm)
    simp [he]
  · rintro ⟨d, e, J, hB⟩
    let L := max J 1
    let p := max k (e + 1)
    apply nearby_iff_polynomial_conflict_budget.mpr
    refine ⟨d, d + p + 2, L, fun N ↦ ?_⟩
    obtain ⟨B, hpos, hsid, hdense, hoverlap⟩ := hB N
    refine ⟨B, hpos, hsid, fun j hj ↦ hdense j ((le_max_left _ _).trans hj), ?_⟩
    intro j hj hjN
    have hjJ : J ≤ j := (le_max_left _ _).trans hj
    have hj2 : 2 ≤ j + 1 := by have := (le_max_right _ _).trans hj; omega
    have hk : (j + 1) ^ k ≤ (j + 1) ^ p :=
      pow_le_pow_right₀ (by omega) (le_max_left _ _)
    have he : j * (j + 1) ^ e ≤ (j + 1) ^ p := by
      calc
        _ ≤ (j + 1) ^ (e + 1) := by
          rw [pow_succ, mul_comm j]
          exact Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ ≤ _ := pow_le_pow_right₀ (by omega) (le_max_right _ _)
    have hroot := dyadic_half_power_le_weighted_card j d _ (hdense j hjJ hjN)
    calc
      _ ≤ 2 ^ (j / 2) * (j + 1) ^ k + j * (2 ^ (j / 2) * (j + 1) ^ e) :=
        nearby_conflict_budget_of_wide_overlaps B j _ _ hpos (hsid j) (hoverlap j hjJ hjN)
      _ = 2 ^ (j / 2) * ((j + 1) ^ k + j * (j + 1) ^ e) := by ring
      _ ≤ 2 ^ (j / 2) * ((j + 1) ^ p + (j + 1) ^ p) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add hk he)
      _ ≤ ((B j).card * (j + 1) ^ (d + 1)) * ((j + 1) ^ p * (j + 1)) := by
        rw [← mul_two]
        exact Nat.mul_le_mul hroot (Nat.mul_le_mul_left _ hj2)
      _ = (B j).card * (j + 1) ^ (d + p + 2) := by
        rw [← pow_succ, mul_assoc, ← pow_add]
        congr 2
        omega

/-- A finite Sidon set of size m forbids at most m³ + m² + m new points. -/
private lemma exists_sidon_insert_of_card_lt (S D : Finset ℕ) (hS : IsSidon (S : Set ℕ))
    (hD : S.card ^ 3 + S.card ^ 2 + S.card < D.card) :
    ∃ x ∈ D, x ∉ S ∧ IsSidon (↑(insert x S) : Set ℕ) := by
  let linear := ((S ×ˢ S) ×ˢ S).image fun abc ↦ abc.1.1 + abc.1.2 - abc.2
  let double := (S ×ˢ S).image fun ab ↦ (ab.1 + ab.2) / 2
  let bad := linear ∪ double ∪ S
  have hlin : linear.card ≤ S.card ^ 3 := by
    calc
      _ ≤ ((S ×ˢ S) ×ˢ S).card := Finset.card_image_le
      _ = _ := by rw [Finset.card_product, Finset.card_product, pow_succ, pow_two]
  have hdbl : double.card ≤ S.card ^ 2 := by
    calc
      _ ≤ (S ×ˢ S).card := Finset.card_image_le
      _ = _ := by rw [Finset.card_product, pow_two]
  have hbad : bad.card ≤ S.card ^ 3 + S.card ^ 2 + S.card := by
    calc
      _ ≤ (linear ∪ double).card + S.card := Finset.card_union_le _ _
      _ ≤ linear.card + double.card + S.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add hlin hdbl) _
  obtain ⟨x, hx, hxB⟩ := Finset.exists_mem_notMem_of_card_lt_card (hbad.trans_lt hD)
  have hxS : x ∉ S := fun h ↦ hxB (Finset.mem_union_right _ h)
  have hl (a b c : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (he : a + b = x + c) :
      False := by
    apply hxB
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨((a,b),c),
      Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hc⟩, by dsimp; omega⟩
  have hd (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S) (he : a + b = x + x) :
      False := by
    apply hxB
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, by dsimp; omega⟩
  refine ⟨x, hx, hxS, ?_⟩
  intro a ha b hb c hc d hd' he
  simp only [Finset.mem_coe, Finset.mem_insert] at ha hb hc hd'
  rcases ha with rfl | ha <;> rcases hb with rfl | hb <;>
    rcases hc with rfl | hc <;> rcases hd' with rfl | hd' <;> try omega
  · exact (hd b d hb hd' he.symm).elim
  · exact (hl b d c hb hd' hc he.symm).elim
  · exact (hd a c ha hc he).elim
  · exact (hl a c d ha hc hd' he).elim
  · exact (hl b d a hb hd' ha (by omega)).elim
  · exact (hl a c b ha hc hb (by omega)).elim
  · exact hS a ha b hb c hc d hd' he

private lemma exists_sidon_extension_of_cubic_budget (A D : Finset ℕ)
    (hA : IsSidon (A : Set ℕ)) (n : ℕ) (hD : (A.card + n + 1) ^ 3 ≤ D.card) :
    ∃ S : Finset ℕ, A ⊆ S ∧ S \ A ⊆ D ∧ IsSidon (S : Set ℕ) ∧ S.card = A.card + n := by
  induction n with
  | zero => exact ⟨A, le_rfl, by simp, hA, by simp⟩
  | succ n ih =>
    obtain ⟨S, hsub, hnew, hS, hcard⟩ := ih
      ((Nat.pow_le_pow_left (by omega) 3).trans hD)
    have hsize : S.card ^ 3 + S.card ^ 2 + S.card < D.card := by
      calc
        _ < (S.card + 2) ^ 3 := by nlinarith [Nat.zero_le (S.card ^ 2)]
        _ ≤ _ := by simpa only [hcard, Nat.succ_eq_add_one, Nat.add_assoc] using hD
    obtain ⟨x, hxD, hxS, hx⟩ := exists_sidon_insert_of_card_lt S D hS hsize
    refine ⟨insert x S, hsub.trans (Finset.subset_insert _ _), ?_, hx, ?_⟩
    · intro y hy
      obtain ⟨hy, hyA⟩ := Finset.mem_sdiff.mp hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxD
      · exact hnew (Finset.mem_sdiff.mpr ⟨hy,hyA⟩)
    · rw [Finset.card_insert_of_notMem hxS, hcard]
      omega

/-- Greedy extensions give a common Sidon host with cube-root-size clusters in
every dyadic block of a finite horizon. -/
private lemma cubic_sidon_prefix (n : ℕ) :
    ∃ S : Finset ℕ, IsSidon (S : Set ℕ) ∧ S ⊆ Finset.range (2 ^ (n + 12)) ∧
      S.card ≤ (3 + n % 3) * 2 ^ (n / 3) ∧
      ∀ j, 12 ≤ j → j < n + 12 →
        2 ^ ((j - 12) / 3) ≤ (S ∩ Finset.Ico (2 ^ j) (2 ^ (j + 1))).card := by
  induction n with
  | zero =>
    refine ⟨∅, by simp [IsSidon], Finset.empty_subset _, by simp, ?_⟩
    omega
  | succ n ih =>
    obtain ⟨A, hA, hpos, hcard, hprev⟩ := ih
    let T : ℕ := 2 ^ (n / 3)
    let D := Finset.Ico (2 ^ (n + 12)) (2 ^ (n + 13))
    have hT : 1 ≤ T := Nat.one_le_pow _ _ (by decide)
    have hbound : A.card + T ≤ (4 + n % 3) * T := by
      calc
        _ ≤ (3 + n % 3) * T + T := Nat.add_le_add_right hcard _
        _ = _ := by ring
    have hDcard : D.card = 2 ^ (n + 12) := by
      dsimp [D]
      rw [Nat.card_Ico, show n + 13 = (n + 12) + 1 by omega, pow_succ]
      omega
    have hbudget : (A.card + T + 1) ^ 3 ≤ D.card := by
      have hsmall : A.card + T + 1 ≤ 7 * T := by
        have hm := Nat.mul_le_mul_right T (show 4 + n % 3 ≤ 6 by omega)
        omega
      calc
        _ ≤ (7 * T) ^ 3 := Nat.pow_le_pow_left hsmall _
        _ ≤ 4096 * T ^ 3 := by rw [mul_pow]; exact Nat.mul_le_mul_right _ (by decide)
        _ = 2 ^ (n / 3 * 3 + 12) := by rw [pow_add, pow_mul, mul_comm]; rfl
        _ ≤ (2 : ℕ) ^ (n + 12) := pow_le_pow_right₀ (by decide) (by omega)
        _ = _ := hDcard.symm
    obtain ⟨S, hsub, hnew, hS, hScard⟩ := exists_sidon_extension_of_cubic_budget A D hA T hbudget
    refine ⟨S, hS, ?_, ?_, ?_⟩
    · intro x hx
      apply Finset.mem_range.mpr
      by_cases hxA : x ∈ A
      · have : x < (2 : ℕ) ^ (n + 12) := Finset.mem_range.mp (hpos hxA)
        exact this.trans_le (pow_le_pow_right₀ (by decide) (by omega))
      · have := (Finset.mem_Ico.mp (hnew (Finset.mem_sdiff.mpr ⟨hx, hxA⟩))).2
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using this
    · rw [hScard]
      apply hbound.trans
      dsimp [T]
      by_cases hm : n % 3 = 2
      · have hq : (n + 1) / 3 = n / 3 + 1 := by omega
        have hr : (n + 1) % 3 = 0 := by omega
        rw [hq, hr, hm, pow_succ]
        ring_nf
        exact le_rfl
      · have hq : (n + 1) / 3 = n / 3 := by omega
        have hr : (n + 1) % 3 = n % 3 + 1 := by omega
        rw [hq, hr]
        ring_nf
        exact le_rfl
    · intro j hj hjn
      by_cases hlast : j = n + 12
      · subst j
        have hfilter : S \ A ⊆ S ∩ D := fun x hx ↦
          Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hx).1, hnew hx⟩
        have hsdiff : (S \ A).card = T := by
          rw [Finset.card_sdiff_of_subset hsub, hScard]
          omega
        have hcount := Finset.card_le_card hfilter
        rw [hsdiff] at hcount
        simpa only [D, T, Nat.add_sub_cancel_right, Nat.add_assoc] using hcount
      · exact (hprev j hj (by omega)).trans (Finset.card_le_card fun x hx ↦
          Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩)

/-- The exact packing and difference separation hold at every scale when the
cardinality requirement is weakened to cube-root growth. -/
private lemma nearby_packing_cubic_density :
    ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, IsSidon (B j : Set ℕ)) ∧
      (∀ j, 12 ≤ j → j ≤ N → 2 ^ j ≤ 16384 * (B j).card ^ 3) ∧
      ∀ i j, i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
        b < a → v < u → a - b ≠ u - v := by
  intro N
  obtain ⟨S, hS, _, _, hcount⟩ := cubic_sidon_prefix (N + 1)
  let B j := S ∩ Finset.Ico (2 ^ j) (2 ^ (j + 1))
  have hsub j : B j ⊆ S := Finset.inter_subset_left
  refine ⟨B, fun j ↦ Finset.inter_subset_right, ?_, ?_, ?_⟩
  · intro j a ha u hu b hb v hv he
    exact hS a (hsub j ha) u (hsub j hu) b (hsub j hb) v (hsub j hv) he
  · intro j hj hjN
    have h := hcount j hj (by omega)
    calc
      _ ≤ 2 ^ (((j - 12) / 3) * 3 + 14) := pow_le_pow_right₀ (by decide) (by omega)
      _ = 16384 * (2 ^ ((j - 12) / 3)) ^ 3 := by
        rw [pow_add, pow_mul, mul_comm]
        rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
  · intro i j hij a ha b hb u hu v hv hba hvu he
    have hEq := (sidon_positive_difference_unique S hS (hsub i ha) (hsub i hb)
      (hsub j hu) (hsub j hv) hba hvu he).1
    have ha' := (Finset.mem_Ico.mp (Finset.inter_subset_right ha)).2
    have hu' := (Finset.mem_Ico.mp (Finset.inter_subset_right hu)).1
    have hPow : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by decide) (by omega)
    exact (ha'.trans_le (hPow.trans hu')).ne hEq

private def ambiguousSumPairs (T : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T.filter fun e ↦ 1 < (T.filter fun f ↦ f.1 + f.2 = e.1 + e.2).card

private lemma ambiguousSumPairs_card_add_twice_image (T : Finset (ℕ × ℕ)) :
    (ambiguousSumPairs T).card + 2 * (T.image fun e ↦ e.1 + e.2).card ≤ 2 * T.card := by
  let f (e : ℕ × ℕ) := e.1 + e.2
  let R := T.image f
  let E := ambiguousSumPairs T
  let F (U : Finset (ℕ × ℕ)) (z : ℕ) := U.filter fun e ↦ f e = z
  have hT : T.card = ∑ z ∈ R, (F T z).card :=
    Finset.card_eq_sum_card_fiberwise (fun e he ↦ Finset.mem_image_of_mem f he)
  have hE : E.card = ∑ z ∈ R, (F E z).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun e he ↦ Finset.mem_image_of_mem f (Finset.mem_filter.mp he).1)
  change E.card + 2 * R.card ≤ 2 * T.card
  rw [hT, hE]
  calc
    _ = ∑ z ∈ R, ((F E z).card + 2) := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]
    _ ≤ ∑ z ∈ R, 2 * (F T z).card := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨e, he, hez⟩ := Finset.mem_image.mp hz
      have hpos : 1 ≤ (F T z).card :=
        Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hez⟩⟩
      by_cases hlarge : 1 < (F T z).card
      · have hle : (F E z).card ≤ (F T z).card :=
          Finset.card_le_card fun a ha ↦
            Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1,
              (Finset.mem_filter.mp ha).2⟩
        omega
      · have hempty : F E z = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a ha
          obtain ⟨haE, haz⟩ := Finset.mem_filter.mp ha
          have hlarge' := (Finset.mem_filter.mp haE).2
          have heq : 1 < (F T (f a)).card := hlarge'
          rw [haz] at heq
          exact hlarge heq
        simp only [hempty, Finset.card_empty, zero_add]
        omega
    _ = _ := (Finset.mul_sum ..).symm

/-- A mixed representation is ambiguous when at least two pairs give its sum. -/
private def ambiguousMixedPairs (A B : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ B).filter fun e ↦
    1 < ((A ×ˢ B).filter fun f ↦ f.1 + f.2 = e.1 + e.2).card

private lemma mem_ambiguousMixedPairs_of_collision (A B : Finset ℕ) {a b u v : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hu : u ∈ B) (hv : v ∈ B) (hab : a ≠ b)
    (hsum : a + u = b + v) : (a,u) ∈ ambiguousMixedPairs A B := by
  have h₁ : (a,u) ∈ A ×ˢ B := Finset.mem_product.mpr ⟨ha, hu⟩
  have h₂ : (b,v) ∈ A ×ˢ B := Finset.mem_product.mpr ⟨hb, hv⟩
  exact Finset.mem_filter.mpr ⟨h₁, Finset.one_lt_card.mpr
    ⟨(a,u), Finset.mem_filter.mpr ⟨h₁, rfl⟩,
      (b,v), Finset.mem_filter.mpr ⟨h₂, hsum.symm⟩, fun h ↦ hab (congrArg Prod.fst h)⟩⟩

private lemma ambiguousMixedPairs_card_add_twice_sumset (A B : Finset ℕ) :
    (ambiguousMixedPairs A B).card +
      2 * ((A ×ˢ B).image (fun e ↦ e.1 + e.2)).card ≤ 2 * (A.card * B.card) := by
  simpa only [ambiguousMixedPairs, ambiguousSumPairs, Finset.card_product] using
    ambiguousSumPairs_card_add_twice_image (A ×ˢ B)

private lemma card_filter_fst_mem (E : Finset (ℕ × ℕ)) (S : Finset ℕ) :
    (E.filter fun e ↦ e.1 ∈ S).card =
      ∑ a ∈ S, (E.filter fun e ↦ e.1 = a).card := by
  have hm : Set.MapsTo Prod.fst (↑(E.filter fun e ↦ e.1 ∈ S) : Set (ℕ × ℕ)) (S : Set ℕ) :=
    fun e he ↦ (Finset.mem_filter.mp he).2
  rw [Finset.card_eq_sum_card_fiberwise hm]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.symm ▸ ha⟩, h.2⟩⟩

private lemma exists_half_bounded_cost (S : Finset ℕ) (f : ℕ → ℚ) (p : ℚ)
    (hf : ∀ a, 0 ≤ f a) (hp : 0 ≤ p) (hbudget : ∑ a ∈ S, f a ≤ p / 2) :
    ∃ G ⊆ S, S.card ≤ 2 * G.card ∧ ∀ a ∈ G, (S.card : ℚ) * f a ≤ p := by
  let D := S.filter fun a ↦ p < (S.card : ℚ) * f a
  let G := S \ D
  have hDsub : D ⊆ S := Finset.filter_subset _ _
  have hsize : 2 * D.card ≤ S.card := by
    by_contra! h
    have hn : D.Nonempty := Finset.card_pos.mp (by omega)
    have hlt : (D.card : ℚ) * p < (S.card : ℚ) * ∑ a ∈ D, f a := by
      rw [Finset.mul_sum, ← show (∑ _ ∈ D, p) = (D.card : ℚ) * p by simp [nsmul_eq_mul]]
      apply Finset.sum_lt_sum_of_nonempty hn
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hDsub (fun a _ _ ↦ hf a)
    have hc : (S.card : ℚ) ≤ 2 * (D.card : ℚ) := by exact_mod_cast h.le
    have hmul := mul_le_mul_of_nonneg_right hc hp
    have hu := mul_le_mul_of_nonneg_left (hs.trans hbudget) (show (0 : ℚ) ≤ S.card by positivity)
    linarith
  refine ⟨G, Finset.sdiff_subset, ?_, ?_⟩
  · rw [show G.card = S.card - D.card from Finset.card_sdiff_of_subset hDsub]
    have := Finset.card_le_card hDsub
    omega
  · intro a ha
    exact le_of_not_gt (fun h ↦ (Finset.mem_sdiff.mp ha).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, h⟩))

private def blockSelectionDenominator (P i : ℕ) : ℕ :=
  4 * (12 * (i + 1) * P) * ((i + 1) * (i + 2))

set_option maxHeartbeats 2000000 in
/-- Select a polynomial fraction of each block while eliminating sparse
bipartite conflicts, allowing the earlier and later block to both change. -/
private lemma select_blocks_without_bipartite_conflicts
    (B : ℕ → Finset ℕ) (E : ℕ → ℕ → Finset (ℕ × ℕ)) (P : ℕ → ℕ)
    (hP : ∀ i, 1 ≤ P i)
    (hzero : ∀ i j, ¬ (i < j ∧ j < 3 * i) → E i j = ∅)
    (hE : ∀ i j, (E i j).card ≤ (B j).card * P i) (n : ℕ) :
    ∃ C : ℕ → Finset ℕ, (∀ i, C i ⊆ B i) ∧
      (∀ i, i < n → (C i).card = (B i).card / blockSelectionDenominator (P i) i) ∧
      (∀ i, n ≤ i → C i = ∅) ∧
      ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C j, (a,b) ∉ E i j := by
  let I (i : ℕ) := Finset.Ioo i (3 * i)
  let deg (i j a : ℕ) := ((E i j).filter fun e ↦ e.1 = a).card
  let cost (i a : ℕ) : ℚ := ∑ j ∈ I i, (deg i j a : ℚ) / (B j).card
  let p (i : ℕ) : ℕ := 12 * (i + 1) * P i
  let w (i : ℕ) : ℕ := (i + 1) * (i + 2)
  let Q (i : ℕ) := blockSelectionDenominator (P i) i
  have hQeq i : Q i = 4 * p i * w i := rfl
  have hQ i : 4 ≤ Q i := by
    have hp : 1 ≤ p i := by
      dsimp [p]
      have := hP i
      exact Nat.mul_pos (by positivity) (by omega)
    have hw : 1 ≤ w i := by dsimp [w]; exact Nat.mul_pos (by omega) (by omega)
    rw [hQeq]
    simpa using Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp) hw
  have hcost0 i a : 0 ≤ cost i a :=
    Finset.sum_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hs i j : ∑ a ∈ B i, deg i j a ≤ (E i j).card := by
    rw [show (∑ a ∈ B i, deg i j a) = _ from (card_filter_fst_mem (E i j) (B i)).symm]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have havg i : ∑ a ∈ B i, cost i a ≤ (p i : ℚ) / 2 := by
    unfold cost
    rw [Finset.sum_comm]
    have hiter j : ∑ a ∈ B i, (deg i j a : ℚ) / (B j).card ≤ P i := by
      by_cases hj : (B j).card = 0
      · simp [hj]
      · rw [← Finset.sum_div]
        apply (div_le_iff₀ (show (0 : ℚ) < (B j).card by exact_mod_cast Nat.pos_of_ne_zero hj)).mpr
        rw [← Nat.cast_sum, ← Nat.cast_mul, mul_comm (P i)]
        exact_mod_cast (hs i j).trans (hE i j)
    have hI : (I i).card ≤ 3 * i := by
      rw [← Finset.card_range (3 * i)]
      exact Finset.card_le_card fun j hj ↦ Finset.mem_range.mpr (Finset.mem_Ioo.mp hj).2
    calc
      _ ≤ ∑ _ ∈ I i, (P i : ℚ) := Finset.sum_le_sum fun j _ ↦ hiter j
      _ ≤ ((3 * i : ℕ) : ℚ) * (P i : ℚ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (by positivity)
      _ ≤ _ := by
        dsimp [p]
        push_cast
        nlinarith [show (0 : ℚ) ≤ P i by positivity, show (0 : ℚ) ≤ i * (P i : ℚ) by positivity]
  choose G hG hGc hGcost using fun i ↦
    exists_half_bounded_cost (B i) (cost i) (p i) (hcost0 i) (by positivity) (havg i)
  let blocked (A : Finset ℕ) (i j : ℕ) :=
    ((E i j).filter fun e ↦ e.1 ∈ A).image Prod.snd
  have hblocked (A : Finset ℕ) (i j : ℕ) (hA : A ⊆ G i)
      (hAc : A.card = (B i).card / Q i) :
      4 * ((blocked A i j).card : ℚ) ≤ ((B j).card : ℚ) * (1 / ((i + 1) * (i + 2))) := by
    by_cases hj : j ∈ I i
    swap
    · have he : E i j = ∅ := hzero i j (by simpa [I, Finset.mem_Ioo] using hj)
      simpa [blocked, he] using
        (show (0 : ℚ) ≤ ((B j).card : ℚ) * (1 / ((i + 1) * (i + 2))) by positivity)
    by_cases hb : (B j).card = 0
    · have he : E i j = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (by simpa only [hb, zero_mul] using hE i j))
      simp [blocked, he, hb]
    have hcap i j : (blocked A i j).card ≤ ∑ a ∈ A, deg i j a :=
      Finset.card_image_le.trans (card_filter_fst_mem (E i j) A).le
    have hd a : (deg i j a : ℚ) / (B j).card ≤ cost i a :=
      Finset.single_le_sum (f := fun k ↦ (deg i k a : ℚ) / (B k).card) (fun k _ ↦ by positivity) hj
    have hrel : ((blocked A i j).card : ℚ) ≤ (∑ a ∈ A, cost i a) * (B j).card := by
      calc
        _ ≤ ∑ a ∈ A, (deg i j a : ℚ) := by exact_mod_cast hcap i j
        _ ≤ ∑ a ∈ A, cost i a * (B j).card := by
          apply Finset.sum_le_sum
          intro a _
          exact (div_le_iff₀ (show (0 : ℚ) < (B j).card by exact_mod_cast Nat.pos_of_ne_zero hb)).mp (hd a)
        _ = _ := (Finset.sum_mul ..).symm
    by_cases hi : (B i).card = 0
    · have hA0 : A = ∅ := Finset.card_eq_zero.mp (by simp [hAc, hi])
      simpa [hA0, blocked] using
        (show (0 : ℚ) ≤ ((B j).card : ℚ) * (1 / ((i + 1) * (i + 2))) by positivity)
    have hi' : (0 : ℚ) < (B i).card := by exact_mod_cast Nat.pos_of_ne_zero hi
    have hdiv : A.card * Q i ≤ (B i).card := by
      rw [hAc]
      exact Nat.div_mul_le_self _ _
    have hdiv' : (A.card : ℚ) * (4 * (p i : ℚ) * (w i : ℚ)) ≤ (B i).card := by
      exact_mod_cast (hQeq i ▸ hdiv)
    have hsum : ((B i).card : ℚ) * ∑ a ∈ A, cost i a ≤ (A.card : ℚ) * (p i : ℚ) := by
      rw [Finset.mul_sum]
      simpa [nsmul_eq_mul] using Finset.sum_le_sum fun a ha ↦ hGcost i a (hA ha)
    have hfactor : 4 * (w i : ℚ) * ∑ a ∈ A, cost i a ≤ 1 := by
      refine le_of_mul_le_mul_left ?_ hi'
      calc
        (B i).card * (4 * (w i : ℚ) * ∑ a ∈ A, cost i a) =
            (4 * (w i : ℚ)) * ((B i).card * ∑ a ∈ A, cost i a) := by ring
        _ ≤ (4 * (w i : ℚ)) * ((A.card : ℚ) * (p i : ℚ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (A.card : ℚ) * (4 * (p i : ℚ) * (w i : ℚ)) := by ring
        _ ≤ (B i).card * 1 := by simpa only [mul_one] using hdiv'
    have hw' : (0 : ℚ) < w i := by dsimp [w]; positivity
    have hscaled : 4 * ∑ a ∈ A, cost i a ≤ 1 / (w i : ℚ) := by
      apply (le_div_iff₀ hw').mpr
      calc
        _ = 4 * (w i : ℚ) * ∑ a ∈ A, cost i a := by ring
        _ ≤ _ := hfactor
    calc
      _ ≤ 4 * ((∑ a ∈ A, cost i a) * (B j).card) := mul_le_mul_of_nonneg_left hrel (by norm_num)
      _ = (4 * ∑ a ∈ A, cost i a) * (B j).card := by ring
      _ ≤ (1 / (w i : ℚ)) * (B j).card :=
        mul_le_mul_of_nonneg_right hscaled (by positivity)
      _ = _ := by simp [w, mul_comm]
  have hex (m : ℕ) : ∃ C : ℕ → Finset ℕ, (∀ i, C i ⊆ G i) ∧
      (∀ i, i < m → (C i).card = (B i).card / Q i) ∧
      (∀ i, m ≤ i → C i = ∅) ∧
      ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C j, (a,b) ∉ E i j := by
    induction m with
    | zero =>
      refine ⟨fun _ ↦ ∅, fun _ ↦ Finset.empty_subset _, ?_, by simp, by simp⟩
      omega
    | succ m ih =>
      obtain ⟨C, hC, hCc, htail, hfree⟩ := ih
      let D := (Finset.range m).biUnion (fun i ↦ blocked (C i) i m)
      have hD : 4 * D.card ≤ (B m).card := by
        have hcard : D.card ≤ ∑ i ∈ Finset.range m, (blocked (C i) i m).card :=
          Finset.card_biUnion_le
        have hcast : 4 * (D.card : ℚ) ≤ ((B m).card : ℚ) := by
          calc
            _ ≤ 4 * ∑ i ∈ Finset.range m, ((blocked (C i) i m).card : ℚ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by norm_num)
            _ ≤ ∑ i ∈ Finset.range m, ((B m).card : ℚ) * (1 / ((i + 1) * (i + 2))) := by
              rw [Finset.mul_sum]
              exact Finset.sum_le_sum fun i hi ↦ hblocked (C i) i m (hC i) (hCc i (Finset.mem_range.mp hi))
            _ ≤ _ := by
              rw [← Finset.mul_sum]
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left (reciprocal_weight_sum_le (Finset.range m))
                  (show (0 : ℚ) ≤ (B m).card from Nat.cast_nonneg _)
        exact_mod_cast hcast
      let Av := G m \ D
      have hAv : (B m).card ≤ 4 * Av.card := by
        have hc : (G m).card ≤ Av.card + D.card :=
          Finset.card_le_card (show G m ⊆ Av ∪ D by
            intro x hx
            by_cases hd : x ∈ D
            · exact Finset.mem_union_right _ hd
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hd⟩)) |>.trans
            (Finset.card_union_le _ _)
        have := hGc m
        omega
      have hneed : (B m).card / Q m ≤ Av.card :=
        (Nat.div_le_iff_le_mul (by have := hQ m; omega)).mpr (by
          have hmul := Nat.mul_le_mul_right Av.card (hQ m)
          rw [Nat.mul_comm (Q m)] at hmul
          have hpositive := hQ m
          omega)
      obtain ⟨U, hU, hUc⟩ := Finset.exists_subset_card_eq hneed
      let C' := Function.update C m U
      have hsame i (hi : i ≠ m) : C' i = C i := Function.update_of_ne hi _ _
      have hm : C' m = U := Function.update_self _ _ _
      refine ⟨C', ?_, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i = m
        · subst i
          rw [hm]
          exact hU.trans Finset.sdiff_subset
        · rw [hsame i hi]
          exact hC i
      · intro i hi
        by_cases he : i = m
        · subst i
          rw [hm]
          exact hUc
        · rw [hsame i he]
          exact hCc i (by omega)
      · intro i hi
        rw [hsame i (by omega)]
        exact htail i (by omega)
      · intro i j hij a ha b hb he
        rcases lt_trichotomy j m with hj | rfl | hj
        · rw [hsame i (by omega)] at ha
          rw [hsame j hj.ne] at hb
          exact hfree i j hij a ha b hb he
        · rw [hsame i hij.ne] at ha
          rw [hm] at hb
          have hbid : b ∈ D := Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hij,
            Finset.mem_image.mpr ⟨(a,b), Finset.mem_filter.mpr ⟨he,ha⟩, rfl⟩⟩
          exact (Finset.mem_sdiff.mp (hU hb)).2 hbid
        · rw [hsame j hj.ne', htail j hj.le] at hb
          exact Finset.notMem_empty _ hb
  obtain ⟨C, hC, hcard, htail, hfree⟩ := hex n
  exact ⟨C, fun i ↦ (hC i).trans (hG i), hcard, htail, hfree⟩

/-- A near-product mixed sumset suffices even when the number of colliding pairs
of representations is larger than their deficit in distinct sums. -/
private lemma nearby_iff_mixed_sumset_budget (k : ℕ) :
    H1 ↔ ∃ d e J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, IsSidon (B j : Set ℕ)) ∧
      (∀ j, J ≤ j → j ≤ N →
        2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧
      ∀ i j, j / 3 < i → i < j → J ≤ j → j ≤ N →
        2 ^ (j / 2) * (j + 1) ^ k < 2 ^ i →
        (B i).card * (B j).card ≤
          ((B i ×ˢ B j).image (fun e ↦ e.1 + e.2)).card + (B j).card * (j + 1) ^ e := by
  classical
  constructor
  · intro h
    obtain ⟨d, J, B, hpos, hsid, hcount, hsep⟩ :=
      nearby_iff_infinite_separated_packing.mp h
    refine ⟨d, 0, J, fun N ↦ ⟨B, hpos, hsid, fun j hj _ ↦ hcount j hj, ?_⟩⟩
    intro i j _ hij _ _ _
    have hinj : Set.InjOn (fun e : ℕ × ℕ ↦ e.1 + e.2) (↑(B i ×ˢ B j) : Set (ℕ × ℕ)) := by
      intro ⟨a,u⟩ hau ⟨b,v⟩ hbv he
      obtain ⟨ha,hu⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hau)
      obtain ⟨hb,hv⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hbv)
      change a + u = b + v at he
      have hab : a = b := by
        rcases lt_trichotomy a b with h | h | h
        · exact (hsep i j hij b hb a ha u hu v hv h (by omega) (by omega)).elim
        · exact h
        · exact (hsep i j hij a ha b hb v hv u hu h (by omega) (by omega)).elim
      exact Prod.ext hab (by dsimp; omega)
    rw [Finset.card_image_of_injOn hinj, Finset.card_product]
    exact Nat.le_add_right _ _
  · rintro ⟨d, e, J, hB⟩
    let P (i : ℕ) := 2 * (i + 1) ^ (3 * e)
    let Q (i : ℕ) := blockSelectionDenominator (P i) i
    let p := 3 * e + 11
    have hP i : 1 ≤ P i := by dsimp [P]; exact Nat.mul_pos (by decide) (by positivity)
    have hQ0 i : 0 < Q i := by
      have hp : 0 < P i := hP i
      dsimp [Q, blockSelectionDenominator]
      positivity
    have hQ i (hi : 1 ≤ i) : Q i ≤ (i + 1) ^ p := by
      let r := i + 1
      have hir : 2 ≤ r := by dsimp [r]; omega
      have hnext : i + 2 ≤ 2 * r := by dsimp [r]; omega
      calc
        Q i = 4 * (12 * r * (2 * r ^ (3 * e))) * (r * (i + 2)) := rfl
        _ ≤ 4 * (12 * r * (2 * r ^ (3 * e))) * (r * (2 * r)) := by gcongr
        _ = 192 * r ^ (3 * e + 3) := by rw [pow_add]; ring
        _ ≤ r ^ 8 * r ^ (3 * e + 3) := Nat.mul_le_mul_right _
          ((by decide : 192 ≤ 2 ^ 8).trans (Nat.pow_le_pow_left hir _))
        _ = (i + 1) ^ p := by rw [← pow_add]; congr 1; dsimp [p]; omega
    obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_large_dyadic_counts d p)
    let L := max J (max 1 K)
    apply (nearby_iff_wide_overlap_budget k).mpr
    refine ⟨d + (p + 1), 0, L, fun N ↦ ?_⟩
    obtain ⟨B, hpos, hsid, hcount, hmix⟩ := hB N
    let active (i j : ℕ) : Prop :=
      j / 3 < i ∧ i < j ∧ J ≤ j ∧ j ≤ N ∧ 2 ^ (j / 2) * (j + 1) ^ k < 2 ^ i
    let E (i j : ℕ) := if active i j then ambiguousMixedPairs (B i) (B j) else ∅
    have hzero i j (h : ¬ (i < j ∧ j < 3 * i)) : E i j = ∅ := by
      apply if_neg
      rintro ⟨hnear, hij, _⟩
      exact h ⟨hij, by omega⟩
    have hes i j : (E i j).card ≤ (B j).card * P i := by
      by_cases h : active i j
      swap
      · simp [E,h]
      simp only [E, if_pos h]
      obtain ⟨hnear, hij, hjJ, hjN, hwide⟩ := h
      have hs := ambiguousMixedPairs_card_add_twice_sumset (B i) (B j)
      have hm := hmix i j hnear hij hjJ hjN hwide
      have hp : j + 1 ≤ (i + 1) ^ 3 := by
        have hl : j + 1 ≤ 3 * i := by omega
        exact hl.trans (by nlinarith [Nat.zero_le (i ^ 3), Nat.zero_le (i ^ 2)])
      have hpow : (j + 1) ^ e ≤ (i + 1) ^ (3 * e) := by
        rw [pow_mul]
        exact Nat.pow_le_pow_left hp _
      calc
        _ ≤ 2 * ((B j).card * (j + 1) ^ e) := by omega
        _ ≤ 2 * ((B j).card * (i + 1) ^ (3 * e)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpow)
        _ = _ := by dsimp [P]; ring
    obtain ⟨C, hC, hCc, _, hfree⟩ :=
      select_blocks_without_bipartite_conflicts B E P hP hzero hes (N + 1)
    refine ⟨C, fun j ↦ (hC j).trans (hpos j), ?_, ?_, ?_⟩
    · intro j a ha b hb u hu v hv he
      exact hsid j a (hC j ha) b (hC j hb) u (hC j hu) v (hC j hv) he
    · intro j hj hjN
      have hjJ : J ≤ j := (le_max_left _ _).trans hj
      have hj1 : 1 ≤ j := (le_max_left _ _).trans ((le_max_right _ _).trans hj)
      have hjK : K ≤ j := (le_max_right _ _).trans ((le_max_right _ _).trans hj)
      have hd := hcount j hjJ hjN
      have hbig := hK j hjK (B j).card hd
      have hbound : Q j ≤ (B j).card := by
        apply (hQ j hj1).trans
        have hpow : (j + 1) ^ p ≤ (2 * (j + 1)) ^ p :=
          Nat.pow_le_pow_left (by omega) _
        omega
      have hc : (C j).card = (B j).card / Q j := hCc j (by omega)
      have hposC : 1 ≤ (C j).card := by
        rw [hc]
        exact (Nat.le_div_iff_mul_le (hQ0 j)).mpr (by simpa only [one_mul] using hbound)
      have hmod := Nat.mod_lt (B j).card (hQ0 j)
      have hrel : (B j).card ≤ (C j).card * (j + 1) ^ (p + 1) := by
        calc
          (B j).card = (B j).card % Q j + Q j * (C j).card := by
            rw [hc, Nat.mod_add_div]
          _ ≤ Q j + Q j * (C j).card := Nat.add_le_add_right hmod.le _
          _ = Q j * (1 + (C j).card) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ Q j * (2 * (C j).card) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ (j + 1) ^ p * ((j + 1) * (C j).card) :=
            Nat.mul_le_mul (hQ j hj1) (Nat.mul_le_mul_right _ (by omega))
          _ = _ := by rw [pow_succ]; ring
      exact dyadic_energy_count_transfer j d (p + 1) _ _ hd hrel
    · intro j hj hjN i hnear hij hwide
      have hjJ : J ≤ j := (le_max_left _ _).trans hj
      have ha : active i j := ⟨hnear, hij, hjJ, hjN, hwide⟩
      have hz : positiveDifferences (C j) ∩ positiveDifferences (C i) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        obtain ⟨hrj, hri⟩ := Finset.mem_inter.mp hr
        obtain ⟨u, hu, v, hv, hvu, hej⟩ := mem_positiveDifferences.mp hrj
        obtain ⟨a, ha', b, hb, hba, hei⟩ := mem_positiveDifferences.mp hri
        have he : (a,v) ∈ E i j := by
          simp only [E, if_pos ha]
          exact mem_ambiguousMixedPairs_of_collision (B i) (B j)
            (hC i ha') (hC i hb) (hC j hv) (hC j hu) hba.ne' (by omega)
        exact hfree i j hij a ha' v hv he
      simp [hz]

/-- A dyadic dilation trades a polynomial factor in density for a polynomial
increase in the minimum difference of a quadratic Sidon ruler. -/
private lemma exists_dense_ruler_with_polynomial_gap (k : ℕ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n, J ≤ n →
      ∃ R : Finset ℕ, R ⊆ Finset.range (2 ^ n) ∧ IsSidon (R : Set ℕ) ∧
        2 ^ n ≤ R.card ^ 2 * (n + 1) ^ (2 * (k + 6)) ∧
        ∀ a ∈ R, ∀ b ∈ R, b < a → 2 ^ (n / 2) * (n + 1) ^ k < a - b := by
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp (eventually_dyadic_pruning_budget (2 * k + 10))
  refine ⟨max 1 J₀, le_max_left _ _, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hbudget := hJ₀ n ((le_max_right _ _).trans hn)
  let M := (n + 1) ^ k
  let ell := Nat.log 2 M + 3
  have hM0 : 0 < M := by dsimp [M]; positivity
  have hMlow : M < 2 ^ (ell - 2) := by
    have he : ell - 2 = (Nat.log 2 M).succ := by dsimp [ell]; omega
    rw [he]
    exact Nat.lt_pow_succ_log_self (by decide) _
  have hMhigh : 2 ^ ell ≤ 8 * M := by
    dsimp [ell]
    rw [pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 hM0.ne')
  have hpoly : 4096 * M ^ 2 ≤ 4 * (n + 1) ^ (2 * k + 10) := by
    have hconst : 4096 ≤ 4 * (n + 1) ^ 10 :=
      (by decide : 4096 ≤ 4 * 2 ^ 10).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    calc
      _ ≤ (4 * (n + 1) ^ 10) * M ^ 2 := Nat.mul_le_mul_right _ hconst
      _ = _ := by
        dsimp [M]
        rw [← pow_mul, pow_add, mul_comm 2 k]
        ring
  have hnlen : 2 * ell + 6 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2 ^ (2 * ell + 6) = 64 * (2 ^ ell) ^ 2 := by rw [pow_add, mul_comm 2 ell, pow_mul]; ring
      _ ≤ 64 * (8 * M) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hMhigh _)
      _ = 4096 * M ^ 2 := by ring
      _ ≤ 4 * (n + 1) ^ (2 * k + 10) := hpoly
      _ ≤ 4 * (2 ^ (n / 3)) ^ 2 * (n + 1) ^ (2 * k + 10) := by
        have hpow : 1 ≤ (2 ^ (n / 3) : ℕ) ^ 2 := Nat.one_le_pow _ _ (by positivity)
        simpa only [mul_one] using
          Nat.mul_le_mul_right ((n + 1) ^ (2 * k + 10)) (Nat.mul_le_mul_left 4 hpow)
      _ ≤ _ := hbudget
  let s := n - 2 * ell
  have hs : 6 ≤ s := by dsimp [s]; omega
  obtain ⟨S, hpos, hsid, hcount, hgap⟩ := exists_dense_sidon_range_with_gap s hs
  let D : ℕ := 2 ^ (2 * ell)
  let R := S.image (fun x ↦ D * x)
  have hD : 0 < D := by dsimp [D]; positivity
  have hinj : Function.Injective (fun x : ℕ ↦ D * x) :=
    fun _ _ he ↦ Nat.eq_of_mul_eq_mul_left hD he
  have hwidth : D * 2 ^ s = (2 : ℕ) ^ n := by
    dsimp [D]
    rw [← pow_add]
    congr 1
    dsimp [s]
    omega
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (hwidth ▸ Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp (hpos hx)) hD)
  · intro a ha b hb u hu v hv he
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    rw [← Nat.mul_add, ← Nat.mul_add] at he
    rcases hsid a₀ ha₀ b₀ hb₀ u₀ hu₀ v₀ hv₀ (hinj he) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  · have hc : R.card = S.card := Finset.card_image_of_injective _ hinj
    have hDhigh : D ≤ 64 * M ^ 2 := by
      calc
        _ = (2 ^ ell) ^ 2 := by dsimp [D]; rw [mul_comm 2 ell, pow_mul]
        _ ≤ (8 * M) ^ 2 := Nat.pow_le_pow_left hMhigh _
        _ = _ := by ring
    have hconst : 2048 ≤ (n + 1) ^ 12 :=
      (by decide : 2048 ≤ 2 ^ 12).trans (Nat.pow_le_pow_left (by omega) _)
    rw [hc, ← hwidth]
    calc
      _ ≤ D * (32 * S.card ^ 2) := Nat.mul_le_mul_left _ hcount
      _ ≤ (64 * M ^ 2) * (32 * S.card ^ 2) := Nat.mul_le_mul_right _ hDhigh
      _ = S.card ^ 2 * (M ^ 2 * 2048) := by ring
      _ ≤ S.card ^ 2 * (M ^ 2 * (n + 1) ^ 12) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hconst)
      _ = _ := by
        dsimp [M]
        rw [← pow_mul, ← pow_add]
        congr 2
        omega
  · intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have hxy : y < x := (Nat.mul_lt_mul_left hD).mp hab
    have hshift : D * 2 ^ (s / 2 - 2) = 2 ^ (n / 2) * 2 ^ (ell - 2) := by
      dsimp [D]
      rw [← pow_add, ← pow_add]
      congr 1
      dsimp [s, ell] at *
      omega
    calc
      2 ^ (n / 2) * M < 2 ^ (n / 2) * 2 ^ (ell - 2) :=
        Nat.mul_lt_mul_of_pos_left hMlow (by positivity)
      _ = D * 2 ^ (s / 2 - 2) := hshift.symm
      _ ≤ D * (x - y) := Nat.mul_le_mul_left _ (hgap x hx y hy hxy).le
      _ = D * x - D * y := Nat.mul_sub_left_distrib _ _ _

/-- One host realizes the logarithmic windows of anchors separated by a
half-scale gap with polynomial slack in their widths. -/
private lemma sidon_cluster_profile_polynomially_separated_windows (k : ℕ) :
    ∃ J : ℕ, ∀ (N : ℕ) (I : Finset ℕ),
      (∀ n ∈ I, J ≤ n ∧ n ≤ N) →
      (∀ m ∈ I, ∀ n ∈ I, m < n → 2 ^ m ≤ 2 ^ (n / 2) * (n + 1) ^ k) →
      ∃ S : Finset ℕ, IsSidon (S : Set ℕ) ∧
        ∀ n ∈ I, ∀ j, 1 ≤ j → j ≤ n → 2 ^ (n - j) ≤ j + 1 → ∃ t : ℕ,
          2 ^ j ≤ (S.filter fun x ↦ t ≤ x ∧ x < t + 2 ^ j).card ^ 2 *
            (j + 1) ^ (2 * (2 * k + 13)) := by
  classical
  obtain ⟨J, _, hJ⟩ := exists_dense_ruler_with_polynomial_gap k
  refine ⟨J, fun N I hI hsep ↦ ?_⟩
  have hex n (hn : n ∈ I) := hJ n (hI n hn).1
  choose Q hQsub hQsid hQcount hQgap using hex
  let R n := if hn : n ∈ I then Q n hn else ∅
  have hr {n : ℕ} (hn : n ∈ I) : R n = Q n hn := dif_pos hn
  have hactive {n a : ℕ} (ha : a ∈ R n) : n ∈ I := by
    by_contra hn
    simp [R, hn] at ha
  have hRsub n : R n ⊆ Finset.range (2 ^ n) := by
    intro a ha
    have hn := hactive ha
    rw [hr hn] at ha
    exact hQsub n hn ha
  have hRsid n : IsSidon (R n : Set ℕ) := by
    by_cases hn : n ∈ I
    · simpa only [hr hn] using hQsid n hn
    · simp [R, hn, IsSidon]
  let C n := (R n).image (fun a ↦ a + 2 ^ n)
  have hpos n : C n ⊆ Finset.Ico (2 ^ n) (2 ^ (n + 1)) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have ha' := Finset.mem_range.mp (hRsub n ha)
    exact Finset.mem_Ico.mpr ⟨by omega, by rw [pow_succ]; omega⟩
  have hsid n : IsSidon (C n : Set ℕ) := by
    intro a ha b hb u hu v hv he
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    rcases hRsid n a₀ ha₀ b₀ hb₀ u₀ hu₀ v₀ hv₀ (by omega) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  have hcross m n (hmn : m < n) a (ha : a ∈ C m) b (hb : b ∈ C m)
      u (hu : u ∈ C n) v (hv : v ∈ C n) (hab : b < a) (hvu : v < u) :
      a - b ≠ u - v := by
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b₀, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp hv
    have hm := hactive ha₀
    have hn := hactive hu₀
    have hbound := Finset.mem_range.mp (hRsub m ha₀)
    have hgap := hQgap n hn u₀ (hr hn ▸ hu₀) v₀ (hr hn ▸ hv₀) (by omega)
    have hsmall : a₀ - b₀ < (2 : ℕ) ^ m := (Nat.sub_le _ _).trans_lt hbound
    have hlt := hsmall.trans_le (hsep m hm n hn hmn)
    omega
  let S := translatedHost N C
  refine ⟨S, (translated_host_of_separated_blocks N C hpos hsid hcross).2, ?_⟩
  intro n hn j hj hjn hdist
  let t := 2 ^ n + 2 ^ (N + 2) * clusterTag N n
  let f (x : ℕ) := x + t
  have hsub : (R n).image f ⊆ S.filter (fun x ↦ t ≤ x ∧ x < t + 2 ^ n) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have har := Finset.mem_range.mp (hRsub n ha)
    have henc : hostEncoding N n (a + 2 ^ n) = f a := by simp only [hostEncoding, f, t, Nat.add_assoc]
    have haC : a + 2 ^ n ∈ C n := Finset.mem_image_of_mem _ ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (by have := (hI n hn).2; omega), ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨a + 2 ^ n, haC, henc⟩
    · exact ⟨by dsimp [f]; omega, by dsimp [f]; omega⟩
  have hc : (R n).card ≤ (S.filter fun x ↦ t ≤ x ∧ x < t + 2 ^ n).card := by
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ (fun a b he ↦ Nat.add_right_cancel he)] at hc
  obtain ⟨u, hu⟩ := localize_cluster S t j n hjn
  have hfactor : n + 1 ≤ (j + 1) ^ 2 := by
    have hdiff := (show n - j < (2 : ℕ) ^ (n - j) from Nat.lt_two_pow_self).trans_le hdist
    calc
      _ ≤ 2 * (j + 1) := by omega
      _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
  have hcount : 2 ^ j ≤ (R n).card ^ 2 * (j + 1) ^ (2 * (2 * k + 11 + 1)) := by
    calc
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by decide) hjn
      _ ≤ (R n).card ^ 2 * (n + 1) ^ (2 * (k + 6)) := by
        rw [hr hn]
        exact hQcount n hn
      _ ≤ (R n).card ^ 2 * ((j + 1) ^ 2) ^ (2 * (k + 6)) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hfactor _)
      _ = _ := by rw [← pow_mul]; congr 2
  refine ⟨u, ?_⟩
  have hcard : (R n).card ≤ (S.filter fun x ↦ u ≤ x ∧ x < u + 2 ^ j).card * (j + 1) ^ 1 := by
    rw [pow_one, mul_comm]
    exact hc.trans (hu.trans (Nat.mul_le_mul_right _ hdist))
  simpa only [show 2 * k + 11 + 1 + 1 = 2 * k + 13 by omega] using
    dyadic_energy_count_transfer j (2 * k + 11) 1 _ _ hcount hcard

/-- The packing conclusion holds on the logarithmic windows of the stretched
anchor rulers, with no conflicts between any two of the selected scales. -/
private lemma nearby_packing_polynomially_separated_windows (k : ℕ) :
    ∃ J : ℕ, ∀ (N : ℕ) (I : Finset ℕ),
      (∀ n ∈ I, J ≤ n ∧ n ≤ N) →
      (∀ m ∈ I, ∀ n ∈ I, m < n → 2 ^ m ≤ 2 ^ (n / 2) * (n + 1) ^ k) →
      ∃ B : ℕ → Finset ℕ,
        (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
        (∀ j, IsSidon (B j : Set ℕ)) ∧
        (∀ n ∈ I, ∀ j, J ≤ j → j ≤ n → 2 ^ (n - j) ≤ j + 1 →
          2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (2 * k + 17))) ∧
        ∀ i j, i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
          b < a → v < u → a - b ≠ u - v := by
  classical
  obtain ⟨J₀, hhost⟩ := sidon_cluster_profile_polynomially_separated_windows k
  obtain ⟨J₁, hpack⟩ := cluster_packing_on_scales (2 * k + 12)
  let J := max J₀ (max 1 J₁)
  refine ⟨J, fun N I hI hsep ↦ ?_⟩
  obtain ⟨S, hS, hcluster⟩ := hhost N I
    (fun n hn ↦ ⟨(le_max_left _ _).trans (hI n hn).1, (hI n hn).2⟩) hsep
  let W := (Finset.Icc J N).filter fun j ↦ ∃ n ∈ I, j ≤ n ∧ 2 ^ (n - j) ≤ j + 1
  have hbase j (hj : j ∈ W) : max 1 J₁ ≤ j :=
    (le_max_right _ _).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
  obtain ⟨B, hpos, hsid, hc, hdiff⟩ := hpack W S hS
    (fun j hj ↦ (le_max_right _ _).trans (hbase j hj)) (fun j hj ↦ by
      obtain ⟨_, n, hn, hjn, hdist⟩ := Finset.mem_filter.mp hj
      exact hcluster n hn j ((le_max_left _ _).trans (hbase j hj)) hjn hdist)
  refine ⟨B, hpos, fun j a ha b hb u hu v hv he ↦ hsid j a ha u hu b hb v hv he, ?_, hdiff⟩
  intro n hn j hj hjn hdist
  apply hc j
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj, hjn.trans (hI n hn).2⟩, n, hn, hjn, hdist⟩

private def orderedSumPairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter fun p ↦ p.1 ≤ p.2

private lemma mem_ambiguousSumPairs_of_collision {T : Finset (ℕ × ℕ)} {p q : ℕ × ℕ}
    (hp : p ∈ T) (hq : q ∈ T) (hne : p ≠ q) (he : p.1 + p.2 = q.1 + q.2) :
    p ∈ ambiguousSumPairs T :=
  Finset.mem_filter.mpr ⟨hp, Finset.one_lt_card.mpr
    ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, q, Finset.mem_filter.mpr ⟨hq, he.symm⟩, hne⟩⟩

/-- A small deficit in distinct unordered sums permits thinning to a Sidon
subset at a cost polynomial in the deficit per vertex. -/
private lemma sidon_subset_of_ordered_sumset_budget (S : Finset ℕ) (P : ℕ)
    (hbudget : (orderedSumPairs S).card ≤
      ((orderedSumPairs S).image fun p ↦ p.1 + p.2).card + S.card * P) :
    ∃ R ⊆ S, S.card ≤ R.card * (2 * (4 * (2 * P) + 1)) ∧ IsSidon (R : Set ℕ) := by
  let U := orderedSumPairs S
  let E := (ambiguousSumPairs U).filter fun p ↦ p.1 ≠ p.2
  have hE : E.card ≤ S.card * (2 * P) := by
    have hf := Finset.card_le_card (Finset.filter_subset (s := ambiguousSumPairs U)
      (fun p ↦ p.1 ≠ p.2))
    have hc := ambiguousSumPairs_card_add_twice_image U
    change E.card ≤ (ambiguousSumPairs U).card at hf
    change U.card ≤ (U.image fun p ↦ p.1 + p.2).card + S.card * P at hbudget
    rw [← mul_assoc, mul_comm S.card 2, mul_assoc]
    omega
  obtain ⟨R, hR, hc, hf⟩ :=
    thin_avoiding_pairs S E (2 * P) (fun p hp ↦ (Finset.mem_filter.mp hp).2) hE
  refine ⟨R, hR, hc, (Set.isSidon_iff_le _).mpr ?_⟩
  intro a ha b hb c hc' d hd hab hcd he
  have hp : (a,b) ∈ U := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hR ha,hR hb⟩, hab⟩
  have hq : (c,d) ∈ U := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hR hc',hR hd⟩, hcd⟩
  by_cases hpq : (a,b) = (c,d)
  · exact ⟨congrArg Prod.fst hpq, congrArg Prod.snd hpq⟩
  exfalso
  by_cases hab' : a = b
  · have hcd' : c ≠ d := by
      intro h
      apply hpq
      exact Prod.ext (by dsimp; omega) (by dsimp; omega)
    have hq' : (c,d) ∈ E := Finset.mem_filter.mpr
      ⟨mem_ambiguousSumPairs_of_collision hq hp (fun h ↦ hpq h.symm) he.symm, hcd'⟩
    exact hf (c,d) hq' hc' hd
  · have hp' : (a,b) ∈ E := Finset.mem_filter.mpr
      ⟨mem_ambiguousSumPairs_of_collision hp hq hpq he, hab'⟩
    exact hf (a,b) hp' ha hb

private lemma image_deficit_mono {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (S T : Finset α) (hsub : S ⊆ T) :
    S.card + (T.image f).card ≤ T.card + (S.image f).card := by
  have hcover : T.image f ⊆ (T \ S).image f ∪ S.image f := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    by_cases h : a ∈ S
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨ha,h⟩))
  have hc := (Finset.card_le_card hcover).trans
    (Finset.card_union_le ((T \ S).image f) (S.image f))
  have hbound := hc.trans (Nat.add_le_add_right
    (Finset.card_image_le (s := T \ S) (f := f)) _)
  rw [Finset.card_sdiff_of_subset hsub] at hbound
  have := Finset.card_le_card hsub
  omega

/-- Both the Sidon condition on a block and the cross-scale condition can be
replaced by bounds on the deficits in their respective sumsets. -/
private lemma nearby_iff_approximate_sumset_budgets (k : ℕ) :
    H1 ↔ ∃ d e f J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, J ≤ j → j ≤ N →
        2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧
      (∀ j, J ≤ j → j ≤ N → (orderedSumPairs (B j)).card ≤
        ((orderedSumPairs (B j)).image (fun p ↦ p.1 + p.2)).card + (B j).card * (j + 1) ^ e) ∧
      ∀ i j, j / 3 < i → i < j → J ≤ j → j ≤ N →
        2 ^ (j / 2) * (j + 1) ^ k < 2 ^ i →
        (B i).card * (B j).card ≤
          ((B i ×ˢ B j).image (fun p ↦ p.1 + p.2)).card + (B j).card * (j + 1) ^ f := by
  classical
  constructor
  · intro h
    obtain ⟨d, f, J, hB⟩ := (nearby_iff_mixed_sumset_budget k).mp h
    refine ⟨d, 0, f, J, fun N ↦ ?_⟩
    obtain ⟨B, hpos, hsid, hc, hm⟩ := hB N
    refine ⟨B, hpos, hc, ?_, hm⟩
    intro j _ _
    have hinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2) (↑(orderedSumPairs (B j)) : Set (ℕ × ℕ)) := by
      intro ⟨a,b⟩ hp ⟨c,d⟩ hq he
      obtain ⟨hp', hab⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      obtain ⟨hq', hcd⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp'
      obtain ⟨hc,hd⟩ := Finset.mem_product.mp hq'
      obtain ⟨h₁,h₂⟩ := (Set.isSidon_iff_le _).mp (hsid j) a ha b hb c hc d hd hab hcd he
      exact Prod.ext h₁ h₂
    rw [Finset.card_image_of_injOn hinj]
    exact Nat.le_add_right _ _
  · rintro ⟨d, e, f, J, hB⟩
    let L := max J 1
    let p := e + 5
    apply (nearby_iff_mixed_sumset_budget k).mpr
    refine ⟨d + p, f + p, L, fun N ↦ ?_⟩
    obtain ⟨B, hpos, hd, hs, hm⟩ := hB N
    have hex j (hj : L ≤ j ∧ j ≤ N) := sidon_subset_of_ordered_sumset_budget
      (B j) ((j + 1) ^ e) (hs j ((le_max_left _ _).trans hj.1) hj.2)
    choose R hR hRc hRsid using hex
    let C j := if hj : L ≤ j ∧ j ≤ N then R j hj else ∅
    have ht j (hj : L ≤ j ∧ j ≤ N) : C j = R j hj := dif_pos hj
    have hC j : C j ⊆ B j := by
      by_cases hj : L ≤ j ∧ j ≤ N
      · rw [ht j hj]
        exact hR j hj
      · simp [C, hj]
    have hsid j : IsSidon (C j : Set ℕ) := by
      by_cases hj : L ≤ j ∧ j ≤ N
      · simpa only [ht j hj] using hRsid j hj
      · simp [C, hj, IsSidon]
    have hcloss j (hj : L ≤ j) (hjN : j ≤ N) : (B j).card ≤ (C j).card * (j + 1) ^ p := by
      have hj2 : 2 ≤ j + 1 := by have := (le_max_right _ _).trans hj; omega
      have hpow : 1 ≤ (j + 1) ^ e := Nat.one_le_pow _ _ (by positivity)
      rw [ht j ⟨hj, hjN⟩]
      refine (hRc j ⟨hj, hjN⟩).trans (Nat.mul_le_mul_left _ ?_)
      calc
        _ ≤ 18 * (j + 1) ^ e := by omega
        _ ≤ (j + 1) ^ 5 * (j + 1) ^ e := Nat.mul_le_mul_right _
          ((by decide : 18 ≤ 2 ^ 5).trans (Nat.pow_le_pow_left hj2 _))
        _ = _ := by dsimp [p]; rw [← pow_add, Nat.add_comm 5 e]
    refine ⟨C, fun j ↦ (hC j).trans (hpos j), hsid, ?_, ?_⟩
    · intro j hj hjN
      exact dyadic_energy_count_transfer j d p _ _
        (hd j ((le_max_left _ _).trans hj) hjN) (hcloss j hj hjN)
    · intro i j hnear hij hj hjN hwide
      have hprod : C i ×ˢ C j ⊆ B i ×ˢ B j := by
        intro a ha
        obtain ⟨hi', hj'⟩ := Finset.mem_product.mp ha
        exact Finset.mem_product.mpr ⟨hC i hi', hC j hj'⟩
      have hmono := image_deficit_mono (fun a : ℕ × ℕ ↦ a.1 + a.2) _ _ hprod
      simp only [Finset.card_product] at hmono
      have hbudget := hm i j hnear hij ((le_max_left _ _).trans hj) hjN hwide
      have hbound : (B j).card * (j + 1) ^ f ≤ (C j).card * (j + 1) ^ (f + p) := by
        calc
          _ ≤ ((C j).card * (j + 1) ^ p) * (j + 1) ^ f :=
            Nat.mul_le_mul_right _ (hcloss j hj hjN)
          _ = _ := by rw [pow_add]; ring
      omega

end Erdos1191HostPacking

theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_ii_R2.H1 := by
  apply Erdos1191HostPacking.nearby_iff_adaptive_cyclic_sidon_profile.mpr
  sorry
