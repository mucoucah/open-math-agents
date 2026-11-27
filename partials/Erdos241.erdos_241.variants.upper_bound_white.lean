import FormalConjectures.ErdosProblems.«241»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! Signed triples and smoothed pair energy for Erdős Problem 241. -/

-- Problem: Erdős Problem 241 — upper bound white
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/241.lean:96 (declaration Erdos241.erdos_241.variants.upper_bound_white)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.White241

open Finset

/-- The multiset formulation of the B₃ condition on a finite set. -/
def IsB3 (A : Finset ℕ) : Prop :=
  ∀ m n : Multiset ℕ, m.card = 3 → n.card = 3 →
    (∀ x ∈ m, x ∈ A) → (∀ x ∈ n, x ∈ A) → m.sum = n.sum → m = n

/-- A nondegenerate signed sum determines the negative term and the unordered positive pair. -/
lemma signedTriple_unique {A : Finset ℕ} (hA : IsB3 A)
    {a b c a' b' c' : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (ha' : a' ∈ A) (hb' : b' ∈ A) (hc' : c' ∈ A)
    (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≤ b) (hab' : a' ≤ b')
    (hs : (a : ℤ) + b - c = (a' : ℤ) + b' - c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have hs' : a + b + c' = a' + b' + c := by omega
  have hm := hA ({a, b, c'} : Multiset ℕ) {a', b', c}
    (by simp) (by simp)
    (by simpa using And.intro ha (And.intro hb hc'))
    (by simpa using And.intro ha' (And.intro hb' hc))
    (by simpa [add_assoc] using hs')
  have hcc : c = c' := by
    have h : c ∈ ({a, b, c'} : Multiset ℕ) := by rw [hm]; simp
    simpa [hca, hcb] using h
  subst c'
  have hm' : ({a, b} : Multiset ℕ) = {a', b'} := by
    have hp : ({a, b} : Multiset ℕ) + {c} = {a', b'} + {c} := by
      convert hm using 1 <;> simp [Multiset.cons_add, Multiset.singleton_add]
    exact add_right_cancel hp
  have h₁ : a = a' ∨ a = b' := by
    have h : a ∈ ({a', b'} : Multiset ℕ) := by rw [← hm']; simp
    simpa using h
  have h₂ : a' = a ∨ a' = b := by
    have h : a' ∈ ({a, b} : Multiset ℕ) := by rw [hm']; simp
    simpa using h
  omega

private abbrev Triple := ℕ × ℕ × ℕ

private def triples (A : Finset ℕ) : Finset Triple := A ×ˢ (A ×ˢ A)

private def signedSum (p : Triple) : ℤ := (p.1 : ℤ) + p.2.1 - p.2.2

private def nondegenerate (p : Triple) : Prop := p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1

private instance (p : Triple) : Decidable (nondegenerate p) := by
  unfold nondegenerate
  infer_instance

private def swap (p : Triple) : Triple := (p.2.1, p.1, p.2.2)

private def ordered (p : Triple) : Prop := p.1 ≤ p.2.1

private instance (p : Triple) : Decidable (ordered p) := by
  unfold ordered
  infer_instance

private def signature (e : ℕ) (p : Triple) : ℤ × Bool :=
  (signedSum p - e, decide (ordered p))

private lemma ordered_eq_of_signedSum_eq {A : Finset ℕ} (hA : IsB3 A)
    {p q : Triple} (hp : p ∈ triples A) (hq : q ∈ triples A)
    (hd : nondegenerate p) (hop : ordered p) (hoq : ordered q)
    (h : signedSum p = signedSum q) : p = q := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨a', b', c'⟩ := q
  simp only [triples, mem_product] at hp hq
  obtain ⟨rfl, rfl, rfl⟩ := signedTriple_unique hA hp.1 hp.2.1 hp.2.2
    hq.1 hq.2.1 hq.2.2 hd.1 hd.2 hop hoq h
  rfl

private lemma swap_mem_triples {A : Finset ℕ} {p : Triple} (hp : p ∈ triples A) :
    swap p ∈ triples A := by
  simp only [triples, mem_product, swap] at hp ⊢
  exact ⟨hp.2.1, hp.1, hp.2.2⟩

private lemma signedSum_swap (p : Triple) : signedSum (swap p) = signedSum p := by
  simp [signedSum, swap, add_comm]

private lemma signature_injOn {A : Finset ℕ} (hA : IsB3 A) (e : ℕ) :
    Set.InjOn (signature e) ↑((triples A).filter nondegenerate) := by
  intro p hp q hq heq
  obtain ⟨hp, hd⟩ := mem_filter.mp hp
  obtain ⟨hq, hdq⟩ := mem_filter.mp hq
  have h : signedSum p = signedSum q := by
    simpa [signature] using congrArg Prod.fst heq
  have ho : ordered p ↔ ordered q := by
    simpa [signature] using congrArg Prod.snd heq
  by_cases hop : ordered p
  · exact ordered_eq_of_signedSum_eq hA hp hq hd hop (ho.mp hop) h
  · have hoq : ¬ ordered q := mt ho.mpr hop
    have hswap : swap p = swap q := ordered_eq_of_signedSum_eq hA
      (swap_mem_triples hp) (swap_mem_triples hq) ⟨hd.2, hd.1⟩
      (le_of_not_ge hop) (le_of_not_ge hoq) (by simpa only [signedSum_swap] using h)
    exact congrArg swap hswap

private lemma card_degenerate_le (A : Finset ℕ) :
    #((triples A).filter fun p ↦ ¬ nondegenerate p) ≤ 2 * #A ^ 2 := by
  classical
  have hinj : Set.InjOn (fun p : Triple ↦ ((p.1, p.2.1), decide (p.2.2 = p.1)))
      ↑((triples A).filter fun p ↦ ¬ nondegenerate p) := by
    rintro ⟨a,b,c⟩ hp ⟨a',b',c'⟩ hq h
    have hab : (a,b) = (a',b') := congrArg Prod.fst h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    have hc : c = a ∨ c = b := by
      have h := (mem_filter.mp hp).2
      change ¬ (c ≠ a ∧ c ≠ b) at h
      tauto
    have hc' : c' = a ∨ c' = b := by
      have h := (mem_filter.mp hq).2
      change ¬ (c' ≠ a ∧ c' ≠ b) at h
      tauto
    have hca : c = a ↔ c' = a := by simpa using congrArg Prod.snd h
    by_cases h : c = a
    · rw [h, hca.mp h]
    · rw [hc.resolve_left h, hc'.resolve_left (mt hca.mpr h)]
  calc
    _ ≤ #((A ×ˢ A) ×ˢ (univ : Finset Bool)) :=
      card_le_card_of_injOn _ (by
        intro p hp
        have ht := (mem_filter.mp hp).1
        simp only [triples, mem_product] at ht
        exact mem_product.mpr ⟨mem_product.mpr ⟨ht.1, ht.2.1⟩, mem_univ _⟩) hinj
    _ = _ := by simp [card_product, pow_two, mul_comm]

/-- Signed triples already imply a cubic bound up to lower order terms. -/
lemma card_cube_le {A : Finset ℕ} {N : ℕ} (hA : IsB3 A) (hAN : A ⊆ Icc 1 N) :
    #A ^ 3 ≤ 2 * (3 * N + 1) + 2 * #A ^ 2 := by
  have hnd : #((triples A).filter nondegenerate) ≤ 2 * (3 * N + 1) := by
    calc
      _ ≤ #((Icc (-(N : ℤ)) (2 * N)) ×ˢ (univ : Finset Bool)) := by
        apply card_le_card_of_injOn (signature 0) _ (signature_injOn hA 0)
        intro p hp
        have ht := (mem_filter.mp hp).1
        simp only [triples, mem_product] at ht
        have ha := (mem_Icc.mp (hAN ht.1)).2
        have hb := (mem_Icc.mp (hAN ht.2.1)).2
        have hc := (mem_Icc.mp (hAN ht.2.2)).2
        refine mem_product.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, mem_univ _⟩ <;>
          simp only [signature, signedSum, Nat.cast_zero, sub_zero] <;> omega
      _ = _ := by
        rw [card_product, Int.card_Icc, show #(univ : Finset Bool) = 2 by decide]
        omega
  have hcard : #A ^ 3 = #(triples A) := by simp [triples, card_product, pow_succ, mul_assoc]
  rw [hcard, ← card_filter_add_card_filter_not nondegenerate]
  exact Nat.add_le_add hnd (card_degenerate_le A)

/-- Weighted counts of equal pair sums up to a shift. -/
noncomputable def energy (A : Finset ℕ) (w : ℤ → ℝ) : ℝ :=
  ∑ e ∈ A, ∑ p ∈ triples A, w (signedSum p - e)

/-- Nondegenerate triples cost at most two per shift and fixed fourth element.
All degenerate triples can be bounded using the maximum weight. -/
lemma energy_le {A : Finset ℕ} (hA : IsB3 A) {D : Finset ℤ} {w : ℤ → ℝ} {M : ℝ}
    (hnonneg : ∀ d, 0 ≤ w d) (hsupport : ∀ d ∉ D, w d = 0)
    (hmass : ∑ d ∈ D, w d ≤ 1) (hmax : ∀ d, w d ≤ M) (hM : 0 ≤ M) :
    energy A w ≤ 2 * (#A : ℝ) + 2 * (#A : ℝ) ^ 3 * M := by
  classical
  have hnd (e : ℕ) : ∑ p ∈ (triples A).filter nondegenerate, w (signedSum p - e) ≤ 2 := by
    let T := (triples A).filter nondegenerate
    let U := T.filter fun p ↦ (signature e p).1 ∈ D
    have hUT : U ⊆ T := filter_subset _ _
    have hsub : U.image (signature e) ⊆ D ×ˢ (univ : Finset Bool) := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      exact mem_product.mpr ⟨(mem_filter.mp hp).2, mem_univ _⟩
    change ∑ p ∈ T, w (signature e p).1 ≤ 2
    calc
      _ = ∑ p ∈ U, w (signature e p).1 := by
        symm
        apply sum_subset hUT
        intro p hp hpu
        exact hsupport _ (fun hd ↦ hpu (mem_filter.mpr ⟨hp, hd⟩))
      _ = ∑ q ∈ U.image (signature e), w q.1 := by
        rw [sum_image (fun p hp q hq ↦ signature_injOn hA e (hUT hp) (hUT hq))]
      _ ≤ ∑ q ∈ D ×ˢ (univ : Finset Bool), w q.1 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ ↦ hnonneg q.1)
      _ = 2 * ∑ d ∈ D, w d := by simp [sum_product, nsmul_eq_mul, ← mul_sum]
      _ ≤ 2 := by linarith
  have hd (e : ℕ) : ∑ p ∈ (triples A).filter (fun p ↦ ¬ nondegenerate p),
      w (signedSum p - e) ≤ 2 * (#A : ℝ) ^ 2 * M := by
    calc
      _ ≤ ∑ _p ∈ (triples A).filter (fun p ↦ ¬ nondegenerate p), M :=
        sum_le_sum fun p _ ↦ hmax (signedSum p - e)
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_degenerate_le A) hM
  unfold energy
  calc
    _ ≤ ∑ _e ∈ A, (2 + 2 * (#A : ℝ) ^ 2 * M) := by
      apply sum_le_sum
      intro e _
      rw [← sum_filter_add_sum_filter_not (triples A) nondegenerate]
      exact add_le_add (hnd e) (hd e)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

/-- The extremal cardinality is attained by a set satisfying the B₃ condition. -/
lemma exists_maximizer (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ IsB3 A ∧ #A = Erdos241.f N 3 := by
  classical
  let candidates := (Icc 1 N).powerset.filter IsB3
  have hne : candidates.Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), ?_⟩⟩
    intro m n hm hn hmem
    have h : m = 0 := by
      by_contra h
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h
      simpa using hmem x hx
    simp [h] at hm
  obtain ⟨A, hA, hcard⟩ := exists_mem_eq_sup candidates hne card
  obtain ⟨hAN, hB⟩ := mem_filter.mp hA
  exact ⟨A, mem_powerset.mp hAN, hB, hcard.symm⟩

private def boxPairs (H : ℕ) := range H ×ˢ range H

private def boxDiff (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2

/-- Distribution of the difference of two independent uniform points in `[0,H)`. -/
noncomputable def boxWeight (H : ℕ) (d : ℤ) : ℝ :=
  (#((boxPairs H).filter fun p ↦ boxDiff p = d) : ℝ) / (H : ℝ) ^ 2

private lemma boxDiff_mem {H : ℕ} {p : ℕ × ℕ} (hp : p ∈ boxPairs H) :
    boxDiff p ∈ Icc (-(H : ℤ)) H := by
  obtain ⟨ha, hb⟩ := mem_product.mp hp
  have ha' := mem_range.mp ha
  have hb' := mem_range.mp hb
  simp only [boxDiff, mem_Icc]
  omega

lemma energy_boxWeight_le {A : Finset ℕ} (hA : IsB3 A) {H : ℕ} (hH : 0 < H) :
    energy A (boxWeight H) ≤ 2 * (#A : ℝ) + 2 * (#A : ℝ) ^ 3 / H := by
  have hH' : 0 < (H : ℝ) := by exact_mod_cast hH
  rw [div_eq_mul_inv]
  apply energy_le hA (D := Icc (-(H : ℤ)) H) (fun _ ↦ by unfold boxWeight; positivity)
  · intro d hd
    have h : ((boxPairs H).filter fun p ↦ boxDiff p = d) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hEq := (mem_filter.mp hp).2
      rw [← hEq] at hd
      exact hd (boxDiff_mem (mem_filter.mp hp).1)
    simp [boxWeight, h]
  · have hcard := card_eq_sum_card_fiberwise (fun _ hp ↦ boxDiff_mem (H := H) hp)
    have hcard' : (∑ d ∈ Icc (-(H : ℤ)) H,
        (#((boxPairs H).filter fun p ↦ boxDiff p = d) : ℝ)) = (H : ℝ) ^ 2 := by
      exact_mod_cast (by simpa [boxPairs, card_product, pow_two] using hcard.symm :
        (∑ d ∈ Icc (-(H : ℤ)) H, #((boxPairs H).filter fun p ↦ boxDiff p = d)) = H ^ 2)
    simp only [boxWeight, ← sum_div, hcard']
    exact (div_self (pow_ne_zero _ hH'.ne')).le
  · intro d
    have hcard : #((boxPairs H).filter fun p ↦ boxDiff p = d) ≤ #(range H) := by
      apply card_le_card_of_injOn Prod.fst
      · intro p hp
        exact (mem_product.mp (mem_filter.mp hp).1).1
      · intro p hp q hq h
        have h₁ := (mem_filter.mp hp).2
        have h₂ := (mem_filter.mp hq).2
        have heq : p.2 = q.2 := by
          simp only [boxDiff] at h₁ h₂
          omega
        exact Prod.ext h heq
    rw [card_range] at hcard
    have hcast : (#((boxPairs H).filter fun p ↦ boxDiff p = d) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast hcard
    apply (div_le_div_of_nonneg_right hcast (by positivity)).trans
    rw [pow_two, div_mul_eq_div_div, div_self hH'.ne', one_div]
  · positivity

private lemma cube_root_pow {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma card_le_four_cbrt {A : Finset ℕ} {N : ℕ} (hA : IsB3 A) (hAN : A ⊆ Icc 1 N)
    (hN : 1 ≤ N) : (#A : ℝ) ≤ 4 * (N : ℝ) ^ ((1 : ℝ) / 3) := by
  have hN' : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : 1 ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Real.one_le_rpow hN' (by norm_num)
  by_cases h : (#A : ℝ) ≤ 4
  · linarith
  have hk : 0 ≤ (#A : ℝ) := by positivity
  have hbound : (#A : ℝ) ^ 3 ≤ 2 * (3 * (N : ℝ) + 1) + 2 * (#A : ℝ) ^ 2 := by
    exact_mod_cast card_cube_le hA hAN
  have hlow := mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (sq_nonneg (#A : ℝ))
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity)
  rw [mul_pow, cube_root_pow (by positivity)]
  nlinarith

/-- The finite energy lower bound needed for the asymptotic argument. -/
def BoxEnergyLower (c : ℝ) : Prop :=
  ∀ (N H : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → 0 < H →
    c * (#A : ℝ) ^ 4 / ((N : ℝ) + H) ≤ energy A (boxWeight H)

private lemma cube_le_of_boxEnergyLower {c : ℝ} (hc : 0 < c) (hLower : BoxEnergyLower c)
    {N H : ℕ} {A : Finset ℕ} (hAN : A ⊆ Icc 1 N) (hA : IsB3 A) (hH : 0 < H) :
    (#A : ℝ) ^ 3 ≤ (2 / c) * ((N : ℝ) + H) * (1 + (#A : ℝ) ^ 2 / H) := by
  by_cases hEmpty : A = ∅
  · simp only [hEmpty, card_empty, Nat.cast_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)]
    positivity
  have hk : 0 < (#A : ℝ) := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hEmpty)
  have hH' : 0 < (H : ℝ) := by exact_mod_cast hH
  have hNH : 0 < (N : ℝ) + H := by positivity
  have h := (div_le_iff₀ hNH).mp ((hLower N H A hAN hH).trans (energy_boxWeight_le hA hH))
  apply le_of_mul_le_mul_left _ (mul_pos hc hk)
  calc
    _ = c * (#A : ℝ) ^ 4 := by ring
    _ ≤ (2 * (#A : ℝ) + 2 * (#A : ℝ) ^ 3 / H) * ((N : ℝ) + H) := h
    _ = _ := by field_simp [hc.ne']

open Filter Topology
open scoped Asymptotics

/-- A lower bound for box-smoothed energy gives the desired cube-root asymptotic. -/
lemma asymptotic_of_boxEnergyLower {c : ℝ} (hc : 0 < c) (hLower : BoxEnergyLower c) :
    ∃ ε : ℕ → ℝ, ε =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ N in atTop, (Erdos241.f N 3 : ℝ) ≤
        ((2 / c) ^ ((1 : ℝ) / 3) + ε N) * (N : ℝ) ^ ((1 : ℝ) / 3) := by
  let z (N : ℕ) : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 6)
  let B (N : ℕ) : ℝ := (2 / c) * (1 + 2 * z N) * (1 + 16 * z N)
  refine ⟨fun N ↦ (B N) ^ ((1 : ℝ) / 3) - (2 / c) ^ ((1 : ℝ) / 3), ?_, ?_⟩
  · apply (Asymptotics.isLittleO_one_iff ℝ).mpr
    have hz : Tendsto z atTop (𝓝 0) := by
      simpa only [z, neg_div, Function.comp_def] using (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 6)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hB : Tendsto B atTop (𝓝 (2 / c)) := by
      have h₁ : Tendsto (fun N ↦ 1 + 2 * z N) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hz.const_mul 2)
      have h₂ : Tendsto (fun N ↦ 1 + 16 * z N) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hz.const_mul 16)
      simpa [B] using (h₁.const_mul (2 / c)).mul h₂
    simpa using (hB.rpow_const (p := (1 : ℝ) / 3) (Or.inr (by norm_num))).sub_const
      ((2 / c) ^ ((1 : ℝ) / 3))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    obtain ⟨A, hAN, hA, hext⟩ := exists_maximizer N
    rw [← hext, add_sub_cancel]
    let t : ℝ := (N : ℝ) ^ ((5 : ℝ) / 6)
    let H : ℕ := ⌈t⌉₊
    have hN' : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hNp : 0 < (N : ℝ) := by positivity
    have ht : 1 ≤ t := Real.one_le_rpow hN' (by norm_num)
    have htH : t ≤ (H : ℝ) := Nat.le_ceil t
    have hHp : 0 < (H : ℝ) := by linarith
    have hH : 0 < H := by exact_mod_cast hHp
    have hz : 0 ≤ z N := by dsimp [z]; positivity
    have hHupper : (N : ℝ) + H ≤ (N : ℝ) * (1 + 2 * z N) := by
      have hceil := (Nat.ceil_lt_add_one (by linarith : 0 ≤ t)).le
      have htz : (N : ℝ) * z N = t := by
        have h := (Real.rpow_add hNp 1 (-(1 : ℝ) / 6)).symm
        norm_num at h
        simpa only [z, t, neg_div] using h
      rw [mul_add, mul_one, show (N : ℝ) * (2 * z N) = 2 * ((N : ℝ) * z N) by ring, htz]
      linarith
    have hsq : (#A : ℝ) ^ 2 / H ≤ 16 * z N := by
      have hcard := pow_le_pow_left₀ (by positivity : 0 ≤ (#A : ℝ))
        (card_le_four_cbrt hA hAN hN) 2
      have hpow : ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) = t * z N := by
        rw [← Real.rpow_mul_natCast hNp.le]
        change (N : ℝ) ^ _ = (N : ℝ) ^ ((5 : ℝ) / 6) * (N : ℝ) ^ (-(1 : ℝ) / 6)
        rw [← Real.rpow_add hNp]
        norm_num
      rw [mul_pow, hpow] at hcard
      apply (div_le_iff₀ hHp).mpr
      calc
        _ ≤ 16 * t * z N := by simpa only [show (4 : ℝ) ^ (2 : ℕ) = 16 by norm_num, mul_assoc] using hcard
        _ ≤ _ := by nlinarith [mul_nonneg hz (sub_nonneg.mpr htH)]
    have hB : 0 ≤ B N := by dsimp [B]; positivity
    apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity)
    rw [mul_pow, cube_root_pow hB, cube_root_pow hNp.le]
    calc
      _ ≤ (2 / c) * ((N : ℝ) + H) * (1 + (#A : ℝ) ^ 2 / H) :=
        cube_le_of_boxEnergyLower hc hLower hAN hA hH
      _ ≤ (2 / c) * ((N : ℝ) * (1 + 2 * z N)) * (1 + 16 * z N) := by gcongr
      _ = _ := by dsimp [B]; ring

open MeasureTheory
open scoped Convolution

private noncomputable def cell (H a x : ℝ) : ℝ :=
  (Set.Icc a (a + H)).indicator (fun _ ↦ 1) x

private lemma cell_nonneg (H a x : ℝ) : 0 ≤ cell H a x := by
  classical
  by_cases hx : x ∈ Set.Icc a (a + H) <;> simp [cell, hx]

private lemma cell_le_one (H a x : ℝ) : cell H a x ≤ 1 := by
  classical
  by_cases hx : x ∈ Set.Icc a (a + H) <;> simp [cell, hx]

private lemma integrable_cell (H a : ℝ) : Integrable (cell H a) :=
  (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])).integrable_indicator
    measurableSet_Icc

private lemma integral_cell {H : ℝ} (hH : 0 ≤ H) (a : ℝ) : (∫ x, cell H a x) = H := by
  change (∫ x, (Set.Icc a (a + H)).indicator (fun _ ↦ (1 : ℝ)) x) = H
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc_of_le (by linarith)]
  ring

private lemma cell_mul_eq (H s t : ℝ) : (fun x ↦ cell H s x * cell H t x) =
    (Set.Icc (max s t) (min (s + H) (t + H))).indicator (fun _ ↦ (1 : ℝ)) := by
  classical
  funext x
  have hmem : x ∈ Set.Icc (max s t) (min (s + H) (t + H)) ↔
      x ∈ Set.Icc s (s + H) ∧ x ∈ Set.Icc t (t + H) := by
    simp only [Set.mem_Icc, max_le_iff, le_min_iff]
    tauto
  by_cases h₁ : x ∈ Set.Icc s (s + H) <;> by_cases h₂ : x ∈ Set.Icc t (t + H) <;>
    simp [cell, hmem, h₁, h₂]

private lemma integrable_cell_mul (H s t : ℝ) : Integrable (fun x ↦ cell H s x * cell H t x) := by
  rw [cell_mul_eq]
  exact (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])).integrable_indicator
    measurableSet_Icc

private lemma card_boxDiff (H : ℕ) (s t : ℤ) :
    #((boxPairs H).filter fun p ↦ boxDiff p = s - t) =
      #(Ico (max s t) (min (s + H) (t + H))) := by
  apply card_bij (fun p _ ↦ s + (p.2 : ℤ))
  · intro p hp
    have ⟨hp, hd⟩ := mem_filter.mp hp
    have ⟨ha, hb⟩ := mem_product.mp hp
    have ha' := mem_range.mp ha
    have hb' := mem_range.mp hb
    unfold boxDiff at hd
    simp only [mem_Ico, max_le_iff, lt_min_iff]
    omega
  · intro p hp q hq heq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    unfold boxDiff at hp' hq'
    apply Prod.ext <;> omega
  · intro x hx
    simp only [mem_Ico, max_le_iff, lt_min_iff] at hx
    let p : ℕ × ℕ := ((x - t).toNat, (x - s).toNat)
    refine ⟨p, ?_, ?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩, ?_⟩ <;>
        dsimp [p, boxDiff] <;> omega
    · dsimp [p]
      omega

private lemma integral_cell_mul (H : ℕ) (s t : ℤ) :
    (∫ x, cell H s x * cell H t x) =
      (#((boxPairs H).filter fun p ↦ boxDiff p = s - t) : ℝ) := by
  rw [card_boxDiff, Int.card_Ico, cell_mul_eq, integral_indicator_const _ measurableSet_Icc,
    smul_eq_mul, mul_one, Real.volume_real_Icc, max_comm]
  rw [← Int.cast_natCast (min (s + (H : ℤ)) (t + H) - max s t).toNat, Int.toNat_eq_max]
  push_cast
  exact max_comm _ _

private noncomputable def sumCells {ι : Type*} (P : Finset ι) (s : ι → ℝ) (H x : ℝ) : ℝ :=
  ∑ p ∈ P, cell H (s p) x

private lemma sumCells_nonneg {ι : Type*} (P : Finset ι) (s : ι → ℝ) (H x : ℝ) :
    0 ≤ sumCells P s H x := sum_nonneg fun p _ ↦ cell_nonneg H (s p) x

private lemma sumCells_le_card {ι : Type*} (P : Finset ι) (s : ι → ℝ) (H x : ℝ) :
    sumCells P s H x ≤ (#P : ℝ) := by
  simpa [sumCells] using (sum_le_sum fun p (_ : p ∈ P) ↦ cell_le_one H (s p) x)

private lemma integrable_sumCells {ι : Type*} (P : Finset ι) (s : ι → ℝ) (H : ℝ) :
    Integrable (sumCells P s H) := integrable_finsetSum P fun p _ ↦ integrable_cell H (s p)

private lemma integral_sumCells {ι : Type*} (P : Finset ι) (s : ι → ℝ) {H : ℝ} (hH : 0 ≤ H) :
    (∫ x, sumCells P s H x) = (#P : ℝ) * H := by
  unfold sumCells
  rw [integral_finsetSum P (fun p _ ↦ integrable_cell H (s p))]
  simp [integral_cell hH, nsmul_eq_mul]

private lemma integral_sumCells_sq {ι : Type*} (P : Finset ι) (s : ι → ℤ) (H : ℕ) :
    (∫ x, sumCells P (fun p ↦ (s p : ℝ)) H x ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P, (#((boxPairs H).filter fun u ↦ boxDiff u = s p - s q) : ℝ) := by
  have h (x : ℝ) : sumCells P (fun p ↦ (s p : ℝ)) H x ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, cell H (s p) x * cell H (s q) x := by
    rw [pow_two, sumCells, sum_mul]
    simp only [mul_sum]
  simp_rw [h]
  rw [integral_finsetSum P (fun p _ ↦ integrable_finsetSum P (fun q _ ↦ integrable_cell_mul H (s p) (s q)))]
  apply sum_congr rfl
  intro p _
  rw [integral_finsetSum P (fun q _ ↦ integrable_cell_mul H (s p) (s q))]
  simp only [integral_cell_mul]

private def pairCenter (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) + p.2

private lemma energy_eq_integral_sumCells_sq (A : Finset ℕ) (H : ℕ) :
    energy A (boxWeight H) =
      (∫ x, sumCells (A ×ˢ A) (fun p ↦ (pairCenter p : ℝ)) H x ^ 2) / (H : ℝ) ^ 2 := by
  simp only [integral_sumCells_sq, energy, triples, sum_product, boxWeight, sum_div]
  let F (a b c e : ℕ) : ℝ :=
    (#((boxPairs H).filter fun u ↦ boxDiff u = pairCenter (a,b) - pairCenter (c,e)) : ℝ) / (H : ℝ) ^ 2
  have hF (a b c e : ℕ) : signedSum (a,b,c) - e = pairCenter (a,b) - pairCenter (c,e) := by
    simp only [signedSum, pairCenter]
    omega
  simp_rw [hF]
  change (∑ e ∈ A, ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A, F a b c e) =
    ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A, ∑ e ∈ A, F a b c e
  rw [sum_comm (f := fun e a ↦ ∑ b ∈ A, ∑ c ∈ A, F a b c e)]
  apply sum_congr rfl
  intro a _
  rw [sum_comm (f := fun e b ↦ ∑ c ∈ A, F a b c e)]
  apply sum_congr rfl
  intro b _
  exact sum_comm

private lemma cell_translate (H a x : ℝ) : cell H a x = cell H 0 (x - a) := by
  classical
  have hmem : x ∈ Set.Icc a (a + H) ↔ x - a ∈ Set.Icc (0 : ℝ) H := by
    simp only [Set.mem_Icc]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  by_cases h : x ∈ Set.Icc a (a + H)
  · simp [cell, h, hmem.mp h]
  · simp [cell, h, mt hmem.mpr h]

private lemma integrable_cell_shift_mul (H a b x : ℝ) :
    Integrable (fun t ↦ cell H a t * cell H b (x - t)) := by
  refine (integrable_cell H a).mul_bdd (c := 1) ((integrable_cell H b).comp_sub_left x).aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  simpa [Real.norm_eq_abs, abs_of_nonneg (cell_nonneg H b (x - t))] using cell_le_one H b (x - t)

private lemma integral_cell_shift_mul (H a b x : ℝ) :
    (∫ t, cell H a t * cell H b (x - t)) = ∫ t, cell H 0 t * cell H (a + b) (x - t) := by
  rw [← integral_sub_right_eq_self (fun t ↦ cell H 0 t * cell H (a + b) (x - t)) a]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [cell_translate H a t, cell_translate H b (x - t), cell_translate H (a + b) (x - (t - a))]
  congr 2
  ring

private lemma convolution_sumCells (A : Finset ℕ) (H : ℕ) :
    sumCells A (fun a ↦ (a : ℝ)) H ⋆ sumCells A (fun a ↦ (a : ℝ)) H =
      cell H 0 ⋆ sumCells (A ×ˢ A) (fun p ↦ (pairCenter p : ℝ)) H := by
  funext x
  simp only [convolution_lsmul, smul_eq_mul, sumCells, sum_product]
  have h (t : ℝ) : (∑ a ∈ A, cell H a t) * (∑ b ∈ A, cell H b (x - t)) =
      ∑ a ∈ A, ∑ b ∈ A, cell H a t * cell H b (x - t) := by
    rw [sum_mul]
    simp only [mul_sum]
  simp_rw [h, mul_sum]
  rw [integral_finsetSum A (fun a _ ↦ integrable_finsetSum A (fun b _ ↦ integrable_cell_shift_mul H a b x))]
  have hR (a b : ℕ) : (pairCenter (a,b) : ℝ) = (a : ℝ) + b := by simp [pairCenter]
  simp only [hR]
  rw [integral_finsetSum A (fun a _ ↦
    integrable_finsetSum A (fun b _ ↦ integrable_cell_shift_mul H 0 (a + b) x))]
  apply sum_congr rfl
  intro a _
  rw [integral_finsetSum A (fun b _ ↦ integrable_cell_shift_mul H a b x),
    integral_finsetSum A (fun b _ ↦ integrable_cell_shift_mul H 0 (a + b) x)]
  exact sum_congr rfl fun b _ ↦ integral_cell_shift_mul H a b x

private lemma square_integral_mul_le {K g : ℝ → ℝ} (hK : Integrable K)
    (hK₀ : ∀ t, 0 ≤ K t) (hK₁ : 0 < ∫ t, K t)
    (h₁ : Integrable (fun t ↦ K t * g t)) (h₂ : Integrable (fun t ↦ K t * g t ^ 2)) :
    (∫ t, K t * g t) ^ 2 ≤ (∫ t, K t) * (∫ t, K t * g t ^ 2) := by
  let m := (∫ t, K t * g t) / (∫ t, K t)
  have hvar : 0 ≤ ∫ t, K t * (g t - m) ^ 2 := integral_nonneg fun t ↦ by positivity [hK₀ t]
  have heq : (fun t ↦ K t * (g t - m) ^ 2) =
      fun t ↦ (K t * g t ^ 2 - (K t * g t) * (2 * m)) + K t * m ^ 2 := by
    funext t
    ring
  have hs : Integrable (fun t ↦ K t * g t ^ 2 - K t * g t * (2 * m)) :=
    h₂.sub (h₁.mul_const (2 * m))
  rw [heq, integral_add hs (hK.mul_const (m ^ 2)), integral_sub h₂ (h₁.mul_const (2 * m)),
    integral_mul_const (2 * m) (fun t ↦ K t * g t), integral_mul_const (m ^ 2) K] at hvar
  have hvar' : 0 ≤ (∫ t, K t * g t ^ 2) - (∫ t, K t * g t) ^ 2 / (∫ t, K t) := by
    convert hvar using 1
    dsimp [m]
    field_simp [hK₁.ne']
    ring
  simpa only [mul_comm] using (div_le_iff₀ hK₁).mp (sub_nonneg.mp hvar')

private lemma integral_convolution_cell_sq_le {H : ℝ} (hH : 0 < H) {g : ℝ → ℝ}
    (hg : Integrable g) {C : ℝ} (hbound : ∀ t, ‖g t‖ ≤ C) :
    (∫ x, ((cell H 0 ⋆ g) x) ^ 2) ≤ H ^ 2 * (∫ x, g x ^ 2) := by
  let g₂ : ℝ → ℝ := fun t ↦ g t ^ 2
  have hg₂ : Integrable g₂ := by
    simpa only [g₂, pow_two] using hg.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall hbound)
  have hpt (x : ℝ) : ((cell H 0 ⋆ g) x) ^ 2 ≤ H * (cell H 0 ⋆ g₂) x := by
    simp only [convolution_lsmul, smul_eq_mul, g₂]
    have hK := integrable_cell H 0
    have hK₁ := integral_cell hH.le 0
    have hboundK : ∀ᵐ t ∂volume, ‖cell H 0 t‖ ≤ 1 := Eventually.of_forall fun t ↦ by
      simpa [Real.norm_eq_abs, abs_of_nonneg (cell_nonneg H 0 t)] using cell_le_one H 0 t
    have h₁ := (hg.comp_sub_left x).bdd_mul hK.aestronglyMeasurable hboundK
    have h₂ := (hg₂.comp_sub_left x).bdd_mul hK.aestronglyMeasurable hboundK
    simpa only [hK₁] using square_integral_mul_le hK (cell_nonneg H 0) (hK₁.symm ▸ hH) h₁ h₂
  calc
    _ ≤ ∫ x, H * (cell H 0 ⋆ g₂) x := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun x ↦ sq_nonneg _) _ (Eventually.of_forall hpt)
      exact ((integrable_cell H 0).integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg₂).const_mul H
    _ = _ := by
      rw [integral_const_mul, integral_convolution _ (integrable_cell H 0) hg₂, integral_cell hH.le]
      simp [smul_eq_mul, pow_two, ← mul_assoc, g₂]

/-- The interval-length form of the autoconvolution lower bound for bounded densities. -/
def IntervalAutoconvolutionLower (c : ℝ) : Prop :=
  ∀ (L : ℝ) (g : ℝ → ℝ), 0 < L → Integrable g → (∀ x, 0 ≤ g x) →
    (∃ C : ℝ, ∀ x, g x ≤ C) → (∀ x ∉ Set.Icc 0 L, g x = 0) →
    c * (∫ x, g x) ^ 4 ≤ L * (∫ x, ((g ⋆ g) x) ^ 2)

lemma boxEnergyLower_of_intervalAutoconvolutionLower {c : ℝ}
    (hLower : IntervalAutoconvolutionLower c) : BoxEnergyLower c := by
  intro N H A hAN hH
  let f := sumCells A (fun a ↦ (a : ℝ)) H
  let g := sumCells (A ×ˢ A) (fun p ↦ (pairCenter p : ℝ)) H
  have hH' : 0 < (H : ℝ) := by exact_mod_cast hH
  have hL : 0 < (N : ℝ) + H := by positivity
  have hf0 : ∀ x ∉ Set.Icc (0 : ℝ) ((N : ℝ) + H), f x = 0 := by
    intro x hx
    unfold f sumCells
    apply sum_eq_zero
    intro a ha
    have hNa : (a : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp (hAN ha)).2
    have hxa : x ∉ Set.Icc (a : ℝ) ((a : ℝ) + H) := by
      intro h
      exact hx ⟨le_trans (by positivity) h.1, h.2.trans (by linarith)⟩
    simp [cell, hxa]
  have hf := hLower ((N : ℝ) + H) f hL (integrable_sumCells ..)
    (fun x ↦ sumCells_nonneg _ _ _ x) ⟨#A, fun x ↦ sumCells_le_card _ _ _ x⟩ hf0
  rw [show (∫ x, f x) = (#A : ℝ) * H from integral_sumCells _ _ hH'.le,
    show f ⋆ f = cell H 0 ⋆ g from convolution_sumCells A H] at hf
  have hgBound (x : ℝ) : ‖g x‖ ≤ (#(A ×ˢ A) : ℝ) := by
    have h₀ : 0 ≤ g x := sumCells_nonneg _ _ _ _
    rw [Real.norm_eq_abs, abs_of_nonneg h₀]
    exact sumCells_le_card _ _ _ _
  have hg := integral_convolution_cell_sq_le hH' (g := g) (integrable_sumCells ..) hgBound
  have hc := hf.trans (mul_le_mul_of_nonneg_left hg hL.le)
  rw [energy_eq_integral_sumCells_sq]
  change c * (#A : ℝ) ^ 4 / ((N : ℝ) + H) ≤ (∫ x, g x ^ 2) / (H : ℝ) ^ 2
  apply (div_le_iff₀ hL).mpr
  apply le_of_mul_le_mul_left _ (by positivity : 0 < (H : ℝ) ^ 4)
  calc
    _ = c * ((#A : ℝ) * H) ^ 4 := by ring
    _ ≤ ((N : ℝ) + H) * ((H : ℝ) ^ 2 * ∫ x, g x ^ 2) := hc
    _ = _ := by field_simp

/-- White's lower bound restricted to bounded, nonnegative probability densities. -/
def UnitAutoconvolutionLower (c : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Integrable g → (∀ x, 0 ≤ g x) → (∃ C : ℝ, ∀ x, g x ≤ C) →
    (∀ x ∉ Set.Icc (-(1 : ℝ) / 2) (1 / 2), g x = 0) → (∫ x, g x) = 1 →
    c ≤ ∫ x, ((g ⋆ g) x) ^ 2

private lemma integral_affine {L : ℝ} (hL : 0 < L) (g : ℝ → ℝ) (a : ℝ) :
    (∫ x, g (L * (x + a))) = (∫ x, g x) / L := by
  rw [integral_add_right_eq_self (fun x ↦ g (L * x)) a, Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr hL), smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma intervalAutoconvolutionLower_of_unit {c : ℝ} (hUnit : UnitAutoconvolutionLower c) :
    IntervalAutoconvolutionLower c := by
  rintro L g hL hg hg₀ ⟨C, hC⟩ hgSupp
  let M := ∫ x, g x
  by_cases hMzero : M = 0
  · change c * M ^ 4 ≤ _
    simpa [hMzero] using mul_nonneg hL.le (integral_nonneg fun x ↦ sq_nonneg ((g ⋆ g) x))
  have hM : 0 < M := (integral_nonneg hg₀).lt_of_ne (Ne.symm hMzero)
  let f : ℝ → ℝ := fun x ↦ (L / M) * g (L * (x + 1 / 2))
  have hf : Integrable f :=
    (((integrable_comp_mul_left_iff g hL.ne').mpr hg).comp_add_right (1 / 2)).const_mul (L / M)
  have hf₀ (x : ℝ) : 0 ≤ f x := mul_nonneg (by positivity) (hg₀ _)
  have hfC (x : ℝ) : f x ≤ (L / M) * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hfSupp : ∀ x ∉ Set.Icc (-(1 : ℝ) / 2) (1 / 2), f x = 0 := by
    intro x hx
    have hlx : L * (x + 1 / 2) ∉ Set.Icc (0 : ℝ) L := by
      intro h
      have h₀ : 0 ≤ x + 1 / 2 := (mul_le_mul_iff_right₀ hL).mp (by simpa [mul_comm L] using h.1)
      have h₁ : x + 1 / 2 ≤ 1 := (mul_le_mul_iff_right₀ hL).mp (by simpa [mul_comm L] using h.2)
      exact hx ⟨by linarith, by linarith⟩
    change L / M * g (L * (x + 1 / 2)) = 0
    rw [hgSupp _ hlx, mul_zero]
  have hf₁ : (∫ x, f x) = 1 := by
    dsimp only [f]
    rw [integral_const_mul, integral_affine hL]
    change L / M * (M / L) = 1
    field_simp
  have hconv (x : ℝ) : (f ⋆ f) x = ((L / M) ^ 2 / L) * (g ⋆ g) (L * (x + 1)) := by
    simp only [convolution_lsmul, smul_eq_mul, f]
    have heq : (fun t : ℝ ↦ (L / M * g (L * (t + 1 / 2))) *
          (L / M * g (L * (x - t + 1 / 2)))) =
        fun t ↦ (L / M) ^ 2 * (g (L * (t + 1 / 2)) *
          g (L * (x + 1) - L * (t + 1 / 2))) := by
      funext t
      rw [show L * (x - t + 1 / 2) = L * (x + 1) - L * (t + 1 / 2) by ring]
      ring
    rw [heq, integral_const_mul, integral_affine hL (fun t ↦ g t * g (L * (x + 1) - t))]
    ring
  have hnorm : (∫ x, ((f ⋆ f) x) ^ 2) = (L / M ^ 4) * (∫ x, ((g ⋆ g) x) ^ 2) := by
    simp_rw [hconv, mul_pow]
    rw [integral_const_mul, integral_affine hL (fun x ↦ ((g ⋆ g) x) ^ 2)]
    field_simp
  have h := hUnit f hf hf₀ ⟨_, hfC⟩ hfSupp hf₁
  rw [hnorm] at h
  change c * M ^ 4 ≤ L * _
  apply (le_div_iff₀ (pow_pos hM 4)).mp
  simpa only [div_mul_eq_mul_div] using h

open scoped FourierTransform

private lemma circleCoeff_energy {f : ℝ → ℂ} (hf : Integrable f)
    (hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hs : ∀ x ∉ Set.Icc (-1 : ℝ) 1, f x = 0)
    (S : Finset ℤ) :
    (1 / 2 : ℝ) * (∑ n ∈ S, ‖𝓕 f ((n : ℝ) / 2)‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := by
  let hI : (-1 : ℝ) < 1 := by norm_num
  obtain ⟨C, hC⟩ := hbound
  have hsq : Integrable (fun x ↦ ‖f x‖ ^ 2) := by
    simpa only [pow_two] using hf.norm.mul_bdd hf.norm.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC x)
  have hLp := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hsq
  have hP := hasSum_sq_fourierCoeffOn hI (hLp.mono_measure (Measure.restrict_le_self))
  have hcoef (n : ℤ) : fourierCoeffOn hI f n = (1 / 2 : ℂ) * 𝓕 f ((n : ℝ) / 2) := by
    rw [fourierCoeffOn_eq_integral, Real.fourier_real_eq_integral_exp_smul]
    simp only [show (1 : ℝ) - (-1) = 2 by norm_num, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, smul_eq_mul]
    congr 1
    rw [intervalIntegral.integral_of_le hI.le, ← integral_Icc_eq_integral_Ioc]
    let k : ℝ → ℂ := fun x ↦ Complex.exp (↑(-2 * Real.pi * x * ((n : ℝ) / 2)) * Complex.I) * f x
    change _ = ∫ x, k x
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := k) (s := Set.Icc (-1 : ℝ) 1)
      (fun x hx ↦ by simp [k, hs x hx])]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    dsimp only [k]
    rw [fourier_coe_apply]
    congr 2
    push_cast
    ring
  have hsum := hP.summable.sum_le_tsum S (fun _ _ ↦ sq_nonneg _)
  rw [hP.tsum_eq] at hsum
  rw [intervalIntegral.integral_of_le hI.le, ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by simp [hs x hx])] at hsum
  simp_rw [hcoef, norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num,
    mul_pow, ← mul_sum] at hsum
  norm_num [smul_eq_mul] at hsum ⊢
  linarith

private lemma complex_autoconvolution (g : ℝ → ℝ) :
    (fun x ↦ ((g ⋆ g) x : ℂ)) =
      ((fun x ↦ (g x : ℂ)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] (fun x ↦ (g x : ℂ))) := by
  ext x : 1
  simp only [convolution_lsmul, smul_eq_mul, ← Complex.ofReal_mul, integral_complex_ofReal]

/-- A finite set of Fourier modes gives a fourth-power lower bound for autoconvolution. -/
lemma autoconvolution_fourier_lower {g : ℝ → ℝ} (hg : Integrable g) (hg₀ : ∀ x, 0 ≤ g x)
    {C : ℝ} (hC : ∀ x, g x ≤ C) (hs : ∀ x ∉ Set.Icc (-(1 : ℝ) / 2) (1 / 2), g x = 0)
    (S : Finset ℤ) :
    (1 / 2 : ℝ) * (∑ n ∈ S, ‖𝓕 (fun x ↦ (g x : ℂ)) ((n : ℝ) / 2)‖ ^ 4) ≤
      ∫ x, ((g ⋆ g) x) ^ 2 := by
  let f : ℝ → ℂ := fun x ↦ ((g ⋆ g) x : ℂ)
  have hfi : Integrable f := (hg.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg).ofReal
  have hn (x : ℝ) : 0 ≤ (g ⋆ g) x :=
    integral_nonneg fun t ↦ mul_nonneg (hg₀ t) (hg₀ (x - t))
  have hfn (x : ℝ) : ‖f x‖ = (g ⋆ g) x := by simp [f, abs_of_nonneg (hn x)]
  have hfC (x : ℝ) : ‖f x‖ ≤ (∫ t, g t) * C := by
    rw [hfn]
    change (∫ t, g t * g (x - t)) ≤ _
    rw [← integral_mul_const]
    apply integral_mono_of_nonneg (Eventually.of_forall fun t ↦ mul_nonneg (hg₀ t) (hg₀ (x - t)))
      (hg.mul_const C)
    exact Eventually.of_forall fun t ↦ mul_le_mul_of_nonneg_left (hC (x - t)) (hg₀ t)
  have hfs : ∀ x ∉ Set.Icc (-1 : ℝ) 1, f x = 0 := by
    intro x hx
    change ((∫ t, g t * g (x - t) : ℝ) : ℂ) = 0
    have hz (t : ℝ) : g t * g (x - t) = 0 := by
      by_cases ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)
      · rw [hs (x - t) (fun h ↦ hx ⟨by linarith [ht.1, h.1], by linarith [ht.2, h.2]⟩), mul_zero]
      · rw [hs t ht, zero_mul]
    simp [hz]
  have h := circleCoeff_energy hfi ⟨_, hfC⟩ hfs S
  have hgi : Integrable (fun x ↦ (g x : ℂ)) := hg.ofReal
  have hconv (n : ℤ) : ‖𝓕 f ((n : ℝ) / 2)‖ ^ 2 =
      ‖𝓕 (fun x ↦ (g x : ℂ)) ((n : ℝ) / 2)‖ ^ 4 := by
    simp only [show f = _ from complex_autoconvolution g, Real.fourier_smul_convolution_eq hgi hgi,
      smul_eq_mul, norm_mul]
    ring
  simpa only [hconv, hfn] using h

private noncomputable def dualCos (n : ℤ) (x : ℝ) : ℝ := Real.cos (Real.pi * n * x)

private lemma re_fourier_eq_cos {g : ℝ → ℝ} (hg : Integrable g) (n : ℤ) :
    (𝓕 (fun x ↦ (g x : ℂ)) ((n : ℝ) / 2)).re = ∫ x, dualCos n x * g x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have hi : Integrable (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ((n : ℝ) / 2)) * Complex.I) * (g x : ℂ)) := by
    refine (hg.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x ↦ ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  change RCLike.re (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * ((n : ℝ) / 2)) * Complex.I) * (g x : ℂ)) = _
  rw [← integral_re hi]
  apply integral_congr_ae
  filter_upwards [] with x
  change (Complex.exp (↑(-2 * Real.pi * x * ((n : ℝ) / 2)) * Complex.I) * (g x : ℂ)).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re, dualCos]
  rw [show -2 * Real.pi * x * ((n : ℝ) / 2) = -(Real.pi * n * x) by ring, Real.cos_neg]

private lemma quartic_tangent (a b : ℝ) : 4 * a ^ 3 * b - 3 * a ^ 4 ≤ b ^ 4 := by
  have h := mul_nonneg (sq_nonneg (b - a))
    (show 0 ≤ (b + a) ^ 2 + 2 * a ^ 2 by positivity)
  linarith only [show b ^ 4 - (4 * a ^ 3 * b - 3 * a ^ 4) =
    (b - a) ^ 2 * ((b + a) ^ 2 + 2 * a ^ 2) by ring, h]

/-- A finite trigonometric certificate for the desired numerical lower bound. -/
def HasFourierCertificate (c : ℝ) : Prop :=
  ∃ (S : Finset ℤ) (u : ℤ → ℝ), ∀ x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
    c ≤ (1 / 2 : ℝ) * ∑ n ∈ S, (4 * u n ^ 3 * dualCos n x - 3 * u n ^ 4)

lemma autoconvolution_lower_of_certificate {c : ℝ} (hcert : HasFourierCertificate c)
    {g : ℝ → ℝ} (hg : Integrable g) (hg₀ : ∀ x, 0 ≤ g x)
    {C : ℝ} (hC : ∀ x, g x ≤ C) (hs : ∀ x ∉ Set.Icc (-(1 : ℝ) / 2) (1 / 2), g x = 0)
    (hmass : (∫ x, g x) = 1) : c ≤ ∫ x, ((g ⋆ g) x) ^ 2 := by
  obtain ⟨S, u, hu⟩ := hcert
  have hi (n : ℤ) : Integrable (fun x ↦ dualCos n x * g x) := by
    refine hg.bdd_mul (c := 1) (by unfold dualCos; fun_prop) (Eventually.of_forall fun x ↦ ?_)
    exact Real.abs_cos_le_one _
  have ht (n : ℤ) : Integrable (fun x ↦ (4 * u n ^ 3 * dualCos n x - 3 * u n ^ 4) * g x) := by
    convert ((hi n).const_mul (4 * u n ^ 3)).sub (hg.const_mul (3 * u n ^ 4)) using 1
    ext x
    simp only [Pi.sub_apply]
    ring
  have hs₁ : (∫ x, c * g x) ≤ ∫ x, ((1 / 2 : ℝ) * ∑ n ∈ S,
      (4 * u n ^ 3 * dualCos n x - 3 * u n ^ 4)) * g x := by
    apply integral_mono (hg.const_mul c)
    · simpa only [mul_assoc, sum_mul] using (integrable_finsetSum S (fun n _ ↦ ht n)).const_mul (1 / 2)
    · intro x
      by_cases hx : x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)
      · exact mul_le_mul_of_nonneg_right (hu x hx) (hg₀ x)
      · simp [hs x hx]
  have hterm (n : ℤ) : (∫ x, (4 * u n ^ 3 * dualCos n x - 3 * u n ^ 4) * g x) =
      4 * u n ^ 3 * (𝓕 (fun x ↦ (g x : ℂ)) ((n : ℝ) / 2)).re - 3 * u n ^ 4 := by
    have heq (x : ℝ) : (4 * u n ^ 3 * dualCos n x - 3 * u n ^ 4) * g x =
        (4 * u n ^ 3) * (dualCos n x * g x) - (3 * u n ^ 4) * g x := by ring
    simp_rw [heq]
    rw [integral_sub ((hi n).const_mul (4 * u n ^ 3)) (hg.const_mul (3 * u n ^ 4)),
      integral_const_mul (4 * u n ^ 3), integral_const_mul (3 * u n ^ 4),
      ← re_fourier_eq_cos hg, hmass, mul_one]
  rw [integral_const_mul, hmass, mul_one] at hs₁
  have hfactor (x : ℝ) : ((1 / 2 : ℝ) * ∑ n ∈ S, (4 * u n ^ 3 * dualCos n x - 3 * u n ^ 4)) * g x =
      (1 / 2 : ℝ) * ∑ n ∈ S, (4 * u n ^ 3 * dualCos n x - 3 * u n ^ 4) * g x := by
    rw [← sum_mul, mul_assoc]
  simp_rw [hfactor] at hs₁
  rw [integral_const_mul, integral_finsetSum _ (fun n _ ↦ ht n)] at hs₁
  simp_rw [hterm] at hs₁
  refine hs₁.trans ((mul_le_mul_of_nonneg_left (sum_le_sum fun n _ ↦ ?_) (by norm_num)).trans
    (autoconvolution_fourier_lower hg hg₀ hC hs S))
  let z := 𝓕 (fun x ↦ (g x : ℂ)) ((n : ℝ) / 2)
  exact (quartic_tangent (u n) z.re).trans (by
    change z.re ^ (4 : ℕ) ≤ ‖z‖ ^ (4 : ℕ)
    simpa only [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ z.re ^ (4 : ℕ))] using
      pow_le_pow_left₀ (abs_nonneg z.re) (Complex.abs_re_le_norm z) 4)

/-- Rational coefficients suffice for a certificate, using Chebyshev polynomials on `[0,1]`. -/
def HasChebyshevCertificate (c : ℝ) : Prop :=
  ∃ (S : Finset ℤ) (u : ℤ → ℚ), ∀ y ∈ Set.Icc (0 : ℝ) 1,
    c ≤ (1 / 2 : ℝ) * ∑ n ∈ S,
      (4 * (u n : ℝ) ^ 3 * (Polynomial.Chebyshev.T ℝ n).eval y - 3 * (u n : ℝ) ^ 4)

lemma fourierCertificate_of_chebyshev {c : ℝ} (h : HasChebyshevCertificate c) :
    HasFourierCertificate c := by
  obtain ⟨S, u, hu⟩ := h
  refine ⟨S, fun n ↦ (u n : ℝ), ?_⟩
  intro x hx
  have h₁ := mul_le_mul_of_nonneg_left hx.1 Real.pi_pos.le
  have h₂ := mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le
  have hy : Real.cos (Real.pi * x) ∈ Set.Icc 0 1 :=
    ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩, Real.cos_le_one _⟩
  have he (n : ℤ) : (Polynomial.Chebyshev.T ℝ n).eval (Real.cos (Real.pi * x)) = dualCos n x := by
    rw [Polynomial.Chebyshev.T_real_cos, dualCos, mul_left_comm, mul_assoc]
  simpa only [he] using hu _ hy


lemma unitAutoconvolutionLower_of_chebyshev {c : ℝ} (h : HasChebyshevCertificate c) :
    UnitAutoconvolutionLower c := by
  rintro g hg hg₀ ⟨C, hC⟩ hs hmass
  exact autoconvolution_lower_of_certificate (fourierCertificate_of_chebyshev h) hg hg₀ hC hs hmass

end OMA.White241

theorem OMA.solution : type_of% @Erdos241.erdos_241.variants.upper_bound_white := by
  apply OMA.White241.asymptotic_of_boxEnergyLower (by norm_num : 0 < (0.574636066 : ℝ))
  apply OMA.White241.boxEnergyLower_of_intervalAutoconvolutionLower
  apply OMA.White241.intervalAutoconvolutionLower_of_unit
  apply OMA.White241.unitAutoconvolutionLower_of_chebyshev
  sorry

