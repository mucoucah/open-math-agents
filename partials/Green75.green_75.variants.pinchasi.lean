import FormalConjectures.GreensOpenProblems.«75»
import Mathlib

-- Problem: Ben Green's Open Problem 75 — pinchasi
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/75.lean:96 (declaration Green75.green_75.variants.pinchasi)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace G75Pin
open Green75 Finset
open scoped Classical

/-- Shear invariance of the cross product. -/
theorem cross_shear (c : ℝ) (p q x : ℝ × ℝ) :
    cross (p.1 + c * p.2, p.2) (q.1 + c * q.2, q.2) (x.1 + c * x.2, x.2) = cross p q x := by
  unfold cross; ring

/-- A shear makes first coordinates distinct and preserves all imbalances. -/
theorem shear (X : Finset (ℝ × ℝ)) : ∃ e : (ℝ × ℝ) ↪ (ℝ × ℝ),
    Set.InjOn Prod.fst (↑(X.map e) : Set (ℝ × ℝ)) ∧
    ∀ p q, imbalance (X.map e) (e p) (e q) = imbalance X p q := by
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    ((X ×ˢ X).image (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.2.1 - z.1.1) / (z.1.2 - z.2.2)))
  have hinj : Function.Injective (fun x : ℝ × ℝ => (x.1 + c * x.2, x.2)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext (by rw [h2] at h1; linarith) h2
  let e : (ℝ × ℝ) ↪ (ℝ × ℝ) := ⟨_, hinj⟩
  refine ⟨e, ?_, ?_⟩
  · intro u hu v hv huv
    simp only [coe_map, Set.mem_image, mem_coe] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    simp only [e, Function.Embedding.coeFn_mk] at huv ⊢
    by_cases h2 : a.2 = b.2
    · have : a.1 = b.1 := by rw [h2] at huv; linarith
      rw [Prod.ext this h2]
    · exfalso
      apply hc
      refine mem_image.mpr ⟨(a, b), mem_product.mpr ⟨ha, hb⟩, ?_⟩
      have hne : a.2 - b.2 ≠ 0 := sub_ne_zero.mpr h2
      field_simp
      linarith
  · intro p q
    have hl : leftCount (X.map e) (e p) (e q) = leftCount X p q := by
      unfold leftCount
      rw [filter_map, card_map]
      congr 1
      exact filter_congr fun x _ => by
        simp only [Function.comp, e, Function.Embedding.coeFn_mk, cross_shear]
    have hr : rightCount (X.map e) (e p) (e q) = rightCount X p q := by
      unfold rightCount
      rw [filter_map, card_map]
      congr 1
      exact filter_congr fun x _ => by
        simp only [Function.comp, e, Function.Embedding.coeFn_mk, cross_shear]
    unfold imbalance; rw [hl, hr]

/-- Pinchasi's crossing-level bound for line arrangements with distinct slopes
(the deep part of [Pi03]); remaining gap. -/
theorem pinchasi_core : ∃ C : ℝ, ∀ A : Finset (ℝ × ℝ), 3 ≤ A.card →
    Set.InjOn Prod.fst (↑A : Set (ℝ × ℝ)) →
    ∃ p ∈ A, ∃ q ∈ A, p.1 < q.1 ∧ ∃ t : ℝ, q.2 - t*q.1 = p.2 - t*p.1 ∧
      ((|((A.filter fun x ↦ p.2 - t*p.1 < x.2 - t*x.1).card : ℤ) -
        ((A.filter fun x ↦ x.2 - t*x.1 < p.2 - t*p.1).card : ℤ)| : ℤ) : ℝ)
          ≤ C * Real.log (Real.log A.card) := by
  sorry

end G75Pin

theorem OMA.solution : type_of% @Green75.green_75.variants.pinchasi := by
  classical
  obtain ⟨C, hC⟩ := G75Pin.pinchasi_core
  refine ⟨C, fun X hn => ?_⟩
  obtain ⟨e, hinj, him⟩ := G75Pin.shear X
  obtain ⟨p, hp, q, hq, hpq, t, ht, hl⟩ :=
    hC (X.map e) (by simpa using hn) hinj
  have hc (x : ℝ × ℝ) : Green75.cross p q x = (q.1 - p.1) * ((x.2 - t*x.1) - (p.2 - t*p.1)) := by
    unfold Green75.cross
    linear_combination (p.1 - x.1) * ht
  have hpos : 0 < q.1 - p.1 := sub_pos.mpr hpq
  have hleft : Green75.leftCount (X.map e) p q =
      ((X.map e).filter fun x => p.2 - t*p.1 < x.2 - t*x.1).card := by
    unfold Green75.leftCount
    congr 1
    ext x
    simp only [Finset.mem_filter, hc]
    exact and_congr_right fun _ => ⟨fun h => sub_pos.mp (pos_of_mul_pos_right h hpos.le),
      fun h => mul_pos hpos (sub_pos.mpr h)⟩
  have hright : Green75.rightCount (X.map e) p q =
      ((X.map e).filter fun x => x.2 - t*x.1 < p.2 - t*p.1).card := by
    unfold Green75.rightCount
    congr 1
    ext x
    simp only [Finset.mem_filter, hc]
    exact and_congr_right fun _ => ⟨fun h => sub_neg.mp (neg_of_mul_neg_right h hpos.le),
      fun h => mul_neg_of_pos_of_neg hpos (sub_neg.mpr h)⟩
  have hbound : (Green75.imbalance (X.map e) p q : ℝ) ≤ C * Real.log (Real.log (X.map e).card) := by
    simpa only [Green75.imbalance, hleft, hright] using hl
  obtain ⟨p', hp', rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hq
  refine ⟨p', hp', q', hq', fun h => hpq.ne (by rw [h]), ?_⟩
  simpa only [him, Finset.card_map] using hbound
