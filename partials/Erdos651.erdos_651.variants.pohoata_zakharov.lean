import FormalConjectures.ErdosProblems.«651»
import Mathlib.Algebra.Module.Submodule.Union

-- Problem: Erdős Problem 651 — pohoata zakharov
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/651.lean:139 (declaration Erdos651.erdos_651.variants.pohoata_zakharov)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Erdos651
open scoped EuclideanGeometry

namespace OMA.PZ

/-- Pohoata and Zakharov, Theorem 1.1, in dimension three (the research core). -/
theorem core3 : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ N ∈ cardSet 3 n, (N : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by
  sorry

/-- Points of a finite set whose image lies in a given finite set. -/
theorem pullback {α β : Type*} [DecidableEq β] (L : α → β) (X : Finset α) (Z : Finset β)
    (hZ : Z ⊆ X.image L) (hL : Set.InjOn L (X : Set α)) :
    ∃ Y ⊆ X, Y.image L = Z := by
  classical
  refine ⟨X.filter (fun y => L y ∈ Z), Finset.filter_subset _ _, ?_⟩
  ext z
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨_, hy⟩, rfl⟩; exact hy
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hZ hz)
    exact ⟨y, ⟨hy, hz⟩, rfl⟩

/-- Convex position lifts along a linear map injective on the set. -/
theorem lift_convex {d k n : ℕ} (L : (ℝ^d) →ₗ[ℝ] (ℝ^k)) (X : Finset (ℝ^d))
    (hL : Set.InjOn L (X : Set (ℝ^d))) (h : HasConvexSubset n (X.image L)) :
    HasConvexSubset n X := by
  classical
  obtain ⟨Z, hZX, hZn, hZ⟩ := h
  obtain ⟨Y, hYX, hYZ⟩ := pullback L X Z hZX hL
  have hLY : Set.InjOn L (Y : Set (ℝ^d)) := hL.mono (by exact_mod_cast hYX)
  refine ⟨Y, hYX, ?_, ?_⟩
  · rw [← hZn, ← hYZ, Finset.card_image_of_injOn hLY]
  · intro s y hy
    let s' : Set ↥(Z : Set (ℝ^k)) := {z | z.val ∈ L '' (Subtype.val '' s)}
    have hmem : (L y.val) ∈ (Z : Set (ℝ^k)) := by
      rw [← hYZ]; exact Finset.mem_image_of_mem L y.prop
    have himg : L '' (Subtype.val '' s) = Subtype.val '' s' := by
      ext w
      constructor
      · rintro hw
        obtain ⟨a, ha, rfl⟩ := hw
        obtain ⟨b, hb, rfl⟩ := ha
        have hbZ : L b.val ∈ (Z : Set (ℝ^k)) := by
          rw [← hYZ]; exact Finset.mem_image_of_mem L b.prop
        exact ⟨⟨L b.val, hbZ⟩, ⟨b.val, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨z, hz, rfl⟩; exact hz
    have hcv : (Subtype.val (⟨L y.val, hmem⟩ : ↥(Z : Set (ℝ^k)))) ∈
        convexHull ℝ (Subtype.val '' s') := by
      rw [← himg, ← L.image_convexHull]
      exact ⟨y.val, hy, rfl⟩
    obtain ⟨a, ⟨b, hb, rfl⟩, hab⟩ := hZ s' _ hcv
    have : b = y := Subtype.ext (hLY b.prop y.prop hab)
    exact this ▸ hb

/-- A generic projection keeps general position. -/
theorem projection {k : ℕ} (hk : 1 ≤ k) (X : Finset (ℝ^(k+1)))
    (hX : IsInGeneralPosition X) :
    ∃ L : (ℝ^(k+1)) →ₗ[ℝ] (ℝ^k),
      Set.InjOn L (X : Set (ℝ^(k+1))) ∧ IsInGeneralPosition (X.image L) := by
  classical
  let S := X.powerset.filter fun Y => Y.card ≤ k + 1
  let W : S → Submodule ℝ (ℝ^(k+1)) := fun Y => vectorSpan ℝ (Y.val : Set (ℝ^(k+1)))
  have hW : ∀ Y, W Y ≠ ⊤ := by
    intro Y htop
    have hc : Y.val.card ≤ k + 1 := (Finset.mem_filter.mp Y.prop).2
    have hle : Module.finrank ℝ (W Y) ≤ k := by
      rcases Y.val.eq_empty_or_nonempty with he | hne
      · change Module.finrank ℝ (vectorSpan ℝ (Y.val : Set (ℝ^(k+1)))) ≤ k
        rw [he, Finset.coe_empty, vectorSpan_empty, finrank_bot]; omega
      · have h1 : Y.val.card = (Y.val.card - 1) + 1 := by
          have := hne.card_pos; omega
        have h2 := finrank_vectorSpan_image_finset_le ℝ id Y.val h1
        rw [Finset.image_id] at h2
        exact h2.trans (by omega)
    rw [htop, finrank_top, finrank_euclideanSpace_fin] at hle
    omega
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top W hW
  have hv0 : v ≠ 0 := fun h0 => hv ⟨∅, by simp [S]⟩ (h0 ▸ Submodule.zero_mem _)
  let U := ℝ ∙ v
  have hdim : Module.finrank ℝ ((ℝ^(k+1)) ⧸ U) = Module.finrank ℝ (ℝ^k) := by
    have h := U.finrank_quotient_add_finrank
    rw [finrank_span_singleton hv0, finrank_euclideanSpace_fin] at h
    rw [finrank_euclideanSpace_fin]; omega
  let L : (ℝ^(k+1)) →ₗ[ℝ] (ℝ^k) := (LinearEquiv.ofFinrankEq _ _ hdim).toLinearMap ∘ₗ U.mkQ
  have hker : ∀ Y ⊆ X, Y.card ≤ k + 1 →
      Disjoint (vectorSpan ℝ (Y : Set (ℝ^(k+1)))) (LinearMap.ker L) := by
    intro Y hYX hY
    rw [Submodule.disjoint_def]
    intro u hu hLu
    have hU : u ∈ U := by
      have : U.mkQ u = 0 := by
        apply (LinearEquiv.ofFinrankEq _ _ hdim).injective
        simpa [L] using hLu
      simpa using this
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hU
    by_cases ha : a = 0
    · simp [ha]
    · exact absurd ((Submodule.smul_mem_iff _ ha).mp hu)
        (hv ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hYX, hY⟩⟩)
  have hinj : Set.InjOn L (X : Set (ℝ^(k+1))) := by
    intro a ha b hb hab
    have hsub : ({a, b} : Finset (ℝ^(k+1))) ⊆ X := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hm : a -ᵥ b ∈ vectorSpan ℝ (({a, b} : Finset (ℝ^(k+1))) : Set (ℝ^(k+1))) :=
      vsub_mem_vectorSpan ℝ (by simp) (by simp)
    have hk' : a -ᵥ b ∈ LinearMap.ker L := by
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub, hab, sub_self]
    have := Submodule.disjoint_def.mp
      (hker _ hsub (Finset.card_le_two.trans (by omega))) _ hm hk'
    exact sub_eq_zero.mp (by simpa using this)
  refine ⟨L, hinj, ?_⟩
  intro Z hZ hZc
  obtain ⟨Y, hYX, hYZ⟩ := pullback L X Z hZ hinj
  have hLY : Set.InjOn L (Y : Set (ℝ^(k+1))) := hinj.mono (by exact_mod_cast hYX)
  have hYc : Y.card ≤ k + 1 := by
    rw [← Finset.card_image_of_injOn hLY, hYZ]; exact hZc
  let p : ↥(Y : Set (ℝ^(k+1))) → ℝ^(k+1) := Subtype.val
  have hr : Set.range (L ∘ p) = (Z : Set (ℝ^k)) := by
    rw [Set.range_comp, Subtype.range_coe, ← Finset.coe_image, hYZ]
  suffices h : AffineIndependent ℝ (L ∘ p) by rw [← hr]; exact h.range
  rcases isEmpty_or_nonempty ↥(Y : Set (ℝ^(k+1))) with he | hne
  · exact affineIndependent_of_subsingleton _ _
  · obtain ⟨y⟩ := hne
    have hp : AffineIndependent ℝ p := hX Y hYX (by omega)
    rw [affineIndependent_iff_linearIndependent_vsub ℝ p y] at hp
    rw [affineIndependent_iff_linearIndependent_vsub ℝ (L ∘ p) y]
    have hsp : Submodule.span ℝ (Set.range (fun i : {i // i ≠ y} => p i -ᵥ p y)) ≤
        vectorSpan ℝ (Y : Set (ℝ^(k+1))) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact vsub_mem_vectorSpan ℝ i.val.prop y.prop
    have hm := hp.map ((hker Y hYX hYc).mono_left hsp)
    convert hm using 1
    funext i
    simp [Function.comp_apply, vsub_eq_sub, map_sub]

theorem raise {k n N : ℕ} (hk : 1 ≤ k) (hN : N ∈ cardSet k n) : N ∈ cardSet (k + 1) n := by
  classical
  intro X hX hc
  obtain ⟨L, hL, hgp⟩ := projection hk X hX
  exact lift_convex L X hL (hN _ hgp (by rwa [Finset.card_image_of_injOn hL]))

theorem raise_all {k n N : ℕ} (hk : 3 ≤ k) (hN : N ∈ cardSet 3 n) : N ∈ cardSet k n := by
  induction k, hk using Nat.le_induction with
  | base => exact hN
  | succ d hd ih => exact raise (by omega) ih

end OMA.PZ

theorem OMA.solution : type_of% @Erdos651.erdos_651.variants.pohoata_zakharov := by
  intro k hk ε hε
  filter_upwards [OMA.PZ.core3 ε hε] with n ⟨N, hN, hle⟩
  exact le_trans (by exact_mod_cast f_le (OMA.PZ.raise_all hk hN)) hle
