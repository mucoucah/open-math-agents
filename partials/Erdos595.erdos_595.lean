import FormalConjectures.ErdosProblems.«595»
import Mathlib.SetTheory.Cardinal.Continuum

/-! Obstructions to constructing a witness for Erdős Problem 595. -/

-- Problem: Erdős Problem 595 (\$250)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/595.lean:54 (declaration Erdos595.erdos_595)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Erdos595

open SimpleGraph Cardinal
open scoped Sym2

/-- Vertices with binary sequence labels give a countable edge cover whenever
the subgraph formed by edges within label fibers is triangle-free. -/
theorem cover_of_triangleFree_fibers {V : Type*} (G : SimpleGraph V)
    (label : V → ℕ → Bool)
    (h : ∀ ⦃a b c⦄, G.Adj a b → G.Adj a c → G.Adj b c →
      label a = label b → label a = label c → False) :
    _root_.Erdos595.IsCountableUnionOfTriangleFree G := by
  classical
  let same : SimpleGraph V := {
    Adj := fun a b => G.Adj a b ∧ label a = label b
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  let cut (n : ℕ) : SimpleGraph V := {
    Adj := fun a b => G.Adj a b ∧ label a n ≠ label b n
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => h.2 rfl⟩ }
  let H : ℕ → SimpleGraph V
    | 0 => same
    | n + 1 => cut n
  refine ⟨H, ?_, ?_⟩
  · intro i s hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
    cases i with
    | zero => exact h hab.1 hac.1 hbc.1 hab.2 hac.2
    | succ n =>
      have h₁ := hab.2
      have h₂ := hac.2
      have h₃ := hbc.2
      change label a n ≠ label b n at h₁
      change label a n ≠ label c n at h₂
      change label b n ≠ label c n at h₃
      revert h₁ h₂ h₃
      cases label a n <;> cases label b n <;> cases label c n <;> decide
  · ext a b
    rw [iSup_adj]
    constructor
    · intro hab
      by_cases heq : label a = label b
      · exact ⟨0, hab, heq⟩
      · obtain ⟨n, hn⟩ : ∃ n, label a n ≠ label b n := by
          by_contra! hall
          exact heq (funext hall)
        exact ⟨n + 1, hab, hn⟩
    · rintro ⟨i, hi⟩
      cases i <;> exact hi.1

/-- In particular, a witness to Erdős 595 must have more than continuum
many vertices. -/
theorem cover_of_binary_embedding {V : Type*} (G : SimpleGraph V) (f : V ↪ (ℕ → Bool)) :
    _root_.Erdos595.IsCountableUnionOfTriangleFree G := by
  apply cover_of_triangleFree_fibers G f
  intro a b c hab hac hbc heq heq'
  exact hab.ne (f.injective heq)

/-- An edge partition whose triangles lie entirely in individual parts can
reuse the same countable palette in every part. -/
theorem cover_of_triangle_partition {V ι : Type*} (K : ι → SimpleGraph V)
    (hparts : ∀ i, _root_.Erdos595.IsCountableUnionOfTriangleFree (K i))
    (htriangle : ∀ ⦃i j a b c⦄, (K i).Adj a b → (K j).Adj a c →
      (⨆ k, K k).Adj b c → i = j) :
    _root_.Erdos595.IsCountableUnionOfTriangleFree (⨆ i, K i) := by
  classical
  choose H hfree hsup using hparts
  have hle (i : ι) (n : ℕ) : H i n ≤ K i := hsup i ▸ le_iSup (H i) n
  refine ⟨fun n => ⨆ i, H i n, ?_, ?_⟩
  · intro n s hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
    obtain ⟨i, hab⟩ := iSup_adj.mp hab
    obtain ⟨j, hac⟩ := iSup_adj.mp hac
    obtain ⟨k, hbc⟩ := iSup_adj.mp hbc
    have hij := htriangle (hle i n hab) (hle j n hac) (iSup_adj.mpr ⟨k, hle k n hbc⟩)
    have hik := htriangle (hle i n hab.symm) (hle k n hbc) (iSup_adj.mpr ⟨j, hle j n hac⟩)
    subst j k
    exact hfree i n {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  · conv_lhs => enter [1, i]; rw [hsup i]
    exact iSup_comm

/-- Isolated vertices do not affect the binary labeling argument. -/
theorem cover_of_small_support {V : Type*} (G : SimpleGraph V) (h : #G.support ≤ 𝔠) :
    _root_.Erdos595.IsCountableUnionOfTriangleFree G := by
  classical
  have hb : lift #G.support ≤ lift #(ℕ → Bool) := by
    simpa [mk_arrow, mk_bool, mk_nat] using h
  obtain ⟨f⟩ := lift_mk_le'.mp hb
  let label (v : V) : ℕ → Bool := if hv : v ∈ G.support then f ⟨v, hv⟩ else fun _ => false
  apply cover_of_triangleFree_fibers G label
  intro a b c hab hac hbc heq heq'
  have hf : f ⟨a, hab.mem_support_left⟩ = f ⟨b, hab.mem_support_right⟩ := by
    simpa only [label, dif_pos hab.mem_support_left, dif_pos hab.mem_support_right] using heq
  exact hab.ne (congrArg Subtype.val (f.injective hf))

private theorem mk_biUnion_le_continuum {α β : Type u} (A : α → Set β) (s : Set α)
    (hs : #s ≤ 𝔠) (hA : ∀ x ∈ s, #(A x) ≤ 𝔠) : #(⋃ x ∈ s, A x) ≤ 𝔠 := by
  calc
    _ ≤ #s * ⨆ x : s, #(A x.1) := mk_biUnion_le A s
    _ ≤ 𝔠 * 𝔠 := mul_le_mul' hs (ciSup_le' fun x => hA x x.property)
    _ = 𝔠 := continuum_mul_self

/-- Finite chains in a relation with at most continuum many successors at
each element reach at most continuum many elements. -/
private theorem mk_reachable_le_continuum {α : Type*} (r : α → α → Prop)
    (h : ∀ x, #{y | r x y} ≤ 𝔠) (x : α) :
    #{y | Relation.ReflTransGen r x y} ≤ 𝔠 := by
  let level : ℕ → Set α := Nat.rec {x} (fun _ S => ⋃ y ∈ S, {z | r y z})
  have hlevel : ∀ n, #↥(level n) ≤ 𝔠 := by
    intro n
    induction n with
    | zero => exact (mk_singleton x).le.trans (nat_lt_continuum 1).le
    | succ n ih => exact mk_biUnion_le_continuum _ _ ih fun y _ => h y
  have hsubset : {y | Relation.ReflTransGen r x y} ⊆ ⋃ n, level n := by
    intro y hy
    induction hy with
    | refl => exact Set.mem_iUnion.mpr ⟨0, rfl⟩
    | tail _ hyz ih =>
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ih
      exact Set.mem_iUnion.mpr ⟨n + 1, Set.mem_iUnion₂.mpr ⟨_, hn, hyz⟩⟩
  refine (mk_le_mk_of_subset hsubset).trans ?_
  apply lift_le_continuum.mp
  calc
    _ ≤ lift #ℕ * ⨆ n, lift #↥(level n) := mk_iUnion_le_lift level
    _ ≤ ℵ₀ * 𝔠 := mul_le_mul' (by simp) (ciSup_le' fun n => lift_le_continuum.mpr (hlevel n))
    _ = 𝔠 := aleph0_mul_continuum

private def shareTriangle {V : Type*} (G : SimpleGraph V) (e f : Sym2 V) : Prop :=
  ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ e = s(a, b) ∧ f = s(a, c)

private def triangleSetoid {V : Type*} (G : SimpleGraph V) : Setoid (Sym2 V) where
  r := Relation.ReflTransGen (shareTriangle G)
  iseqv := by
    let : Std.Symm (shareTriangle G) := ⟨by
      rintro _ _ ⟨a, b, c, hab, hac, hbc, he, hf⟩
      exact ⟨a, c, b, hac, hab, hbc.symm, hf, he⟩⟩
    exact ⟨fun _ => .refl, fun h => symm h, fun h h' => h.trans h'⟩

private def triangleBlock {V : Type*} (G : SimpleGraph V) (q : Quotient (triangleSetoid G)) :
    SimpleGraph V where
  Adj a b := G.Adj a b ∧ Quotient.mk (triangleSetoid G) s(a, b) = q
  symm := ⟨fun _ _ h => ⟨h.1.symm, Sym2.eq_swap ▸ h.2⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

private theorem mk_shareTriangle_le_continuum {V : Type*} (G : SimpleGraph V)
    (h : ∀ a b, G.Adj a b → #(G.commonNeighbors a b) ≤ 𝔠) (e : Sym2 V) :
    #{f | shareTriangle G e f} ≤ 𝔠 := by
  induction e using Sym2.ind with
  | h a b =>
    by_cases hab : G.Adj a b
    · let A := (fun c => s(a, c)) '' G.commonNeighbors a b
      let B := (fun c => s(b, c)) '' G.commonNeighbors a b
      have hsub : {f | shareTriangle G s(a, b) f} ⊆ A ∪ B := by
        rintro f ⟨p, q, c, hpq, hpc, hqc, he, rfl⟩
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨c, ⟨hpc, hqc⟩, rfl⟩
        · exact Or.inr ⟨c, ⟨hqc, hpc⟩, rfl⟩
      calc
        _ ≤ #(A ∪ B : Set (Sym2 V)) := mk_le_mk_of_subset hsub
        _ ≤ #A + #B := mk_union_le _ _
        _ ≤ 𝔠 + 𝔠 := add_le_add (mk_image_le.trans (h a b hab)) (mk_image_le.trans (h a b hab))
        _ = 𝔠 := continuum_add_self
    · have hempty : {f | shareTriangle G s(a, b) f} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro f ⟨p, q, c, hpq, hpc, hqc, he, hf⟩
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hab hpq
        · exact hab hpq.symm
      simp [hempty]

/-- If every edge belongs to at most continuum many triangles, the graph
has a countable triangle-free edge cover. -/
theorem cover_of_small_common_neighbors {V : Type*} (G : SimpleGraph V)
    (h : ∀ a b, G.Adj a b → #(G.commonNeighbors a b) ≤ 𝔠) :
    _root_.Erdos595.IsCountableUnionOfTriangleFree G := by
  classical
  let K := triangleBlock G
  have hsup : (⨆ q, K q) = G := by
    ext a b
    rw [iSup_adj]
    exact ⟨fun ⟨_, ha⟩ => ha.1, fun ha => ⟨_, ha, rfl⟩⟩
  rw [← hsup]
  apply cover_of_triangle_partition K
  · intro q
    obtain ⟨e, rfl⟩ := Quotient.mk_surjective q
    let E : Set (Sym2 V) := {f | Relation.ReflTransGen (shareTriangle G) e f}
    have hE : #E ≤ 𝔠 :=
      mk_reachable_le_continuum _ (mk_shareTriangle_le_continuum G h) e
    have hsupport : (K (Quotient.mk (triangleSetoid G) e)).support ⊆
        ⋃ f ∈ E, (f : Set V) := by
      intro a ha
      obtain ⟨b, hab⟩ := (K _).mem_support.mp ha
      exact Set.mem_iUnion₂.mpr ⟨s(a, b), (Quotient.exact hab.2.symm), Sym2.mem_iff.mpr (Or.inl rfl)⟩
    apply cover_of_small_support
    refine (mk_le_mk_of_subset hsupport).trans (mk_biUnion_le_continuum _ _ hE ?_)
    intro f hf
    induction f using Sym2.ind with
    | h a b =>
      have hs : (↑s(a, b) : Set V) = {a, b} := by ext x; simp
      rw [hs]
      exact (lt_aleph0_of_finite _).le.trans aleph0_le_continuum
  · intro i j a b c hab hac hbc
    rw [hsup] at hbc
    have hlocal : (triangleSetoid G).r s(a, b) s(a, c) :=
      Relation.ReflTransGen.single ⟨a, b, c, hab.1, hac.1, hbc, rfl, rfl⟩
    exact hab.2.symm.trans ((Quotient.sound hlocal).trans hac.2)

theorem cover_iSup_nat {V : Type*} (G : ℕ → SimpleGraph V)
    (hG : ∀ i, _root_.Erdos595.IsCountableUnionOfTriangleFree (G i)) :
    _root_.Erdos595.IsCountableUnionOfTriangleFree (⨆ i, G i) := by
  classical
  choose H hfree hsup using hG
  let K (n : ℕ) := H (Nat.pairEquiv.symm n).1 (Nat.pairEquiv.symm n).2
  refine ⟨K, fun n => hfree _ _, ?_⟩
  ext a b
  simp only [iSup_adj, K, hsup]
  constructor
  · rintro ⟨i, j, hij⟩
    exact ⟨Nat.pairEquiv (i, j), by simpa using hij⟩
  · rintro ⟨n, hn⟩
    exact ⟨_, _, hn⟩

def restrictByCodegree {V : Type*} (G : SimpleGraph V) (p : Cardinal → Prop) :
    SimpleGraph V where
  Adj a b := G.Adj a b ∧ p #(G.commonNeighbors a b)
  symm := ⟨fun a b h => ⟨h.1.symm, G.commonNeighbors_symm a b ▸ h.2⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- The obstruction to a countable cover survives removing all edges that
belong to at most continuum many triangles of the original graph. -/
theorem not_cover_large_codegree_subgraph {V : Type*} (G : SimpleGraph V)
    (h : ¬ _root_.Erdos595.IsCountableUnionOfTriangleFree G) :
    ¬ _root_.Erdos595.IsCountableUnionOfTriangleFree (restrictByCodegree G (𝔠 < ·)) := by
  intro hlarge
  let low := restrictByCodegree G (· ≤ 𝔠)
  have hlow : _root_.Erdos595.IsCountableUnionOfTriangleFree low := by
    apply cover_of_small_common_neighbors
    intro a b hab
    have hsub : low.commonNeighbors a b ⊆ G.commonNeighbors a b := by
      intro c hc
      exact ⟨hc.1.1, hc.2.1⟩
    exact (mk_le_mk_of_subset hsub).trans hab.2
  let H : ℕ → SimpleGraph V
    | 0 => low
    | _ + 1 => restrictByCodegree G (𝔠 < ·)
  have heq : (⨆ i, H i) = G := by
    ext a b
    rw [iSup_adj]
    constructor
    · rintro ⟨i, hi⟩
      cases i <;> exact hi.1
    · intro hab
      rcases le_or_gt #(G.commonNeighbors a b) 𝔠 with hle | hgt
      · exact ⟨0, hab, hle⟩
      · exact ⟨1, hab, hgt⟩
  apply h
  rw [← heq]
  apply cover_iSup_nat
  intro i
  cases i
  · exact hlow
  · exact hlarge

/-- A witness has an edge with an independent common neighborhood larger
than the continuum. -/
theorem exists_large_independent_common_neighbors {V : Type*} (G : SimpleGraph V)
    (hk : G.CliqueFree 4) (h : ¬ _root_.Erdos595.IsCountableUnionOfTriangleFree G) :
    ∃ a b, G.Adj a b ∧ 𝔠 < #(G.commonNeighbors a b) ∧ G.IsIndepSet (G.commonNeighbors a b) := by
  classical
  have hlarge : ∃ a b, G.Adj a b ∧ 𝔠 < #(G.commonNeighbors a b) := by
    by_contra! hn
    exact h (cover_of_small_common_neighbors G hn)
  obtain ⟨a, b, hab, hcard⟩ := hlarge
  refine ⟨a, b, hab, hcard, ?_⟩
  intro c hc d hd hne hcd
  have ht : G.IsNClique 3 {a, b, c} := is3Clique_triple_iff.mpr ⟨hab, hc.1, hc.2⟩
  obtain ⟨x, hx, hdx⟩ := ht.exists_not_adj_of_cliqueFree_succ hk d
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hdx hd.1.symm
  · exact hdx hd.2.symm
  · exact hdx hcd.symm

end OMA.Erdos595

theorem OMA.solution : type_of% @Erdos595.erdos_595 := by
  sorry

