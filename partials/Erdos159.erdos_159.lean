import FormalConjectures.ErdosProblems.«159»

/-! Finite triangle counting for the four-cycle versus clique Ramsey problem. -/

-- Problem: Erdős Problem 159
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/159.lean:43 (declaration Erdos159.erdos_159)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Erdos159Relay

open scoped BigOperators Classical
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Delete one representative of each forbidden set that lies in the sample. -/
private lemma avoid_family (S : Finset V) (F : Finset (Finset V))
    (hne : ∀ B ∈ F, B.Nonempty) :
    ∃ U ⊆ S, (∀ B ∈ F, ¬ B ⊆ U) ∧
      S.card ≤ U.card + (F.filter (· ⊆ S)).card := by
  classical
  let Q := F.filter (· ⊆ S)
  let pick : Q → V := fun B => (hne B.1 (Finset.mem_filter.mp B.2).1).choose
  let R := Q.attach.image (fun B => pick B)
  let U := S \ R
  refine ⟨U, Finset.sdiff_subset, ?_, ?_⟩
  · intro B hB hBU
    have hBS : B ⊆ S := hBU.trans Finset.sdiff_subset
    let b : Q := ⟨B, Finset.mem_filter.mpr ⟨hB, hBS⟩⟩
    have hpB : pick b ∈ B := (hne b.1 (Finset.mem_filter.mp b.2).1).choose_spec
    have hpR : pick b ∈ R := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
    exact (Finset.mem_sdiff.mp (hBU hpB)).2 hpR
  · have hR : R.card ≤ Q.card := Finset.card_image_le.trans_eq Finset.card_attach
    exact Finset.card_le_card_sdiff_add_card.trans (Nat.add_le_add_left hR _)

/-- Average the vertex deletion bound over all samples of size `k`. -/
private lemma fixed_sample_bound (S : Finset V) (F : Finset (Finset V))
    (hF : ∀ B ∈ F, B ⊆ S ∧ B.card = 3) (L k : ℕ) (hk : 3 ≤ k)
    (hcap : ∀ U ⊆ S, (∀ B ∈ F, ¬ B ⊆ U) → U.card ≤ L) :
    k * S.card.choose k ≤ L * S.card.choose k + F.card * (S.card - 3).choose (k - 3) := by
  classical
  let P := S.powersetCard k
  have hsample (A : Finset V) (hA : A ∈ P) : k ≤ L + (F.filter (· ⊆ A)).card := by
    obtain ⟨hAS, hAk⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨U, hUA, hUF, hcount⟩ := avoid_family A F (fun B hB => by
      apply Finset.card_pos.mp
      rw [(hF B hB).2]
      decide)
    rw [← hAk]
    exact hcount.trans (Nat.add_le_add_right (hcap U (hUA.trans hAS) hUF) _)
  have card_filter_eq_sum (Q : Finset (Finset V)) (p : Finset V → Prop)
      [DecidablePred p] :
      (Q.filter p).card = ∑ B ∈ Q, if p B then 1 else 0 :=
    (Finset.sum_boole (R := ℕ) p Q).symm
  have hcount :
      (∑ A ∈ P, (F.filter (· ⊆ A)).card) = F.card * (S.card - 3).choose (k - 3) := by
    calc
      _ = ∑ B ∈ F, ((S.powersetCard k).filter (B ⊆ ·)).card := by
        simp only [card_filter_eq_sum, P]
        exact Finset.sum_comm
      _ = F.card * (S.card - 3).choose (k - 3) := by
        apply Finset.sum_const_nat
        intro B hB
        obtain ⟨hBS, hB3⟩ := hF B hB
        rw [Finset.card_filter_powersetCard_subset B S k hBS (hB3 ▸ hk), hB3]
  have hsum := Finset.sum_le_sum hsample
  rw [Finset.sum_add_distrib, hcount] at hsum
  simpa [P, Finset.card_powersetCard, mul_comm] using hsum

/-- A bound on triangle-free induced subsets forces a cubic lower bound on the
number of triangles, once the vertex set is more than twice the bound. -/
lemma triangle_count_of_induced_cap (G : SimpleGraph V) (S : Finset V) (L : ℕ)
    (hL : 2 ≤ L)
    (hcap : ∀ U ⊆ S, (∀ B ⊆ U, ¬ G.IsNClique 3 B) → U.card ≤ L) :
    S.card ≤ 2 * L ∨
      S.card ^ 3 ≤ 32 * ((S.powersetCard 3).filter (G.IsNClique 3)).card * L ^ 2 := by
  classical
  let F := (S.powersetCard 3).filter (G.IsNClique 3)
  let m := S.card
  by_cases hm : m ≤ 2 * L
  · exact Or.inl hm
  right
  have hLk : 3 ≤ 2 * L := by omega
  have hkm : 2 * L ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hsample := fixed_sample_bound S F
    (fun B hB => Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB).1) L (2 * L) hLk
    (fun U hUS hUF => hcap U hUS (fun B hBU hB =>
      hUF B (Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hBU.trans hUS, hB.card_eq⟩, hB⟩) hBU))
  change 2 * L * m.choose (2 * L) ≤
    L * m.choose (2 * L) + F.card * (m - 3).choose (2 * L - 3) at hsample
  have hcancel : L * m.choose (2 * L) ≤ F.card * (m - 3).choose (2 * L - 3) := by
    rw [show 2 * L * m.choose (2 * L) =
      L * m.choose (2 * L) + L * m.choose (2 * L) by ring] at hsample
    exact Nat.le_of_add_le_add_left hsample
  have hp : 0 < m.choose (2 * L) := Nat.choose_pos hkm
  have hchoose : L * m.choose 3 ≤ F.card * (2 * L).choose 3 := by
    apply Nat.le_of_mul_le_mul_right (c := m.choose (2 * L)) _ hp
    calc
      (L * m.choose 3) * m.choose (2 * L) =
          (L * m.choose (2 * L)) * m.choose 3 := by ring
      _ ≤ (F.card * (m - 3).choose (2 * L - 3)) * m.choose 3 :=
        Nat.mul_le_mul_right _ hcancel
      _ = F.card * (m.choose 3 * (m - 3).choose (2 * L - 3)) := by ring
      _ = (F.card * (2 * L).choose 3) * m.choose (2 * L) := by
        rw [← Nat.choose_mul hLk]
        ring
  have three_choose (a : ℕ) : 6 * a.choose 3 = a * (a - 1) * (a - 2) := by
    calc
      _ = a.descFactorial 3 := (Nat.descFactorial_eq_factorial_mul_choose a 3).symm
      _ = _ := by simp [Nat.descFactorial_succ, Nat.mul_comm]
  have htriple : L * (m * (m - 1) * (m - 2)) ≤
      F.card * (2 * L * (2 * L - 1) * (2 * L - 2)) := by
    rw [← three_choose, ← three_choose]
    simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left 6 hchoose
  have hleft : m ^ 3 ≤ 4 * (m * (m - 1) * (m - 2)) := by
    calc
      m ^ 3 = m * m * m := by ring
      _ ≤ m * (2 * (m - 1)) * (2 * (m - 2)) := by
        gcongr <;> omega
      _ = _ := by ring
  have hright : 2 * L * (2 * L - 1) * (2 * L - 2) ≤ 8 * L ^ 3 := by
    calc
      _ ≤ 2 * L * (2 * L) * (2 * L) := by gcongr <;> omega
      _ = _ := by ring
  change m ^ 3 ≤ 32 * F.card * L ^ 2
  apply Nat.le_of_mul_le_mul_right (c := L) _ (by omega)
  calc
    m ^ 3 * L ≤ (4 * (m * (m - 1) * (m - 2))) * L :=
      Nat.mul_le_mul_right _ hleft
    _ = 4 * (L * (m * (m - 1) * (m - 2))) := by ring
    _ ≤ 4 * (F.card * (2 * L * (2 * L - 1) * (2 * L - 2))) :=
      Nat.mul_le_mul_left _ htriple
    _ ≤ 4 * (F.card * (8 * L ^ 3)) := by gcongr
    _ = (32 * F.card * L ^ 2) * L := by ring

/-- The number of triangles entirely contained in a vertex set. -/
noncomputable def triangleCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((S.powersetCard 3).filter (G.IsNClique 3)).card

/-- A triangle-free induced cap of `L` gives a cap of `6 * D * L` on vertex sets
having at most `D ^ 2` triangles per vertex. -/
lemma card_le_of_sparse_triangles (G : SimpleGraph V) (S : Finset V)
    {L : ℕ} (hL : 2 ≤ L) {D : ℝ} (hD : 1 ≤ D)
    (hcap : ∀ U ⊆ S, (∀ B ⊆ U, ¬ G.IsNClique 3 B) → U.card ≤ L)
    (htri : (triangleCount G S : ℝ) ≤ (S.card : ℝ) * D ^ 2) :
    (S.card : ℝ) ≤ 6 * D * L := by
  let m : ℝ := S.card
  change m ≤ 6 * D * (L : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hL₀ : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  rcases triangle_count_of_induced_cap G S L hL hcap with hsmall | hcubic
  · have hle : m ≤ 2 * (L : ℝ) := by
      change (S.card : ℝ) ≤ 2 * (L : ℝ)
      exact_mod_cast hsmall
    nlinarith only [hle, hL₀, mul_nonneg (sub_nonneg.mpr hD) hL₀]
  by_cases hm₀ : m = 0
  · rw [hm₀]
    positivity
  have hmpos : 0 < m := lt_of_le_of_ne hm (fun h => hm₀ h.symm)
  change S.card ^ 3 ≤ 32 * triangleCount G S * L ^ 2 at hcubic
  have hcubic' : m ^ 3 ≤ 32 * (triangleCount G S : ℝ) * (L : ℝ) ^ 2 := by
    change (S.card : ℝ) ^ 3 ≤ 32 * (triangleCount G S : ℝ) * (L : ℝ) ^ 2
    exact_mod_cast hcubic
  have hsq : m ^ 2 ≤ 32 * (D * (L : ℝ)) ^ 2 := by
    apply le_of_mul_le_mul_of_pos_left _ hmpos
    calc
      m * m ^ 2 = m ^ 3 := by ring
      _ ≤ 32 * (triangleCount G S : ℝ) * (L : ℝ) ^ 2 := hcubic'
      _ ≤ 32 * (m * D ^ 2) * (L : ℝ) ^ 2 := by gcongr
      _ = m * (32 * (D * (L : ℝ)) ^ 2) := by ring
  apply (sq_le_sq₀ hm (by positivity : 0 ≤ 6 * D * (L : ℝ))).mp
  nlinarith only [hsq, sq_nonneg (D * (L : ℝ))]

/-- The number of triangles contained in `S` that meet the vertex `x`. -/
noncomputable def triangleDegree (G : SimpleGraph V) (S : Finset V) (x : V) : ℕ :=
  ((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card

private lemma triangle_count_insert_le (G : SimpleGraph V) {R S : Finset V} {x : V}
    (hinc : insert x R ⊆ S) :
    triangleCount G (insert x R) ≤ triangleCount G R + triangleDegree G S x := by
  classical
  let F := (R.powersetCard 3).filter (G.IsNClique 3)
  let Q := (S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)
  have hsubset : ((insert x R).powersetCard 3).filter (G.IsNClique 3) ⊆ F ∪ Q := by
    intro B hB
    obtain ⟨hb, htri⟩ := Finset.mem_filter.mp hB
    obtain ⟨hBsub, hB3⟩ := Finset.mem_powersetCard.mp hb
    apply Finset.mem_union.mpr
    by_cases hxb : x ∈ B
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hBsub.trans hinc, hB3⟩, htri, hxb⟩)
    · have hBR : B ⊆ R := by
        intro y hy
        rcases Finset.mem_insert.mp (hBsub hy) with h | h
        · exact (hxb (h ▸ hy)).elim
        · exact h
      exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hBR, hB3⟩, htri⟩)
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le F Q)

/-- Iteratively peel vertices with few incident triangles. The triangles in the
removed set can each be charged to their first vertex removed. -/
lemma split_at_triangle_degree (G : SimpleGraph V) (S : Finset V) (d : ℝ) :
    ∃ R U : Finset V, Disjoint R U ∧ R ∪ U = S ∧
      (triangleCount G R : ℝ) ≤ (R.card : ℝ) * d ∧
      ∀ x ∈ U, d < (triangleDegree G U x : ℝ) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hdense : ∀ x ∈ S, d < (triangleDegree G S x : ℝ)
    · have hempty : (∅ : Finset V).powersetCard 3 = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      exact ⟨∅, S, by simp, by simp, by simp [triangleCount, hempty], hdense⟩
    push Not at hdense
    obtain ⟨x, hx, hdeg⟩ := hdense
    obtain ⟨R, U, hdisj, hsplit, hRc, hUd⟩ := ih (S.erase x) (Finset.erase_ssubset hx)
    have hRsub : R ⊆ S.erase x := hsplit ▸ Finset.subset_union_left
    have hUsub : U ⊆ S.erase x := hsplit ▸ Finset.subset_union_right
    have hxR : x ∉ R := fun h => Finset.notMem_erase x S (hRsub h)
    have hxU : x ∉ U := fun h => Finset.notMem_erase x S (hUsub h)
    refine ⟨insert x R, U, Finset.disjoint_insert_left.mpr ⟨hxU, hdisj⟩, ?_, ?_, hUd⟩
    · rw [Finset.insert_union, hsplit, Finset.insert_erase hx]
    have hinc : insert x R ⊆ S := Finset.insert_subset hx (hRsub.trans (Finset.erase_subset _ _))
    have hcount := triangle_count_insert_le G hinc
    have hcount' : (triangleCount G (insert x R) : ℝ) ≤
        (triangleCount G R : ℝ) + (triangleDegree G S x : ℝ) := by exact_mod_cast hcount
    rw [Finset.card_insert_of_notMem hxR, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact hcount'.trans (add_le_add hRc hdeg)

/-- Combine the sparse bound and a bound for sets of large minimum triangle degree. -/
lemma card_le_of_triangle_degree_caps (G : SimpleGraph V) (S : Finset V)
    {L : ℕ} (hL : 2 ≤ L) {D M : ℝ} (hD : 1 ≤ D)
    (hcap : ∀ U ⊆ S, (∀ B ⊆ U, ¬ G.IsNClique 3 B) → U.card ≤ L)
    (hcore : ∀ U ⊆ S, (∀ x ∈ U, D ^ 2 < (triangleDegree G U x : ℝ)) →
      (U.card : ℝ) ≤ M) :
    (S.card : ℝ) ≤ 6 * D * L + M := by
  obtain ⟨R, U, hdisj, hsplit, hR, hU⟩ := split_at_triangle_degree G S (D ^ 2)
  have hRsub : R ⊆ S := hsplit ▸ Finset.subset_union_left
  have hUsub : U ⊆ S := hsplit ▸ Finset.subset_union_right
  have hsparse := card_le_of_sparse_triangles G R hL hD
    (fun T hTR => hcap T (hTR.trans hRsub)) hR
  rw [← hsplit, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
  exact add_le_add hsparse (hcore U hUsub hU)

/-- A graph avoiding both Ramsey alternatives. -/
def RamseyBad (n m : ℕ) (G : SimpleGraph (Fin m)) : Prop :=
  ¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ

/-- Power bound for sets with large minimum triangle degree. -/
def LargeTriangleDegreeBound (ε B : ℝ) : Prop :=
  ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → RamseyBad n m G →
      (∀ x ∈ S, (n : ℝ) ^ ε < (triangleDegree G S x : ℝ)) →
      (S.card : ℝ) ≤ B * (n : ℝ) ^ (2 - ε / 2)

/-- A power saving for triangle-free subsets, together with one for subsets of
minimum triangle degree above `n ^ ε`, gives an exponent of `2 - ε / 2`. -/
theorem ramsey_of_triangle_degree_bounds {ε A B : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hfree : ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → RamseyBad n m G →
      (∀ T ⊆ S, ¬ G.IsNClique 3 T) → (S.card : ℝ) ≤ A * (n : ℝ) ^ (2 - ε))
    (hcore : LargeTriangleDegreeBound ε B) :
    ∀ n : ℕ, 1 ≤ n → (graphRamsey (cycleGraph 4) (completeGraph (Fin n)) : ℝ) ≤
      (6 * (A + 3) + B + 1) * (n : ℝ) ^ (2 - ε / 2) := by
  intro n hn
  let D : ℝ := (n : ℝ) ^ (ε / 2)
  let Y : ℝ := (n : ℝ) ^ (2 - ε)
  let X : ℝ := (n : ℝ) ^ (2 - ε / 2)
  let L := ⌈A * Y⌉₊ + 2
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hD : 1 ≤ D := Real.one_le_rpow hnreal (by linarith)
  have hY : 1 ≤ Y := Real.one_le_rpow hnreal (by linarith)
  have hX : 1 ≤ X := Real.one_le_rpow hnreal (by linarith)
  have hApos : 0 ≤ A := by linarith
  have hYpos : 0 ≤ Y := by linarith
  have hXpos : 0 ≤ X := by linarith
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hceil : (⌈A * Y⌉₊ : ℝ) ≤ A * Y + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hApos hYpos)).le
  have hLupper : (L : ℝ) ≤ (A + 3) * Y := by
    dsimp [L]
    push_cast
    linarith only [hY, hceil]
  have hDY : D * Y = X := by
    dsimp [D, Y, X]
    rw [← Real.rpow_add hnpos, show ε / 2 + (2 - ε) = 2 - ε / 2 by ring]
  have hDsq : D ^ 2 = (n : ℝ) ^ ε := by
    dsimp [D]
    rw [pow_two, ← Real.rpow_add hnpos, show ε / 2 + ε / 2 = ε by ring]
  let P := (6 * (A + 3) + B) * X
  have hP : 0 ≤ P := by
    exact mul_nonneg (by linarith) hXpos
  have hbad_cap (m : ℕ) (G : SimpleGraph (Fin m)) (hbad : RamseyBad n m G) : (m : ℝ) ≤ P := by
    have hc (U : Finset (Fin m)) (_ : U ⊆ Finset.univ)
        (hU : ∀ T ⊆ U, ¬ G.IsNClique 3 T) : U.card ≤ L := by
      have hcU : U.card ≤ ⌈A * Y⌉₊ := by
        exact_mod_cast (hfree n m G U hn hbad hU).trans (Nat.le_ceil (A * Y))
      dsimp [L]
      omega
    have hd (U : Finset (Fin m)) (_ : U ⊆ Finset.univ)
        (hU : ∀ x ∈ U, D ^ 2 < (triangleDegree G U x : ℝ)) : (U.card : ℝ) ≤ B * X := by
      rw [hDsq] at hU
      exact hcore n m G U hn hbad hU
    have hbound : (m : ℝ) ≤ 6 * D * L + B * X := by
      simpa using card_le_of_triangle_degree_caps G Finset.univ hL hD hc hd
    calc
      _ ≤ 6 * D * L + B * X := hbound
      _ ≤ 6 * D * ((A + 3) * Y) + B * X := by
        gcongr
      _ = P := by
        dsimp [P]
        rw [← hDY]
        ring
  let N := ⌊P⌋₊ + 1
  have hN : P < (N : ℝ) := by simpa [N] using Nat.lt_floor_add_one P
  have hit (G : SimpleGraph (Fin N)) :
      (cycleGraph 4).IsContained G ∨ (completeGraph (Fin n)).IsContained Gᶜ := by
    by_contra h
    rw [not_or] at h
    exact hN.not_ge (hbad_cap N G h)
  have hRamsey : graphRamsey (cycleGraph 4) (completeGraph (Fin n)) ≤ N := Nat.sInf_le hit
  calc
    _ ≤ (N : ℝ) := by exact_mod_cast hRamsey
    _ ≤ P + 1 := by simpa [N] using add_le_add_right (Nat.floor_le hP) (1 : ℝ)
    _ ≤ _ := by change P + 1 ≤ (6 * (A + 3) + B + 1) * X; linarith only [hX, show P = _ from rfl]

private lemma indep_budget_after_neighborhood (G : SimpleGraph V) {r : ℕ} {S : Finset V}
    {x : V} (hx : x ∈ S)
    (hind : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r + 1)
    (I : Finset V) (hIR : I ⊆ S \ insert x (S.filter (G.Adj x)))
    (hI : G.IsIndepSet (I : Set V)) : I.card ≤ r := by
  classical
  have hRsub : S \ insert x (S.filter (G.Adj x)) ⊆ S := Finset.sdiff_subset
  have hxN : x ∈ insert x (S.filter (G.Adj x)) := Finset.mem_insert_self _ _
  have hxI : x ∉ I := fun h => (Finset.mem_sdiff.mp (hIR h)).2 hxN
  have hi : G.IsIndepSet (↑(insert x I) : Set V) := by
    rw [Finset.coe_insert, isIndepSet_iff, Set.pairwise_insert_of_notMem hxI]
    refine ⟨hI, ?_⟩
    intro y hy
    have hyR := Finset.mem_sdiff.mp (hIR hy)
    have hxy : ¬ G.Adj x y := fun h =>
      hyR.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hyR.1, h⟩))
    exact ⟨hxy, fun hyx => hxy hyx.symm⟩
  have hiBound := hind (insert x I) (Finset.insert_subset hx (hIR.trans hRsub)) hi
  rw [Finset.card_insert_of_notMem hxI] at hiBound
  omega

/-- A low-degree vertex and its neighbours cost at most `d` vertices and one
unit of the independence budget. -/
private lemma minimum_degree_core (G : SimpleGraph V) (d r : ℕ) (S : Finset V)
    (hind : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r) :
    ∃ U ⊆ S, S.card ≤ U.card + r * d ∧
      ∀ x ∈ U, d ≤ (U.filter (G.Adj x)).card := by
  classical
  induction r generalizing S with
  | zero =>
    have hempty : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hs
      obtain ⟨x, hx⟩ := hs
      have hc := hind {x} (Finset.singleton_subset_iff.mpr hx) (by simp)
      simp at hc
    subst S
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ r ih =>
    by_cases hmin : ∀ x ∈ S, d ≤ (S.filter (G.Adj x)).card
    · exact ⟨S, le_rfl, Nat.le_add_right _ _, hmin⟩
    push Not at hmin
    obtain ⟨x, hx, hdeg⟩ := hmin
    let N := insert x (S.filter (G.Adj x))
    let R := S \ N
    have hRsub : R ⊆ S := Finset.sdiff_subset
    have hR : ∀ I ⊆ R, G.IsIndepSet (I : Set V) → I.card ≤ r :=
      indep_budget_after_neighborhood G hx hind
    obtain ⟨U, hUR, hcard, hU⟩ := ih R hR
    have hN : N.card ≤ d := (Finset.card_insert_le _ _).trans (by omega)
    have hS : S.card ≤ R.card + N.card := Finset.card_le_card_sdiff_add_card
    refine ⟨U, hUR.trans hRsub, ?_, hU⟩
    rw [Nat.succ_mul]
    omega

private lemma indep_card_le {m n : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : RamseyBad n m G) (I : Finset (Fin m)) (hI : G.IsIndepSet (I : Set (Fin m))) :
    I.card ≤ n - 1 := by
  classical
  have hlt : I.card < n := by
    by_contra! hge
    obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq hge
    apply hbad.2
    apply ((Gᶜ).not_cliqueFree_iff_top_isContained n).mp
    intro hfree
    have hclique : Gᶜ.IsClique (I : Set (Fin m)) := by
      simpa only [isClique_compl] using hI
    exact hfree J ⟨hclique.subset hJI, hJ⟩
  omega

/-- The triangle-free bound under the degree constraints of the R1 reduction. -/
def TriangleFreeWindowBound (ε A : ℝ) : Prop :=
  ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → RamseyBad n m G →
      (∀ x ∈ S, S.card ≤ 16 * n * ((S.filter (G.Adj x)).card + 1) ∧
        (S.filter (G.Adj x)).card ≤ 2 * (n - 1)) →
      (∀ T ⊆ S, ¬ G.IsNClique 3 T) → (S.card : ℝ) ≤ A * (n : ℝ) ^ (2 - ε)

private lemma budget_le_quarter (m n : ℕ) :
    4 * ((n - 1) * (m / (4 * n))) ≤ m := by
  let d := m / (4 * n)
  change 4 * ((n - 1) * d) ≤ m
  calc
    _ = (4 * (n - 1)) * d := by ring
    _ ≤ (4 * n) * d := by gcongr; omega
    _ ≤ m := by simpa [d, Nat.mul_comm] using Nat.div_mul_le_self m (4 * n)

private lemma lower_degree_window {n m s k : ℕ} (hn : 1 ≤ n) (hs : s ≤ m)
    (hk : m / (4 * n) ≤ k) : s ≤ 16 * n * (k + 1) := by
  have hlarge : m < (k + 1) * (4 * n) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 4 * n)).mp (Nat.lt_succ_of_le hk)
  calc
    s ≤ m := hs
    _ ≤ (k + 1) * (4 * n) := hlarge.le
    _ ≤ (k + 1) * (16 * n) := by gcongr; omega
    _ = _ := Nat.mul_comm _ _

/-- The triangle-free hypothesis of the Ramsey transfer follows from a bound
on the degree window used by the existing R1 reduction. -/
lemma triangle_free_cap_of_degree_window {ε A : ℝ}
    (hwindow : TriangleFreeWindowBound ε A) :
    ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → RamseyBad n m G →
      (∀ T ⊆ S, ¬ G.IsNClique 3 T) → (S.card : ℝ) ≤ (2 * A) * (n : ℝ) ^ (2 - ε) := by
  classical
  intro n m G S hn hbad hfree
  let d := S.card / (4 * n)
  obtain ⟨U, hUS, hsize, hdeg⟩ :=
    minimum_degree_core G d (n - 1) S (fun I _ hI => indep_card_le hbad I hI)
  have hbudget : 4 * ((n - 1) * d) ≤ S.card := budget_le_quarter S.card n
  have hcompare : S.card ≤ 2 * U.card := by omega
  have hcompare' : (S.card : ℝ) ≤ 2 * (U.card : ℝ) := by exact_mod_cast hcompare
  have hUfree (T : Finset (Fin m)) (hTU : T ⊆ U) : ¬ G.IsNClique 3 T := hfree T (hTU.trans hUS)
  have hUwindow (x : Fin m) (hx : x ∈ U) :
      U.card ≤ 16 * n * ((U.filter (G.Adj x)).card + 1) ∧
        (U.filter (G.Adj x)).card ≤ 2 * (n - 1) := by
    constructor
    · exact lower_degree_window hn (Finset.card_le_card hUS) (hdeg x hx)
    · have hi : G.IsIndepSet (↑(U.filter (G.Adj x)) : Set (Fin m)) := by
        intro y hy z hz hyz hadj
        obtain ⟨hyU, hxy⟩ := Finset.mem_filter.mp hy
        obtain ⟨hzU, hxz⟩ := Finset.mem_filter.mp hz
        have hsub : ({x, y, z} : Finset (Fin m)) ⊆ U :=
          Finset.insert_subset hx (Finset.insert_subset hyU (Finset.singleton_subset_iff.mpr hzU))
        exact hUfree _ hsub (is3Clique_triple_iff.mpr ⟨hxy, hxz, hadj⟩)
      have b := indep_card_le hbad (U.filter (G.Adj x)) hi
      omega
  have hu := hwindow n m G U hn hbad hUwindow hUfree
  linarith only [hcompare', hu]

/-- Prune vertices of low ordinary degree and low triangle degree in the same
process. The ordinary-degree deletions have an independent set of witnesses. -/
lemma split_at_both_degrees (G : SimpleGraph V) (d : ℕ) (τ : ℝ)
    (S : Finset V) (r : ℕ)
    (hind : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r) :
    ∃ R U : Finset V, R ⊆ S ∧ U ⊆ S ∧
      S.card ≤ R.card + U.card + r * d ∧
      (triangleCount G R : ℝ) ≤ (R.card : ℝ) * τ ∧
      ∀ x ∈ U, d ≤ (U.filter (G.Adj x)).card ∧ τ < (triangleDegree G U x : ℝ) := by
  classical
  induction S using Finset.strongInductionOn generalizing r with
  | _ S ih =>
    by_cases hdeg : ∀ x ∈ S, d ≤ (S.filter (G.Adj x)).card
    · by_cases htri : ∀ x ∈ S, τ < (triangleDegree G S x : ℝ)
      · have hempty : (∅ : Finset V).powersetCard 3 = ∅ :=
          Finset.powersetCard_eq_empty.mpr (by simp)
        exact ⟨∅, S, by simp, le_rfl, by simp, by simp [triangleCount, hempty],
          fun x hx => ⟨hdeg x hx, htri x hx⟩⟩
      push Not at htri
      obtain ⟨x, hx, hxd⟩ := htri
      have hsub := Finset.erase_subset x S
      obtain ⟨R, U, hR, hU, hsize, hcount, hwin⟩ :=
        ih (S.erase x) (Finset.erase_ssubset hx) r (fun I hI => hind I (hI.trans hsub))
      have hxR : x ∉ R := fun h => Finset.notMem_erase x S (hR h)
      have hinc := Finset.insert_subset hx (hR.trans hsub)
      refine ⟨insert x R, U, hinc, hU.trans hsub, ?_, ?_, hwin⟩
      · have herase := Finset.card_erase_add_one hx
        rw [Finset.card_insert_of_notMem hxR]
        omega
      · have hstep : (triangleCount G (insert x R) : ℝ) ≤
            (triangleCount G R : ℝ) + (triangleDegree G S x : ℝ) := by
          exact_mod_cast triangle_count_insert_le G hinc
        rw [Finset.card_insert_of_notMem hxR, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        exact hstep.trans (add_le_add hcount hxd)
    push Not at hdeg
    obtain ⟨x, hx, hxd⟩ := hdeg
    have hr : 1 ≤ r := by simpa using hind {x} (Finset.singleton_subset_iff.mpr hx) (by simp)
    let N := insert x (S.filter (G.Adj x))
    let S' := S \ N
    have hsub : S' ⊆ S := Finset.sdiff_subset
    have hxnot : x ∉ S' := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)
    have hprop : S' ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hxnot (he ▸ hx)⟩
    have hind' : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r - 1 + 1 :=
      fun I hI hi => (hind I hI hi).trans (by omega)
    obtain ⟨R, U, hR, hU, hsize, hcount, hwin⟩ :=
      ih S' hprop (r - 1) (indep_budget_after_neighborhood G hx hind')
    have hN : N.card ≤ d := (Finset.card_insert_le _ _).trans (by omega)
    have hsplit : S.card ≤ S'.card + N.card := Finset.card_le_card_sdiff_add_card
    have hprod : (r - 1) * d + d = r * d := by
      calc
        _ = (r - 1) * d + 1 * d := by simp
        _ = _ := by rw [← Nat.add_mul, Nat.sub_add_cancel hr]
    exact ⟨R, U, hR.trans hsub, hU.trans hsub, by omega, hcount, hwin⟩

/-- Power bound under simultaneous lower bounds on ordinary and triangle degree. -/
def DenseDegreeWindowBound (ε B : ℝ) : Prop :=
  ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
    1 ≤ n → RamseyBad n m G →
    (∀ x ∈ S, S.card ≤ 16 * n * ((S.filter (G.Adj x)).card + 1) ∧
      (n : ℝ) ^ ε < (triangleDegree G S x : ℝ)) →
    (S.card : ℝ) ≤ B * (n : ℝ) ^ (2 - ε / 2)

/-- With a triangle-free power bound, it suffices to bound the core with both
ordinary and triangle minimum degree constraints. -/
lemma large_triangle_degree_cap_of_windows {ε A B : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hA : 1 ≤ A)
    (hfree : TriangleFreeWindowBound ε A) (hcore : DenseDegreeWindowBound ε B) :
    LargeTriangleDegreeBound ε (24 * A + 2 * B) := by
  classical
  intro n m G S hn hbad _
  let d := S.card / (4 * n)
  let D : ℝ := (n : ℝ) ^ (ε / 2)
  let Y : ℝ := (n : ℝ) ^ (2 - ε)
  let X : ℝ := (n : ℝ) ^ (2 - ε / 2)
  let L := ⌊2 * A * Y⌋₊
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hD : 1 ≤ D := Real.one_le_rpow hnreal (by linarith)
  have hY : 1 ≤ Y := Real.one_le_rpow hnreal (by linarith)
  have hAY : 2 ≤ 2 * A * Y := by nlinarith only [hA, hY, mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hY)]
  have hApos : 0 ≤ 2 * A * Y := by linarith
  have hL : 2 ≤ L := (Nat.le_floor_iff' (by decide : 2 ≠ 0)).mpr (by simpa using hAY)
  have hDY : D * Y = X := by
    dsimp [D, Y, X]
    rw [← Real.rpow_add hnpos, show ε / 2 + (2 - ε) = 2 - ε / 2 by ring]
  have hDsq : D ^ 2 = (n : ℝ) ^ ε := by
    dsimp [D]
    rw [pow_two, ← Real.rpow_add hnpos, show ε / 2 + ε / 2 = ε by ring]
  obtain ⟨R, U, _, hU, hsize, hRtri, hUwin⟩ :=
    split_at_both_degrees G d ((n : ℝ) ^ ε) S (n - 1) (fun I _ hi => indep_card_le hbad I hi)
  have hbudget : 4 * ((n - 1) * d) ≤ S.card := budget_le_quarter S.card n
  have hall : S.card ≤ 2 * (R.card + U.card) := by omega
  have hall' : (S.card : ℝ) ≤ 2 * ((R.card : ℝ) + U.card) := by exact_mod_cast hall
  have hRcap (T : Finset (Fin m)) (_ : T ⊆ R) (hT : ∀ W ⊆ T, ¬ G.IsNClique 3 W) : T.card ≤ L := by
    by_cases hzero : T.card = 0
    · simp [hzero]
    exact (Nat.le_floor_iff' hzero).mpr (triangle_free_cap_of_degree_window hfree n m G T hn hbad hT)
  have hsparse := card_le_of_sparse_triangles G R hL hD hRcap (by simpa only [hDsq] using hRtri)
  have hsparse' : (R.card : ℝ) ≤ 12 * A * X := by
    calc
      _ ≤ 6 * D * L := hsparse
      _ ≤ 6 * D * (2 * A * Y) := by gcongr; exact Nat.floor_le hApos
      _ = _ := by rw [← hDY]; ring
  have hdense := hcore n m G U hn hbad (fun x hx => ⟨
    lower_degree_window hn (Finset.card_le_card hU) (hUwin x hx).1, (hUwin x hx).2⟩)
  change (S.card : ℝ) ≤ (24 * A + 2 * B) * X
  change (U.card : ℝ) ≤ B * X at hdense
  linarith only [hall', hsparse', hdense]

/-- A triangle packing with a triangle-free remainder. -/
lemma exists_triangle_packing (G : SimpleGraph V) (S : Finset V) :
    ∃ F : Finset (Finset V),
      (∀ T ∈ F, T ⊆ S ∧ G.IsNClique 3 T) ∧
      (↑F : Set (Finset V)).PairwiseDisjoint id ∧
      ∀ T ⊆ S \ F.biUnion id, ¬ G.IsNClique 3 T := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hfree : ∀ T ⊆ S, ¬ G.IsNClique 3 T
    · exact ⟨∅, by simp, by simp, by simpa using hfree⟩
    push Not at hfree
    obtain ⟨B, hBS, hB⟩ := hfree
    have hne : B.Nonempty := card_pos.mp (by rw [hB.card_eq]; decide)
    have hsmall : S \ B ⊂ S := by
      obtain ⟨x, hx⟩ := hne
      exact Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun h =>
        (mem_sdiff.mp (show x ∈ S \ B from h.symm ▸ hBS hx)).2 hx⟩
    obtain ⟨F, hF, hdisj, hrest⟩ := ih (S \ B) hsmall
    have hsep (T : Finset V) (hT : T ∈ F) : Disjoint B T :=
      disjoint_left.mpr fun _ hx hy => (mem_sdiff.mp ((hF T hT).1 hy)).2 hx
    refine ⟨insert B F, ?_, ?_, ?_⟩
    · intro T hT
      rcases mem_insert.mp hT with rfl | hT
      · exact ⟨hBS, hB⟩
      · exact ⟨(hF T hT).1.trans sdiff_subset, (hF T hT).2⟩
    · rw [coe_insert, Set.pairwiseDisjoint_insert]
      exact ⟨hdisj, fun T hT _ => hsep T hT⟩
    intro T hT
    apply hrest T
    intro x hx
    have hx' := mem_sdiff.mp (hT hx)
    rw [biUnion_insert, id_eq, mem_union, not_or] at hx'
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hx'.1, hx'.2.1⟩, hx'.2.2⟩

/-- The two common neighbors of a pair must coincide in a four-cycle-free graph. -/
lemma common_neighbor_unique (G : SimpleGraph V) (hG : ¬ (cycleGraph 4).IsContained G)
    {x y a b : V} (hxy : x ≠ y) (hxa : G.Adj x a) (hya : G.Adj y a)
    (hxb : G.Adj x b) (hyb : G.Adj y b) : a = b := by
  by_contra hab
  let f : Fin 4 → V := ![x, a, y, b]
  have hf : Function.Injective f := by
    have h₁ := hxa.ne
    have h₂ := hya.ne
    have h₃ := hxb.ne
    have h₄ := hyb.ne
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;> grind
  apply hG
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact hxa
    | exact hya
    | exact hxb
    | exact hyb
    | exact hxa.symm
    | exact hya.symm
    | exact hxb.symm
    | exact hyb.symm
    | exact (show ¬ (cycleGraph 4).Adj _ _ by decide) hij |>.elim

private lemma triangle_third_vertex (G : SimpleGraph V)
    {T : Finset V} (hT : G.IsNClique 3 T) {a b : V}
    (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) :
    ∃ c ∈ T, c ≠ a ∧ c ≠ b := by
  have hdel : ((T.erase a).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem (mem_erase.mpr ⟨hab.symm, hb⟩),
      Finset.card_erase_of_mem ha, hT.card_eq]
  obtain ⟨c, hc⟩ := card_pos.mp (show 0 < ((T.erase a).erase b).card by omega)
  simp only [mem_erase] at hc
  exact ⟨c, hc.2.2, hc.2.1, hc.1⟩

/-- An outside vertex has at most one neighbor in any triangle. -/
lemma triangle_neighbor_unique (G : SimpleGraph V) (hG : ¬ (cycleGraph 4).IsContained G)
    {T : Finset V} (hT : G.IsNClique 3 T) {x a b : V} (hx : x ∉ T)
    (ha : a ∈ T) (hb : b ∈ T) (hxa : G.Adj x a) (hxb : G.Adj x b) : a = b := by
  by_contra hab
  obtain ⟨c, hc, hca, hcb⟩ := triangle_third_vertex G hT ha hb hab
  have hxc : x ≠ c := by
    rintro rfl
    exact hx hc
  exact hab (common_neighbor_unique G hG hxc
    hxa (hT.isClique hc ha hca) hxb (hT.isClique hc hb hcb))

/-- Two disjoint triangles have at most one edge between them. -/
lemma triangle_cross_edge_unique (G : SimpleGraph V) (hG : ¬ (cycleGraph 4).IsContained G)
    {T U : Finset V} (hT : G.IsNClique 3 T) (hU : G.IsNClique 3 U)
    (hTU : Disjoint T U) {a c b d : V}
    (ha : a ∈ T) (hc : c ∈ T) (hb : b ∈ U) (hd : d ∈ U)
    (hab : G.Adj a b) (hcd : G.Adj c d) : a = c ∧ b = d := by
  have hdT : d ∉ T := fun h => disjoint_left.mp hTU h hd
  have haU : a ∉ U := disjoint_left.mp hTU ha
  have hcU : c ∉ U := disjoint_left.mp hTU hc
  by_cases hac : a = c
  · subst c
    exact ⟨rfl, triangle_neighbor_unique G hG hU haU hb hd hab hcd⟩
  have hbd : b ≠ d := fun h => hac
    (triangle_neighbor_unique G hG hT hdT ha hc (h ▸ hab.symm) hcd.symm)
  have hcb := hU.isClique hd hb hbd.symm
  have hca := hT.isClique ha hc hac
  have had : a ≠ d := by
    rintro rfl
    exact haU hd
  have heq := common_neighbor_unique G hG had hca hcd.symm hab hcb
  exact (hcU (heq.symm ▸ hb)).elim

/-- In a four-cycle-free graph, an edge belongs to at most one triangle. -/
lemma triangle_eq_of_shared_edge (G : SimpleGraph V)
    (hG : ¬ (cycleGraph 4).IsContained G) {T U : Finset V}
    (hT : G.IsNClique 3 T) (hU : G.IsNClique 3 U) {x y : V} (hxy : x ≠ y)
    (hxT : x ∈ T) (hyT : y ∈ T) (hxU : x ∈ U) (hyU : y ∈ U) :
    T = U := by
  obtain ⟨a, ha, hax, hay⟩ := triangle_third_vertex G hT hxT hyT hxy
  obtain ⟨b, hb, hbx, hby⟩ := triangle_third_vertex G hU hxU hyU hxy
  have hab := common_neighbor_unique G hG hxy
    (hT.isClique hxT ha hax.symm) (hT.isClique hyT ha hay.symm)
    (hU.isClique hxU hb hbx.symm) (hU.isClique hyU hb hby.symm)
  subst b
  let C : Finset V := {x, y, a}
  have hC : C.card = 3 := by simp [C, hxy, hax.symm, hay.symm]
  have hCT : C ⊆ T := insert_subset hxT (insert_subset hyT (singleton_subset_iff.mpr ha))
  have hCU : C ⊆ U := insert_subset hxU (insert_subset hyU (singleton_subset_iff.mpr hb))
  have heqT := eq_of_subset_of_card_le hCT (hT.card_eq.trans hC.symm).le
  have heqU := eq_of_subset_of_card_le hCU (hU.card_eq.trans hC.symm).le
  exact heqT.symm.trans heqU

/-- The triangles at a vertex use disjoint pairs of its neighbors. Removing one
vertex from each pair leaves an independent set inside the neighborhood. -/
lemma neighborhood_triangle_bounds {n m : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : RamseyBad n m G) (S : Finset (Fin m)) {x : Fin m} (hxS : x ∈ S) :
    2 * triangleDegree G S x ≤ (S.filter (G.Adj x)).card ∧
      (S.filter (G.Adj x)).card ≤ (n - 1) + triangleDegree G S x := by
  classical
  let N := S.filter (G.Adj x)
  let F := (S.powersetCard 3).filter fun T => G.IsNClique 3 T ∧ x ∈ T
  let edges := F.image fun T => T.erase x
  have hF (T : Finset (Fin m)) (hT : T ∈ F) :
      T ⊆ S ∧ G.IsNClique 3 T ∧ x ∈ T := by
    obtain ⟨hsub, hclique, hx⟩ := mem_filter.mp hT
    exact ⟨(mem_powersetCard.mp hsub).1, hclique, hx⟩
  have hN (T : Finset (Fin m)) (hT : T ∈ F) : T.erase x ⊆ N := by
    intro y hy
    obtain ⟨hyx, hyT⟩ := mem_erase.mp hy
    obtain ⟨hTS, htri, hxT⟩ := hF T hT
    exact mem_filter.mpr ⟨hTS hyT, htri.isClique hxT hyT hyx.symm⟩
  have hpair_card (T : Finset (Fin m)) (hT : T ∈ F) : (T.erase x).card = 2 := by
    rw [card_erase_of_mem (hF T hT).2.2, (hF T hT).2.1.card_eq]
  have hdisj : (↑F : Set (Finset (Fin m))).PairwiseDisjoint (fun T => T.erase x) := by
    intro T hT U hU hne
    apply Finset.disjoint_left.mpr
    intro y hyT hyU
    obtain ⟨hyx, hyT⟩ := mem_erase.mp hyT
    have hT' := hF T hT
    have hU' := hF U hU
    exact hne (triangle_eq_of_shared_edge G hbad.1 hT'.2.1 hU'.2.1 hyx.symm
      hT'.2.2 hyT hU'.2.2 (mem_of_mem_erase hyU))
  have hbi : (F.biUnion fun T => T.erase x).card = 2 * F.card := by
    rw [card_biUnion hdisj]
    calc
      _ = ∑ _ ∈ F, 2 := sum_congr rfl hpair_card
      _ = _ := by simp [Nat.mul_comm]
  have hsub : F.biUnion (fun T => T.erase x) ⊆ N := by
    intro y hy
    obtain ⟨T, hT, hyT⟩ := mem_biUnion.mp hy
    exact hN T hT hyT
  constructor
  · change 2 * F.card ≤ N.card
    exact hbi ▸ card_le_card hsub
  have hne (E : Finset (Fin m)) (hE : E ∈ edges) : E.Nonempty := by
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hE
    exact card_pos.mp (by rw [hpair_card T hT]; decide)
  obtain ⟨I, hIN, havoid, hsize⟩ := avoid_family N edges hne
  have hI : G.IsIndepSet (I : Set (Fin m)) := by
    intro y hy z hz hyz hyz_adj
    have hyI : y ∈ I := hy
    have hzI : z ∈ I := hz
    obtain ⟨hyS, hxy⟩ := mem_filter.mp (hIN hyI)
    obtain ⟨hzS, hxz⟩ := mem_filter.mp (hIN hzI)
    let T : Finset (Fin m) := {x, y, z}
    have hT : G.IsNClique 3 T := is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz_adj⟩
    have hTF : T ∈ F := mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨insert_subset hxS (insert_subset hyS (singleton_subset_iff.mpr hzS)), hT.card_eq⟩,
      hT, mem_insert_self _ _⟩
    have hpair : T.erase x ⊆ I := by
      intro w hw
      have hw' := mem_erase.mp hw
      rcases mem_insert.mp hw'.2 with h | h
      · exact (hw'.1 h).elim
      rcases mem_insert.mp h with rfl | h
      · exact hyI
      simpa only [mem_singleton.mp h] using hzI
    exact havoid _ (mem_image_of_mem _ hTF) hpair
  have hcount : (edges.filter (· ⊆ N)).card ≤ F.card :=
    (card_filter_le _ _).trans card_image_le
  exact hsize.trans (Nat.add_le_add (indep_card_le hbad I hI) hcount)

/-- The dense window restricted to sets with a large disjoint triangle packing. -/
def PackedDenseDegreeWindowBound (ε B : ℝ) : Prop :=
  ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
    1 ≤ n → RamseyBad n m G →
    (∀ x ∈ S, S.card ≤ 16 * n * ((S.filter (G.Adj x)).card + 1) ∧
      (n : ℝ) ^ ε < (triangleDegree G S x : ℝ)) →
    (∃ F : Finset (Finset (Fin m)), S.card ≤ 2 * (F.biUnion id).card ∧
      (∀ T ∈ F, T ⊆ S ∧ G.IsNClique 3 T) ∧
      (↑F : Set (Finset (Fin m))).PairwiseDisjoint id ∧
      (∀ T ⊆ S \ F.biUnion id, ¬ G.IsNClique 3 T) ∧
      ∀ T ∈ F, ∀ U ∈ F, T ≠ U → ∀ a ∈ T, ∀ c ∈ T, ∀ b ∈ U, ∀ d ∈ U,
        G.Adj a b → G.Adj c d → a = c ∧ b = d) →
    (S.card : ℝ) ≤ B * (n : ℝ) ^ (2 - ε / 2)

/-- A triangle-free size cap either bounds the whole set or forces its maximal
triangle packing to cover at least half of the vertices. -/
lemma dense_degree_window_of_packing {ε A B : ℝ}
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfree : TriangleFreeWindowBound ε A)
    (hpacked : PackedDenseDegreeWindowBound ε B) :
    DenseDegreeWindowBound ε (4 * A + B) := by
  classical
  intro n m G S hn hbad hdegrees
  obtain ⟨F, hF, hdisj, hrest⟩ := exists_triangle_packing G S
  let P := F.biUnion id
  let R := S \ P
  have hP : P ⊆ S := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := mem_biUnion.mp hx
    exact (hF T hT).1 hxT
  have hsize : P.card + R.card = S.card := by
    simpa only [R, add_comm] using Finset.card_sdiff_add_card_eq_card hP
  have hbase : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (2 - ε) ≤ (n : ℝ) ^ (2 - ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  by_cases hcover : S.card ≤ 2 * P.card
  · have hbound := hpacked n m G S hn hbad hdegrees
        ⟨F, hcover, hF, hdisj, hrest, fun T hT U hU hne a ha c hc b hb d hd =>
          triangle_cross_edge_unique G hbad.1 (hF T hT).2 (hF U hU).2
            (hdisj hT hU hne) ha hc hb hd⟩
    refine hbound.trans ?_
    gcongr
    linarith
  · have hS : (S.card : ℝ) ≤ 2 * (R.card : ℝ) := by
      exact_mod_cast (show S.card ≤ 2 * R.card by omega)
    have hR := triangle_free_cap_of_degree_window hfree n m G R hn hbad hrest
    calc
      _ ≤ 2 * (R.card : ℝ) := hS
      _ ≤ 2 * ((2 * A) * (n : ℝ) ^ (2 - ε)) := by gcongr
      _ = (4 * A) * (n : ℝ) ^ (2 - ε) := by ring
      _ ≤ (4 * A + B) * (n : ℝ) ^ (2 - ε / 2) := by
        gcongr
        linarith


private abbrev Triangle (G : SimpleGraph (Fin m)) := ↥(G.cliqueFinset 3)

private abbrev TriangleChoice (G : SimpleGraph (Fin m)) :=
  ∀ T : Triangle G, ↥(T : Finset (Fin m))

/-- Keep the two edges incident to a chosen vertex in each triangle. -/
private def triangleDeletion {m : ℕ} (G : SimpleGraph (Fin m)) (f : TriangleChoice G) :
    SimpleGraph (Fin m) where
  Adj x y := G.Adj x y ∧ ∀ T : Triangle G, x ∈ T.val → y ∈ T.val →
    (f T).val = x ∨ (f T).val = y
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

private lemma triangleDeletion_le {G : SimpleGraph (Fin m)} (f : TriangleChoice G) :
    triangleDeletion G f ≤ G := fun _ _ h => h.1

private lemma triangleDeletion_free {G : SimpleGraph (Fin m)} (f : TriangleChoice G) :
    (triangleDeletion G f).CliqueFree 3 := by
  intro T hT
  have hTG : G.IsNClique 3 T :=
    ⟨hT.isClique.mono (triangleDeletion_le f), hT.card_eq⟩
  let Q : Triangle G := ⟨T, mem_cliqueFinset_iff.mpr hTG⟩
  have hcard : (T.erase (f Q).val).card = 2 := by
    rw [card_erase_of_mem (f Q).property, hT.card_eq]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < (T.erase (f Q).val).card by omega)
  obtain ⟨ha', ha⟩ := mem_erase.mp ha
  obtain ⟨hb', hb⟩ := mem_erase.mp hb
  rcases (hT.isClique ha hb hab).2 Q ha hb with h | h
  · exact ha' h.symm
  · exact hb' h.symm

private lemma choice_outside_of_independent {G : SimpleGraph (Fin m)}
    (hG : ¬ (cycleGraph 4).IsContained G) {f : TriangleChoice G} {W : Finset (Fin m)}
    (hW : (triangleDeletion G f).IsIndepSet (W : Set (Fin m)))
    (T : Triangle G) (hlarge : 2 ≤ (T.val ∩ W).card) :
    (f T).val ∉ W := by
  intro hmem
  have hcent : (f T).val ∈ T.val ∩ W := mem_inter.mpr ⟨(f T).property, hmem⟩
  have hne : ((T.val ∩ W).erase (f T).val).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hcent]
    omega
  obtain ⟨y, hy⟩ := hne
  obtain ⟨hyne, hy⟩ := mem_erase.mp hy
  obtain ⟨hyT, hyW⟩ := mem_inter.mp hy
  have hxy : (f T).val ≠ y := hyne.symm
  have htri := mem_cliqueFinset_iff.mp T.property
  apply hW hmem hyW hxy
  refine ⟨htri.isClique (f T).property hyT hxy, ?_⟩
  intro U hxU hyU
  have hTU : T = U := Subtype.ext (triangle_eq_of_shared_edge G hG htri
    (mem_cliqueFinset_iff.mp U.property) hxy (f T).property hyT hxU hyU)
  subst U
  exact Or.inl rfl

private lemma intersect_card_le_two {G : SimpleGraph (Fin m)} {W : Finset (Fin m)}
    {T : Triangle G} {a : ↥(T : Finset (Fin m))} (ha : a.val ∉ W) :
    (T.val ∩ W).card ≤ 2 := by
  have hs : T.val ∩ W ⊆ T.val.erase a.val := by
    intro x hx
    obtain ⟨hxT, hxW⟩ := mem_inter.mp hx
    exact mem_erase.mpr ⟨fun he => ha (he ▸ hxW), hxT⟩
  have h := card_le_card hs
  rwa [card_erase_of_mem a.property, (mem_cliqueFinset_iff.mp T.property).card_eq] at h

private noncomputable def constrainedTriangles (G : SimpleGraph (Fin m)) (W : Finset (Fin m)) :
    Finset (Triangle G) :=
  univ.filter fun T => 2 ≤ (T.val ∩ W).card

/-- A large independent set after deletion forces choices in many triangle coordinates. -/
private lemma constrainedTriangles_card {n m d : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : RamseyBad n m G) {f : TriangleChoice G} {W : Finset (Fin m)}
    (hW : (triangleDeletion G f).IsIndepSet (W : Set (Fin m)))
    (hlarge : 8 * n * d ≤ W.card) :
    W.card * d ≤ (constrainedTriangles G W).card := by
  classical
  obtain ⟨U, hUW, hcard, hdeg⟩ := minimum_degree_core G (4 * d) (n - 1) W
    (fun I _ => indep_card_le hbad I)
  have hbudget : 2 * ((n - 1) * (4 * d)) ≤ 8 * n * d := by
    calc
      _ = 8 * (n - 1) * d := by ring
      _ ≤ _ := by gcongr; omega
  have hhalf : W.card ≤ 2 * U.card := by omega
  let R := constrainedTriangles G W
  let row (x : Fin m) := (U.filter (G.Adj x)).image (fun y => (x, y))
  let arcs := U.biUnion row
  have hrows : (↑U : Set (Fin m)).PairwiseDisjoint row := by
    intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro p hx hy
    obtain ⟨a, _, ha⟩ := mem_image.mp hx
    obtain ⟨b, _, hb⟩ := mem_image.mp hy
    exact hxy (congrArg Prod.fst (ha.trans hb.symm))
  have harcs_lower : U.card * (4 * d) ≤ arcs.card := by
    rw [show arcs.card = ∑ x ∈ U, (row x).card from card_biUnion hrows]
    calc
      U.card * (4 * d) = ∑ _ ∈ U, 4 * d := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro x hx
        rw [show (row x).card = (U.filter (G.Adj x)).card from
          card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
        exact hdeg x hx

  let pairs (T : Triangle G) := (T.val ∩ W).offDiag
  have harcs_sub : arcs ⊆ R.biUnion pairs := by
    intro p hp
    obtain ⟨x, hx, hp⟩ := mem_biUnion.mp hp
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
    obtain ⟨hy, hxy⟩ := mem_filter.mp hy
    have hxW := hUW hx
    have hyW := hUW hy
    have hnot := hW hxW hyW hxy.ne
    have hfail : ¬ ∀ T : Triangle G, x ∈ T.val → y ∈ T.val →
        (f T).val = x ∨ (f T).val = y := fun h => hnot ⟨hxy, h⟩
    push Not at hfail
    obtain ⟨T, hxT, hyT, _, _⟩ := hfail
    have hxl := mem_inter.mpr ⟨hxT, hxW⟩
    have hyl := mem_inter.mpr ⟨hyT, hyW⟩
    have hR : T ∈ R := mem_filter.mpr ⟨mem_univ _, one_lt_card.mpr ⟨x, hxl, y, hyl, hxy.ne⟩⟩
    exact mem_biUnion.mpr ⟨T, hR, mem_offDiag.mpr ⟨hxl, hyl, hxy.ne⟩⟩
  have hpair_card (T : Triangle G) (hT : T ∈ R) : (pairs T).card ≤ 2 := by
    have hT' := (mem_filter.mp hT).2
    have hout := choice_outside_of_independent hbad.1 hW T hT'
    have hcap := intersect_card_le_two hout
    have heq : (T.val ∩ W).card = 2 := by omega
    simp [pairs, offDiag_card, heq]
  have harcs_upper : arcs.card ≤ R.card * 2 := by
    calc
      _ ≤ (R.biUnion pairs).card := card_le_card harcs_sub
      _ ≤ ∑ T ∈ R, (pairs T).card := card_biUnion_le
      _ ≤ ∑ _ ∈ R, 2 := sum_le_sum hpair_card
      _ = _ := by simp
  have hmul := Nat.mul_le_mul_right d hhalf
  have haux : 2 * (W.card * d) ≤ R.card * 2 := by
    calc
      _ ≤ 2 * ((2 * U.card) * d) := Nat.mul_le_mul_left 2 hmul
      _ = U.card * (4 * d) := by ring
      _ ≤ _ := harcs_lower.trans harcs_upper
  change W.card * d ≤ R.card
  omega

private lemma outside_choice_unique {G : SimpleGraph (Fin m)} {W : Finset (Fin m)}
    {T : Triangle G} {a b : ↥(T : Finset (Fin m))}
    (hlarge : 2 ≤ (T.val ∩ W).card) (ha : a.val ∉ W) (hb : b.val ∉ W) : a = b := by
  apply Subtype.ext
  by_contra hne
  have hb' : b.val ∈ T.val.erase a.val := mem_erase.mpr ⟨fun h => hne h.symm, b.property⟩
  have hsub : T.val ∩ W ⊆ (T.val.erase a.val).erase b.val := by
    intro x hx
    obtain ⟨hxT, hxW⟩ := mem_inter.mp hx
    exact mem_erase.mpr ⟨fun h => hb (h ▸ hxW),
      mem_erase.mpr ⟨fun h => ha (h ▸ hxW), hxT⟩⟩
  have hc := card_le_card hsub
  rw [card_erase_of_mem hb', card_erase_of_mem a.property,
    (mem_cliqueFinset_iff.mp T.property).card_eq] at hc
  omega

private lemma triangle_choice_space_card {G : SimpleGraph (Fin m)} :
    Fintype.card (TriangleChoice G) = 3 ^ Fintype.card (Triangle G) := by
  classical
  rw [Fintype.card_pi]
  have h (T : Triangle G) : Fintype.card ↥(T : Finset (Fin m)) = 3 := by
    simpa using (mem_cliqueFinset_iff.mp T.property).card_eq
  simp [h]

private noncomputable def badTriangleChoices (G : SimpleGraph (Fin m)) (W : Finset (Fin m)) :
    Finset (TriangleChoice G) :=
  univ.filter (fun f => (triangleDeletion G f).IsIndepSet (W : Set (Fin m)))

private lemma badTriangleChoices_card {n m d : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : RamseyBad n m G) (W : Finset (Fin m)) (hlarge : 8 * n * d ≤ W.card) :
    (badTriangleChoices G W).card * 3 ^ (W.card * d) ≤ 3 ^ Fintype.card (Triangle G) := by
  classical
  by_cases hnon : (badTriangleChoices G W).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hnon, card_empty, zero_mul]
    exact Nat.zero_le _
  obtain ⟨g, hg⟩ := hnon
  have hgW := (mem_filter.mp hg).2
  let R := constrainedTriangles G W
  let allowed (T : Triangle G) : Finset ↥(T : Finset (Fin m)) :=
    if T ∈ R then {g T} else univ
  have hsub : badTriangleChoices G W ⊆ Fintype.piFinset allowed := by
    intro f hf
    have hfW := (mem_filter.mp hf).2
    apply Fintype.mem_piFinset.mpr
    intro T
    by_cases hT : T ∈ R
    · have hT' := (mem_filter.mp hT).2
      have eq := outside_choice_unique hT'
        (choice_outside_of_independent hbad.1 hfW T hT')
        (choice_outside_of_independent hbad.1 hgW T hT')
      simp [allowed, hT, eq]
    · simp [allowed, hT]
  have hallowed : (Fintype.piFinset allowed).card = 3 ^ (Fintype.card (Triangle G) - R.card) := by
    have h (T : Triangle G) : Fintype.card ↥(T : Finset (Fin m)) = 3 := by
      simpa using (mem_cliqueFinset_iff.mp T.property).card_eq
    rw [Fintype.card_piFinset]
    simp only [allowed, apply_ite card, card_singleton, card_univ, h]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    simpa [Finset.sdiff_eq_filter] using
      (Finset.card_sdiff_of_subset (Finset.subset_univ R))
  have hR : W.card * d ≤ R.card := constrainedTriangles_card hbad hgW hlarge
  have hR' : R.card ≤ Fintype.card (Triangle G) := card_le_univ _
  calc
    _ ≤ 3 ^ (Fintype.card (Triangle G) - R.card) * 3 ^ R.card := by
      exact Nat.mul_le_mul ((card_le_card hsub).trans_eq hallowed)
        (Nat.pow_le_pow_right (by decide) hR)
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hR']

/-- Deleting one edge from every triangle can preserve the independence bound
up to a logarithmic factor in the number of vertices. -/
lemma exists_triangle_free_spanning_subgraph {n m : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : RamseyBad n m G) {d : ℕ} (hd : 0 < d) (hm : m < 3 ^ d) (hn : 0 < n) :
    ∃ H : SimpleGraph (Fin m), H ≤ G ∧ H.CliqueFree 3 ∧ RamseyBad (8 * n * d) m H := by
  classical
  let k := 8 * n * d
  let P := (univ : Finset (Fin m)).powersetCard k
  have hk : 0 < k := by dsimp [k]; positivity
  have hlt : P.card < 3 ^ (k * d) := by
    dsimp only [P]
    rw [card_powersetCard, card_univ, Fintype.card_fin, mul_comm k d, pow_mul]
    exact (Nat.choose_le_pow m k).trans_lt (Nat.pow_lt_pow_left hm (by omega))
  suffices hgood : ∃ f : TriangleChoice G, ∀ W ∈ P,
      ¬ (triangleDeletion G f).IsIndepSet (W : Set (Fin m)) by
    obtain ⟨f, hf⟩ := hgood
    refine ⟨triangleDeletion G f, triangleDeletion_le f, triangleDeletion_free f,
      fun h => hbad.1 (h.mono_right (triangleDeletion_le f)), ?_⟩
    intro hcontain
    have hnot := ((triangleDeletion G f)ᶜ.not_cliqueFree_iff_top_isContained k).mpr hcontain
    apply hnot
    intro W hW
    apply hf W (mem_powersetCard.mpr ⟨subset_univ _, hW.card_eq⟩)
    simpa only [isClique_compl] using hW.isClique
  by_contra! hall
  have hcover : (univ : Finset (TriangleChoice G)) ⊆
      P.biUnion (badTriangleChoices G) := by
    intro f _
    obtain ⟨W, hW, hI⟩ := hall f
    exact mem_biUnion.mpr ⟨W, hW, mem_filter.mpr ⟨mem_univ _, hI⟩⟩
  let M := 3 ^ Fintype.card (Triangle G)
  have htotal : M ≤ ∑ W ∈ P, (badTriangleChoices G W).card := by
    dsimp only [M]
    rw [← triangle_choice_space_card (G := G), ← card_univ]
    exact (card_le_card hcover).trans card_biUnion_le
  have hsum : (∑ W ∈ P, (badTriangleChoices G W).card) * 3 ^ (k * d) ≤ P.card * M := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ _ ∈ P, M := by
        apply sum_le_sum
        intro W hW
        have hcard := (mem_powersetCard.mp hW).2
        have h := badTriangleChoices_card hbad W (by rw [hcard])
        rw [hcard] at h
        exact h
      _ = _ := by simp
  have hpos : 0 < M := by dsimp [M]; positivity
  have hc := (Nat.mul_le_mul_right (3 ^ (k * d)) htotal).trans hsum
  rw [Nat.mul_comm M] at hc
  exact (Nat.not_lt_of_ge (Nat.le_of_mul_le_mul_right hc hpos)) hlt


private lemma bad_card_le_quadratic {n m : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : RamseyBad n m G) (hn : 1 ≤ n) : m ≤ 2 * n ^ 2 := by
  classical
  let S : Finset (Fin m) := univ
  let d := 2 * (n - 1) + 1
  obtain ⟨U, hUS, hcard, hmin⟩ := minimum_degree_core G d (n - 1) S
    (fun I _ => indep_card_le hbad I)
  have hU : U = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    obtain ⟨htri, hdeg⟩ := neighborhood_triangle_bounds hbad U hx
    have hlow := hmin x hx
    dsimp only [d] at hlow
    omega
  rw [hU, card_empty, zero_add] at hcard
  calc
    m = S.card := by simp [S]
    _ ≤ (n - 1) * d := hcard
    _ ≤ n * (2 * n) := by dsimp only [d]; gcongr <;> omega
    _ = _ := by ring

/-- A power bound for the triangle-free degree window alone suffices for the
four-cycle versus clique Ramsey problem. -/
theorem ramsey_of_triangle_free_window {ε A : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hA : 1 ≤ A)
    (hfree : TriangleFreeWindowBound ε A) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (graphRamsey (cycleGraph 4) (completeGraph (Fin n)) : ℝ) ≤
        C * (n : ℝ) ^ (2 - ε / 2) := by
  let p := ε / 4
  let K : ℝ := 1 + (Real.log 2 + 2 / p) / Real.log 3
  let C : ℝ := 2 * A * (8 * K) ^ (2 - ε)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  have hcard (n m : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin m))
      (hbad : RamseyBad n m G) : (m : ℝ) ≤ C * (n : ℝ) ^ (2 - ε / 2) := by
    by_cases hm : m = 0
    · subst m; simpa using mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) (2 - ε / 2))
    let d := Nat.log 3 m + 1
    have hd : 0 < d := by dsimp only [d]; omega
    have hnm : m < 3 ^ d := Nat.lt_pow_succ_log_self (by decide) m
    obtain ⟨H, _, hHfree, hHbad⟩ :=
      exists_triangle_free_spanning_subgraph hbad hd hnm hn
    let k := 8 * n * d
    have hk : 1 ≤ k := by
      change 0 < 8 * n * d
      positivity
    have hH := triangle_free_cap_of_degree_window hfree k m H Finset.univ hk hHbad
      (fun T _ => hHfree T)
    rw [card_univ, Fintype.card_fin] at hH
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : 0 < (n : ℝ) := by linarith
    have hpow : 1 ≤ (n : ℝ) ^ p := Real.one_le_rpow hnreal hp.le
    have hlogm : (Nat.log 3 m : ℝ) * Real.log 3 ≤ Real.log (m : ℝ) := by
      have hpowlog : (3 : ℝ) ^ Nat.log 3 m ≤ (m : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 3 hm
      simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpowlog
    have hquadratic : (m : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
      exact_mod_cast bad_card_le_quadratic hbad hn
    have hlogn : Real.log (m : ℝ) ≤ Real.log 2 + 2 * Real.log (n : ℝ) := by
      calc
        _ ≤ Real.log (2 * (n : ℝ) ^ 2) := Real.log_le_log hmreal hquadratic
        _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
    have hlogbound : Real.log (n : ℝ) ≤ (n : ℝ) ^ p / p :=
      Real.log_le_rpow_div (Nat.cast_nonneg n) hp
    have hd_upper : (d : ℝ) ≤ K * (n : ℝ) ^ p := by
      rw [← le_div_iff₀ hlog3] at hlogm
      have hd' : (d : ℝ) = (Nat.log 3 m : ℝ) + 1 := by simp [d]
      rw [hd']
      calc
        _ ≤ Real.log (m : ℝ) / Real.log 3 + 1 := add_le_add_left hlogm 1
        _ ≤ (Real.log 2 + 2 * Real.log (n : ℝ)) / Real.log 3 + 1 := by gcongr
        _ ≤ ((Real.log 2 + 2 / p) * (n : ℝ) ^ p) / Real.log 3 + (n : ℝ) ^ p := by
          gcongr
          nlinarith only [hlogbound, mul_nonneg hlog2 (sub_nonneg.mpr hpow),
            show 2 * ((n : ℝ) ^ p / p) = (2 / p) * (n : ℝ) ^ p by ring]
        _ = _ := by dsimp only [K]; ring
    have hk_upper : (k : ℝ) ≤ (8 * K) * (n : ℝ) ^ (1 + p) := by
      have hk' : (k : ℝ) = 8 * (n : ℝ) * (d : ℝ) := by simp [k]
      rw [hk', Real.rpow_add hnpos, Real.rpow_one]
      calc
        _ ≤ 8 * (n : ℝ) * (K * (n : ℝ) ^ p) := by gcongr
        _ = _ := by ring
    have hexp : (1 + p) * (2 - ε) ≤ 2 - ε / 2 := by
      dsimp only [p]
      nlinarith only [sq_nonneg ε]
    have hpow_k : (k : ℝ) ^ (2 - ε) ≤ (8 * K) ^ (2 - ε) * (n : ℝ) ^ (2 - ε / 2) := by
      calc
        _ ≤ ((8 * K) * (n : ℝ) ^ (1 + p)) ^ (2 - ε) :=
          Real.rpow_le_rpow (Nat.cast_nonneg k) hk_upper (by linarith)
        _ = (8 * K) ^ (2 - ε) * (n : ℝ) ^ ((1 + p) * (2 - ε)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hnpos.le]
        _ ≤ _ := by gcongr
    calc
      _ ≤ (2 * A) * (k : ℝ) ^ (2 - ε) := hH
      _ ≤ (2 * A) * ((8 * K) ^ (2 - ε) * (n : ℝ) ^ (2 - ε / 2)) :=
        mul_le_mul_of_nonneg_left hpow_k (by linarith)
      _ = _ := by dsimp only [C]; ring
  refine ⟨C + 1, fun n hn => ?_⟩
  let X := (n : ℝ) ^ (2 - ε / 2)
  have hX : 1 ≤ X := Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  let N := ⌊C * X⌋₊ + 1
  have hN : C * X < (N : ℝ) := by simpa [N] using Nat.lt_floor_add_one (C * X)
  have hit (G : SimpleGraph (Fin N)) :
      (cycleGraph 4).IsContained G ∨ (completeGraph (Fin n)).IsContained Gᶜ := by
    by_contra h
    exact hN.not_ge (hcard n N hn G (not_or.mp h))
  have hRamsey : graphRamsey (cycleGraph 4) (completeGraph (Fin n)) ≤ N := Nat.sInf_le hit
  calc
    _ ≤ (N : ℝ) := by exact_mod_cast hRamsey
    _ ≤ C * X + 1 := by
      simpa [N] using add_le_add_right (Nat.floor_le (by positivity : 0 ≤ C * X)) (1 : ℝ)
    _ ≤ (C + 1) * X := by linarith only [hX]

private lemma bad_card_lt_graphRamsey {n m : ℕ} {G : SimpleGraph (Fin m)}
    (hn : 1 ≤ n) (hbad : RamseyBad n m G) :
    m < graphRamsey (cycleGraph 4) (completeGraph (Fin n)) := by
  let R := graphRamsey (cycleGraph 4) (completeGraph (Fin n))
  let sizes : Set ℕ := {k | ∀ H : SimpleGraph (Fin k),
    (cycleGraph 4).IsContained H ∨ (completeGraph (Fin n)).IsContained Hᶜ}
  have hexists : sizes.Nonempty := by
    refine ⟨2 * n ^ 2 + 1, ?_⟩
    intro H
    by_contra h
    have hcap := bad_card_le_quadratic (G := H) (not_or.mp h) hn
    omega
  have hR : R ∈ sizes := Nat.sInf_mem hexists
  by_contra! hle
  let f : Fin R ↪ Fin m := Fin.castLEEmb hle
  let H := G.comap f
  have hH : H.IsContained G := isContained_iff_exists_le_comap.mpr ⟨f, le_rfl⟩
  have hcomp : Hᶜ.IsContained Gᶜ := by
    apply isContained_iff_exists_le_comap.mpr
    refine ⟨f, ?_⟩
    intro x y h
    exact ⟨fun hxy => h.1 (f.injective hxy), h.2⟩
  rcases hR H with hc | hi
  · exact hbad.1 (hc.trans hH)
  · exact hbad.2 (hi.trans hcomp)

/-- A power bound for the Ramsey number also bounds the triangle-free window. -/
lemma triangle_free_window_of_ramsey {c C : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n →
      (graphRamsey (cycleGraph 4) (completeGraph (Fin n)) : ℝ) ≤ C * (n : ℝ) ^ (2 - c)) :
    TriangleFreeWindowBound (min c 1) (max C 1) := by
  intro n m G S hn hbad _ _
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcard : (S.card : ℝ) ≤ (m : ℝ) := by
    have hS : S.card ≤ m := by simpa using S.card_le_univ
    exact_mod_cast hS
  have hm : (m : ℝ) ≤ (graphRamsey (cycleGraph 4) (completeGraph (Fin n)) : ℝ) := by
    exact_mod_cast (bad_card_lt_graphRamsey hn hbad).le
  calc
    _ ≤ (m : ℝ) := hcard
    _ ≤ _ := hm
    _ ≤ C * (n : ℝ) ^ (2 - c) := h n hn
    _ ≤ max C 1 * (n : ℝ) ^ (2 - c) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ max C 1 * (n : ℝ) ^ (2 - min c 1) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (le_max_right _ _))
      exact Real.rpow_le_rpow_of_exponent_le hnreal (sub_le_sub_left (min_le_left _ _) _)

end OMA.Erdos159Relay

open OMA.Erdos159Relay in
theorem OMA.solution : type_of% @Erdos159.erdos_159 := by
  suffices h : ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ A ∧ TriangleFreeWindowBound ε A by
    obtain ⟨ε, A, hε, hεone, hA, hfree⟩ := h
    obtain ⟨C, hC⟩ := ramsey_of_triangle_free_window hε hεone hA hfree
    exact ⟨ε / 2, by positivity, C, hC⟩
  sorry
