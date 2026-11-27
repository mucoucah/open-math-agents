import FormalConjectures.ErdosProblems.«78»

/-! # Strongly explicit Ramsey graphs from a binary two-source disperser -/

-- Problem: Erdős Problem 78 — li strongly explicit
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/78.lean:160 (declaration Erdos78.erdos_78.variants.li_strongly_explicit)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos78.LiExplicit

open Filter Real ComplexityTheory

/-- A one-bit disperser takes both values on products of sufficiently large sets of words. -/
def DispersesRectangles (color : ℕ → ℕ → Bool) (width threshold : ℕ) : Prop :=
  ∀ A B : Finset (Fin (2 ^ width)), threshold ≤ A.card → threshold ≤ B.card →
    ∀ bit : Bool, ∃ a ∈ A, ∃ b ∈ B, color a b = bit

/-- The binary extractor bound on independent uniform sources supported on two finite sets. -/
def ExtractsOnFlatSources (color : ℕ → ℕ → Bool) (width : ℕ) (entropy error : ℝ) : Prop :=
  ∀ A B : Finset (Fin (2 ^ width)),
    A.Nonempty → B.Nonempty → entropy ≤ logb 2 A.card → entropy ≤ logb 2 B.card →
    let rect := A.product B
    let ones := rect.filter (fun p => color p.1 p.2 = true)
    |(ones.card : ℝ) / (rect.card : ℝ) - 1 / 2| ≤ error

private lemma dispersesRectangles_of_entropyBias (color : ℕ → ℕ → Bool) {d D : ℕ}
    {K ε : ℝ} (hd : 1 ≤ d) (hK : K ≤ D) (hε : ε < 1 / 2)
    (h : ExtractsOnFlatSources color d (K * logb 2 d) ε) :
    DispersesRectangles color d (d ^ D) := by
  have hpow : 0 < d ^ D := pow_pos (by omega) _
  have hlog : 0 ≤ logb 2 (d : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hd)
  have entropy_le {a : ℕ} (ha : d ^ D ≤ a) : K * logb 2 d ≤ logb 2 a := by
    calc
      _ ≤ (D : ℝ) * logb 2 d := mul_le_mul_of_nonneg_right hK hlog
      _ = logb 2 ((d : ℝ) ^ D) := (Real.logb_pow 2 d D).symm
      _ ≤ logb 2 a := Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast ha)
  intro A B hA hB bit
  let rect := A.product B
  let ones := rect.filter (fun p => color p.1 p.2 = true)
  have hposA := hpow.trans_le hA
  have hposB := hpow.trans_le hB
  have hrect : 0 < (rect.card : ℝ) := by
    simpa [rect, Finset.card_product, Nat.cast_mul] using
      mul_pos (Nat.cast_pos.mpr hposA : (0 : ℝ) < A.card)
        (Nat.cast_pos.mpr hposB : (0 : ℝ) < B.card)
  have hbias := h A B (Finset.card_pos.mp hposA) (Finset.card_pos.mp hposB)
    (entropy_le hA) (entropy_le hB)
  change |(ones.card : ℝ) / (rect.card : ℝ) - 1 / 2| ≤ ε at hbias
  by_contra! hmissing
  cases bit
  · have hall : ones = rect := Finset.filter_eq_self.mpr fun p hp => by
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      simpa using hmissing p.1 ha p.2 hb
    rw [hall, div_self hrect.ne'] at hbias
    linarith [(abs_le.mp hbias).2]
  · have hnone : ones = ∅ := Finset.filter_eq_empty_iff.mpr fun {p} hp => by
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      exact hmissing p.1 ha p.2 hb
    rw [hnone, Finset.card_empty, Nat.cast_zero, zero_div] at hbias
    linarith [(abs_le.mp hbias).1]

/-- Use the width of the vertex count and present the two vertices in increasing order. -/
def extractorAdj (color : ℕ → ℕ → ℕ → Bool) (input : ℕ × ℕ × ℕ) : Bool :=
  color (Nat.size input.1) (min input.2.1 input.2.2) (max input.2.1 input.2.2)

private lemma orderedRectangle {α : Type*} [LinearOrder α] (s : Finset α) (m : ℕ)
    (hs : s.card = 2 * m) :
    ∃ A B : Finset α, A ⊆ s ∧ B ⊆ s ∧ A.card = m ∧ B.card = m ∧
      ∀ a ∈ A, ∀ b ∈ B, a < b := by
  let e := s.orderEmbOfFin hs
  let first : Fin m ↪ Fin (2 * m) := Fin.castLEEmb (by omega)
  let last : Fin m ↪ Fin (2 * m) := (Fin.natAddEmb m).trans (Fin.castLEEmb (by omega))
  refine ⟨Finset.univ.map (first.trans e.toEmbedding),
    Finset.univ.map (last.trans e.toEmbedding), ?_, ?_, by simp, by simp, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
    exact s.orderEmbOfFin_mem hs (first i)
  · intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hb
    exact s.orderEmbOfFin_mem hs (last i)
  · intro a ha b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hb
    apply e.strictMono
    change (i : ℕ) < m + (j : ℕ)
    omega

private lemma extractorAdj_iff (color : ℕ → ℕ → ℕ → Bool) {n : ℕ}
    {u v : Fin n} (h : u < v) :
    (stronglyExplicitGraph (extractorAdj color) n).Adj u v ↔
      color (Nat.size n) u v = true := by
  have hv : (u : ℕ) ≤ (v : ℕ) := h.le
  simp [stronglyExplicitGraph, extractorAdj, h.ne, min_eq_left hv, min_eq_right hv,
    max_eq_left hv, max_eq_right hv]

private lemma noHom_of_dispersesRectangles (color : ℕ → ℕ → ℕ → Bool) {n m : ℕ}
    (h : DispersesRectangles (color (Nat.size n)) (Nat.size n) m) :
    NoHomogeneousSet (stronglyExplicitGraph (extractorAdj color) n) (2 * m) := by
  have crossPair (s : Finset (Fin n)) (hs : s.card = 2 * m) (bit : Bool) :
      ∃ u ∈ s, ∃ v ∈ s, u < v ∧ color (Nat.size n) u v = bit := by
    obtain ⟨A, B, hAs, hBs, hA, hB, hlt⟩ := orderedRectangle s m hs
    let e := Fin.castLEEmb (Nat.lt_size_self n).le
    obtain ⟨_, ha, _, hb, hbit⟩ := h (A.map e) (B.map e) (by simp [hA]) (by simp [hB]) bit
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
    exact ⟨u, hAs hu, v, hBs hv, hlt u hu v hv, hbit⟩
  constructor
  · intro s hs
    obtain ⟨u, hu, v, hv, hlt, hfalse⟩ := crossPair s hs.card_eq false
    have htrue := (extractorAdj_iff color hlt).mp (hs.isClique hu hv hlt.ne)
    simp [hfalse] at htrue
  · intro s hs
    obtain ⟨u, hu, v, hv, hlt, htrue⟩ := crossPair s hs.card_eq true
    have hnot := ((SimpleGraph.compl_adj _ u v).mp (hs.isClique hu hv hlt.ne)).2
    exact hnot ((extractorAdj_iff color hlt).mpr htrue)

private lemma size_le_log_div_add_one {n : ℕ} (hn : 0 < n) :
    (Nat.size n : ℝ) ≤ log n / log 2 + 1 := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.size_pos.mpr hn).ne'
  have hpow : 2 ^ d ≤ n := Nat.lt_size.mp (by rw [hd]; omega)
  have hpowReal : (2 : ℝ) ^ d ≤ (n : ℝ) := by exact_mod_cast hpow
  have hlog : (d : ℝ) * log 2 ≤ log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpowReal
  have hdiv := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
  simpa [hd, Nat.cast_succ] using add_le_add_right hdiv 1

private lemma twice_size_pow_le (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2 * Nat.size n ^ D ≤ ⌈(log n) ^ ((D : ℝ) + 1)⌉₊ := by
  let K : ℝ := 1 / log 2 + 1
  have hK : 0 ≤ K := by
    have : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
    dsimp [K]
    positivity
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually_ge_atTop (1 : ℝ),
    hlog.eventually_ge_atTop (2 * K ^ D)] with n hn hone hlarge
  have hsize : (Nat.size n : ℝ) ≤ K * log n := by
    calc
      _ ≤ log n / log 2 + 1 := size_le_log_div_add_one hn
      _ ≤ log n / log 2 + log n := add_le_add_right hone _
      _ = K * log n := by simp only [K, div_eq_mul_inv]; ring
  have hbound : (2 : ℝ) * (Nat.size n : ℝ) ^ D ≤ (log n) ^ (D + 1) := by
    calc
      _ ≤ 2 * (K * log n) ^ D := by gcongr
      _ = (2 * K ^ D) * (log n) ^ D := by rw [mul_pow]; ring
      _ ≤ log n * (log n) ^ D := mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = _ := by rw [pow_succ']
  have hrpow : (log n) ^ ((D : ℝ) + 1) = (log n) ^ (D + 1) := by
    rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add, Real.rpow_natCast]
  have hcast : ((2 * Nat.size n ^ D : ℕ) : ℝ) ≤ (log n) ^ ((D : ℝ) + 1) := by
    rw [hrpow]
    exact_mod_cast hbound
  exact Nat.cast_le.mp (hcast.trans (Nat.le_ceil _))

private lemma fromDisperser (D : ℕ) (color : ℕ → ℕ → ℕ → Bool)
    (htime : IsPolyTime (extractorAdj color))
    (hspread : ∀ᶠ d : ℕ in atTop, DispersesRectangles (color d) d (d ^ D)) :
    ∃ C > (0 : ℝ), ∃ adj : ℕ × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (stronglyExplicitGraph adj n) ⌈(log n) ^ C⌉₊ := by
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp hspread
  refine ⟨(D : ℝ) + 1, by positivity, extractorAdj color, htime, ?_⟩
  filter_upwards [twice_size_pow_le D, eventually_ge_atTop (2 ^ d₀)] with n hbound hn
  have hw : d₀ ≤ Nat.size n := (Nat.lt_size.mpr hn).le
  obtain ⟨hclique, hindependent⟩ := noHom_of_dispersesRectangles color (hd₀ _ hw)
  exact ⟨hclique.mono hbound, hindependent.mono hbound⟩

private lemma fromExtractor (K ε : ℝ) (color : ℕ → ℕ → ℕ → Bool) (hε : ε < 1 / 2)
    (htime : IsPolyTime (extractorAdj color))
    (hspread : ∀ᶠ d : ℕ in atTop, ExtractsOnFlatSources (color d) d (K * logb 2 d) ε) :
    ∃ C > (0 : ℝ), ∃ adj : ℕ × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (stronglyExplicitGraph adj n) ⌈(log n) ^ C⌉₊ := by
  apply fromDisperser ⌈K⌉₊ color htime
  filter_upwards [eventually_ge_atTop (1 : ℕ), hspread] with d hd hextract
  exact dispersesRectangles_of_entropyBias (color d) hd (Nat.le_ceil K) hε hextract

/-- Two-sided dispersion of the oracle graph on ordered rectangles of side `m` inside `Fin n`:
some cross pair is a non-edge in both query orders and some cross pair is an edge. -/
def OrderedBipartiteRamsey (adj : ℕ × ℕ × ℕ → Bool) (n m : ℕ) : Prop :=
  ∀ A B : Finset (Fin n), A.card = m → B.card = m → (∀ a ∈ A, ∀ b ∈ B, a < b) →
    (∃ a ∈ A, ∃ b ∈ B, adj (n, (a : ℕ), (b : ℕ)) = false ∧ adj (n, (b : ℕ), (a : ℕ)) = false) ∧
    (∃ a ∈ A, ∃ b ∈ B, adj (n, (a : ℕ), (b : ℕ)) = true ∨ adj (n, (b : ℕ), (a : ℕ)) = true)

private lemma noHom_of_orderedBipartite (adj : ℕ × ℕ × ℕ → Bool) {n m : ℕ}
    (h : OrderedBipartiteRamsey adj n m) :
    NoHomogeneousSet (stronglyExplicitGraph adj n) (2 * m) := by
  constructor
  · intro s hs
    obtain ⟨A, B, hAs, hBs, hA, hB, hlt⟩ := orderedRectangle s m hs.card_eq
    obtain ⟨⟨a, ha, b, hb, h1, h2⟩, -⟩ := h A B hA hB hlt
    have hadj := hs.isClique (hAs ha) (hBs hb) (hlt a ha b hb).ne
    simp [stronglyExplicitGraph, h1, h2] at hadj
  · intro s hs
    obtain ⟨A, B, hAs, hBs, hA, hB, hlt⟩ := orderedRectangle s m hs.card_eq
    obtain ⟨-, a, ha, b, hb, h1⟩ := h A B hA hB hlt
    have hne := (hlt a ha b hb).ne
    have hnot := ((SimpleGraph.compl_adj _ a b).mp (hs.isClique (hAs ha) (hBs hb) hne)).2
    apply hnot
    simp only [stronglyExplicitGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne, h1⟩

private lemma orderedBipartite_of_dispersesRectangles (color : ℕ → ℕ → ℕ → Bool) {n m : ℕ}
    (h : DispersesRectangles (color (Nat.size n)) (Nat.size n) m) :
    OrderedBipartiteRamsey (extractorAdj color) n m := by
  intro A B hA hB hlt
  let e : Fin n ↪ Fin (2 ^ Nat.size n) := Fin.castLEEmb (Nat.lt_size_self n).le
  have key (bit : Bool) : ∃ a ∈ A, ∃ b ∈ B, color (Nat.size n) a b = bit := by
    obtain ⟨_, ha, _, hb, hbit⟩ := h (A.map e) (B.map e) (by simp [hA]) (by simp [hB]) bit
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
    exact ⟨u, hu, v, hv, hbit⟩
  have hval (a b : Fin n) (hab : a < b) :
      extractorAdj color (n, (a : ℕ), (b : ℕ)) = color (Nat.size n) a b ∧
      extractorAdj color (n, (b : ℕ), (a : ℕ)) = color (Nat.size n) a b := by
    have hv : (a : ℕ) ≤ (b : ℕ) := hab.le
    simp [extractorAdj, min_eq_left hv, min_eq_right hv, max_eq_left hv, max_eq_right hv]
  constructor
  · obtain ⟨a, ha, b, hb, hbit⟩ := key false
    obtain ⟨h1, h2⟩ := hval a b (hlt a ha b hb)
    exact ⟨a, ha, b, hb, by rw [h1, hbit], by rw [h2, hbit]⟩
  · obtain ⟨a, ha, b, hb, hbit⟩ := key true
    obtain ⟨h1, -⟩ := hval a b (hlt a ha b hb)
    exact ⟨a, ha, b, hb, Or.inl (by rw [h1, hbit])⟩

/-- Weakest form of the remaining obligation: any polytime oracle whose graphs are two-sided
dispersing on ordered rectangles of polylogarithmic side gives the target. -/
private lemma fromOrderedBipartite (D : ℕ) (adj : ℕ × ℕ × ℕ → Bool)
    (htime : IsPolyTime adj)
    (hspread : ∀ᶠ n : ℕ in atTop, OrderedBipartiteRamsey adj n (Nat.size n ^ D)) :
    ∃ C > (0 : ℝ), ∃ adj : ℕ × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (stronglyExplicitGraph adj n) ⌈(log n) ^ C⌉₊ := by
  refine ⟨(D : ℝ) + 1, by positivity, adj, htime, ?_⟩
  filter_upwards [twice_size_pow_le D, hspread] with n hbound hn
  obtain ⟨hclique, hindependent⟩ := noHom_of_orderedBipartite adj hn
  exact ⟨hclique.mono hbound, hindependent.mono hbound⟩

/-- The disperser route factors through the ordered bipartite form, so the hole in the final
theorem is implied by the hypotheses of `fromDisperser` and of `fromExtractor`. -/
private lemma orderedBipartite_of_disperser (D : ℕ) (color : ℕ → ℕ → ℕ → Bool)
    (hspread : ∀ᶠ d : ℕ in atTop, DispersesRectangles (color d) d (d ^ D)) :
    ∀ᶠ n : ℕ in atTop, OrderedBipartiteRamsey (extractorAdj color) n (Nat.size n ^ D) := by
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp hspread
  filter_upwards [eventually_ge_atTop (2 ^ d₀)] with n hn
  have hw : d₀ ≤ Nat.size n := (Nat.lt_size.mpr hn).le
  exact orderedBipartite_of_dispersesRectangles color (hd₀ _ hw)

end Erdos78.LiExplicit

theorem OMA.solution : type_of% @Erdos78.erdos_78.variants.li_strongly_explicit := by
  have h : ∃ (D : ℕ) (adj : ℕ × ℕ × ℕ → Bool), ComplexityTheory.IsPolyTime adj ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        Erdos78.LiExplicit.OrderedBipartiteRamsey adj n (Nat.size n ^ D) := by
    sorry
  obtain ⟨D, adj, htime, hspread⟩ := h
  exact Erdos78.LiExplicit.fromOrderedBipartite D adj htime hspread
