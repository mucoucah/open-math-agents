# Relay notes for Erdos1029.erdos_1029 (prize: $100)


## Leg 1: grok  (05:53, 21 min, ended: budget15_no_progress)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 1: opus  (10:05, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos1029.erdos_1029 notes (opus leg)
Approach: none feasible. Target = Tendsto (R(k) / (k * 2^(k/2))) atTop atTop, the open Erdos $100 problem.
Faithfulness: diagonalRamsey k = classicalRamsey k k = graphRamsey K_k K_k = sInf {n | every C on Fin n has K_k in C or Cc}.
The set is nonempty by Ramsey, so sInf is the true R(k); no 0-value / empty-set loophole. Real division, rpow 2^(k/2): faithful.
Best known: R(k) >= (sqrt2/e) k 2^(k/2) (1+o(1)) (Spencer 1975), off by a constant factor; no improvement known.
Compiled: nothing new (file = single sorry skeleton).
Remaining gap: the whole open conjecture.
Dead ends: none worth trying; FAILED fast pass.

## Leg 2: codex  (10:09, 4 min, ended: exit)
File stats: proved lemmas 9, sorries 1, lines 152 (was 0 / 1 / 10)
# Erdos1029 relay leg 2

Approach: use the existing Erdős–Szekeres Ramsey theorem to show the defining set of sizes is nonempty, then use graph embeddings to prove monotonicity in the number of vertices. Turn the limit into an equivalent graph-existence problem. An even-clique-size reduction removes the real powers and floors. Restrict the witness for `2 * (k / 2)` to prove the claim for `k`, allowing a factor of four in the vertex count.

Compiled with direct Lean: `forcesClique_mono`, `forcesClique_choose`, `lt_diagonalRamsey_iff`, `scale_pos`, `tendsto_iff_cliqueFree_graphs`, `scale_even`, `floor_mul_scale_even`, `scale_le_four_mul_of_div_two`, and `tendsto_iff_even_cliqueFree_graphs`. CI lint rejects the one remaining `sorry`.

Remaining gap: for every `a : ℕ` and all sufficiently large `t : ℕ`, construct a graph and complement both `(2 * t)`-clique-free on `a * (2 * t * 2 ^ t)` vertices. The sole `sorry` in `OMA.solution` is this assertion.

Dead ends: the imported `sInf` really is the finite Ramsey minimum. The standard symmetric local lemma for random edge colors has dependency degree of order `choose k 2 * choose (n-2) (k-2)` and gives only a constant multiplier at this scale. Ordinary lexicographic graph products multiply both clique and independence numbers, so their vertex-count amplification does not give the needed additive control of the clique parameter. No progress on the arbitrary-`a` construction.
