# Relay notes for Erdos159.erdos_159 (prize: $100)


## Leg 1: opus  (07:59, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos159.erdos_159 (opus leg 1)
Approach: checked the statement for a loophole. None found.
- graphRamsey = sInf {n | forall C on Fin n, G contained in C or H contained in complement C}. The set is nonempty (Ramsey), so the value is the real R(C4,K_n).
- cycleGraph 4 is a real C4. The target is R(C4,K_n) <= C n^(2-c) for some c>0. That is the open $100 Erdos problem. The best known bound is O(n^2/log^2 n) (Szemeredi / Caro-Li-Rousseau-Zhang).
Compiled: nothing new. The proofs file is unchanged (one sorry).
Existing work: reduction R1 by TheWaler (PR 6002) is merged. Its steps R1.H1 (triangle-free case) and R1.H2 (triangle-packing case) are both still research-level.
Gap: the whole open problem. An exponent saving over n^2 is unknown even for triangle-free C4-free graphs.
Dead ends: none worth repeating. Report FAILED fast pass.

## Leg 2: codex  (08:12, 12 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 585 (was 0 / 1 / 10)
# Erdos159.erdos_159, Codex leg 2

Approach: average over fixed-size samples and delete one vertex per sampled triangle. Then prune low ordinary degree and low triangle degree together. Ordinary deletions charge an independent-set budget. Every triangle in the triangle-pruned set is charged to its first vertex removed.

Compiled with pinned Lean: `avoid_family`, `fixed_sample_bound`, `triangle_count_of_induced_cap` (m ≤ 2L or m³ ≤ 32 T L²), `card_le_of_sparse_triangles`, `split_at_triangle_degree`, `card_le_of_triangle_degree_caps`, `minimum_degree_core`, `indep_card_le`, and `split_at_both_degrees`. The three transfers `triangle_free_cap_of_degree_window`, `large_triangle_degree_cap_of_windows`, and `ramsey_of_triangle_degree_bounds` all compile and depend only on propext, Classical.choice, Quot.sound. The exact target applies these at c = ε/2.

Exact remaining goal: ∃ ε A B : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ A ∧ 0 ≤ B ∧ TriangleFreeWindowBound ε A ∧ DenseDegreeWindowBound ε B. The first conjunct is the R1.H1 bound at fixed parameters. The second asks for |S| ≤ B n^(2−ε/2) in C4-free graphs with no n-vertex independent set, where every x ∈ S satisfies |S| ≤ 16n(deg_S(x)+1) and lies in > n^ε triangles in S. Neither power bound is proved.

R1 connection for follow-up: its degree upper bound and cross-edge uniqueness hold automatically. Given H1 at ε, a maximal disjoint packing misses at most 2A n^(2−ε) vertices by `triangle_free_cap_of_degree_window`. Below twice that size the dense cap is immediate from H1, and above it at least half the core is packed. Thus one can attack the H2 class with the added minimum triangle-degree constraint.

Dead ends: the previous leg found no definitional shortcut. A maximal packing alone certifies only linearly many triangles. The sparse-triangle counting argument needs an actual polynomial bound for triangle-free sets.

Checker: rejected at lint on the one remaining sorry. Direct pinned Lean elaborated the entire partial file.

## Leg 1: opus  (09:53, 0 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 585 (was 16 / 1 / 585)
# Erdos159.erdos_159, opus relay leg 1 (wt17)
Approach: none new. This is the open $100 Erdos problem R(C4,K_n) << n^(2-c), faithful, no loophole (checked by earlier legs and in memory). The best known bound is O(n^2/log^2 n).
Compiled (kept unchanged, from the codex leg): avoid_family, fixed_sample_bound, triangle_count_of_induced_cap, card_le_of_sparse_triangles, split_at_triangle_degree, card_le_of_triangle_degree_caps, minimum_degree_core, indep_card_le, split_at_both_degrees, triangle_free_cap_of_degree_window, large_triangle_degree_cap_of_windows, ramsey_of_triangle_degree_bounds.
Exact remaining gap (one sorry): exists eps A B, TriangleFreeWindowBound eps A and DenseDegreeWindowBound eps B. The first is a power saving for triangle-free C4-free graphs with no n-independent set (R1.H1); the second is the dense triangle-degree core. Both are open research.
Dead ends: no definitional shortcut; a maximal packing gives only linearly many triangles.
Recommendation: do not spend more legs here. Report STALLED.

## Leg 2: codex  (10:05, 11 min, ended: exit)
File stats: proved lemmas 37, sorries 1, lines 1263 (was 16 / 1 / 585)
# Erdos159.erdos_159, Codex relay

Approach: in a four-cycle-free graph each edge lies in at most one triangle. Choose one vertex independently in each triangle and keep the two incident edges. The resulting spanning subgraph is triangle-free. If a k-set W is independent after deletion, each original edge inside W belongs to a triangle meeting W exactly twice, whose choice is then forced to be its third vertex. Minimum-degree pruning finds at least k*d such independent coordinates for k >= 8*n*d. Count bad assignments for each W by 3^(-k*d), then sum over size-k sets. Taking d = log_3 m + 1 gives a spanning triangle-free subgraph with no independent set of size 8*n*d. The quadratic cap m <= 2*n^2 and log n <= n^(ε/4)/(ε/4) absorb the loss and transfer the triangle-free exponent saving ε to ε/2 for the full Ramsey number.

Compiled by pinned Lean: `common_neighbor_unique`, `triangle_eq_of_shared_edge`, `neighborhood_triangle_bounds`, `triangleDeletion_free`, `choice_outside_of_independent`, `constrainedTriangles_card`, `badTriangleChoices_card`, `exists_triangle_free_spanning_subgraph`, and `ramsey_of_triangle_free_window`. Also preserved the original lemmas and compiled the fallback packing transfer `dense_degree_window_of_packing` with `exists_triangle_packing` and `triangle_cross_edge_unique`.

Exact remaining gap (single sorry): `∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ A ∧ TriangleFreeWindowBound ε A`. This is R1.H1, a power saving for triangle-free, C4-free graphs in the ordinary-degree window and with no independent n-set. The dense triangle-degree hypothesis has been discharged.

Dead ends: no definitional shortcut. Maximal packing alone gives only linearly many triangles. A naive random vertex subset loses a power when eliminating all triangles. The edge-choice argument avoids that loss.

Direct Lean compiles the whole file with only the remaining sorry warning.

Final verification: `triangle_free_window_of_ramsey` proves the converse using `bad_card_lt_graphRamsey`, so the single remaining hypothesis is equivalent to the parent power bound. The axiom audit of both transfers and `exists_triangle_free_spanning_subgraph` reports only `propext`, `Classical.choice`, and `Quot.sound`. The exact CI checker reports `rejected` with reason `lint: forbidden: 'sorry'`. Its lint failure is at the sole placeholder in `OMA.solution`, line 1263. All prior helpers are preserved.
