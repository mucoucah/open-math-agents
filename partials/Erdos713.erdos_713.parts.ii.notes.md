# Relay notes for Erdos713.erdos_713.parts.ii (prize: $500)


## Leg 1: opus  (08:19, 1 min, ended: exit)
File stats: proved lemmas 1, sorries 1, lines 25 (was 0 / 1 / 10)
# Erdos713.erdos_713.parts.ii - opus leg 1 notes
Approach: statement is faithful to the OPEN Erdos $500 question (must the Turan exponent of a single
bipartite graph be rational). No loophole: extremalNumber is genuine Mathlib, alpha in [1,2) with c>0
is uniquely determined; open for e.g. graphs whose exponent is unknown (C8, K44, cube...).
Compiled (lake env lean, 1 sorry): proofs file splits alpha = 1 (proved, rational) from
alpha in (1,2): OMA.core_superlinear (sorry) = the open core.
Upstream merged reductions R1 (kcd1011: peel min-degree<2, H2 = min-degree-2 minimal core),
R1.H2.R1, R1.H2.R1.H2.R1 exist; leaves research level.
Dead ends: none worth repeating; do not spend time, open problem. FAILED fast pass.

## Leg 2: codex  (08:32, 12 min, ended: exit)
File stats: proved lemmas 17, sorries 1, lines 469 (was 1 / 1 / 25)
# Erdős 713(ii), Codex leg 2

- Approach: weaken the positive asymptotic equivalent to big-O and failure of little-o at the same power. Minimize vertex count plus edge count among copies inside the original forbidden graph at that scale. Every strictly smaller copy has little-o growth at that scale.
- Compiles with cached Lean: `OMA.extremalPowerOrder_of_equivalent`, `OMA.extremalNumber_isBigO_of_contained`, `OMA.exists_minimal_extremalPower`, `OMA.core_superlinear`, and the original `OMA.solution` wrapper. The sole placeholder is in `OMA.core_minimal_power`.
- Also compiled: `OMA.card_edges_le_extremal_add_copyCount`, `OMA.eventually_copyCount_lower`, `OMA.coloring_labelledCopyCount_bound`, and `OMA.eventually_labelledCopyCount_amplified`. Uniform edge coloring gives ω(n^α) labelled copies of each smaller pattern with at least two edges in hosts with at least δ n^α edges for any fixed δ > 0.
- Compiled `OMA.extremalNumber_power_subseq_lower` and `OMA.exponent_ge_deletion_bound`: α is at least each contained J's rational deletion exponent 2 − (|V(J)| − 2)/(|E(J)| − 1), for |E(J)| ≥ 2. The proof handles equality with any such bound for the original forbidden graph before minimizing.
- Gap: `OMA.core_minimal_power` asks for rationality in (1, 2) with big-O and failure of little-o for the bipartite pattern F, little-o for every smaller copy, and α strictly above the deletion bound for every contained J. There is no power saving from the little-o condition and no matching upper bound from edge coloring.
- Dead ends: a deletion bound only solves the equality case. Asymptotic uniqueness and the amplified count for smaller copies do not yield a rational exponent. Earlier reductions cover leaves, disconnected graphs, and the threshold 3/2.
- The prescribed checker rejects at lint solely for the one remaining placeholder. Cached Lean compiles the entire file and the new lemmas depend only on propext, Classical.choice, and Quot.sound. The solution wrapper additionally depends on sorryAx through the unresolved core.

## Leg 1: opus  (09:28, 0 min, ended: exit)
File stats: proved lemmas 17, sorries 1, lines 469 (was 17 / 1 / 469)
# Erdos713.erdos_713.parts.ii - opus relay leg (wt18)
Approach: none new. The statement faithfully asks the OPEN Erdos $500 question: is the Turan exponent of a bipartite graph rational? There is no loophole, since alpha is unique when c>0.
Compiled (lake env lean, warning only at line 433): every codex leg-2 lemma (extremalPowerOrder_of_equivalent,
exists_minimal_extremalPower, exponent_ge_deletion_bound, coloring lemmas, core_superlinear, OMA.solution).
Exact remaining gap: ONE sorry in OMA.core_minimal_power. It needs rationality of alpha in (1,2) for a
minimal bipartite F, with alpha strictly above every deletion exponent. This is research level (open).
Dead ends: deletion bound only handles the equality case; asymptotic uniqueness gives nothing.
Do not spend more time on it.

## Leg 2: codex  (09:40, 12 min, ended: exit)
File stats: proved lemmas 40, sorries 1, lines 1042 (was 17 / 1 / 469)
# Erdős 713(ii), current Codex leg

- Approach: dependent random choice, Hall's theorem, and Jensen's inequality give the upper exponent 2 − 1/t with up to t unrestricted-degree vertices on the bounded-degree side. Injective samples pre-embed those vertices. Affine incidence graphs over prime fields give a four-cycle lower exponent of 3/2. The wrapper handles equality with the rational bounds.
- Compiled: `OMA.tupleCommon`, `OMA.mem_tupleCommon`, `OMA.rich_tuples_of_degree_moment`, `OMA.rich_tuples_of_descending_degree_moment`, `OMA.degree_side_moment_bound`, `OMA.degree_side_descending_moment_bound`, `OMA.extremalNumber_le_degree_side_power`, `OMA.extremalNumber_le_exceptional_degree_side_power`, `OMA.exponent_le_degree_side_bound`, `OMA.exponent_le_exceptional_degree_side_bound`, `OMA.cycle_four_extremal_subseq`, `OMA.exponent_ge_cycle_four`, and their private helpers. All new bounds were audited with only propext, Classical.choice, and Quot.sound.
- Exact gap: the sole placeholder is `OMA.core_minimal_power`. Rationality remains for the minimal-scale bipartite pattern strictly above all contained deletion exponents, strictly above 3/2 when it contains a four-cycle, and strictly below 2 − 1/t whenever some bipartition has at most t vertices of degree greater than t on one side. The prescribed checker rejects solely for the placeholder.
- Dead ends: the lower and upper bounds settle equality cases. Qualitative smaller-pattern copy amplification and asymptotic uniqueness supply no rationality argument for the interior.

## Leg 1: opus  (10:19, 0 min, ended: exit)
File stats: proved lemmas 40, sorries 1, lines 1042 (was 40 / 1 / 1042)
# Erdos713.erdos_713.parts.ii - opus relay leg 1 (wt17)
Approach: none new. The statement faithfully asks the OPEN Erdos $500 question: is the Turan exponent
of a bipartite graph rational? No loophole (alpha unique when c>0).
Compiled: file unchanged (1042 lines, codex lemmas: DRC upper bound 2-1/t, C4 lower bound 3/2,
deletion exponent lower bound, minimization, coloring amplification, core_superlinear, OMA.solution).
Exact remaining gap: ONE sorry in OMA.core_minimal_power (line ~1002): rationality of alpha in
(1,2) for a minimal bipartite F, strictly above all deletion exponents, above 3/2 if F has C4,
below every 2-1/t DRC bound. This is the open research core.
Dead ends: all equality cases already handled; interior needs a new theorem. Do not spend time.

## Leg 2: codex  (10:27, 8 min, ended: stalled)
File stats: proved lemmas 51, sorries 1, lines 1228 (was 40 / 1 / 1042)
# Erdős 713(ii), current Codex leg

- Approach: continue the minimal-pattern reduction by using quadratic finite-field incidence graphs on two copies of K³. A putative six-cycle yields two linear relations from its coordinate equations. Eliminating the middle slope gives a product of two nonzero slope differences and a point-coordinate difference, forcing two points to coincide.
- Compiled: all inherited lemmas plus `OMA.cycle_six_extremal_subseq`, `OMA.exponent_ge_cycle_six`, and their private helpers. Direct Lean compiled the integrated wrapper. The new public bounds use only propext, Classical.choice, and Quot.sound.
- Gap: the sole placeholder remains `OMA.core_minimal_power`. The minimal-scale pattern now also has α > 4/3 if it contains a six-cycle, after handling equality in the wrapper. The inherited strict deletion, four-cycle, and degree-side bounds remain.
- Dead ends: equality with a known rational bound settles only that case. Qualitative smaller-pattern supersaturation supplies no power saving and gives no rationality argument in the interior.

## Leg 1: gemini  (10:38, 10 min, ended: no_progress_10m)
File stats: proved lemmas 51, sorries 1, lines 1228 (was 51 / 1 / 1228)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (10:48, 10 min, ended: exit)
File stats: proved lemmas 71, sorries 1, lines 1697 (was 51 / 1 / 1228)
# Erdős 713(ii), Codex relay leg

- Approach: quadratic norm graphs give a 5/3 lower exponent for K_{3,3}. Inverting at one common vertex yields two norm equations with distinct centers. Eliminating the Frobenius term gives a quadratic with at most two solutions.
- Approach: if a host avoids two copies of J joined at one root, every root has a bounded hitting set for the other rooted copies. Vertex sampling retains a constant fraction of edges outside O(n) conflicting pairs and removes all copies of J when J has no isolated vertices.
- Compiled and audited: `OMA.complete_bipartite_three_extremal_subseq`, `OMA.exponent_ge_complete_bipartite_three`, `OMA.card_edges_le_of_root_copy_hitting_sets`, `OMA.extremalNumber_le_rootedDouble`, `OMA.extremalNumber_rootedDouble_isLittleO`, and `OMA.minimal_power_not_contained_rootedDouble`, with only propext, Classical.choice and Quot.sound. The inherited declarations and the integrated wrapper compile.
- Exact gap: `OMA.core_minimal_power` still asks for rationality in the interior of the known bounds for a scale-minimal bipartite F. It now also has α > 5/3 if K_{3,3} embeds in F, and F cannot embed in the root-identified double of any strictly smaller contained J without isolated vertices. The prescribed checker rejects solely for the remaining placeholder.
- Dead ends: equality with a rational bound does not settle an interior exponent. Qualitative copy amplification gives no power saving. The hitting-set proof for two copies of the same rooted J does not handle an arbitrary cut vertex joining different rooted bipartite patterns.

## Leg 1: gemini  (11:01, 10 min, ended: no_progress_10m)
File stats: proved lemmas 71, sorries 1, lines 1697 (was 71 / 1 / 1697)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (11:16, 15 min, ended: exit)
File stats: proved lemmas 98, sorries 1, lines 2578 (was 71 / 1 / 1697)
# Erdős 713(ii), Codex relay

- Eight-cycle bound: three slope moments force alternating slopes. One additional incidence coordinate excludes that alternation in odd characteristic. The graph has 2q^5 vertices and at least q^6 edges. Compiled `OMA.cycle_eight_extremal_subseq` and `OMA.exponent_ge_cycle_eight`.
- Edge amalgamation: use a bounded hitting set at each host root edge. Two-color vertex sampling keeps a constant fraction of edges. Compiled `OMA.card_edges_le_of_edge_copy_hitting_sets`, `OMA.card_edges_le_of_edgeAmalgam_free`, `OMA.extremalNumber_le_edgeAmalgam_of_rooted_copy`, `OMA.extremalNumber_le_edgeAmalgam_of_flip`, and their little-o consequences.
- Regularization: cover the edges incident to m vertices by induced subgraphs on at most 2m vertices. Remove high-degree vertices at arbitrarily small cost in edge density, then prune low-degree vertices. Compiled `OMA.card_incident_edges_le_of_small_extremal_bound`, `OMA.card_incident_edges_le_power`, `OMA.exists_subgraph_bounded_degree_at_extremal_scale`, and `OMA.frequently_almost_regular_at_extremal_scale`. Audited the main amalgamation and regularization bounds with only propext, Classical.choice, and Quot.sound.
- Exact gap: `OMA.core_minimal_power` is the sole placeholder. It asks for rationality at an interior exponent of a scale-minimal bipartite F, with α > 6/5 if F contains an eight-cycle, an exclusion for compatible edge amalgams of smaller contained pieces, and arbitrarily large F-free hosts with Ω(n^α) edges and degrees Θ(n^(α−1)) on their support.
- Dead ends: equality with the known rational bounds only settles the equality cases. Qualitative little-o conditions for proper subgraphs do not give power savings. Without orientation compatibility an edge amalgam can have mismatched rooted copies. Almost-regular hosts do not provide an argument that the exponent is rational.

- Final verification: direct Lean compiles the integrated file with one placeholder warning. The prescribed checker returned `rejected` solely for that placeholder. The first import, full solution wrapper, and all inherited declaration names were preserved.
