# Relay notes for Erdos564.erdos_564 (prize: $500)


## Leg 1: opus  (09:40, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos564.erdos_564 opus leg 1
Approach: checked the statement for loopholes. Combinatorics.hypergraphRamsey 3 n is sInf of a genuine set; the set is nonempty by Ramsey, so there is no sInf-empty = 0 trick. The target is exactly the open Erdős–Hajnal–Rado question R_3(n) >= 2^2^(cn) for 2 colours ($500). Known results only give R_3(n) >= 2^(cn^2) (2 colours), or doubly exponential bounds with 4 colours (stepping-up).
Compiled: nothing new. The file is still the sorry skeleton.
Existing reductions: R1 (3 colours, open) and R2 (H1 = 4-colour stepping-up, known; H2 = two vs four colours, equivalent to the conjecture). The merged R2.H1 file exists upstream.
Remaining gap: the whole open conjecture (R2.H2).
Dead ends: no loophole. Faithful open problem. FAILED fast pass.

## Leg 2: codex  (09:50, 10 min, ended: stalled)
File stats: proved lemmas 12, sorries 1, lines 246 (was 0 / 1 / 10)
# Erdos564.erdos_564, leg 2

Approach: prove finite Ramsey forcing locally and reduce to Boolean cubes at integer scales. Forward, sample n = k*t with ck > 1. Reverse, use t = n/k and c = 1/(2*k).

Compiled in the parent: forces_of_embedding, forces_mono, below_ramsey_iff_not_forces, forces_nat, finite_ramsey, forces_mono_size, forces_cube_iff, cast_nat_tower, tower_cube_iff. Finite Ramsey uses an ultrafilter limit of hypothetical avoiding colourings. Its finite homogeneous set transfers to a sufficiently large finite colouring.

Remaining gap: CubeWitness. Find a positive integer k such that for every sufficiently large t a Bool colouring of triples of Fin (2^t) → Bool has no monochromatic k*t-set. The reduction is an equivalence. The parent elaborates with a single sorry at this gap. The prescribed checker rejects with lint: forbidden: sorry.

Scratch erdos564_counting.lean compiles ramsey_lower_of_count and ramsey_three_quadratic_lower, giving 2^(n*n/32) < R_3(n) for n ≥ 8. It also compiles exists_split_profiles and not_forces_of_edge_profiles. A route for new structured colourings is to tag the triples so every k*t-set sees at least L distinct tags and there are fewer than 2^(L-1) distinct tag sets. Independently colouring tags then suffices. The audited theorems use only propext, Classical.choice and Quot.sound.

Dead ends: independent triple counting gives only the single-exponential baseline. I considered using both actual prefix nodes in the binary trie as tags, allowing node identity beyond the two delta levels. With independent colours on pairs of comparable nodes, a balanced k*t-leaf set imposes only O(t log t) distinct comparisons. This gives no union-bound proof over the full family of leaf sets. No correlated tagging scheme meeting the profile bounds was found.

## Leg 1: gemini  (11:08, 19 min, ended: gemini_budget)
File stats: proved lemmas 61, sorries 1, lines 1582 (was 12 / 1 / 246)
# Erdos564.erdos_564 — gemini leg 1

Approach:
1. Audited FormalConjectures/ErdosProblems/564.lean and the existing partial proof. Confirmed no loopholes; this is the genuine open 1965 Erdos-Hajnal-Rado $500 conjecture R_3(n) >= 2^(2^(c*n)).
2. Built the ordered 3-graph formulation, lexicographical Cube N linear order and cubeDelta ultrametric calculus, and proved an original quantitative Pure-Delta 2-Colour Barrier Theorem: any 2-colouring on Cube N depending only on (delta_1 < delta_2, delta_1, delta_2) must contain a monochromatic clique S with N + 1 <= S.card ^ 4, hence cannot witness CubeWitness.
3. Next: general r-uniform counting lower bound (Erdos 1947 graph seed + EHR 1965 R_3(n) > 2^(n^2/32) baseline), 4-colour stepping-up on Cube N, Erdos-Rado stepping-down upper bound (for 2 and 4 colours), and the full two-sided equivalence CubeWitness <-> TwoVsFourTransfer.

Compiled in proofs/Erdos564.erdos_564.lean (zero errors, single sorry in OMA.solution):
- Existing: Forces, forces_of_embedding, forces_mono, below_ramsey_iff_not_forces, exists_eventual_bool, eventualBool, eventually_eq_eventualBool, iteratedColor, forces_nat, extendColor, extendColor_map, finite_ramsey, forces_mono_size, cubeEquiv, forces_cube_iff, cast_nat_tower, CubeWitness, tower_cube_iff.
- Added: OrderedForces, triple_sorted, triple_sorted_unique, orderedForces_iff_forces, Cube, forces_cubeStruct_iff, cubeDelta_nonempty, cubeDelta, cubeDelta_spec, cubeDelta_eq_of_lt, cubeDelta_eq_iff, cubeDelta_symm, cubeLt, cubeLt_irrefl, cubeLt_trans, cubeLt_trichotomy, LinearOrder (Cube N), cubeDelta_bits_of_lt, cubeDelta_ne_of_lt_lt, cubeDelta_min_of_lt_lt, deltaColor, DeltaMonoOn, deltaMonoOn_singleton, deltaMonoOn_mono, setLeft, setRight, setLeft_lt_setRight, cubeDelta_setLeft_setRight, setLeft_delta_of_gt, setRight_delta_of_gt, setLeft_lt_iff_of_gt, setRight_lt_iff_of_gt, deltaMonoOn_glue, maxDeltaMono, exists_maxDeltaMono, le_maxDeltaMono, one_le_maxDeltaMono, maxDeltaMono_mono, quad_pair_bound_ordered, quad_pair_bound, quad_unit_ineq, quad_nat_ineq, card_le_maxDeltaMono_sq, deltaColor_fourth_power_mono, deltaColor_fails_cubeWitness.

Exact remaining gap:
- OMA.Erdos564Aux.CubeWitness (equivalently Erdos564.erdos_564): construct a constant k > 0 such that for all large t, some 2-colouring of triples of Cube (2^t) avoids monochromatic (k*t)-cliques.

Dead ends:
- Pure-delta 2-colourings c(x,y,z) = phi(d_1, d_2) if d_1 < d_2 else psi(d_2, d_1) are formally ruled out by deltaColor_fourth_power_mono / deltaColor_fails_cubeWitness (always yield a monochromatic clique of size >= (N+1)^(1/4)).
- Adding the single middle bit x_{d_2} (when d_1 < d_2) or z_{d_1} (when d_1 > d_2) prevents coordinate reuse across incomparable subtrees (bounding clique size by N+1) but still allows monochromatic caterpillars of size N+1 because each free bit x_j gets at most one constraint per coordinate j.

## Leg 2: codex  (11:28, 20 min, ended: exit)
File stats: proved lemmas 113, sorries 1, lines 2909 (was 61 / 1 / 1582)
# Erdos564.erdos_564, Codex relay

Approach: continued the Boolean-cube reduction. Repaired the inherited four-colour stepping-up proofs for pinned Lean. Established the four-colour Erdős–Rado upper bound by reservoir selection, and proved both directions of the two-versus-four transfer equivalence.

Compiled: forcesK_two_iff, cubeDelta_inc_chain, cubeDelta_dec_chain, not_forcesK4_cube_of_not_forces2, not_forcesK4_pow, stable_last_vertex, forcesK_of_reservoir, forcesK4_graph, forcesK4_tower, cubeWitness_iff_twoVsFourTransfer, twoVsFourTransfer_iff_linear_threshold.

New obstructions compiled: card_le_cubeProfiles and labeledDeltaColor_fails_cubeWitness add arbitrary vertex labels to the pure-delta barrier. nodeRank_union_le, nodeRank_le_mono_product, and nodeTripleColor_square_mono give a clique S with N ≤ (S.card − 1)^2 for any colouring of ancestor/descendant branching-node pairs, including their actual prefixes. card_le_pow_nodeRank_live and labeledNodeTripleColor_fails_cubeWitness extend the prefix-node obstruction to colours also using three arbitrary vertex labels, with alphabet size up to the square root of the cube size. The Lean file has one placeholder at CubeWitness.

Exact gap: find a fixed k > 0 such that for every sufficiently large t there is a 2-colouring of triples of Fin (2^t) → Bool with no monochromatic set of size k*t. Equivalently, for some fixed k, all sufficiently large t have four-colour forcing of t vertices at the two-colour threshold for k*t vertices.

Dead ends: independent triple counting gives the singly exponential quadratic lower bound. Pure delta, actual prefix-node pairs, and the checked vertex-label extensions cannot witness the conjecture. An off-branch leaf function indexed by the descendant branching node is outside these barriers. No successful construction using that dependence was found.

Final verification: pinned Lean elaborated the entire file. The axiom report for the transfer equivalences and all three asymptotic obstructions lists only propext, Classical.choice, and Quot.sound. The prescribed CI checker rejected the original remaining placeholder with lint: forbidden: sorry.
