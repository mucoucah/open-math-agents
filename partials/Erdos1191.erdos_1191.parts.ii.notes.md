# Relay notes for Erdos1191.erdos_1191.parts.ii (prize: $1000)


## Leg 1: opus  (08:21, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_opus: Erdos1191.erdos_1191.parts.ii
Approach: fast pass audit only. Statement is faithful: exists infinite Sidon A, c>0 with
liminf |A cap [1,x]| (log x)^c / sqrt x > 0 (ENNReal). Any c>0 still forces counting
function >= x^(1/2)/polylog, which implies Erdos 39 (N^(1/2-eps) Sidon), open $500;
best known is Ruzsa x^(sqrt2-1+o(1)). No loophole (large c does not help; x=0,1 irrelevant
for liminf; IsSidon is the standard one).
Compiled: nothing new; file is the bare sorry skeleton.
Gap: the whole open problem.
Dead ends: none beyond the open-problem barrier. Verdict FAILED fast pass.

## Leg 2: codex  (08:31, 10 min, ended: exit)
File stats: proved lemmas 6, sorries 1, lines 249 (was 0 / 1 / 10)
# Codex leg 2 — Erdős 1191(ii)
Approach: square the counts at dyadic checkpoints and use compactness of `ℕ → Bool` to pass from finite witnesses to an infinite set. Restriction of an infinite witness proves the converse.
Compiled in the proof: `density_from_dyadic_counts`, `closed_prefix_condition`, `compact_prefix_conditions`, `infinite_of_dyadic_counts`, `sidon_of_finite_dyadic_witnesses`, `finite_dyadic_witnesses_of_density`. The file elaborates with one remaining placeholder. Audited the density, infinitude, compactness application, and converse lemmas; they use only propext, Classical.choice, and Quot.sound.
Exact gap: `∃ d J : ℕ, FiniteDyadicSidon d J`. For every N, one Sidon subset S of [1, 2^N] must satisfy 2^j ≤ |S ∩ [1, 2^j]|² (j+1)^(2(d+1)) simultaneously for J ≤ j ≤ N, with d and J independent of N. CI rejected the remaining placeholder at lint.
Alternative route: `erdos1191_codex_pruning.lean` compiles and proves `nearby_dyadic_packing_implies_H1`. Give every large dyadic block a dense Sidon set, and prevent shared positive differences between blocks i < j only for j/3 < i. The pruning lemmas delete at most 2^(j/3) points from block j to remove all distant collisions, preserve the count with one extra log power, and construct the merged H1 finite witnesses. Dense packing at nearby scales is unproved. See related.md for the separate H2 encoding hint.
Dead ends: a roughly uniform near-optimal finite Sidon set for N fails at earlier cutoffs. Independent thinning gives no control of nearby-block difference collisions. Distinct small prime scale multipliers still collide on their common multiples. Giving every block a distinct subspace slope in two equal-size coordinates costs half the ambient dimension before imposing Sidon.

## Leg 1: opus  (09:23, 0 min, ended: exit)
File stats: proved lemmas 6, sorries 1, lines 249 (was 6 / 1 / 249)
# notes_opus (relay leg 1, wt16): Erdos1191.erdos_1191.parts.ii
Approach: audit only. File already holds codex compactness/density glue (6 compiled lemmas:
density_from_dyadic_counts, closed_prefix_condition, compact_prefix_conditions,
infinite_of_dyadic_counts, sidon_of_finite_dyadic_witnesses, finite_dyadic_witnesses_of_density),
plus one sorry: exists d J, FiniteDyadicSidon d J.
Gap: that sorry is EQUIVALENT to the target (the converse lemma is proved), i.e. the open $1000
Erdos problem; it implies open Erdos 39 (best known Ruzsa x^(sqrt2-1+o(1))). No loophole.
Compiled this leg: nothing new (file left unchanged).
Dead ends: the open-problem barrier; see codex notes (uniform near-optimal finite Sidon fails at
early cutoffs, independent thinning, prime multipliers, subspace slopes).

## Leg 2: codex  (09:28, 5 min, ended: stalled)
File stats: proved lemmas 6, sorries 1, lines 249 (was 6 / 1 / 249)
Approach: preserve the six previous finite-prefix/density lemmas and discharge R2.H2 independently. Pack the raw bits in chunks of widths 1, 2, 4, ...; at each chunk put base-4 digits of the dyadic label and its square in two lower fields, with carry guards. A common truncation decodes the three sums; a sum and sum of squares determine an unordered pair.
Compiled: .oma/scratch/codex_1191_encoding.lean, theorem Codex1191.dyadic_additive_code. Audited axioms are propext, Classical.choice, Quot.sound. Size is at most 2^j (j+2)^15 on dyadic block j.
Exact remaining target gap: dense dyadic Sidon blocks with disjoint positive differences for j/3 < i < j, uniformly through every finite horizon (R2.H1). Prior R2 pruning and compactness give the target once this is proved.
Dead ends carried forward: single uniform finite witness at the final horizon, independent thinning, distinct small prime multipliers, and allocating a distinct subspace slope to every block.

## Leg 3: fable  (09:33, 4 min, ended: exit)
File stats: proved lemmas 34, sorries 1, lines 854 (was 6 / 1 / 249)
# notes_fable (relay leg 3, wt16): Erdos1191.erdos_1191.parts.ii

Approach: no restart. Re-audited the statement (faithful, open $1000 problem, no loophole: Real.log, rpow,
standard IsSidon, liminf in ENNReal over x : Nat; any fixed c still forces x^(1/2)/polylog, beyond Ruzsa
x^(sqrt2-1), implies Erdos 39). Then promoted the previous leg's scratch file codex_1191_combined.lean
into the proofs file after checking it compiles directly (lake env lean, 9 s, only warning: one sorry).

Proofs file now (854 lines, ONE sorry, compiles):
- kept all six old lemmas: density_from_dyadic_counts, closed_prefix_condition, compact_prefix_conditions,
  infinite_of_dyadic_counts, sidon_of_finite_dyadic_witnesses, finite_dyadic_witnesses_of_density
- new, compiled: namespace Codex1191 (base/span/weight/pack/encode ... dyadic_additive_code) = full proof
  of R2.H2 (additive code remembering the dyadic label pair, size <= 2^j (j+2)^15)
- new, compiled: sidon_positive_difference_unique, prune_short_differences,
  prune_distant_dyadic_collisions, eventually_dyadic_pruning_budget,
  eventually_dyadic_pruning_preserves_count, two_block_core, coded_union_sidon, eventually_log_shift,
  coded_finite_witness (R2 glue: nearby packing + code -> FiniteDyadicSidon)
- OMA.solution is proved from the single hypothesis hpacking : NearbyDyadicSidon (the only sorry).

Exact remaining gap (= merged reduction R2.H1, def NearbyDyadicSidon in the file):
exists d J, for every N a family B j of finsets in [2^j, 2^(j+1)), each Sidon, with
2^j <= |B j|^2 (j+1)^(2(d+1)) for J <= j <= N, and for j/3 < i < j no positive difference of B i equals
a positive difference of B j. This is still the open problem in substance (near-extremal Sidon blocks
whose difference sets are disjoint across about (2/3) j nearby scales).

Possible cheap weakening not done (no real value): the threshold j/3 can be raised to about
j/2 - (d+2) log2 j, because pruning one endpoint of every difference < t in block j costs <= t points.

Dead ends (all recorded before, still valid): one uniform near-optimal finite Sidon set (fails at early
cutoffs); independent random thinning (collisions at scales i > j/2 exceed block size); distinct small
prime multipliers per block (collide on common multiples); a distinct subspace slope per block (halves
the dimension); digit-restricted sets in base p with digit set T (need |T| >= sqrt p for density, then
T - T covers all leading digits, so difference classes cannot be separated).

Backup of the 249-line file from before this leg: .oma/scratch/backup_fable_before_promote.lean
Verdict: RESULT: STALLED. Blocker: sorry at hpacking : NearbyDyadicSidon in OMA.solution (open problem).

## Leg 1: opus  (10:12, 0 min, ended: exit)
File stats: proved lemmas 34, sorries 1, lines 854 (was 34 / 1 / 854)
# notes_opus (relay leg 1, wt16, later round): Erdos1191.erdos_1191.parts.ii
Approach: audit only; file unchanged (854 lines, ONE sorry, compiles per leg 3).
Compiled (kept): six compactness/density lemmas, Codex1191.dyadic_additive_code (= R2.H2),
pruning glue (prune_short_differences, prune_distant_dyadic_collisions, ...).
Exact gap: hpacking : NearbyDyadicSidon (= R2.H1): dense Sidon dyadic blocks with disjoint positive
differences for j/3 < i < j, uniformly in the horizon. This is the open core of a $1000 Erdos problem
(implies Erdos 39; best known Ruzsa x^(sqrt2-1+o(1))). No loophole.
Dead ends: all those listed in handover_notes (uniform finite witness, independent thinning, prime
multipliers, subspace slopes, R3 parity/range splits; a code preserves sums so cannot kill cross-block collisions).

## Leg 2: codex  (10:22, 10 min, ended: exit)
File stats: proved lemmas 46, sorries 1, lines 1243 (was 34 / 1 / 854)
Approach: preserve the prior compactness, encoding, and pruning proof. In each block form a graph whose edges are pairs with a positive difference also seen in an earlier block. Sidon injects these edges into the distinct shared differences. Turán on the complement gives an independent set of size at least M²/(M+2D), for M points and D shared differences. Polynomial average degree costs only a polynomial factor in block size.
Compiled this leg: dyadic_count_after_budget; mem_positiveDifferences; prune_forbidden_differences, prune_shared_dyadic_differences, dyadic_conflicts_card_le; independent_set_from_edge_count, prune_sparse_forbidden_differences; nearby_of_sparse_dyadic_blocks, sparse_of_nearby_dyadic_blocks; dyadic_conflict_budget_of_card_le, dyadic_conflict_budget_from_scale, dyadic_conflict_budget_from_pairwise_overlap. All 34 prior lemmas retained. Direct Lean compiles with the one existing placeholder. Both directions between NearbyDyadicSidon and SparseDyadicSidon and the pairwise estimate use only the three allowed axioms.
Exact gap: hpacking : SparseDyadicSidon. Fix d,k,J independent of N. For every horizon N, construct Sidon B j in [2^j,2^(j+1)) with 2^j ≤ M_j² (j+1)^(2(d+1)) and M_j + 2D_j ≤ M_j (j+1)^k for J ≤ j ≤ N. Here M_j is |B j| and D_j is the number of distinct positive differences of B j occurring in any B i with i<j.
Sufficient pairwise bound: for s(j)<i<j, limit |Δ(B i) ∩ Δ(B j)| to 2^⌊j/2⌋ (j+1)^ℓ with fixed ℓ, and take any s(j) with 2^s(j) at most the same quantity. The contribution of i≤s(j) is automatic. In particular absolute separation at j/2<i<j suffices.
Dead ends: prior handover records final-scale uniform witnesses, independent thinning, prime multipliers, subspace slopes, and digit-restricted difference classes. A fixed polynomial-size residue tag leaves multiples of its modulus unseparated. Recursing by first differing residue digit leaves the cumulative density loss unresolved.
CI verdict: rejected at lint for the sole remaining sorry.

## Leg 1: gemini  (10:49, 24 min, ended: exit)
File stats: proved lemmas 70, sorries 1, lines 2262 (was 46 / 1 / 1243)
# notes_gemini (relay leg 1, wt16): Erdos1191.erdos_1191.parts.ii

Approach: preserved all 46 prior lemmas unchanged. Added a purely finitary probabilistic alteration theorem (`alteration_sidon_avoiding`, averaging over colorings `S -> Fin q` in `Nat` with no measure theory) that simultaneously removes cross-block conflict pairs, 3-APs, and 4-element additive quadruples. This relaxes `SparseDyadicSidon` to `ApproxDyadicSidon` (blocks in `[0, 2^j)`, no Sidon requirement) and further to `AdditiveEnergyDyadicBlocks`, expressed purely in terms of standard additive energy `E(B_j)` and pairwise cross-additive energy `E(B_i, B_j)` across `j/2 < i < j`. Proved full two-way equivalences (`AdditiveEnergyDyadicBlocks <-> ApproxDyadicSidon <-> SparseDyadicSidon <-> NearbyDyadicSidon`).

Compiled (direct `lake env lean`: zero errors, zero warnings beyond sole sorry; all audited axioms strictly within `[propext, Classical.choice, Quot.sound]`; `tools/check.sh` rejects only at lint for the single sorry):
- All 46 prior lemmas retained.
- New definitions/lemmas: `conflictPairs`, `mem_conflictPairs`, `card_conflictPairs_le_of_isSidon`, `threeAPs`, `mem_threeAPs`, `threeAPs_eq_empty_of_isSidon`, `fourQuadruples`, `mem_fourQuadruples`, `fourQuadruples_eq_empty_of_isSidon`, `no_nontrivial_sum_of_empty`, `isSidon_of_no_threeAPs_fourQuadruples`, `delete_conflicts_and_quadruples`, `card_fun_zero_on`, `alteration_sidon_avoiding`, `positiveDifferences_image_add`, `isSidon_image_add`, `positiveDifferences_image_sub`, `isSidon_image_sub`, `earlierBlockDifferences`, `ApproxDyadicSidon`, `nearby_of_approx_dyadic_blocks`, `approx_of_sparse_dyadic_blocks`, `crossDifferenceMatches`, `card_conflictPairs_le_crossDifferenceMatches`, `approx_conflict_budget_from_cross_energy`, `additiveEnergy`, `crossAdditiveEnergy`, `additiveEnergy_lower_bound`, `additiveEnergy_le_of_isSidon`, `crossAdditiveEnergy_eq`, `AdditiveEnergyDyadicBlocks`, `approx_of_additiveEnergy_dyadic_blocks`, `additiveEnergy_of_nearby_dyadic_blocks`.

Exact remaining gap: `hpacking : AdditiveEnergyDyadicBlocks` in `OMA.solution`. Fix `d, k, J` independent of `N`. For every horizon `N`, construct `B j ⊆ [0, 2^j)` (not required to be Sidon) such that for `J <= j <= N`:
1. `2^j <= |B j|^2 * (j+1)^(2(d+1))`
2. `E(B j) <= 2 |B j|^2 + |B j| (j+1)^(2k)`
3. `|{(u, v) in B j^2 : 0 < u - v < 2^(j/2)}| <= 2^(j/2) (j+1)^k`
4. For `j/2 < i < j`, `E(B i, B j) <= |B i| |B j| + 2^(j/2) (j+1)^k`.
This remains equivalent to the open $1000 Erdos 1191(ii) problem (which implies open $500 Erdos 39; best known infinite Sidon set is Ruzsa `x^(sqrt 2 - 1 + o(1))`).

Dead ends / mathematical obstructions (beyond prior handover):
- Arbitrary forbidden difference set `F` of density `delta = (log M)^(-C)` at every scale: `F = qZ` (`q ~ 1/delta`) forces `|Delta^+(B) cap F| >= M / polylog(M) >> sqrt(M) polylog(M)` by pigeonhole.
- Random forbidden set `F` of density `delta = (log M)^(-C)`: Chernoff gives `P(|Delta^+(B) cap F| <= delta m^2 / 2) = exp(-Omega(M / polylog M))`, crushing `(M choose m) = exp(O(sqrt(M) log M))`. Thus independent/uncorrelated scale constructions provably fail; scales must share correlated algebraic/spectral structure so `g_i` and `g_j` cancel their zero-frequency peaks in Parseval.

## STEER (2026-11-27 10:51 CT, Thiago)

Contestant @anmolspace posted a complete proof of child `Erdos1191.erdos_1191.parts.ii.R2.H2` (the additive coding step, E(a) ≤ 2^j (j+2)^16) on our reduction PR #7467; a dedicated PR is still to come. H2 is TAKEN. Do not spend a leg on H2 and do not copy their source.

H1, the finite Sidon packing statement in our R2 reduction, remains open. Remaining work on parts.ii — including the next legs of this run — should target R2.H1 only: dense Sidon sets in dyadic blocks with the stated cardinality and cross-scale difference condition. The standalone child id `Erdos1191.erdos_1191.parts.ii.R2.H1` is queued at high priority ($1000 parent).

Related hint only: Nicholas Wierenga’s #3944 proves a related encoding on a *different* reduction (R1.H2, exponent 30) and likewise leaves finite packing as the open step. Do not copy that file.

Our R2 module is OWN (merged PR #7467). H2 lemmas from other contestants are not ours to paste.


## Leg 2: codex  (11:04, 15 min, ended: exit)
File stats: proved lemmas 96, sorries 1, lines 3370 (was 70 / 1 / 2262)
Approach: reduce to cardinalities of sumsets. A self-sumset deficit bounds the number of repeated unordered representations; remove collisions by taking an independent set in their graph. A mixed-sumset deficit bounds the number of repeated mixed representations. Partition each block into equal-sized bins. Independently choosing one bin per block gives a finite weighted average of cross conflicts bounded by a telescoping series. Delete later endpoints of the retained conflict edges, losing at most half of each chosen bin.

Compiled: all inherited lemmas retained. Key new lemmas are sidon_subset_of_small_additiveEnergy, additiveEnergy_of_dyadicEnergyBounds, crossDifferenceMatches_le_of_no_heavy, trim_heavyMixedPairs, dyadicEnergyBounds_of_mixedMoment, card_two_choice_fiber, balanced_finset_choices, exists_choices_le_weighted_edges, dyadicBlocks_avoiding_repeatPairs, dyadicEnergyBounds_of_repeatPairs, repeatedArguments_card_le, sidon_subset_of_self_sumset, repeatPairs_of_sumsetBounds, self_sumset_full, mixed_sumset_full, sumsetBounds_of_nearby, nearby_iff_sumsetBounds. Lean elaborates the new reduction with the sole placeholder. Audited nearby_iff_sumsetBounds, sumsetBounds_of_nearby, and dyadicEnergyBounds_of_repeatPairs use only propext, Classical.choice, and Quot.sound.

Exact gap: hpacking : DyadicSumsetBounds. Fix d,k,J independent of the finite horizon. Construct B_j in [0, 2^j) for J ≤ j ≤ N with M_j²(j+1)^(2(d+1)) ≥ 2^j. The self-sumset deficit M_j(M_j+1)/2 − |B_j + B_j| must be at most M_j(j+1)^k. For j/2 < i < j, the mixed deficit M_i M_j − |B_i + B_j| must be at most 2^floor(j/2)(j+1)^k. nearby_iff_sumsetBounds proves this is equivalent to the original nearby-difference packing condition. A uniform family meeting these deficits remains unconstructed.

Dead ends: prior handover records uncorrelated blocks and arithmetic tags. A reversed truncated polynomial square can distinguish scales in a carry-free model when the sum of the input parameters is a unit, but same-scale differences lose high coefficient information for parameter pairs with a long common low-digit prefix. Those pairs create too many internal collisions. Independent dense blocks give mixed deficits on the order of 2^i up to polynomial factors, too large once i is substantially above j/2.

CI verdict: rejected at lint for the sole remaining placeholder in OMA.solution.

## Leg 2: codex  (11:17, 11 min, ended: exit)
File stats: proved lemmas 108, sorries 1, lines 3778 (was 96 / 1 / 3370)
Approach: work on R2.H1 at adaptive checkpoints. A dense Sidon parent can supply many nearby blocks by partitioning into disjoint bins and localizing each bin to an interval of the child's length. Sibling differences are disjoint by Sidon uniqueness. The older weighted deletion argument now works on an arbitrary finite set of parent indices, so parents can start with small sumset deficits.

Compiled: dyadicBlocks_on_support_avoiding_repeatPairs (the old dyadicBlocks_avoiding_repeatPairs remains as its interval specialization), localize_finset, positiveDifferences_subset, disjoint_positiveDifferences_of_subsets, eventually_dyadic_card_ge_twice_index, sparse_of_checkpoint_dyadic_sidon, checkpoint_dyadic_sidon_of_nearby, nearby_iff_checkpoint_dyadic_sidon, eventually_checkpoint_index_close, checkpoint_dyadic_sidon_of_checkpoint_sumset_bounds, checkpoint_sumset_bounds_of_nearby, nearby_iff_checkpoint_sumset_bounds. The final equivalence uses only propext, Classical.choice, and Quot.sound. The whole file elaborates with one placeholder. The prescribed checker rejected at lint for that placeholder.

Exact gap: hpacking : CheckpointDyadicSumsetBounds. With fixed d,e,k,J, for every horizon N choose a finite set of parent indices P such that every j in [J,N] has s in P with j ≤ s and 2^(s-j) ≤ (j+1)^e. Choose B_s inside [2^s,2^(s+1)) with M_s²(s+1)^(2(d+1)) ≥ 2^s. Require self-sumset deficit ≤ M_s(s+1)^k and mixed-sumset deficit ≤ 2^floor(s/2)(s+1)^k for parents s/2 < r < s. No uniform construction of these parents was obtained.

Dead ends: see inherited notes for independent blocks, arithmetic/residue tags, subspaces, and truncated polynomial squares. A fixed large coefficient field with O(log j) carry-guarded digits has a degree step of order j/log j, beyond the O(log j) checkpoint gap. Coarsening a modular representative cut changes a difference d in a parent of length L with probability only d/L, which gives too little suppression for comparisons against much smaller blocks.
