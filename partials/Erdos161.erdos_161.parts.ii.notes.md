# Relay notes for Erdos161.erdos_161.parts.ii (prize: $500)


## Leg 1: opus  (08:16, 1 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_opus: Erdos161.erdos_161.parts.ii (leg 1, opus)
Approach: none viable. Faithful Lean version of an open question (t>=4 densities give same order).
State of the reduction tree (all no-sorry files under relay/.../related_files):
- R1 (merged): target <= H1 (t=3, CFS11 sqrt log lower bound) + H2 (t>=4, (log n)^{1/(t-1)} lower bound for every alpha>0).
- R1.H1: open PR #3187 (1208 lines, no sorry) -> t=3 case essentially done.
- R1.H2.R1 (merged): H2 <= H1 (hypergraph Ramsey, merged proof) + H2 (hypergraph Nikiforov for cliques, t>=4:
  delta C(n,d) d-cliques => K_d^t(s) blowup with s >= c (log n)^{1/(t-1)}). This Nikiforov-type statement is the open core.
Compiled: nothing new (file still the trivial sorry skeleton; no lemma worth keeping).
Exact remaining gap: R1.H2.R1.H2 (hypergraph Nikiforov blowup, t>=4) = research-level open.
Dead ends: no loophole in the statement (Theta over atTop, alpha,beta in (0,1/2), t>=3 is faithful).
RESULT: FAILED fast pass.

## Leg 2: codex  (08:22, 5 min, ended: exit)
File stats: proved lemmas 6, sorries 1, lines 88 (was 0 / 1 / 10)
# Codex relay notes

Approach: monotonicity lets reciprocal endpoint densities bracket any two densities in (0, 1/2). This gives a direct route if a higher-to-lower density transfer can be proved without the stronger Nikiforov bound.
Compiled in the target: `threshold_feasible`, `threshold_le_of_feasible`, `threshold_mono_density`, `threshold_mono_vertices`, `threshold_bigO_of_density_le`, `theta_of_reciprocal_comparisons`, and the `k = 0` branch. A direct Lean run finished with the single `sorry` warning. The prescribed CI checker returned `rejected`, reason `lint: forbidden: 'sorry'`.
Exact gap: for `3 ≤ t` and every positive `k`, prove `threshold t (1 / 2 - endpointGap k) =O[atTop] threshold t (endpointGap k)`, where `endpointGap k = 1 / (k + 4)`. The common-scale route still needs the CFS t = 3 lower bound integrated and the open matching lower bound for t ≥ 4.
Dead ends: independent random recoloring improves expected density but its union bound requires the same log-scale size as a fresh random coloring. A single complete t-partite box of equal part size s only forces a small bias via inclusion–exclusion: the centered transversal count has magnitude s^t/2, bounded by 2^t times the maximum induced count deviation over unions of parts. This can address densities near 1/2 given the box estimate, but gives no comparison at densities tending to 0.

## Leg 1: opus  (09:35, 0 min, ended: exit)
File stats: proved lemmas 6, sorries 1, lines 88 (was 6 / 1 / 88)
# notes_opus: Erdos161.erdos_161.parts.ii (relay leg 1, opus, second pass)
Approach: none viable. This is a faithful Lean version of an open $500 Erdos question (for t>=4, do all fixed densities give the same order of growth?).
Compiled: kept codex's lemmas unchanged (threshold_feasible, threshold_le_of_feasible, threshold_mono_density,
threshold_mono_vertices, threshold_bigO_of_density_le, theta_of_reciprocal_comparisons, k=0 branch). One sorry is left.
Exact remaining gap: for 3<=t and k>0, threshold t (1/2 - endpointGap k) =O threshold t (endpointGap k).
That needs the CFS11 t=3 bound plus the open hypergraph Nikiforov blowup for t>=4 (R1.H2.R1.H2).
Dead ends: no loophole in the statement; random recoloring and single-box bias give nothing at densities tending to 0 (see codex notes).
RESULT: STALLED (open research core)

## Leg 2: codex  (09:47, 11 min, ended: exit)
File stats: proved lemmas 19, sorries 1, lines 636 (was 6 / 1 / 88)
## Codex relay leg 2

Approach: a monochromatic complete t-partite box forces a discrepancy on one of the unions of its parts. Inclusion–exclusion isolates the transversal sum, while the product of the part sizes bounds its magnitude below. The finite box proof counts incidences with rich fibers and iterates the common-fiber estimate across the first t−1 coordinates.

New compiled lemmas in the target:
- `sum_transversals`, `abs_sum_transversals_le`, `card_transversals_ge`, `threshold_gt_of_monochromatic_transversals`.
- `exists_large_common_fiber`, `card_relation_eq_sum_fibers`, `exists_cartesian_box_of_density`, `exists_monochromatic_transversals`. The last gives side size s when `(d + 1) * (s * 32 ^ ((s + 1) ^ d)) ≤ n`, with t = d + 1.
- `threshold_pos_of_pos_uniformity`, `log_le_threshold_pow_near_half`, `logScale_bigO_threshold_near_half`, `exists_density_with_logScale_lower`, `reciprocal_comparisons_iff_lower_logScale`. Thus near-half densities have the matching log-scale lower bound. For each t, the reverse implication from the desired comparisons to the log-scale lower bound at all positive densities is unconditional. The other implication takes the random-coloring upper bound as a hypothesis.

Exact gap: the original single sorry remains in the succ branch. For `3 ≤ t` and every `k > 0`, prove `threshold t (1 / 2 - endpointGap k) =O[atTop] threshold t (endpointGap k)`. With the random upper estimate from R1, the equivalent missing mathematical claim is `logScale (t - 1) =O[atTop] threshold t ρ` for every `0 < ρ < 1/2`. The t = 3 CFS result from the related PR is still unintegrated. The matching lower bound at arbitrary positive density for t ≥ 4 remains open.

Dead ends: a single box only gives the fixed near-half density window, and enlarging to an arbitrary number of parts by applying the general box lemma to the clique relation loses the exponent. Random recoloring did not give a direct transfer in earlier legs. A fixed density pivot by itself only repackages the required transfer.

Verification: direct Lean elaboration succeeded with only the single sorry warning. The two main new results, `logScale_bigO_threshold_near_half` and `reciprocal_comparisons_iff_lower_logScale`, depend only on propext, Classical.choice, and Quot.sound. The prescribed checker returned rejected with reason `lint: forbidden: 'sorry'`.
