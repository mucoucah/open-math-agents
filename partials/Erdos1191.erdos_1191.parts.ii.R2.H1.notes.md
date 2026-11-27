# Relay notes for Erdos1191.erdos_1191.parts.ii.R2.H1 (prize: )


## Leg 2: codex  (11:36, 17 min, ended: exit)
File stats: proved lemmas 33, sorries 1, lines 991 (was 0 / 1 / 9)
Approach
- Use one finite Sidon host with dense clusters at arbitrary locations. Hall allocation with weights 1/((j+1)(j+2)) yields disjoint subclusters, then translations give the required blocks.
- Conversely prune distant differences and assemble blocks using translation tags that recover the pair of block indices. The resulting host has diameter O(2^N (N+1)^3), so Bertrand embeds it in a prime cycle. Splitting wrapped arcs and localizing larger arcs permits adaptive widths.
- Explicit quadratic-residue rulers realize terminal logarithmic windows. Their minimum gap allows independent rulers at anchors m < n with m ≤ n/2 - 2 to coexist in one host.

Compiled
- Allocation and assembly: disjoint_cluster_allocation, cluster_packing_on_scales, translated_host_of_separated_blocks, bounded_sidon_cluster_profile_of_nearby.
- Equivalences: nearby_iff_sidon_cluster_profile, nearby_iff_prime_cyclic_sidon_profile, nearby_iff_adaptive_cyclic_sidon_profile.
- Explicit cases: quadratic_residue_sidon_with_gap, exists_dense_sidon_range_with_gap, nearby_packing_top_window, nearby_packing_separated_windows.
- Direct Lean compile succeeds with the final placeholder warning. The adaptive equivalence and both restricted packing theorems audit to propext, Classical.choice, Quot.sound. The prescribed checker rejects solely for the remaining placeholder.

Exact gap
- Prove AdaptiveCyclicSidonProfile at line 622. Fix d,e,J. For every N choose a single prime q and Sidon subset S modulo q. For every J ≤ j ≤ N, find an exponent s ≥ j with 2^(s-j) ≤ (j+1)^e and 2^s ≤ q, and an arc of length 2^s in the cycle containing at least 2^(s/2)/(s+1)^(d+1) points. Arc positions may vary. The restricted construction does not cover the intervals of exponents between its separated windows.

Dead ends
- Inherited: independent random thinning, small prime multipliers, uniform finite witnesses at early scales, distinct subspace slopes.
- A fixed power-series square truncation loses v digits at input differences of valuation v. Products of Sidon graphs permit independent swaps in different coordinates. A perfect difference set in a cycle is too uniform: double-counting translated windows gives a maximum cluster bound O(L/sqrt(q) + q^(1/4)), inadequate for L = q^alpha with 1/2 < alpha < 1. This last observation is informal guidance.

## Leg 1: gemini  (11:59, 10 min, ended: no_progress_10m)
File stats: proved lemmas 33, sorries 1, lines 991 (was 33 / 1 / 991)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (12:25, 20 min, ended: no_progress_10m)
File stats: proved lemmas 38, sorries 1, lines 1307 (was 33 / 1 / 991)
Approach
- Retain the common Sidon host and adaptive cyclic profile equivalences. Use Boolean prefix compactness on pruned witnesses to get a single infinite family. For approximate witnesses, discard high-degree vertices and choose a maximal independent subset in each ruler's graph of earlier difference conflicts.

Compiled this leg
- nearby_iff_infinite_separated_packing is in the proof file. Direct Lean compiled with only the final placeholder; CI rejected solely for that placeholder.
- thin_avoiding_pairs, nearbyDifferenceConflicts_card, and nearby_iff_polynomial_conflict_budget are in the proof file. Direct Lean compiled with only the final placeholder.

Exact remaining gap
- Obtain polynomially dense dyadic rulers at every required scale. The conflict formulation permits, for each j, at most card(B j) times a fixed polynomial in j for the number of distinct positive differences shared with earlier nearby rulers. Separated logarithmic windows still leave uncovered exponents.

Dead ends
- Inherited: random thinning of independent nearby rulers, small prime multipliers, independent digit products (pair swaps), fixed truncated power-series square (valuation loses information), distinct subspace slopes, and the uniformity of perfect difference sets.

## Leg 1: gemini  (12:56, 10 min, ended: no_progress_10m)
File stats: proved lemmas 38, sorries 1, lines 1307 (was 38 / 1 / 1307)
# Gemini Leg 1 Notes for Erdos1191.erdos_1191.parts.ii.R2.H1

## Mathematical Diagnosis
- `H1` is **mathematically equivalent** to the open $1000 Erdős Problem 1191(ii) (existence of an infinite Sidon set `A` with `|A ∩ [1, x]| >> sqrt(x) / (log x)^c`):
  - `H1 → 1191(ii)` is formally proved by `R2.main` + merged `H2` (PR #9061).
  - `1191(ii) → SidonClusterProfile → H1`: taking `S = A ∩ [1, 2^N]` and `t = 0` at every scale satisfies `SidonClusterProfile`, which implies `H1` via `nearby_of_sidon_cluster_profile`.
- The best known exponent for infinite Sidon sets in the literature is Ruzsa (1998) / Cilleruelo (2014): `N^(sqrt(2)-1 + o(1)) ≈ N^0.414`.
- Even the **two-scale specialization** (`m = 3n/4` and `n`: find Sidon `B_1 ⊆ [0, 2^m)` of size `2^(m/2)/n^d` and `B_2 ⊆ [0, 2^n)` of size `2^(n/2)/n^d` with disjoint positive differences) exhibits the full obstruction:
  - By Cauchy-Schwarz over `2^(n-m)` intervals of length `2^m`, `D_2 = (B_2 - B_2)^+ ∩ [1, 2^m)` has size `>= 2^m / (4 n^(2d))` (positive polylog density in `[1, 2^m)`), as does `D_1 = (B_1 - B_1)^+`.
  - No pseudorandom `D_2` of density `δ = 1/poly(n)` can be avoided by a Sidon set `B_1` of size `> (2 log L)/δ` (first-moment / random graph clique bound).
  - No subgroup `qℤ` or Bohr-set partition separates `D_1` and `D_2`: pigeonhole forces the avoiding set to have size `<= index` (or `<= 1/volume`), while the contained set's density requires `index <= poly(n)`.
  - No dense Sidon host `S ⊆ [0, M)` of size `~ sqrt(M)` works: window variance forces `|S ∩ [t, t+L)| <= 2L/sqrt(M) + O(M^(1/4))`, which is `o(sqrt(L))` for `L = M^(3/4)` (and rules out all subsets of Singer / Bose-Chowla / Erdős-Turán sets of diameter `2^N`).
  - Single-multiplier Ruzsa `⌊M α log p⌋` embeddings fail at scale `2^m` (`m < n`) because fitting `2^(m/2)` primes forces `Y_m ≈ M 2^(-m/2)`, where the curvature `M Δ_m^2 / Y_m^2 = 2^(2m - n)` limits `|B_m|` to `2^(m - n/2) << 2^(m/2)`.
  - Base-`Q` / finite-field slice constructions (`(y, y^2) ∈ F_{q^4}^2`) with `q^2` differences per slice either exhaust `F_q^6` completely or lose polynomial powers of `Q` when buffer-zoned.

## Current Approach
- Keep all 38 compiled lemmas in `proofs/Erdos1191.erdos_1191.parts.ii.R2.H1.lean`.
- Tighten the conflict-window equivalence from `j / 3 < i < j` to `j / 2 + O(log j) < i < j` (specifically `2 ^ j * (j + 1) ^ (2 * k) < (2 ^ i) ^ 2` and `i < j`) using `thin_avoiding_pairs` on short differences of a Sidon set: since any Sidon set `B j` has at most `Δ` pairs with difference `< Δ`, taking `Δ = 2 ^ (j / 2) * (j + 1) ^ k ≤ |B j| * (j + 1) ^ (d + 1 + k)` removes all differences below `2 ^ (j / 2) * (j + 1) ^ k` at only a polynomial density loss.
- Also formalize the clean half-scale separation equivalence (`j / 2 < i < j`) and general separated-anchor packing (for anchors with `2 ^ m ≤ 2 ^ (n / 2) * (n + 1) ^ k`, improving `m ≤ n / 2 - 2` without relying on special minimum-gap rulers).

## Compiled Lemma Names (existing)
- Allocation/assembly: `reciprocal_weight_sum_le`, `disjoint_cluster_allocation`, `dyadic_energy_count_transfer`, `eventually_large_dyadic_counts`, `cluster_packing_on_scales`, `translated_host_of_separated_blocks`, `bounded_sidon_cluster_profile_of_nearby`
- Equivalences: `nearby_iff_sidon_cluster_profile`, `nearby_iff_prime_cyclic_sidon_profile`, `nearby_iff_adaptive_cyclic_sidon_profile`, `nearby_iff_infinite_separated_packing`, `nearby_iff_polynomial_conflict_budget`
- Explicit/restricted: `quadratic_residue_sidon_with_gap`, `exists_dense_sidon_range_with_gap`, `sidon_cluster_profile_top_window`, `nearby_packing_top_window`, `sidon_cluster_profile_separated_windows`, `nearby_packing_separated_windows`
- Thinning: `thin_avoiding_pairs`, `nearbyDifferenceConflicts_card`

## Exact Remaining Gap
- Construct polynomially dense dyadic Sidon sets `B j ⊆ [2^j, 2^(j+1))` avoiding positive-difference conflicts from earlier scales in `(j / 2 + O(log j), j)` (or equivalently prove `SidonClusterProfile` / `AdaptiveCyclicSidonProfile` / `H1`).

## Dead Ends
- Inherited: independent random thinning, small prime multipliers, uniform finite witnesses at early scales, distinct subspace slopes, fixed truncated power-series square, digit products (pair swaps), perfect difference sets.
- New: two-scale (`3n/4`, `n`) separation via congruence/Bohr partitions, Erdős-Turán with stretched spacing `M = C p`, buffer-zoned `F_q` slices, single-multiplier `⌊M α log p⌋` (curvature collapses to `2^(2m-n)`), subsets of Singer/Bose-Chowla sets (variance bound `2L/sqrt(M) + O(M^(1/4))`).

## Leg 2: codex  (13:24, 19 min, ended: exit)
File stats: proved lemmas 59, sorries 1, lines 2412 (was 38 / 1 / 1307)
Approach
- Count all short predecessor differences with one cutoff range. For wider predecessors use the overlap budget or the deficit in distinct mixed sums. At most twice that deficit many representations lie in ambiguous fibers. Select blocks in increasing order, controlling outgoing ambiguous degrees with reciprocal weights so cumulative exclusions are at most one quarter. The same deficit count on ordered pairs permits thinning a single approximate ruler.
- Greedy Sidon extensions give cubic density at every scale. Dyadically dilating smaller quadratic rulers gives square-root density up to polynomial loss on logarithmic windows whose anchors satisfy 2^m ≤ 2^(n/2)(n+1)^k.

Compiled this leg
- nearby_conflict_budget_of_wide_overlaps, dyadic_half_power_le_weighted_card, nearby_iff_wide_overlap_budget.
- exists_sidon_insert_of_card_lt, exists_sidon_extension_of_cubic_budget, cubic_sidon_prefix, nearby_packing_cubic_density.
- ambiguousSumPairs_card_add_twice_image, mem_ambiguousMixedPairs_of_collision, ambiguousMixedPairs_card_add_twice_sumset, card_filter_fst_mem, exists_half_bounded_cost, select_blocks_without_bipartite_conflicts, nearby_iff_mixed_sumset_budget.
- exists_dense_ruler_with_polynomial_gap, sidon_cluster_profile_polynomially_separated_windows, nearby_packing_polynomially_separated_windows.
- mem_ambiguousSumPairs_of_collision, sidon_subset_of_ordered_sumset_budget, image_deficit_mono, nearby_iff_approximate_sumset_budgets.
- Direct Lean succeeds with only the final placeholder. All five new headline results audit to propext, Classical.choice, Quot.sound. The prescribed checker rejects at lint for the final placeholder.

Exact gap
- AdaptiveCyclicSidonProfile at line 622 is still unproved: one cyclic Sidon host per horizon must have dense arcs covering every scale within polynomial width slack. Equivalently, construct dense dyadic blocks at every scale with at most card(B_j) times a fixed polynomial in j missing unordered sums within B_j and missing mixed sums between B_i and B_j where j/3<i<j and 2^i>2^(j/2)(j+1)^k.
- Cube-root size falls below the square-root requirement. Stretched anchor windows leave intervening exponents uncovered.

Dead ends
- Inherited attempts are in HANDOVER_NOTES.md. Small-modulus scale tags leave same-residue differences. Tagging every digit spends too many bits or loses square-map information at high valuations.
- Nested prime-power discrete logs align moduli, but product congruence alone only determines products when i ≥ αj/(1−α) for prime size exponent α. Uniform collision heuristics for the intervening range reach α ≤ sqrt(2)−1, below the target.
- Translated reflected subsets of one smaller ruler coalesce within-cluster mixed-sum collisions. With coarse radix tags, Sidonicity also forces pairwise disjoint tag differences across copies of each template point, exhausting the tag difference range and losing density.

## Leg 1: gemini  (15:50, 3 min, ended: exit)
File stats: proved lemmas 59, sorries 1, lines 2412 (was 59 / 1 / 2412)
(the model wrote no notes; see partial_gemini.lean)
