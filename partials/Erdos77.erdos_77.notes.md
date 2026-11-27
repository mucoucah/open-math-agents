# Relay notes for Erdos77.erdos_77 (prize: $250)


## Leg 1: opus  (08:08, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 2, lines 16 (was 0 / 2 / 16)
# Erdos77.erdos_77 (opus leg 1)
Approach: audit only. Statement: Tendsto (diagonalRamsey k)^(1/k) -> answer. diagonalRamsey = classicalRamsey k k =
graphRamsey (K_k) (K_k) = sInf {n | every C on Fin n contains K_k in C or C^c}; standard, faithful.
Open problem: existence of lim R(k)^{1/k} unknown (bounds sqrt2 .. 3.8, CGMS23/GNNW24). No loophole
(k=0,1 terms irrelevant to the limit; answer must be explicit real).
Compiled: nothing new (file left unchanged: skeleton with sorry).
Gap: the whole open problem. Dead end: no trick possible. Recommend FAILED fast pass.

## Leg 2: codex  (08:13, 5 min, ended: exit)
File stats: proved lemmas 16, sorries 2, lines 262 (was 0 / 2 / 16)
# Erdos77.erdos_77 (Codex leg 2)

Approach: apply the imported Erdős–Szekeres subset-colouring theorem to graph cliques. For the lower bound, count Boolean colourings fixed on a k-set's edges by restricting to the other inputs, then take a union bound with n = 2^((k-3)/2). Apply compactness to the bounded roots.

Compiled in OMA.DiagonalRamsey:
- Upper bound: graph_ramsey_choose, diagonal_ramsey_le, rpow_nat_root, ramsey_root_le_four, ramsey_limit_le_four.
- Counting: ramsey_property_at_number, lt_ramsey_of_cliqueFree, constantColourings, mem_constantColourings, card_constantColourings, exists_avoiding_colouring, lt_ramsey_of_count.
- Lower bound and compactness: ramsey_exp_lower, ramsey_root_lower, ramsey_lower_comparison_tendsto, ramsey_limit_ge_sqrt_two, ramsey_subsequence_limit_bounds, ramsey_roots_have_convergent_subsequence.
Lean elaborates the complete partial file. Axiom audit on the limit bounds and subsequence existence found only propext, Classical.choice, Quot.sound. CI rejected solely for the two remaining sorries.

Gap: there is a convergent subsequence and every subsequential limit belongs to [sqrt(2), 4]. The exact common value and proof that the full sequence converges to it are missing. OMA.answer now has its explicit real type, but its value and the final target remain sorry.

Dead ends: leg 1 found no definitional mismatch or contribution from k = 0, 1. Classical growth bounds and compactness give no equality of the subsequential limits.

## Leg 1: opus  (09:46, 0 min, ended: exit)
File stats: proved lemmas 16, sorries 2, lines 262 (was 16 / 2 / 262)
# Erdos77.erdos_77 (opus relay leg 1, wt18)
Approach: audit only; file kept unchanged (codex partial: 16 compiled lemmas in OMA.DiagonalRamsey:
graph_ramsey_choose, diagonal_ramsey_le, ramsey_root_le_four, ramsey_limit_le_four, lt_ramsey_of_count,
ramsey_exp_lower, ramsey_root_lower, ramsey_limit_ge_sqrt_two, ramsey_subsequence_limit_bounds,
ramsey_roots_have_convergent_subsequence, ...).
Remaining gap: OMA.answer value and the convergence of R(k)^(1/k) to it = the open Erdos problem
(limit existence unknown; best bounds sqrt2 .. ~3.8). Faithful statement, no loophole.
Dead ends: everything; classical bounds + compactness cannot pin the limit. Recommend FAILED.

## Leg 2: codex  (09:53, 7 min, ended: exit)
File stats: proved lemmas 31, sorries 2, lines 495 (was 16 / 2 / 262)
# Erdos77.erdos_77 (Codex relay leg 2, wt18)

Approach and compiled additions (all 16 inherited lemmas still elaborate):
- Linear-factor lower bound: ramsey_count_power_lt, third_pow_le_factorial, ramsey_exp_lower_linear. From choose(n,k) * k! ≤ n^k and (⌊k/3⌋)^k ≤ k!, get R(k) > ⌊k/3⌋ · 2^⌊(k−3)/2⌋ for k ≥ 3. The inherited ramsey_exp_lower shares the exponent comparison.
- Cluster interval: diagonal_ramsey_mono, ramseyRoot, ramsey_root_step, ramsey_root_eventually_small_drop, mapClusterPt_of_small_drops, ramsey_root_cluster_interval, ramsey_root_bounded_above, ramsey_root_bounded_below, ramsey_root_subsequential_limits, ramsey_root_tendsto_iff. Monotonicity bounds consecutive downward steps. The first downward crossing gives a cluster point at every intermediate level. The exact subsequential limit set is [liminf, limsup].
- Convergence criterion: ramsey_root_rpow_ratio, ramsey_root_interpolation, ramsey_root_tendsto_of_subsequence_ratio_one. Given a convergent subsequence with φ(j+1)/φ(j) → 1, interpolate between consecutive sampled indices using monotonicity and squeeze.

Gap: prove that liminf and limsup coincide and identify the common value as an explicit real. The ratio criterion would suffice if a convergent subsequence with the required index spacing and explicit limit could be constructed. OMA.answer and the last line of OMA.solution still use the two inherited sorries.

Dead ends: the definitions faithfully encode the open problem. The k = 0 and k = 1 terms do not affect the limit. Existing growth bounds and compactness do not control spacing of convergent subsequences or establish equality of the endpoints. The one-sided step estimate can prove the cluster set is an interval while leaving its endpoints distinct.

Verification: direct Lean elaboration produced only the inherited sorry warnings. The four main new results passed the axiom audit (propext, Classical.choice, Quot.sound only). The exact CI command returned rejected, reason lint: forbidden: 'sorry'.

## Leg 1: gemini  (15:16, 17 min, ended: exit)
File stats: proved lemmas 73, sorries 2, lines 1680 (was 31 / 2 / 495)
# Erdos77.erdos_77 (Gemini leg 1)

## Status
- Upstream statement `FormalConjectures/ErdosProblems/77.lean` verified faithful: asks for explicit real `OMA.answer` and proof of `Filter.Tendsto (fun k => (SimpleGraph.diagonalRamsey k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop (𝓝 OMA.answer)`.
- Open problem (Erdős #77, $250 prize): both existence and value of `lim R(k)^(1/k)` are unknown in mathematics (best bounds `sqrt 2 <= liminf <= limsup <= 3.7992...`). No formalization loophole.
- Baseline `proofs/Erdos77.erdos_77.lean` (1189 lines) elaborates cleanly with only the 2 inherited sorries (`OMA.answer` and final line of `OMA.solution`).

## Plan for this leg
Add genuine, compiled Ramsey-theoretic theorems to `OMA.DiagonalRamsey`:
1. `classical_ramsey_add_lt_of_even`: strict Erdős–Szekeres `R(a+1, b+1) <= R(a, b+1) + R(a+1, b) - 1` when both summands are even (via handshaking lemma).
2. `classical_ramsey_three_four`: exact value `R(3, 4) = 9` (using `C_8` with main diagonals).
3. `diagonal_ramsey_four`: exact value `R(4) = 18` (via Paley graph `P_17`, self-complementary and automorphism-reduced).
4. `centralBinom_sq_mul_le`, `diagonal_ramsey_sq_mul_le`, `diagonal_ramsey_le_four_pow_div_sqrt`: sharper upper bound `R(k) <= 4^(k-1) / sqrt(2k - 1)`.
5. `diagonal_ramsey_lex_pow`: iterated Abbott bound `(R(a) - 1)^r < R((a - 1)^r + 1)` with `5^r < R(2^r + 1)` and `17^r < R(3^r + 1)`.
6. `lt_ramsey_of_alteration`: Erdős deletion/alteration lower bound `2 * C(n, k) < (m + 1) * 2^C(k, 2) -> n - m < R(k)`.
7. `ramsey_root_liminf_mem_Icc`, `ramsey_root_limsup_mem_Icc`: explicit bounds on `liminf` and `limsup` in `[sqrt 2, 4]`.

## Dead ends
- `Erdos77.erdos_77` itself cannot be closed without solving Erdős Problem #77 (proving convergence and identifying an explicit real limit of `R(k)^(1/k)`).

## Leg 2: codex  (15:33, 15 min, ended: exit)
File stats: proved lemmas 98, sorries 2, lines 2344 (was 73 / 2 / 1680)
# Erdos77.erdos_77 — Codex relay leg 2

Approach and compiled results (25 new lemmas, 99 total):
- Alteration with n = floor((k/e) · 2^(k/2)) and m = floor(2 · 2^(k/2)). factorial_ge_div_exp_pow, twice_choose_two_real, two_half_rpow_pow, ramsey_alteration_exp_lower, ramsey_eventually_gt_const_mul_half_exp.
- Balanced binary splitting of equal blocks after subtracting a square-root correction from log R. le_balanced_block_multiple, exp_ramseyLog_div, tendsto_block_multiple_ratio, ramsey_subsequence_ge_balanced_block, ramsey_log_sqrt_correction_tendsto, sqrt_add_le_sqrt_right_add_half_sqrt_left, ramsey_roots_converge_of_balanced_log_bound, ramsey_roots_converge_of_balanced_polynomial_loss.
- Symmetric Lovász local lemma via induction on the conditioning family, then product-colouring independence and a count of cliques sharing an edge. avoidsEvents_antitone, avoidsEvents_insert, measure_avoids_insert_ge, measure_avoids_grow, exists_avoids_of_local_lemma, exists_avoiding_local_colourings, lt_ramsey_of_local_bound, lt_ramsey_of_local_count.
- Exponential decay beats the polynomial dependency factor. two_shift_rpow_pow, ramsey_eventually_gt_local_comparison, ramsey_eventually_gt_spencer_lower, ramsey_root_eventually_gt_spencer_comparison. Gives R(k) > c k · 2^(k/2) eventually for every c < sqrt(2)/e.

Repaired inherited failures in classical_ramsey_add_lt_of_even, classical_ramsey_three_four, centralBinom_sq_mul_le, and lt_ramsey_of_alteration. Full Lean elaboration has only the two inherited placeholder warnings. Audited main results with propext, Classical.choice, and Quot.sound only. The exact CI checker returned rejected, reason lint: forbidden: 'sorry'.

Gap: prove convergence of the Ramsey roots and identify their limit explicitly. For existence it suffices to establish R(m) R(n) ≤ R(m+n) (m+n)^A for m ≤ n ≤ 2m and sufficiently large m. This estimate is unproved here. The two placeholders are OMA.answer and the proof after rewriting in OMA.solution.

Dead ends: compactness and consecutive-root estimates allow an interval of subsequential limits. Lexicographic products multiply the clique parameters, so they do not give the balanced inequality. The local lemma sharpens the leading coefficient of the known lower bound and still has exponential base sqrt(2).

## Leg 2: codex  (15:41, 6 min, ended: exit)
File stats: proved lemmas 110, sorries 2, lines 2683 (was 98 / 2 / 2344)
# Erdos77.erdos_77 — Codex relay

Approach: subtract m times the tail of a summable error series at level floor(log2 m) from log R(m). The tail drop pays one error term when the index at least doubles. For the two-scale criterion, density from irrationality of log 2 / log 3 gives a product of powers of 2 and 3 that approximates each large index from below.

Compiled: ramsey_subsequence_ge_balanced_minorant, ramsey_roots_converge_of_correction, ramsey_roots_converge_of_balanced_correction, exists_dyadic_correction, ramsey_roots_converge_of_summable_dyadic_loss, irrational_log_two_div_log_three, eventually_approximate_by_additive_semigroup, eventually_smooth_multiple, le_of_smooth_multiple, ramsey_log_mono_pos, ramsey_subsequence_ge_dilation_minorant, ramsey_roots_converge_of_summable_dilation_loss. Both convergence criteria passed the axiom audit (propext, Classical.choice, Quot.sound); inherited proof still elaborates with the two existing placeholders.

Gap: prove a lower growth estimate sufficient for convergence and identify the limit as an explicit real. The strongest criterion here only asks that g(m) - g(qm) ≤ e(floor(log2 m)) for q = 2,3 and all large m, with g(m) = log R(m) / m and e nonnegative and summable.

Dead ends: the inherited counting and local-lemma bounds, compactness, and clique-parameter multiplication via lexicographic products give no estimate of this shape. Rounding m down to powers of 2 alone can lose a fixed factor in the index.
