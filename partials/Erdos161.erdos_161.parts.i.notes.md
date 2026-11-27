# notes_opus: Erdos161.erdos_161.parts.i (leg 1, opus)
Approach: none feasible. The target asks for the exact set of pairs (a,b) in [0,1/2)^2 with
balancedColoringThreshold n t a =Theta= ... n t b, for EVERY t>=1.
Expected answer: t=1,2 -> full square (t=1: threshold ~ n for all a; t=2: Theta(log n) for all a,
Ramsey lower + random upper). t>=3: {a=b=0} union {a>0,b>0}. Proving a=0 vs a>0 differ for t=3
needs F(n,0)=o(sqrt log n), i.e. the Erdos-Hajnal tower conjecture r_3(k)>=2^2^{ck} (OPEN);
the a,b>0 part for t>=4 is parts.ii (OPEN). So the value is unknown.
Definition audited (Extremal.lean:105): sInf over m, positive count + a*choose bound, no loophole
(empty set gives sInf=0 only if no m works, but m=n+1 always works vacuously).
Compiled: nothing new. Dead end: no loophole, faithful open problem. RESULT: FAILED fast pass.

## Leg 1: opus  (08:15, 1 min, ended: exit)
File stats: proved lemmas 0, sorries 2, lines 16 (was 0 / 2 / 16)
# notes_opus: Erdos161.erdos_161.parts.i (leg 1, opus)
Approach: none feasible. The target asks for the exact set of pairs (a,b) in [0,1/2)^2 with
balancedColoringThreshold n t a =Theta= ... n t b, for EVERY t>=1.
Expected answer: t=1,2 -> full square (t=1: threshold ~ n for all a; t=2: Theta(log n) for all a,
Ramsey lower + random upper). t>=3: {a=b=0} union {a>0,b>0}. Proving a=0 vs a>0 differ for t=3
needs F(n,0)=o(sqrt log n), i.e. the Erdos-Hajnal tower conjecture r_3(k)>=2^2^{ck} (OPEN);
the a,b>0 part for t>=4 is parts.ii (OPEN). So the value is unknown.
Definition audited (Extremal.lean:105): sInf over m, positive count + a*choose bound, no loophole
(empty set gives sInf=0 only if no m works, but m=n+1 always works vacuously).
Compiled: nothing new. Dead end: no loophole, faithful open problem. RESULT: FAILED fast pass.

## Leg 2: codex  (08:26, 11 min, ended: exit)
File stats: proved lemmas 30, sorries 1, lines 750 (was 0 / 2 / 16)
# Erdos161.erdos_161.parts.i — leg 2 (Codex)

Approach: majority for t=1; graph Ramsey bound plus an exponential average over colorings for t=2. For all t≥2 the average gives O((log n)^(1/(t−1))), using the falling-factorial bound on choose.
Compiled: entire file elaborates with one sorry. Main t=1,2 branches closed by threshold_one_theta and threshold_two_theta. General bounds and reductions: threshold_isBigO_log_rpow, threshold_ge_of_sparse, logScale_isBigO_of_sparse, threshold_anchor_of_logScale_lower, threshold_classes_iff, threshold_zero_le_iff, logScale_not_isBigO_zero_iff.
Exact gap: hclasses for each t≥3. Prove all positive densities Θ-equivalent to 1/4 and prove F(n,t,1/4) is not O(F(n,t,0)). The two-class candidate at t≥3 is conjectural. If the matching positive-density lower bound is available (CFS for t=3, via the sparse-witness lemmas), separation is equivalent to the existence of arbitrarily large n with a two-coloring avoiding monochromatic m-sets for m arbitrarily small relative to (log n)^(1/(t−1)).
Dead ends: no sInf degeneracy. Separation requires arbitrarily small ratios on a subsequence, weaker than little-o or a tower bound at t=3. Direct Bool discrimination avoids simp_all recursion.
Verification: standalone Lean exits 0 with only the hclasses placeholder warning. Axiom audit of the six main helpers reported only propext, Classical.choice, Quot.sound. Final tools/check.sh verdict rejected solely at lint for the one sorry.

## Leg 1: opus  (09:27, 0 min, ended: exit)
File stats: proved lemmas 30, sorries 1, lines 750 (was 30 / 1 / 750)
# notes_opus: Erdos161.erdos_161.parts.i (relay leg 1, opus, wt12)
Approach: none new. The proofs file (750 lines, 30 compiled lemmas, from codex leg 2) proves t=1,2
(threshold_one_theta, threshold_two_theta) and states the answer {t<=2 or (a=0 iff b=0)}.
Remaining gap: ONE sorry hclasses (t>=3). This needs (i) all positive densities Theta-equivalent
(parts.ii, open for t>=4) and (ii) F(n,t,0) separated from F(n,t,1/4) (Erdos-Hajnal tower
conjecture for t=3, open). Faithful statement, definition audited, no loophole.
Dead ends: see memory erdos161-parts-i-dead-ends and earlier notes. File left unchanged.
RESULT: STALLED (open research problem; blocker = hclasses for t>=3).

## Leg 2: codex  (09:40, 13 min, ended: exit)
File stats: proved lemmas 68, sorries 1, lines 1501 (was 30 / 1 / 750)
# Erdos161.erdos_161.parts.i — relay Codex

Approach: retained the t=1,2 cases and the general random-coloring upper bound. Proved finite Ramsey by asymmetric recursion on the two target clique sizes. Used highest differing binary bits to step from arity 3 to 4, then lifted to any t≥4 by coloring each edge from its first four vertices.

Compiled: exists_ramseyBound, avoidMono_iff_lt_diagonalRamsey, logScale_not_isBigO_zero_iff_diagonalRamsey, avoidMono_step_three_four, diagonalRamsey_step_three_four, avoidMono_raise_uniformity, threshold_zero_isBigO_log_log_high, threshold_zero_isLittleO_log_rpow_high, threshold_classes_iff_diagonalRamsey_of_logScale_lower, and threshold_classes_high_of_power_lower. The proof file has 68 private lemmas. Local Lean elaborated it with only the single hclasses warning. The axiom audit of the main additions found propext, Classical.choice, Quot.sound. CI verdict: rejected at lint for the single sorry.

Exact remaining gap: hclasses for t≥3. At t=3, given the matching positive-density lower bounds, the candidate is equivalent to log R₃(m)/m² being unbounded on every tail. At t≥4, F_t(n,0)=O(sqrt(log log n)); any positive-power logarithmic lower bound for F_t(n,1/4) suffices for the jump. That weak positive-density lower bound is still unformalized here, and the comparisons among all positive densities for t≥4 remain open in the file.

Dead ends: no sInf degeneracy. A full tower lower bound or all-n little-o at t=3 would be stronger than the needed Ramsey subsequence. The t≥4 zero-density estimate alone cannot compare two positive densities.

## Leg 1: opus  (10:15, 0 min, ended: exit)
File stats: proved lemmas 68, sorries 1, lines 1501 (was 68 / 1 / 1501)
# notes_opus: Erdos161.erdos_161.parts.i (relay leg 1, opus, wt10)
Approach: none new. Proofs file (1501 lines, 68 compiled lemmas from earlier codex legs) proves t=1,2
and states the answer {t<=2 or (a=0 iff b=0)}.
Remaining gap: ONE sorry hclasses (t>=3). Needs (i) all positive densities Theta-equivalent
(parts.ii, open for t>=4) and (ii) F(n,t,0) not Theta F(n,t,1/4) (Erdos-Hajnal tower conjecture
for t=3, open). Faithful statement, definition audited (Extremal.lean:105), no loophole.
Dead ends: see earlier notes; open research value question. File left unchanged.
RESULT: STALLED (blocker = hclasses for t>=3, open research problem).

## Leg 2: codex  (10:29, 14 min, ended: exit)
File stats: proved lemmas 88, sorries 1, lines 2023 (was 68 / 1 / 1501)
# Erdős 161(i), Codex relay leg

Approach: retain all existing proofs. Ramsey supersaturation gives a dense relation on ordered monochromatic d-cliques. Jensen and independence produce a complete Cartesian product of clique choices, and a union bound removes repeated vertices. Nontransverse t-sets inject into tuples with a collision of part indices. A floor of a constant times (log n)^(1/d) gives the part size.

Compiled in the target: expect_box, expect_precomp, expect_noninjective, exists_injective_box, exists_dense_monoTuple, sparse_of_mono_box, eventually_log_box_size, positive_threshold_log_power, threshold_jump_high. The main proof now uses threshold_jump_high for all t≥4. The only placeholder is hremaining.

Exact remaining gap: compare all positive densities to 1/4 for t≥3, and show F₃(n,1/4) is not O(F₃(n,0)). Given the matching positive-density lower bound at t=3 (CFS), the latter is equivalent to log R₃(m)/m² being unbounded on every tail. Comparison of positive densities at t≥4 remains open here. The dense clique box has exponent 1/d, insufficient for those comparisons.

Dead ends: the weak power bound separates zero only for t≥4. Its exponent can be much smaller than the random-coloring upper exponent. The CFS graph focusing argument at t=3 is a separate direction.

Final verification: the target elaborates with only hremaining's placeholder warning. Axiom audit of exists_dense_monoTuple, sparse_of_mono_box, positive_threshold_log_power, threshold_jump_high, and threshold_zero_isLittleO_positive_high found only propext, Classical.choice, and Quot.sound. The exact CI checker rejected at lint solely for the one sorry. The first import and OMA.solution statement are unchanged.

CFS scratch work: exists_complete_bipartite, exists_constant_pattern, focus_patterns, and graph_density_ge elaborate in erdos161_work.lean. The subtype transport in graph_biclique times out under whnf even at 800000 heartbeats. The following round and round-iteration drafts are in erdos161_round.part and erdos161_rounds.part and are not verified. After transport and round iteration, apply graph Ramsey to the part-index colors and reuse sparse_of_mono_box. This can establish the positive-density comparison at t=3, while the Ramsey growth question at t=3 remains.
Bisected the CFS timeout to the statement and first half of graph_biclique, through applying exists_complete_bipartite to the vertex subtype. The subsequent map/image construction is outside the failing prefix.

## Leg 1: gemini  (10:41, 10 min, ended: no_progress_10m)
File stats: proved lemmas 88, sorries 1, lines 2023 (was 88 / 1 / 2023)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (10:53, 11 min, ended: exit)
File stats: proved lemmas 112, sorries 1, lines 3014 (was 88 / 1 / 2023)
# Erdős 161(i), Codex relay leg

Approach: completed CFS focusing for triples. Enumerate the reserve by Fin S.card, thin earlier blocks to a common color pattern, and extract an injective block with a large common neighborhood. Iterate and apply graph Ramsey to the part colors. The existing collision bound gives sparse subsets at every positive density on the sqrt(log n) scale. For general arity, sample all but one part of a t-part box and extract the final part from its common neighborhood. Inclusion-exclusion on unions of parts converts that box into signed imbalance.

Compiled triple results: exists_complete_bipartite, exists_constant_pattern, focus_patterns, graph_density_ge, graph_biclique, TriplesFocused, focus_triples_round, focus_triples_many, sorted_triple, focused_triples_mono_box, logScale_isBigO_positive_three, threshold_three_positive_theta, threshold_three_jump_iff.

Compiled general results: exists_injective_box_last, eventually_mono_box_on_logScale, imbalance_eq, imbalance_neg, imbalance_of_mono_box, nearHalf_bounds, sparse_nearHalf_of_mono_box, threshold_nearHalf_theta, threshold_positive_anchor_iff_logScale, threshold_theta_near_half_interval, logScale_isBigO_iff_sparse, threshold_positive_anchor_iff_sparse_below_nearHalf. Near-half densities in [1/2 − 1/[4(2t)^t], 1/2) have matching logarithmic bounds for every t≥2.

Exact remaining gap: hremaining. For t≥4 and 0 < α < nearHalf t, prove HasSparseSubsetsAtLogScale t α, meaning every coloring has a subset of size Ω((log n)^(1/(t−1))) where one color has density below α. This condition is equivalent to the high-arity positive thresholds having a common Θ class. For t=3, prove that log R₃(m)/m² is unbounded on every tail, exactly the jump-at-zero claim given the triple estimates.

Dead ends: expectation specialization directly on the vertex subtype timed out. An explicit Fin equivalence resolved it. Thinning each pair of old parts in a putative four-uniform focusing round to a fixed edge pattern can require exponential loss in an arbitrary graph. The t-part box alone gives a fixed deficit from 1/2, and the earlier many-part estimate has a weaker exponent than needed for smaller positive densities.

Verification: standalone Lean elaborates with only hremaining's placeholder warning. Axiom audits on the main additions report only propext, Classical.choice, Quot.sound. The exact checker rejects solely at lint for the single placeholder. The first import and OMA.solution statement are unchanged.

## Leg 1: gemini  (11:08, 13 min, ended: gemini_budget)
File stats: proved lemmas 133, sorries 1, lines 3454 (was 112 / 1 / 3014)
# Erdos161.erdos_161.parts.i — leg 1 (gemini)

Approach:
1. Verified the problem status: `Erdos161.erdos_161.parts.i` is faithfully formalized (no definitional loophole) and genuinely open on both remaining fronts:
   - For `t = 3`, all `a in (0, 1/2)` are `Theta(sqrt(log n))`, so deciding `OMA.answer 3` is equivalent to deciding whether `limsup (log R_3(m)) / m^2 = infinity` (improving the 1952 Erdos-Rado lower bound `R_3(m) >= 2^(c m^2)` vs disproving the $500 Erdos-Hajnal-Rado conjecture `R_3(m) = 2^(2^(Theta(m)))`).
   - For `t >= 4`, deciding whether all `a in (0, 1/2)` share the `logScale t` growth rate is Erdos Problem 161 `parts.ii` ($500 prize, open).
2. Sharpened the proven `Theta((log n)^(1/(t-1)))` near-half interval for every `t >= 2` from `nearHalf t = 1/2 - 1/(4*(2t)^t)` down to the exact inclusion-exclusion optimum on a monochromatic `t`-partite box:
   `sharpNearHalf t = 1/2 - t! / (2 * sum_{k=0}^t C(t,k) k^t)`
   (yielding `1/3` for `t=2`, `4/9` for `t=3`, `41/85` for `t=4`, strictly below `nearHalf t` for all `t >= 2`, and valid right at the endpoint `sharpNearHalf t` via strict `t! * choose m t < m^t`).
3. Proved monotonicity and countable `1/(k+3)` reduction of `HasSparseSubsetsAtLogScale`, and proved the general Erdos-Rado lower bound `c * m^(t-1) <= log(diagonalRamsey t m)` for all `t >= 2` (specializing to `c * m^2 <= log(diagonalRamsey 3 m)`).

Compiled new lemmas (all sorry-free, verified with Lean 4.33.1; 19 new proved lemmas + 2 defs, 3454 lines total, 1 sorry in `hremaining`):
- `descFactorial_le_pow_nat`, `factorial_mul_choose_le_pow`
- `descFactorial_lt_pow_nat`, `factorial_mul_choose_lt_pow`
- `sharpNearHalfDenom`, `sharpNearHalf`, `sum_finset_card_compl_pow`
- `sharpNearHalfDenom_le`, `factorial_lt_sharpNearHalfDenom`
- `sharpNearHalf_bounds`, `sharpNearHalf_lt_nearHalf`
- `sharpNearHalf_two`, `sharpNearHalf_three`, `sharpNearHalf_four`
- `imbalance_sum_mono_box`, `sharp_sparse_of_mono_box`
- `threshold_sharpNearHalf_theta`, `threshold_theta_sharpNearHalf_interval`
- `hasSparseSubsetsAtLogScale_mono`
- `threshold_positive_anchor_iff_sparse_below_sharpNearHalf`
- `threshold_positive_anchor_iff_sparse_inv`
- `exists_pow_le_log_diagonalRamsey`, `exists_sq_le_log_diagonalRamsey_three`

Exact remaining gap (`hremaining` in `OMA.solution`, 1 sorry):
1. For `t >= 4`: `HasSparseSubsetsAtLogScale t a` for `0 < a < sharpNearHalf t` (equivalently for `a = 1/(k+3)` for all `k`).
2. For `t = 3`: `forall C > 0, forall N, exists m >= N, C * m^2 < log (diagonalRamsey 3 m)` (we now have the matching `exists c > 0, eventually c * m^2 <= log (diagonalRamsey 3 m)`).

Dead ends:
- Inclusion-exclusion on part-unions of a single monochromatic `t`-partite box `K^(t)(s,...,s)` is tight at `sharpNearHalf t` (for `t=4`, densities `p_1=44/85, p_2=284/595, p_3=48/85, p_4=0` achieve `41/85` on all part-unions). Going below `sharpNearHalf t` for `t >= 4` at scale `(log n)^(1/(t-1))` requires going beyond a single monochromatic `t`-partite box.
- Both conjuncts of `hremaining` are famous open conjectures in combinatorics; `OMA.solution` cannot be closed without a mathematical breakthrough.

## Leg 2: codex  (11:20, 12 min, ended: exit)
File stats: proved lemmas 169, sorries 1, lines 4372 (was 133 / 1 / 3454)
# Erdős 161(i), Codex relay leg

Approach: preserve every inherited helper. Step up from each arity r ≥ 3 using the first comparison when the delta word turns, and realize chosen deltas inside a monotone block. For Ramsey upper bounds, choose ordered vertices and thin the reserve by the new color patterns after each choice. For density, use double counting under one-vertex deletion to shrink any sparse witness to exactly the desired size.

Compiled in the target:
- avoidMono_step_general, diagonalRamsey_step_general, threshold_zero_le_iterated_binary, threshold_zero_isBigO_iterated_binary.
- lastUniform_build, diagonalRamsey_upper_step, diagonalRamsey_three_upper, log_log_isBigO_threshold_three_zero, threshold_zero_four_isLittleO_three.
- threshold_classes_three_iff_diagonalRamsey and threshold_three_full_square_iff_quadratic give the two possible classifications at t = 3.
- exists_sparse_of_card, hasSparseSubsetsAtLogScale_iff_exact, hasSparseSubsetsAtLogScale_iff_binary_exponential, threshold_classes_high_iff_binary_exponential. The high-arity candidate is now equivalent to exact m-vertex sparse witnesses at n = 2^(K m^(t−1)), for every density 1/(k+3), some K depending on t,k, and all sufficiently large m.

Exact gap: hremaining still needs (1) for t ≥ 4 and each 0 < a < sharpNearHalf t, every coloring must admit a subset of size Ω((log n)^(1/(t−1))) with one color below density a, and (2) for t = 3, for every C > 0 and N there must be m ≥ N with log R₃(m) > C m².

Dead ends: the single multipartite box only gives the near-half interval through its part unions. The larger many-part box has a weaker logarithmic exponent. For t = 3 a tower lower bound, or little-o on the entire sequence, would be stronger than the required unboundedness on every tail. The new Ramsey upper bound does not decide this unboundedness.

Verification: the full target elaborates with only hremaining's placeholder warning. The first import, OMA.solution statement, and all inherited helper bodies were preserved.
Axiom audits on nine main additions list only propext, Classical.choice, and Quot.sound. The exact CI checker rejected at lint solely for the remaining sorry.

RESULT: STALLED
