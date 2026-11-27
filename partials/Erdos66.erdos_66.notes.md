# Relay notes for Erdos66.erdos_66 (prize: $500)


## Leg 1: opus  (08:13, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos66.erdos_66 -- opus leg 1 notes
Statement: exists A subset N, c != 0, sumRep A n / log n -> c. sumRep = ordered-pair count of a+b=n
(antidiagonal filter), a genuine Nat, log is Real.log. Faithful to Erdos $500 open problem.
Loophole check: none. c != 0 forced; sumRep finite; log n -> infinity, n=0,1 irrelevant for limit.
No construction known (Erdos-Turan conjecture-adjacent; Erdos proved only Theta(log n) via probabilistic
method, ratio not convergent). Open research problem.
What compiled: nothing new (file is the plain sorry skeleton).
Remaining gap: the whole open conjecture.
Dead ends: none worth trying; random A gives limit only in probability-fluctuating sense (Erdos 1956
gives c1 log n <= r(n) <= c2 log n, not a limit).
Verdict: FAILED fast pass.

## Leg 2: codex  (08:18, 5 min, ended: exit)
File stats: proved lemmas 9, sorries 1, lines 237 (was 0 / 1 / 10)
Approach: Reduce the exact target in both directions to finite prefix feasibility. Use rational intervals for sumRep divided by Nat.log 2 n, with width at most 1/(k+1), positive first lower bound, and a common start schedule. Compactness of Bool-valued indicators turns arbitrary finite witnesses into one global set. Consecutive powers of two give the normalization and the converse follows by choosing rational intervals around the limit.
Compiled: sumRep_eq_of_agree_below, continuous_sumRep_indicator, exists_set_of_finite_sumRep_constraints, tendsto_natLog_two_atTop, tendsto_log_div_natLog_two, tendsto_div_natLog_two_iff, rat_ratioBounds_iff, exists_limit_of_finiteDyadicRepresentation, finiteDyadicRepresentation_of_exists_limit. The public proof helpers use only propext, Classical.choice, Quot.sound.
Remaining gap: OMA.solution has one sorry, the proposition OMA.Erdos66.finiteDyadicRepresentation. Find one schedule L, U, start such that every cutoff M has a finite B within [0,M] satisfying all activated intervals. Independent schedules for individual cutoffs do not suffice.
Dead ends: The previous leg found no statement loophole. Fixed-intensity independent sampling gives logarithmic-order bounds but does not supply uniformly vanishing relative error. Digital complementary masks give accurate cross terms but can contribute large same-mask or overlapping-mask spikes.
CI verdict: rejected at lint for the single remaining sorry. Direct Lean elaboration succeeded; the target alone depends on sorryAx.

## Leg 1: opus  (09:32, 0 min, ended: exit)
File stats: proved lemmas 9, sorries 1, lines 237 (was 9 / 1 / 237)
# Erdos66.erdos_66 -- opus relay leg 1 (this round) notes
Approach: none new. Target is the faithful open Erdos $500 problem (r_A(n)/log n -> c != 0), no loophole.
What compiled: file unchanged; keeps codex leg 2 compactness equivalence (9 lemmas:
sumRep_eq_of_agree_below, continuous_sumRep_indicator, exists_set_of_finite_sumRep_constraints,
tendsto_natLog_two_atTop, tendsto_log_div_natLog_two, tendsto_div_natLog_two_iff, rat_ratioBounds_iff,
exists_limit_of_finiteDyadicRepresentation, finiteDyadicRepresentation_of_exists_limit).
Remaining gap: the single sorry OMA.Erdos66.finiteDyadicRepresentation = the open problem itself
(one common rational interval schedule with all finite prefixes feasible).
Dead ends: random sampling (only Theta(log n), no limit); digital masks (spikes); splitting into
independent H's impossible (one existential over one set A) -- reduction leg returned NO_REDUCTION.
Verdict: STALLED immediately (open research problem).

## Leg 2: codex  (09:38, 6 min, ended: exit)
File stats: proved lemmas 14, sorries 1, lines 450 (was 9 / 1 / 237)
# Erdos66.erdos_66, Codex relay leg 2

Approach: Preserve the rational-window compactness reduction. Extend a fixed prefix B below m by D in [m, 2m). For n < 2m, the new count is the old count plus twice the number of j in D with j ≤ n and n - j in B. This gives explicit linear constraints for each dyadic extension.

Compiled: All nine inherited lemmas, plus sumRep_eq_prefix_add_twice, sumRep_union_extension, exists_set_of_dyadic_extensions, hasDyadicExtensions_iff_exists_set, and finiteDyadicRepresentation_iff_hasDyadicExtensions. Direct Lean elaboration succeeds. The five new lemmas use only propext, Classical.choice, and Quot.sound.

Remaining gap: OMA.Erdos66.finiteDyadicRepresentation. The new equivalence gives an exact alternative: choose one positive rational interval schedule with widths shrinking to zero and exhibit a prefix invariant with an initial witness and, for every prefix in the invariant, a compatible extension satisfying all linear constraints in the next block and preserving the invariant. No such invariant is known here.

Dead ends inherited: fixed-intensity independent random sampling does not give uniform vanishing relative error, and overlapping digital masks produce representation spikes.

CI verdict: rejected at lint for the single sorry in OMA.solution. The import line and target statement are unchanged.
