# Relay notes for Erdos1191.erdos_1191.parts.i (prize: $1000)


## Leg 1: opus  (09:23, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 34 (was 0 / 1 / 10)
# Erdos1191.erdos_1191.parts.i  (opus leg 1)
Status: STALLED. The statement is the open 1000-dollar Erdos question and it is formalised faithfully:
the target asserts liminf = 0 for EVERY infinite Sidon A, with no answer(sorry) and no loophole
(Icc 1 x leaves out 0, liminf is in ENNReal, IsSidon is the standard notion).
Compiled (lake env lean, one sorry): OMA.E1191i.liminf_ofReal_zero_of_frequently (my own, about 6 lines),
and OMA.solution reduces to OMA.E1191i.core (for every eps>0, frequently count/sqrt x * sqrt log x <= eps).
Remaining gap: core = the open problem itself. Merged reduction R1 (kenanwienberg): H1 dyadic bound
(proved upstream, PR 772) plus H2 (a scale with few new points in the next L dyadic blocks), and H2 is the open part.
Dead ends: none worth trying in one session; Erdos's bound gives only liminf <= c, not 0.

## Leg 2: codex  (09:29, 5 min, ended: stalled)
File stats: proved lemmas 2, sorries 1, lines 34 (was 2 / 1 / 34)
# Erdos1191 i, relay leg 2
The previous liminf conversion and OMA.solution are preserved. The core remains open.
Approach under investigation: restrict the classical short-difference budget to pairs inside disjoint, equal-width cells. A positive critical liminf should force positive density of short differences from mesoscopic scales. The known absolute budget only gives a constant bound.

## Leg 3: fable  (09:32, 3 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 60 (was 2 / 1 / 34)
# Erdos1191.erdos_1191.parts.i  (fable leg 3)
Status: STALLED. Faithful formalisation of the open 1000-dollar Erdos question; I re-audited it and found no loophole
(IsSidon in FormalConjecturesForMathlib/Combinatorics/Basic.lean:68 is the standard notion; log is Real.log of the cast;
a / b * c parses as (a / b) * c; Icc 1 x; liminf in ENNReal along atTop on Nat).

## Approach
Keep the two-step shell from leg 1 and push the single sorry down to an rpow-free, filter-free statement.

## What compiled (lake env lean on the proofs file, 6 s, exactly one sorry)
- OMA.E1191i.liminf_ofReal_zero_of_frequently (leg 1, kept unchanged)
- OMA.E1191i.normalised_le_of_sq_le (NEW): for x >= 1 and eps > 0,
  n^2 * log x <= eps^2 * x  implies  n / x^(1/2) * (log x)^(1/2) <= eps.
- OMA.E1191i.core (was the sorry, NOW PROVED from core_sq via Filter.frequently_atTop)
- OMA.solution (unchanged statement, proved from core)

## Exact remaining gap (the only sorry)
OMA.E1191i.core_sq: for A infinite Sidon, eps > 0 and every N there is x >= N, x >= 1 with
  ((A inter Icc 1 x).ncard : Real)^2 * Real.log x <= eps^2 * x.
This is the open problem itself (equivalently limsup a_k / (k^2 log k) = infinity for the k-th element a_k).

## Dead ends (do not repeat)
- Erdos block argument (blocks of length N inside [1, N^2], sum of C(D_k,2) <= N/2, Cauchy-Schwarz with weights k^(-1/2))
  gives only liminf <= constant. Shifted or overlapping windows only improve the constant (factor 2).
- Extending the range to [N, N^K] with K > 2 does not help: beyond N^2 the blocks hold 0 or 1 points on average,
  so convexity forces no pairs there; the budget argument stays consistent for small c.
- First-moment heuristic: density (c/2)/sqrt(x log x) gives expected number of representations of a difference d
  inside [d, d^2] equal to (c^2/4) log 2, so pure difference counting cannot contradict small c > 0.
- Merged R1 (H1 dyadic bound proved upstream by another contestant, H2 open) does not shrink the gap; H2 is the open core.
A real proof needs a new idea beyond counting short differences; not a session-sized task.

## Leg 1: opus  (10:12, 0 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 60 (was 4 / 1 / 60)
# Erdos1191.erdos_1191.parts.i  (opus relay leg 1, this round)
Status: STALLED (fast stop). Open 1000-dollar Erdos question, faithful formalisation, no loophole (audited in earlier rounds; not re-audited).
File unchanged from previous best partial: compiled lemmas liminf_ofReal_zero_of_frequently, normalised_le_of_sq_le, core, OMA.solution.
Exact remaining gap (single sorry): OMA.E1191i.core_sq: for A infinite Sidon, eps>0, N, exists x>=N, x>=1 with
  ncard(A inter Icc 1 x)^2 * log x <= eps^2 * x.  This IS the open problem.
Dead ends (see handover_notes.md): Erdos block / Cauchy-Schwarz arguments, wider ranges [N,N^K], first-moment
short-difference counting all give only liminf <= const. Merged R1.H2 and R2 halves are equally open.

## Leg 2: codex  (10:18, 5 min, ended: exit)
File stats: proved lemmas 12, sorries 1, lines 271 (was 4 / 1 / 60)
# Erdős 1191(i) — Codex relay

Baseline from previous legs: liminf_ofReal_zero_of_frequently, normalised_le_of_sq_le,
core and OMA.solution compiled, with a single gap in core_sq (arbitrarily small squared critical density).
Approach in progress: replace the real all-scale condition with an integer dyadic obstruction for finite Sidon prefixes, and prove the transfers.
Earlier dead ends: total short-difference budget gives a constant, and enlarging the window range gives no forced pairs past the quadratic scale.

Compiled progress (lake env lean, one sorry): prefix_filter_card and
core_sq_from_finite_obstruction. Existing core_sq now follows from finite_obstruction.
The gap is currently DyadicFiniteObstruction: for every positive integer d and initial index J,
some finite K >= J makes every Sidon subset S of [1,2^K] have a j in [J,K] with
d * |S ∩ [1,2^j]|^2 * j <= 2^j.
Working on the converse via a convergent subsequence of Boolean membership functions.

Also compiled and merged matching_prefixes, infinite_of_strict_dyadic_counts, and
infinite_witness_of_finite_witnesses. Unbounded finite counterexample prefixes give
an infinite Sidon A with 2^j < d * |A ∩ [1,2^j]|^2 * j for all j >= J. The proof extracts
a subsequence in the compact product of Boolean membership coordinates.

Compiled and merged critical_lower_bound_of_dyadic and finite_obstruction_from_core_sq.
Between dyadic scales the loss in the squared lower bound is at most a factor of two.
The two transfers make the finite obstruction equivalent to the previous open core,
with no dependency on the remaining sorry in either direction.

Final main file compiled with exactly one sorry, in finite_obstruction. The
decidableDyadicHorizon definition also compiled, giving a finite search for each fixed d, J, K.
The mandated tools/check.sh verdict is rejected with reason lint: forbidden: 'sorry'.
No counting argument was retried. The unresolved step is the uniform existence of K
for every (d, J); deciding individual horizons establishes no uniform existence result.
Lean's axiom audit confirmed the two transfer lemmas depend only on propext,
Classical.choice, and Quot.sound. Two small opposite-outcome horizon tests evaluated with decide.

## Leg 2: codex  (15:47, 0 min, ended: exit)
File stats: proved lemmas 12, sorries 1, lines 271 (was 12 / 1 / 271)
(the model wrote no notes; see partial_codex.lean)
