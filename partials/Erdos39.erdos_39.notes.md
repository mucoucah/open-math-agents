# Erdos39.erdos_39 notes (opus leg 1)
Approach: audited statement only. Faithful formalisation of the OPEN Erdos $500 problem
(infinite Sidon set with |A cap [1,N]| >> N^(1/2-eps) for every eps>0).
IsSidon (FormalConjecturesForMathlib/Combinatorics/Basic.lean:68) is the standard definition;
the function is (N:R)^(1/2-eps) via rpow, IsBigO atTop, ncard of Icc 1 N cap A. No loophole:
eps ranges over all positive reals, small eps is the genuine problem.
Best known: Ruzsa 1998 N^(sqrt2-1+o(1)); exponent 1/2-eps for all eps is open.
Compiled: nothing new (file unchanged, one sorry).
Gap: the whole open problem.
Dead ends: none beyond no-loophole audit. Recommend FAILED fast pass, stop at once.

## Leg 1: opus  (08:12, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos39.erdos_39 notes (opus leg 1)
Approach: audited statement only. Faithful formalisation of the OPEN Erdos $500 problem
(infinite Sidon set with |A cap [1,N]| >> N^(1/2-eps) for every eps>0).
IsSidon (FormalConjecturesForMathlib/Combinatorics/Basic.lean:68) is the standard definition;
the function is (N:R)^(1/2-eps) via rpow, IsBigO atTop, ncard of Icc 1 N cap A. No loophole:
eps ranges over all positive reals, small eps is the genuine problem.
Best known: Ruzsa 1998 N^(sqrt2-1+o(1)); exponent 1/2-eps for all eps is open.
Compiled: nothing new (file unchanged, one sorry).
Gap: the whole open problem.
Dead ends: none beyond no-loophole audit. Recommend FAILED fast pass, stop at once.

## Leg 2: codex  (08:16, 4 min, ended: exit)
File stats: proved lemmas 7, sorries 1, lines 175 (was 0 / 1 / 10)
# Erdős 39, Codex leg 2

Approach: exact finite-prefix reformulation. Use exponents 1/2 − 1/(k+4); absorb the Big-O multipliers with exponent slack; clear the rational exponents with positive integer powers. Take an ultrafilter limit of finite witnesses. Each finite prefix stabilizes along the ultrafilter, so Sidonicity and the prefix inequalities pass to the limit.

Compiled: prefix_power_iff, tendsto_nat_rpow, exists_exponent_ge, eventual_lower_bound, finiteWitnesses_of_bigO, limit_of_finiteWitnesses, exists_of_finiteWitnesses. Both public directions depend only on propext, Classical.choice, and Quot.sound. The full file elaborates with one placeholder. The requested checker returned rejected, lint: forbidden: 'sorry'.

Exact remaining gap: prove ∃ T : ℕ → ℕ, HasFiniteWitnesses T. A single T must work for every M. At each M find one Sidon finset B ⊆ [1,M] with N^(k+2) ≤ |B ∩ [1,N]|^(2*(k+4)) for all k,N ≤ M with T k ≤ N.

Dead ends: leg 1 confirmed the translation matches the open problem. Endpoint-only finite Sidon bounds provide no simultaneous prefix estimates. The finite criterion makes the remaining requirement explicit but does not supply the uniform witnesses.

## Leg 1: opus  (09:35, 0 min, ended: exit)
File stats: proved lemmas 7, sorries 1, lines 175 (was 7 / 1 / 175)
# Erdos39.erdos_39 notes (opus relay leg 1, this round)
Approach: none new. The file keeps codex's compiled finite-prefix and ultrafilter reformulation
(prefix_power_iff, tendsto_nat_rpow, exists_exponent_ge, eventual_lower_bound,
finiteWitnesses_of_bigO, limit_of_finiteWitnesses, exists_of_finiteWitnesses). File unchanged.
Remaining gap: the sorry `∃ T, HasFiniteWitnesses T`. It is equivalent to the target
(the converse finiteWitnesses_of_bigO is proved), so it is exactly the OPEN Erdos $500 problem.
Best known: Ruzsa N^(sqrt2-1+o(1)).
Dead ends: the statement is faithful with no loophole (checked in earlier legs and in the wt12 memory);
the reduction leg found NO_REDUCTION. Recommend: stop at once, FAILED.

## Leg 2: codex  (09:39, 3 min, ended: exit)
File stats: proved lemmas 13, sorries 1, lines 296 (was 7 / 1 / 175)
# Erdős 39, Codex relay leg 2

Approach: retained the exact finite-prefix reformulation and added a lower-exponent baseline. Scan the integers in order, inserting an integer whenever Sidonicity survives. Each rejected integer x has a collision x+a=b+c among earlier entries, with a≠b. The ordered off-diagonal count gives N ≤ |B ∩ [1,N]|³ at every prefix.

Compiled in the proof file: all seven prior lemmas, plus greedyPrefix, greedyPrefix_sidon, greedyPrefix_subset, greedyPrefix_mono, greedyPrefix_card, exists_cubic_prefix_witness, and finiteWitnesses_through_two. The latter gives one witness at each M for all N≤M and k≤2 with threshold zero.

Remaining gap: ∃ T, HasFiniteWitnesses T. A single T must work for every M, with one Sidon witness B ⊆ [1,M] at each M satisfying N^(k+2) ≤ |B ∩ [1,N]|^(2*(k+4)) for all k,N≤M with T k≤N. The new construction verifies k≤2 only.

Dead ends: earlier legs audited the statement and found the exact open problem. Endpoint estimates give no simultaneous prefix bounds. The greedy collision count supplies exponent 1/3 and does not furnish the higher exponents.

Verification: Lean elaborated the full file with one existing placeholder. Both new public lemmas depend only on propext, Classical.choice, and Quot.sound. The exact CI command rejected at lint with forbidden: 'sorry'.
