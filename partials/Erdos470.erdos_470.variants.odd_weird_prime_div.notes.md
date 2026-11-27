# Relay notes for Erdos470.erdos_470.variants.odd_weird_prime_div (prize: $10)


## Leg 1: fable  (22:26, 14 min, ended: stalled)
File stats: proved lemmas 9, sorries 1, lines 168 (was 0 / 1 / 10)
# notes_fable (leg 1) - Erdos470 odd_weird_prime_div

RESULT OF LEG: STALLED (not accepted). Proofs file compiles with ONE sorry (OMA.core).

NOTE: notes_codex.md / notes_opus.md and reductions/...odd_weird_10_pow_21.R1.lean in this scratch
dir belong to the SIBLING problem odd_weird_10_pow_21, not to this one. This problem had no
earlier leg.

## Target
Every odd abundant n with at most 5 distinct primes is pseudoperfect (Liddy-Riedl 2018).
No loophole in the Lean statement (n = 0 is not abundant; the ncard is primeFactors.card).

## How to compile (check.sh lints sorry before compiling, so compile directly; about 5 s)
cd /workspace/left-to-solve/repo/.oma/formal-conjectures && lake env lean /workspace/left-to-solve/wt10/proofs/Erdos470.erdos_470.variants.odd_weird_prime_div.lean

## Compiled (proofs file, no errors, ONE sorry = OMA.core)
- OMA.pp_of_dvd       : positive multiple of a pseudoperfect number is pseudoperfect
- OMA.ncard_eq        : the ncard in the target = n.primeFactors.card
- OMA.pp_of_excess    : t subset properDivisors n, sum t + n = sum properDivisors n -> Pseudoperfect n
- OMA.pp_of_list      : certificate form, strictly increasing list of proper divisors with sum n
                        (all hypotheses close with decide on numerals; tested by OMA.pp_945)
- OMA.pp_mul_step     : q > 1 coprime to m, s subset divisors m, t subset properDivisors m,
                        sum s + q * sum t = m * q  ->  Pseudoperfect (m * q)
- OMA.pp_mul_step_pow : same with m | d, t subset properDivisors d, sum s + q * sum t = d * q
                        (use d = m * q^k for a prime power q^(k+1))
- OMA.all_pp          : strong induction, reduces to primitive abundant (all proper divisors deficient)
- OMA.solution        : glue, uses all_pp

## Reduction candidate (official checker verdict: accepted, as a REDUCTION, not a proof)
.oma/scratch/reductions/Erdos470.erdos_470.variants.odd_weird_prime_div.R1.lean
  H1: odd primitive abundant, at most 4 distinct primes -> pseudoperfect (584 numbers, below 10^18)
  H2: odd primitive abundant, exactly 5 distinct primes -> pseudoperfect
Checked with: cd .oma/scratch && OMA_FC=/workspace/left-to-solve/repo/.oma/formal-conjectures ../../tools/check.sh <absolute path> /tmp/v.json

## Exact remaining gap
OMA.core: Odd n, n.Abundant, all proper divisors Deficient, n.primeFactors.card <= 5 -> n.Pseudoperfect.

## Size of the gap (scratch/count_pa.py: exact rational tree search, reproduces Dickson 8 and 576)
- exactly 3 primes: 8 numbers (largest prime 13, n < 10^6)
- exactly 4 primes: 576 numbers (largest prime 383, n up to 18 digits)
- exactly 5 primes: count unknown, see scratch/count5.out (the run has a 7 minute limit and had
  not finished after 5). The set is finite (Dickson) but huge and contains 38-digit numbers: the
  prime set {3, 5, 17, 257, q} allows every prime q up to 65521, and
  3^19 * 5^13 * 17^6 * 257^3 * 65521 = 38087924837528242729787913841552734375 is odd primitive
  abundant (verified by scratch/monster.py: excess about 1.09 * 10^28, 15680 divisors). This is far
  above the 10^21 range of Fang, so no existing search result covers the gap.
So OMA.core is a finite statement, but far too big for one certificate per number. A finished
proof needs EITHER a kernel-evaluated verified tree search (effective Dickson: branch on next prime
and exponent, cap exponents, prune when h(m) * prod q/(q-1) over the remaining slots is at most 2,
leaf = abundant node, leaf check by a greedy subset sum) with a soundness proof, OR uniform family
lemmas for a large last prime built on OMA.pp_mul_step. Neither fits in a 15 to 25 minute leg.

## Maths facts worked out (not in Lean)
- 3 | n always; second prime in {5,7,11}; {3,11,13,17,19} is the only prime set with second prime 11.
- Last-prime step, n = m * q, q prime not dividing m, delta = 2m - sigma(m) > 0:
  excess(n) = sigma(m) - q * delta, and n is pseudoperfect iff there is t, a sum of distinct proper
  divisors of m, with q * (delta + t) a sum of distinct divisors of m (this is OMA.pp_mul_step).
- excess is even for non-square n and 2 is never a sum of distinct odd divisors, so any proof must
  exclude sigma(n) = 2n + 2 for these n. No congruence argument found; only the enumeration does it.
- Interval heuristic: if every x in [L, sigma(m) - L] is a sum of distinct divisors of m and
  q * (max gap) <= sigma(m) - 2L + 1, the same L works for m * q. Example: sums of distinct
  divisors of 315 are all of [0, 624] except 2 and 622.

## Worth a human check (unverified, no network here)
The source is an undergraduate honors thesis. If it counts the 6 prime divisors WITH multiplicity,
the upstream Lean statement (6 DISTINCT primes) is much stronger than the cited result, and its
proof is the large Dickson enumeration above rather than a short list of cases.

## Dead ends
- check.sh on a file with sorry: instant lint reject, gives no compile info (compile directly).
- Short pen-and-paper argument: none found. Families with a huge last prime need the exact
  subset-sum structure of m, and small excess values (2) need the exact arithmetic of each case.
- count_pa.py 5 with exponent cap p^e <= 10^30: too slow to finish (do not rerun as is).

## Leg 2: opus  (22:27, 1 min, ended: exit)
File stats: proved lemmas 9, sorries 1, lines 168 (was 9 / 1 / 168)
# notes_opus (leg 2) - Erdos470 odd_weird_prime_div

RESULT OF LEG: STALLED, stopped early on purpose (about 3 min). Proofs file unchanged, still compiles
with ONE sorry (OMA.core). Every lemma from leg 1 is kept (pp_of_dvd, ncard_eq, pp_of_excess,
pp_of_list, pp_945, pp_mul_step, pp_mul_step_pow, all_pp, solution).

## Re-checked
- The upstream statement (470.lean:121) is faithful: Odd n, n.Weird, 6 <= number of distinct prime
  divisors. No loophole.
- The file compiles: lake env lean gives warnings only, plus the sorry in OMA.core.

## Exact remaining gap (same as leg 1)
OMA.core: Odd n, Abundant, every proper divisor Deficient, primeFactors.card <= 5 -> Pseudoperfect.
This is the effective Dickson enumeration of odd primitive abundant numbers with at most 5 primes,
and it includes 38-digit cases (see notes_fable.md). That cannot be done with one certificate per
number. It needs either a verified tree search evaluated by the kernel (decide, no native_decide)
or uniform family lemmas for a large last prime. Neither fits in a 15 to 25 minute leg.

## Why I stopped
Small side lemmas, such as no odd abundant number having at most 2 prime factors, would not
reduce the real gap (the 5-prime enumeration), so they are not worth a leg's time.
Recommendation: report FAILED for the fast pass, or attempt it only as a multi-hour project
(computable tree search plus a soundness proof).

## Leg 3: grok  (22:32, 5 min, ended: stalled)
File stats: proved lemmas 9, sorries 1, lines 168 (was 9 / 1 / 168)
(the model wrote no notes; see partial_grok.lean)
