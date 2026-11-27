# Relay notes for Erdos470.erdos_470.variants.odd_weird_10_pow_21 (prize: $10)


## Leg 1: fable  (22:01, 4 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 69 (was 0 / 1 / 10)
# notes_fable (leg 1) — Erdos470 odd_weird_10_pow_21

RESULT OF LEG: STALLED (target is infeasible; glue compiled, one sorry = OMA.core).

## Assessment
- Target: forall n < 10^21, Odd n -> not n.Weird. Mathlib defs are standard
  (Abundant: n < sum properDivisors; Pseudoperfect: 0 < n and some subset of properDivisors sums to n).
  No loophole in the statement: it is exactly Fang 2022 (arXiv 2207.12906).
- Fang's result is a huge exhaustive tree search over odd primitive abundant numbers
  (first done by volunteer computing, yoyo@home OWS, CPU-years). It contains e.g. the fact that
  no odd n < 10^21 has sigma(n) = 2n+2 (abundance 2 is never a sum of odd divisors, so such n
  would be weird); no theoretical proof of that exists, only search.
  So a kernel-checked proof (no native_decide) is NOT feasible in a session.

## What compiled (proofs file, 6 s with lake env lean; the ONLY sorry is OMA.core)
- OMA.pp_of_dvd : d | n, 0 < n, d.Pseudoperfect -> n.Pseudoperfect
- OMA.pp_iff_abundance : 0 < n -> (n.Pseudoperfect <-> exists t subset properDivisors,
  sum t + 2n = sum divisors)   (abundance criterion, complement trick; not yet used)
- OMA.all_pp : strong induction, reduces target to OMA.core
- OMA.solution : from OMA.all_pp
- OMA.core (SORRY): forall n < 10^21, Odd n -> n.Abundant ->
  (forall d in n.properDivisors, d.Deficient) -> n.Pseudoperfect

## Reduction candidate (check.sh verdict: ACCEPTED, 12 s)
- .oma/scratch/reductions/Erdos470.erdos_470.variants.odd_weird_10_pow_21.R1.lean
  H1 = core restricted to 3 | n, H2 = core restricted to not 3 | n; main = pp_of_dvd + strong induction.
  Check it with: cd .oma/scratch && OMA_FC=/workspace/left-to-solve/repo/.oma/formal-conjectures
  ../../tools/check.sh <ABSOLUTE path of the R1 file> /tmp/v.json

## Exact remaining gap
- OMA.core = every odd primitive abundant number below 10^21 is pseudoperfect.
  This IS the computation of the paper (order 10^15 or more primitive abundant numbers).

## How to compile while a sorry is present
- tools/check.sh rejects at lint (forbidden: sorry) without compiling. To see Lean errors:
  cd /workspace/left-to-solve/repo/.oma/formal-conjectures && lake env lean <absolute path of proofs file>

## Dead ends
- Do not try decide / interval_cases on the core: range is 10^21.
- No shortcut via Mathlib: only weird_seventy and basic Abundant/Deficient lemmas exist.
- Explicit witnesses (e.g. 945 pseudoperfect, then all multiples by pp_of_dvd) only kill
  single families; the primitive abundant numbers m*p with m near-perfect and p a large prime
  are the bulk and need the real search.

## Ideas NOT tried (unverified, only if someone has hours)
- Abundancy-index bound: an odd abundant n < 10^21 must be divisible by 3 or 5
  (primes 7..61 already multiply to about 3.9e21). Would shrink H2 but not close it.
- For n = m*p (p large prime, p not dividing m): abundance is sigma(m) - p*(2m - sigma(m));
  n is pseudoperfect iff that is A + p*B with A a subset sum of divisors of m and B a subset
  sum of proper divisors of m. Needs a dense-subset-sum (practical-number style) lemma for odd m.

## Leg 2: opus  (22:02, 0 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 69 (was 4 / 1 / 69)
# notes_opus (leg 2) - Erdos470 odd_weird_10_pow_21

RESULT OF LEG: STALLED, stopped early on purpose. No change to the proofs file.

## Approach
Same as leg 1: glue compiled, the only gap is OMA.core (odd primitive abundant n below 10^21
is pseudoperfect). That gap is Fang 2022's exhaustive search: about 10^15 or more primitive
abundant numbers, CPU-years of volunteer computing. It includes facts with no known theoretical
proof, e.g. no odd n below 10^21 has sigma n = 2n+2. A kernel proof without native_decide
is not possible in a session.

## Compiled (unchanged)
OMA.pp_of_dvd, OMA.pp_iff_abundance, OMA.all_pp, OMA.solution; one sorry, OMA.core.
Reduction R1 (split by 3 | n) was check.sh-ACCEPTED in scratch/reductions (leg 1).

## Exact remaining gap
OMA.core, the whole computational content of the paper.

## Dead ends
Everything in handover_notes.md. Extra splits (3 | n or 5 | n, abundancy bounds) only shrink
the cases; they do not remove the search. Recommend the next leg also stops quickly.

## Leg 3: grok  (22:07, 5 min, ended: stalled)
File stats: proved lemmas 4, sorries 1, lines 69 (was 4 / 1 / 69)
(the model wrote no notes; see partial_grok.lean)

## Leg 4: codex  (22:11, 4 min, ended: exit)
File stats: proved lemmas 12, sorries 1, lines 277 (was 4 / 1 / 69)
# Leg 4

Approach: write n = d*p with d = m*p^k, where p is the largest prime factor
and p does not divide m. Split its proper divisors into divisors of m and
p times proper divisors of d. Use the deficit of d to compute the abundance.

Compiled with Lean: OMA.pp_of_dvd, OMA.pp_iff_abundance,
OMA.properDivisors_prime_step, OMA.sum_properDivisors_prime_step,
OMA.subset_sum_prime_step, OMA.subset_sum_prime_step_bounded,
OMA.subset_sum_prime_step_of_lt, OMA.abundance_eq_prime_step, OMA.core,
OMA.all_pp, OMA.solution. The only sorry is OMA.core_prime_search (line 188).

Remaining search: given n = d*p below 10^21, odd, every prime quotient
deficient, let a = sigma(m) - deficit(d)*p > 0. Prove sum(s) + p*sum(t) = a
with s drawn from divisors of m at most a and t from proper divisors of d
at most a/p. When a < p, the compiled of_lt lemma leaves only the divisor
sums of m. This still requires ruling out candidates such as a = 2,
which cannot be a sum of distinct positive odd divisors.

Final CI verdict: rejected, lint: forbidden sorry. Direct Lean compilation
reported the sole sorry and a module docstring warning, with no errors.

Dead ends from earlier legs: direct enumeration to 10^21, a bare split by
small prime divisibility, and searching Mathlib for the target. The
largest-prime reduction narrows each subset-sum search, and no exhaustive
certificate for the remaining candidates is available in the handover.
