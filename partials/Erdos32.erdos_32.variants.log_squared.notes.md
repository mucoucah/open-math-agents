# Relay notes for Erdos32.erdos_32.variants.log_squared (prize: $50)


## Leg 1: grok  (23:20, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (23:21, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 35 (was 0 / 1 / 10)
# Erdos32 log_squared — leg 2 (opus) notes
Approach: the file reduces OMA.solution to OMA32.core (explicit bound card <= C (log N)^2 for N >= N0),
using OMA32.bigO_of_bound (compiles). Whole file compiles via lake env lean with exactly ONE sorry: OMA32.core.
check.sh rejects only because of lint (sorry).

Remaining gap = the Erdos 1954 theorem itself (OMA32.core).
Math analysis / dead ends:
- Dyadic greedy set cover (universe n in [2^k,2^{k+1}), sets S_a={n : n-a prime}, a<2^{k+1}):
  each n covered by pi(n) >= pi(2^k) >= c 2^k/k sets, so greedy needs O(k^2) elements PER BLOCK,
  summing to O(log^3 N) (this is Lorentz-type bound). NOT enough for log^2.
- Fractional cover with weights C log a / a also loses a factor k through greedy (ln of universe size).
- Erdos real proof: random A with P(a in A)= C log a / a; needs, for almost every n,
  sum over primes p<n of log(n-p)/(n-p) >> log n (averaged short-interval prime estimates, second
  moment via Brun/Selberg sieve upper bound for prime pairs p, p+h), exceptions fixed by hand.
  Requires sieve upper bound (pairs of primes with fixed difference) — not in Mathlib; multi-hour project.
- No loophole: statement is faithful (0 in A irrelevant, count on [1,N]).
Possible future route: prove log^3 version is NOT accepted (target is log^2) — so the sieve is unavoidable.

## Leg 3: codex  (23:27, 5 min, ended: stalled)
File stats: proved lemmas 2, sorries 1, lines 35 (was 2 / 1 / 35)
Leg 3. Preserving OMA32.bigO_of_bound and the exact solution statement.
Approach in progress: independently sample m(k+1) points with replacement from [2^k,2^(k+1)); the prefix count is deterministic. Express each miss probability as a finite product and apply first Borel–Cantelli. The required prime estimate will be isolated from the sampling argument.
Compiled so far: inherited OMA32.bigO_of_bound. Gap: OMA32.core. Earlier per-block greedy loses one logarithm.

## Site hints (2026-11-26)

https://www.erdosproblems.com/32 (YAML: open — whether o((log N)^2) or even O(log N) is possible is still open). This variant is already a theorem of Erdős 1954, *Some results on additive number theory*: there is an additive complement A to the primes with |A ∩ {1,…,N}| = O((log N)^2). Follow that paper. (Ruzsa 1998 later proved liminf |A∩[1,N]| / log N ≥ e^γ, which is the `ruzsa` / `liminf_gt_one` variants.) Write-up: /workspace/left-to-solve/research/erdosproblems.md

## Leg 4: fable  (23:32, 5 min, ended: stalled)
File stats: proved lemmas 2, sorries 1, lines 35 (was 2 / 1 / 35)
(the model wrote no notes; see partial_fable.lean)
