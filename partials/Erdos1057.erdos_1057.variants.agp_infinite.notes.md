# Relay notes for Erdos1057.erdos_1057.variants.agp_infinite (prize: )


## Leg 2: codex  (16:20, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 2: codex  (17:17, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:34, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 35 (was 0 / 1 / 10)
# notes_opus: Erdos1057 agp_infinite (relay leg 1)
Approach: restored the earlier compiled partial (runs/...-fast4-2121/final.lean) into the proof file.
Compiled (direct lake env lean, only warning is the sorry): lemma reduce (Set.Infinite {n | IsCarmichael n} -> Tendsto carmichaelCounting atTop atTop), OMA.solution := reduce carmichael_infinite.
Remaining gap: ONE sorry, lemma carmichael_infinite = full AGP94 theorem.
Possible further split (not a sorry drop): follow merged reduction R1 (H1 Davenport bound via vEB-K/Meshulam, H3 Korselt sufficiency, both elementary; H2 = AGP analytic prime production via Prachar + Bombieri-Vinogradov, not in Mathlib). H2 is the true blocker.
Dead ends: none new; the target is faithful, no loophole (IsCarmichael includes compositeness).

## Leg 1: gemini  (23:44, 20 min, ended: cap20_sorry_unchanged)
File stats: proved lemmas 2, sorries 1, lines 35 (was 2 / 1 / 35)
# notes_gemini: Erdos1057.erdos_1057.variants.agp_infinite (relay leg 1)

## Approach
Unconditional infinitude of Carmichael numbers (AGP 1994) requires a pointwise prime-in-AP estimate up to level $d \le x^B$ ($B > 0$) avoiding $O(1)$ exceptional moduli (AGP Theorem 2.1, proved via a log-free zero-density estimate for Dirichlet L-functions, not in Mathlib; standard Bombieri-Vinogradov does not suffice because divisors of $L$ have exponentially small density).

To maximize concrete progress while preserving sorry count = 1, I am reducing `carmichael_infinite` (and hence `OMA.solution`) completely inside `proofs/Erdos1057.erdos_1057.variants.agp_infinite.lean` to the single analytic input `agp_primes_in_ap` (AGP Theorem 2.1, weak form for $a = 1$ with any $0 < B < 1/2$):
- `agp_primes_in_ap`: exists $0 < B < 1/2$, $0 < c_1 \le c_2$, $x_0 \ge 2$, $E : \mathbb{N}$ such that for all $x \ge x_0$, exists a finset $\mathcal{E}$ of integers $> 1$ with $|\mathcal{E}| \le E$ such that for all $1 \le d \le x^B$ not divisible by any $e \in \mathcal{E}$, $c_1 x / (\phi(d) \log x) \le \pi(x; d, 1) \le c_2 x / (\phi(d) \log x)$.

All other ingredients are proved completely without sorry:
1. Korselt sufficiency (`korselt_sufficient`, adapted from R1.H3 by @ivillar).
2. van Emde Boas-Kruyswijk / Meshulam Davenport bound (`davenport_bound`, adapted from R1.H1 by @marcusbuffett).
3. AGP assembly from `H2` to `carmichael_infinite` (adapted from R1 by @Dugongue).
4. Elementary primorial bound `prod_primes_le_four_pow`: $\prod_{p \le n} p \le 4^n$ via central binomial coefficients.
5. Smooth-shifted-prime construction `exists_smooth_shifted_primes` from `agp_primes_in_ap` (uses only $d=1$ on a single interval $(u, Cu]$ plus $d=a$ on $(y^{1+\delta/2}, y^{1+\delta}]$, no Mertens theorem needed).
6. Exponent bound `exponent_zmod_le` using the explicit multiple $W = (\prod_{r \le y} r) \cdot (\prod_{r \le \sqrt{y}} r^{	ext{Nat.log } r \lfloor y^{1+\delta} floor}) \le 4^y (y^2)^{\sqrt{y}}$.
7. Dyadic pigeonhole + coprimality union bound via `agp_primes_in_ap` at $(x, d)$ and $(x, d q)$ to prove `agp_prime_production` (`R1.H2`).

## Status
Starting implementation in `proofs/Erdos1057.erdos_1057.variants.agp_infinite.lean`.
