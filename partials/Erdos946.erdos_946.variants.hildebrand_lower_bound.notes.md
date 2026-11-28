# Relay notes for Erdos946.erdos_946.variants.hildebrand_lower_bound (prize: )


## Leg 2: codex  (16:22, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (17:53, 1 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 77 (was 0 / 1 / 10)
# notes_opus (relay leg 3, wt16): Erdos946.erdos_946.variants.hildebrand_lower_bound

Approach: statement audited: faithful full Hildebrand [Hi85] x/(log log x)^3 lower bound, no loophole
(count <= x+1, log log x > 0 eventually). Research-level (needs He84 seven-translate sieve machinery
plus Hildebrand reciprocal-mass estimates); not provable in a leg.

Compiled (proofs file, one sorry): namespace OMA946
- loglog_pos (16 <= y -> 0 < log log y), loglog_mono
- of_nat_core: Nat-indexed bound (exists c>0, eventually in N, c*N/(loglog N)^3 <= #{n<=N : tau n = tau(n+1)})
  implies the real IsBigO target (via N = floor x, x <= 2N).
- OMA.solution := of_nat_core hildebrand_nat_core

Exact remaining gap: hildebrand_nat_core (the Nat-indexed Hildebrand bound itself = whole theorem).
Hints: open PR 12698 (physbuzz R1) splits into seven-collision pigeonhole H1 (proved) + analytic H2
(reciprocal mass over disjoint translate families); H2 is the real blocker.
Dead ends: none cheap; Heath-Brown x/(log x)^7 variant also FAILED earlier (see memory).

## Leg 1: gemini  (02:59, 20 min, ended: cap20_sorry_unchanged)
File stats: proved lemmas 27, sorries 1, lines 1068 (was 4 / 1 / 77)
# notes_gemini (relay leg 1, wt11): Erdos946.erdos_946.variants.hildebrand_lower_bound

## Approach (Completely Elementary Uniform Proof of Hildebrand's x / (log log x)^3 Bound)
We avoid beta-sieve, Buchstab iterations, and Wirsing's theorem completely:
1. **Module 1 (Mertens 1 & 2 + inverse-square tail):** Elementary two-sided bounds
   `|sum_{p<=N} log p / p - log N| <= C1` and `|sum_{p<=N} 1 / p - log log N| <= C2`.
2. **Module 2 (Heath-Brown 7-point construction + Pigeonhole + Disjoint Family Reconstruction):**
   - 7 points `hb_a : Fin 7 -> Nat` (credit: @marcusbuffett PR #4914) with `a_j - a_i = gcd(a_i, a_j)` and divisor balance.
   - `seven_collision`: 7 positive naturals summing to `<= 27` have two equal.
   - Disjointness: if `a_i n + 1 = b_i * m_i * v_i` with `b_i = q_i^{e_i}` (`q_i <= z0`), `m_i` sqfree with primes in `(z0, z1]`, `omega(m_i) = k` independent of `i`, and `v_i > 1` sqfree with primes `> z1` and `sum omega(v_i) <= 27`, then `m = (m_1, ..., m_7)` is uniquely determined by `n`, so `T(m)` are pairwise disjoint and `sum_m |T(m)| <= 49 * erdos946Count(K * x)`.
3. **Module 3 (CRT + W0 pre-filtering + exact local root count `nu(d)`):**
   - Given valid `m`, find `h, M = prod b_i m_i`, and `t0 mod W0 = prod_{p <= z0} p` so that
     `L_i(u) = (a_i(h + M(t0 + W0 u)) + 1) / (b_i m_i)` has NO prime factors `<= z0`,
     exact local root count `nu(p) = 7` for `p > z0, p nmid M'`, `nu(p) = 1` for `p | M'`,
     and `|#{u in [1, U] : d | prod L_i(u)} - U * nu(d) / d| <= nu(d)`.
4. **Module 4 (Reciprocal mass lower bound):**
   - Restrict to 7-tuples `m` with `omega(m_i) = k` (for `|k - S| <= sqrt S`), primes in `(z0, z1]` (`z1 = x^{1/10000}`),
     pairwise coprime, `prod m_i <= x^{1/100}`, and `sum_{p | prod m_i} 1/p <= eps0 = 10^{-4}`.
   - Rankin's trick (with `alpha = 1 / log z1`) kills `prod m_i > x^{1/100}` loss; Markov's inequality kills `sum_{p | M'} 1/p > eps0` loss (since `E[sum_{p|m} 1/p] <= sum_{p>z0} 1/p^2 <= 1/z0`).
   - Stirling lower bound gives `sum_{m in M_good} 1 / (prod m_i) >= c * (log x)^7 / (log log x)^3`.
5. **Module 5 (Uniform Selberg Lambda^2 Weighted Sieve with F(t) = 1 - t):**
   - Exact Selberg diagonalization on squarefree `r <= R` coprime to `M'` with `P^-(r) > z0`, setting `y_r = mu(r) * (1 - log r / log R)`:
     - Identity 1: `sum h(lcm(d1, d2)) lam_{d1} lam_{d2} = sum g(r) y_r^2`.
     - Identity 2 (for `p > z0, p nmid M'`): `sum h(lcm(p, d1, d2)) lam_{d1} lam_{d2} = h(p) sum_{p nmid r} g(r) (y_r + y_{pr})^2`.
   - Elementary `S(R^t) / S(R) = t^7 + O(1 / log R)` from Mertens 1 via `8 * sum_{r<=X} g(r) log r = 7 (log X) S(X) + O(S(X))` and integrating `d(log I(X))`.
   - Exact closed-form integral at `alpha = 2` (`R = U^{1/4 - eps}`, `y = R^2 = U^{1/2 - 2eps}`):
     `7*(2+alpha)/alpha + 4609/360 - (28/5)/alpha + 7*(log alpha - 1 + 1/alpha) = 7381/360 + 7*log 2 = 25.355 < 28`!
   - Penalty `30 * sum_{p|P(u), p<=z1} 1` adds `O(delta^2 + eps0) < 0.1`, killing all primes `<= z1`.
   - Large prime-square loss (`p > z1, p^2 | L_i(u)`) is `O(U / z1 + sqrt x) = o(U / (log R)^7)` uniformly in `m`.
   - On surviving `u`, `omega(P(u)) <= 27` and `W(u) <= C (log R)^{14}`, yielding `|T(m)| >= c * x / (M * (log x)^7)`.

## Status
- Currently implementing Modules 1 and 2 in `proofs/Erdos946.erdos_946.variants.hildebrand_lower_bound.lean`.
