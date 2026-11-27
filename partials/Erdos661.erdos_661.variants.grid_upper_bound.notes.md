# Relay notes for Erdos661.erdos_661.variants.grid_upper_bound (prize: $50)


## Leg 1: grok  (23:19, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (23:22, 2 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 116 (was 0 / 1 / 10)
# notes_opus (leg 2) Erdos661 grid_upper_bound
Approach: grid of k^2 points, k = sqrt(2n)+1; split 2n of them into halves; cross distances are sqrt(m),
m <= N := 2k^2 a sum of two squares. So F(n) <= #S2(N), with 2n <= k^2 <= 7n.
COMPILED (proofs file, namespace OMA661): S2, gp, gp_inj, dist_gp, cross_le, and the full glue OMA.solution
(uses landau_upper + cross_le, constant |C|*14). Compiles via lake env lean with ONE sorry.
EXACT REMAINING GAP: lemma OMA661.landau_upper :
  exists C, forall N >= 2, #(S2 N) <= C * N / sqrt(log N)   (Landau 1908 upper bound; not in Mathlib).
Fast compile: cd repo/.oma/formal-conjectures; lake env lean <abs path>  (about 10 s).
Dead ends: no loophole (F is a genuine sInf; best known construction is the grid).
Route idea for landau_upper: S(x) log x <= sum_m f(m) theta_allowed(x/m) + O(x), needs
sum_{p<=y, p=1 mod 4} log p / p <= (1/2) log y + O(1) (Mertens in APs, exact 1/2 constant);
Chebyshev constant c<1 is NOT enough (gives x (log x)^(c-1)). Check merged proofs dirs for a
Mertens-in-AP / Dirichlet-density port before starting (see PNT port memory).

## Leg 3: codex  (23:29, 7 min, ended: stalled)
File stats: proved lemmas 18, sorries 1, lines 296 (was 4 / 1 / 116)
# Codex relay notes
Approach: elementary convolution bound instead of Mertens in progressions. Let g be the completely multiplicative indicator of positive integers with every prime factor 1 mod 4, and h = 1 * chi4 in Dirichlet convolution. On g-supported n, (g*g)(n) = h(n) = d(n), and off support g*g vanishes while h is nonnegative (check prime powers). Alternation gives sum_{n<=x} h(n)/n <= 1+log x by reindexing. Apply this at x=N² to bound (sum_{n<=N} g(n)/n)². The von Mangoldt logarithm identity and Chebyshev.psi_le_const_mul_self then give sum_{n<=N} g(n) = O(N/sqrt(log N)). Mathlib Nat.eq_sq_add_sq_iff_eq_sq_mul reduces S2 to a²*b with b or b/2 good, since 4 cannot divide b. Sum the resulting bounds over a.
Compiled from previous leg: gp_inj, dist_gp, cross_le, OMA.solution modulo landau_upper.
Current gap: formalizing the analytic estimate and transfer to S2. No Mertens-in-AP port found in proofs or reductions. The Chebyshev-only Mertens shortcut from the earlier notes has the wrong log exponent.

## Site hints (2026-11-26)

https://www.erdosproblems.com/661 (YAML: open — whether F(n) = o(n/√(log n)) is still open). This variant is the elementary upper bound: 2n points of a square grid determine O(n/√(log n)) distinct distances by Erdős 1946; splitting into two n-point halves gives F(n) = O(n/√(log n)). Follow that grid argument. Write-up: /workspace/left-to-solve/research/erdosproblems.md

## Leg 4: fable  (23:34, 5 min, ended: stalled)
File stats: proved lemmas 18, sorries 1, lines 296 (was 18 / 1 / 296)
# notes_fable (leg 4) Erdos661 grid_upper_bound
Approach (continuing codex plan, all elementary): g = goodWeight, G(N) = sum_{n<=N} g(n)/n.
 L1 altsum: sum_{b<=M} chi4(b)/b <= 1 (induction on M with mod 4 strengthening).
 L2 sum_{n<=N} divSumChi4(n)/n <= 1 + log N (sum_mul_pairs + L1 + harmonic_le_one_add_log).
 L3 G(N)^2 <= 1 + 2 log N (goodWeight_sq_le + sum_mul_pairs at N^2).
 L4 sum_{n<=N} g(n) log n <= K N G(N) (vonMangoldt_sum, g(dm)<=g(m), Chebyshev.psi_le_const_mul_self).
 L5 for b>=1: A(N/b) log N <= (N/b)((1+K) G(N) + log b), A(M) = sum_{c<=M} g(c); uses log(N/(bc)) <= N/(bc).
 L7 transfer: #S2(N) <= 1 + 2 sum_{a in Icc 1 N} A(N/a^2) (sumsq_goodPart).
 L8 sum over b = a^2: sum 1/a^2 <= 2, log(a^2) <= 4 sqrt a, sum 1/(a sqrt a) <= Z (rpow 3/2 summable).
Status: see bottom (updated as lemmas compile).
