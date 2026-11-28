# Relay notes for Erdos5.erdos_5.variants.hildebrand_maier (prize: )


## Leg 2: codex  (16:19, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 2: codex  (17:16, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:35, 2 min, ended: exit)
File stats: proved lemmas 5, sorries 1, lines 149 (was 0 / 1 / 10)
# notes_opus (leg 1) hildebrand_maier
Approach: glue. OMA.solution <- OMA.HM.windows (bounded window [A, 40/c] of normalizedGap hit
frequently) <- OMA.HM.core (density) + sum_gaps + nth_le (p_n <= 5 n log n via Chebyshev.pi_ge').
Compiled (lake env lean, only warning = sorry in core): OMA.HM.sum_gaps, log_small, nth_le,
windows, OMA.solution.
EXACT remaining gap: ONE sorry, OMA.HM.core :
  forall A>0, exists c>0, eventually N, c*N <= #{n<N : A*log n < primeGap n}
(positive density of large prime gaps at index scale; Maier matrix method / Bombieri-Vinogradov,
cf. reduction R1.H1.R1.H1.R1 open PR 13680). Research-level, not in Mathlib.
Dead ends: none new; core is the whole deep content (HiMa88 / Maier). No loophole: target is faithful.

## Leg 1: gemini  (23:23, 20 min, ended: cap20_sorry_unchanged)
File stats: proved lemmas 5, sorries 1, lines 149 (was 5 / 1 / 149)
# notes_gemini (leg 1) — Erdos5.erdos_5.variants.hildebrand_maier

## Current file status (kept intact)
`proofs/Erdos5.erdos_5.variants.hildebrand_maier.lean` (149 lines, 1 sorry):
- Compiled lemmas: `OMA.HM.sum_gaps`, `OMA.HM.log_small`, `OMA.HM.nth_le`, `OMA.HM.windows`, `OMA.solution`.
- Single remaining sorry: `OMA.HM.core` (positive lower density of prime gaps `> A * log n`).
- Target statement is faithful (no loophole).

## Repo inventory of relevant merged proofs (reusable with credit)
- Full **Bombieri-Vinogradov** is completely proved across the merged tree `ElliottHalberstamConjecture.elliott_halberstam.variants.bombieri_vinogradov.{R1, R1.H2, R1.H1.R1, R1.H1.R1.H1, R1.H1.R1.H2.R1, R1.H1.R1.H2.R1.H1, R1.H1.R1.H2.R1.H2}` (note: `R1.H1.R1.H2.R1.H1` is 10,777 lines of Siegel-Walfisz only; no Deuring-Heilbronn or log-free zero-density).
- Full **Maynard-Tao** (for fixed admissible `(H, M, b)` given BV) is proved in `proofs/Erdos6.erdos_6.variants.decreasing.R1.H2.lean` (4,379 lines).
- Full **Westzynthius covering** (`OMA.one_by_one`, `OMA.greedy`, `OMA.cover`, `OMA.crt`) is proved in `proofs/Erdos5.erdos_5.variants.westzynthius.lean`.
- Full **Selberg 2D upper bound sieve** for prime pairs is proved in `proofs/Erdos5.erdos_5.variants.erdos_ricci.lean`.
- Quantitative PNT (`effective_pnt_psi1`) + Perron/Landau/Blaschke machinery in `proofs/Erdos6.erdos_6.variants.decreasing.R1.H1.R1.H1.lean`.

## Dead ends / mathematical barriers verified
1. **Standard Bombieri-Vinogradov or Siegel-Walfisz alone is insufficient**:
   - To create a prime-free interval of length `A * log X` for arbitrarily large `A`, even optimal Erdős-Rankin / Westzynthius covering requires a primorial modulus `P(z) = ∏_{p ≤ z} p` with `z ≫ log X / log log X` (Westzynthius: `z = ε log X`), so `log P(z) ≫ log X / log log X`.
   - Siegel-Walfisz only covers `log q ≪ log log X`.
   - Classical zero-free region (Page/Landau) only covers `log q ≪ sqrt(log X)`.
   - Standard BV has error `X / (log X)^A`, which is larger than `X / φ(P(z))`, so summing BV over multiples of `P(z)` gives no lower bound.
   - Fixing a constant modulus `Q` (or `Q ≤ (log X)^K`) fails by the Fundamental Lemma of the Sieve: `u = log(A log X) / log z → ∞`, so every shift `b` leaves `(1+o(1)) A log X · φ(Q)/Q` rough numbers, and the `φ(Q)/Q` factor cancels in the Selberg upper bound.
   - Taking `z = sqrt(2 A log X)` (at the Page boundary `u = 2`) only gives `ω(2) = 1/2` vs `e^{-γ} ≈ 0.561` and requires `2 A < c₀` (fails for large `A`).
2. **Fixed-tuple Maynard-Tao (`Erdos6...R1.H2`)**: produces `O(1)` gaps (`0 ∈ limitPointSet`), not gaps of size `[A log X, B log X]`. For growing tuples with `h_j - h_i ≈ (β_j - β_i) log X`, ruling out intermediate primes requires Erdős-Rankin + BV for a fixed smooth modulus `B ≤ X^δ` saving `φ(B)` in the error (BFM 2016 Theorem 4.2), which again requires log-free zero-density + Deuring-Heilbronn.
3. **Erdős-Ricci (`erdos_ricci.lean`) + Westzynthius (`westzynthius.lean`)**: Erdős-Ricci upper bounds small gaps (compatible with all gaps `≤ 2 log X`), while Westzynthius gives no `O(log X)` upper bound on the constructed gap.

## Cleanest blueprint to finish (exact remaining blocker)
To prove `OMA.HM.windows` directly (without even needing full-density `OMA.HM.core`):
1. Use Westzynthius (`westzynthius.lean`) with `z = ε log X` (`P = ∏_{p ≤ 2z} p ≤ X^{1/D}`) to construct `k - 1` prime-free holes of length `A log X` separated by `k` intervals `I_1, ..., I_k` of length `B log X` containing `≫ (φ(P)/P) log X` coprime shifts.
2. **BLOCKER — Gallagher's theorem (1970)**: PNT in APs for good moduli `P ≤ X^{1/D}` (after deleting at most one exceptional prime factor `q₀` from a possible Siegel zero) to show `E_m[#primes in I_i] ≥ 10`. Requires:
   - explicit formula / partial fraction for `-L'/L(s, χ)` and zero counting `N(T, χ) ≪ T log(qT)`,
   - Deuring-Heilbronn zero repulsion,
   - Linnik/Gallagher log-free zero-density estimate `∑_{q ≤ Q} ∑^*_χ N(σ, T, χ) ≪ (Q^2 T)^{c(1-σ)}`.
3. Adapt Selberg 2D upper bound sieve (`erdos_ricci.lean`) to progressions mod `P` to get `E_m[(#primes in I_i)^2] ≤ C_sieve (E_m[#primes in I_i])^2`, so by Paley-Zygmund `P(I_i has a prime) ≥ 1 / C_sieve`.
4. Choose `k = C_sieve + 1`: by pigeonhole, some row `m ∈ (M, 2M]` has primes in two distinct `I_i, I_j` straddling a prime-free hole of length `A log X`, giving a prime gap in `[A log X, k(A + B) log X]`.

None of Gallagher's theorem (log-free zero-density + Deuring-Heilbronn) exists in Mathlib or this repo; formalizing it from scratch is multi-thousand-line research-level analytic number theory, beyond a 20-minute leg.
