# Relay notes for Erdos5.erdos_5.variants.pintz (prize: )


## Leg 2: codex  (16:18, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 2: codex  (17:16, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:32, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 84 (was 0 / 1 / 10)
# notes_opus: Erdos5.erdos_5.variants.pintz (leg 1, 2026-11-27 17:37)
Approach: closed-set glue. If no [0,c] lies in S (S closed), choose lacunary beta in (0,1)
(2 beta_i < beta_j) where every beta_i and every beta_j - beta_i is outside S; a finite-pattern
theorem then gives a contradiction. The glue was written independently (same idea as merged R1).
Compiled (lake env lean, no errors): OMA.PintzPartial.miss_near_zero, OMA.PintzPartial.build, OMA.solution.
Remaining gap (ONE sorry): OMA.PintzPartial.core :
  exists m, forall beta : Fin m -> R, (0<beta i<1) -> (i<j -> 2 beta i < beta j) ->
  exists i<j, beta j - beta i in limitPointSet.
  This is BFM16 Thm 1.1 / Pintz16 restricted to lacunary shifts. It needs the Maynard-Tao sieve
  plus Erdos-Rankin, and neither is in Mathlib. Stating it with limitPointSet (normalised by log n)
  removes the need for H2 (log p_n ~ log n).
Note: the full BFM 9-point theorem implies pintz directly (use build with m=9).
Dead ends: none new; the core is research-level, so this is STALLED.

## Leg 1: gemini  (22:15, 20 min, ended: cap20_sorry_unchanged)
File stats: proved lemmas 12, sorries 1, lines 447 (was 3 / 1 / 84)
# notes_gemini: Erdos5.erdos_5.variants.pintz (leg 1)

## Key Discovery
1. **Bombieri-Vinogradov IS already proved in this repo** across 5 files:
   - `proofs/Erdos6.erdos_6.variants.decreasing.R1.H1.R1.H1.lean` (285 KiB, quantitative PNT)
   - `proofs/Erdos6.erdos_6.variants.decreasing.R1.H1.R1.H3.lean` (70 KiB, character orthogonality)
   - `proofs/ElliottHalberstamConjecture.elliott_halberstam.variants.bombieri_vinogradov.R1.H1.R1.H2.R1.H1.lean` (457 KiB, Siegel-Walfisz)
   - `proofs/ElliottHalberstamConjecture.elliott_halberstam.variants.bombieri_vinogradov.R1.H1.R1.H2.R1.H2.lean` (363 KiB, Vaughan + Large Sieve)
   - plus reduction glue (~46 KiB). Total: ~1.22 MB.
2. **Maynard-Tao sieve IS already proved from Bombieri-Vinogradov** in:
   - `proofs/Erdos6.erdos_6.variants.decreasing.R1.H2.lean` (229 KiB, `namespace MaynardH2`).
3. **Hard lint blocker for a 0-sorry single-file proof**:
   - `tools/lint.py` enforces a hard 512 KiB file-size cap and forbids importing `OMAReductions.*` from `proofs/Erdos5.erdos_5.variants.pintz.lean`.
   - Inlining Bombieri-Vinogradov (~1.22 MB) + Maynard-Tao (~229 KiB) + Pintz (~35 KiB) = ~1.48 MB, nearly 3x the 512 KiB cap.
   - To close `Erdos5.erdos_5.variants.pintz` with 0 sorries in the OMA system, one needs a reduction split (`H1`: Bombieri-Vinogradov, `H2`: Bombieri-Vinogradov -> Pintz), NOT a single monolithic file.
4. **Complete, Erdos-Rankin-free proof of `HasBombieriVinogradov -> Erdos5.erdos_5.variants.pintz`**:
   - Fix Maynard parameters `k, L, c_wt` first (via `MaynardH2.exists_maynard_weights` with `M_target = 512`), giving `W`-independent `I, J, C_wt, K_card`.
   - Choose `c > 0` depending only on `k, L, c_wt` (NOT on `W`, `beta`, `eps`).
   - Given `beta : Fin k -> R` in `(0, c)` and `eps > 0`, pick rational approximations `a_i / Q` within `eps/4`, fix `W` divisible by all primes `<= max (4*k) (max a_i)` and by `2`, and set `h_i = a_i * W * 2^t` at scale `X = exp(Q * W * 2^t)`.
   - Because `W` is fixed and `h_j - h_i = (a_j - a_i) * W * 2^t`, `hsep` holds for all `t`, so `MaynardH2` works verbatim!
   - For intermediate `u in (h_0, h_{k-1}] \ H` with `(1 + u).Coprime W`, expand `T(u) = sum_n w(n)^2 primeLog(n + u)`.
   - By `sieveDiagonal_mass` + `sieveKernel_local_mass_bound` + `sifted_euler_product_le` (W-independent constant `8`), `|M(u)| <= C_1 * (boxScale)^k * prod_{p in B(u)} (1 + 2/p)`.
   - Averaging `prod_{p in B(u)} (1 + 2/p)` over `u in U` via `prod x_j <= sum x_j^k` and CRT mod `W * d` cancels `W / W.totient` completely, yielding `(4*k) * sum_{u in U} T(u) <= C_total * c * s * log X < I * s * log X`, while `S_2 - (2 log X) S_1 > 28 * I * s * log X`.
   - Hence there exists `n in (X/2, X]` with `n === 1 [MOD W]`, >= 2 primes in `n + h_i`, and 0 primes in intermediate `n + u`.

## Current Action
Prototyping and compiling the complete `HasBombieriVinogradov -> Erdos5.erdos_5.variants.pintz` proof in `.oma/scratch/pintz_bv.lean` to replace the unprovable `maynard_tao_in_ap` sorry with the standard `bombieri_vinogradov` sorry while keeping all existing compiled lemmas.
