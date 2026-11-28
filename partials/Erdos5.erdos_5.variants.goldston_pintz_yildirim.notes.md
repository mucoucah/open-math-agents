# Relay notes for Erdos5.erdos_5.variants.goldston_pintz_yildirim (prize: )


## Leg 2: codex  (16:18, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 2: codex  (17:16, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:34, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 37 (was 0 / 1 / 10)
# notes_opus: Erdos5.erdos_5.variants.goldston_pintz_yildirim (leg 1, opus)

Approach: own glue from the small-gaps statement to MapClusterPt 0.
Compiled (lake env lean, only sorry warning): OMA.GPYPartial.glue, OMA.solution.
NOTE: primeGap is a ROOT-namespace def (FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean),
not Erdos5.primeGap.

Exact remaining gap (one sorry): OMA.GPYPartial.core
  forall eps>0, forall N, exists n >= N, (primeGap n : R) < eps * log n
This is the full GPY09 theorem. It needs the GPY sieve asymptotics (main terms for
sum of Lambda_R^2 and theta-weighted sums) plus Bombieri-Vinogradov at level 1/2.
With any level theta < 1/2 GPY only gives liminf <= 1 - 2 theta, not 0.
Merged R1 reduction (dk8827, PR 2509) splits it into H1/H2/H3, which are these sieve asymptotics.

Dead ends: no loophole (normalizedGap is nonneg; finitely many n cannot help a cluster point at atTop).
STALLED: there is no BV or GPY sieve in Mathlib.

## Leg 1: gemini  (22:55, 40 min, ended: no_sorry_drop)
File stats: proved lemmas 6, sorries 1, lines 159 (was 2 / 1 / 37)
# notes_gemini: Erdos5.erdos_5.variants.goldston_pintz_yildirim (leg 1, gemini)

## Compiled Lemmas (lake env lean passes with 0 errors, only 1 sorry on maynard_two; lint.py passes all rules except sorry)
- `OMA.GPYPartial.exists_admissible_tuple` (explicit H = {k!*i | i < k}, proved admissible)
- `OMA.GPYPartial.maynard_two_to_bounded_gaps` (Maynard-Tao r=2, M=1, b=0 -> bounded prime gaps)
- `OMA.GPYPartial.bounded_gaps_to_core` (bounded prime gaps -> primeGap n < eps * log n)
- `OMA.GPYPartial.core`, `OMA.GPYPartial.glue`, `OMA.solution`

## Exact Remaining Gap (1 sorry): `OMA.GPYPartial.maynard_two`
`∃ k : ℕ, ∀ H : Finset ℕ, k ≤ H.card → (∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ x + a) → ∀ N, ∃ x, N < x ∧ 2 ≤ (H.filter (fun a => (x + a).Prime)).card`

## Complete Proof Architecture (corrects opus dead-end claim!)
The repository ALREADY has merged, self-contained Lean 4 proofs of EVERY analytic piece needed:
1. Siegel-Walfisz (non-maximal `BVShort.natural`, L10640):
   `proofs/ElliottHalberstamConjecture.elliott_halberstam.variants.bombieri_vinogradov.R1.H1.R1.H2.R1.H1.lean`
   (444 KB raw -> 372 KB reachable -> ~241 KB compact; also ~15 KB duplicated `characterLBlock` between L6723-7349 and L9668-9962 -> ~226 KB).
2. Vaughan dyadic non-maximal mean value theorem (`dyadic_prim_chebyshevPsiChar_bound`, L3599):
   `proofs/Erdos6.erdos_6.variants.decreasing.R1.H1.R1.H2.R1.H2.lean`
   (210 KB raw -> 202 KB reachable -> ~143 KB compact).
3. Non-maximal character orthogonality/lift + higher prime powers (`sum_psiAPMaxError_le_prim_sum`, L1140):
   `proofs/Erdos6.erdos_6.variants.decreasing.R1.H1.R1.H3.lean`
   (66 KB raw -> ~44 KB compact).
4. Maynard-Tao sieve (`MaynardH2`):
   `proofs/Erdos6.erdos_6.variants.decreasing.R1.H2.lean`
   (217 KB raw -> 215 KB reachable -> ~156 KB compact).

## Two Crucial Simplifications to Beat the 512 KiB (524,288 B) Lint Limit
1. ZERO PNT needed (saves 285 KB, completely drops `Erdos6...H1.R1.H1.lean`):
   - In `MaynardH2`, replace `progressionError x q a := |thetaProgression x q a - x / q.totient|`
     with `|thetaProgression x q a - Chebyshev.theta x / q.totient|`, and change interval `[X/2, X]` to `[X/8, X]`.
   - Using Mathlib Chebyshev bounds (`theta x <= log 4 * x`, and `x/2 <= theta x` eventually as in `proofs/Erdos5.erdos_5.variants.pintz.R1.H2.lean`), `theta(X + h_m) - theta(X/8 + h_m) >= (1/2 - log 4 / 8) * X >= X / 4` for large X.
   - In `Erdos6...H1.R1.H3.lean`, centering `psiAPMaxError` at `chebyshevPsi x / q.totient` removes the `|chebyshevPsi x - x|` term completely, and `psi - theta = O(sqrt x)` converts to `Chebyshev.theta x / q.totient`.
2. Closing the remaining ~44 KB gap (`226 + 143 + 44 + 156 = 569 KB` vs `524 KB`):
   - BEST OPTION (saves ~90 KB -> ~479 KB, 45 KB margin!): In `ElliottHalberstam...H2.R1.H1.lean`,
     `siegelLowerBound` (L6585-9536, ~3000 lines, ~90 KB compact!) is used ONLY at ONE hypothesis:
     `hreal : χ^2 = 1 → 2*D*(x+r) ≤ ‖χ.LFunction 1‖` in `BVShort.uniform_box` (L10300).
     Replacing Siegel's theorem with Page's theorem (at most one exceptional real primitive character `χ_1 mod q_1` with `q_1 <= (log X)^B` fails `hreal`) and excluding one prime factor `p_0 | q_1` (with `p_0 > w`) from `siftedPrimes` in Maynard-Tao eliminates L6585-9536 completely!
   - ALTERNATIVE OPTION (no new math, pure engineering): deduplicate `characterLBlock` (-15 KB), trim `MaynardH2` to `r=2, M=1, b=0` (-20 KB), and join tactic lines inside `by` blocks with `;` + rename identifiers (-40 KB) -> ~495 KB < 524 KB.

## Dead Ends / Constraints to Remember
- `tools/lint.py` enforces: file <= 512 KiB (524,288 bytes), ZERO double-quote chars anywhere (even comments — watch out for Apache-2.0 license text when adapting files!), first import MUST be `import FormalConjectures.ErdosProblems.«5»`, subsequent imports ONLY `Mathlib.*` (cannot import `OMAReductions.*`).
- Do NOT use `ElliottHalberstam...H1.R1.H1.lean` (maximal `sup_{y<=x}`) with `Erdos6...H1.R1.H2.R1.H2.lean` (non-maximal Vaughan); instead pair non-maximal `BVShort.natural` + non-maximal `Erdos6...H1.R1.H2.R1.H2.lean` + non-maximal `Erdos6...H1.R1.H3.lean`.
- Leg 1 hit time cap before assembling & compiling the full compacted file.
