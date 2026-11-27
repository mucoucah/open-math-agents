# Relay notes for Erdos30.erdos_30.variants.O_one (prize: $1000)


## Leg 1: grok  (05:31, 32 min, ended: max25)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 1: opus  (10:13, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_opus: Erdos30.erdos_30.variants.O_one
Approach: none viable. The target is (h N - sqrt N) =O[atTop] 1, with h N = maxSidonSubsetCard (Icc 1 N) cast to R.
It is the faithful open Erdos conjecture h(N) = sqrt N + O(1). No loophole: standard IsSidon, real subtraction, no
degenerate filter.
Compiled: nothing new. The file is unchanged (one sorry in OMA.solution).
Gap: the whole open conjecture. You would need both |h N - sqrt N| <= C above and below, but the best known error
terms are about N^(1/4) above and N^0.2625 below.
Dead ends: there is no loophole. A wt17 glue split into upper_O1 and lower_O1 compiled, but both halves are open.
Recommendation: stop the relay.

## Leg 2: codex  (10:19, 6 min, ended: exit)
File stats: proved lemmas 10, sorries 1, lines 270 (was 0 / 1 / 10)
Approach: interpolate between consecutive squares using monotonicity of h, then convert to quadratic interval length with linear error in the number of marks. A CRT proof of Ruzsa's construction gives the existence bound at m = p − 1. Taking subsets covers any fixed distance d below these sizes.
Compiled: fits_iff_le_h, h_monotone, h_le_length, sqrt_bracket, bounded_error_at_squares_iff, square_envelope_iff_linear_packing, fits_before_prime, Fits.mono, fits_near_prime, linear_packing_iff_away_from_primes. The final Lean audit reported only propext, Classical.choice, Quot.sound for the square and packing equivalences and the prime construction.
Exact gap: the sole sorry requires a universal c with (1) an m-element Sidon set in [1,m²+c m] whenever neither m+1 nor m+2 is prime, and (2) m² ≤ N+c m for every m-element Sidon set in [1,N]. The equivalence holds for any fixed d in place of the selected d = 1.
Dead ends: the previous real upper/lower split left both open. A fourth-root error in h gives superlinear error in interval length. Fixed-distance interpolation from primes alone leaves arbitrarily long gaps, as seen from consecutive integers following a factorial.
CI verdict: rejected, lint: forbidden: 'sorry'. Direct Lean compilation succeeded with the one expected warning.

## Leg 2: codex  (16:07, 0 min, ended: exit)
File stats: proved lemmas 10, sorries 1, lines 270 (was 10 / 1 / 270)
(the model wrote no notes; see partial_codex.lean)
