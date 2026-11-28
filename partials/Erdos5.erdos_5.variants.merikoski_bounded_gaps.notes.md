# Relay notes for Erdos5.erdos_5.variants.merikoski_bounded_gaps (prize: )


## Leg 1: gemini  (16:29, 3 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_gemini.lean)

## Leg 3: opus  (18:14, 1 min, ended: exit)
File stats: proved lemmas 8, sorries 1, lines 211 (was 0 / 1 / 10)
# notes_opus: Erdos5.erdos_5.variants.merikoski_bounded_gaps (leg 3, opus)

Approach: Me20 Cor 3 from Me20 Thm 1 (four shifts). If S had holes of every length,
hole_map gives g with x <= g x and g x - y not in S for 0 <= y <= x; take
beta = ![0, g 0, g (g 0), g (g (g 0))]; every difference lies in a hole, which contradicts four_shift.

Compiled (lake env lean, one sorry): theta_half, pi_ge, nth_prime_le, log_ratio, transfer,
four_shift, hole_map, OMA.solution (full glue). Helpers come from our own merikoski_measure partial.

Remaining gap: the single sorry merikoski_prime_norm = Merikoski Thm 1 in the log p_n normalisation
(Maynard sieve + Bombieri-Vinogradov, not in Mathlib). Same blocker as merikoski / merikoski_measure.
Dead ends: no loophole (the statement is faithful). Merged R1 already splits into H1 (pattern) + H2 (scale, proved).
