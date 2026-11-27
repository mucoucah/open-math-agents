# Relay notes for Erdos1107.erdos_1107.variants.two (prize: )


## Leg 1: gemini  (16:20, 3 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (17:15, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:28, 2 min, ended: exit)
File stats: proved lemmas 6, sorries 1, lines 67 (was 0 / 1 / 10)
# notes_opus: Erdos1107.erdos_1107.variants.two (Heath-Brown 1988, sums of three 2-full numbers)
Approach: glue OMA.solution to a single core lemma: eventually n = q^3 x^2 + y^2 + z^2.
Compiled (lake env lean, only sorry is core): full_sq, full_mul, full_cube_mul_sq, of_three, four_mul, OMA.solution glue.
Remaining gap: OMA.E1107two.core (the ternary local-global step). This is Heath-Brown / Blomer theta-series uniformity
(same as H2 of the merged reduction reductions/Erdos1107.erdos_1107.variants.two.R1.lean; H1 = Chebyshev 7 mod 8 is merged).
Dead ends: Mathlib has NO Legendre three-squares theorem (grep three_sq: none), so even the n != 4^a(8b+7) case is out of reach.
Elementary mod-8 tricks fail: n = 7 mod 8 needs an odd non-square 2-full term (27, 125, 343, ...); the remaining two terms
then need a sum-of-two-squares (binary) representation, i.e. sieve. Forms x^2+y^2+8z^2 and x^2+y^2+2z^2 (z even) miss 7 mod 8.
x^2+y^2+27z^2 is not known regular; proving regularity is infeasible anyway.
