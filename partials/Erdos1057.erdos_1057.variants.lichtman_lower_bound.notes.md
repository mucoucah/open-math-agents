# Relay notes for Erdos1057.erdos_1057.variants.lichtman_lower_bound (prize: )


## Leg 1: gemini  (16:26, 3 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_gemini.lean)

## Leg 3: opus  (17:53, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 37 (was 0 / 1 / 10)
# notes_opus: Erdos1057.erdos_1057.variants.lichtman_lower_bound (leg 3)
Approach: statement is faithful (Mathlib IsCarmichael requires composite; ncard of finite set) -> full Lichtman 2022 Cor 1.2, no loophole.
Compiled (lake env lean, one sorry): OMA.Lichtman1057.lichtman_beta_lt (15/(32 sqrt e) < 0.2844), exponent_margin (0.3389 < 0.4736*(1-0.2844)-1e-6), OMA.solution glue from core.
Remaining gap: OMA.Lichtman1057.core : eventually x^(0.4736*(1-0.2844)-1e-6) <= carmichaelCounting x
  = Lichtman Thm 1.1 (smooth shifted primes, beta=0.2844, moduli to x^(17/32)) + AGP/Harman construction at level 0.4736. Not in Mathlib; research scale.
Dead ends: none worth retrying; merged R1 (H1 Lichtman, H2 AGP-Harman) already holds the clean split. Report STALLED/FAILED fast.

## Leg 1: gemini  (04:00, 44 min, ended: no_sorry_drop)
File stats: proved lemmas 3, sorries 1, lines 37 (was 3 / 1 / 37)
(the model wrote no notes; see partial_gemini.lean)
