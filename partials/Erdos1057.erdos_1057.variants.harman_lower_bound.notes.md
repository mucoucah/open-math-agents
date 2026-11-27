# Relay notes for Erdos1057.erdos_1057.variants.harman_lower_bound (prize: )


## Leg 2: codex  (16:24, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (17:56, 1 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 48 (was 0 / 1 / 10)
# Opus relay leg 3 notes: Erdos1057.erdos_1057.variants.harman_lower_bound

Approach: glue only. The target is Harman 2008 (C(x) > x^0.33336704) and is faithful, with no loophole
(IsCarmichael requires a composite number). The exact exponent 0.4736*0.7039 needs Lichtman beta < 0.2961
(see merged reduction R1 by LordMike: H1 = Lichtman Thm 1.1, H2 = AGP construction at level 0.4736).
Compiled (direct lake env lean, 2026-11-27): threshold (15/(32 sqrt e) < 0.2844), exponent_gap,
of_core (core implies target), OMA.solution := of_core core. Def SmoothShifted is for documentation only.
Remaining gap: ONE sorry, OMA.Harman1057.core:
  eventually x^(0.4736*(1-0.2844) - 1e-6) <= carmichaelCounting x
  (this is R1.H2 applied to R1.H1 at beta = 0.2844).
Dead ends: none worth trying in a relay leg. Research-scale analytic number theory, nothing for it
in Mathlib. Same picture as lichtman_lower_bound (wt10 glue, one sorry core).
Recommendation: STALLED; stop relay legs on this target.
