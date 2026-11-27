# Relay notes for CramerConjecture.cramer_conjecture.variants.baker_harman_pintz (prize: )


## Leg 2: codex  (17:05, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (17:48, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 56 (was 0 / 1 / 10)
# notes_opus: CramerConjecture.cramer_conjecture.variants.baker_harman_pintz (leg 3)
Approach: glue from a short-interval prime theorem to the indexed gap bound.
Compiled (lake env lean, only sorry warning): OMA.BHP.glue (any C>0 with eventually a prime in [x, x+C x^0.525] gives primeGap = O(p_n^0.525), constant 1+2C), OMA.solution (from bhp_interval + glue).
Remaining gap: ONE sorry OMA.BHP.bhp_interval = Baker-Harman-Pintz 2001 (prime in [x, x+C x^0.525]). This is the full BHP sieve/zero-density theorem, not in Mathlib; infeasible.
Dead ends: statement faithful, no loophole (=O on atTop with genuine exponent 0.525; Bertrand only gives O(p_n)). Merged R1/R1.H1.R1 reductions leave the same BHP core (R1.H1.R1.H1).
Copy: .oma/scratch/partial_opus_bhp.lean
