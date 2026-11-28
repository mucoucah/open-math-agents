# Relay notes for Erdos5.erdos_5.variants.merikoski_measure (prize: )


## Leg 2: codex  (16:26, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (18:08, 2 min, ended: exit)
File stats: proved lemmas 9, sorries 1, lines 248 (was 0 / 1 / 10)
# Erdos5 merikoski_measure, opus leg 3 notes
Approach: four-shift Merikoski Thm 1 (sieve core) + greedy measure argument (idea of merged R1 reduction).
Compiled (lake env lean, only warning = one sorry): OMA.Merikoski.theta_half, pi_ge, nth_prime_le,
log_ratio, transfer (from own wt16 merikoski file), four_shift, vol_Icc_ne_top, greedy_step, OMA.solution.
Remaining gap: ONE sorry merikoski_prime_norm = Me20 Thm 1 in log p_n normalisation (= merged R1.H1);
needs Maynard sieve + Bombieri-Vinogradov, not in Mathlib.
Dead ends: none new; glue is complete, do not redo it.
