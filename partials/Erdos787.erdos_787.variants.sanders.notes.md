# Relay notes for Erdos787.erdos_787.variants.sanders (prize: )


## Leg 2: codex  (17:09, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (17:53, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 32 (was 0 / 1 / 10)
# Erdos787.erdos_787.variants.sanders, leg 3 (opus)
Approach: target is the full Sanders 2021 theorem (g(n) >= (log n)^(1+c)), faithful, no loophole
(c > 0 fixed, g is the real sSup, le_g upstream gives the lower-bound direction).
Compiled (lake env lean, one sorry): OMA.sanders_of_core (glue via Erdos787.le_g + Nat.le_ceil),
OMA.solution := sanders_of_core sanders_core.
Remaining gap: OMA.sanders_core = every n-set of reals has a sum-avoiding subset of size
ceil((log n)^(1+c)) for large n. This is the whole 45-page Sanders paper (Croot-Sisask almost
periodicity + Bogolyubov-type arguments for k-configurations); not in Mathlib.
Dead ends: Klarner greedy only gives c*log n (merged klarner file); no way to get the extra
(log n)^c without Sanders / Beker. FAILED fast pass.
