# Relay notes for Green97.green_97.variants.bowtell_keevash (prize: )


## Leg 3: opus  (17:46, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 60 (was 0 / 1 / 10)
# notes_opus (relay leg 3, wt16): Green97.green_97.variants.bowtell_keevash

Approach: statement audited, faithful (numToroidalQueens is an honest count of Perm (Fin n) with
injective sigma i - i and sigma i + i in ZMod n; filter atTop inf n%6 in {1,5}); no loophole.
It is the full Bowtell-Keevash 2021 theorem (entropy upper bound + random greedy/absorber lower bound).

Proofs file (compiles via lake env lean, ONE sorry):
- OMA.BK.log_asymp (sorry): log T(n)/n - log n -> -3 along toroidalDegrees  (the whole theorem)
- OMA.BK.eventually_pos (compiled): log asymptotic implies T(n) > 0 eventually (T=0 gives -log n)
- OMA.BK.glue (compiled): exp of the log asymptotic gives T(n)^(1/n)/n -> exp(-3)
- OMA.solution := glue log_asymp
Remaining gap: log_asymp = merged R1.H1 (upper) and R1.H2 (lower) combined.
Dead ends: trivial T(n) <= n! only gives -1 not -3; sigma(i)=2i only gives T(n) >= 1.
RESULT: STALLED (blocker: log_asymp, the full BoKe21 theorem).
