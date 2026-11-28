# Relay notes for Erdos507.erdos_507.variants.upper_cpz24 (prize: )


## Leg 2: codex  (16:28, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (18:17, 1 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 85 (was 0 / 1 / 10)
# notes_opus: Erdos507.erdos_507.variants.upper_cpz24 (leg 3)
Approach: target is faithful (IsBigO atTop, real Heilbronn alpha, o -> 0); no loophole
(alpha >= 0 genuine, trivial bound only gives exponent -1). Needs full CPZ24 incidence theorem.
Compiled (lake env lean, one sorry): OMA507.alpha_nonneg, OMA507.oFun (diagonal exponent
max 0 (log(alpha n * n^(7/6))/log n)), OMA507.oFun_tendsto, OMA507.alpha_le, OMA.solution glue (C=1).
Remaining gap: OMA507.cpz_core : forall eps>0, eventually alpha n * n^(7/6) <= n^eps  (= CPZ24 itself).
Dead ends: none elementary; KPS81 8/7 is also deep; do not retry fast passes. STALLED.
