# Relay notes for Erdos186.erdos_186.variants.pham_zakharov (prize: )


## Leg 2: codex  (16:26, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (18:10, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 40 (was 0 / 1 / 10)
# Erdos186 pham_zakharov - opus leg 3
Approach: split on epsilon. Target is the full Pham-Zakharov 2024 theorem (faithful, no loophole;
F N >= c N^{1/4} by Bosznay, so the statement is sharp).
Compiled (lake env lean, only warning = sorry in small_eps): OMA.F_le (F N <= N), OMA.large_eps
(eps >= 3/4 case), OMA.solution glue.
Remaining gap: ONE sorry OMA.small_eps (0 < eps < 3/4). For 1/4 < eps < 3/4 it would follow from
Erdos-Sarkozy (N log N)^{1/2}; merged proofs/Erdos186...erdos_sarkozy.lean is 6834 lines by another
contestant (cannot copy, proof files are not importable). eps <= 1/4 needs the PhZa24 argument itself.
Dead ends: no finite or trivial route; do not retry fast passes.
