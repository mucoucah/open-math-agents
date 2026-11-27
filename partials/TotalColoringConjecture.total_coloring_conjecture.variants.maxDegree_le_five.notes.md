# Relay notes for TotalColoringConjecture.total_coloring_conjecture.variants.maxDegree_le_five (prize: )


## Leg 2: codex  (16:16, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 2: codex  (17:13, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:25, 2 min, ended: exit)
File stats: proved lemmas 27, sorries 1, lines 934 (was 0 / 1 / 10)
# notes_opus: TotalColoring maxDegree_le_five (relay leg 1, opus)

Approach: the 10-line stub in the proof file was replaced by OUR earlier partial
(lemmas/partial/...maxDegree_le_five.ref.lean). Header and OMA.solution line kept exactly; `import Mathlib` added as line 2.
Compiles (lake env lean, 45 s) with ONE sorry: `OMATC.core_colorable` (line 907).

Proved lemmas (all compile): Good, totalColorable_of_good, tcn_le, case_zero, case_one,
fin2 (decide over Fin 4), step2, case_two (Delta=2), stepD (greedy add of a vertex with <=2 S-neighbours, D>=3),
reduce_to_core, swapC*, kempe_swap, kempe_component, core_three_closed, case_high (modulo core).

Remaining gap: core_colorable = for 3<=Delta<=5, total (Delta+2)-colouring of every induced S with min degree >=3.
 - Delta=3: proved upstream by another contestant (merged R1.H1, PR 8576; maximal matching M plus list edge-colouring
   lemma lem2 for q=Delta+1 in {3,4}, cycle list colouring cyc_col). HINTS ONLY: re-deriving it is ~900 lines.
 - Delta=4,5: Kostochka 1977/1996. Infeasible. The matching idea needs lem2 for q=5,6, a Vizing-type list statement
   (cyc_col breaks for q>=5); unproven and possibly false.
Dead ends: see memory total-coloring-maxdeg5-dead-ends (radius-1 decide fails for Delta=3; Kempe needs <=2 swaps).
