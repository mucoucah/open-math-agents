# Relay notes for KaplanskyUInvariant.u_invariant_values.variants.nine (prize: )


## Leg 2: codex  (16:16, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 2: codex  (17:12, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:24, 1 min, ended: exit)
File stats: proved lemmas 5, sorries 1, lines 54 (was 0 / 1 / 10)
# notes_opus: KaplanskyUInvariant.u_invariant_values.variants.nine (leg 1, opus)
Approach: glue reduction. Target = Izhboldin 2001 (Ann. Math. 154, 60 pages, motivic cohomology,
Rost degree formula, iterated function-field tower). Formalization is faithful (anisotropicDims =
nondegenerate anisotropic forms on Fin n -> F, char not 2, IsGreatest); no loophole.
Compiled (direct lean, 7 s): OMA.Nine.zext, zext_apply_castLE, zext_injective,
  mem_of_le (anisotropicDims downward closed in char not 2), isUInvariant_nine_of
  (9 in dims and 10 not in dims gives IsUInvariant 9), OMA.solution from the core.
Exact remaining gap: ONE sorry OMA.Nine.izhboldin_core :
  exists F field, NeZero 2, 9 in anisotropicDims F and 10 not in anisotropicDims F.
  This is the entire content of Izhboldin's theorem; not formalizable in a leg (needs
  Merkurjev-type tower constructions plus Izhboldin's 9-dim form incompressibility results).
Dead ends: no loophole (universe Type harmless, NeZero 2 required, nondegenerate auto).
Verdict: STALLED / FAILED fast pass.

## Leg 1: gemini  (20:51, 20 min, ended: cap20_sorry_unchanged)
File stats: proved lemmas 30, sorries 1, lines 739 (was 5 / 1 / 54)
(the model wrote no notes; see partial_gemini.lean)
