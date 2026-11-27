# Relay notes for Erdos827.erdos_827.variants.n_five_le (prize: )


## Leg 2: codex  (16:16, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 2: codex  (17:14, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:29, 3 min, ended: exit)
File stats: proved lemmas 6, sorries 2, lines 121 (was 0 / 1 / 10)
# notes_opus Erdos827 n_five_le (leg 1, opus, 17:30)
Approach: own rewrite of the merged R1 reduction structure (Javi #4669), relational (uses
OnCircleOfRadius directly, no choice function, so no circle-existence lemma needed).
COMPILED (namespace OMA.E827N5): pt_two, radius_unique, radius_unique_card, no_four,
chord_bound (fixed chord has <=2 completions of a radius, from general position), and the full
glue OMA.solution (sorry-free itself).
REMAINING (2 sorries):
 1. rainbow_core: purely combinatorial (relation R with unique values, <=2 completions per pair,
    <=12 equal-valued triangles per vertex => rainbow 5-set in 37 points). This is merged R1.H2
    (Marcus Buffett #4926, 355 lines: shadow_budget / link_budget / vertex_fiber / edge_fiber).
    Hint only, must rewrite. Naive union bound FAILS: edge-bad pairs <=666*17, *33 five-sets =
    373626; vertex-bad <=37*630*11/2 = 128205; total 501831 > C(37,5)=435897. Need: count bad
    4-sets (not pairs) for edge overlaps, and subtract adjacent pairs in vertex classes (link of a
    class is a max-degree-2 graph).
 2. dense_core: vertex a with >=13 triangles of one radius r. This is R1.H3 = genuine gap of
    MaRo15 (their count ignores edge-sharing pairs). Open; no idea yet. Only geometric fact
    available: the 13 pairs form a max-degree-2 graph (chord_bound) with distinct centers on the
    circle of radius r around a.
Dead ends: none beyond the naive union bound above.
