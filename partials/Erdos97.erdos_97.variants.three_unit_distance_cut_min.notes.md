# Relay notes for Erdos97.erdos_97.variants.three_unit_distance_cut_min (prize: $100)


## Leg 1: grok  (00:21, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (00:22, 1 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos97 three_unit_distance_cut_min, leg 2 (opus)

Target: sInf {n | convex n-gon V with cut A,B (disjoint convex hulls), every a in A has >=3 unit
neighbours in B and vice versa} = 20. This is the FULL Fishburn-Reeds 1992 result, in two parts:
 (1) upper: an explicit convex 20-gon with such a cut (algebraic coordinates; need exact
     unit-distance checks, a ConvexIndep proof and a cut proof by separating line);
 (2) lower: no such configuration for n <= 19. FiRe92 does this by computer-assisted
     case analysis of bipartite unit-distance graphs in convex position. That is not feasible in Lean in a session.
Faithfulness: the statement matches the paper. I see no loophole: sInf of a nonempty set needs (1), and the value 20 needs (2).
Note: wt10/proofs/Erdos97.erdos_97.variants.three_unit_distance.lean (KKP 2026, any k) gives
existence for large k but NO cut and no size control. It is useless for the exact value 20.
Compiled: nothing new (the file is still the 1-sorry skeleton).
Only easy pieces: |A|,|B| >= 3, so n >= 6. That is far from 20.
Verdict: FAILED fast pass; the blocker is the n<=19 impossibility, a computer search.

## Leg 3: codex  (00:36, 14 min, ended: exit)
File stats: proved lemmas 37, sorries 1, lines 756 (was 0 / 1 / 10)
# Codex relay notes

A cross-unit four-cycle would make the two same-side midpoints coincide. Disjoint other-neighbor sets give 2·degree(a)+1 ≤ |A|. Double-counting degrees gives |B| ≤ |A| if |A| ≤ 8, so the remaining sorted pairs below 20 are (7,7), (8,8), (9,9), (9,10). The one sorry in OMA.solution requests exactly exclusion of these pairs and a 20-point witness.

Compiled with lean_codex.sh: planar_dist_sq, cross_unit_midpoints, no_cross_unit_four_cycle, twice_degree_add_one_le_side_card, seven_le_side_card, degree_eq_three_of_side_card_le_eight, pair_has_common_unit_neighbor_of_card_seven, pair_has_unique_unit_neighbor_of_card_seven, sum_cross_unit_degrees_swap, other_side_card_le_of_side_card_le_eight, fourteen_le_cut_card, small_cut_card_pairs, convexIndep_of_support, isCut_union_of_separator, not_collinear_of_convexIndep, cut_line_disjoint_opposite_hull, distance_monge_iff_turn_mul_neg, exists_strict_distance_monge_order, exists_ordered_cut_distance_matrix, no_ordered_unit_six_cycle, unit_path_missing_entry_lt_one_iff, extreme_row_units_between, extreme_row_units_consecutive, and their helpers.

The strict Monge order is proved in Lean, by sorting distances relative to two opposite-side anchors. Each three-unit 2×2 submatrix forces the sign of the fourth distance minus 1. The consecutive extreme-row blocks are proved. The remaining 7+7 contradiction is a finite ordered incidence argument described in codex_fano.md. Strict Monge alone cannot dispose of 9+9: real Pappus gives an abstract strict Monge point-line matrix with 3 unit entries per row and column. C4-freeness alone cannot dispose of 9+10: delete two disjoint blocks from the affine plane of order 3.

CI verdict: rejected at lint for the single sorry. Direct Lean elaboration reports only that sorry.

## Leg 4: fable  (00:41, 5 min, ended: stalled)
File stats: proved lemmas 37, sorries 1, lines 756 (was 37 / 1 / 756)
(the model wrote no notes; see partial_fable.lean)
