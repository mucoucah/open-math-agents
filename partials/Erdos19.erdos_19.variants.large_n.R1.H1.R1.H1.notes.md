# Relay notes for Erdos19.erdos_19.variants.large_n.R1.H1.R1.H1 (prize: )


## Leg 1: gemini  (13:25, 10 min, ended: no_progress_10m)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (14:08, 36 min, ended: exit)
File stats: proved lemmas 50, sorries 1, lines 2042 (was 0 / 1 / 9)
Approach: endpoint sums colour disjoint larger blocks. For dense pair graphs, cap precoloured larger-block classes, assign parity omissions to distinct incidences by Hall, complete classes with unused pair matchings, and finish the residual graph by Vizing. Add uncovered pairs before applying this when larger-block incidence degree is small.
Compiled: color_disjoint_large_blocks, dense_pair_matching, cover_precolored_classes, color_pairs_of_degree_lt, precolor_large_blocks, parity_omissions, color_bounded_dense_pairs, bounded_pair_completion, color_of_sparse_large_blocks, total_degree_lt_from_pair_deficit, critical_hypothesis_iff_bounded_rank, color_of_uniform_pair_deficit_of_approx. Kernel audit of the main helpers reports only propext, Classical.choice, Quot.sound.
Exact gap: the final branch has intersecting larger blocks and a point with larger-block incidence degree greater than floor((n−12(R+2))/(12(6R+1)(R−1))). Exclude these critical families. Uniform degree slack reduces to the missing bounded-rank asymptotic colouring theorem. The mixed case also needs to handle near-full pair stars alongside congested points. One final placeholder remains.
Dead ends: the minimum-rank count gives only r² ≤ n. A list-Vizing argument with arbitrary fixed vertex bans fails on a star whose leaves forbid a common colour.

## Leg 2: codex  (16:01, 0 min, ended: exit)
File stats: proved lemmas 50, sorries 1, lines 2042 (was 50 / 1 / 2042)
(the model wrote no notes; see partial_codex.lean)
