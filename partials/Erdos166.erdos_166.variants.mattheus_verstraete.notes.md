# Relay notes for Erdos166.erdos_166.variants.mattheus_verstraete (prize: $250)


## Leg 1: grok  (00:21, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (00:23, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 46 (was 0 / 1 / 10)
# notes_opus: Erdos166 mattheus_verstraete
Target: exists C>0, eventually R(4,k) >= C k^3/(log k)^4. This is the full Mattheus-Verstraete 2024 theorem.
Faithful: classicalRamsey = sInf over Fin n graphs (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean). No loophole.
(The parent erdos_166 has an external formal proof via Bradac construction with an unspecified exponent c, which is not enough for exponent 4.)
Compiled (lake env lean): OMA.lt_classicalRamsey_of_graph (a graph on Fin n with no K_a and no K_b in the complement gives n < R(a,b), or R(a,b)=0).
Remaining: ONE sorry OMA.mv_construction (= the whole theorem: the Hermitian-unital/pseudorandom K4-free graph plus a random-subgraph argument). Not session-sized.
Dead ends: none tried beyond the loophole audit.

## Leg 3: codex  (00:37, 14 min, ended: exit)
File stats: proved lemmas 30, sorries 1, lines 1164 (was 2 / 1 / 46)
# Leg 3 Codex
Approach: split each point star of a Hermitian unital into two parts, use the resulting induced density to count independent sets by greedy encoding, then sample vertices and delete one per surviving independent set. The dyadic q = 2^j choice uses r = 4Aqj pivots, t of order qj², and floor(q/j²)+1 sampling colors.
Compiled: mv_peel_step, mv_independent_encoding, mv_mem_independents, mv_card_independents_le, mv_card_labelings_containing, mv_sample_avoids_independents, mv_sample_of_count_le, mv_finite_ramsey, mv_classicalRamsey_pos, mv_ramsey_of_sample, mv_choose_mul_pow_le, mv_ramsey_of_dense_graph, mv_bound_of_dyadic, mv_square_le_pow_two, mv_bound_from_hosts. Retained lt_classicalRamsey_of_graph from leg 2.
Compiled for construction: mv_split_graph_k4_free, mv_split_pair_count, mv_density_of_balanced_stars, mv_pivot_of_edge_density, mv_quadrilateral_det_zero, mv_small_side_count, mv_unbalanced_split_count, mv_product_weight_count, mv_split_weight_sum, mv_split_restrict_equiv, mv_split_bad_mass_count. mv_host_edge_construction, mv_host_construction and mv_construction all follow from mv_incidence_host_construction.
Exact remaining gap: sole sorry in mv_incidence_host_construction. For large dyadic q, formalize the Hermitian unital of q³+1 isotropic points, with secant lines of size q+1 and q⁴−q³+q² secants, verify linearity and the no-O'Nan condition, and give one simultaneous star splitting whose balanced stars carry at least q|S|/2 incidences for every |S|>Dq².
Next details: normalize a hypothetical ordinary quadrilateral with the first three intersection points as basis and write the fourth line as Σ a_i x_i=0, all a_i≠0. Its three edge points are a_i⁻¹e_i−a_j⁻¹e_j. Their isotropy yields the three cross equations of mv_quadrilateral_det_zero, contradicting nondegeneracy. For splitting, mv_split_bad_mass_count handles independent restricted star choices for one fixed S. Lift its bound to all choices using mv_split_restrict_equiv and the product type equivalence, then union over S (at most n^x sets of size x). The bound is 3^p/(10/9)^(q x/2), where p≤2q³, x>Dq². Since (10/9)^8>2, a fixed large D absorbs 3^p and q≫log q absorbs the number of sets. Enough good mass follows because each secant has q+1 points.
Dead ends: the parent bound has unspecified logarithmic exponent. Sampling with t of order q log q fails to absorb the greedy encoding cost. The q log² q scale works.
Verification: direct Lean compilation exited 0 with one sorry warning. CI verdict rejected (lint: forbidden: 'sorry').

## Leg 4: fable  (00:42, 5 min, ended: stalled)
File stats: proved lemmas 30, sorries 1, lines 1164 (was 30 / 1 / 1164)
(the model wrote no notes; see partial_fable.lean)
