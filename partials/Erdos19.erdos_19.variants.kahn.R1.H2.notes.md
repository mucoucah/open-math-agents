# Relay notes for Erdos19.erdos_19.variants.kahn.R1.H2 (prize: )


## Leg 1: grok  (03:42, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (03:44, 2 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 109 (was 0 / 1 / 9)
# Erdos19.erdos_19.variants.kahn.R1.H2 -- leg 2 (opus)
Approach: split on r. r <= 2: greedy colouring (D0 = 1, conflict degree <= r(D-1) <= 2D-2 < 2D).
Compiled (proofs file, namespace OMA.E19H2): greedy_color (generic greedy colouring for a symmetric
relation with conflict degree k < m), nbr_card_le (edges meeting A, other than A, number at most
|A|(D-1)), color_small_rank (r(D-1) < m colours suffice), OMA.solution (r <= 2 case closed).
Remaining gap: ONE sorry, OMA.E19H2.core_rank_ge3 (r >= 3). This is chromatic index <= 2D for
linear hypergraphs of rank r with D large, i.e. a Pippenger--Spencer / Kahn nibble consequence.
Greedy only gives r(D-1)+1 colours. The statement is faithful and has no loophole (D0 depends on r, n is arbitrary).
Dead ends: no elementary route to 2D for r >= 3 was found (random splitting + greedy gives worse bounds).
Compile directly with: cd repo/.oma/formal-conjectures; lake env lean file (it works with the OMAReductions import).

## Leg 3: codex  (03:57, 13 min, ended: stalled)
File stats: proved lemmas 37, sorries 1, lines 770 (was 4 / 1 / 109)
# Erdos19 H2 relay leg 3

The proof file keeps the original import, OMA.solution statement, and all incoming lemmas. Direct Lean compiles it with a single hole, `OMA.E19H2.core_local_matching`. The CI checker rejects at lint for that sorry.

Compiled reductions:
- `regularize`, `deg_regular_step`, `linear_layers_fills`: take r disjoint layers and add the transversal of each deficient vertex. This preserves linearity and uniformity and increases each deficient degree by one. Iterate at most D steps.
- `card_padEdge`, `linear_padded`, `deg_padded_inl`, `deg_padded_inr_le_one`, `color_from_uniform_regular`: pad using private vertices, then embed in a uniform regular family.
- `linear_assignments`, `card_assignmentEdge`, `deg_assignments_inl`, `deg_assignments_inr`, `card_target`, `deg_targets_le`: replace each edge-color choice by one (r+1)-edge through an edge vertex and r point-color vertices. This is linear and D-regular. The target for a point is the set of its incident edge vertices.
- `deg_unassigned`, `color_from_assignment_matching`, `core_uniform_regular`, `core_rank_ge3`, `OMA.solution`: a matching gives one palette of D colors. If each target misses at most D/r vertices, the remaining maximum degree is at most D/r, and the old `color_small_rank` lemma finishes with D colors.

Exact gap: for fixed q,s and sufficiently large D, a q-uniform D-regular finite linear hypergraph has a matching missing at most D/s vertices of each prescribed target U, when |U| ≤ D and each vertex is in at most q targets. Global near-perfect matching alone does not supply this pointwise bound. Greedy yields r(D-1)+1 colors and random splitting followed by greedy does not improve it (leg 2).

Direct check: in the configured formal-conjectures checkout, run lake env lean on the absolute proof path. No local formalization of the nibble or local lemma was found.

Scratch: `finite_local_lemma.lean` contains the compiled finite-cardinality Lovász local lemma (`finite_local_lemma`), using induction on the conditioning event set. The hypotheses are conditional cardinal bounds when the event is independent of the conditioning events. A product-space wrapper is in progress.
The LLL scratch file now compiles including `card_inter_mul_of_dependsOn` and `product_local_lemma`. The wrapper uses uniform samples `κ → X`, disjoint coordinate supports and single-event cardinal bounds. Choosing each edge by testing whether its coordinate in Fin m equals 0 gives independent Bernoulli trials with p = 1/m.

Scratch: `sparse_trials.lean` compiles through `trialMean_centered_exp` and `trialMean_upper_tail`. It gives the sparse bound exp(n p t² L² − t u), for Bernoulli probability p, insertion sensitivity L, and tL ≤ 1. The uniform-sample bridge is being checked.

## Leg 4: fable  (04:02, 5 min, ended: stalled)
File stats: proved lemmas 37, sorries 1, lines 770 (was 37 / 1 / 770)
(the model wrote no notes; see partial_fable.lean)
