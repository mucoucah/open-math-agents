# Relay notes for Erdos147.erdos_147.variants.janzer_conjecture (prize: $500)


## Leg 1: gemini  (14:32, 10 min, ended: no_progress_10m)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (15:30, 54 min, ended: exit)
File stats: proved lemmas 113, sorries 1, lines 3797 (was 0 / 1 / 10)
Compiled solution ranges: all even r ≥ 4 and all odd r ≥ 3 with ε > 2/(r(r+1)). OMA.solution has one placeholder for the remaining small-error odd range. The checker rejects it at lint.
Even proof: pack complete-link tuples, prune a sparse-overlap core, use the weighted conflict-free cycle lemma, and lift to a cycle blow-up. Deleting its explicit perfect matching gives degree 2t−1. Compiled: sparseConflictCycles_of_ratio, even_cycle_blowup_bound, adjacent_degrees_bound, even_degree_case, odd_degree_with_error.
Odd r=2t+1 ≥5: use the two-layer t-fold cycle blow-up with matching rungs. Opposite edges of distinct rectangles give the tuple graph. Compiled: contains_odd_cycle_with_matching, exists_almost_regular_subcopy, extremal_of_almost_regular_bipartite_test, uniform_bounded_codegree_bipartite_odd_witness_of_exponent, odd_degree_reduction_to_high_codegrees_at_exponent.
Exact remaining odd ≥5 step: choose 0<η<ε and 0≤δ<r(ε−η). In sufficiently large almost-regular bipartite hosts with ≥n^(2−2/r+ε−η) edges and a (t+1)-set with >n^δ common neighbors, force the fixed witness selected by odd_degree_reduction_to_high_codegrees_at_exponent. The smaller-codegree case is proved. The standalone cubic proof for 0<ε≤1/6 is also missing.
Dead ends: degree r+1 loses 2/(r(r+1)) in exponent. Unequal blow-up groups force oversized bicliques. The matching-rung witness contains C4, so it cannot give the cubic exponent. Unconstrained rectangular density maximization can select a star. A high-codegree proof using a different witness needs a shared r-regular subgraph.
Final audit: even_degree_case, odd_degree_with_error, sparseConflictCycles_of_ratio, uniform_bounded_codegree_bipartite_odd_witness_of_exponent, and odd_degree_reduction_to_high_codegrees_at_exponent depend only on propext, Classical.choice, and Quot.sound. OMA.solution additionally depends on the single remaining placeholder.

## Leg 1: gemini  (15:38, 3 min, ended: exit)
File stats: proved lemmas 113, sorries 1, lines 3797 (was 113 / 1 / 3797)
(the model wrote no notes; see partial_gemini.lean)
