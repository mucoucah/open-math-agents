# Relay notes for Erdos107.variants.su_bound.R1.H1 (prize: )


## Leg 1: grok  (03:42, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (03:43, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
# Opus leg 2, Erdos107.variants.su_bound.R1.H1

Approach: none new. Audited the statement and stopped early, as the memory and earlier legs advised.
H1 is Suk's 2017 theorem (ES(n) <= 2^((1+eps)n) for large even n) in planar coordinates. It is faithful, with no loophole:
- if N is smaller than the ES number, a general-position X with no convex n-subset exists, so the statement fails;
- u = v = 0 gives no strict inequality, so a trivial witness is impossible;
- Erdos-Szekeres cups-caps gives only about 4^n, too weak for any eps < 1.
Compiled: nothing new. The file is unchanged: one sorry in OMA.solution.
Remaining gap: the whole Suk argument (Por-Valtr positive-fraction ES, the transitive-colouring cups-caps inside regions, gluing). That is thousands of lines and nothing of it is in Mathlib.
Pieces that already exist in the wt11 proofs/Erdos107.variants.su_bound.lean helpers: cups_caps_planar, the bridge, the glue. None of them reduces the 4^n -> 2^((1+eps)n) gap.
Dead ends: cups-caps alone (4^n); the eps >= 1 trick does not apply (eps < 1 here).

## Leg 3: codex  (03:55, 12 min, ended: stalled)
File stats: proved lemmas 51, sorries 1, lines 1098 (was 0 / 1 / 9)
# Codex leg 3

Approach: use the own parent scratch theorem ordered_regions_of_general_position, choose nonadjacent outward gaps, apply projective cups/caps separately in the gaps, and glue supported caps. The number of gaps can be fixed after choosing ε. This permits any fixed density loss in the asymptotic threshold.

Compiled in the target file: dense_subsets, large_completion_regions, chain_or_antichain, nested_iff, anchors_of_antichain, cup_or_cap_in_chart, cup_or_anchored_cap, ordered_regions_of_general_position, right_of_gap, left_of_gap, cap_edge_external, normalizeGap_orient, normalizeGap_anchors, normalizedGap_bounds, normalized_antichain_x, exposed_of_support, exposed_of_ordered_piece and their helpers. Target currently has one sorry.

Remaining: assemble the family gluing and the H1 threshold, and prove extraction in the large-chain branch.

Dead ends: balanced global cups/caps give order 4^n. Adjacent gaps can interfere, so use a buffer anchor edge. For nested pairs the signs at the anchors are opposite, and an external point need not share the sign at the closer anchor. For example the normalized base (0,0),(1,0), p=(.7,1), q=(.874,.4) give a nested pair. Its sign at (1,0) is positive and its sign at (2,-100) is negative. A chain argument needs more than the cap support-ray calculation.

## Leg 4: fable  (04:00, 5 min, ended: stalled)
File stats: proved lemmas 51, sorries 1, lines 1098 (was 51 / 1 / 1098)
(the model wrote no notes; see partial_fable.lean)
