# Relay notes for Erdos41.erdos_41 (prize: $500)


## Leg 1: opus  (09:41, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Opus leg 1 notes: Erdos41.erdos_41 ($500, open)
Approach: checked whether the statement is faithful and has a loophole. It is faithful: NtupleCondition A 3 is exactly the B_3 condition (multisets, no trivial coincidences),
the ratio is >= 0 and bounded (cubic_count in merged R1 gives |A cap [1,N]| <= C N^{1/3}), so the real liminf is a genuine value in [0,C]; the sSup-of-unbounded-set loophole does not apply.
Merged R1 (reductions/Erdos41.erdos_41.R1.lean) reduces it to H1 (small gaps, o(i^2 log i)) and H2 (large gap moments); both are the open core of Erdos's question.
Compiled: nothing new; proofs file unchanged (sorry skeleton).
Gap: the whole open Erdos problem (B_3 analogue of Erdos's Sidon liminf N^{1/2} theorem; the Sidon proof's difference trick has no B_3 analogue).
Dead ends: loophole hunt (none), fast pass. Verdict FAILED fast pass.

## Leg 2: codex  (09:53, 11 min, ended: exit)
File stats: proved lemmas 12, sorries 1, lines 415 (was 0 / 1 / 10)
Approach: an infinite B3 set has nonzero counting liminf iff its enumeration eventually satisfies f(n) ≤ (d*(n+1))^3 for some d>0. A nonzero liminf also implies a global quadratic bound on short ordered pairs. Translate every short difference outside the prefix of width k^3 by each prefix point. Signed uniqueness gives capacity O(k^3), while the prefix has Ω(k) points. Pairs meeting the prefix lie within [0, 2k^3].
Compiled: signed_triples_eq, closePair_capacity, blocks_closePair_capacity, finite_count_cube, scaled_count_of_ne_zero, enumeration_le_cube, tail_closePairs_quadratic, all_closePairs_quadratic, eventually_ratio_le_twelve, scaled_count_of_enumeration_le_cube, liminf_pos_of_scaled_count, liminf_ne_zero_iff_cubic_enumeration. Direct Lean exits zero with the lone target sorry. CI rejects at lint for that sorry.
Remaining gap: rule out an infinite B3 set A with eventual f(n) ≤ (d*(n+1))^3. The target now also has eventual |D| ≤ (196+4*d)*k^2 for every finite family D of ordered distinct pairs in A at distance ≤ k^3.
Dead ends: fixing the third summand below the window length loses (window/scale)^(1/3), so dyadic summation is bounded. The short-pair upper bound has the same scale as the pairs contributed by the prefix. Recasting via dilation limits runs into proving repeated near-Schur correlations for possibly singular limiting measures.
A stronger regularity case worth distinguishing: if the normalized count tends to c>0, then for each fixed bin index m the count in (mH,(m+1)H] is asymptotic to c*((m+1)^(1/3)-m^(1/3))*H^(1/3). For R=8^j, use u in [R,2R), v in [2R,3R), and bin u+v. The R^2 choices contribute Ω_c(H) distinct signed triples in [-H,2H] per scale. Taking arbitrarily many fixed scales is contradictory, but a positive liminf by itself gives no binwise lower bound. This observation is not formalized.
