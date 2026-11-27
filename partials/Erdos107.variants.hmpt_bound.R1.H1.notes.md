# Relay notes for Erdos107.variants.hmpt_bound.R1.H1 (prize: )


## Leg 1: grok  (04:04, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (04:07, 2 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 136 (was 0 / 1 / 9)
# Leg 2 (opus) notes: Erdos107.variants.hmpt_bound.R1.H1
Gap = full Por-Valtr positive-fraction Erdos-Szekeres (k parts, each >= 2^{-Ak}|X|, convex transversals). Research-size formalization (ham-sandwich / same-type style partition + ES cups/caps).
Plan this leg: prove k<=3 cases (k-1 residue classes partition; 3 noncollinear points are convex), leave k>=4 core as one sorry.

## Compiled (lean_codex.sh, 5 s, only warning = sorry in core_large)
- OMA.E107H1.small_convex: k<=3, injective transversal of noncollinear set is in convex position.
- OMA.E107H1.partition: k<=|X| -> k residue-class pieces T i (images of m*k+i under X.equivFin), |X| <= 2k|T i|, transversals injective.
- OMA.solution: full glue (A := max A0 1; k>=4 via core_large with monotone 2^(A k); k<=3 via partition+small_convex).
## Exact remaining gap
core_large: exists A, for all k>=4 the Por-Valtr partitioned Erdos-Szekeres statement (same shape as H1). This IS the whole theorem (Por-Valtr 2002; Suk uses 2^{-32k}); needs ES cups/caps + positive-fraction partition (ham-sandwich / same-type). Nothing in Mathlib.
## Dead ends
- No loophole: T i must be pairwise disjoint for k>=2 (injectivity), sizes forced >= |X|/2^{Ak}; k=4 already needs a positive-fraction 4-convex partition.

## Leg 4: fable  (04:17, 10 min, ended: stalled)
File stats: proved lemmas 26, sorries 1, lines 606 (was 3 / 1 / 136)
# Leg 4 (fable) notes: Erdos107.variants.hmpt_bound.R1.H1  (Por-Valtr, k>=4 open = core_large)

## ROUTE (complete paper proof, all pieces elementary; OWN earlier files give most Lean)
OWN source to paste from (ours, reuse freely): /workspace/left-to-solve/relay/Erdos107.variants.su_bound.R1.H1/partial_fable.lean
 (Point := R x R, orient, turn, HasSeq, card_le_binomial = cups-caps, ordered_turns_of_hasSeq, OrderedTurns, InGap,
  inGap_of_orderedTurns, even_odd_determine, image_eq_of_orderedTurns, pow_le_mul_choose, dense_subsets, dense_ordered_regions)
 and related_files/reductions__Erdos107.variants.su_bound.R1.lean (finite_image_pullback, planar_coordinates, orient_ne_in_image).
Proof of core_large with A = 40, K = 2k gaps, d = 2K+1 = 4k+1, m = orderedRegionSample K <= 2^(8k):
 1. coordinates: planar_coordinates gives linear x y with x injective on X; S = X.image (x.prod y); orient_ne_in_image gives general position.
 2. dense_subsets + card_le_binomial: C(n,d) <= |G| * C(m,d), G = good d-subsets (ordered d-cup or d-cap).
 3. pigeonhole on anchors (up, even points) in A0 = univ x piFinset S (card 2 n^(K+1)): some anchor a with |G| <= |A0| * |fiber|;
    fiber injects into prod_i R_i, R_i = S.filter (InGap up a i). With pow_le_mul_choose: n^K <= Q * prod_i |R_i|, Q = 2^(d+1) d! C(m,d) <= 2^(32k^2+12k+2).
 4. GEOMETRIC MEAN step (new vs weak version): M = 2^(40k). If fewer than k gaps have n <= M |R_i| then M^(k+1) prod|R_i| <= n^K <= Q prod|R_i|, contradiction with Q < M^(k+1). So k large gaps; pick them by Finset.orderEmbOfFin.
 5. transversal y_i in R_(sigma i): x-monotone (anchors monotone because every gap is nonempty) and every triple i<j<l is a turn:
    with a = a_J, b = a_(J+1), J = sigma j: InGap gives turn(y_i,a,b), turn(a,y_j,b), turn(a,b,y_l); identity
    (b.1-a.1) * orient y_i y_j y_l = (x_j-x_i)(F_l-F_j) - (F_j-F_i)(x_l-x_j), F p = (p.2-a.2)(b.1-a.1) - (b.2-a.2)(p.1-a.1),
    F y_i = orient y_i a b, F y_j = - orient a y_j b, F y_l = orient a b y_l.
 6. OrderedTurns => convex position: for interior i use functional f p = (c.1-a.1)(p.2-a.2)-(c.2-a.2)(p.1-a.1), a = e_(i-1), c = e_(i+1);
    f e_i = - orient a e_i c, f e_j = orient a c e_j (j>i+1) or orient e_j a c (j<i-1), f a = f c = 0; ends use x. Then convexHull_min + convex_halfSpace_gt.

## Compiled so far
(see list at the bottom; updated as I go)

## Dead ends
- weak version (large_completion_regions, all gaps > L) only gives 2^(-O(k^2)); need step 4.
- no loophole for k>=4 (see leg 2).
