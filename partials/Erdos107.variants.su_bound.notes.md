# Relay notes for Erdos107.variants.su_bound (prize: $500)


## Leg 1: grok  (23:13, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (23:14, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_opus (leg 2) Erdos107.variants.su_bound
(earlier notes_opus/notes_codex/notes_fable content in this dir is about other problems; ignore it)

## Verdict: FAILED fast pass, no loophole
- Target: exists r = o(n) with f n <= 2^(n + r n) for all n >= 3, f n = sInf (cardSet n).
- Definitions are faithful (FormalConjecturesForMathlib/Geometry/2d.lean): NonTrilinear = no 3 collinear,
  ConvexIndep S = every a in S lies outside convexHull (S minus a), HasConvexNGon = finset of card n inside P.
- Possible loophole, ruled out: if cardSet n were empty then f n = 0, but cardSet n is nonempty (Erdos-Szekeres),
  so f n is the true ES number and the target is exactly Suk 2017 (JAMS) upper bound 2^(n+o(n)).
- Choosing r n := log2 (f n) - n does not help: r = o(n) still needs the Suk upper bound.
- The ES binomial bound C(2n-4,n-2)+1 ~ 4^n gives only r ~ n, not o(n).
- Suk's proof needs positive-fraction ES (Posa-Pach-Solymosi type), the Dilworth / transitive-colouring cup-cap
  argument, and the ES cups-caps theorem. None of this is in Mathlib; far beyond a session.
## Compiled: nothing new (file is still the 1-sorry skeleton).
## Remaining gap: the whole Suk theorem.

## Leg 3: codex  (23:25, 10 min, ended: stalled)
File stats: proved lemmas 10, sorries 1, lines 227 (was 0 / 1 / 10)
# Codex leg 3 on Suk's bound

Target file compiles with one sorry, now `suk_finite_threshold`: for every ε>0 and all sufficiently large n, the floor of 2^((1+ε)n) is in `Erdos107.cardSet n`. Verified in target: `from_eventual_epsilon` and `from_epsilon_cardSet` (use max of the log-base-2 excess and zero), `patch_eventual_bound`, `sublinear_log_power`, `from_eventual_cardSet`, `from_suk_threshold`, `dense_subsets` (double-counted density of hitting configurations), `large_completion_regions` (pigeonhole/capacity bound), and `chain_or_antichain` (rank fibers).

Verified scratch `su_projective.lean`: `orient_chart`, `orient_left_anchor`, `orient_right_anchor`, `nested_iff`, `nested_trans`, `anchors_of_antichain`. In normalized coordinates, chart (x/y,(x−1)/y) preserves orientation for y>0 and converts triangle nesting into opposite coordinate orders. Antichain order makes both base anchors have the desired clockwise sign. Neighboring standalone proof Erdos107.variants.ersz_bounds.lean supplies the asymmetric cups–caps recurrence; `su_caps.lean` adapts it to this chart and builds caps with good anchor signs.

Approach for dense regions: double-count monotone cups/caps of size 2k+1, fix even-index points as anchors, and view odd-index points as completions in k gaps. `su_regions.lean` is under verification for this step. With k fixed, the constant fraction may be arbitrarily small.

Main remaining geometric gap: extract and glue compatible convex subsets from dense ordered regions. In particular, a nesting-chain secant may put an external region on either side even when it separates the two local anchors. A separate geometric argument is needed to join sufficiently large pieces or get a full polygon from one piece.

Checker run: rejected by lint for the single remaining sorry. Earlier dead ends: empty cardSet, logarithm alone, and the symmetric classical binomial upper bound as the desired estimate. No network.

## Site hints (2026-11-26)

https://www.erdosproblems.com/107 (YAML: falsifiable; equality still open). This variant is Suk [Su17], *On the Erdős-Szekeres convex polygon problem*, JAMS 2017: f(n) ≤ 2^{(1+o(1))n}. Follow that paper. Write-up: /workspace/left-to-solve/research/erdosproblems.md

## Leg 4: fable  (23:34, 9 min, ended: exit)
File stats: proved lemmas 40, sorries 1, lines 867 (was 10 / 1 / 227)
# notes_fable (leg 4) Erdos107.variants.su_bound

## Verdict: STALLED. Target = full Suk 2017 theorem ES(n) <= 2^(n+o(n)); faithful, no loophole.

## Approach
OMA.solution := from_epsilon_exists suk_finite_threshold. Everything is proved except ONE sorry,
suk_planar_small_eps (line 844), a statement purely about Finset (R x R):
  for eps in (0,1), eventually in n, EXISTS N with (N : R) <= 2^((1+eps) n) such that every
  X : Finset (R x R) with X.card = N and PlanarGeneral X has Y subset X, Y.card = n, PlanarConvex Y.
PlanarGeneral X = fst injective on X and orient a b c != 0 for x-sorted triples.
PlanarConvex Y = every p in Y has (u, v) with u*p.1 + v*p.2 < u*q.1 + v*q.2 for all other q in Y.
No EuclideanSpace / convexHull / Collinear / floor is left in the gap.

## Compiled in proofs file (867 lines, 40 private theorems, lean compiles it in 6 s, one sorry)
Leg 4 additions:
- cardSet_mono (N in cardSet n, N <= M => M in cardSet n), cardSet_anti (m <= n => N in cardSet m).
- from_epsilon_exists : exists-N threshold form implies the target.
- finite_image_pullback, planar_coordinates, orient_ne_in_image; defs orient, PlanarConvex, PlanarGeneral.
- cardSet_of_planar : coordinate statement for (N, n) ==> N in cardSet n.
- extreme_of_increasing_slopes, planarConvex_of_cup, planarConvex_of_cap : a set with distinct
  abscissas whose x-sorted triples all have orient > 0 (cup) or all < 0 (cap) is PlanarConvex.
- section CupsCaps (ported from ersz_bounds: turn, turns, IsSeq, HasSeq, card_le_binomial,
  turn_of_mem, ...) plus cups_caps_planar (C(s+t,s) < X.card and PlanarGeneral X give an
  (s+2)-cup or (t+2)-cap as a Finset) and convex_of_cups_caps (PlanarConvex Y of that size).
- suk_planar_large_eps : the case eps >= 1 from the classical binomial bound (end-to-end test
  of the pipeline); suk_planar (case split); suk_finite_threshold (proved from suk_planar).
Kept from leg 3: patch_eventual_bound, sublinear_log_power, from_eventual_cardSet,
from_suk_threshold, from_eventual_epsilon, from_epsilon_cardSet, dense_subsets,
chain_or_antichain, large_completion_regions.

## Exact remaining gap
suk_planar_small_eps = all of Suk's proof (in coordinates). Ingredients still missing:
1. Por-Valtr positive-fraction ES: for |P| >= 2^(32k) there is a k-cap or k-cup X whose
   k-1 edge regions T_i (triangle on edge x_i x_(i+1) cut by the two neighbouring edge lines)
   each hold >= |P| / 2^(32k) points. dense_subsets + large_completion_regions are the
   counting half; the geometric half (regions of a fixed anchor, transversals convex) is missing.
2. In each region: order p < q iff q in conv(base edge + p); chain_or_antichain gives the split.
   Antichain => points ordered by angle, cups_caps_planar in a local chart (leg 3 scratch
   su_projective.lean has the chart lemmas); chain => transitive 2-colouring of triples,
   cups-caps for transitive colourings (not written).
3. Gluing: about n^(1/3)/2 non-consecutive regions each with a 2n^(2/3)-cup, or consecutive
   regions with chains; show the union is PlanarConvex. No Lean for this.
4. Parameter arithmetic: k = n^(2/3), N = 2^(n + C n^(2/3) log n); from_suk_threshold is ready.

## Dead ends
- Empty cardSet (f = 0): impossible, cardSet is nonempty.
- r := logb 2 f - n: still needs the upper bound.
- Symmetric ES bound C(2n-4,n-2)+1 ~ 4^n: only covers eps >= 1 (done), never eps < 1.
- No shortcut proof of 2^(n+o(n)) is known; HMPT20 is harder, not easier.
- A full formalisation is thousands of lines; not a 15-minute leg.

## Practical
- tools/check.sh rejects at lint on the word sorry BEFORE compiling, so it says nothing about
  errors. Compile directly: bash .oma/scratch/check_su.sh proofs/Erdos107.variants.su_bound.lean
  (about 6 s). Scratch copy of the current file: .oma/scratch/su_planar3_fable.lean.
