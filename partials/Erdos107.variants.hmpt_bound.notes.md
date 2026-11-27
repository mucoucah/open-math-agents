# Relay notes for Erdos107.variants.hmpt_bound (prize: $500)


## Leg 1: grok  (23:14, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (23:16, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos107.variants.hmpt_bound - leg 2 (opus) notes
Approach: none viable. Target is the full HMPT20 theorem f(n) <= 2^(n+O(sqrt(n log n))), stronger than Suk 2017.
Faithfulness: definitions faithful (cardSet, f = sInf). Loophole f = 0 (empty cardSet) is ruled out: cardSet n is
nonempty by Erdos-Szekeres. Choosing r n := log2 (f n) - n just moves the problem to an upper bound on f.
Even a full Lean proof of ErSz35 (binomial(2n-4,n-2)+1 ~ 4^n) only gives r ~ n, not O(sqrt(n log n)).
Needs: positive-fraction Erdos-Szekeres + cups-caps + HMPT refinement. None in Mathlib.
Compiled: nothing new (file unchanged: single sorry).
Dead ends: same as su_bound (wt11 notes). Recommend FAILED.

## Leg 3: codex  (23:28, 12 min, ended: stalled)
File stats: proved lemmas 15, sorries 1, lines 411 (was 0 / 1 / 10)
# Erdos107.variants.hmpt_bound, Codex

Approach: use k = ceil sqrt(n/log n). Absorb the loss C(k log n + n/k) and rounding by bounding it with (3C+1) sqrt(n log n). A subset of one certified large polygon handles the finite prefix.
Compiled by direct Lean: HMPT.cardSet_mono_polygon, of_eventually_cardSet, balancedParameter_pos, balancedParameter_bound, of_eventually_balanced_cardSet, one_le_scale, of_eventually_planar_bound, exists_chain_or_antichain, baseOrder_iff, baseDet_flip, exists_subset_by_base_signs. The last lemma gives a size tradeoff between pairs whose connecting line separates the two base endpoints and pairs whose connecting line leaves them on the same side.
Also compiled: HMPT.exists_support_slope, score_lt_of_endpoints, convexIndep_of_slope_blocks, card_choose_le_convexSubsets_mul. The block lemma combines cups using strict support in a prescribed slope interval. The count lemma double-counts convex n-subsets from a smaller certified cardinal threshold.
Gap: prove that some absolute C >= 0 has the following property eventually in n. Every finite general-position planar X of size strictly greater than 2^(n+C(k log n+n/k)) contains a convex n-gon. This is the single placeholder in the solution.
Dead ends: the classical cups/caps bound alone gives about 4^n. Upstream research declarations are unavailable. The exact checker rejects the remaining placeholder.

## Site hints (2026-11-26)

https://www.erdosproblems.com/107 (YAML: falsifiable; f(n)=2^{n-2}+1 still open). This variant is Holmsen–Mojarrad–Pach–Tardos [HMPT20], JEMS 2020: f(n) ≤ 2^{n+O(√(n log n))}. Follow that paper. A Lean proof that f(n) is finite (not this bound) is at https://github.com/linrock/math-proofs/blob/cd3cf0b176e95209584bf35555a7c0e501255f6e/erdos-107/Solution.lean#L59 . Write-up: /workspace/left-to-solve/research/erdosproblems.md

## Leg 4: fable  (23:33, 4 min, ended: exit)
File stats: proved lemmas 15, sorries 1, lines 411 (was 15 / 1 / 411)
# Erdos107.variants.hmpt_bound - leg 4 (fable) notes

## Verdict of this leg
STALLED. No new lemma. The proof file is unchanged (411 lines, 15 proved lemmas, ONE sorry in OMA.solution).

## Approach (unchanged from leg 3)
k = ceil sqrt(n / log n); everything analytic and the finite prefix are done.
OMA.solution = HMPT.of_eventually_planar_bound applied to the single open claim below.

## Exact remaining gap (the only sorry)
exists C >= 0 such that eventually in n: every finite X in the plane with NonTrilinear X and
card X > HMPT.threshold C n = 2^(n + C*(k log n + n/k)) has HasConvexNGon n X.
This IS the Holmsen-Mojarrad-Pach-Tardos theorem (JEMS 2020). Nothing weaker suffices.

## Checked again this leg (do not redo)
- Definitions are faithful: NonTrilinear = no three distinct points collinear, ConvexIndep = no point in the hull of
  the others, HasConvexNGon n = a ConvexIndep Finset of card n inside, cardSet/f = sInf. Exponent is Real.rpow with
  n cast to R. No loophole: f n >= 2^(n-2)+1 genuinely, so r must really bound log2 (f n) - n.
- tools/check.sh runs the lint BEFORE Lean, so its verdict on this file is only: rejected, lint: forbidden sorry.
  It says nothing about compilation. To test compilation of a file with sorry use a direct compile:
  cd /workspace/left-to-solve/repo/.oma/formal-conjectures && lake env lean <absolute path of the proof file>
  (direct compile result of the unchanged file: see the last section).

## Useful resource the earlier legs did not use
proofs/Erdos107.variants.ersz_bounds.lean (merged, accepted, same first import) holds the classical machinery,
pasteable (lines 12-519, no double-quote characters; wrap in a section because it opens Finset and Classical):
- OMA.planar_coordinates: linear coordinates x y on the plane, x injective on X, (x,y) jointly injective.
- ErdosSzekeresUpper.card_le_binomial: cups-caps, no (s+2)-cup and no (t+2)-cap => card <= choose (s+t) s
  (points as pairs, lists with increasing first coordinate, orient sign = turn).
- ErdosSzekeresUpper.convex_from_seq: an n-cup or n-cap in the image gives HasConvexNGon n.
- ErdosSzekeresUpper.upper_mem: choose (2n-4) (n-2) + 1 is in cardSet n (only gives r ~ n, useless alone).
Any real attack on the gap needs these three first; do not re-derive them.

## Why it cannot be closed in a relay leg
- Erdos-Szekeres alone: about 4^n, i.e. r ~ n.
- Suk 2017 route (positive-fraction ES of Por-Valtr + Dilworth chain/antichain in each region + unbalanced
  cups-caps) is itself a long geometric formalization and only yields r = O(n^(2/3) log n), NOT O(sqrt(n log n)).
  So even a full Suk formalization does not prove this target.
- The sqrt(n log n) error term needs the HMPT refinement (their signotope / pseudo-configuration argument with
  loss n^O(k) * 2^O(n/k)). Not in Mathlib, not in any worktree proofs dir (grep for cup, ConvexIndep done).
  Estimated size: several thousand lines of Lean.

## Dead ends (cumulative)
- Loophole via f = 0 or vacuous cardSet: impossible.
- Choosing r n := log2 (f n) - n: just restates the upper bound.
- Codex lemmas exists_subset_by_base_signs, convexIndep_of_slope_blocks, card_choose_le_convexSubsets_mul are
  plausible ingredients, but nothing connects them to the gap yet; the gap is still the whole theorem.

## Direct compile of the unchanged file
DONE: lake env lean on proofs/Erdos107.variants.hmpt_bound.lean, rc=0, 6.4 s wall, only message:
406:8 warning: declaration uses sorry. So all 15 helper lemmas compile and the file is sound up to the one sorry.
A direct compile is fast (seconds), so iterate with it and call tools/check.sh only for a sorry-free file.
