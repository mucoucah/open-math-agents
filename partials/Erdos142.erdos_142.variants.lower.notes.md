# Relay notes for Erdos142.erdos_142.variants.lower (prize: $10000)


## Leg 1: opus  (08:00, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_opus: Erdos142.erdos_142.variants.lower (leg 1)
Target: for every k>1, r_k(N) = o(N/log N), with r = Set.IsAPOfLengthFree.maxCard
(subsets of Icc 1 N, sSup of the card). I checked the definition: it is faithful.
Non-trivial means length k with 1<k, d nonzero is forced by ENat.card = k. No loophole.
Status by k: k=2 is trivial (r_2 <= 1). k=3 needs Kelley-Meka, which is not in Mathlib.
k=4 needs Green-Tao: their (log N)^-c bound has tiny c, so it does NOT give o(N/log N).
For k>=5 the claim is OPEN (Gowers gives only (loglog N)^-c; LSS24 gives
exp(-(loglog)^c)). So the full statement is an open research problem.
Compiled: nothing new. The proofs file is still the trivial sorry skeleton.
Existing merged reductions (R1 by DarkWingMcQuack, R2 by Halldon, and their steps) are
listed in related.md. Their leaf steps still contain the open density bound.
Dead end: no elementary route exists. Do not try a direct proof. FAILED fast pass.

## Leg 2: codex  (08:09, 8 min, ended: exit)
File stats: proved lemmas 26, sorries 1, lines 531 (was 0 / 1 / 10)
# Erdős 142 lower, Codex relay

Approach: pack extremizers into the intervals (4·4^j, 5·4^j] for j in [n, 2n). A nonconstant three-term progression cannot cross these blocks. Antitonicity of r_k(4^j)/4^j lets the reciprocal mass of the packed set control j·r_k(4^j)/4^j. Interpolate via the integer logarithm. The reverse bound sums the weighted density estimate over the same finite window.

Compiled: `r_two_le_one`, `two_littleO` (the full k=2 case), `apFree_iff`, `exists_maximizer`, `card_le_r`, `r_mono`, `r_add_le`, `r_mul_le`, `blockDensity_antitone`, `littleO_of_blockDensity`, `shiftBlock`, `mem_shiftBlock_bounds`, `pow_four_gap`, `blockIndex_le`, `block_indices_of_midpoint`, `shifted_blocks_free`, `shiftBlocks_pairwiseDisjoint`, `shiftBlock_reciprocal_lower`, `weighted_blockDensity_of_window`, `littleO_of_window`, `weighted_blockDensity_of_littleO`, `reciprocalMass_block_upper`, `window_of_weighted_blockDensity`, `littleO_iff_window`, `threeAPFree_iff`, `r_three_eq_roth`, `three_littleO_linear`. Direct Lean passes except for the single placeholder warning. Axiom audits for `two_littleO`, `littleO_iff_window`, and `three_littleO_linear` list only the three CI-allowed axioms. The required checker rejects at lint for the placeholder.

Exact gap: `OMA.solution` needs `ReciprocalWindowBound k` for each k ≥ 3. For every ε > 0 and all sufficiently large n, the reciprocal sum of every finite k-AP-free subset of the union of (4·4^j, 5·4^j] over n ≤ j < 2n is at most ε. `littleO_iff_window` proves equivalence with the original estimate for each such k.

Dead ends: the definitions are faithful. Qualitative density decay (including `three_littleO_linear`) and log powers with exponent at most one do not close the gap. R2 uses a stronger unresolved summability assertion. The pinned Mathlib has qualitative Roth but no Kelley–Meka bound. The worktree has standalone Kelley–Meka proofs, notably `proofs/Erdos3.erdos_3.variants.kelley_meka.lean` (`Erdos3KM.pg`), but the checker only allows Mathlib imports after the target import, and the relay rules forbid copying the standalone proof. Even a quantitative k=3 theorem leaves the unproved longer-progression estimates.

## Leg 1: opus  (09:19, 0 min, ended: exit)
File stats: proved lemmas 26, sorries 1, lines 531 (was 26 / 1 / 531)
# notes_opus: Erdos142.erdos_142.variants.lower (relay leg, opus)
Approach: none new. The statement (r_k(N) = o(N/log N) for EVERY k>1) is a faithful
formalisation of an open problem: k>=5 is open, k=4 Green-Tao exponent too small,
k=3 needs Kelley-Meka (not in Mathlib). No loophole (ENat.card = k forces d nonzero).
Compiled (unchanged, from codex leg): 26 lemmas incl. two_littleO (k=2), r_add_le,
blockDensity_antitone, littleO_iff_window, three_littleO_linear. File left untouched.
Exact remaining gap: ReciprocalWindowBound k for every k>=3 (the open density bound).
Dead ends: any direct/elementary proof; qualitative Roth/Szemeredi decay; log powers
with exponent <= 1. Reduction R3 (k=3 / k>=4 window decay) was ACCEPTED in wt17.
Recommendation: FAILED fast pass; do not spend more legs on it.

## Leg 2: codex  (09:24, 5 min, ended: exit)
File stats: proved lemmas 36, sorries 1, lines 772 (was 26 / 1 / 531)
# Codex relay notes — Erdős 142 lower

Approach: glue the existing shifted extremizers in (4·4^j, 5·4^j] into a single progression-free set. Each finite packed window fits inside (N,N²] at N = 4·4^n. For the converse, partition (N,N²] by floor(log₄ x) and sum the weighted density estimate.

Compiled: all previous lemmas, plus shifted_blocks_union_free, weighted_blockDensity_of_packed_windows, squareWindowDecay_iff_tendsto, squareWindowDecay_of_summable, exists_set_controlling_littleO, squareWindowDecay_of_littleO, littleO_iff_squareWindowDecay, littleO_iff_supported_squareWindowDecay, littleO_of_stretched_exponential, three_littleO_of_roth_estimate. Direct Lean passed with one placeholder warning. The k=2 proof, old window equivalence, supported square-window equivalence, summability implication, and conditional k=3 proof use only propext, Classical.choice, and Quot.sound. The required checker returned rejected with reason lint: forbidden: 'sorry'.

Exact gap at OMA.solution: for each k ≥ 3 and each k-AP-free A ⊆ ℕ supported in the union of (4·4^j, 5·4^j], prove ∑_{x∈A, N<x≤N²} 1/x → 0. It suffices to prove this for the single packed extremizer set in exists_set_controlling_littleO. Equivalently, close ReciprocalWindowBound k as in the previous leg.

Dead ends: qualitative decay and log powers with exponent ≤ 1 leave the gap. Full reciprocal summability is stronger and open in general. A positive stretched-exponential density bound for rothNumberNat suffices for k=3 via the new lemma, but the standalone Kelley–Meka files are unavailable through allowed imports and the handoff rules prohibit copying their proof. Longer lengths still need the open estimate.

## Dedicated Gemini 4 Neon (09:38, 0 min, ended: exit)
File stats: proved lemmas 36, sorries 1, lines 772 (was 36 / 1 / 772)
(the model wrote no notes; see partial_gemini.lean)

## Dedicated Gemini 4 Neon (10:07, 5 min, ended: exit)
File stats: proved lemmas 36, sorries 1, lines 772 (was 36 / 1 / 772)
(the model wrote no notes; see partial_gemini.lean)

## Leg 1: opus  (10:08, 0 min, ended: exit)
File stats: proved lemmas 36, sorries 1, lines 772 (was 36 / 1 / 772)
# notes_opus: Erdos142.erdos_142.variants.lower (relay leg 1, opus, round 3)
Approach: none new. The target says r_k(N) = o(N/log N) for EVERY k>1. It is a faithful
formalisation of an open problem: k>=5 is open, the Green-Tao exponent for k=4 is too small,
and k=3 needs Kelley-Meka, which is not in Mathlib. No loophole: ENat.card = k forces d to be nonzero.
Compiled: unchanged, 36 lemmas from the codex legs. They include two_littleO (k=2),
littleO_iff_window, littleO_iff_supported_squareWindowDecay and
three_littleO_of_roth_estimate. I left the file untouched; it has ONE sorry (OMA.solution).
Exact remaining gap: ReciprocalWindowBound k for every k>=3 (the open density bound).
Dead ends: a direct or elementary proof; qualitative Roth/Szemeredi decay; log powers with
exponent <= 1; full reciprocal summability (stronger and open).
Recommendation: FAILED fast pass. Do not spend more legs on it.

## Leg 2: codex  (10:12, 4 min, ended: exit)
File stats: proved lemmas 42, sorries 1, lines 978 (was 36 / 1 / 772)
# Erdős 142 lower, Codex relay

Approach: transfer the interval extremal estimate to prime cyclic groups. An interval of length N embeds in ZMod q for q > 2N without introducing progressions. The first two representatives fix a signed step, and each subsequent step lifts because sums stay below q. Conversely, adding one to the canonical representatives makes a cyclic progression-free set interval progression-free. Bertrand supplies a prime between 2N and 4N.

Compiled with direct Lean: all prior lemmas and `cyclic_image_free`, `exists_cyclic_extremal_set`, `cyclic_card_le_r`, `littleO_iff_primeCyclicBound`, `cyclic_threeAPFree_iff`, `littleO_three_iff_primeRothBound`. The two new asymptotic equivalences use only `propext`, `Classical.choice`, and `Quot.sound`. The first import and solution statement are unchanged. Required checker verdict: rejected at lint, forbidden `sorry`.

Exact gap: prove `PrimeCyclicBound k` for every k ≥ 3, equivalently the supported square-window reciprocal decay left at `OMA.solution`. For every ε > 0 and sufficiently large prime q, every cyclic k-AP-free subset of ZMod q must have size at most ε q/log q. For k = 3 this is the same bound on Mathlib's `addRothNumber` of the whole prime cyclic group.

Dead ends from previous legs: qualitative density decay and log powers with exponent at most one do not give the target. Full reciprocal summability is stronger. The standalone Kelley–Meka file is unavailable through permitted imports and cannot be copied. A quantitative proof for k = 3 would still leave longer progressions.
