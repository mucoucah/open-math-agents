# Relay notes for Erdos142.erdos_142.variants.three (prize: $10000)


## Leg 1: opus  (09:23, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 2, lines 16 (was 0 / 2 / 16)
# notes_opus: Erdos142.erdos_142.variants.three (leg 1)
Approach: none possible. Target: (fun N => (r 3 N : R)) ~[atTop] answer, with an explicit answer.
This asks for an exact asymptotic formula for r_3(N). That is wide open: the best known bounds are
Behrend-type lower N exp(-c sqrt(log N)) and Kelley-Meka upper N exp(-c (log N)^(1/12)).
Even the order of magnitude (isTheta variant) is unknown.
Loophole check: the only way to close it is answer := r 3 itself (or something defined from maxCard),
which the rules forbid (not built from Erdos142, no sup of the quantity; a person checks the answer).
r is the abbrev Set.IsAPOfLengthFree.maxCard and the statement is faithful, so there is no loophole.
What compiled: nothing new; the file is still the untouched template (one sorry).
Remaining gap: the whole open problem. Dead ends: everything; recommend FAILED fast pass, stop at once.

## Leg 2: codex  (09:26, 3 min, ended: exit)
File stats: proved lemmas 8, sorries 2, lines 179 (was 0 / 2 / 16)
# Codex leg 2 — Erdős 142, three-term variant

Approach: the midpoint characterization identifies progression freeness with Mathlib's ThreeAPFree. Shifting [1,N] to [0,N) then identifies r₃(N) with rothNumberNat N. Transfer Mathlib's Behrend lower bound and Roth's o(N) theorem, and use the lower bound to show N^α=o(r₃(N)) for α<1.

Compiled in the target file: `progression_shape`, `mem_midpoint_eq`, `threeAPFree_iff`, `maxCard_three_eq_rothNumberNat`, `maxCard_three_lower_bound`, `maxCard_three_isLittleO`, `eventually_rpow_le_maxCard_three`, `rpow_isLittleO_maxCard_three`, `not_equivalent_rpow`. The scratch file `erdos142_three_codex.lean` audits the two transferred bounds and pure-power obstruction to propext, Classical.choice, Quot.sound only. Direct Lean compiles the target with two sorry warnings. The exact CI checker rejects it at lint with forbidden sorry. The first import and OMA.solution header are unchanged.

Remaining gap: supply an explicit f : ℕ → ℝ and prove r₃(N)/f(N) → 1. The available bounds give no matching profile. Dead ends: every pure power N^α is ruled out by the compiled lemma, and rothNumberNat itself is just r₃ under another name. The older placeholder-axiom objection is stale because the current checker skips the answer placeholder during the audit.

## Leg 1: opus  (10:12, 0 min, ended: exit)
File stats: proved lemmas 8, sorries 2, lines 179 (was 8 / 2 / 179)
# notes_opus: Erdos142.erdos_142.variants.three (relay leg 1, opus, this round)
Approach: none possible. Target asks for an explicit f with r_3(N) ~ f(N): a wide-open problem
(Behrend lower N exp(-c sqrt log N) vs Kelley-Meka upper N exp(-c (log N)^(1/12)); even the order of magnitude is unknown).
What compiled (from codex leg, kept untouched): progression_shape, mem_midpoint_eq, threeAPFree_iff,
maxCard_three_eq_rothNumberNat, maxCard_three_lower_bound, maxCard_three_isLittleO,
eventually_rpow_le_maxCard_three, rpow_isLittleO_maxCard_three, not_equivalent_rpow.
Remaining gap: the whole open problem (explicit answer + r3/f -> 1). Only loophole answer := r 3 / rothNumberNat is forbidden.
Dead ends: pure powers N^alpha (refuted in file), rothNumberNat (same quantity renamed), any reduction (answer is opaque).
Recommendation: FAILED fast pass, stop at once.

## Leg 2: codex  (10:17, 5 min, ended: exit)
File stats: proved lemmas 13, sorries 2, lines 333 (was 8 / 2 / 179)
# Codex relay leg 2 — Erdős 142, three-term variant

Approach and result: encode the product of two 3-AP-free sets with radix 2m, so there are no carries in the midpoint equation. This proves r₃(m)r₃(n) ≤ r₃(2mn). For K = o(N), subadditivity bounds the increment by r₃(K), and the product bound shows r₃(K) ≤ r₃(N)/r₃(m) for every fixed m eventually. The Behrend bound gives r₃(m) → ∞. This proves r₃(N+K) ~ r₃(N) and more generally preserves asymptotic equivalence under natural-valued reindexing. In particular, an equivalent f(n) for r₃(n²) would give f(⌊√N⌋) for r₃(N).

New compiled lemmas: maxCard_three_mul_le, maxCard_three_tendsto_atTop, maxCard_three_shift_isEquivalent, maxCard_three_reindex_isEquivalent, maxCard_three_squares_iff. Direct Lean compiled the entire file with the two original hole warnings only. The five new lemmas audit to propext, Classical.choice, and Quot.sound. The prior proof and exact required header are preserved.

Gap: give an explicit f and prove r₃(n²)/f(n) → 1 (or an equivalent directly on all N). Neither the transferred lower bound nor Roth's o(N) upper bound fixes a matching profile. Prior dead ends: the pure powers N^α were all ruled out, and rothNumberNat is the same extremal quantity under another name.

The exact CI checker returned rejected, with reason lint: forbidden: 'sorry'. The two original holes are OMA.answer and OMA.solution.

## Leg 1: gemini  (15:35, 3 min, ended: exit)
File stats: proved lemmas 13, sorries 2, lines 333 (was 13 / 2 / 333)
(the model wrote no notes; see partial_gemini.lean)
