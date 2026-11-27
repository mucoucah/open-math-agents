# Notes for BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two
- Opus 2h retry (C-2047) left TriangleFactor proved, CycleStep open (R1 reduction PR #2769 submitted: H1 TriangleFactor, H2 CycleStep).
- Codex gpt-6.2-sol leg (22:58-22:11, ~14 min) closed everything except one sorry inside CycleStep: remaining case = several cycles, n < 4d (d = maxDegree G2), every component has at most 8d+3-2n vertices. partial.lean is Codex's file (~6200 lines).
# Lesson: BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two

- Updated: 2026-11-26 20:42:48 CST
- Run: `BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two-E-1739`
- Model: fable
- Verdict: rejected | does not compile
- File size: 686 lines; proved lemmas/theorems: 11; remaining sorry: 0
- No-waste outcomes: partial:lemmas/partial/BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two.ref.lean; lemma-request; lesson; retry-queued:opus:1/2; retry queued on opus (attempt 1/2), 2-hour budget, continue from previous final.lean
- Exact blocker: file does not compile (no sorry, unsolved goal or type error)

## What was tried
Driver segments:
- claude segment 4 (model fable, effort max, ~3 min left)
- claude segment 4 exit 0
- claude segment 5 (model fable, effort max, ~3 min left)
- claude segment 5 exit 0
- claude segment 6 (model fable, effort max, ~2 min left)
- claude segment 6 exit 0
- claude segment 7 (model fable, effort max, ~2 min left)
- claude segment 7 exit 0

## Remaining holes
- The file has no `sorry` but does not compile (likely an unsolved tactic goal or a type error).

## Proved lemmas to reuse
- `lemma mem_conf` (5 lines)
- `lemma step` (123 lines)
- `lemma sauer_spencer` (16 lines)
- `lemma leaf_step` (114 lines)
- `lemma reduce_to_cycles` (47 lines)
- `lemma packs_of_almost` (15 lines)
- `lemma relocate` (132 lines)
- `lemma double_relocate` (93 lines)
- `lemma almost_packing` (26 lines)
- `theorem solution_of_cycleStep` (49 lines)
- `theorem OMA.solution` (4 lines)

## Earlier notes

# Lesson: BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two

- Updated: 2026-11-26 20:42:48 CST
- Run: `BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two-E-1739`
- Model: fable
- Verdict: rejected | does not compile
- File size: 686 lines; proved lemmas/theorems: 11; remaining sorry: 0
- No-waste outcomes: 
- Exact blocker: file does not compile (no sorry, unsolved goal or type error)

## What was tried
Driver segments:
- claude segment 4 (model fable, effort max, ~3 min left)
- claude segment 4 exit 0
- claude segment 5 (model fable, effort max, ~3 min left)
- claude segment 5 exit 0
- claude segment 6 (model fable, effort max, ~2 min left)
- claude segment 6 exit 0
- claude segment 7 (model fable, effort max, ~2 min left)
- claude segment 7 exit 0

## Remaining holes
- The file has no `sorry` but does not compile (likely an unsolved tactic goal or a type error).

## Proved lemmas to reuse
- `lemma mem_conf` (5 lines)
- `lemma step` (123 lines)
- `lemma sauer_spencer` (16 lines)
- `lemma leaf_step` (114 lines)
- `lemma reduce_to_cycles` (47 lines)
- `lemma packs_of_almost` (15 lines)
- `lemma relocate` (132 lines)
- `lemma double_relocate` (93 lines)
- `lemma almost_packing` (26 lines)
- `theorem solution_of_cycleStep` (49 lines)
- `theorem OMA.solution` (4 lines)



## Focused leg 1: fable  (22:33, 13 min, ended: exit)
File stats: proved lemmas 115, sorries 1, lines 6377 (was 113 / 1 / 6330)
# notes_fable (FOCUSED GAP leg 1, BEC maxDegree_le_two)

## Status (end of leg): STALLED on the mathematics, file compiles with ONE sorry
- Proof file compiles (lake env lean, rc 0, 1m30s); the only sorry is the body of
  `OMA.smallCycleStep_holds : SmallCycleStep` (line ~6272).
- New this leg (compiled):
  * `def OMA.SmallCycleStep : Prop` = exactly the open case as a standalone statement.
  * `theorem OMA.cycleStep_of_small : SmallCycleStep -> CycleStep` (NO sorry; it is the old
    `cycleStep_partial` proof: equality case, one-cycle case, large-component case).
  * `cycleStep_partial := cycleStep_of_small smallCycleStep_holds`.
- Reduction candidate (def-free, lint ok, checker verdict: see bottom line of this file):
  `.oma/scratch/reductions/<id>.R6.lean`: H1 = triangle factor (proved in the proof file as
  `triangleFactor_holds`), H2 = SmallCycleStep. Sharper than R1/R5 (H2 there = all of CycleStep).
  Check it from `.oma/scratch` with an ABSOLUTE path:
  `OMA_FC=... ../../tools/check.sh /abs/.../reductions/<id>.R6.lean /tmp/v.json`.
- Note: tools/check.sh on the proof file stops at lint (forbidden sorry) BEFORE compiling; to
  see compile errors run `cd $OMA_FC && lake env lean /abs/path/to/proofs/<id>.lean`.

## The open case (SmallCycleStep)
d = maxDegree G2 >= 3, 3d+2 <= n <= 4d-1, C = disjoint cycles + isolated vertices,
at least two cycles, EVERY component has <= 8d+3-2n vertices (so <= 2d-1; <= 5 when n = 4d-1),
xy a non-triangle conflict edge of an almost-packing sigma (plus relocation/absorb data).
The goal is TRUE (it is the Aigner-Brandt theorem itself), not false as stated.

## PLAN (informal) and why it is not finished
Write s = 4d - n (1 <= s <= d-2), H = complement of sigma-image of G2 (every vertex has <= d
non-neighbours), A = cycle of xy with a = L+1 <= 2s+3 vertices, path y=p_0,...,p_L=x,
S = V \ A, Nb(v) = bad (G2) neighbours of v.
1. (in file) single swaps x<->w, y<->w for w outside A plus inner rotations give
   |Nb(x) n A| + |Nb(y) n A| >= L, |S| <= |Nb(y) n S| + |Nb(u) n S| + 2|Nb(x) n S| and the
   mirror bound, hence 2n + a <= 8d+3. This is exactly hypothesis 5 of SmallCycleStep and is
   NOT contradictory: e.g. a = 4, n = 4d-1, Nb(x) = {y,v} + (d-2) outside,
   Nb(y) = {x} + (d-1) outside satisfies every cover condition.
2. Extra moves needed (not in file):
   (a) Posa rotation as a transformer: if x ~H p_i (1 <= i <= L-2), reversing p_{i+1..L} gives a
       NEW almost-packing, same conflict edge, x-image sigma p_{i+1} (the involution f in the
       proof of `rotate` already does this; only the last branch of hcase uses hy). All bounds of
       step 1 then hold for every rotated endpoint. I checked that ONE such rotation only
       improves the bound by 1 (2(n-a) <= 8d-3L-1), so a real Posa-set argument is needed.
   (b) swaps of x with w INSIDE A (cycle_swap_clean allows it).
   (c) IH on other smaller graphs: A replaced by (a-1)-cycle + isolated vertex; two cycles
       replaced by one path on a+b vertices; a whole cycle made isolated.
   (d) any 2-regular C1 with |E(C1)| <= |E(C)| having a component > 8d+3-2n packs
       (IH + cycle_pack_by_component_size), e.g. two cycles merged; splitting back needs chords.
3. Link counting: every w != x,y needs a link x-C-b-G2-w or x-G2-a-C-w (<= 4d-2 links);
   n = 4d-s leaves s spare links while a <= 2s+3. Closing this trade-off for all s is the
   12-page core of Aigner-Brandt (J. London Math. Soc. 48 (1993) 39-51); I found NO short
   argument. Realistic size: comparable to the pasted Hajnal-Szemeredi block (thousands of lines).

## Dead ends (do not repeat)
- single swaps + inner rotations: stop at 2n + a <= 8d+3 (see 1).
- one extra Posa rotation: gains only 1.
- n = 4d-1 by rigidity (as in cycle_tight_links): would need a case split over the single
  unit of slack and does not extend to n <= 4d-2.
- Hajnal-Szemeredi cliques (sizes 3..4 only) + linking: link graph too sparse.
- merging two cycles keeps the edge count, so IH alone does not apply; via the repair lemma
  the merged graph packs, but splitting needs two chords that need not exist.
- making a second cycle isolated via IH and closing A with one-component counting is circular
  (it only re-proves that C minus a cycle packs).
- WLOG n <= 3d+4 (enlarge G2) does not shrink the open case.

## Checker results (this leg)
- proofs file: compiles, one sorry (smallCycleStep_holds); check.sh verdict = rejected (lint: sorry).
- reductions/<id>.R6.lean: check.sh verdict = ACCEPTED (kernel accepted; axioms propext,
  Classical.choice, Quot.sound). H1 = triangle factor, H2 = SmallCycleStep.

## Focused leg 2: grok  (22:42, 8 min, ended: stalled)
File stats: proved lemmas 115, sorries 1, lines 6377 (was 115 / 1 / 6377)
(no notes written; see partial_grok.lean)

## Focused leg 3: codex  (22:55, 13 min, ended: exit)
File stats: proved lemmas 115, sorries 1, lines 6377 (was 115 / 1 / 6377)
## PLAN

I have a local switching reduction, with the final implication still open. The
brief cites Aigner–Brandt but supplies no text of their proof, and I found no
copy inside this worktree.

1. Assume no packing. Relabel the host by the given permutation, write
   (B(u,v)) for a forbidden pair, and let (u) be the other cycle neighbor
   of (x). Take any vertex (z) outside the conflicting cycle with
   neither (B(z,y)) nor (B(z,u)).
2. Swapping (x,z) repairs both edges at (x). The only possible new
   conflicts are at (z), one for each cycle neighbor (b) of (z) with
   (B(x,b)). Zero such neighbors gives a packing. Exactly one gives an
   almost-packing whose only conflict is on a different cycle, with the
   same host vertex at one end of the conflict. This uses the supplied
   almost-packing, degree-two hypothesis and exterior reachability.
3. If a placement criterion can exclude that transfer into a collection
   (S) of exterior vertices closed under cycle neighbors, every member
   of (S) lies in (N_B(y) cup N_B(u)) or receives two links through
   (N_B(x)). Counting the links yields
   (|S| le |N_B(y)cap S|+|N_B(u)cap S|+|N_B(x)cap S|).
   The outstanding implication is to force such a transfer exclusion
   (or a repair after transfer) from the remaining hypotheses when every
   component is small. The ordinary single-swap bound from the handover
   does not supply it.

No counterexample is known; the statement is a case of Aigner–Brandt.

## Compiled progress

- `conflict_transfer.lean` compiles with the pinned Lean environment. It
  contains `swap_transfers_conflict`, `swap_transferred_edge`, and
  `pack_or_transfer_of_exterior_card`. The third lemma formalizes all three
  steps above (counting ordered pairs by reversing them).
- Apply the bound with the full exterior (S). Because the original conflict
  spends one unit of each of (x,y)'s forbidden degree inside the conflicting
  cycle, ( |S|>3d-2 ) implies a packing or a single conflict on a different
  component. The transported endpoint keeps the same host vertex.
- Exact blocker remains: an almost-packing with its conflict on another small
  cycle need not close by the existing size lemma. Need a repair after the
  transfer, or an extremal placement/packing argument that excludes transfers
  into enough of the exterior. No changes to the target file yet.

## Extremal placement and local limitation

- `exterior_card_of_minimal_conflict` also compiles. Fix a host vertex
  (X) as one end of the conflict. Minimize the number (q) of its
  forbidden neighbors in the conflicting cycle over all almost-packings
  with that fixed endpoint. Swapping (X) into a different cycle cannot
  increase the number of its forbidden neighbors there. Thus one can take
  (S) to be the union of exterior components with fewer than (q) such
  neighbors, and the three-term bound holds for that (S). The original
  packing hypotheses still allow (S) to be too small (in particular,
  (q=1) only excludes cycles with zero such neighbors).
- A local example shows why the packing-or-transfer disjunction cannot be
  strengthened to packing by a single transposition. On vertices 0 through
  10 take cycles ((0,1,2,3)), ((4,5,6,7)), and ((8,9,10)).
  Forbidden edges are
  (01,02,08,17,18,25,27,34,35,36,49,4{10},59,68,6{10},7{10}).
  The original placement conflicts only at (01). Exhausting all
  transpositions gives no repair. Swapping 0 and 9 transfers the conflict
  to (89); a further swap of 3 and 8 repairs it. This is a limitation of
  the local argument, and the example does pack.
- The prescribed checker was run on the target. Verdict `rejected`,
  reason `lint: forbidden: 'sorry'`, at the original gap.

## Counting over all slots

- `pack_or_move_fixed_endpoint` compiles. It applies under the original
  (nge 3d+2) assumption without a condition on the exterior size.
  Exclude the two red neighbors (y,u) of (x) and their forbidden
  neighborhoods. There are at least (n-2d-2ge d) candidate slots.
  The old slot (x) is not a candidate because (xy) is forbidden.
  Unless a swap packs or leaves a lone conflict incident to the same
  host vertex, each candidate needs two links. There are at most (2d-1)
  usable links since (x)--(y)--(x) ends at the excluded old slot.
- This move can stay in the same component or be reversible. Existence
  of a move at every placement is insufficient to force a packing.
  Possible additional leverage is to count all admissible moves with
  their destinations and prove an escape from a closed family of
  almost-packings. No such escape argument is proved.

- An exterior move is not guaranteed at the threshold. Use the same
  three cycles as above and forbidden edges (01,04,06,14,16,28,29,2{10},
  38,39,3{10}). For either pivot 0 or 1, slots 4,6 are blocked by the
  opposite endpoint and 8,9,10 by the other cycle neighbor of the pivot.
  The remaining exterior slots 5,7 each have two forbidden links to the
  pivot. Both endpoints have the prescribed relocation to 4. The
  instance packs by the interior swap of 0 and 3.
- The target proof is unchanged. Closing a conflict in an arbitrary
  collection of small cycles is the sole unresolved goal.

## Focused leg 4: opus  (23:03, 7 min, ended: exit)
File stats: proved lemmas 116, sorries 1, lines 6481 (was 115 / 1 / 6377)
# notes_opus (FOCUSED GAP leg 4, BEC maxDegree_le_two, OMA.smallCycleStep_holds)

## PLAN
Setting at the sorry (d = maxDegree G2 >= 3, n = card V, H = complement of G2 pulled back
by sigma, t = n - 3d - 2 >= 0, 4d - n >= 1):
C = disjoint cycles + isolated vertices, >= 2 cycles, every component has
<= 8d+3-2n = 2d-1-2t vertices, IH: every max-degree-2 graph with fewer edges packs,
sigma = almost-packing with single conflict xy (xy in no triangle) + absorb + relocation data.

The case is TRUE (it is a sub-case of the Aigner-Brandt theorem); I found no counterexample
and no vacuity (codex leg exhibited 11-vertex instances satisfying all local hypotheses).

Informal proof route (what a complete proof needs; numbered for formalization):
1. Freedom of the conflict position: for every cycle B of C and every edge e of B the IH
   applied to C - e gives an almost-packing with conflict at e (or a packing). So the
   conflict may be put on any non-triangle cycle; relocation/absorb data come with it
   (relocate, absorb, double_relocate). All components are small, so this choice gives no
   counting gain by itself.
2. Posa closure at both ends: R_x = set of x-end images reachable by rotations (rotate
   lemma, y-end fixed). No packing => R_x subset N_G2(sigma y), |R_x| <= d.
3. Exterior exchange (swap with w outside the cycle A of xy): for every endpoint r in R_x
   with predecessor r-, each exterior w is blocked by sigma w in N(sigma y) or N(r-) or a
   C-neighbour b of w with sigma b in N(r). Counting with |N(sigma y) n sigma Ext| <= d-|R_x|
   and Posa |N_H(r) n sigma A| <= |R_x|+2 gives only n <= 4d - a + 4 + |R_x| (NO contradiction).
4. The missing step is the Aigner-Brandt exchange analysis combining (2),(3) for BOTH ends
   with swaps inside other cycles (moving a whole exterior cycle or transferring the
   conflict to another cycle and coming back). This is the 12-page core of
   Aigner-Brandt, J. London Math. Soc. 48 (1993) 39-51; not reconstructible here.

Partial idea checked on paper (needs restructuring, NOT formalized):
5. Vertex deletion: if some cycle B (length k) satisfies k <= t, embed B on any k-cycle of H
   (H has min degree >= (2n-1)/3, k-cycles exist greedily) placed on S, then
   G2 - S has max degree <= d and 3(d+1) <= (n-k)+1, so C - B packs with G2 - S by the
   theorem for n-k vertices (requires turning OMA.solution into strong induction on n).
   Remaining after 5 + cycle_pack_by_component_size: every cycle length k has
   t < k <= 2d-1-2t, possible iff t <= (2d-2)/3. Still open.
6. Merging two cycles A,B into one (a+b)-cycle keeps the edge count, so it packs by
   cycle_pack_by_component_size when a+b > 2d-1-2t, but splitting back needs the two chords
   z_i z_(i+a-1), z_(i+a) z_(i-1) for some i; G2 can kill all a+b splits using only 2 of its
   d neighbours per vertex. Dead end alone.

## Status
- leg start: proof file unchanged (1 sorry at smallCycleStep_holds).
- NEW compiled helper (scratch .oma/scratch/opus/rot.lean compiles, rc 0; inserted in the proof
  file right after `rotate`, line ~5038): `OMA.rotate_almost` = Posa rotation as a TRANSFORMER.
  Same hypotheses as `rotate` minus `hy`; conclusion: exists sigma' with the almost-packing
  property for the same conflict edge xy, sigma' x = sigma (p (i+1)), sigma' y = sigma y, and
  sigma' v = sigma v for every v outside the segment p (i+1) .. p L. This is the building block
  for the Posa-set step 2 of the PLAN (iterate rotations, R_x subset N_G2(sigma y)).
  Backup of the file before the insertion: .oma/scratch/opus/backup_before.lean.

## Exact blocker (unchanged)
The body of `OMA.smallCycleStep_holds`: the Aigner-Brandt exchange analysis (PLAN step 4).
Local moves available in the file (single swaps, inner rotations, relocations, absorb,
double relocation, now rotate_almost) only yield 2n + a <= 8d+3, which is exactly the
hypothesis of the open case, not a contradiction. Next legs: a multi-session formalization
of the A-B paper (or Fan-Kierstead square path), NOT more local swap counting.

## Dead ends (this leg, add to the list in handover_notes)
- naive Posa-set + exterior swap counting: n <= 4d - a + 4 + |R_x|, no contradiction.
- vertex deletion of a short cycle (length k <= n-3d-2) works only after restructuring to
  strong induction on n and leaves all cycles of length in (t, 2d-1-2t].
- merge two cycles + split by chords: G2 can block every split.

## Checker results (this leg)
- Full proof file with `rotate_almost` inserted: lake env lean rc 0; the only warning about
  sorry is at line 6378 (`smallCycleStep_holds`). The file is now 6476 lines.
- tools/check.sh verdict: rejected | lint: forbidden: sorry (same gap as at the start).
RESULT: STALLED. Blocker: the body of OMA.smallCycleStep_holds, i.e. the Aigner-Brandt exchange
analysis (PLAN step 4). Needs a plan spanning several sessions, not more local swaps.
