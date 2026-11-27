# Relay notes for Erdos19.erdos_19.variants.kahn.R1.H1 (prize: )


## Leg 1: grok  (03:41, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (03:43, 1 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 114 (was 0 / 1 / 9)
# notes_opus: Erdos19.erdos_19.variants.kahn.R1.H1
Approach: H1 is exactly Kahn 1996 asymptotic list-edge-colouring (list size D + D/q, rank <= 2q, linear).
Compiled (lake env lean, only warning = sorry) in proofs file, namespace OMAH1:
- meet_le (edges meeting A <= |A| * d)
- greedy (list colouring if each edge has fewer neighbours than list size; strong induction on H)
- nbhd_le (neighbours of A in H.erase A <= |A|*(D-1))
- case_one (q = 1, D0 = 1: 2(D-1) < 2D)
OMA.solution splits q < 2 (done via case_one) / q >= 2 (sorry).
Remaining gap: q >= 2 needs Kahn 1996 nibble/list colouring (neighbours up to 2q(D-1) >> D+D/q); greedy cannot work.
Dead ends: greedy beyond q=1; no loophole (statement faithful, true by Kahn).

## Leg 3: codex  (03:51, 8 min, ended: stalled)
File stats: proved lemmas 16, sorries 1, lines 335 (was 4 / 1 / 114)
Approach: encode (edge, colour) assignments as an auxiliary bipartite hypergraph. A left vertex requests a colour for an edge, right vertices are the exclusive resources (original vertex, colour). A matching saturating the left side is equivalent to a list colouring.
Compiled from prior legs: meet_le, greedy, nbhd_le, case_one.
Gap: q ≥ 2. Plan to isolate the one-sided matching nibble with degree slack and codegree one; Mathlib search found no such theorem. The matching argument in the local Green84 proof bounds total uncovered vertices and requires |V| * codegree = O(D); neither suffices for uniform local control here.
Dead ends: plain greedy for q ≥ 2, as recorded previously.

Compiled new lemmas: mem_choices, mem_slots, slots_card, choice_degree, slot_degree, demand_slot_codegree, slot_codegree, colour_of_matching, case_of_matching. OMA.solution now has one goal at the admitted branch, OneSidedMatching (2 * q) q for q ≥ 2. Exact statement is in the proof file. The type allows indexed options, ranks at most r, demand degree ≥ D + D/q, resource degree ≤ D, and mixed and resource/resource codegree ≤ 1.

Also compiled truncate_choices (exact demand degrees by trimming each fiber), greedy_residual and finish_with_reserve (an explicit deterministic endgame for a partial colouring with unused reserve lists and small residual vertex degree).

In scratch h1_concentration.lean, markAvg_exp_centered compiles without admissions. It bounds the centred exponential moment for a function of independent Bernoulli marks by exp(Σ pᵢ (t bᵢ)²), where bᵢ bounds the effect of flipping mark i and |t| bᵢ ≤ 1. This is suited to pᵢ ~ 1/D and O(D²) relevant marks in a nibble round.

Scratch now also compiles markProb_tail and exists_avoid_marks, a finite symmetric Lovász local lemma for events with disjoint supports on independent Bernoulli marks. Independent two-stage exposure can handle waste: for a demand group of size O(D), expose its O(D²) assignment marks first. There are O(D) marked options with exponentially high probability. Count internal collisions with sparse bounded differences. Conditional on the first exposure, only O(D²) outside marks can hit these marked options; a flip spoils at most rank-many internally isolated options. This keeps the concentration variance on scale D even for waste events.

## Leg 4: fable  (04:00, 8 min, ended: exit)
File stats: proved lemmas 42, sorries 1, lines 894 (was 16 / 1 / 335)
# notes_fable: Erdos19.erdos_19.variants.kahn.R1.H1 (leg 4)

Approach: unchanged. H1 = Kahn 1996 list colouring (rank <= 2q, lists D + D/q). No loophole, no elementary route.
q = 1 is greedy (case_one, done). q >= 2 is the ONE sorry: OMAH1.OneSidedMatching (2 * q) q
(reduction case_of_matching compiles).

Compiled this leg (lake env lean, 6 s, only warning = the one sorry; file now 894 lines, 43 theorems):
- merged the whole Bernoulli section of scratch h1_concentration.lean into the proofs file (namespace OMAH1):
  markAvg_insert/const/mono/mul/sub/congr, bernoulli_exp_bound, markAvg_exp_centered, markProb_tail
  (tail exp(sum p_i (t b_i)^2 - a) for a function of independent marks with flip effect b_i),
  markAvg_mul_disjoint, markProb_and_disjoint, markProb_partition, exists_of_markProb_pos,
  exists_avoid_marks (symmetric LLL: events local to mark sets U j, at most N overlaps, prob <= x(1-x)^N),
  markProb_pattern (probability of a fixed mark pattern on U = product).
- NEW two-stage exposure lemmas (all compile): markAvg_empty, markAvg_add, markAvg_union (Fubini: average over
  U union V = iterated average, U V disjoint), markProb_le_one, markProb_union, markProb_two_stage
  (P_{U+V}(A) <= P_U(not G) + eps if every good first stage S1 has P_V(A(S1 union .)) <= eps).
- NEW union bounds (compile): markProb_or_le, markProb_exists_le (finite family).
- backup of the pre-merge file: .oma/scratch/h1_before_fable.lean

Remaining gap (exact): OneSidedMatching (2 * q) q for q >= 2 = the full nibble. Nothing probabilistic about the
hypergraph itself is proved yet.

Design finding (do this, it avoids a trap): prove the q >= 2 branch in the LIST-COLOURING form, not through the
abstract OneSidedMatching. Reason: the abstract form has no plain vertex degree, so its endgame needs an LLL
finishing lemma with ratio (options per demand)/(resource degree) >= C r log^2, i.e. about log log D rounds.
In list form a CONSTANT number of rounds T(q) suffices and the endgame is the already compiled finish_with_reserve.
Round state: uncoloured K, proper partial colouring of H minus K, lists Lt A (subset of L A, no colour of a coloured
neighbour), with |Lt A| >= l, colour degree #{A in K : v in A, c in Lt A} <= d, plain degree of K <= g.
Round (wasteful nibble): mark each pair (A, c), c in Lt A, independently with prob theta / l; (A, c) is kept if it is
the only mark on A and no neighbour B has mark (B, c); colour c leaves Lt A as soon as ANY neighbour is marked c
(kept or not) or an equalising coin for (A, c) fails (coin chosen so every pair survives with the same prob Keep
= (1 - theta/l)^(r d)). Expected: l' = l Keep, d' = d Keep (1 - theta k), g' = g (1 - theta k), k >= exp(-theta(1+r)).
So ratio l/d grows by 1/(1 - theta k) per round, sum of r theta d/l converges, l stays >= exp(-r) D while g decays
geometrically: after T = O(r/theta) rounds r g < l and finish_with_reserve applies. Slack D/q pays for the errors.
Per round needs: concentration of l'(A), d'(v,c), g'(v) (use markProb_tail; for d' and g' flip effects are only
small after a two-stage exposure: first the marks on edges at v, then the outside marks of those colours; the Fubini
step is now markProb_two_stage), then exists_avoid_marks over all A, (v,c), v
(overlap count is polynomial in D, tails are exp(-D^c)).

Dead ends: greedy for q >= 2; Hall only gives resource rank 1; Haxell needs degree ratio > 2r - 1; one-shot LLL
(expected conflicts per option about r/(1+1/q) >= 1); direct Lipschitz bound for d', g' gives variance D^2 (too big).
Honest size estimate for the round lemma + iteration: several thousand lines; not a single-leg job.
