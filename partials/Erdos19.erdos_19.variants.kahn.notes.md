# Relay notes for Erdos19.erdos_19.variants.kahn (prize: $500)


## Leg 1: grok  (23:18, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (23:20, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 84 (was 0 / 1 / 10)
# opus leg 2 notes: Erdos19 kahn
Target = Kahn 1992 (chi <= (1+o(1))n for EFL), via dual: proper edge colouring of a linear
hypergraph on n vertices with (1+eps)n colours. Needs Pippenger-Spencer nibble; faithful, no loophole
(V arbitrary Type, floor((1+eps)n) >= n only). Not session-sized.
Plan: glue = generalise colorable_of_sharedColoring to m >= n colours, reduce to a single sorry
kahn_shared (colour shared vertices with floor((1+eps)n) colours, distinct inside each clique).

## Compiled (lake env lean in formal-conjectures, only warning: kahn_shared uses sorry)
- OMA19.colorable_of_sharedColoring_le (m >= n colours version of upstream colorable_of_sharedColoring)
- OMA19.le_floor_mul : n <= floor((1+eps) n)
- OMA.solution glue: filter_upwards [kahn_shared] then the two lemmas above.
## Exact remaining gap: OMA19.kahn_shared
 for eps>0, eventually in n, every EFLConfig V n has c : V -> Fin floor((1+eps)n) injective on the
 shared vertices of each clique A i. = chromatic index of a linear hypergraph on n vertices
 <= (1+o(1))n (Kahn 1992, Pippenger-Spencer nibble). Not in Mathlib.
## Dead ends
- Greedy: a shared vertex in d cliques conflicts with up to d(n-1) others; fails.
- Chang-Lawler 3n/2 bound and Vizing-type arguments give only constant factor > 1.
- No loophole: statement faithful, V arbitrary, floor((1+eps)n) only >= n.
check.sh rejects at lint (sorry) as expected; compile check: copy file into formal-conjectures dir, lake env lean.

## Leg 3: codex  (23:29, 9 min, ended: stalled)
File stats: proved lemmas 14, sorries 1, lines 423 (was 3 / 1 / 84)
# Codex leg 3

Preserved the existing private-vertex extension, floor lemma and OMA.solution.
Plan: dualize to a finite linear family, then split the rank at constants r and R.
Color rank >= R first in descending order of rank. If the next rank is s,
each point belongs to at most n/(s-1) prior supports, so the conflict count is
at most n + n/(R-1). Put ranks r..R-1 in their own palette, using the bounded-rank
asymptotic list-edge theorem with degree bound n/(r-1). For ranks < r, use
the main palette with the large-support colors removed from each list.
Each such list loses at most r*n/(R-1) colors. Pick r large relative to 1/eps
and R large relative to r/eps.
Currently the existing compiled lemmas are colorable_of_sharedColoring_le and
le_floor_mul, with the solution calling kahn_shared. Starting the deterministic
rank-reduction lemmas. Mathlib has no Kahn or Pippenger-Spencer theorem by name.
The earlier unrestricted greedy dead end does not handle small ranks.

Compiled additions: Linear.mono, incident_mul_le, meeting_card_le, large_rank_color.
The descending-rank greedy bound is n + floor(n/q) + 1 colors for rank >= q+1.
Next: formalize palette assembly, floor budget and transfer back to EFL.

## Site hints (2026-11-26)

https://www.erdosproblems.com/19 (YAML: decidable — full EFL reduced to finitely many n). This variant is Kahn [Ka92], *Coloring nearly-disjoint hypergraphs with n+o(n) colors*, JCTA 1992: χ(G) ≤ (1+o(1))n. Follow that paper. Forum comments do not give a shorter proof. Write-up: /workspace/left-to-solve/research/erdosproblems.md

## Leg 4: fable  (23:32, 3 min, ended: exit)
File stats: proved lemmas 14, sorries 1, lines 424 (was 14 / 1 / 423)
# Fable leg 4 notes: Erdos19 kahn

## Approach (unchanged from codex leg 3)
Dualise EFL to a linear family H on Fin n (supports of shared vertices), split by rank:
large ranks greedy, small ranks list-coloured avoiding the large colours, middle ranks in
their own small palette. Everything is glue around ONE deep input.

## What compiles now (lean_local.sh, 5 s, only warning = the one sorry)
Leg 3 left the file NOT compiling (2 errors in palette_le_floor, which also broke kahn_shared).
Fixed both: binder is now (n : Nat) with an explicit real cast, and q > 0 via rcases.
Whole file now elaborates. Compiled lemmas:
colorable_of_sharedColoring_le, le_floor_mul, Linear.mono, incident_mul_le, meeting_card_le,
large_rank_color, support, mem_support, support_inter_le, shared_of_linear_color,
ProperOn.map, ProperOn.piecewise, linear_color (uses the sorry), palette_le_floor,
kahn_shared (uses the sorry), OMA.solution (uses the sorry).

## Exact remaining gap: OMA19.bounded_rank_list_color (the only sorry)
For all r, q>0 there is D0 such that for every linear H on Fin n with 2 <= |A| <= r,
max degree <= D, D >= D0, and lists L A in Fin m with |L A| >= D + D/q, there is a proper
list colouring. This is Kahn 1996 (asymptotically good list colourings) for linear hypergraphs
of bounded rank = Pippenger-Spencer nibble with lists. Not in Mathlib (no nibble, no LLL).
It is used twice in linear_color: (r=2q, q) with D=n, and (r=2q^2, q=1) with D=n/(2q).

## Dead ends
- Greedy for small ranks: an edge of rank s meets up to s*D others, needs s*D colours.
- Chang-Lawler / Vizing type arguments: constant factor > 1 only.
- No loophole in the statement (V arbitrary Type, floor((1+eps)n) >= n only).
- eps >= 1 alone is easy (greedy, 2n colours) but does not help for small eps.

## Final state of leg 4 (stopped early: remaining gap is not session-sized)
- tools/check.sh verdict: rejected, reason = lint: forbidden sorry. No other lint issue
  (no double-quote character, first import line and OMA.solution statement untouched).
- Compile check: bash .oma/scratch/lean_local.sh proofs/Erdos19.erdos_19.variants.kahn.lean
  (5 s) prints only the sorry warning at bounded_rank_list_color.
- The sorry statement is a TRUE theorem (Kahn 1996 with codegree <= 1), so nobody is chasing
  a false lemma, but it needs the full semi-random method (nibble + concentration + local lemma).
- Why no cheaper route: greedy cost is rank x degree, about n for every rank class, so every
  class below the greedy threshold needs a (1+delta) factor theorem. Even the list-free middle
  palette (factor 2 at rank up to 2q^2) is not elementary. Do not retry threshold reshuffles.
- Only sensible next step for a long session: formalise a nibble for bounded-rank linear
  hypergraphs with lists. Nothing shorter closes the file.
