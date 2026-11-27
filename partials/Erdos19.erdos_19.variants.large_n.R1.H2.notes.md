# Relay notes for Erdos19.erdos_19.variants.large_n.R1.H2 (prize: )


## Leg 1: grok  (03:42, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (03:43, 1 min, ended: exit)
File stats: proved lemmas 1, sorries 1, lines 26 (was 0 / 1 / 9)
# Leg 2 (opus) Erdos19.large_n.R1.H2
Compiled (lake env lean, about 6 s): OMA19H2.inter_card_le_one (distinct blocks of the PBD meet in at most 1 point). OMA.solution still sorry.
Why H2 is research-level (no elementary route):
 - Greedy by decreasing block size colours every block with s*s > n (each such block meets at most s(n-s)/(s-1) < n blocks of size >= s). Small blocks are the problem.
 - Embedding: take ANY PBD D on m points, add k ~ sqrt(m)+1 new points forming one block L, and join each new point to each old point with a 2-block. The result is a PBD on n = m+k points with |L|^2 > n. A colouring from H2 restricts to a colouring of D with m + O(sqrt m) colours.
   So H2 implies EFL with only sqrt slack for every PBD, which is stronger than Kahn's n+o(n) and so needs KKKMO-type nibble plus absorption.
Dead ends: greedy (see above); trying to use the long line L to bound degrees (points off L have degree >= |L|, so degrees go up, not down).

## Leg 3: codex  (03:54, 10 min, ended: exit)
File stats: proved lemmas 10, sorries 1, lines 440 (was 1 / 1 / 26)
# Leg 3 (Codex)
- Preserved the import, exact `OMA.solution` header, and `inter_card_le_one`.
- Compiled `exists_padded_design` and `eventually_color_with_sqrt_slack`. Complete a linear family after adjoining a disjoint block of size floor(sqrt m)+2. Thus H2 implies m+floor(sqrt m)+2 colors for every sufficiently large linear family, even without a large block or pairwise balance.
- Compiled `neighbor_rank_sum_eq`, `fewer_than_n_neighbors_of_ge_rank`, `colorable_insert_of_lt`, `colorable_of_large_min_rank`, and `colorable_of_colorable_cores`. The sum of |B|-1 over neighbors B of A is exactly |A|(n-|A|). Greedy deletion reduces to subfamilies where each block has at least n neighbors. All-large subfamilies are colorable.
- Compiled `cross_pairs_le_neighbors` and `min_rank_sq_lt_of_large_block`. If the smallest block A of a remaining subfamily had |A|²=n, the weight bound forces exactly n neighbors in the ambient design, all of size |A|. The ambient large block L must be disjoint from A. The |A||L| pairs crossing A and L give that many distinct neighbors of A, a contradiction.
- Exact gap is the single `hsmall` proof in `OMA.solution`. Eventually, color any subfamily S of a PBD K with a large block, when every block of S meets at least n others in S and the minimum squared rank is strictly below n. The large block of K may lie outside S. Direct `lake env lean` compiles with the warning for this one placeholder.
- Dead ends: decreasing-size greedy only handles large ranks. A large block does not uniformly lower degrees off it. The other local reductions handle special structures, and none supplies the general small-rank coloring or a formal asymptotic EFL theorem.
- CI checker verdict: rejected at lint solely for the remaining `sorry`.

## Leg 4: fable  (03:56, 2 min, ended: exit)
File stats: proved lemmas 10, sorries 1, lines 440 (was 10 / 1 / 440)
# Leg 4 (fable) Erdos19.erdos_19.variants.large_n.R1.H2

Verdict: STALLED, stopped early on purpose. No change to the proof file (still 440 lines, 10 proved lemmas, ONE sorry).

## State of the file (re-verified this leg)
Direct compile `cd /workspace/left-to-solve/repo/.oma/formal-conjectures && lake env lean <abs path>` takes 5 s and reports only
`415:8 declaration uses sorry` (the `hsmall` have inside `OMA.solution`). Everything else compiles:
inter_card_le_one, neighbor_rank_sum_eq, fewer_than_n_neighbors_of_ge_rank, cross_pairs_le_neighbors,
min_rank_sq_lt_of_large_block, colorable_insert_of_lt, colorable_of_large_min_rank, colorable_of_colorable_cores,
exists_padded_design, eventually_color_with_sqrt_slack. check.sh would reject at lint (sorry) without compiling.

## Exact remaining gap (`hsmall`)
Eventually in n: for a PBD K on Fin n with a block L, n < |L|^2, and any S ⊆ K such that
 (1) some A in S has |A|^2 < n, and
 (2) every A in S meets at least n other blocks of S,
S has a proper colouring Finset (Fin n) -> Fin n. L need not be in S.

## Why this is not a session-sized step (the reason is itself Lean-checked)
`eventually_color_with_sqrt_slack` (compiled) shows H2 implies: for all large m, EVERY linear family on Fin m
(blocks of size >= 2, no large block, no balance needed) is properly colourable with m + floor(sqrt m) + 2 colours.
The best elementary bound is Chang-Lawler ceil(1.5 m - 2); m + o(m) is Kahn 1992 (nibble), and an additive
O(sqrt m) error term is only known through KKKMO21 itself. So any proof of H2 must contain a nibble-type
argument; none of that is in Mathlib. The case split of R1 does not make H2 easier than the parent.

## Checked this leg (pen and paper, not in the file)
- No loophole in the statement: card products are in Nat, colours are Fin n, K is a genuine PBD.
- Greedy cannot be rescued even for a huge block: with |L| = n - 2, complement {x, y}, blocks L, {x,y} and all
  {p,x}, {p,y} (p in L), EVERY block has at least n neighbours, so S = K is already a core. It is colourable only
  because L and {x,y} share a colour, i.e. colour classes must be chosen as matchings, not greedily.
- Degree facts for whoever continues: a point off L lies on at least |L| blocks; a block {p,x} with p in L has
  up to n + (n - |L|) - 2 neighbours; a block A disjoint from L has at least |A||L| neighbours
  (cross_pairs_le_neighbors).
- No converse: sqrt-slack colourings of K restricted to the complement of L do not lift, because blocks sharing a
  point of L must also get distinct colours.

## Dead ends (do not repeat)
- Greedy in any order (decreasing size handles only |A|^2 > n; increasing size fails at the large blocks).
- Using L to lower degrees (it raises them off L).
- More restatements of the core: the gap is equivalent in strength to sqrt-slack EFL, reformulation is exhausted.
- Looking for a vacuous range or a loophole: none.

## Advice to the next leg
Unless you can formalise a Kahn-type nibble with additive sqrt error, stop at once and report STALLED.
The only honest way forward on the site is a further reduction of `hsmall` into named research statements.
