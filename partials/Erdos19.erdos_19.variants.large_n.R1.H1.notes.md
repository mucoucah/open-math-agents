# Relay notes for Erdos19.erdos_19.variants.large_n.R1.H1 (prize: )


## Leg 1: grok  (03:41, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (03:42, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
# Leg 2 (opus) notes: Erdos19 large_n R1.H1
Approach: none viable. H1 = EFL for linear spaces (PBD) with all blocks of size k, k^2 <= n, for large n.
This is the core of Kang-Kelly-Kuhn-Methuku-Osthus 2021 (small-edge nibble + absorption), a research paper.
Elementary bound fails: block of size k meets up to k(n-k) other blocks, so greedy needs k(n-k) < n -- false.
Compiled: nothing new (file still one sorry, statement untouched).
Gap: entire statement H1.
Dead ends: greedy / degree counting (line-graph degree up to k(n-k)); no loophole (statement faithful, Fin n colours, K arbitrary).
Recommendation: report FAILED / STALLED fast pass.

## Leg 3: codex  (03:53, 10 min, ended: exit)
File stats: proved lemmas 19, sorries 1, lines 439 (was 0 / 1 / 9)
# Leg 3 (Codex)

Approach: count exact pair budgets through each point and around each block. Rank-two families color by the sum of the endpoints in `Fin n`. Uniform designs on r² points color by selecting, for each block, its unique parallel representative through a fixed point. Then pass to an inclusion-minimal uncolorable subfamily of the input design.

Compiled using pinned Lean: `block_eq_of_pair`, `links_disjoint`, `link_weight_eq`, `meeting_weight_eq`, `pair_of_mem_of_card_two`, `color_two_blocks`, `extend_coloring_of_unused`, `extend_coloring`, `all_colors_blocked`, `exists_critical_subfamily`, `meeting_card_mul_le_sum`, `meeting_card_mul_le`, `uniform_square_saturation`, `critical_pair_neighbor_card`, `through_meeting_card`, `uniform_through_card`, `existsUnique_parallel_through`, `color_uniform_square`. `OMA.solution` elaborates with the single hole below.

Gap: `eventually_no_critical_subfamily`. For sufficiently large n, rule out an uncolorable L inside a unique-pair design K with block ranks from 2 to sqrt(n). Every one-block deletion from L is n-colorable, but every such coloring uses all n colors on the deleted block’s neighbors. L has a block of rank at least 3 and a block of rank strictly less than sqrt(n). Each rank-two block in L has at least four rank-two neighbors in L. The eventual threshold remains available to the proof.

Dead ends: raw greedy degree counting cannot handle mixed or small ranks. No Vizing edge-coloring theorem or Brooks theorem was found in the pinned Mathlib graph library. No general construction for the remaining critical designs was found.

Prescribed checker verdict: rejected at lint for the one remaining sorry. Direct Lean elaboration produced only that warning.

## Leg 4: fable  (03:56, 2 min, ended: exit)
File stats: proved lemmas 19, sorries 1, lines 439 (was 19 / 1 / 439)
# Leg 4 (fable) notes: Erdos19 large_n R1.H1

Approach: none new that is viable. Re-verified the leg 3 file and audited the remaining gap. Proof file left byte-identical to leg 3 (no lemma lost).

Compiled (re-checked with `bash .oma/scratch/lean_codex.sh proofs/Erdos19.erdos_19.variants.large_n.R1.H1.lean`, 5 s, only output is the sorry warning at line 377):
`block_eq_of_pair`, `links_disjoint`, `link_weight_eq`, `meeting_weight_eq`, `pair_of_mem_of_card_two`, `color_two_blocks`, `extend_coloring_of_unused`, `extend_coloring`, `all_colors_blocked`, `exists_critical_subfamily`, `meeting_card_mul_le_sum`, `meeting_card_mul_le`, `uniform_square_saturation`, `critical_pair_neighbor_card`, `through_meeting_card`, `uniform_through_card`, `existsUnique_parallel_through`, `color_uniform_square`, and `OMA.solution` modulo the one hole.

Exact remaining gap: `eventually_no_critical_subfamily` (line 377), the only sorry. For large n: no vertex-critical uncolourable subfamily L of a linear space K on Fin n with all block sizes in [2, sqrt n]. This is NOT a small residue, it is the whole theorem again:
- Take K = any Steiner triple system on n points. The gap then says: chromatic index of every large STS(n) is at most n. Only known via nibble (Pippenger-Spencer / Kahn); greedy gives 3(n-3)/2 + 1.
- There is no slack to burn: K = complete graph on odd n needs exactly n colours, and a complete graph with one triangle merged still needs n. So any proof must be exact near the extremal cases. That is the small-edge regime of Kang-Kelly-Kuhn-Methuku-Osthus 2021 (nibble plus absorption, about 100 pages, nothing of it in Mathlib).
- No loophole: hypotheses are satisfiable for every n (complete graph), colours are Fin n, `∃!` pair condition is the faithful linear-space axiom.

Dead ends (do not repeat):
- Greedy / degeneracy in any order: a rank-k block meets up to k(n-k)/(r-1) blocks of rank >= r; this is < n only when k^2 > n, i.e. exactly the regime excluded here.
- Pair-budget counting on a critical L: for the minimum-rank block it yields only r^2 <= n (consistent, no contradiction); equality case is already `uniform_square_saturation` + `color_uniform_square`. For a rank-k block it yields only a neighbour of rank <= k.
- Sum colouring (`color_two_blocks`) does not extend to rank >= 3: {i,j,k} and {i,j',k'} with j+k = j'+k' collide.
- No Vizing / Brooks / hypergraph edge-colouring in pinned Mathlib (leg 3 searched).
- More restatements of the gap are pointless (the parent problem already had an iff-reformulation, see memory note erdos19-large-n-dead-ends).

Recommendation: stop the relay on this step; report STALLED/FAILED. If a further reduction is wanted, split the gap by maximum block rank (bounded rank r <= R: Kahn-type list colouring; rank between R and sqrt n: KKKMO medium-edge reservoir argument), but both halves stay research-level.

Checker: not rerun (file unchanged from leg 3, it lints out on the one sorry).
