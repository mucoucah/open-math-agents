# Relay notes for Erdos590.erdos_590.variants.finite_cardinal (prize: $250)


## Leg 1: grok  (00:20, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (00:22, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 46 (was 0 / 1 / 10)
# Erdos590 finite_cardinal, leg 2 (opus)
Target: for all m : Nat, OrdinalCardinalRamsey (w^w) (w^w) m. For m at least 3 this is Milnor's theorem
(m=3 is Chang 1972 = the parent erdos_590, itself a research theorem; Larson 1973 short proof is still ~15 pages).
Compiled in proofs file (lake env lean, only warning is the sorry):
- OMA.typeLT_univ_toType : typeLT (univ : Set a.ToType) = a
- OMA.small_m : m at most 2 gives OrdinalCardinalRamsey a a m for any ordinal a (blue edge or red complete)
- OMA.solution glue: splits m at most 2 / m at least 3.
Remaining gap: ONE sorry OMA.milnor (m at least 3). This implies the parent erdos_590 (m=3), so no shortcut.
Dead ends: no loophole (definition is faithful: red clique of order type w^w, blue clique of card m).
Possible next step: port Larson 1973 / the plby lean-proofs Erdos590 (8000 lines) -- not session-sized.

## Leg 3: codex  (00:34, 12 min, ended: exit)
File stats: proved lemmas 25, sorries 1, lines 544 (was 3 / 1 / 46)
# Erdos590 finite cardinal — Codex leg

- Preserved the exact import, `OMA.solution` statement, and the previous `typeLT_univ_toType` and `small_m` proofs. The full file elaborates with one sorry. The required CI command returned `rejected`, reason `lint: forbidden: 'sorry'`.
- `ramsey_on` transports Ramsey relations to subsets. `neighbor_type_lt` uses the preceding blue clique size to bound the order type of each blue neighborhood by an ordinal strictly below the input.
- `strictMono_of_type_le`, `type_range`, `lex_type`, `ordered_blocks`, `type_le_of_blocks`, `omega_le_of_infinite`, `power_le_union`, and `type_biUnion_finset_lt` compile. They supply ordered reservoirs and closure of the sets of order type below a fixed finite ω-power under finite unions.
- `clique_choice`, `clique_of_uniform_bound`, `countable_power`, `nonempty_power`, `finite_power_ramsey`, and `uniform_omega_power` compile. With one common rank bound on the blue neighborhoods, reserve an ordered block per target point and enumerate the target to avoid finitely many earlier choices. For finite red powers, induction on the blue clique size produces the needed common bound.
- `lt_some_power`, `red_block_after`, and `diagonal_red_blocks` compile. In the local-bound case, choose ordered red blocks B_n of type ω^n while excluding the blue neighborhoods and singletons of the first n+1 vertices of a fixed enumeration. For each vertex x, all sufficiently late blocks are entirely red to x. `clique_of_subblocks`, `unbounded_neighbors`, and the induction glue in `milnor` compile conditional on the lemma below.

**Only remaining gap** — `OMA.thin_diagonal_red_blocks`. Thin B_n to D_n ⊆ B_n so that every cross-edge among the D_n is red and their order types remain unbounded among the finite ω-powers. Hypotheses include exclusion of a blue m-clique, local smaller-than-ω^ω blue neighborhood types, no common bound on those types, ordered red B_n, and eventual red adjacency from every individual vertex to the B_n.

**Dead ends** — Eventual red adjacency has a threshold per vertex. It does not yield a uniform threshold on an infinite part of a block. For example, blue edges from an earlier block vertex to later blocks with index at most its enumeration index give this obstruction and have unbounded finite blue cliques. Thus amalgamation must use the finite blue clique bound. Pairwise red relations between block ultrafilters also did not directly solve the issue, because successive filter constraints can discard already scheduled subblocks.

## Leg 4: fable  (00:39, 5 min, ended: stalled)
File stats: proved lemmas 25, sorries 1, lines 544 (was 25 / 1 / 544)
(the model wrote no notes; see partial_fable.lean)
