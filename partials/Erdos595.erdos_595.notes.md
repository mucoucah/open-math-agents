# Relay notes for Erdos595.erdos_595 (prize: $250)


## Leg 1: opus  (09:53, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos595.erdos_595 notes (opus leg 1)
Approach: none viable. Target = exists infinite K4-free graph not a countable union of triangle-free graphs.
Faithful to the open Erdos-Hajnal $250 problem (only finite Folkman/Nesetril-Rodl version known;
infinite version: consistency results only, Shelah-type forcing; ZFC status open).
Loophole check: IsCountableUnionOfTriangleFree requires G = iSup H i with each H i CliqueFree 3 on the
same V; universe-polymorphic V : Type u but no trick; Infinite V needed; CliqueFree 4 genuine. No loophole.
Compiled: nothing new (file is the trivial sorry skeleton).
Remaining gap: the entire open problem.
Dead ends: none worth repeating; do not spend time - FAILED fast pass.

## Leg 2: codex  (10:02, 9 min, ended: exit)
File stats: proved lemmas 11, sorries 1, lines 299 (was 0 / 1 / 10)
# Erdos595 relay leg 2

Approach: isolate obstructions to prospective constructions. Binary sequence vertex labels give countably many bipartite cuts plus the subgraph within label fibers. For the local bound, group edges into components under sharing a triangle. Continuum-bounded triangle codegree gives at most continuum many edges reachable by finite chains from each edge, and hence continuum-bounded support for each block.

Compiled with pinned Lean: `OMA.Erdos595.cover_of_triangleFree_fibers`, `cover_of_binary_embedding`, `cover_of_triangle_partition`, `cover_of_small_support`, `cover_of_small_common_neighbors`, `cover_iSup_nat`, `not_cover_large_codegree_subgraph`, `exists_large_independent_common_neighbors`, and their helpers. Any witness must resist every labeling with continuum many triangle-free vertex classes and contain an edge with an independent common neighborhood larger than the continuum. Keeping only the edges with more than continuum many common neighbors in the original graph preserves the obstruction to a countable edge cover.

Remaining gap: construct a K4-free graph with no countable triangle-free edge cover, equivalently one in which every ℕ-valued edge coloring yields a monochromatic triangle. The necessary conditions above leave the existence step open. Only `OMA.solution` contains a placeholder.

Verification: pinned Lean compiled the full partial file. The four main helper results use only `propext`, `Classical.choice`, and `Quot.sound`. `tools/check.sh` rejected the solution at lint for the remaining `sorry`.

Dead ends: the finite partite construction uses backward homogenization over finitely many template edges. Disjoint unions of finite Folkman graphs are countably coverable. The adjacent upstream finite Folkman variant has a placeholder proof. A single round of adding apices over triangle-free sets can always use a fresh edge color if one is available. The pruning lemma measures codegree before deleting edges, so repeated pruning needs a separate argument at limit stages.
