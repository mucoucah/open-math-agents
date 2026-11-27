# Relay notes for Erdos713.erdos_713.parts.i (prize: $500)


## Leg 1: opus  (08:17, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_opus: Erdos713.erdos_713.parts.i (leg 1, opus)
Approach: none possible. Statement is faithful to the open Erdos $500 question
(every bipartite G with >=2 edges has ex(n;G) ~ c n^alpha, alpha in [1,2)).
Contains open cases: order of ex(n;C8), ex(n;K_{4,4}), asymptotic constant for C6/C8 etc.
No loophole: Mathlib extremalNumber is genuine, q and G arbitrary, 2 <= edges excludes only
degenerate cases. Forests (alpha=1) and C4/K_{2,t}/K_{3,3} are known but cannot cover all G.
Compiled: nothing new (file is the bare sorry skeleton).
Remaining gap: the whole open conjecture.
Dead ends: no attempt worth recording; existing reductions R1 (forest / dense core split) and
R1.H1.R1, R1.H2.R1 already merged upstream; their leaves are research level.
Verdict: FAILED fast pass.

## Leg 2: codex  (08:29, 12 min, ended: exit)
File stats: proved lemmas 19, sorries 1, lines 599 (was 0 / 1 / 10)
# Erdos713.erdos_713.parts.i, leg 2

Approach: double-count injective neighbor tuples and apply Jensen to bound
ex(n;G) by q n^(2-1/q). A star or consecutive matching gives ex(n;G) ≥ floor(n/2).
A finite positive normalized limit therefore forces its exponent into
[1, 2 - 1/q]. Remove isolated vertices by extending a copy of the support with
unused vertices. Disjoint unions of free hosts and Fekete give the connected
density dichotomy. A spanning tree embeds greedily into a host of high minimum
degree. Deleting a low-degree vertex gives the linear bound for forests.

Compiled: balanced_degree_count, balanced_edge_bound, bipartite_extremal_upper,
extremal_linear_lower, exponent_ge_one, exponent_le_bipartite_bound,
connected_extremal_superadditive, connected_density_alternative,
tree_copies_into_high_degree, forest_extremal_upper, contained_iff_contained_support,
extremal_eq_on_support, remove_isolated_vertices, and their helpers.

Remaining gap: the only sorry is hlimit in OMA.solution. For the isolate-free
bipartite H with at least two edges and no finite positive limit of ex(n;H)/n,
construct α and c > 0 with ex(n;H)/n^α → c. When H is connected, it is cyclic
and ex(n;H)/n → ∞. The disconnected case is still present in the gap.

Dead ends: CI permits only Mathlib imports after the required import, so the
parent file cannot use the merged reductions directly. Quantitative power
bounds alone do not give a limiting exponent or coefficient.

Verification: direct Lean elaborates the final file. The axiom audit on the
completed top-level helpers found only propext, Classical.choice, and Quot.sound.
The exact CI checker rejected the remaining sorry at lint.

## Leg 1: opus  (09:27, 0 min, ended: exit)
File stats: proved lemmas 19, sorries 1, lines 599 (was 19 / 1 / 599)
# notes_opus: Erdos713.erdos_713.parts.i (relay leg 1 this round, opus)
Approach: none new. Statement is the faithful open Erdos $500 question (ex(n;G) ~ c n^alpha
for every bipartite G with >= 2 edges). Includes C8, K_{4,4}, whose orders of magnitude are
unknown, so no proof route exists. Mathlib extremalNumber is genuine; no loophole.
Compiled: unchanged. The file keeps codex leg-2 lemmas (balanced_edge_bound, bipartite_extremal_upper,
extremal_linear_lower, exponent_ge_one, exponent_le_bipartite_bound, connected_density_alternative,
forest_extremal_upper, remove_isolated_vertices, ...). Single sorry hlimit in OMA.solution.
Remaining gap: hlimit = power-law limit for isolate-free bipartite H with no finite positive
linear limit (connected cyclic case plus disconnected case). This is the open problem itself.
Dead ends: see memory; R2 (connected cyclic / disconnected split) already ACCEPTED in wt16.
Verdict: STALLED/FAILED fast pass; stopped early so the file was not changed.

## Leg 2: codex  (09:33, 5 min, ended: stalled)
File stats: proved lemmas 19, sorries 1, lines 599 (was 19 / 1 / 599)
# Erdos713.erdos_713.parts.i, codex relay

Approach: preserve the previous bounds and isolate removal. Investigating an extremal comparison with the connected components by deleting the vertices of a found component copy.
Compiled so far: inherited 19 lemmas, including bipartite_extremal_upper, exponent_ge_one, connected_density_alternative, forest_extremal_upper, and remove_isolated_vertices.
Gap: a finite positive power-law limit for the isolate-free bipartite graph when the linear limit case does not apply.
Dead ends inherited: merged reduction imports are disallowed by CI. Power bounds alone do not yield an exponent or a coefficient.

## Leg 3: fable  (09:35, 2 min, ended: exit)
File stats: proved lemmas 19, sorries 1, lines 599 (was 19 / 1 / 599)
# notes_fable: Erdos713.erdos_713.parts.i (relay leg 3, fable, 09:34-09:38)

Approach: none new; stopped early. The proof file was NOT changed.

Verified this leg: direct compile of proofs/Erdos713.erdos_713.parts.i.lean
(cd repo/.oma/formal-conjectures && lake env lean <abs path>) takes 7 s and gives
exactly one message: line 552, declaration uses sorry (OMA.solution). No errors.
check.sh was not run: it rejects at lint on the sorry without compiling.

Compiled (inherited from codex leg 2, all intact): contained_in_balanced_bipartite,
balanced_degree_count, balanced_edge_bound, bipartite_extremal_upper,
extremal_linear_lower, exponent_ge_one, exponent_le_bipartite_bound,
connected_extremal_superadditive, connected_density_alternative,
tree_copies_into_high_degree, forest_extremal_upper, contained_iff_contained_support,
extremal_eq_on_support, remove_isolated_vertices, plus helpers. OMA.solution is complete
except for one sorry.

Exact remaining gap: the sorry closing hlimit inside OMA.solution. Context there:
H : SimpleGraph (Fin k) bipartite, no isolated vertex, at least 2 edges,
linear : no c > 0 with ex(n;H)/n -> c, hdiv : H connected -> ex(n;H)/n -> infinity,
hcyclic : H connected -> H not acyclic.
Goal: exists alpha c, 0 < c and ex(n;H)/n^alpha -> c.
It splits into two parts, neither closable:
 (a) H contains a cycle: this is the open conjecture itself. Already for H = C6 the
     limit of ex(n;C6)/n^(4/3) is not known to exist; for C8 and K_{4,4} even the
     exponent is unknown. No amount of Lean work closes this.
 (b) H a disconnected forest: need lim ex(n;H)/n to exist. Fekete does not apply
     (a disjoint union of H-free hosts can contain H, one component in each host).
     Not attempted; even if proved, (a) remains.

Statement check (own reading of 713.lean): faithful. q and G are arbitrary, Mathlib
extremalNumber is the genuine sup over H-free graphs on Fin n, IsBipartite is
Colorable 2, the 2-edge condition only removes degenerate cases. No loophole.

Dead ends (do not repeat): importing the merged reductions (CI allows only Mathlib
imports after the required one); power bounds n/2 <= ex <= q n^(2-1/q) alone give no
limiting exponent or constant; Fekete for disconnected H.

Advice for the next leg: nothing here can reach ACCEPTED. The reduction R2
(connected cyclic / disconnected split) is already accepted in wt16, so a further
reduction leg would only restate the open core.

Verdict: STALLED. Blocker: hlimit = open Erdos-Simonovits power-law conjecture.

## Leg 1: opus  (10:21, 0 min, ended: exit)
File stats: proved lemmas 19, sorries 1, lines 599 (was 19 / 1 / 599)
# notes_opus: Erdos713.erdos_713.parts.i (relay leg 1, opus, this round)
Approach: none new; stopped at once. Proof file NOT changed.
Statement: faithful open Erdos $500 question (ex(n;G) ~ c n^alpha for every bipartite G, >=2 edges).
Contains C6 (constant unknown), C8 and K_{4,4} (exponent unknown). Mathlib extremalNumber genuine; no loophole.
Compiled (inherited codex lemmas, intact): balanced_edge_bound, bipartite_extremal_upper,
extremal_linear_lower, exponent_ge_one, exponent_le_bipartite_bound, connected_density_alternative,
tree_copies_into_high_degree, forest_extremal_upper, extremal_eq_on_support, remove_isolated_vertices, ...
Exact remaining gap: one sorry hlimit in OMA.solution = power-law limit for isolate-free bipartite H
with no positive linear limit: (a) H has a cycle = the open conjecture; (b) disconnected forest linear limit.
Dead ends: importing merged reductions (CI disallows); power bounds give no limit; Fekete for disconnected H.
Verdict: STALLED. Blocker: open Erdos-Simonovits conjecture.

## Leg 2: codex  (10:26, 5 min, ended: stalled)
File stats: proved lemmas 19, sorries 1, lines 599 (was 19 / 1 / 599)
# Erdos713.erdos_713.parts.i, codex relay

Approach: for the linear-density branch, replicate a nearly extremal host with
a shared set S of high-degree vertices. For each possible assignment of some
vertices of the forbidden graph to S, and each subset of remaining vertices,
consider the images of admissible partial copies outside S. A small family
which meets every image can be isolated, while other patterns admit copies
avoiding any set of at most q occupied vertices. This should let one relocate
each layer of a hypothetical forbidden copy back into the original host.

Compiled: inherited lemmas only so far. The exact gap is the positive power-law
limit in hlimit for the isolate-free bipartite H when its linear limit is absent.
Dead ends: power bounds alone, direct Fekete for disconnected H, reduction imports.

## Leg 1: gemini  (10:39, 10 min, ended: no_progress_10m)
File stats: proved lemmas 19, sorries 1, lines 599 (was 19 / 1 / 599)
# notes_gemini: Erdos713.erdos_713.parts.i (relay leg 1, gemini)

Approach:
Target Erdos713.erdos_713.parts.i is faithfully the open $500 Erdos-Simonovits conjecture,
so a sorry-free ACCEPTED proof is not possible. However, the current partial file
(19 lemmas, 599 lines) can be substantially strengthened by proving three concrete,
elementary reductions that narrow the remaining sorry in OMA.solution:
1. High-girth max-degree extremal lower bound for ANY cyclic graph H on Fin k:
   take a maximal graph on Fin n with no cycle of length <= k and max degree <= D;
   any two low-degree vertices have distance < k, so |low| <= (D+1)^(k-1), giving
   D * (n - (D+1)^(k-1)) <= 2 * ex(n; H), hence ex(n; H)/n -> infinity and
   alpha >= 1 + 1/(k-1) > 1.
2. Connected-component deletion sandwich bound for any isolate-free H on Fin k:
   max_C ex(n; H_C) <= ex(n; H) <= max_C ex(n; H_C) + k * n.
   Combined with (1), this reduces ALL disconnected cyclic bipartite graphs to the
   connected cyclic bipartite case.
3. Exact linear limit ex(n; H)/n -> m - 1 for any m-edge matching (m >= 2).

Compiled so far: baseline 19 lemmas verified cleanly via lake env lean.
In progress: Module 1 (high-girth lower bound).
Exact remaining gap: open Erdos-Simonovits conjecture (connected cyclic bipartite graphs)
plus disconnected forests with max degree >= 2.
Dead ends: reduction imports disallowed by CI; power bounds alone give no limit.

## Leg 2: codex  (10:56, 17 min, ended: exit)
File stats: proved lemmas 58, sorries 1, lines 1792 (was 19 / 1 / 599)
# Erdos713.erdos_713.parts.i, Codex relay

Approach: for cyclic graphs, greedily embed connected components with an
additive O(n) edge loss, take the maximum component asymptotic, and prune
leaves with another O(n) loss. A maximal bounded-degree graph with no short
cycles gives divergent cyclic extremal density, forcing any finite positive
power-law limit to have exponent > 1.

For forests, grow a bounded boundary by adding disjoint hitting sets for
rooted patterns that cannot be replicated. Some hitting set has small
total degree. Erase it and glue many copies along the corresponding
boundary. A forbidden copy could be relocated back into the original
host. This rules out density upcrossings and proves the positive linear
limit, including for disconnected forests.

Compiled: extremal_le_component_bound, cyclic_extremal_degree_bound,
cyclic_density_diverges, limit_of_component_limits,
exists_boundary_regularizer, gluedGraph_free, gluedGraph_edge_lower,
exists_boundary_with_small_loss, linear_extremal_density_exists,
extremal_limit_of_leaf_pruned, connected_cyclic_limit_from_min_degree,
and cyclic_exponent_gt_one. All 19 inherited lemmas are retained.

Exact gap: minDegreeCore inside OMA.solution is the only sorry. For a
finite connected bipartite J of minimum degree at least two, prove that
there are reals a, c with c > 0 and ex(n;J)/n^a tending to c. This still
includes K_{4,4}. The forest and reduction arguments elaborate. The new
main helpers depend only on propext, Classical.choice, and Quot.sound.
Exact CI verdict: rejected at lint for the single remaining sorry.

Dead ends: importing reductions violates CI, power bounds do not give
an asymptotic equivalent, and ordinary disjoint union fails to preserve
freedom for disconnected forbidden graphs.

## Leg 1: gemini  (11:07, 10 min, ended: no_progress_10m)
File stats: proved lemmas 58, sorries 1, lines 1792 (was 58 / 1 / 1792)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (11:21, 14 min, ended: exit)
File stats: proved lemmas 87, sorries 1, lines 2384 (was 58 / 1 / 1792)
# Erdos713.erdos_713.parts.i, Codex relay

Approach: retained the earlier forest, component, and leaf reductions. Count
ordered neighbor tuples for a rectangular complete bipartite forbidden graph.
For C4, the affine polarity graph over ZMod p gives the matching leading
coefficient at n = p². For a bouquet of k four-cycles meeting at one vertex,
take bounded hitting sets for rooted squares and for neighbor pairs with high
codegree. Hall's theorem completes disjoint high-codegree pairs to squares.
Deleting the marked edges destroys every C4 with O_k(n) edge loss.

Compiled: all 58 inherited lemmas and 29 new ones, including
rectangular_degree_count, rectangular_edge_bound, rectangular_extremal_bound,
fourCycle_limit_prime_squares, fourCycle_limit_of_prime_approximation,
two_side_exponent_fixed, fourCycle_limit_fixed, exists_square_cover,
exists_rich_pair_cover, squareBouquet_extremal_upper, and
squareBouquet_limit_of_fourCycle.

Exact gap: reducedCore is the only sorry. It asks for the full C4 limit
ex(n,C4)/n^(3/2) → 1/2, and for a finite positive power-law limit for every
other finite connected cyclic bipartite graph of minimum degree at least two
outside the four-cycle bouquet family. The latter still includes K_{4,4}.
The C4 interpolation lemma needs eventual prime-square approximants from
below with relative size tending to one.

Dead ends: the sharp bound and prime-square subsequence alone do not give
the full C4 limit. The Mathlib prime interval results located here only give
fixed-ratio bounds. Reduction imports are disallowed by CI, and ordinary
disjoint union can introduce a disconnected forbidden graph.

Verification: direct Lean elaborated the file with only the expected sorry
warning. The six principal new results audited used propext, Classical.choice,
and Quot.sound. Exact CI verdict: rejected at lint for the remaining sorry.
