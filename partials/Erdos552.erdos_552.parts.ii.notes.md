# Relay notes for Erdos552.erdos_552.parts.ii (prize: $100)


## Leg 1: opus  (08:00, 1 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos552.erdos_552.parts.ii - opus leg 1 notes
Status: FAILED fast pass (open Erdos $100 problem, faithful, no loophole).
- graphRamsey = sInf {n | forall C on Fin n, G <= C or H <= C compl} (FormalConjecturesForMathlib Ramsey.lean:88); faithful;
  set nonempty for C4 vs K_{1,n} (Parsons), so no sInf-empty=0 loophole. Star = completeBipartiteGraph (Fin 1) (Fin n), correct.
- Merged reduction R1 (Deldor14): H1 Parsons p^2 values, H2 Chen monotone + step<=2 (merged proof by Salofe),
  H3 = counting double jumps vs stationary steps below a prime square = literally the open problem restated.
- Known: R <= n + sqrt n + 1 (Parsons), equality-type values at q^2, q^2+1; lower bound n + sqrt n - 6 n^(11/40).
  Whether R <= n + sqrt n - c infinitely often for every c is OPEN. No Lean beyond the sorry skeleton is worth writing.
Remaining gap: the whole open problem (H3 of R1).
Dead ends: none tried beyond audit; do not spend time on it.

## Leg 2: codex  (08:05, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Codex leg 2

Approach: express the exact target through minimum degrees in four-cycle-free graphs, then use the disjoint second neighborhoods to constrain every obstruction. This is independent of the prime-square jump-count reduction.
Compiled so far: the starting submission contains only its target stub.
Remaining gap: for each fixed positive deficit, exhibit unbounded graph orders at which the required minimum degree is impossible.
Dead ends: the previous leg already ruled out the empty Ramsey set and identified the missing estimate in R1.H3. The pair count by itself yields only a constant-error upper bound on the other side of n + sqrt n.

## Leg 3: fable  (08:09, 4 min, ended: exit)
File stats: proved lemmas 10, sorries 1, lines 275 (was 0 / 1 / 10)
# Fable leg 3 notes - Erdos552.erdos_552.parts.ii

Status: STALLED. The target is the open Erdos 100 dollar question itself; no proof is known in either direction.

Approach: none new. Re-audited the statement (graphRamsey = sInf of a nonempty set, IsContained = non-induced copy,
star = completeBipartiteGraph (Fin 1) (Fin n)): faithful, no loophole. Then consolidated leg 2's scratch file
(.oma/scratch/erdos552_codex.lean, which DOES compile, 8 s) into the proofs file so the open core is isolated.

What compiles now in proofs/Erdos552.erdos_552.parts.ii.lean (direct lean compile, only warning = the one sorry):
namespace OMA.Erdos552Helpers
- star_iff_degree: star K_{1,n} contained in G iff some vertex has degree >= n
- common_neighbor_unique: C4-free => two distinct vertices have at most one common neighbour
- degree_mul_sub_one_le: C4-free, min degree d => deg v * (d-1) <= N-1
- mem_orders_iff, orders_nonempty (2n+2 works), orders_mono
- ramsey_le_iff_no_obstruction: R(C4,S_n) <= N iff no C4-free graph on Fin N with min degree >= N-n
- degree_criterion_iff: DegreeCriterion iff the target statement (both directions proved)
- degree_range: any obstruction with sqrt N >= (K+4)(K+1) has all degrees in [sqrt N - K, sqrt N + K + 3]
OMA.solution := degree_criterion_iff.mp OMA.degree_criterion_core

Exact remaining gap (ONE sorry, OMA.degree_criterion_core):
  forall K B : Nat, exists N > B, there is NO C4-free graph on Fin N with min degree >= Nat.sqrt N - K.
This is equivalent to the target, i.e. it is the open problem, not a technical gap.

Why it is out of reach:
- Counting (degree_mul_sub_one_le) only gives N >= d^2-d+1, i.e. excludes d >= sqrt N + 1/2; the target needs
  to exclude d = sqrt N - K, off by about (2K+1) sqrt N vertices. Polarity graphs ER_q (N = q^2+q+1, min degree q)
  show the count cannot be improved at prime-power orders, so one needs N far from those AND a nonexistence
  theorem for near-polarity-graph structures (as hard as nonexistence of projective planes with a polarity
  for runs of consecutive orders). Nothing like this is known even for K = 1.

Dead ends (do not repeat):
- sInf-of-empty-set loophole: ruled out (orders_nonempty is proved).
- R1 jump-count reduction (merged, Deldor14): H3 is the same open problem.
- Pair counting / second-neighbourhood counting alone: wrong side of n + sqrt n by a constant.
- check.sh will never accept this file while the sorry is there; use .oma/scratch/lean_local.sh <file> to compile.

## Leg 1: opus  (09:54, 0 min, ended: exit)
File stats: proved lemmas 10, sorries 1, lines 275 (was 10 / 1 / 275)
# Erdos552.erdos_552.parts.ii - opus relay leg 1 (latest) notes
Status: STALLED immediately. Target = open Erdos 100 dollar question (R(C4,K_{1,n}) <= n + sqrt n - c infinitely often, for every c). Faithful, no loophole (audited 3+ times).
Approach: none new; kept the file unchanged.
Compiled (unchanged, from fable leg): OMA.Erdos552Helpers.{star_iff_degree, common_neighbor_unique, degree_mul_sub_one_le, mem_orders_iff, orders_nonempty, orders_mono, ramsey_le_iff_no_obstruction, degree_criterion_iff, degree_range}.
Exact remaining gap: ONE sorry OMA.degree_criterion_core:
  forall K B, exists N > B with NO C4-free graph on Fin N of min degree >= Nat.sqrt N - K.
Equivalent to the target, i.e. the open problem itself.
Dead ends: counting (pair count) only excludes min degree >= sqrt N + 1/2; polarity graphs are tight at prime-power orders; R2 reduction leg found NO_REDUCTION. Do not retry.

## Leg 2: codex  (09:59, 5 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 467 (was 10 / 1 / 275)
# Codex relay leg 2

Approach: delete a vertex and some of its neighbors. C4-freeness ensures every survivor loses at most two neighbors. Iterating transfers high-minimum-degree obstructions to nearby smaller orders. This gives equivalent criteria on sets of graph orders with gaps O(sqrt N), on square graph orders, and on square star sizes.

Compiled and axiom-audited: OMA.Erdos552Helpers.DegreeObstruction.shrink_once, DegreeObstruction.shrink, sampled_degree_criterion_iff, square_degree_criterion_iff, square_star_criterion_iff (with private helper square_star_bound_iff). Each uses only propext, Classical.choice, Quot.sound. The incoming lemmas remain intact. CI rejects the single remaining sorry.

Exact gap: in OMA.degree_criterion_core, after applying square_star_criterion_iff.mpr, prove that for every K B : Nat there is s > B with R(C4, S_(s^2)) + K <= s^2 + s. Equivalently, square_degree_criterion_iff asks for s > B with no C4-free graph on s^2 vertices of minimum degree >= s - K.

Dead ends: elementary second-neighborhood counting bounds degree on the other side of sqrt N. R1.H3 is equivalent to the target, and the Ramsey order set is nonempty. Deletion pays bounded degree loss per sqrt N vertices, so it does not bridge unbounded gaps between prime roots at fixed degree loss. Parsons' prime-square exact values do not supply the required square-star deficit.
