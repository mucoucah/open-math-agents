# Relay notes for Erdos604.erdos_604.variants.sqrt_log (prize: $500)


## Leg 1: grok  (04:25, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (04:28, 3 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos604.erdos_604.variants.sqrt_log, relay leg 2 (opus)
Approach: none feasible. The target is Erdos's open pinned-distance conjecture
(some point has >> n/sqrt(log n) distinct distances). It is faithful: Euclidean R^2,
pinnedDistinctDistances is an sInf over n-point sets, IsBigO at atTop. No loophole.
The best known result is OAI26 / Katz-Tardos n^{1-o(1)}-type, which is weaker than n/sqrt log n.
It is implied by variants.average (also open; see wt18 notes).
Compiled: nothing new. The file is still the 1-sorry skeleton.
Remaining gap: the whole conjecture.
Dead ends: none tried. Reduction R1 is already merged upstream (light fibers); R1.H1 is in open PR 3827.
Recommendation: report FAILED/STALLED at once.

## Leg 4: fable  (04:56, 27 min, ended: max25)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_fable.lean)

## Leg 1: gemini  (14:23, 3 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos604.erdos_604.variants.sqrt_log — Gemini leg 1 notes

## Verification of formal statement
Checked `FormalConjectures/ErdosProblems/604.lean` and `reductions/Erdos604.erdos_604.variants.sqrt_log.R1.lean`:
- Target: `(fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt) =O[atTop] (fun n => (Erdos604.pinnedDistinctDistances n : ℝ))`.
- `ℝ²` is `EuclideanSpace ℝ (Fin 2)` with standard Euclidean `dist`.
- `distinctDistancesFrom A x` is `#((A.erase x).image (fun y => dist y x))`.
- `pinnedDistinctDistances n = sInf {m : ℕ | ∃ A : Finset ℝ², #A = n ∧ A.sup (distinctDistancesFrom A) = m}`. Since `ℝ²` is infinite, the set is nonempty for all `n` and `sInf` is the true minimum.
- `atTop` avoids any `n = 0, 1` edge cases; there is no `answer(sorry)` and no formalization loophole.

## Mathematical status / blocker
- The statement is faithful to Paul Erdos's open sharp pinned distinct distances conjecture ($\max_{x \in A} d_A(x) \gg n / \sqrt{\log n}$ for every $n$-point $A \subset \mathbb{R}^2$).
- Proving this immediately implies Erdos Problem 89 in its sharp $\Omega(n / \sqrt{\log n})$ form for unpinned distinct distances (beating Guth-Katz 2015's $\Omega(n / \log n)$).
- The Elekes-Sharir / Guth-Katz second-moment ($Q(A) = O(n^3 \log n)$) framework is fundamentally capped at $\Omega(n / \log n)$ because the $\sqrt{n} 	imes \sqrt{n}$ integer grid itself has $Q(A) = \Theta(n^3 \log n)$.
- Best known pinned bound (`erdos_604`, [OAI26]) is $n^{1-o(1)}$, strictly weaker than $\Omega(n / \sqrt{\log n})$.
- Upstream reduction `R1` reduces `sqrt_log` to `H1` (algebraic integer specialization, PR #3827) and `H2` (average bound $\gg n^2 / \sqrt{\log n}$ on heavy-fiber algebraic integer configurations), which still contains the full open conjecture.

## Compiled lemmas
None added (`proofs/Erdos604.erdos_604.variants.sqrt_log.lean` remains the 1-sorry skeleton).

## Remaining gap
The entire open conjecture: proving $\max_{x \in A} d_A(x) \ge c n / \sqrt{\log n}$ for all large $n$-point sets $A \subset \mathbb{R}^2$.

## Dead ends
- No formalization loophole exists.
- Second-moment / Cauchy-Schwarz distance energy bounds cannot pass $\Omega(n / \log n)$.

## Leg 2: codex  (14:34, 8 min, ended: exit)
File stats: proved lemmas 14, sorries 1, lines 381 (was 0 / 1 / 10)
# Codex relay leg 2 — Erdos604 sqrt_log

Approach: Each distance fiber from a pin meets a line or a circle centered elsewhere in at most two points. A mixed cover has capacity 2(k+d) per fiber if it uses d lines and at most k circle radial intervals overlap at any observed radius. Combine with the light-fiber branch of R1, then pass to the attained minimum. One concrete special case uses levels at x separated by more than 2 dist(x,y) to get at least half their covered mass in distinct distances at y.

Compiled and axiom-audited: card_distance_image, card_le_two_of_two_distances, mem_circlesAtDistance, card_le_of_circle_cover_overlap, card_le_of_circle_cover, card_le_of_separated_radii, card_le_of_two_pins, card_le_two_on_line_at_distance, card_le_of_line_cover, card_le_of_mixed_cover, card_lightTargets_le, sharp_bound_of_not_sparse, minimum_attained, sharp_of_sparse_configurations. All use only allowed axioms.

Exact gap: At L = sqrt(log n), prove some uniform c > 0 such that every sufficiently large n-point SparseConfiguration has maximum pinned count at least c n/L. At every pin at most half the targets lie in fibers of size ≤ L. Every subset B away from a pin that admits a mixed cover as above has B.card * L ≤ (k+d) n. OMA.solution applies the compiled reduction and has one sorry for this gap. CI rejects that sorry.

Dead ends: Bypassed the previously recorded second-moment limit. The two-pin product bound has square-root scale. A circular-arc crossing approach with a uniform endpoint multiplicity parameter would need control of highly populated perpendicular bisectors or a stronger bound on repeated arcs. The mixed-cover estimates do not provide that logarithmic multiplicity control.
