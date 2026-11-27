# Relay notes for Erdos552.erdos_552.parts.i (prize: $100)


## Leg 1: opus  (07:59, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 2, lines 16 (was 0 / 2 / 16)
# Erdos552.erdos_552.parts.i - notes (opus leg 1)
Approach: none viable. Target asks for an explicit closed formula answer(n) = R(C4, K_{1,n}) for ALL n.
This is the open BEFRS89 problem: exact values known only for special n (q^2, q^2+1, q^2-q+1 type
via polarity graphs, Parsons / Chen / Zhang-Broersma-Chen), general n unknown (even n + sqrt n - c
question, parts.ii, is open). Statement is faithful (graphRamsey of cycleGraph 4 vs K_{1,n}).
Loophole check: answer must be explicit and is checked by a person; a brute-force computable
definition of the Ramsey number would be the quantity itself -> rejected. No loophole.
Compiled: nothing new (file unchanged, still sorry skeleton).
Dead ends: whole problem is open research. FAILED fast pass; next legs should stop at once.

## Leg 2: codex  (08:05, 5 min, ended: exit)
File stats: proved lemmas 9, sorries 2, lines 212 (was 0 / 2 / 16)
# Erdos552.erdos_552.parts.i, Codex leg 2

Approach: for fixed v in a C4-free graph, the sets N(w) minus {v}, w in N(v), are disjoint. A graph on m vertices avoids the complement n-leaf star iff every red degree is at least m-n. Restriction via comap proves monotonicity in m.
Compiled in OMA.CycleStar: cycle_adj_cases, cycle_of_walks, copy_star_of_degree, degree_mul_pred_le, exists_degree_of_copy_star, not_copy_star_compl_iff, cycle_or_star_at_bound, ramsey_le_add_sqrt_add_two, ramsey_le_iff_cycle_or_star, lt_ramsey_iff_exists_min_degree.
Gap: give an explicit all-n candidate r(n). By lt_ramsey_iff_exists_min_degree, for positive r(n) one needs a C4-free graph of order r(n)-1 and minimum degree at least r(n)-1-n, and an obstruction to one of order r(n) and minimum degree at least r(n)-n. The general upper bound is n + Nat.sqrt n + 2. Both original placeholders remain.
Dead end from leg 1: finite search for the first Ramsey order restates the quantity and does not satisfy human review. The related part ii work addresses jump bounds and prime-square anchors.
Verification: standalone Lean compiled the updated file. Axiom reports for degree_mul_pred_le, ramsey_le_add_sqrt_add_two, and lt_ramsey_iff_exists_min_degree contain only propext, Classical.choice, and Quot.sound. The required checker rejected the submission at lint for the two sorry placeholders.

## Leg 1: opus  (10:04, 0 min, ended: exit)
File stats: proved lemmas 9, sorries 2, lines 212 (was 9 / 2 / 212)
# Erdos552.erdos_552.parts.i - notes (opus, relay leg 1 of this round)
Approach: none viable. Target needs an explicit closed formula answer(n) = R(C4, K_{1,n}) for ALL n,
which is the open BEFRS89 problem (exact values known only for special n via polarity graphs; even
the parts.ii question n + sqrt n - c infinitely often is open). Statement faithful, no loophole
(a brute-force definition restates the quantity and fails human review).
Compiled (kept unchanged from codex leg): OMA.CycleStar lemmas incl. ramsey_le_add_sqrt_add_two,
lt_ramsey_iff_exists_min_degree, ramsey_le_iff_cycle_or_star.
Remaining gap: OMA.answer (explicit formula) and OMA.solution - both open research.
Dead ends: whole problem is open. File left unchanged. Next legs should stop at once.

## Leg 2: codex  (10:10, 5 min, ended: exit)
File stats: proved lemmas 22, sorries 2, lines 458 (was 9 / 2 / 212)
# Erdos552.erdos_552.parts.i, Codex relay

Approach: keep the starting degree in the two-step-walk count to force regularity when the order m is just above d(d-1)+1. For odd degree, handshaking excludes odd m. At m=d(d-1)+2, the graph of pairs with no common neighbor is a perfect matching, and its matrix B=(d-1)I+J-A² commutes with the original adjacency matrix A. Odd degree forces every matched pair to be adjacent in the original graph, by handshaking in each vertex's neighborhood. The matching involution is an automorphism, so any edge outside the matching gives a C4.
Compiled: vertex_degree_mul_pred_le, regular_of_small_order, ramsey_le_of_odd_order_and_degree, ramsey_le_add_of_even_excess, degree_missingCommonGraph, missingCommonGraph_commute, adjacent_to_unique_missing, odd_degree_le_one_of_excess_one, ramsey_le_add_of_excess_one, plus all prior lemmas. The upper bound improves by one for n=(k-1)^2+t, odd k, and t=1 or positive even t ≤ k-2.
Gap: an explicit all-n candidate r(n) and matching existence and nonexistence theorems at orders r(n)-1 and r(n) with the corresponding minimum degrees. OMA.answer and OMA.solution retain their two original holes.
Dead end: defining the answer by exhaustive search merely restates the requested quantity and fails human review. The regularity and matching arguments address special orders only.
Verification: standalone Lean succeeded. Both sharpened bounds and the previous universal bound and minimum-degree equivalence use only propext, Classical.choice, Quot.sound. The required checker rejected at lint solely for the two original sorry placeholders.
