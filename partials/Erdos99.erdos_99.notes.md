# Relay notes for Erdos99.erdos_99 (prize: $100)


## Leg 1: opus  (08:00, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos99.erdos_99 notes (opus leg 1)
Approach: audit only. Statement is the faithful open Erdos problem 99 (min-diameter n-point sets with min distance 1
contain a unit equilateral triangle for large n). ℝ² = EuclideanSpace ℝ (Fin 2) (EuclideanGeometry opened), so Euclidean
distance; diam of a finite set is honest; the feasible set {B | card = n, HasMinDist1 B} is nonempty for n>=2 (collinear
unit-spaced points) and minimizers exist by compactness, so the IsMinOn hypothesis is not vacuous. No loophole.
Compiled: nothing new (file is the bare sorry skeleton).
Remaining gap: the whole open conjecture (only Bezdek-Fodor small-n results known).
Dead ends: looking for a misformalization loophole (none: Euclidean metric, nonvacuous minimizer, card = n exact).
Verdict: FAILED fast pass; do not spend more relay legs.

## Leg 2: codex  (08:10, 10 min, ended: exit)
File stats: proved lemmas 8, sorries 1, lines 373 (was 0 / 1 / 10)
# Erdős 99, Codex leg 2

Approach: scale a separated competitor by the reciprocal of its attained minimum distance. For a sufficiently small positive displacement along a velocity field, unit distances with nonnegative linear term stay at least one by the squared-distance expansion. Strict contractions of diametral pairs persist and the remaining inequalities have slack.

Compiled: `exists_dist_eq_diam`, `no_separated_improvement`, `isMinOn_iff_no_separated_improvement`, `no_contracting_velocity`, `exists_diametral_pair_with_contacts`, `exists_wide_contact_component`, `inner_pairGradient`, `zero_mem_convexHull_signedGradients`. The last lemma uses finite convex hull separation and the Riesz representation to certify balance of unit-contact and diametral gradients.

Exact gap: the single obligation at the end of `OMA.solution` asks for a strictly narrower equally sized 1-separated competitor for every sufficiently large triangle-free configuration satisfying the three proved necessary conditions. The component bound comes from translating each unit-contact component toward the origin at the velocity of a representative point.

Dead ends: the prior audit ruled out vacuity. The brief reports triangle-free locally minimizing rings, so a general local deformation or balance argument alone does not supply the global competitor.

## Leg 1: opus  (09:55, 0 min, ended: exit)
File stats: proved lemmas 8, sorries 1, lines 373 (was 8 / 1 / 373)

## Relay leg 1 (opus, round 2, 2026-11-27)
Approach: none new; this is the faithful open Erdos 99 conjecture (no loophole, audited earlier).
File unchanged: keeps codex leg 2 compiled lemmas (exists_dist_eq_diam, no_separated_improvement,
isMinOn_iff_no_separated_improvement, no_contracting_velocity, exists_diametral_pair_with_contacts,
exists_wide_contact_component, inner_pairGradient, zero_mem_convexHull_signedGradients).
Remaining gap: the single sorry in OMA.solution = global competitor for large triangle-free balanced
configurations, i.e. the open core itself (triangle-free locally minimizing rings exist, so local
variational arguments cannot close it).
Dead ends: loophole search (none), local deformation/balance arguments (insufficient).
Verdict: STALLED immediately; do not spend more legs.

## Leg 2: codex  (10:09, 14 min, ended: exit)
File stats: proved lemmas 33, sorries 1, lines 1055 (was 8 / 1 / 373)
# Erdős 99, Codex leg 2, round 2

Approach: keep the prior perturbation and stress reductions. Count vertices in disjoint unit-width annuli along a wide contact component. Bound triangle-free degree by rotating one contact to angle zero and partitioning the other possible directions into four sectors.

Compiled geometry: eventually_diam_gt, exists_unitConnected_in_annulus, exists_contact_component_card_ge, eventually_exists_large_contact_component, card_unitNeighbors_le_five.

Compiled packing comparison: hasSeparatedImprovement_of_short_packing and card_lt_add_of_diametral_cover. Three half-open lattice rhombi plus the origin prove exists_hexagonal_packing and diam_le_two_mul_of_card_le for 3m(m+1)+1 points.

Compiled global bounds: exists_translate_finset_of_volume averages over one fundamental domain. hexFundamentalDomain_volume and mem_hexSpan_iff_exists_latticePoint identify the triangular lattice of covolume √3/2. exists_separated_finset_of_volume, diam_lt_two_mul_of_disk_area, and diam_sq_le_lattice_density give π(D/2)^2 ≤ n√3/2. volume_le_of_retained_subset and volume_replacementRegion_le bound the area available for replacing A \ K by (n − |K|)√3/2 when K has strictly smaller diameter.

Exact remaining gap: the single sorry in OMA.solution asks for a strictly narrower unit-separated competitor of equal cardinality for every sufficiently large triangle-free configuration meeting the proved bounds, contact conditions, and gradient balance. No argument forces a violation of the area bounds or constructs a competitor when the bounds hold.

Dead ends: prior legs ruled out vacuity and a metric mismatch. The locally minimizing triangle-free rings in the brief block a general first-order deformation argument. The lattice upper bounds alone cannot distinguish exact unit triangles.

Verification: direct Lean compiled the complete partial. The main six new results audited with only propext, Classical.choice, and Quot.sound. The required checker rejects the single remaining sorry.
