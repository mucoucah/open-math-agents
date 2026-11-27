# Relay notes for Erdos30.erdos_30 (prize: $1000)


## Leg 1: opus  (09:15, 1 min, ended: exit)
File stats: proved lemmas 5, sorries 1, lines 78 (was 0 / 1 / 10)
# Erdos30.erdos_30 relay leg 1 (opus)
Faithful open $1000 problem (h(N)=sqrt N+O(N^eps)); no loophole (abs value BigO needs both sides).
File proofs/Erdos30.erdos_30.lean compiles (lake env lean) with ONE sorry:
- compiled: OMA.E30.h_witness, h_le_nat (via upstream lindstrom_weak), h_le_real (h N <= 2 sqrt N + 1),
  large_eps (eps >= 1/2 case), OMA.solution glue (split eps >= 1/2 / eps < 1/2).
- sorry: OMA.E30.small_eps (0<eps<1/2). Lower side needs prime(-power) gaps x^{2eps} near x
  (Hoheisel-type for eps<1/2, subpolynomial for small eps; Bose construction in R1 reduction file);
  upper side needs Lindstrom for eps>=1/4 and an open improvement for eps<1/4.
Dead ends: none worth retrying; problem is open. Do not spend time on small_eps.

## Leg 2: codex  (09:20, 5 min, ended: exit)
File stats: proved lemmas 10, sorries 1, lines 238 (was 5 / 1 / 78)
# Erdos30 relay leg 2 (Codex)

Approach: inject additive-energy collisions into pairs of a mark and a shift or pairs of shifts. Cauchy–Schwarz with shifts of size about N^(3/4) gives h(N) ≤ √N + 8 N^(1/4).
Compiled: h_witness, h_le_nat, h_le_real, large_eps, sidon_energy_le, sidon_shift_bound, h_le_sqrt_add_quarter, upper_error_bound, and small_eps/OMA.solution conditional on unresolved_bounds. The upper-bound lemmas audit to propext, Classical.choice, and Quot.sound.
Exact gap: unresolved_bounds is the sole sorry. For each 0 < ε < 1/2, need eventually √N − h(N) ≤ C N^ε. For 0 < ε < 1/4, also need eventually h(N) − √N ≤ C' N^ε.
Dead ends: the energy estimate balances the diagonal term with the shift-range enlargement at the quarter-power scale. Bose plus fixed-ratio prime intervals gives relative asymptotics without the required power error. R1 gives a sufficient prime-power gap condition for the lower side, and R3 gives an equivalent doubling formulation.
CI verdict: rejected at lint for the single sorry. Direct Lean compilation succeeded, with sorryAx confined to the unresolved bound and its dependents.
