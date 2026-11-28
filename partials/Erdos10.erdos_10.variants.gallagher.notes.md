# Relay notes for Erdos10.erdos_10.variants.gallagher (prize: )


## Leg 3: opus  (17:56, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 22 (was 0 / 1 / 10)
# notes_opus: Erdos10.erdos_10.variants.gallagher (leg 3)
Approach: target is full Gallagher 1975 (faithful; lowerDensity = liminf of partialDensity on N, no loophole).
Compiled (lake env lean, one sorry):
- OMA.gallagher_large_eps (eps >= 1, via Set.lowerDensity_nonneg) PROVED
- OMA.solution glue: case split le_or_gt 1 eps PROVED
Remaining gap: OMA.gallagher_small_eps (0 < eps < 1) = the whole Ga75 theorem (large-sieve /
Gallagher prime density in short shifted sets); not in Mathlib; infeasible in a leg.
Dead ends: no trivial loophole (sumPrimeAndTwoPows k is genuine; primes alone have density 0;
odd-number density 1/2 would already need a Romanoff-type theorem).
Note: le_or_lt is not a known name in this Mathlib; use le_or_gt.
