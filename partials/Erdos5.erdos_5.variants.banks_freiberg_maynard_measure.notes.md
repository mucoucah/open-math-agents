# Relay notes for Erdos5.erdos_5.variants.banks_freiberg_maynard_measure (prize: )


## Leg 3: opus  (17:46, 2 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 128 (was 0 / 1 / 10)
# Opus relay leg 3: Erdos5.erdos_5.variants.banks_freiberg_maynard_measure
Approach: reduce the measure statement (1-eps)T/8 to the BFM nine-point theorem by greedy packing:
if vol(S cap [0,T]) < T/8, pick 9 increasing points in [0,T] with pairwise differences outside S.
Compiled (direct lake env lean, only one sorry): OMA.BFMMeasure.greedy_step, greedy_points, main, OMA.solution.
Sole remaining sorry: OMA.BFMMeasure.nine_point (beta : Fin 9 -> R, nonneg, StrictMono => some
beta j - beta i in limitPointSet). This is BFM16 Thm 1.1 (Maynard sieve + Erdos-Rankin), not in Mathlib.
Index normalization (normalizedGap uses log n) is built into nine_point, so no H2 scaling lemma is needed.
Dead ends: eps >= 1 trivial only; no loophole; Maynard sieve absent from Mathlib.
