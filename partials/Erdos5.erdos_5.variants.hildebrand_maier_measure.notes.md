# Relay notes for Erdos5.erdos_5.variants.hildebrand_maier_measure (prize: )


## Leg 2: codex  (16:32, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (18:29, 2 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 115 (was 0 / 1 / 10)
# opus leg 3 hildebrand_maier_measure (2026-11-27)
Approach: own packing glue (greedy left-point selection near sInf, remove x + D) reducing the
target to ONE sorry. File compiles (lake env lean from formal-conjectures checkout, seconds).
Compiled (namespace OMA.HMM): step, packing (n+1 increasing points of A in [0,T] with no
difference in L, if n*(eps+vol(L cap [0,T])) < vol A), of_core (Core -> target, c = 1/(2m)),
OMA.solution := of_core core.
Exact remaining gap: lemma core : Core where
  Core := exists m>0, forall beta : Fin (m+1) -> R, nonneg, StrictMono ->
          exists i<j, beta j - beta i in limitPointSet
(= BFM16 Thm 1.1 with m=8, or Merikoski m=3; needs Maynard sieve; research-level, not in Mathlib).
Dead ends: none new; normalization log n vs log p_n is NOT needed in this form (stated on
limitPointSet directly). Do not split Core by m or parity (monotone in m, fake split).
