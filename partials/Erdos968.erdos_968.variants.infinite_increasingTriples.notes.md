# Relay notes for Erdos968.erdos_968.variants.infinite_increasingTriples (prize: )


## Leg 3: opus  (18:04, 2 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 75 (was 0 / 1 / 10)
# Erdos968 infinite_increasingTriples, opus leg 3
Approach: glue in proofs file. u_le_two_log (Chebyshev.pi_ge, n>=18), step_of_gap (gap >= 3 log p => u n < u(n+1)),
OMA.solution from two_large_gaps (ONE sorry: infinitely many n with two consecutive gaps >= 3 log p; FMT18 k=2 / Erdos 1949 / Maier).
Dead ends: Dirichlet-in-AP + CRT gives one-prime window but no size control on q (needs Linnik); averaging/PNT alone cannot force two consecutive above-average gaps.
