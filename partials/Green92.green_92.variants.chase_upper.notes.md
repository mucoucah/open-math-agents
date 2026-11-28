# Relay notes for Green92.green_92.variants.chase_upper (prize: )


## Leg 3: opus  (19:19, 2 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 86 (was 0 / 1 / 10)
# Opus relay leg 3: Green92.green_92.variants.chase_upper

Approach: union-bound glue (same shape as merged R1 reduction, own proof, namespace OMA.G92Upper).
File compiles (lake env lean, about 10 s) with ONE sorry. Backup: .oma/scratch/g92_upper_opus.lean

Compiled: failCount (def), decoder_of_tests (union bound decoder, proved), OMA.solution (glue, proved).
Remaining sorry: pairwise_tests = antisymmetric pairwise tests D at m = ceil(exp(C n^(1/5) log^5 n))
traces, each test failing on at most N/(10*2^n) of the N sample tuples. This is the full content
of Chase 2020 (complex analysis of Littlewood-type polynomials on a small arc) + amplification.

Possible next split (does NOT drop the sorry count): open PR 16315 shape = one-trace separation
(F in [0,1], mean gap >= exp(-C n^(1/5) log^5 n)) + Hoeffding amplification over m traces.
Hoeffding counting form over uniform Fin m -> Finset (Fin n) not yet in this file.

Dead ends / facts:
- Statement faithful (q=1/2, delta=1/10, numTraces = sInf), no loophole.
- NP17/DOS19 exp(C n^(1/3)) bound is too weak (n^(1/3) dominates n^(1/5) log^5 n).
- Chebyshev amplification too weak: needs m >= 10*2^n/a^2, but m is subexponential in n.
