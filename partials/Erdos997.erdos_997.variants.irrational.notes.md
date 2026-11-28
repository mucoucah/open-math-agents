# Relay notes for Erdos997.erdos_997.variants.irrational (prize: )


## Leg 3: opus  (18:21, 2 min, ended: exit)
File stats: proved lemmas 6, sorries 1, lines 79 (was 0 / 1 / 10)
# Opus relay leg 3: Erdos997.erdos_997.variants.irrational

Approach: Baire category. W k = multipliers a with a window of k consecutive primes p where
a(p-1) is within 1/16 of an integer; open, and contains every rational t (via runs of primes
that are 1 mod t.den), so dense. Irrational a in (1/8,1/4) in all W k: fract(a p) < 1/2 on a
window of length k+1, contradicting well-distribution with eps=1/4, I=[1/2,1).

File proofs/Erdos997.erdos_997.variants.irrational.lean compiles (lake env lean, seconds)
with ONE sorry. Compiled (namespace OMA.E997): W, W_open, rat_mem_W, W_dense, fract_small,
main, OMA.solution.

Remaining gap (only sorry) shiu_run:
  forall q k, 0<q -> exists m, forall i, m<=i -> i<m+k -> nth Prime i = 1 [MOD q]
= Shiu 2000 (strings of congruent primes, a=1), Maier matrix method. Not in Mathlib.
Same blocker as Erdos427 shiu (see memory erdos427-shiu-dead-ends): STALLED.

Dead ends (paper): using denominators 2^j or a q-dependent avoided interval does not help;
the residues of a p mod q are 1/q-dense, so any route needs a Shiu/Maier-type bias of
consecutive primes in residue classes mod q with eps independent of q.
