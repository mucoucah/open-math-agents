# Relay notes for Erdos5.erdos_5.variants.merikoski (prize: )


## Leg 3: opus  (18:05, 2 min, ended: exit)
File stats: proved lemmas 6, sorries 1, lines 167 (was 0 / 1 / 10)
# notes_opus (relay leg 3, wt16): Erdos5.erdos_5.variants.merikoski

Approach: target = full Merikoski 2020 Thm 1 (Maynard-sieve four-shift theorem), faithful, no loophole
(beta monotone, differences >= 0; constant beta needs 0 in S = GPY; nothing trivial).
Wrote glue: proofs file (compiles via lake env lean, ONE sorry) namespace OMA.Merikoski:
- theta_half, pi_ge, nth_prime_le, log_ratio (log p_n / log n -> 1), all proved
- transfer: gap/log p_{n k} -> d along StrictMono n  ==> d in limitPointSet, proved
- merikoski_prime_norm: Merikoski Thm 1 in prime normalisation (= merikoski_measure R1.H1 form) -- SORRY
- OMA.solution proved from merikoski_prime_norm + transfer.
Exact remaining gap: merikoski_prime_norm (the sieve theorem; needs Maynard sieve + BV, not in Mathlib).
Dead ends: none new; no loophole in statement.
RESULT: STALLED
