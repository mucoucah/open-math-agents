# Relay notes for Erdos968.erdos_968.variants.infinite_decreasingTriples (prize: )


## Leg 3: opus  (18:04, 4 min, ended: exit)
File stats: proved lemmas 5, sorries 1, lines 126 (was 0 / 1 / 10)
# notes_opus Erdos968 infinite_decreasingTriples (leg 3)
Approach: glue in the proof file (namespace OMA968D). It compiles with ONE sorry:
- maynard_three : exists B, forall X, exists i > X, p(i+2) <= p(i)+B  (Maynard 2015 / GPY-strength bounded gaps for 3 primes; not in Mathlib; infeasible)
Compiled with no sorry: prime_recip_unbounded (from not_summable_one_div_on_primes), totient_small (phi(primorial K) <= delta*primorial K),
nth_prime_superlinear (B(n+1) < p_n eventually, via Nat.primeCounting'_add_le), step, OMA.solution glue.
Test with: cd repo/.oma/formal-conjectures; lake env lean <abs path>  (check.sh lint rejects any sorry).
Remaining gap: exactly maynard_three. Dead ends: no elementary route to two consecutive below-average gaps
(u_n > u_{n+1} iff (n+1)g_n < p_n); the statement is faithful (u n = p_n/(n+1)) and has no loophole.
