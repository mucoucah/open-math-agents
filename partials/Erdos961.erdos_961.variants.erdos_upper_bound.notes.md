# Relay notes for Erdos961.erdos_961.variants.erdos_upper_bound (prize: )


## Leg 1: gemini  (16:23, 3 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (17:17, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:38, 2 min, ended: exit)
File stats: proved lemmas 5, sorries 1, lines 76 (was 0 / 1 / 10)
# Erdos961 erdos_upper_bound — opus leg 1 notes
COMPILED (direct lake env lean, only warning = sorry in core_choose): f_le_of_prop, prop_of_choose
(Erdos961Prop k n from: every m>=k+1 has prime p>k dividing C(m+n-1,n)), choose_le_pow_pi
(C(N,n) <= N^primeCounting k if all prime factors <= k), core, OMA.solution.
REMAINING GAP (one sorry): OMA961.core_choose = eventually exists n < 3k/log k with that binomial property.
Approach: f k <= n via Nat.find_min' (lemma OMA961.f_le_of_prop, COMPILES). OMA.solution reduced
(COMPILES) to OMA961.core : eventually in k, exists n with (n:R) < 3k/log k and Erdos961Prop k n  (ONE sorry).
Math for core (Erdos 1955): suppose m..m+n-1 all k-smooth, N=m+n-1. C(N,n) has all prime factors <= k,
each prime power <= N (Nat.pow_factorization_choose_le), so (N/n)^n <= C(N,n) <= N^pi(k).
With pi(k) <= (1+eps)k/log k (needs PNT, see memory pnt-port) and n ~ (3-eps)k/log k this kills N > k^(3/2).
Middle region k < N <= k^(3/2): NOT covered by binomial bound (gives only k/loglog k); crude Sylvester
(remove max-power terms, product <= (n-1)!) also fails (n log n ~ 3k). Real Erdos argument unknown here = blocker.
Dead ends: crude n! argument; C(N,n) <= N^pi(sqrt N) 4^k for middle region (gives n ~ k/loglog k only).
Compile direct: cd repo/.oma/formal-conjectures; lake env lean /tmp/file.lean (check.sh refuses sorry files).

## Leg 1: gemini  (00:29, 27 min, ended: no_sorry_drop)
File stats: proved lemmas 5, sorries 1, lines 76 (was 5 / 1 / 76)
(the model wrote no notes; see partial_gemini.lean)
