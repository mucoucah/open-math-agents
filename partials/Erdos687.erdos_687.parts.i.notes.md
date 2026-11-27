# Relay notes for Erdos687.erdos_687.parts.i (prize: $1000)


## Leg 1: opus  (08:23, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 2, lines 16 (was 0 / 2 / 16)
# Erdos687.erdos_687.parts.i (opus leg 1)
Target: (fun x => (Y x : R)) =Theta[atTop] answer, with answer an explicit function.
Y x = sSup of y with [1,y] covered by one residue class mod each prime p <= x (Green46.IsCoveredByResidues).
Set is bounded by primorial x (lt_primorial_of_isCoveredByResidues), so Y is a genuine value. Faithful, no loophole.
Getting Y up to constant factors is the open $1000 Erdos problem 687. Known bounds are
x log x logloglog x / loglog x << Y(x) (Ford-Green-Konyagin-Maynard-Tao) and Y(x) << x^2 (Iwaniec), a polynomial-size gap.
Any explicit answer would settle an open problem. Answer := Y is forbidden (built from Erdos687).
Nothing compiled; file left as the template (one sorry). Verdict: FAILED fast pass.

## Leg 2: codex  (08:30, 7 min, ended: exit)
File stats: proved lemmas 16, sorries 2, lines 479 (was 0 / 2 / 16)
# Codex leg

Approach: Westzynthius lower bound. Use zero residues on intermediate primes, greedy averaging on small primes, and reserve the largest primes for individual survivors. Every intermediate survivor is either a divisor of a fixed primorial times a square, or a multiple of a prime above the cutoff. Chebyshev's bounds control the reserve and the large prime multiples.

Compiled with Lean:
- Y_isGreatest, covered_iff_le_Y, predecessor_le_Y, cover_with_reserve
- sieve_one_modulus, sieve_small_primes, smooth_eq_divisor_mul_square, count_medium_survivors, cover_of_sieve_bound
- small_prime_product, primeCounting_eventually_upper, primeCounting_eventually_lower, eventually_smooth_bound
- eventually_mul_le_Y_mul, Y_monotone, eventually_mul_le_Y, tendsto_Y_div_atTop

Exact gap: part i requires an explicit scale f with both Y = O(f) and f = O(Y). The new proof gives c*x ≤ Y(x) eventually for each fixed c. It leaves the two template holes in the answer and Θ proof.

Dead ends: using Y itself as the answer is circular. The known large-gap lower bound and the quadratic Jacobsthal upper bound recorded in the brief give different scales. The finite greedy sieve estimate above gives a lower bound only.

Verification: direct Lean accepted the file with only the two template warnings. The axiom audit for eventually_mul_le_Y and tendsto_Y_div_atTop reported only propext, Classical.choice, and Quot.sound. The requested checker returned rejected with lint reason forbidden: 'sorry' on the two unfinished template holes. The first import and the OMA.solution statement were preserved.

## Leg 1: opus  (09:23, 0 min, ended: exit)
File stats: proved lemmas 16, sorries 2, lines 479 (was 16 / 2 / 479)
# Erdos687.erdos_687.parts.i (opus relay leg 1, wt17)
Approach: none new. Target asks for an explicit answer f with Y =Theta f: this is the open $1000 Erdos problem 687
(known: FGKMT lower x log x logloglog x / loglog x, Iwaniec upper x^2). No loophole: Y is sSup bounded by primorial.
Compiled (kept unchanged, from codex leg): Y_isGreatest, covered_iff_le_Y, predecessor_le_Y, cover_with_reserve,
sieve_one_modulus, sieve_small_primes, smooth_eq_divisor_mul_square, count_medium_survivors, cover_of_sieve_bound,
small_prime_product, primeCounting_eventually_upper/lower, eventually_smooth_bound, eventually_mul_le_Y_mul,
Y_monotone, eventually_mul_le_Y, tendsto_Y_div_atTop.
Remaining gap: OMA.answer (explicit scale) and the Theta proof = the open problem itself.
Dead ends: answer := Y is forbidden/circular; lower and upper known bounds differ polynomially.
Verdict: FAILED fast pass; stop at once.

## Leg 2: codex  (09:31, 8 min, ended: exit)
File stats: proved lemmas 30, sorries 2, lines 896 (was 16 / 2 / 479)
# Codex relay leg

Approach: quantify the existing Westzynthius sieve. The squarefree-part decomposition gives a small-prime density at most 2/log z. Take z = floor(log n/16), so the primorial bound still makes the smooth survivors negligible. Group survivors with a prime factor above n by their cofactor k and sum pi(y/k) using the harmonic bound. Reserve primes in (n,64n], then transfer by monotonicity to arbitrary x.

Compiled: all incoming lemmas, plus sum_inv_divisors_eq_div, sum_inv_divisors_prime_product, sum_inv_sq_le_two, prime_product_le_two_div_log, primeCounting_eventually_reserve, primorial_le_rpow_of_le_log, eventually_smooth_bound_of_le_log, eventually_primeCounting_upper_uniform, cover_of_medium_survivors, count_medium_survivors_sum, sum_primeCounting_div_le, eventually_y_ge_log_sieve, eventually_loglog_floor_le_Y, loglog_div_logloglog_isBigO_Y. The last theorem gives x loglog x/(1+logloglog x) = O(Y(x)).

Exact gap: OMA.answer needs an explicit asymptotic scale and OMA.solution needs the two-sided Theta estimate. The new result only supplies a lower bound. Both incoming template holes remain.

Dead ends: taking Y as the answer is circular. The existing quadratic Jacobsthal bound addresses the other direction at a different scale, and the linked Jacobsthal declaration in the local formal-conjectures source has a placeholder proof. The older product count pi(y) * (y/(n+1)+1) loses a factor in the cofactor variable.

Verification: direct Lean finished with only the two template warnings. Axiom audits for loglog_div_logloglog_isBigO_Y and tendsto_Y_div_atTop found only propext, Classical.choice, and Quot.sound. The requested checker rejected at lint with forbidden: 'sorry'. The first import and OMA.solution statement are exact.

Possible further lower-bound progress: a Rankin bound for smooth survivors could support a larger cutoff z. It would still leave the matching upper estimate.

## Leg 2: codex  (15:45, 0 min, ended: exit)
File stats: proved lemmas 30, sorries 2, lines 896 (was 30 / 2 / 896)
(the model wrote no notes; see partial_codex.lean)
