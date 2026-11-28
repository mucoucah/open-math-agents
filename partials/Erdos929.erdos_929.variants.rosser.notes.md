# Relay notes for Erdos929.erdos_929.variants.rosser (prize: )


## Leg 3: opus  (18:02, 3 min, ended: exit)
File stats: proved lemmas 8, sorries 1, lines 174 (was 0 / 1 / 10)
# Opus relay leg 3: Erdos929.erdos_929.variants.rosser
Approach: own glue in proofs file (namespace OMA.E929). Direct compile OK (lake env lean, about 6 s).
check.sh: rejected, lint forbidden sorry (only complaint).
Compiled lemmas: cover_shift, nonempty_of_pos, pd_count, count_mul_per, periodic_pos (nonempty
periodic set has positive density, full proof), witness (covered block at x = S k), algebra
(k <= C x^(2+eps) gives x >= k^(1/2-eps) eventually), OMA.solution (from these plus the core).
ONE sorry: jacobsthal_core :
  forall delta>0, exists C>0, forall x k n, AllHaveSmallPrimeFactor x k n -> k <= C * x^(2+delta)
= Iwaniec/Rosser linear sieve bound for the Jacobsthal function of the primorial (beta=2).
Infeasible in one leg. Brun pure sieve / fundamental lemma only give x^(C loglog x) or x^s for
some large fixed s, both too weak for exponent 1/2. Upstream R1.H1.R1 reduces to StrongPNT plus
conditional Iwaniec (jasondavies/iwaniec-linear-sieve, a whole project).
Dead ends: no loophole; S k is faithful (periodic sets have density, proved here).

## Leg 4: fable  (18:09, 7 min, ended: exit)
File stats: proved lemmas 11, sorries 1, lines 273 (was 8 / 1 / 174)
# Fable relay leg 4: Erdos929.erdos_929.variants.rosser

Approach: kept opus leg 3 glue (namespace OMA.E929). jacobsthal_core is now PROVED from a pure
sieve-weights lemma by double counting. File compiles (lake env lean, 7 s) with ONE sorry.
Backup of the leg 3 file: .oma/scratch/e929/before_fable.lean.

Compiled lemmas: cover_shift, nonempty_of_pos, pd_count, count_mul_per, periodic_pos, witness,
algebra, OMA.solution (all leg 3), plus NEW this leg:
- cnt_eq   : sum_{i in Icc 1 k} [d | n+i] = (n+k)/d - n/d  (real cast of Nat floors)
- cnt_close: that count is within 1 of k/d
- jacobsthal_core (was the sorry): covered block k <= C*C * x^(2+delta), from sieve_weights (delta/2)

Exact remaining gap (the only sorry), sieve_weights :
  forall delta>0, exists C>0, forall x>=1, exists (D : Finset Nat) (lam : Nat -> Real),
    (all d in D are positive) and  sum_{d in D} |lam d| <= C * x^(2+delta)
    and 1 <= C * x^delta * sum_{d in D} lam d / d
    and forall m>0 with a prime factor <= x :  sum_{d in D, d | m} lam d <= 0
= existence of lower-bound LINEAR sieve weights with sifting limit beta = 2 (Rosser-Iwaniec beta
sieve, or Jurkat-Richert). No interval, no density, no S left in it. Checked true at x=1
(D={1}, lam 1 = 1) and x=2 (D={1,2}, lam = 1,-1); small x by Legendre weights mu(d), d | primorial
(constant absorbed in C); large x needs main term V^-(D,z) >= c/log x at level D = x^(2+delta).

Dead ends checked on paper this leg (do not retry):
- one Buchstab step on top of Selberg upper bound: sifting limit 2.06 (Ankeny-Onishi), gives only
  S k > k^(0.485), not 1/2 - eps for every eps. Needs the INFINITE iteration to reach 2.
- Selberg lower sieve (1 - sum_{p|a} 1) * (sum lambda_d)^2 with one lambda: main term positive
  iff xi > z, but level is z * xi^2 > z^3, so exponent 3 not 2.
- survivors of primes <= x^theta then cover by larger primes with upper-bound sieve: needs
  log(1/theta) < 1/F(s), fails at exponent 2 (works only near 2.4).
- Brun pure sieve / fundamental lemma: exponent is some large constant (leg 3 note).
- large sieve / variance (Montgomery-Vaughan) gives almost all intervals, not all.
- upstream route: R1.H1.R1 (JamesSlash) = StrongPNT + conditional Iwaniec; open PRs 12817/12818
  claim H1/H2, files not available locally; if merged the chain closes upstream.
Next step if anyone continues: beta-sieve weights lam = mu on d = p1>p2>... with
p1...pm * pm^2 < D for all even m; the combinatorial inequality is easy, the main-term bound
(sum over even m of V_m <= (1-c) V(z)) is the whole difficulty (needs Mertens product estimates).
