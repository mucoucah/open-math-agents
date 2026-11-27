# Relay notes for Erdos50.erdos_50 (prize: $250)


## Leg 1: opus  (08:00, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Leg 1 (opus) Erdos50.erdos_50
Statement: for every f with IsDistributionOfPhiRatio f, no x in [0,1] with HasDerivWithinAt f y (Icc 0 1) x and y>0.
Faithful translation of the OPEN Erdos question (erdosproblems #50, category research open).
Loophole audit: not vacuous (Schoenberg: f exists, determined on [0,1] by densities); derivative is within Icc,
so values outside [0,1] irrelevant; endpoints are genuine (x=0: f(c)=o(c), derivative 0;
x=1: 1-f(c) >> 1/log(1/(1-c)) so left derivative infinite) - neither gives a counterexample nor a cheap proof.
Interior points = the open problem itself. No Lean written beyond the sorry skeleton.
Dead ends: none worth pursuing; needs new mathematics. FAILED fast pass.

## Leg 2: codex  (08:13, 13 min, ended: exit)
File stats: proved lemmas 27, sorries 1, lines 796 (was 0 / 1 / 10)
Approach: 0 follows from a quadratic density upper bound. At 1, exact prime-avoidance counts, a mod-6 product lower bound of order m^(-1/3), and an O(1/m) large-divisor reciprocal average force unbounded left slopes. At a finite ratio r=totient(d)/d<1, dilation n↦d*n maps the tail near 1 into the band [r*(1-h),r+h), with density at least the original tail divided by d.
Compiled core lemmas: phi_product, prime_factor_estimate, phi_weight_bound, prime_subset_dvd, finite_prime_average, quadratic_density_bound, derivative_at_zero_nonpos, avoidance_count, totient_gap_le, reciprocal_square_tail, finite_large_divisor_average, wheel_step, wheel_product_bound, partialDensity_count, density_at_one, density_near_one, endpoint_growth_unbounded, no_derivative_at_one, density_difference, phi_ratio_mul_upper, scaled_tail_le_increment, derivative_increment_bound, no_derivative_at_finite_ratio, derivative_band_error, nearby_ratio_bound. Pinned Lean compiles with one sorry. The exact checker rejects the partial at lint for that sorry.
Exact gap: exclude a finite positive derivative at any x∈(0,1) with ¬∃ d:ℕ, 0<d ∧ x=(d.totient:ℝ)/d. It is the sole remaining branch of OMA.solution.
For the next leg: nearby_ratio_bound gives a necessary two-endpoint linearization inequality for every finite ratio r near x. The wheel estimate gives tail mass ≳h^(2/3) on h=1/(j+1), so a sequence of positive d with d^3*|r-x|→0 would contradict the inequality by choosing h comparable to |r-x|. This last implication is by hand and no such approximation theorem is established. Stronger original-prime estimates or control of aggregate mass may be needed.
Dead ends: the a.e. singularity theorem does not exclude exceptional differentiability. A spike from one finite pattern does not address a general interior x without quantitative approximation or aggregate control.

## Leg 1: opus  (09:45, 0 min, ended: exit)
File stats: proved lemmas 27, sorries 1, lines 796 (was 27 / 1 / 796)
# Leg (opus, relay leg 1 of this round) Erdos50.erdos_50
Approach: none new. File unchanged (796 lines, 27 compiled lemmas from codex leg, one sorry).
Compiled: x=0 (derivative_at_zero_nonpos), x=1 (no_derivative_at_one), every totient ratio
x=phi(d)/d (no_derivative_at_finite_ratio), plus helpers (nearby_ratio_bound, wheel_product_bound, ...).
Exact remaining gap: interior x in (0,1) that is NOT of the form totient(d)/d, finite y>0 derivative.
This IS the open Erdos question (erdosproblems #50, research open); no known proof.
Dead ends: a.e. singularity (merged erdos_50_singular) does not exclude exceptional points;
the d^3|phi(d)/d - x| -> 0 approximation idea is unproven (and false-in-general expectations:
generic x need not admit such good approximations by totient ratios).
Recommendation: do not spend further legs; the sorry is the open core.

## Leg 2: codex  (09:51, 5 min, ended: stalled)
File stats: proved lemmas 27, sorries 1, lines 796 (was 27 / 1 / 796)
# Codex relay leg 2

Existing endpoint and finite-ratio lemmas are preserved. Trying to improve the quantitative obstruction by conditioning the divisor average on avoidance of the small primes. The exact checker rejected the incoming partial at lint for its single sorry.

Remaining gap: interior points which are not finite totient ratios. A.e. singularity and the previously proposed universal rapid ratio approximation supply no proof of this branch.

## Leg 3: fable  (09:56, 5 min, ended: stalled)
File stats: proved lemmas 27, sorries 1, lines 796 (was 27 / 1 / 796)
(the model wrote no notes; see partial_fable.lean)

## Leg 1: gemini  (15:02, 10 min, ended: no_progress_10m)
File stats: proved lemmas 27, sorries 1, lines 796 (was 27 / 1 / 796)
# Gemini Leg 1 Notes — Erdos50.erdos_50

## Status
- Target: `Erdos50.erdos_50` (faithful formalization of open Erdős Problem #50: no $x \in [0,1]$ with finite positive derivative $f'(x) = y > 0$ for the distribution function $f$ of $\varphi(n)/n$).
- Existing partial in `proofs/Erdos50.erdos_50.lean` (796 lines, 27 compiled lemmas, 1 sorry):
  - `x = 0`: `derivative_at_zero_nonpos` ($f'(0) \le 0$).
  - `x = 1`: `no_derivative_at_one`.
  - `x = \varphi(d)/d < 1`: `no_derivative_at_finite_ratio`.
  - Quantitative linearization: `nearby_ratio_bound`.

## Mathematical Analysis of Remaining Gap
- Remaining branch: $x \in (0, 1)$ NOT of the form $\varphi(d)/d$ for any $d > 0$, with `HasDerivWithinAt f y (Icc 0 1) x` and $y > 0$.
- **Why single-ratio approximation cannot solve all $x$**:
  - Concrete counterexample to fast approximation: $x = 1/4$. It is not a totient ratio (the largest prime dividing $d$ always divides the reduced denominator of $\varphi(d)/d$), and for ALL $d \ge 1$, $|4\varphi(d) - d| \ge 1$, so $|\varphi(d)/d - 1/4| \ge 1/(4d)$. Even with the sharp tail bound $1 - f(1 - h) \asymp 1/\log(1/h)$, a single $d$ only yields $\frac{1 - f(1 - \Delta)}{d} \asymp \frac{\Delta}{\log(1/\Delta)} = o(\Delta)$, falling short by $\log(1/\Delta)$.
- **Why multi-scale convolution alone fails**:
  - Splitting $Y = -\log(\varphi(n)/n) = Y_{\le P} + Y_{> P}$ yields $\mu_{\le P}((t + a/P, t + b/P]) = (1 + o(1))(b - a)z/P$ for all fixed $a < b$.
  - However, $z \cdot 	ext{Lebesgue}$ is invariant under convolution with $
u_{> P}$, and the atypical atoms of $\mu_{\le P}$ with $d \le \exp(C(\log P)^2/\log\log P)$ still carry mass $\ge 1/P$ with superpolynomially many atoms, so macro convolution estimates remain self-consistent.

## Planned Compiled Progress
1. Upgrade the tail lower bound near $1$ from $h^{2/3}$ (wheel bound) to a Chebyshev/polylogarithmic bound $1 - f(1 - h) \ge c / (\log(1/h))^2$ (or optimal $h^{1/2}$ + Chebyshev $	heta(x) \le (\log 4)x$).
2. Use `nearby_ratio_bound` + upgraded tail bound to prove `no_derivative_at_well_approximable`: exclude every interior $x \in (0, 1)$ admitting arbitrarily good approximations by totient ratios (in particular, a dense $G_\delta$ set of non-ratio interior points).
3. Prove monotonicity and prime-factor decomposition / convolution lemmas for $f$ if helpful for downstream legs.

## Leg 2: codex  (15:21, 10 min, ended: exit)
File stats: proved lemmas 44, sorries 1, lines 1676 (was 27 / 1 / 796)
# Codex relay leg 2

Preserved the 27 incoming lemmas. The pinned Lean toolchain compiles 44 lemmas and the one unfinished theorem branch. CI rejects at lint with `forbidden: 'sorry'`. The main new results were independently audited and depend only on propext, Classical.choice and Quot.sound.

New compiled lemmas:
- Wheel and Baire: tail_at_inverse_square, finite_ratio_separation, prime_product_ratio, finite_ratio_between, dense_nondifferentiability.
- Logarithmic tail via the finite Euler product at 1+t: weighted_prime_reciprocals, inverse_zeta_bound, prime_product_log_bound, small_scale_log_limit, logarithmic_tail_lower.
- Single-ratio obstruction: logarithmic_ratio_separation, scale_log_mono, finite_ratio_log_separation, logarithmic_ratio_divergence.
- Aggregate obstruction: density_finset_dilates_le, scaled_tail_family_le_increment, local_pattern_weight_bound.

Remaining gap: exclude a positive finite derivative at an interior x outside the finite ratios, even when d a (1+log(1/a)) diverges as a = |φ(d)/d−x| tends to 0 and the local pattern bound holds. For squarefree d with every prime factor below 1/h and ratio within h of x, local_pattern_weight_bound bounds the sum of 1/d by O(h log(1/h)). The proof counts disjoint dilates of the near-1 tail. No complementary lower bound or local asymmetry yielding a contradiction is known here.

Dead ends: almost-everywhere singularity leaves exceptional points. Universal fast approximation by one ratio fails at 1/4, where the gap is at least 1/(4d). The logarithmic estimate strengthens but does not bypass that arithmetic barrier.

## Leg 1: gemini  (15:29, 3 min, ended: exit)
File stats: proved lemmas 44, sorries 1, lines 1676 (was 44 / 1 / 1676)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (15:40, 2 min, ended: exit)
File stats: proved lemmas 44, sorries 1, lines 1676 (was 44 / 1 / 1676)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: fable  (16:05, 22 min, ended: exit)
File stats: proved lemmas 53, sorries 1, lines 1848 (was 44 / 1 / 1676)
# Fable relay leg 3 notes: Erdos50.erdos_50

Approach: kept the 44 incoming lemmas untouched (x=0, x=1, every totient ratio, log tail, single-ratio
and aggregate obstructions). Re-audited the statement: faithful open Erdos #50, no loophole.
Direct compile (10 s): cd repo/.oma/formal-conjectures && lake env lean <abs path>.
check.sh verdict: rejected, lint: forbidden sorry (the only complaint).

Compiled this leg (file now 53 lemmas, 1848 lines, one sorry):
- density_nonneg, density_le_one, distribution_mono (f monotone on [0,1]), distribution_bounds.
- Barrier lemmas: four_totient_ne (4*phi(d) != d), quarter_not_ratio (1/4 is an interior
  non-ratio point, so the open branch is not vacuous), quarter_gap (|phi(d)/d - 1/4| >= 1/(4d)),
  quarter_separation_automatic and rational_separation_automatic: at 1/4, and at EVERY rational
  a/b that is not a totient ratio, the conclusion of logarithmic_ratio_divergence
  (d*gap*(1+log(1/gap)) -> infinity) holds with no derivative assumption at all.
  So hsep in the sorry branch carries no information at rational points. Do not try to close
  the branch from hsep.

Remaining gap (unchanged, sole sorry in OMA.solution): interior x in (0,1), x not phi(d)/d, finite y>0.

Analysis this leg (by hand, not Lean):
- Derivative y at x <=> the level-P atomic measure sum_{d | P#} w_d delta_{r_d}, blown up by P around x,
  converges vaguely to y*Lebesgue. y*Lebesgue is a fixed point of the P -> 2P dynamics
  (zoom by 2 plus a (log 2/log P) fraction of one-sided smoothing), so first-moment arguments
  (single ratio, aggregate dilates, upper AND lower pattern-weight bounds) are all self-consistent.
- For rational x (e.g. 1/4) nearest atoms satisfy b*phi(d) - a*d = j with gcd(d,phi(d)) | j:
  Lehmer-type equations. Small-j atoms carry only a 1/log P fraction of a window mass, so their
  scarcity contradicts nothing.
- Heuristic (mine, unproved): the density ratio along dyadic windows is a martingale whose
  increments away from heavy atoms are about 1/sqrt(log(1/h)) and tend to 0, and heavy atoms are
  sparse (spacing eps*h*log(1/h)). In a random model one can steer nested windows so the ratio
  converges, as for Riesz products. So points with a finite positive derivative may well exist,
  i.e. the target could even be FALSE. Nothing here decides it either way.

Dead ends: first-moment mass counting in any form; one-prime functional equation
f(c) = g(c) + g(c p/(p-1))/(p-1) (two unknown functions, differentiability does not transport);
rational x via denominators (gap >= 1/(b d) defeats the log criterion, now Lean-checked);
a lower pattern-weight bound needs independence of smooth part and rough part (crude Markov
gives 1/(K^2 log(1/h)), not o(h)) and would still not contradict anything.

Recommendation: stop relay legs on this target; the sorry is the open problem itself.
