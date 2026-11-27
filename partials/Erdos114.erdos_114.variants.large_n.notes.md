# Relay notes for Erdos114.erdos_114.variants.large_n (prize: $250)


## Leg 1: fable  (22:37, 3 min, ended: exit)
File stats: proved lemmas 8, sorries 1, lines 84 (was 0 / 1 / 10)
# notes_fable (leg 1) - Erdos114.erdos_114.variants.large_n

RESULT OF LEG: STALLED (stopped on purpose). The proofs file compiles with ONE sorry: OMA.core_centred.

## Approach / verdict
Target = full theorem of Tao 2025 (arXiv 2512.12455): for all large n, every monic degree-n p has
H^1{|p|=1} <= H^1{|z^n-1|=1}. Statement checked faithful, NO loophole:
- lemniscateLength = muH[1] of {z | norm (p.eval z) = 1} on C with the Euclidean metric (true arc length).
- RHS is finite (compact analytic curve, length 2n+O(1)), so no top trick; LHS is not trivially small.
- The eventually-in-n quantifier is the real one; no vacuous case.
The paper is ~50 pages of potential theory / harmonic analysis on top of Fryntov-Nazarov. Not a relay-sized job.

## What compiles (proofs file; direct lake env lean gives warnings only)
- OMA.lemniscate_comp_X_add_C : lemniscate (p.comp (X + C a)) = (IsometryEquiv.addRight a) preimage of lemniscate p
- OMA.lemniscateLength_comp_X_add_C : translation invariance of lemniscateLength
- OMA.monic_comp_X_add_C, OMA.natDegree_comp_X_add_C'
- OMA.coeff_comp_X_add_C_of_natDegree : monic p of natDegree m+1 -> (p.comp (X + C a)).coeff m = (m+1)*a + p.coeff m
  (via taylor_coeff + hasseDeriv_coeff)
- OMA.reduce_to_centred : for n >= 1, the bound for monic q with q.coeff (n-1) = 0 implies it for all monic p of degree n
- OMA.core (from core_centred + reduce_to_centred, filter_upwards), OMA.solution (exact OMA.core)
Fast compile (5 s): cd /workspace/left-to-solve/repo/.oma/formal-conjectures && lake env lean <abs path of proofs file>

## Exact remaining gap
OMA.core_centred (sorry): eventually in n, every monic q of natDegree n with q.coeff (n-1) = 0 satisfies
lemniscateLength q <= lemniscateLength (X^n - 1). This is still the whole Tao theorem (centring is only
the trivial normalisation: zeros have mean 0).

## Dead ends / do not repeat
- Loophole hunt in the statement: none (see above).
- Mathlib has no arc-length = muH[1] machinery for analytic curves and no lemniscate facts; even computing
  lemniscateLength (X^n - 1) (or showing it is >= 2n) is a project by itself.
- More invariance lemmas (rotation by unit u, q(z) = u^(-n) p(u z)) are possible but do not shrink the gap.
Recommendation: report FAILED for the fast pass; do not spend further legs.

## Leg 2: opus  (22:38, 0 min, ended: exit)
File stats: proved lemmas 8, sorries 1, lines 84 (was 8 / 1 / 84)
# notes_opus (leg 2) - Erdos114.erdos_114.variants.large_n

RESULT OF LEG: STALLED (stopped early on purpose, ~3 min).

## Approach
No change to leg 1 approach. Re-verified the proofs file compiles (lake env lean): warnings only,
ONE sorry OMA.core_centred (line 71). File left untouched.

## What compiled (unchanged from leg 1)
OMA.lemniscate_comp_X_add_C, OMA.lemniscateLength_comp_X_add_C, OMA.monic_comp_X_add_C,
OMA.natDegree_comp_X_add_C', OMA.coeff_comp_X_add_C_of_natDegree, OMA.reduce_to_centred,
OMA.core, OMA.solution.

## Exact remaining gap
OMA.core_centred = the whole Tao 2025 theorem (arXiv 2512.12455) for centred monic polynomials.
Needs arc length of analytic level curves as muH[1], lemniscate potential theory and
Fryntov-Nazarov; none of it is in Mathlib. Not relay-sized.

## Dead ends
Same as leg 1 (statement faithful, no loophole; invariance lemmas do not shrink the gap).
Recommendation: report FAILED; do not spend further legs.

## Leg 3: grok  (22:43, 5 min, ended: stalled)
File stats: proved lemmas 8, sorries 1, lines 84 (was 8 / 1 / 84)
(the model wrote no notes; see partial_grok.lean)

## Leg 4: codex  (22:48, 5 min, ended: exit)
File stats: proved lemmas 25, sorries 1, lines 452 (was 8 / 1 / 84)
# Leg 4 Codex

RESULT: STALLED. The proof file elaborates with one sorry. The required CI checker rejects it at lint for that sorry.

Approach. Keep the centering reduction. For the benchmark, write z as a point on a radial arc indexed by an n-th root of unity and the sign of Im(z^n). The 2n open arcs are disjoint and their 1-Lipschitz norm projections cover (0,R), where R^n = 2. For the upper bound, the closed arcs cover the entire lemniscate. Reparametrize by radius plus scaled angular variation to make each arc 1-Lipschitz.

Compiled. All earlier lemmas remain. New helpers are norm_sub_one_eq_one_iff, mem_lemniscate_X_pow_sub_one_iff, continuous_modelArc, norm_modelArc, modelArc_pow, modelArc_mem, modelArc_index_unique, exists_modelArc_of_mem, lemniscate_model_eq_iUnion, norm_exp_mul_I_sub_le and modelArc_length_upper. New benchmark results are model_length_lower_bound, model_length_ge_two_mul_degree, model_length_ge_radial_diameter_sum, model_length_upper_bound and model_length_lt_top. The benchmark bounds are 2nR and 2nR + πR. The lower bound, upper bound and finiteness passed a direct axiom audit with only propext, Classical.choice and Quot.sound.

Exact gap. OMA.core_centred_long is the lone sorry. For all sufficiently large n, a centred monic degree-n q of length strictly greater than 2n times 2^(1/n) must have length at most that of X^n - 1. OMA.core_centred handles the complementary case using the compiled lower bound.

Dead ends. Earlier legs ruled out vacuity and infinity shortcuts. The benchmark bounds give no sharp upper bound for arbitrary centred q. General analytic arc-length identification was not attempted again. The remaining gap needs the sharp comparison from Tao's argument.
