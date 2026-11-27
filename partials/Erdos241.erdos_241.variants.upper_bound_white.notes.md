# Relay notes for Erdos241.erdos_241.variants.upper_bound_white (prize: $100)


## Leg 1: grok  (23:52, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (23:53, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Leg 2 (opus) notes: Erdos241.erdos_241.variants.upper_bound_white
Approach: checked faithfulness only. The target is White 2024 (mu_2^2 >= 0.574636066) fed into
Green 2001 Fourier argument: f(N,3) <= ((2/0.574636066)^(1/3)+o(1)) N^(1/3), constant ~1.5155.
f is the genuine max size of a B_3 subset of [1,N] (multisets of size 3, equal sums imply equal).
No loophole: eps must be o(1), constant is below Green 7/2 bound (~1.519), so it is strictly
stronger than the also-unproved upper_bound variant. Trivial counting of 3-sums gives only
18^(1/3) ~ 2.62 (C(k+2,3) <= 3N), far from 1.5155.
Compiled: nothing new (file is still the single-sorry skeleton).
Remaining gap: the whole theorem (Green L2 autoconvolution + Fourier argument + White's
numerical inequality, a computer-assisted optimisation). Research-level, not session-sized.
Dead ends: same as upper_bound (memory erdos241-upper-bound-dead-ends). Recommend FAILED.

## Leg 3: codex  (00:06, 13 min, ended: exit)
File stats: proved lemmas 46, sorries 1, lines 897 (was 0 / 1 / 10)
# Erdos241 upper_bound_white, leg 3

Approach: injectivity of the nondegenerate signed triple a+b-c, after ordering a,b, yields the energy bound 2|A|+2|A|³/H and a crude cubic cardinality bound. Choose H = ceil(N^(5/6)). Box overlap and weighted variance relate the energy to continuous autoconvolution. Normalize to a probability density on [-1/2,1/2]. Parseval on [-1,1], the convolution identity, and the tangent inequality b⁴ ≥ 4a³b−3a⁴ reduce White’s bound to a rational Chebyshev polynomial certificate.

Compiled: `signedTriple_unique`, `signature_injOn`, `card_degenerate_le`, `card_cube_le`, `energy_le`, `exists_maximizer`, `energy_boxWeight_le`, `card_le_four_cbrt`, `asymptotic_of_boxEnergyLower`, `card_boxDiff`, `integral_cell_mul`, `integral_sumCells_sq`, `energy_eq_integral_sumCells_sq`, `convolution_sumCells`, `square_integral_mul_le`, `integral_convolution_cell_sq_le`, `boxEnergyLower_of_intervalAutoconvolutionLower`, `intervalAutoconvolutionLower_of_unit`, `autoconvolution_fourier_lower`, `autoconvolution_lower_of_certificate`, `fourierCertificate_of_chebyshev`, `unitAutoconvolutionLower_of_chebyshev`. Direct Lean succeeds with one final hole. The four main reduction lemmas depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Exact remaining gap: `OMA.White241.HasChebyshevCertificate (0.574636066 : ℝ)`. Supply finite S ⊂ ℤ and rational uₙ such that for all y ∈ [0,1], `(1/2) ∑_{n∈S} (4 uₙ³ Tₙ(y) − 3 uₙ⁴) ≥ 0.574636066`. The proof can alternatively finish by directly proving `UnitAutoconvolutionLower (0.574636066 : ℝ)` and dropping the last `apply`. No numerical certificate is available locally. The prescribed checker rejects at lint for the remaining hole.

Dead ends: counting positive triple sums misses the constant. Bounding cancellations per shift loses an order-|A| term. Exploratory floating-point dual optimization in `explore_white_dual.py` reached only about 0.574569 with 4096 positive modes and the corresponding negative modes. These are exploratory values, with no certified coefficients. Truncating to this range is too weak in the tested discretization.

## Leg 4: fable  (00:12, 5 min, ended: stalled)
File stats: proved lemmas 46, sorries 1, lines 897 (was 46 / 1 / 897)
(the model wrote no notes; see partial_fable.lean)
