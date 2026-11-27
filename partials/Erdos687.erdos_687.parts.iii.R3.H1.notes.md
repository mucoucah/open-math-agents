# Relay notes for Erdos687.erdos_687.parts.iii.R3.H1 (prize: )


## Leg 2: codex  (12:24, 62 min, ended: max60)
File stats: proved lemmas 98, sorries 1, lines 3076 (was 0 / 1 / 9)
# Erdős 687 iii R3 H1, Codex

Approach: truncated explicit formula at height T=x^(7/20). Bound the low-zero sum from density and a zero-free region, extract positive Chebyshev psi mass, and discard higher prime powers by Mathlib's O(sqrt x) estimate.

Compiled in the proof file:
- `exists_prime_of_theta_lt`, `eventually_prime_of_psi`, `eventually_mass_of_truncated_formula`, `norm_cpow_div_sub`, `norm_zeroSum_sub_le`.
- `sum_exp_le_of_count_le`, `zeroWeight_tendsto_zero`, `eventually_prime_of_zeta_estimates`.
- `zetaTermSum_eq`, `norm_riemannZeta₁_le`, `sum_mult_le_jensen`, `right_zeros_unit_count`, `multiplicity_one_sub`, `total_zero_count`, `density_of_right`.
- `negZetaLogDeriv_positive_combination`, `negZetaLogDeriv_near_pole`, `zeroFree_of_logDerivative`.
- `truncatedFormula_of_halfIntegers`, `zeroSum_height_increment`, `halfIntegerFormula_of_selectedHeight`, `exists_separated_height`, `selectedHeightFormula_of_separatedContour`.

Current gap: one placeholder for `ZetaContourEstimate` (shift the zeta Perron integral past the zeros, with the other edges bounded at a separated contour height), `RightDensityEstimate` (multiplicity-weighted N(σ,T) ≪ T^((12/5)(1−σ)) log^B T for 7/12≤σ≤1), and `ZetaGrowthNearOne` (polylogarithmic zeta growth on disks of radius \(4(\log(|t|+3))^{-2/3}\) centered at \(1+it\)).

Compiled and integrated `norm_logDeriv_le_of_ball`, `disk_logDerivative_upper`, `norm_inv_riemannZeta_le_real`, `riemannZeta_near_one_lower`, `zeroFree_of_scaledLogDerivative`, and `scaledLogDerivative_of_zetaGrowth`. Canonical factorization and Borel–Carathéodory derive the required zero-free region from the narrow-strip growth input. This implication has no placeholder.

Dead ends: Bertrand and fixed relative gaps give linear lengths. The RH proof is conditional. The known local Erdos233 formula is for smoothed psi in a different submission and is not an allowed import. The classical c/log T zero-free region alone does not absorb the log powers in the density estimate.

Compiled: `rectIntegral_inv`, `rectIntegral_perron_cross`, `perronVertical_error`, `hasSum_perronTerm_vertical`, `norm_zetaVertical_sub_psi_le_error`, `kernelErrorWeight_halfInteger`, and `separatedContourFormula_of_zetaContour`. This proves the full truncated Perron approximation for ψ at half-integers with error O(q log² q/H), including interchange of the series and the vertical integral. Only the shift across the zeta zeros and the other contour edges are still missing from the explicit formula.

## Leg 1: gemini  (12:51, 10 min, ended: no_progress_10m)
File stats: proved lemmas 98, sorries 1, lines 3076 (was 98 / 1 / 3076)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (14:01, 59 min, ended: exit)
File stats: proved lemmas 237, sorries 1, lines 7466 (was 98 / 1 / 3076)
# Erdős 687 iii R3 H1 — Codex

Approach: truncated Perron formula at height x^(7/20), density with exponent (8/3)(1−σ), and a strong zero-free region give positive Chebyshev mass in the requested prime interval. The contour and the deduction of density from a Weyl estimate are proved in the main file.

Verified contour: `rectIntegral_eq_sum_residues`, `rectIntegral_zetaPerron`, `exists_separated_abscissa`, `zeroSum_sub_filtered_le`, `norm_logDeriv_zeta₁_segment`, `zetaLogDeriv_on_selected_edges`, `zetaContourEstimate_proved`.

Verified density: `zeroWeight_tendsto_zero_with_density`, `rightDensity_of_separated_with`, `separatedDensity_of_shell`, `logDirichletPolynomial_sample_square`, `sample_weighted_dyadicPolynomial`, `divisor_square_sum_le`, `zetaDetector_vertical_difference`, `zetaDetector_right_integral`, `zetaDetector_dichotomy`, `detector_tail_moment`, and `detector_left_moment_of_weyl`. X=ceil H and Y≈H^(4/3) give the needed exponent. The Möbius detector uses rational smoothing with weight (1−n/Y)².

Verified growth: `norm_zeta_sub_cutoff`, `norm_weighted_sum_range_le`, `norm_sum_le_of_dyadic_block_bound`, `cubic_exponent_le`, `norm_zeta_of_oscillation`, and `zetaGrowthNearOne_of_oscillation`.

Exact remaining gap: the one placeholder is `WeylZetaEstimate ∧ ZetaOscillationEstimate`. The first needs |ζ(1/2+it)| ≪ (|t|+3)^(1/6) log^B(|t|+3). The second needs a Vinogradov–Korobov saving C N exp(−b(log N)^3/log²(|t|+3)) for dyadic prefix sums of n^(-it), up to ceil((|t|+3)^2). The full main file compiled locally with only the single placeholder warning. CI rejects the placeholder at lint.

Unintegrated scratch: `erdos687_interior_probe.lean` uses first-derivative cancellation for N≥|t| and trivial estimates for small N, aiming to reduce both assumptions to the middle ranges. The last probe reports two local errors, an extra tactic at line 3783 and a cast into the let-bound m at line 6220. `erdos687_interior_probe.py` assembles it from `erdos687_first_derivative_body.lean`, `erdos687_interior_vk_body.lean`, and `erdos687_weyl_oscillation_body.lean`.

Dead ends: fixed relative gaps give linear lengths, RH is conditional, and the classical 1/log T zero-free region does not absorb the density log powers. The unrelated smoothed explicit formula is unavailable as an allowed import.

## Leg 2: codex  (15:53, 0 min, ended: exit)
File stats: proved lemmas 237, sorries 1, lines 7466 (was 237 / 1 / 7466)
(the model wrote no notes; see partial_codex.lean)
