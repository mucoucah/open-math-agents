# Relay notes for Erdos40.erdos_40.variants.weaker (prize: $500)


## Leg 1: grok  (04:23, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (04:24, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos40.erdos_40.variants.weaker, leg 2 (opus)
Verdict: FAILED fast pass. Faithful formalisation of an OPEN problem that implies Erdos-Turan (Erdos 28),
via upstream implies_erdos_28. No loophole:
- g real-valued but must tend to infinity, so g=0 / negative tricks are impossible eventually.
- Fast-growing g (e.g. g N = N) makes Erdos40For FALSE: A = {1} gives sqrt N / N = O(1) but sumRep bounded.
- So any witness g must grow slowly, and then Erdos40For g is at least as strong as Erdos-Turan.
Compiled: nothing new (file is the 1-sorry skeleton). Existing reduction R1 (H1 finite uniform window, H2 thinning)
is merged upstream; both steps are research-level.
Dead ends: loophole hunt in Erdos40For (none).

## Leg 4: fable  (04:29, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_fable.lean)

## Leg 1: gemini  (15:16, 55 min, ended: exit)
File stats: proved lemmas 59, sorries 1, lines 2798 (was 0 / 1 / 10)
# Erdos40.erdos_40.variants.weaker — Gemini leg 1 handover notes

## Approach & mathematical status
- Target: `∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40For g`.
- Verified faithful formalization with zero loopholes: upstream `Erdos40.erdos_40.variants.implies_erdos_28` (proved sorry-free in `FormalConjectures/ErdosProblems/40.lean`) proves the target implies `Erdos28.erdos_28` (the open 1941 Erdős-Turán conjecture on additive bases of order 2).
- `weaker_iff_constant_one` establishes exact equivalence with `Erdos40For (fun _ ↦ 1)` (no `B_2[g]` set has `|A ∩ [1, N]| ≫ √N`). Even the `g = 2` (`B_2[2]`, `sumRep A n ≤ 4`) case is open.
- File `proofs/Erdos40.erdos_40.variants.weaker.lean` compiles cleanly via `lean` (v4.33.1) with zero double quotes and a single `sorry` at `even_cap_no_dense_shift_not_sqrt_dense`.

## Compiled lemmas in `proofs/Erdos40.erdos_40.variants.weaker.lean`
### Baseline (kept intact)
- `mem_repPairs`, `card_repPairs`, `sidon_diff_inj`, `card_sq_eq_two_mul_lt_add_self`, `sidon_prefix_sq_le`, `sq_sum_le_card_mul_sum_sq_nat`, `bucket_close_pairs_bound`, `sidon_not_sqrt_dense`
- `exists_diag_of_odd_rep`, `greedyDrop`, `greedyDrop_iff`, `exists_even_cap_sub`, `cap_three_not_sqrt_dense`
- `sumRep_shift_inter_lt`, `sumRep_shift_inter_le`, `shift_inter_not_sqrt_dense_of_cap_four`
- `exists_global_cap_of_limsup_ne_top`, `exists_uniform_drop_window`, `weaker_of_constant_one`

### Compiled in leg 1 (prior pass, kept intact)
- `diffPairs`, `mem_diffPairs`, `sum_card_diffPairs_eq`, `sum_card_repPairs_eq`
- `additive_energy_eq_sq_add_two_mul_diff_sq`, `prefixSet`, `mem_prefixSet`, `prefixSet_subset_Icc`, `card_prefixSet`
- `cap_diff_sq_sum_le`, `cap_prefix_sq_le_sharp`, `cap_prefix_sq_le`
- `close_pairs_unbounded_of_quad_prefix`, `cap_close_pairs_unbounded`, `cap_diff_mult_unbounded`
- `diff_bounded_not_sqrt_dense`, `cap_four_cross_shift_mul_sum_le`, `bounded_cap_not_sqrt_dense`

### Newly compiled in this session
- `constant_one_of_weaker`, `weaker_iff_constant_one`
- `shift_eq_min_gap_of_card_union_le_add_one`, `exists_shift_card_union_ge_add_two`
- `card_fst_repPairs`, `card_union_fst_shift_le_sumRep`
- `sumRep_two_shift_inter_le`, `two_shift_inter_sidon_of_cap_four`, `two_shift_inter_subsingleton_of_cap_three`
- `card_inter_image_add_eq_diffPairs`, `sumRep_multi_shift_inter_bound`, `sumRep_multi_shift_inter_le_half`
- `sq_sum_le_card_mul_sum_sq_real`, `sum_Ico_succ_sub`, `dyadBlock`, `mem_dyadBlock`, `card_prefixSet_pow_two_succ`, `dyadBlock_close_pairs_bound`
- `dyadic_close_pairs_master`
- `diff_bounded_prefix_sq_le`, `diff_bounded_erdos_1955_quantitative`, `sidon_erdos_1955_quantitative`, `cap_three_erdos_1955_quantitative`
- `cap_log_close_pairs_at_sq`, `cap_log_diff_mult_at_sq`

## Exact remaining gap
- Single `sorry`: `even_cap_no_dense_shift_not_sqrt_dense` (line 2744): for `g ≥ 2`, no set `A` with `∀ n, sumRep A n ≤ 2 * g`, no `≫ √N`-dense positive shift intersection `A ∩ (A - d)`, and logarithmic positive difference multiplicity `Ω(m)` inside `[1, 2^(2m)]` for some `0 < d < 2^m` (for all large `m`) can satisfy `|A ∩ [1, N]| ≫ √N`.
- Closing this single lemma immediately closes `OMA.solution` (which is already proved sorry-free modulo `even_cap_no_dense_shift_not_sqrt_dense`) and formally proves `Erdos28.erdos_28`.

## Dead ends
- Loophole search: none (`Erdos40.erdos_40.variants.implies_erdos_28` already links target to `Erdos28.erdos_28`, which is faithful).
- Pure L2 / additive energy / Cauchy-Schwarz / Parseval bounds: Ruzsa (1990) constructed an order-2 additive basis with bounded mean-square representation count, and the random model `p_n = c / √n` satisfies all low-order moment, energy, cross-block inner product, and `Ω(P log P)` close-pair statistics at scale `N = P^2`.
- Two-shift / multi-shift intersections alone: in the random model `p_n = c / √n`, `A ∩ (A - d_1) ∩ (A - d_2)` has expected size `∑ c^3 / n^(3/2) = O(1)` (a.s. finite), so `two_shift_inter_sidon_of_cap_four` and `sumRep_multi_shift_inter_le_half` are compatible with `|A ∩ [1, N]| ≫ √N`.

## Leg 2: codex  (15:38, 13 min, ended: exit)
File stats: proved lemmas 74, sorries 1, lines 3413 (was 59 / 1 / 2798)
# Codex relay
- Approach: force many repeated differences in linear-size prefixes, then use the cap to constrain the corresponding rectangles and sums.
- Compiled shift/pattern lemmas: exists_shift_inter_half_cap_sub, card_reflected_le_sumRep, cap_four_rectangle_anchor_gap, sumRep_le_two_of_unique_shifts, cap_four_shift_inter_sidon_except_one, lower_rep_card_le, cap_four_rectangle_sum_inj. Shift intersections retain half of every prefix at half the cap. At cap four, one deletion suffices to make each shift intersection Sidon, and the sum determines the rectangle when its shorter side is the shift.
- Compiled density lemmas: dyadic_close_pairs_master_window, cap_close_pairs_in_dyadic_window, short_diff_pairs_sum, cap_popular_differences_in_linear_window, cap_popular_differences_in_linear_prefix. For each fixed L and all large P, a positive proportion of d < P occur at least L times by M*P for fixed M. The old dyadic theorems remain as special cases.
- Compiled saturation lemmas: exists_nondegenerate_rectangle_of_diffPairs, cap_four_saturated_sums_in_linear_prefix. At cap four, a putative dense set saturates sumRep on a positive proportion of sums in each sufficiently large prefix. A selected rectangle yields a saturated sum, and each sum has at most two chosen directions by canonical injectivity.
- Exact remaining gap: even_cap_popular_differences_not_sqrt_dense is the sole sorry. Need a contradiction for cap 2*g (starting at g=2) with square-root prefix density, no square-root-dense fixed positive shift intersection, logarithmic repeats by P^2, and the linear-window positive-proportion bound. The cap-four saturation lemma gives another necessary condition. The old core is now derived from the strengthened one.
- Dead ends: definitional loopholes, L2-only contradiction, fixed-shift sparsity alone. Unrestricted witness heights lose scale information. The rectangle count forces saturation, with its lower bound still below the available number of sums. A finite separated product of two Sidon blocks already exhibits positive saturation at one scale, so use persistence across scales or a stronger coincidence argument.
- Verification: the integrated target file compiled directly in Lean with only the sole sorry warning. The specified checker rejected the integrated file at lint with forbidden sorry. The first import, theorem statement, and existing declarations were preserved.

## Leg 2: codex  (15:43, 0 min, ended: exit)
File stats: proved lemmas 74, sorries 1, lines 3413 (was 74 / 1 / 3413)
(the model wrote no notes; see partial_codex.lean)
