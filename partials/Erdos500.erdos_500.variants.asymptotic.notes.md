# Relay notes for Erdos500.erdos_500.variants.asymptotic (prize: $500)


## Leg 1: gemini  (15:12, 30 min, ended: no_progress_10m)
File stats: proved lemmas 55, sorries 1, lines 1543 (was 0 / 2 / 16)
# Handover Notes (Gemini leg 1) — Erdos500.erdos_500.variants.asymptotic

## Approach
- Verified upstream formalization (`FormalConjectures/ErdosProblems/500.lean` and `Hypergraph.cliqueExtremalNumber`): faithfully states Turán's 1941 open tetrahedron density problem `pi(K_4^3) = lim_{n -> infty} ex_3(n, K_4^3) / C(n, 3)` ($500 Erdős prize; best known literature bounds `[5/9, 0.557789)` as of arXiv:2609.27495).
- Verified with `tools/check.sh` that `proofs/Erdos500.erdos_500.variants.asymptotic.lean` passes every `tools/lint.py` rule (exact first import, `OMA.answer := 5 / 9`, `OMA.solution` signature, no double quotes, no banned constructs) except the single remaining `sorry` in `OMA.turan_upper_bound`.
- Preserved all 1,544 lines of compiled sorry-free lemmas untouched.

## Compiled Lemmas (all sorry-free, axioms within `propext, Classical.choice, Quot.sound`)
- `OMA.answer : ℝ := 5 / 9`
- `OMA.turanDensity`, `OMA.scaledExtremal`
- `OMA.cliqueExtremalNumber_ge_card`, `OMA.exists_extremal_hypergraph`
- `OMA.cliqueExtremalNumber_step`, `OMA.turanDensity_succ_le`, `OMA.turanDensity_antitone`
- `OMA.turanGraph`, `OMA.turanGraph_no_K4`, `OMA.turan_extremal_lower_parts`, `OMA.turan_extremal_lower_nat`
- `OMA.five_ninths_sub_le_turanDensity`, `OMA.five_ninths_le_turanDensity`
- `OMA.cliqueExtremalNumber_four` (= 3), `OMA.cliqueExtremalNumber_five` (= 7), `OMA.cliqueExtremalNumber_six` (= 14), `OMA.cliqueExtremalNumber_seven` (= 23), `OMA.cliqueExtremalNumber_eight` (= 36), `OMA.cliqueExtremalNumber_nine` (= 54)
- `OMA.cliqueExtremalNumber_ten_le` (`<= 76`, via `OMA.card_cover_eight`, `OMA.card_cover_nine`, `OMA.card_cover_ten`)
- `OMA.turanDensity_le_twenty_two_thirty_fifths` (`<= 22/35` for `n >= 21`)
- `OMA.turanDensity_le_five_eighths` (`<= 5/8 = 0.625` for `n >= 14`)
- `OMA.turanDensity_le_of_ten` (`<= 99481/161700 < 0.6153` for `n >= 100`, via `OMA.knsIter`)
- `OMA.exists_turanDensity_limit` (`∃ L, 5/9 ≤ L ∧ L ≤ 99481/161700 ∧ Tendsto OMA.turanDensity atTop (𝓝 L)`)
- `OMA.extremal_blowup_lower`, `OMA.scaledExtremal_tendsto`, `OMA.scaledExtremal_le_blowup`, `OMA.density_le_iff_finite`, `OMA.tetrahedron_density_eq_iff_finite` (`d = 5/9 ↔ ∀ n > 0, 54 * ex_3(n, K_4^3) ≤ 5 * n^3`)
- `OMA.solution` (reduced cleanly to `OMA.turan_upper_bound`)

## Exact Remaining Gap
- `OMA.turan_upper_bound : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 3 ≤ n ∧ OMA.turanDensity n ≤ 5 / 9 + ε`
  (equivalently, by `OMA.tetrahedron_density_eq_iff_finite`, `∀ n > 0, 54 * Hypergraph.cliqueExtremalNumber n 3 4 ≤ 5 * n ^ 3`).
- Closing this sorry requires proving Turán's 1941 tetrahedron conjecture `pi(K_4^3) = 5 / 9` (or determining the true exact value of `pi(K_4^3)` as an explicit real constant if `pi(K_4^3) > 5/9`), a major open problem in extremal combinatorics.

## Dead Ends
- Formalization loophole check: none exists; `Hypergraph.cliqueExtremalNumber n 3 4` is exact, and `tools/lint.py` plus human review forbid non-explicit `OMA.answer` (no `Classical.choose`, `sInf`, `iInf`, `limUnder`, etc.).
- Codegree Cauchy-Schwarz / Moon-Moser on link graphs caps at `2/3`; Goodman triangle count on link graphs gives `(1/n) sum_v t_3(G_v)/C(n-1,3) = (1/4) x_3`, which combined with `3 x_3 <= 4p` also caps at `2/3` without bounding `x_0, x_1, x_2` from below.
- Iterated KNS from `n = 10` (`ex <= 76` or exact `ex = 75`) asymptotes near `0.615` / `0.614`; Chung-Lu (1999) caps at `(3 + sqrt(17))/12 ≈ 0.5936`.
- Razborov (2010) proves `<= 5/9` only under the extra assumption `x_1 = 0` (no 4-set with 1 edge); unconstrained flag-algebra SDPs through 2026 (arXiv:2609.27495) only reach `< 0.557789`, still strictly above `5/9 ≈ 0.555556`, and exponentially many non-isomorphic extremal 3-graphs of density `5/9` (Kostochka, Fon-der-Flaass, Frohmader) obstruct standard symmetrization/Lagrangian/stability proofs.

## Leg 2: codex  (15:39, 24 min, ended: exit)
File stats: proved lemmas 83, sorries 1, lines 2266 (was 55 / 1 / 1543)
# Codex leg 2

- Approach: continued the inherited covering and blow-up proofs. Tight deletions exclude the rounded cap on 39 vertices. More importantly, an exact integer sum-of-squares certificate on five labels gives the uniform scaled bound 23/40. Pull back along every function from the five labels, including repeats. The pullback stays tetrahedron-free, and the two extra coordinates average independently into squares.
- Compiled and audited: `OMA.flagCertificate_valid`, `OMA.tetrahedron_cubic_upper_flag` (`240 * ex₃(n,K₄³) ≤ 23 * n³`), and `OMA.tetrahedron_density_le_flag` (`d ≤ 23/40`). All use only propext, Classical.choice and Quot.sound. Earlier new lemmas include `OMA.pair_degree_cover_nine`, `OMA.tight_vertices_cover_ten`, `OMA.degree_and_triple_cover_ten`, `OMA.card_bad_deletions_le`, `OMA.avoid_three_inclusion_exclusion`, `OMA.card_cover_ne_of_deletions`, `OMA.cliqueExtremalNumber_thirty_nine_le`, `OMA.turanDensity_le_of_thirty_nine`, and `OMA.tetrahedron_cubic_le_twenty_nine`.
- Remaining gap: `OMA.turan_upper_bound` for `0 < ε ≤ 7/360`, equivalently `54 * ex₃(n,K₄³) ≤ 5 * n³` for all `n ≥ 30`. The required checker rejects the partial at lint for the sole open proof.
- Dead ends: the greedy tight-deletion proof ties at 26 vertices. The five-vertex certificate optimization currently reaches about 0.573, still above 5/9. Direct decide over all Boolean functions was killed during reduction. A precomputed dot-product table verified in the kernel, a bit encoding, and 32 chunks of 32 masks compiled.
- Verification details: the certificate uses `decide +kernel` on a prechecked integer dot-product table, so no native reduction axiom enters the proofs. Direct Lean compilation of the active proof succeeded with only its single remaining open proof. A float-only six-vertex experiment with four rooted labels produced about 0.56746, still above 5/9. Its enumeration and rounding are outside the active proof. Attempts at an unrolled reflected evaluator used more memory than the retained checker.
- Exact obstruction to pushing this same five-label method to 5/9: `erdos500_flag_dual.py` verifies by rational LDL pivots a nonnegative mixture of labelled five-vertex graphs with density `565455137/1000000000` and positive semidefinite rooted flag matrices. This finite mixture is a dual certificate for the relaxation, not a hypergraph counterexample. A successful certificate needs additional constraints or a different argument.
- Final audit compiled the active file with the sole open proof warning. The new upper bounds and 29-vertex prefix use only propext, Classical.choice and Quot.sound. The prescribed checker verdict is `rejected`, reason `lint: forbidden: 'sorry'`.

## Leg 2: codex  (15:43, 0 min, ended: exit)
File stats: proved lemmas 83, sorries 1, lines 2266 (was 83 / 1 / 2266)
(the model wrote no notes; see partial_codex.lean)
