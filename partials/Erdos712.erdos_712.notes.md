# Relay notes for Erdos712.erdos_712 (prize: $500)


## Leg 1: opus  (08:14, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 2, lines 16 (was 0 / 2 / 16)
# notes_opus (leg 1) Erdos712.erdos_712
Approach: fidelity/loophole audit only.
- cliqueExtremalNumber n r k = max card of H subset powersetCard r (Fin n) with no S, card S = k, S.powersetCard r subset H. Faithful ex_r(n,K_k^r).
- Target needs an explicit closed-form value pi(K_k^r) for ALL k>r>2: this is the open hypergraph Turan density problem (even r=3,k=4 = Turan tetrahedron conjecture 5/9 is open; Razborov flag bounds only 0.5617). No loophole: k>r>2 rules out degenerate cases, the answer is over R with explicit value required.
Compiled: nothing new (file left as the template skeleton with sorry).
Remaining gap: the entire open problem.
Dead ends: none worth trying; FAILED fast pass. Limit existence (variant limit_exists) is a separate warm-up target, not this one.

## Leg 2: codex  (08:19, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 2, lines 16 (was 0 / 2 / 16)
# Leg 2, Erdos712.erdos_712
Approach: preserve the supplied parent statement. Derive a finite upper bound for the simplex case k = r + 1 by bounding the sum of face codegrees around each edge and applying Cauchy–Schwarz. This gives an independent bound on any candidate parent answer.
Compiled in e712_simplex.lean: exists_erase_eq, sum_faces_eq_sum_erase, codegree_eq_sum_extensions, exists_missing_replacement, sum_codegrees_on_edge_le, sum_codegrees_mul. Working on the Cauchy–Schwarz step.
Remaining gap: no explicit general density is known, and the parent includes the open tetrahedron case r = 3, k = 4. The limit-existence variant leaves this gap.
Dead ends: no way to use limit existence as an explicit answer under the value requirement.

## Leg 3: fable  (08:21, 2 min, ended: exit)
File stats: proved lemmas 0, sorries 2, lines 19 (was 0 / 2 / 16)
# notes_fable (leg 3) Erdos712.erdos_712

Verdict: cannot be done. This is the open hypergraph Turan density problem. Stopped early on purpose.

## Approach
Third independent audit of the statement, then a decision to stop.
- Read FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean lines 112 and 185-189.
  extremalNumber n r P = sup of card over P-families inside powersetCard r (univ : Finset (Fin n)).
  ContainsCompleteHypergraph H r k = exists S, S.card = k and S.powersetCard r subset H.
  So cliqueExtremalNumber n r k is exactly ex_r(n, K_k^r). Faithful.
- Target: for ALL k > r > 2 the ratio ex/choose n r tends to OMA.answer k r, with OMA.answer an explicit value.
  That value is pi(K_k^r). It is not known for any single pair k > r > 2.
- No loophole: hypotheses 2 < r < k are satisfiable, no vacuous case, no degenerate division
  (choose n r > 0 for n >= r), the limit is the real Turan density in [0,1).

## What compiled
- proofs/Erdos712.erdos_712.lean: the template def had no type and gave 2 elaboration errors
  (Failed to infer type of definition, Unknown identifier OMA.answer). Now
  `noncomputable def OMA.answer : ℕ → ℕ → ℝ := sorry` and the file elaborates with 0 errors
  (direct lake env lean, 5 s). Two sorries remain: the answer value and the proof. No new lemmas.
- Nothing else. I did not add filler lemmas: no lemma moves the target while the value is unknown.

## Exact remaining gap
Everything. Two things are missing and both are open research:
1. an explicit closed form for pi(K_k^r), all k > r > 2 (needed just to WRITE OMA.answer);
2. the matching upper bound proof (lower bounds come from constructions).

## Dead ends (do not repeat)
- Guessing the answer. r = 3: Turan conjecture 1 - (2/(k-1))^2, open even for k = 4 (5/9; best upper
  bound about 0.5617 by flag algebras). r >= 4: no agreed conjecture. The Sidorenko formula
  1 - ((r-1)/(k-1))^(r-1) is NOT the truth in general: for (k,r) = (5,4) it gives 37/64 but the
  Giraud construction gives 11/16. So any closed form for all (k,r) is very likely false.
- Defining OMA.answer as the limit, or as the infimum of the ratio (the ratio is non-increasing,
  Katona-Nemetz-Simonovits), or by choice from limit_exists. The template forbids it
  (no choice / infimum / supremum of the quantity asked for; a person checks the answer).
  It would only restate the question.
- Leg 2 simplex upper bound (scratch e712_simplex.lean, k = r+1, codegree + Cauchy-Schwarz): gives
  de Caen type bounds only, never the exact value.
- Provable neighbours are separate targets and already merged upstream by others:
  variants.limit_exists, variants.graph_case, variants.graph_case_div_sq.

## Advice for the next leg
Report FAILED at once. Do not spend the time budget here.

## Leg 1: opus  (09:39, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 2, lines 19 (was 0 / 2 / 19)
# notes_opus (relay leg 1, new round) Erdos712.erdos_712
Approach: re-read prior notes (3 legs + memory audit). Open hypergraph Turan density problem pi(K_k^r) for ALL k>r>2.
Compiled: file unchanged (typed skeleton, 0 errors, 2 sorries: OMA.answer value and proof). No new lemmas.
Exact remaining gap: explicit closed form for pi(K_k^r) (unknown even for (4,3), Turan tetrahedron 5/9) plus matching upper bound.
Dead ends: guessing answer (Sidorenko formula false for (5,4) by Giraud 11/16), defining answer as limit/inf (forbidden), simplex codegree bounds (only de Caen type).
Stopped at once: FAILED fast pass, per earlier audits.

## Leg 2: codex  (09:44, 4 min, ended: exit)
File stats: proved lemmas 22, sorries 2, lines 302 (was 0 / 2 / 19)
# Codex relay notes for Erdos712.erdos_712

Approach: Turán’s balanced three-part tetrahedron-free construction on `Fin 3 × Fin m`. The edges are rainbow triples and triples with multiplicities 2 and 1 in cyclically adjacent colors. Counting gives a normalized bound of 5/9 at every positive multiple of three, and hence for any limiting tetrahedron density.
Compiled in the parent file: `cliqueFree`, `edge_injective`, `family_card_lower`, `Erdos712Turan.tetrahedron_extremal_lower`, `Erdos712Turan.tetrahedron_ratio_lower`, and `Erdos712Turan.tetrahedron_density_lower`. The three public lemmas depend only on propext, Classical.choice, and Quot.sound. The first import and OMA.solution signature are unchanged.
Checker verdict: rejected, lint: forbidden: 'sorry'. The only two placeholders are the existing OMA.answer value and OMA.solution body.
Exact gap: even for `(k,r) = (4,3)`, proving that the limiting density is at most 5/9 is open. The parent also needs explicit values and their proofs for all `k > r > 2`.
Dead ends from earlier legs: defining the answer as a limit or infimum violates the explicit-value requirement. Limit existence and the simplex codegree upper bound leave the exact value unresolved.

## Leg 1: gemini  (10:24, 1 min, ended: exit)
File stats: proved lemmas 22, sorries 2, lines 302 (was 22 / 2 / 302)
# notes_gemini (relay leg 1) Erdos712.erdos_712

Approach: Independent verification of the upstream statement (`FormalConjectures/ErdosProblems/712.lean`), `Hypergraph.cliqueExtremalNumber` (`FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean`), and `tools/lint.py` / `tools/check.sh` rules, plus review of the existing 302-line partial proof in `proofs/Erdos712.erdos_712.lean`.

What compiled:
- Left `proofs/Erdos712.erdos_712.lean` intact with all 22 previously compiled lemmas from `Erdos712Turan` (`tetrahedron_extremal_lower`, `tetrahedron_ratio_lower`, `tetrahedron_density_lower`, and private helpers). No new filler lemmas added.

Exact remaining gap:
- `Erdos712.erdos_712` is a faithful formalization of the open hypergraph Turan density problem: determining an explicit function `OMA.answer : Nat -> Nat -> Real` (no choice/inf/sup/limit of the target quantity allowed by `tools/lint.py` and human review) and proving `Tendsto (fun n => ex_r(n, K_k^r) / choose n r) atTop (nhds (OMA.answer k r))` for ALL `k > r > 2`.
- Even for the single case `(k, r) = (4, 3)` (Turan tetrahedron conjecture, 5/9), the matching upper bound is famously open since 1941 (best known flag-algebra upper bounds remain strictly above 5/9). For `r >= 4`, no general closed-form conjecture is even agreed upon (e.g., Sidorenko formula gives 37/64 for `(5, 4)`, whereas Giraud gives 11/16).
- No loophole or misformalization exists (`2 < r < k` excludes degenerate cases; `Hypergraph.cliqueExtremalNumber` matches `ex_r(n, K_k^r)` faithfully; `OMA.disproof` is disallowed for value problems and the limit exists in `[0, 1]` by Katona-Nemetz-Simonovits).

Dead ends:
- Defining `OMA.answer` via `sInf`, `limUnder`, `Classical.choose`, or `limit_exists` (explicitly blocked by `tools/lint.py` and the value-problem specification).
- Guessing a general formula (no known formula matches even known constructions for `r >= 4`).
- Adding partial lower/upper bounds (e.g., de Caen / Cauchy-Schwarz or generalized Turan constructions) cannot resolve the missing explicit value or matching upper bound.

## Leg 2: codex  (10:29, 4 min, ended: exit)
File stats: proved lemmas 31, sorries 2, lines 531 (was 22 / 2 / 302)
# Codex relay notes for Erdos712.erdos_712

Approach: preserve Turán’s three-part lower bound. Blow up each vertex into an independent class of size m and lift every edge in m^r ways. The scaled extremal number uses n^r / r! as denominator and has the same limit. The blow-up gives an exact finite test for an upper bound on that limit.

Compiled: extremal_blowup_lower, density_le_iff_finite, tetrahedron_density_eq_iff_finite, and their helpers. All three new public lemmas use only propext, Classical.choice, and Quot.sound. The existing tetrahedron_extremal_lower, tetrahedron_ratio_lower, and tetrahedron_density_lower are preserved. The first import and OMA.solution statement are unchanged.

Exact gap: prove 54 * cliqueExtremalNumber n 3 4 ≤ 5 * n^3 for all n > 0 to settle the tetrahedron case. A finite violation would refute the 5/9 conjecture by blow-up. The parent still requires explicit densities with proofs for all k > r > 2.

Recorded dead ends: defining the value by a limit or infimum violates the value requirement. Limit existence and the simplex codegree estimate do not give the matching bound.

Checker: rejected at lint with forbidden: 'sorry'. The remaining placeholders are the original OMA.answer value and OMA.solution body.
