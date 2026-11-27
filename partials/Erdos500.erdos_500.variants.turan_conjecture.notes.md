# Relay notes for Erdos500.erdos_500.variants.turan_conjecture (prize: $500)


## Leg 1: grok  (04:23, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_grok — Erdos500.erdos_500.variants.turan_conjecture

## Approach
Target is exactly
`(fun n => (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ)) ~[atTop] fun n => 5/9 * (n.choose 3 : ℝ)`.
`~[atTop]` is `Asymptotics.IsEquivalent`: equivalent (since `5/9 * C(n,3) ≠ 0` for large n, via `isEquivalent_iff_tendsto_one`) to
`Tendsto (fun n => (ex n : ℝ) / (n.choose 3 : ℝ)) atTop (𝓝 (5/9))`.
That is Turán's tetrahedron conjecture `π(K_4^3) = 5/9`.

API (printed):
- `Hypergraph.extremalNumber n r P = ((powersetCard r univ).powerset.filter P).sup card`
- `cliqueExtremalNumber n r k = extremalNumber n r (fun H => ¬ H.ContainsCompleteHypergraph r k)`
- `Finset.ContainsCompleteHypergraph H r k = ∃ S, S.card = k ∧ powersetCard r S ⊆ H`
Defs live in `FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite`.

## What compiled
No new lemmas. File left as the required `theorem OMA.solution : type_of% @Erdos500.erdos_500.variants.turan_conjecture := by sorry`. Did not touch the import or the OMA.solution statement.

## Exact remaining gap
Need `limsup ex_3(n,K_4^3) / C(n,3) ≤ 5/9`. The matching liminf `≥ 5/9` is the balanced 3-partite Turán construction (rainbow triples plus cyclic doubletons) and is already a separate solved problem (`Erdos500.erdos_500.variants.lower_bound`, solved-examples, ~450 lines). Do not import the upstream `sorry` theorems (`erdos_500`, `lower_bound`, `upper_bound`, `asymptotic`); the axiom check rejects them. Reproving the lower bound here does not close `~[atTop]`.

Known upper bounds are strictly above 5/9 ≈ 0.555...:
- Razborov flag algebras suggest ≤ 0.561666 (upstream `upper_bound`, not a theorem in this snapshot).
- Baber: `π ≤ 0.5615`.
- Jeong–Park–Im–Lee–Yang arXiv:2609.27495 (cited in 500.lean): `π(K_4^3) < 0.557789`, with an external Lean flag-algebra proof. Still above 5/9, so it does not imply the equivalence.

Limit existence of the ratio (KNS averaging) is Erdős 712 `limit_exists` (solved-examples) and also does not pin the value at 5/9.

## Dead ends
- Proving or refuting the statement in this session: it is a famous open problem (open on erdosproblems.com/500; formal-conjectures category research open). No finite check refutes the asymptotic. No construction beats 5/9. Do not re-search small-n counterexamples or try to finish flag algebras.
- Using upstream `Erdos500.erdos_500.variants.lower_bound` / `upper_bound` (they are `sorry`).
- Copying the Kosters lower-bound file verbatim (other contestant; also insufficient for `~`).

## If a later leg continues
Only a new mathematical upper bound `π ≤ 5/9` (or a construction with density bounded above 5/9) can finish this. Neither is in Mathlib or this snapshot. A useful compiled reduction, if wanted, is the iff with `Tendsto (... / choose 3) atTop (𝓝 (5/9))` via `Asymptotics.isEquivalent_iff_tendsto_one`, then the open half is `limsup ≤ 5/9`.

## Leg 2: opus  (04:24, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 35 (was 0 / 1 / 10)
# notes_opus — Erdos500 turan_conjecture (leg 2)
## Approach
Open problem (Turan tetrahedron pi(K_4^3)=5/9). Reduced target to density form.
## Compiled (lake env lean, only warning = the one sorry)
- OMA.isEquivalent_of_ratio (f) : Tendsto (f n / C(n,3)) atTop (nhds (5/9)) -> f ~[atTop] 5/9*C(n,3)  (fully proved)
- OMA.solution := OMA.isEquivalent_of_ratio _ OMA.turan_density
## Exact remaining gap
ONE sorry: OMA.turan_density : Tendsto (cliqueExtremalNumber n 3 4 / C(n,3)) atTop (nhds (5/9)).
This is exactly the open Turan conjecture (lower half liminf>=5/9 is Kosters' construction in related files; upper half limsup<=5/9 is open, best known ~0.5578).
## Dead ends
Same as leg 1: no loophole, statement faithful, upper bound open. Do not spend more time.

## Leg 4: fable  (04:29, 5 min, ended: stalled)
File stats: proved lemmas 2, sorries 1, lines 35 (was 2 / 1 / 35)
(the model wrote no notes; see partial_fable.lean)

## Leg 1: gemini  (11:07, 9 min, ended: gemini_budget)
File stats: proved lemmas 22, sorries 1, lines 820 (was 2 / 1 / 35)
(the model wrote no notes; see partial_gemini.lean)

## Leg 2: codex  (11:13, 6 min, ended: exit)
File stats: proved lemmas 38, sorries 1, lines 1191 (was 22 / 1 / 820)
# Codex relay — Erdős 500 Turán variant

## Approach
Count missing triples that survive each vertex deletion. A six-vertex cover needs six triples. At equality each vertex lies in three triples and each pair lies in at most two. An eleven-triple cover of seven vertices would have either one vertex of degree three or two of degree four, with all others of degree five. Deleting degree-five vertices and using the six-vertex constraints rules out both cases. Iterate the inherited KNS inequality with integer division from the seven-vertex bound.

## What compiled
`OMA.card_cover_five`, `OMA.card_cover_six`, `OMA.pair_card_cover_six`, `OMA.card_cover_seven`, `OMA.cliqueExtremalNumber_six_le`, `OMA.cliqueExtremalNumber_seven_le`, `OMA.cliqueExtremalNumber_le_cap`, `OMA.cliqueExtremalNumber_nine` (exactly 54), `OMA.turanDensity_le_twenty_two_thirty_fifths` (for n ≥ 21), and `OMA.exists_turanDensity_limit_le_twenty_two_thirty_fifths`. Fixed inherited concrete binomial calculations in `OMA.cliqueExtremalNumber_five_le` and `OMA.turanDensity_le_seven_tenths`. The complete file elaborates with one warning, and the new public bounds and limit theorem use only the permitted axioms. The prescribed checker reports `rejected`, reason `lint: forbidden: 'sorry'`.

## Exact remaining gap
`OMA.turan_upper_bound` asks for each ε > 0 for some n ≥ 3 with density ≤ 5/9 + ε. Equivalently, prove the limit is ≤ 5/9. The certified interval is [5/9, 22/35].

## Dead ends
Known upper bounds above 5/9, including the deletion recurrence here, leave the matching bound open. Upstream placeholder theorems fail the axiom audit. For the installed import, use `by decide` on closed `Nat.choose` equalities instead of `norm_num`.
