# Relay notes for Erdos19.erdos_19.variants.large_n (prize: $500)


## Leg 1: grok  (23:20, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (23:21, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 26 (was 0 / 1 / 10)
# Erdos19.erdos_19.variants.large_n  (leg 2, opus)
Approach: target = full KKKMO21 theorem (Erdos-Faber-Lovasz for all large n). Statement matches the
conjecture: n cliques of size exactly n, pairwise sharing at most 1 vertex, covering V. Padding
shows size exactly n is no weaker than size at most n. No loophole: no vacuity, V is effectively
finite, and the eventual quantifier is genuine.
Compiled (lake env lean, one sorry): OMA19.chrom_eq_of_colorable (Colorable n -> chi = n, uses
upstream le_chromaticNumber); OMA.solution = filter_upwards glue from OMA19.kkkmo_colorable.
Exact remaining gap: OMA19.kkkmo_colorable : eventually n, every EFLConfig V n graph is Colorable n.
That is the whole KKKMO21 absorption/nibble proof (Ann. Math. 2023), not formalisable in a session.
Upstream colorable_of_sharedColoring reduces it further to colouring the shared vertices with
n colours so that shared vertices in a common clique get distinct colours (chromatic index of the
linear hypergraph, restricted to shared vertices), which is still the full theorem.
Dead ends: greedy colouring only gives about 2n; Kahn nibble (1+eps)n is itself unformalised
(see the kahn variant); le_three-style injective colouring needs n choose 2 <= n, so only n <= 3.
Verdict: FAILED fast pass. check.sh rejects at lint (sorry) before compiling.

## Leg 3: codex  (23:29, 8 min, ended: stalled)
File stats: proved lemmas 11, sorries 1, lines 272 (was 2 / 1 / 26)
# Erdos19 large n, leg 3

Approach: dualize shared vertices to edges on Fin n and adjoin every uncovered two-element edge to obtain a pairwise balanced design.
Compiled: OMA19.chrom_eq_of_colorable, OMA19.HasEdgeColoring.mono, OMA19.exists_pairwiseBalanced_superset, OMA19.colorable_of_pairwiseBalanced, OMA19.kkkmo_colorable, and OMA.solution. The last two use the one remaining placeholder.
Exact remaining gap: OMA19.pairwiseBalanced_edgeColorable, eventual proper edge-colorability with n colors for pairwise balanced designs on Fin n. This is the large-order KKKMO theorem in the complete linear hypergraph formulation.
Dead ends from previous legs: unrestricted greedy bound, Kahn asymptotic bound, and globally injective colors on the shared vertices.

## Site hints (2026-11-26)

https://www.erdosproblems.com/19 (YAML: decidable). This variant is Kang–Kelly–Kühn–Methuku–Osthus [KKKMO21], *A proof of the Erdős–Faber–Lovász conjecture*, Ann. of Math. 2023, https://arxiv.org/abs/2101.04698 : EFL holds for all sufficiently large n. Follow that paper. Write-up: /workspace/left-to-solve/research/erdosproblems.md

## Leg 4: fable  (23:31, 2 min, ended: exit)
File stats: proved lemmas 11, sorries 1, lines 272 (was 11 / 1 / 272)
# Erdos19.erdos_19.variants.large_n  (leg 4, fable)

Verdict: cannot be done in a session. STALLED on the full KKKMO21 theorem. Recommend ending the relay.

Approach (unchanged from leg 3): shared vertices dualise to edges of a linear hypergraph on Fin n,
uncovered pairs are adjoined to get a pairwise balanced design (PBD), and an n-edge-colouring of the
PBD is pulled back through the upstream colorable_of_sharedColoring.

Statement audit (re-done independently): faithful, no loophole. EFLConfig V n is inhabited for every n
(n disjoint cliques), V is forced finite by cover, sizes exactly n are no weaker than sizes at most n
(padding with private vertices, proved as OMA19.edgeColorable_of_configs), and the eventual quantifier
is genuine. chromaticNumber = n needs a real n-colouring for every configuration.

Status checked this leg (proof file NOT modified, 272 lines):
- bash .oma/scratch/lean_codex.sh proofs/Erdos19.erdos_19.variants.large_n.lean  (about 5 s): exit 0,
  no errors, exactly one warning: line 256 declaration uses sorry (pairwiseBalanced_edgeColorable).
- tools/check.sh: verdict rejected, reason lint: forbidden: sorry (lint runs before compilation).

What compiles:
OMA19.chrom_eq_of_colorable, IsPairwiseBalanced.linear, mem_incident, IsPairwiseBalanced.sum_incident,
IsPairwiseBalanced.card_incident_le, HasEdgeColoring.mono, exists_pairwiseBalanced_superset,
colorable_of_pairwiseBalanced, edgeColorable_of_configs, configs_colorable_iff_pairwiseBalanced,
kkkmo_colorable (uses the sorry), OMA.solution (uses the sorry).

Exact remaining gap: OMA19.pairwiseBalanced_edgeColorable :
  eventually in n, every IsPairwiseBalanced K on Fin n has HasEdgeColoring K (n colours).
By configs_colorable_iff_pairwiseBalanced this sorry is EQUIVALENT to the target for each n, so the
reformulation phase is finished: no further restatement can shrink the gap. What is left is the whole
KKKMO21 proof (Ann. of Math. 2023, about 100 pages: Kahn-type nibble, Pippenger-Spencer, absorption
via reservoirs, separate treatment of large edges and of the near-extremal cases close to projective
planes and near-pencils). None of that machinery is in Mathlib.

Dead ends (do not repeat):
- greedy by decreasing edge size: an edge of size k meets at most k(n-k)/(k-1) earlier edges, which is
  below n only for k above sqrt n; small edges need about 2n colours.
- Kahn (1+eps)n: weaker than the target and itself unformalised (see the kahn variant).
- injective colouring of all edges: needs at most n edges; de Bruijn-Erdos says a nontrivial PBD has
  at least n edges, with equality only for projective planes and near-pencils, so this only covers the
  extremal designs.
- n at most 3 style counting (n choose 2 at most n) says nothing about large n.
- more reformulations (hypergraph, PBD, shared-vertex colouring): all equivalent to the target.

If someone ever attacks it for real: the first session-sized true lemma would be the large-edge greedy
step (edges of size above sqrt n can be properly coloured with n colours, by decreasing size), but it
does not combine with anything available, so it was not added.
