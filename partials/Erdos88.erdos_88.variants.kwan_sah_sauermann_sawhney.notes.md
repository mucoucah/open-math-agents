# Relay notes for Erdos88.erdos_88.variants.kwan_sah_sauermann_sawhney (prize: $100)


## Leg 1: grok  (00:13, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (00:15, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 49 (was 0 / 1 / 10)
# Erdos88 kwan_sah_sauermann_sawhney - opus leg 2
Approach: split on eta. Target is faithful KSSS22 Thm 1.1 (anticoncentration in Ramsey graphs), no loophole:
for large C the hypotheses are satisfiable (random graphs), and for eta in (0,1) this is the full research theorem.
Compiled (lake env lean, only one sorry): OMA.E88.induce_empty_ncard, OMA.E88.large_eta (eta >= 1 gives m = 0, S = empty),
OMA.solution glue.
Remaining gap: ONE sorry OMA.E88.ksss_main (0 < eta < 1) = the whole KSSS22 theorem. Infeasible in a session.
(C <= 1/2 would be vacuous by Erdos-Szekeres Ramsey, but that does not close large C.)
Dead ends: no loophole in cliqueNum/indepNum/logb/atTop; the erdos_mckay proof (log^2 n range) does not reach (1-eta)e(G).

## Leg 3: codex  (00:26, 10 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 556 (was 3 / 1 / 49)
# Codex leg 3, Erdos88 KSSS variant

Approach: keep the eta ≥ 1 case and close C ≤ 1/2 by neighborhood recursion. For small targets, recursively add a vertex adjacent to all or none of the later vertices. A successful split costs q in pool size plus one. An unsuccessful split costs q/(q−1) and decreases the clique or independence cap, so q^l (q/(q−1))^(a+b) buys every count through choose(l,2). For larger targets, shrink to a minimal induced host with at least 2m edges. The degree sum and minimality bound its edge count by 3m. If m^k ≥ n, its order t satisfies n ≤ t^(2k), so relabel with Ramsey constant 2kC and eta lowered to min(eta,1/2).

Compiled: `induce_empty_ncard`, `large_eta`, `card_add_one_le_two_pow`, `small_C`, `edge_ncard_induce_map`, `cliqueNum_le_of_embedding`, `indepNum_le_of_embedding`, `edge_ncard_le_square`, `edge_ncard_erase`, `exists_induced_edge_ncard_between`, `edge_ncard_insert`, `exists_edges_of_peeling`, `thresholdOrder`, `exists_edges_le_threshold`, `ksss_core`, `ksss_main`, and `OMA.solution` with the one gap below. The first import and solution statement are unchanged.

Exact gap: `ksss_core_above_threshold`. For C > 1/2 and 0 < eta < 1, find k ≥ 1 and prove eventual exact realization for choose(thresholdOrder C n,2) < m ≤ (1−eta)e(G) when m^k < n or e(G) ≤ 3m. Here thresholdOrder C n = floor(log n / (2 log(1 + 4C/log 2))). This leaves the low-density sampling range above the peeling bound and the constant-fraction range. Lean elaborates the file. The prescribed checker rejects at lint solely for the existing `sorry` in that lemma.

Dead ends: the logarithmic-squared guarantee alone cannot reach the constant-fraction range. Shrinking loses control of the Ramsey constant when m is subpolynomial in n, so it cannot close the lower range above the cutoff. The imported upstream statement is unavailable as a proof and was never invoked.

## Leg 4: fable  (00:28, 2 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 556 (was 16 / 1 / 556)
# Fable leg 4, Erdos88 KSSS variant

Approach: none new. I audited the statement and the leg 3 file and judged the remaining gap infeasible in a session, so I stopped early and left the proof file untouched.

Compile status (direct `lake env lean`, 6 s, this leg): exit 0, one `declaration uses sorry` warning at line 454 (`ksss_core_above_threshold`), no errors. check.sh was not run: it rejects at lint on the sorry.

Compiled (inherited from leg 3, file not edited this leg): `induce_empty_ncard`, `large_eta`, `card_add_one_le_two_pow`, `small_C`, `edge_ncard_induce_map`, `cliqueNum_le_of_embedding`, `indepNum_le_of_embedding`, `edge_ncard_le_square`, `edge_ncard_erase`, `exists_induced_edge_ncard_between`, `edge_ncard_insert`, `exists_edges_of_peeling`, `thresholdOrder`, `exists_edges_le_threshold`, `ksss_core`, `ksss_main`, `OMA.solution`.

Exact remaining gap: ONE sorry, `OMA.E88.ksss_core_above_threshold` (C > 1/2, 0 < eta < 1): pick k >= 1, then eventually in n, for every m with choose(thresholdOrder C n, 2) < m <= (1-eta) e(G), find S with exactly m induced edges, in two regimes:
1. `m ^ k < n` (m between about c log^2 n and n^(1/k)). This is the Alon-Krivelevich-Sudakov 2003 theorem (Induced subgraphs of prescribed size: every y <= n^delta(C) is realised in a C-Ramsey graph). About 15 journal pages, nothing of it in Mathlib.
2. `e(G) <= 3 * m` (m a constant fraction of e(G)). This is the heart of KSSS22: the local limit / anticoncentration Theorem 1.2 for e(G[U]) with U a random vertex subset (point probabilities of order n^(-3/2) around the mean), about 80 pages of Fourier-analytic and small-ball arguments. Nothing of it in Mathlib.

Why no loophole (re-audited): for C > 2 random graphs satisfy both hypotheses for large n, so the statement is not vacuous; cliqueNum / indepNum on Fin n are the honest finite values; logb 2 and atTop are used faithfully; m ranges over all naturals up to (1-eta) e(G). C <= 1/2 is vacuous and already proved (small_C).

Dead ends (do not repeat):
- Threshold-graph peeling (all-or-none neighbourhood recursion) tops out at about log^2 n edges; it cannot reach n^delta, let alone a constant fraction.
- The shrink-to-a-minimal-host step only helps when m >= n^(1/k); for smaller m the host has order far below any fixed power of n and the Ramsey constant blows up.
- Weakening or splitting the sorry further is cosmetic: both regimes are published research theorems (AKS03 and KSSS22 Thm 1.2), not session-sized lemmas.

Advice for the next leg: do not spend time here unless you intend a multi-day formalisation. If any piece is attempted, regime 1 (AKS03) is the only one with an elementary combinatorial proof.
