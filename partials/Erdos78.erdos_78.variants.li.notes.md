# Relay notes for Erdos78.erdos_78.variants.li (prize: $100)


## Leg 1: grok  (00:02, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (00:03, 1 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_opus: Erdos78.erdos_78.variants.li (leg 2)
Approach: statement audit only.
Statement: exists C>0, adj : List Bool x N x N -> Bool, IsPolyTime adj (TM2ComputableInPolyTime under
BitstringEncoding, FormalConjecturesForMathlib/Computability/Complexity.lean) and eventually
explicitGraph adj n has no clique / independent set of size ceil((log n)^C).
Faithful, no loophole: every n-vertex graph has a homogeneous set of size about (1/2) log2 n, so
trivial graphs fail; any C works only for a genuine polylog Ramsey family (Li 2023 / CZ two-source
extractors). Brute force in poly(n) time gives only k ~ sqrt(log n) vertex Ramsey graphs; lexicographic
powers then give n^{o(1)}, not polylog. On top, IsPolyTime needs an explicit TM2 machine plus a
runtime bound: no Mathlib library support beyond id.
Compiled: nothing new (file is the sorry skeleton).
Gap: the whole theorem (Li23b) plus a Turing-machine polytime proof.
Dead ends: trivial graphs, choosing large C, brute-force + graph products (n^{o(1)} only).
Verdict: FAILED fast pass.

## Leg 3: codex  (00:09, 5 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 333 (was 0 / 1 / 10)
# Erdős 78 li, leg 3
Approach: apply a one-bit two-source extractor to the sorted pair of fixed-width little-endian vertex labels (width n.log2 + 1). Each color occurs on every sufficiently large rectangle. Split a putative homogeneous set into two consecutive k-vertex blocks, then absorb the factor 2 and the width conversion into one extra power of log n.
Compiled in pinned Lean: lt_two_pow_width, bits_injective_on, exists_separated_blocks, orderedAdj_adj_iff, noHomogeneousSet_of_disperses, tendsto_width_atTop, eventually_width_pow_le, from_disperser. Also encodeNat_eq_bits, bits_eq_getD_encodeNat, encode_query, disperses_of_bias_bound, eventually_disperses_of_flat_extractor.
Exact gap: construct uniform color d and K with eventual bias strictly below 1/2 for independent flat sources of min-entropy at least K * log d, and prove IsPolyTime (orderedAdj color) in the canonical TM2 encoding. This is the sole sorry. Direct proof of dispersion at d^D also suffices via from_disperser. encode_query expands the input blocks and bits_eq_getD_encodeNat identifies extractor bits with zero-padded binary tape contents.
Dead ends inherited: trivial graphs, arbitrary fixed exponent without a construction, brute force plus graph products. No local preformalized extractor located. Related little_o_sqrt H1 is a finite-state parser, useful as a design hint for the input tape only. Its digit scanner cannot implement the extractor.
Runtime bridge compiled: two_pow_width_le, length_encode_query, orderedAdj_isPolyTime_of_runtime. The last lemma packages a TM2 run bounded by C * (2^width + len(u.bits) + len(v.bits) + 1)^E into IsPolyTime. The unary size input permits single-exponential work in the extractor word width.
Final verification: pinned Lean elaborates the full file with one sorry warning. Axiom audits of the graph, flat-source, and runtime transfers report only propext, Classical.choice, and Quot.sound. CI verdict rejected at lint for the single sorry.

## Leg 4: fable  (00:13, 4 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 333 (was 16 / 1 / 333)
# notes_fable: Erdos78.erdos_78.variants.li (leg 4)

Approach: kept the leg 3 (codex) file unchanged in structure. Graph = one-bit two-source
disperser applied to the sorted pair of fixed-width vertex labels (width n.log2 + 1).

Compiled (inherited, re-verified this leg, see bottom): encodeNat_eq_bits, bits_eq_getD_encodeNat,
encode_query, lt_two_pow_width, two_pow_width_le, length_encode_query,
orderedAdj_isPolyTime_of_runtime, bits_injective_on, exists_separated_blocks, orderedAdj_adj_iff,
noHomogeneousSet_of_disperses, tendsto_width_atTop, eventually_width_pow_le, from_disperser,
disperses_of_bias_bound, eventually_disperses_of_flat_extractor.

Exact remaining gap (the single sorry inside OMA.solution):
  exists K and color : (d : Nat) -> (Fin d -> Bool) -> (Fin d -> Bool) -> Bool with
  (a) IsPolyTime (orderedAdj color)   [explicit TM2 machine, runtime may be 2^(O(d)) per query]
  (b) eventually in d: every pair of sets A, B of d-bit strings with card >= d^K gets both colours.
(b) is a two-source disperser for min-entropy O(log d) on d-bit sources = Li 2023 (arXiv 2303.06802),
the current state of the art. Note bias < 1/2 is the same thing as the disperser property, so the
extractor wording of the sorry is not stronger than needed.

Why this cannot be closed in a session (new analysis, do not redo):
- Rectangle size d^K = polylog N (N = 2^d vertices) is exactly the O(log d) entropy regime.
  Chattopadhyay-Zuckerman / Cohen 2016 only give entropy polylog d, i.e. the cohen variant
  2^((log log N)^C). So even those do not suffice here; one needs Li 2023 in full.
- Weak explicitness (time poly N) does not help: any direct derandomization has N^K bad events
  (K = polylog N), not poly N. Conditional expectations, small-bias spaces, t-wise independence
  all need sample space or time about N^K. Naor 1992 (small-bias + products) reaches only
  2^(O(sqrt(log N))). Brute force base graph + lexicographic powers gives N^(o(1)).
- Poly-time checkable certificates (codegree or spectral quasirandomness) stop at about sqrt N.
- Free choice of C does not help: (log n)^C < n eventually for every fixed C, so the clique-free
  conditions are never vacuous.
- On top of (b), part (a) needs a hand-built TM2 for finite-field arithmetic; nothing in Mathlib
  or the related files (little_o_sqrt H1 is only a finite-state parser).

Dead ends (all legs): trivial graphs, large C, brute force + graph products, derandomization via
conditional expectations / small bias / limited independence, quasirandomness certificates,
looking for a loophole in IsPolyTime or the encoding (input length is 6n + 2|u| + |v| + 2, honest).

Verdict: STALLED. Blocker = Li 2023 two-source disperser (b) plus its TM2 polytime proof (a).

Verification this leg (file left byte-identical to the leg 3 version, nothing added or removed):
- direct compile (cd formal-conjectures checkout; lake env lean <abs path>): 6 seconds, zero errors,
  one warning = declaration uses sorry at line 326 (OMA.solution).
- tools/check.sh: verdict rejected, reason lint: forbidden sorry. No double-quote characters.
Advice to the next leg: do not spend time here unless a formalized two-source disperser for
O(log d) min-entropy AND a TM2 polytime library exist somewhere in the proofs dirs; neither does.
