# Relay notes for Erdos78.erdos_78.variants.li_strongly_explicit (prize: $100)


## Leg 1: grok  (00:06, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (00:07, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_opus: Erdos78.erdos_78.variants.li_strongly_explicit (leg 2)
Approach: audited the statement for a loophole; there is none.
- Target: exists C>0, adj : N x N x N -> Bool with IsPolyTime adj (n given in binary,
  so time poly(log n) per query), eventually NoHomogeneousSet (stronglyExplicitGraph adj n) ceil((log n)^C).
- Faithful: every graph on n vertices has a homogeneous set of size about (1/2) log2 n, so choosing C
  does not help; you need a real polylog Ramsey family (Li 2023 two-source extractors), which is
  strictly STRONGER than the weakly explicit variant li (already FAILED, see wt18 notes).
- Brute force on sqrt(log n) vertices + lexicographic powers gives only n^{o(1)} homogeneous sets.
- IsPolyTime needs an explicit TM2ComputableInPolyTime machine; only toy TM machinery exists in the
  little_o_sqrt R1.H1/H2 files.
What compiled: nothing new (file is still the sorry skeleton, statement line unchanged).
Remaining gap: the entire theorem (Li23b extractor + polytime machine). Dead end for a short relay.

## Leg 3: codex  (00:10, 3 min, ended: exit)
File stats: proved lemmas 8, sorries 1, lines 188 (was 0 / 1 / 10)
# Codex relay handover

Approach: specialize a one-bit two-source extractor to uniform sources on finite sets. Error below `1/2` guarantees both bits on a rectangle, and threshold `d ^ ⌈K⌉₊` gives the required `K * logb 2 d` min-entropy. Split any candidate homogeneous set into ordered halves and query across them. Sort endpoints before extraction to handle `SimpleGraph.fromRel` symmetrization. Encode vertices as width-`Nat.size n` words and absorb the factor of two and bit-length conversion with exponent `⌈K⌉₊ + 1`.

Compiled in Lean 4.33.1: `dispersesRectangles_of_entropyBias`, `orderedRectangle`, `extractorAdj_iff`, `noHom_of_dispersesRectangles`, `size_le_log_div_add_one`, `twice_size_pow_le`, `fromDisperser`, and `fromExtractor`. The axiom audit for both reductions reports only `propext`, `Classical.choice`, and `Quot.sound`. The import and target statement are unchanged. CI rejects the single remaining `sorry`, at the witness `h` in `OMA.solution`.

Remaining gap: construct the Li 2023 one-bit family `color d u v`, prove `ExtractsOnFlatSources (color d) d (K * logb 2 d) ε` eventually for a constant `ε < 1/2`, and show `IsPolyTime (extractorAdj color)` for the canonical binary triple encoding. A direct rectangle disperser at threshold `d ^ D` also suffices via `fromDisperser`. The `IsPolyTime` obligation includes width calculation, endpoint sorting, and evaluation, and applies to all triples. Generic `TM2ComputableInPolyTime.comp` is only `proof_wanted` in the pinned Mathlib.

Dead ends inherited: changing the exponent alone does not give polylogarithmic homogeneous-set bounds. Brute-force lexicographic powers yield only subpolynomial bounds.

## Leg 4: fable  (00:15, 5 min, ended: exit)
File stats: proved lemmas 12, sorries 1, lines 256 (was 8 / 1 / 188)
# notes_fable: Erdos78.erdos_78.variants.li_strongly_explicit (leg 4)

Verdict: NOT provable in a relay leg. Statement re-audited, faithful, no loophole:
- BitstringEncoding of N is binary (encodeNat), pairs are delimited blocks, IsPolyTime is a real
  TM2ComputableInPolyTime witness. So adj must run in time poly(log n).
- For any fixed C, (log n)^C < n eventually, so CliqueFree is never vacuous; a genuine
  polylog Ramsey family is required = Li 2023 two-source disperser (not in Mathlib, deep).

Approach (kept from leg 3, extended): reduce the target to ONE hole, now in its weakest form.

What compiled (direct lake env lean, 6 s, only warning = the one sorry at line 250):
- leg 3 lemmas, all kept: dispersesRectangles_of_entropyBias, orderedRectangle, extractorAdj_iff,
  noHom_of_dispersesRectangles, size_le_log_div_add_one, twice_size_pow_le, fromDisperser,
  fromExtractor.
- NEW leg 4: def OrderedBipartiteRamsey adj n m (for A, B in Fin n of card m with A < B pointwise:
  some cross pair has adj false in BOTH query orders, and some cross pair has adj true in one order);
  noHom_of_orderedBipartite (gives NoHomogeneousSet (stronglyExplicitGraph adj n) (2*m));
  fromOrderedBipartite (target from IsPolyTime adj + eventually OrderedBipartiteRamsey adj n (size n ^ D));
  orderedBipartite_of_dispersesRectangles and orderedBipartite_of_disperser (the old
  disperser/extractor hypotheses imply the new one, so the new hole is strictly weaker).

Exact remaining gap (the single sorry, inside OMA.solution):
  exists (D : N) (adj : N x N x N -> Bool), IsPolyTime adj and
    eventually in n, OrderedBipartiteRamsey adj n (Nat.size n ^ D)
i.e. a polytime oracle (no min/max wrapper forced any more: a symmetric adj needs no sorting step)
whose graph on Fin n is two-sided dispersing on ordered rectangles of side (bit length of n)^D.
Two independent sub-obligations, both far beyond a relay leg:
 1. Maths: Li 2023 (two-source disperser for polylog min-entropy). Needs non-malleable extractors,
    resilient functions, etc. Nothing simpler reaches polylog (Frankl-Wilson gives
    exp(sqrt(log n loglog n)), lexicographic powers give n^{o(1)}).
 2. Complexity: an explicit TM2ComputableInPolyTime machine for adj on the delimited binary triple
    encoding. Mathlib only has the identity machine; composition is proof_wanted.

Dead ends (do not repeat): choosing C large; brute force + lexicographic powers; looking for a
unary encoding loophole (there is none); Paley/quadratic residue graphs (polylog bound is open).

Reduction candidate (check.sh verdict: accepted, kernel accepted, axioms propext/Classical.choice/Quot.sound):
  .oma/scratch/reductions/Erdos78.erdos_78.variants.li_strongly_explicit.R1.lean
  H1 = strongly explicit polylog two-source disperser (Li 2023): exists D and polytime ext on
       triples (n, a, b) taking both values on every A x B in Fin n with |A|, |B| >= (size n)^D.
  H2 = IsPolyTime is closed under sorting the two query vertices (min/max) of a triple oracle.
  main : H1 -> H2 -> target. Run it from .oma/scratch with the absolute path (see memory note).

Official check of the proofs file: rejected, lint: forbidden sorry (expected; one sorry left).
Suggestion for the driver: mark the proof FAILED/STALLED; the R1 candidate is the usable output.
