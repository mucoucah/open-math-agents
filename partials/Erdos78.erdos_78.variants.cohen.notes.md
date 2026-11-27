# Relay notes for Erdos78.erdos_78.variants.cohen (prize: $100)


## Leg 1: grok  (00:03, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (00:04, 1 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos78.erdos_78.variants.cohen, leg 2 (opus)
Approach: none viable. Checked the statement for loopholes and found none.
- Target: exists C>0 and a poly-time (TM2 IsPolyTime) weakly explicit adjacency oracle whose n-vertex graph,
  for all large n, has no clique or independent set of size ceil(2^((log log n)^C)).
- For every fixed C, 2^((loglog n)^C) = n^{o(1)}, and it is smaller than exp(log n * logloglog n / loglog n),
  so the bound is a genuine quasi-polylog Ramsey bound (Cohen 2015, two-source dispersers).
- Elementary explicit constructions are too weak: Frankl-Wilson gives exp(sqrt(log n loglog n)).
  Abbott lexicographic powers of a brute-forced Ramsey graph on m about sqrt(log n) vertices (poly(n) time)
  give only exp(log n * logloglog n / loglog n). Paley and character constructions give unproven bounds.
- Taking C large does not help, because the bound stays n^{o(1)} for every C. ceil, atTop and real log: no loophole.
- Same verdict as the sibling variant li (Li23b), which was recorded faithful with no loophole.
Compiled: nothing new (the file is still the 1-sorry skeleton).
Gap: the whole theorem (Cohen 2015 explicit Ramsey graphs, plus a TM2 poly-time implementation).
Verdict: FAILED fast pass.

## Leg 3: codex  (00:08, 3 min, ended: exit)
File stats: proved lemmas 7, sorries 1, lines 196 (was 0 / 1 / 10)
# Leg 3 (Codex)
Approach: evaluate a one-bit two-source disperser on the lower-to-higher orientation of each pair. Ordered halves of a homogeneous set would force a constant rectangle. Embed Fin n into Fin (2^(n.log2+1)) and take target exponent D+1 to absorb the width, rounding, and the factor of two.
Compiled and audited with the pinned Lean environment: orderedSubsets, noHomogeneousSet_of_rectangles, le_pow_width, tendsto_width, noHomogeneousSet_of_disperses, twice_entropySize_le, cohen_of_disperser. These depend only on allowed axioms.
Exact gap: the single placeholder in OMA.solution asks for D>0 and a uniform f : Nat → Nat → Nat → Bool. For all sufficiently large d, both bits must occur on every A × B in Fin (2^d) with each side of size at least 2^ceil((log d)^D). Prove IsPolyTime for the adapter that computes d = length(unary n).log2+1 and evaluates f on increasing queries, returning false otherwise.
Dead ends: elementary constructions in earlier legs give larger bounds. No imported disperser theorem found. Mathlib declares TM2ComputableInPolyTime.comp as proof_wanted, so the adapter cannot rely on a proved generic composition lemma there.
Checker verdict: rejected at lint for the single remaining sorry. Direct Lean verification of all helper lemmas succeeded.

## Leg 4: fable  (00:13, 5 min, ended: stalled)
File stats: proved lemmas 7, sorries 1, lines 196 (was 7 / 1 / 196)
# Leg 4 (fable)

Approach: none new that closes the gap. I kept the leg 3 file unchanged (it is the best partial proof) and spent the leg
auditing the one remaining place a shortcut could hide: the complexity side of the statement.

Compiled (direct Lean run with .oma/scratch/lean_local.sh, 5 s, only warning is the one sorry at line 189):
orderedSubsets, noHomogeneousSet_of_rectangles, le_pow_width, tendsto_width, noHomogeneousSet_of_disperses,
twice_entropySize_le, cohen_of_disperser. Nothing was added or removed in this leg.

Exact remaining gap (the single sorry in OMA.solution):
  exists D > 0 and f : Nat -> Nat -> Nat -> Bool with
  (1) IsPolyTime (CohenRamsey.orderedOracle f), and
  (2) for all large d, both bits occur on every A x B in Fin (2^d) with |A|, |B| >= 2^ceil((log d)^D).
(2) is Cohen's two-source disperser for polylog min-entropy. It is the whole theorem, not a glue step.

New audit results (so nobody repeats them):
- IsPolyTime is faithful. It is IsPolyTimeWithEncoding at the FIXED canonical BitstringEncoding instances
  (Nat = little-endian binary, pair = delimit block ++ rest, List = flattened delimit blocks), so the encoding
  cannot be chosen to smuggle in the answer bit.
- Mathlib FinTM2 requires Fintype for K, Lambda, sigma and the input alphabet only. Work-stack alphabets may be
  infinite types, but every pushed symbol is f(sigma) for one of finitely many push nodes, so only finitely many
  symbols ever appear. No loophole there either.
- The machine must be correct on ALL inputs (not only on 1^n with u, v < n), but adj is ours to define off that set,
  so this costs nothing and gives nothing.
- The power tower is right-associative: 2^((log log n)^C). For every C this is n^{o(1)}; taking C large does not help.

Dead ends (all recorded, do not retry):
- Brute force / conditional expectations in poly(n) time reach only m = 2^sqrt(log n) vertices; lexicographic powers
  then give 2^(sqrt(log n) loglog n), the Frankl-Wilson / Barak range, far above the target.
- Lexicographic products keep log h / log n fixed, so they can never reach the target from a brute-forced base.
- XOR-type products need a no-common-induced-subgraph property between factors, which is as hard to certify as
  the Ramsey property itself.
- Any poly(n)-size family of bad events that certifies no homogeneous k-set needs t-sets with t >= 2 log n,
  hence (n/k)^(2 log n) events. Spectral certificates stop at sqrt(n).
- Mathlib has TM2ComputableInPolyTime.comp only as proof_wanted, so part (1) needs a hand-built TM2 machine.

Verdict: cannot be done in a relay leg. The gap is a research theorem (Cohen 2015) plus a TM2 implementation of it.
RESULT: STALLED
