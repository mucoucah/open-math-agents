
## Site hints (erdosproblems.com, added 23:34 Nov 26)
Proved (Banks–Freiberg–Turnage-Butterbaugh). A public Lean formalization exists (plby/lean-proofs, ErdosProblems/Erdos6.lean). Thiago's rule: use it ONLY as a hint for the proof strategy; write your own proof, do not copy that file.

## Leg 1: grok  (23:43, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (23:44, 1 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 74 (was 0 / 1 / 10)
# Erdos6 increasing — leg 2 (opus) notes
Approach: case split on m in OMA.solution.
Compiled (lake env lean, only sorry is m>=2 branch), namespace OMAE6:
- gap_pos : 0 < primeGap n
- nth_add_const : constant gaps c from M on => nth (M+k) = nth M + k*c
- not_eventually_const : prime gaps are never eventually constant (take k = p_M, get p_M*(1+c) prime)
- case_one : {n | primeGap n < primeGap (n+1)}.Infinite (antitone tail => eventually constant via Nat.find min value)
- OMA.solution: m=0 (Set.infinite_univ), m=1 (case_one) done.
Remaining gap: m+2 case (>=3 consecutive increasing gaps). Even m=2 is upstream Erdos6.erdos_6
(research, BFT15 via Maynard-Tao). No elementary route known: increasing runs of bounded length
do not contradict growth of gaps or Westzynthius large gaps (checked by hand: runs can climb
then drop). Needs Maynard sieve — not session-sized.
Dead ends: trying to derive m>=2 from record/large gaps alone (no contradiction).

## Leg 3: codex  (23:50, 5 min, ended: exit)
File stats: proved lemmas 12, sorries 1, lines 316 (was 4 / 1 / 74)
# Erdős 6 increasing, leg 3
Approach: factorial-scaled powers of 3 are admissible, and gaps grow along any increasing subsequence. CRT assigns a distinct prime above the shift bound to each off-tuple offset. A prime-rich translate in the resulting residue class yields a consecutive block by sorting all prime shifts and taking the first m+2. Arbitrarily large translates give arbitrarily large starting prime indices.
Compiled from leg 2: gap_pos, nth_add_const, not_eventually_const, case_one. The m = 0 and m = 1 branches remain complete.
Compiled in leg 3: prime_indices_of_block, geometric_gap_lt, isolate_shifts, geometricShifts_strictMono, geometricShifts_admissible, gaps_of_isolated_shifts, maynardInProgressions_of_commonSlope, increasing_of_maynard. The whole file elaborates with one sorry in OMA.solution.
Exact remaining gap: OMAE6.MaynardCommonSlope (m + 2 + 2) in the m+2 branch. For each r, a universal k suffices so that every admissible family A*t+c_i with A>0 and strictly increasing c_i has at least r prime values at arbitrarily large common t. The common-slope theorem implies the fixed-progression version by solving A*t+b=a modulo each prime not dividing A; the CRT side condition handles primes dividing A.
Dead ends: leg 2 ruled out the record-gap route. Local search found no proven Maynard theorem or Bombieri–Vinogradov in pinned Mathlib or FormalConjectures. Mathlib's Selberg sieve provides upper bounds and does not give the prime-rich lower bound. Dirichlet gives a single prime form at a time.
Verification: the requested tools/check.sh verdict is rejected, reason lint: forbidden: 'sorry'. A separate Lean axiom audit confirmed all eight new helper lemmas use only permitted axioms. OMA.solution adds only sorryAx from the single Maynard hole. The import and solution statement are exact.

## Leg 4: fable  (23:58, 8 min, ended: exit)
File stats: proved lemmas 13, sorries 1, lines 346 (was 12 / 1 / 316)
# Erdos6 increasing — leg 4 (fable) notes

Approach (unchanged, BFT15): geometric shifts k!*3^i are admissible; CRT residue class kills every
off-tuple offset; a prime-rich translate in that class gives m+2 consecutive primes with increasing gaps.

Compiled (direct lake env lean, 5.5 s, one sorry at OMA.solution): everything from legs 2-3
(gap_pos, nth_add_const, not_eventually_const, case_one, prime_indices_of_block, geometric_gap_lt,
isolate_shifts, geometricShifts_strictMono, geometricShifts_admissible, gaps_of_isolated_shifts,
maynardInProgressions_of_commonSlope, increasing_of_maynard). m=0, m=1 complete.

NEW this leg (compiles): MaynardOnce (def) and maynardCommonSlope_of_once: a single t >= 0 for every
admissible family already gives arbitrarily large t (shift constants by A*(X+1); admissibility kept
via t -> t + (p-1)*(X+1)). OMA.solution now needs only the weaker hole.

Exact remaining gap (the ONE sorry, in OMA.solution): OMAE6.MaynardOnce (m+4), i.e.
  exists k, for all A>0 and strictly increasing c : Fin k -> N with (for every prime p some t with
  p not dividing any A*t+c_i), there EXISTS t with at least r of the A*t+c_i prime.
This is Maynard-Tao for admissible forms with a common slope. Not in Mathlib; needs
Bombieri-Vinogradov (any positive level of distribution) plus the Maynard sieve. Statement is
faithful (m=2 is the parent Erdos 6, open until 2015): no loophole. Not session-sized.

Dead ends (checked this leg, do not retry):
- Translates-only Maynard (A=1, no residue class) does NOT suffice by pigeonhole on prime patterns:
  the full prime pattern in the window is uncontrolled between tuple elements (zigzag admissible
  patterns of any length exist), so compositeness of off-tuple offsets really needs the residue class.
- No Ramsey argument on many primes in a bounded window gives consecutive monotone gaps.
- Splitting by m is useless (statement for m+1 implies m).

Reduction candidate (official tools/check.sh verdict: ACCEPTED, kernel accepted, standard axioms):
.oma/scratch/reductions/Erdos6.erdos_6.variants.increasing.R1.lean
  main : H1 -> H2 -> target, all BFT glue inlined (no defs besides H1, H2).
  H1 = Bombieri-Vinogradov (theta in residue classes, moduli up to sqrt x / (log x)^B, error C x/(log x)^A).
  H2 = (that BV estimate) -> for every r some k: every admissible family A*t+c_i has one t with r primes
       (Maynard-Tao sieve in conditional form; this is BFT15 Theorem 2).
Check it with: cd .oma/scratch && OMA_FC=/workspace/left-to-solve/repo/.oma/formal-conjectures ../../tools/check.sh <ABS path> /tmp/v.json

Advice for the next leg: do not attempt the hole; it is the full Maynard-Tao theorem. Nothing else is open.
