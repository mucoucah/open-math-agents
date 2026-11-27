# Relay notes for Erdos165.erdos_165.variants.conjecture (prize: $250)


## Leg 1: grok  (04:19, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (04:20, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos165.erdos_165.variants.conjecture - leg 2 (opus) notes
Target: R(3,k) ~ k^2/(2 log k). This is the OPEN CJMS25/HHKP25 conjecture. The Lean statement is faithful
(the R(3,k) notation is classicalRamsey, finite for every k, and the asymptotic is the plain IsEquivalent atTop). No loophole.
- Lower half (>= (1/2 - eps) k^2/log k) is HHKP25: a known but research-level theorem, far beyond a session.
- Upper half with constant 1/2 is OPEN (Shearer gives only constant 1; that is the merged variants.upper proof).
- Merged reduction R1 (Skytracker #3326): H1 = HHKP lower bound, H2 = Shearer for average degree <= k/2
  (open PRs #4379/#4380 attack it), H3 = maximal triangle-free graphs with large degree = the open core.
Compiled: nothing new; the file keeps the single sorry. Dead end: whole target. Recommend FAILED, stop at once.

## Leg 4: fable  (04:24, 4 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 117 (was 0 / 1 / 10)
# Erdos165.erdos_165.variants.conjecture - leg 4 (fable) notes

Verdict: CANNOT BE DONE in a session. Target R(3,k) ~ k^2/(2 log k) is the OPEN CJMS25/HHKP25 conjecture.

Statement audit (done independently, agrees with leg 2): no loophole.
- R(3,k) = SimpleGraph.classicalRamsey 3 k = sInf {n | every C : SimpleGraph (Fin n) has K_3 in C or K_k in C^c}.
  IsContained is the usual injective-hom containment and the set is nonempty by Ramsey, so this is the true Ramsey number.
- RHS is k^2/(2 * Real.log k); relation is plain Asymptotics.IsEquivalent along atTop. No junk value to exploit.

Approach: only glue is possible. Target <=> two one-sided bounds.

What compiled (direct lake env lean, 5 s, only warning = the one sorry). File is 117 lines:
- OMA.main_term_pos      : 0 < k^2/(2 log k) for k >= 2.
- OMA.of_two_sided       : lower + upper bound => the IsEquivalent target. Hypotheses are in the shape of
                           upstream variants.lower ((1/2 - eps) * k^2 / log k <= R(3,k)) and its mirror image.
- OMA.two_sided_of_equiv : converse (target => both bounds), so the hole is exactly as strong as the target.
- OMA.core_two_sided     : SORRY. The conjunction of the two bounds.
- OMA.solution           : proved from of_two_sided + core_two_sided.

Exact remaining gap = OMA.core_two_sided, i.e. the whole conjecture:
1. lower: for all eps>0 eventually (1/2 - eps) k^2/log k <= R(3,k). This is the HHKP25 theorem, word for word the
   upstream sibling Erdos165.erdos_165.variants.lower. Research level, nothing in Mathlib. If that sibling ever
   gets a merged proof, paste it here and half the hole closes.
2. upper: for all eps>0 eventually R(3,k) <= (1/2 + eps) k^2/log k. OPEN. Shearer gives constant 1 only
   (that is the merged variants.upper proof by TheWaler, PR #647).

Dead ends: everything except glue. check.sh was not run (it rejects any file containing sorry at the lint stage).
Recommendation for the next leg: stop at once, report FAILED. Do not try to prove either half.
If time must be spent, the only tractable related item is the separate step problem
Erdos165.erdos_165.variants.conjecture.R1.H2 (Shearer for average degree <= k/2), not this file.

STATUS: final. 3 proved helper lemmas + solution wrapper, 1 sorry.
