# Relay notes for Erdos3.erdos_3.variants.green_tao (prize: $5000)


## Leg 1: grok  (04:10, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (04:11, 1 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos3.erdos_3.variants.green_tao -- leg 2 (opus) notes
Approach: none viable. The target is the full Green-Tao 2017 bound r_4(N) << N (log N)^(-c).
Statement is faithful: r = Set.IsAPOfLengthFree.maxCard (sSup of cards of 4-AP-free subsets of Icc 1 N),
BigO at atTop on N : nat. No loophole.
What compiled: nothing new; file unchanged (single sorry in OMA.solution).
Existing upstream: reductions/...green_tao.R1 (transfer to Z/p via Bertrand; H1 = weighted
recurrence estimate, H2 = choice of eps) and proofs/...R1.H2 (merged). The only gap is R1.H1.
Checked: R1.H1 is NOT trivial. eps is universally quantified, so exp(eps^(-B))/p cannot be made large.
For p much bigger than exp(eps^(-B)) it is exactly the Green-Tao density increment for 4-APs (needs
quadratic Fourier analysis, inverse U^3 theorem). Kelley-Meka (r_3) proof in proofs/ does not help with r_4.
Dead end: anything short of formalising GrTa17. FAILED fast pass.

## Leg 4: fable  (04:15, 4 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 92 (was 0 / 1 / 10)
# Erdos3.erdos_3.variants.green_tao -- leg 4 (fable) notes

Approach: none that finishes. Target = full Green-Tao 2017, r_4(N) << N (log N)^(-c).
Re-audited the statement myself: faithful, no loophole.
- r 4 N = sSup of cards of S in Icc 1 N with no 4 distinct terms a, a+d, a+2d, a+3d (ENat.card t = 4).
- the relation is IsBigO atTop on N : nat, rpow with exponent -c, log N > 1 eventually.
Nothing in Mathlib beyond Roth (k = 3). No extra Lake packages (only mathlib and its deps).
proofs/...kelley_meka.lean (520 KB, LeanAPAP port) is r_3 only; r_3 <= r_4 is the wrong direction.

What compiled (direct lake env lean, 5 s, only warning = one sorry at OMA.core):
- OMA.free_elem: IsAPOfLengthFree 4 on a Finset of naturals gives the elementary form
  (no a, d > 0 with a, a+d, a+2d, a+3d all in S).
- OMA.r_le_of_forall: a uniform bound on all admissible S bounds Erdos3.r 4 N (csSup_le', no witness needed).
- OMA.solution: full glue from OMA.core to the target (IsBigO, norms, floor trick).
So the formal-conjectures definitions (sSup, ENat.card, set-builder AP, IsBigO) are completely discharged.

Exact remaining gap = the ONE sorry, OMA.core (definition-free, weakest eventual form):
  exists c > 0, C > 0, N0 such that for all N >= N0 and all S in Finset.Icc 1 N with
  (forall a d, 0 < d -> a in S -> a+d in S -> a+2d in S -> a+3d in S -> False):
  (S.card : real) <= C * (N * Real.log N ^ (-c)).
This is the whole Green-Tao theorem. It needs the inverse U^3 theorem / quadratic Fourier analysis on
Bohr sets and a density increment; none of that exists in Mathlib or in any merged file.

Dead ends (do not repeat):
- loophole hunting in the definitions (checked by legs 2 and 4).
- merged reduction R1: its H1 (weighted recurrence for all eps) is the real theorem, H2 is merged.
- deriving it from Kelley-Meka or Roth: impossible, wrong direction.
- erdos_3 itself (divergent reciprocal sums) would imply it with c = 1, but it is sorry upstream and must not be used.
- even r_4(N) = o(N) (Szemeredi for k = 4) is not available, so no weaker intermediate target is in reach.

RESULT: STALLED (blocker = OMA.core, i.e. the Green-Tao density increment for 4-term progressions,
is not formalised anywhere available and is far beyond a relay leg).
