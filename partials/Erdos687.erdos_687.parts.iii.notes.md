# Relay notes for Erdos687.erdos_687.parts.iii (prize: $1000)


## Leg 1: opus  (08:26, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# notes_opus: Erdos687.erdos_687.parts.iii (leg 1, opus)
Approach: none viable. The target is Y(x) = O(x^{1+eps}) for all eps>0, i.e. the open
Erdos $1000 question (best known upper bound is OAI26a quadratic h(k) << k^2, giving x^2/log^2 x;
Iwaniec gives x^2). Statement is faithful (Y = sSup of covered lengths, Green46.IsCoveredByResidues,
real-valued IsBigO atTop, every fixed eps>0); no loophole (Y is genuinely >= x log x ... by FGKMT,
so no degenerate eps).
What compiled: nothing new; the file keeps the one-sorry skeleton.
Remaining gap: the full open problem.
Dead ends: none worth trying in a session; reduction tree R1... already merged upstream by others,
leaves are research-level (sieve upper bounds for Jacobsthal beyond quadratic).
RESULT: STALLED (FAILED fast pass)

## Leg 2: codex  (08:31, 5 min, ended: exit)
File stats: proved lemmas 11, sorries 1, lines 203 (was 0 / 1 / 10)
# Leg 2, Codex

Approach: use CRT to turn a residue cover into a block of consecutive non-coprimes to the primorial. Absorb each Big-O constant by using the estimate with exponent `1 + ε / 2` first.

Compiled with Lean 4.33.1: `add_residue_complement`, `covered_iff_shifted_nonCoprime`, `covered_iff_le_Y`, `Y_lt_iff_uniform_coprime`, `target_iff_uniform_coprime`, `coprime_of_offset_le_length`, `coprime_of_crossing_period`, `coprime_of_reflected_offset`, `uniform_coprime_of_first_half`, `eventually_twice_le_length`, `target_of_first_half`. Only `OMA.solution` contains a sorry. The first import line and theorem statement are unchanged.

Gap: for every `ε > 0`, eventually in `x`, put `P := primorial x` and `L := ⌈(x : ℝ) ^ (1 + ε)⌉₊`. Show that every `b` with `L < b` and `2*b + L < P` admits `1 ≤ m ≤ L` with `(b + m).Coprime P`. Bertrand handles `b ≤ L`. Reflection handles the second half of one period, with `P - 1` or `P + 1` for blocks crossing its end. The reduction leaves the uniform sieve estimate for the interior offsets.

Dead ends: known quadratic Jacobsthal bounds leave all exponents below two open. Bertrand alone only reaches blocks whose lengths are comparable to their offsets. No known uniform sieve lower bound at the required length.

Verification: the axiom audit for `target_of_first_half` reports `propext`, `Classical.choice`, and `Quot.sound`. The required CI checker returned `rejected` with `lint: forbidden: 'sorry'` for the remaining goal.

## Leg 1: opus  (09:22, 0 min, ended: exit)
File stats: proved lemmas 11, sorries 1, lines 203 (was 11 / 1 / 203)
# notes_opus: Erdos687.erdos_687.parts.iii (relay leg 1, opus, wt11)
Approach: none viable in a session. The target Y(x)=O(x^{1+eps}) for all eps>0 is the open
Erdos $1000 Jacobsthal question (best known: x^2/log^2 x, OAI26a). Statement faithful, no loophole.
What compiled (unchanged, from the earlier codex leg): add_residue_complement,
covered_iff_shifted_nonCoprime, covered_iff_le_Y, Y_lt_iff_uniform_coprime,
target_iff_uniform_coprime, coprime_of_offset_le_length, coprime_of_crossing_period,
coprime_of_reflected_offset, uniform_coprime_of_first_half, eventually_twice_le_length,
target_of_first_half. OMA.solution = apply target_of_first_half; sorry.
Exact remaining gap: for every eps>0, eventually in x, with L = ceil(x^(1+eps)), every b with
L < b and 2b+L < primorial x has some 1<=m<=L with (b+m) coprime to primorial x.
This is the open problem itself (uniform Jacobsthal bound j(primorial x) << x^{1+eps}).
Dead ends: Bertrand handles only b<=L; Ingham prime gaps handle only b with b^2 <= L^3
(R3 reduction in wt10, ACCEPTED); known sieve bounds reach only exponent 2.
RESULT: STALLED (open problem, FAILED fast pass)

## Leg 2: codex  (09:27, 4 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 318 (was 11 / 1 / 203)
# Codex relay leg, wt11

Approach: preserve the CRT and first-half reduction. Put `P = primorial x`, `g = gcd P c`, and `d = P/g`. Squarefreeness gives `(c + d*t).Coprime P ↔ t.Coprime g`. Bertrand in the progression through `c`, followed by reflection within one primorial period, handles nearby blocks when `4*d*x ≤ L`.

Compiled: all 11 existing lemmas plus `coprime_add_reduced_denominator`, `coprime_right_of_center`, `coprime_near_center_on_right`, `coprime_near_reduced_denominator`, and `target_of_offsets_away_from_centers`. The axiom audit for the last lemma gave only `propext`, `Classical.choice`, and `Quot.sound`.

Exact remaining gap: for each `ε > 0` and all sufficiently large `x`, put `L = ⌈x^(1+ε)⌉`. For each `b` with `L < b` and `2*b + L < P`, assume that every `c ≤ P` with `b ≤ c + L` and `c ≤ b + 2*L + 1` satisfies `L < 4*(P/gcd P c)*x`. Find `1 ≤ m ≤ L` such that `(b+m).Coprime P`. This is the single remaining goal of `OMA.solution`.

Dead ends: Bertrand at zero applies only for `b ≤ L`, and R3 uses short prime gaps only for `b² ≤ L³`. Known global Jacobsthal bounds fall short of the exponent. Progressions through centers remove an additional class of offsets, but their denominator bound leaves the uniform sieve estimate open.

Verification: direct Lean elaboration succeeded with only the warning for the remaining `sorry`. The required CI command returned `rejected` with reason `lint: forbidden: 'sorry'`. The first import, theorem statement, and 11 earlier proofs are unchanged.

RESULT: STALLED

## Leg 1: opus  (10:13, 0 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 318 (was 16 / 1 / 318)
# notes_opus: Erdos687.erdos_687.parts.iii (relay leg 1, opus, wt12)
Approach: none viable in a session. Target Y(x)=O(x^{1+eps}) for every eps>0 is the open
Erdos $1000 Jacobsthal question (best known x^2/log^2 x, OAI26a). Statement faithful, no loophole.
What compiled (unchanged, from earlier codex legs): add_residue_complement,
covered_iff_shifted_nonCoprime, covered_iff_le_Y, Y_lt_iff_uniform_coprime,
target_iff_uniform_coprime, coprime_of_offset_le_length, coprime_of_crossing_period,
coprime_of_reflected_offset, uniform_coprime_of_first_half, eventually_twice_le_length,
target_of_first_half, coprime_add_reduced_denominator, coprime_right_of_center,
coprime_near_center_on_right, coprime_near_reduced_denominator, target_of_offsets_away_from_centers.
File left untouched (one sorry, in OMA.solution).
Exact remaining gap: eps>0, x large, L=ceil(x^(1+eps)), P=primorial x; every b with L<b,
2b+L<P (and offsets away from centers: L < 4*(P/gcd P c)*x for nearby c) has 1<=m<=L with
(b+m) coprime to P. This is a uniform Jacobsthal bound j(primorial x) << x^{1+eps}: the open problem.
Dead ends: Bertrand only b<=L; Ingham prime gaps only b^2<=L^3 (wt10 R3); sieve bounds reach exponent 2 only.
RESULT: STALLED (open problem, FAILED fast pass)

## Leg 2: codex  (10:19, 6 min, ended: exit)
File stats: proved lemmas 24, sorries 1, lines 489 (was 16 / 1 / 318)
# Codex relay leg, wt12

Approach: require a maximum-length gap in the first half of the primorial period, with a coprime integer at each endpoint. For each center (c) in the period (P), rule out gaps containing either coprime step (cpm P/gcd(P,c)), in addition to the Bertrand neighborhoods. If some prime covers no point exclusively, move its residue to cover the next point and contradict maximality.

Compiled: all 16 earlier lemmas plus Y_lt_iff_coprime_offsets, coprime_center_plus_step, coprime_center_minus_step, coprime_of_center_step_in_block, target_of_coprime_offsets_away_from_centers, exists_maximal_gap_in_first_half, exists_exclusive_point_in_maximal_gap, target_of_maximal_gaps_away_from_centers. The final reduction depends only on propext, Classical.choice, Quot.sound. The first import, prior helper proofs, and OMA.solution statement were preserved exactly.

Exact gap: for every (arepsilon>0), eventually in (x), set (P=operatorname{primorial}(x)), (y=Y(x)), (L=lceil x^{1+arepsilon}ceil). If (Lle y<b) and (2b+y<P), find a coprime in ((b,b+y]) under these assumptions:
- Both (b) and (b+y+1) are coprime to (P).
- Every prime (ple x) divides some point in the block that no other prime (le x) divides.
- Every center (cle P) in (b-yle cle b+2y+1) has (4(P/gcd(P,c))x>y).
- For every (cle P), neither (c+P/gcd(P,c)) nor (c-P/gcd(P,c)) lands in the block.

Dead ends: zero-centered Bertrand and short prime gaps reach limited offset ranges. Center steps and exclusive points impose local constraints but give no bound uniformly over maximal gaps. The supplied global estimates still fall short of the requested exponent.

Verification: Lean elaborated the complete partial file with the sole warning at OMA.solution. The required checker returned rejected, reason `lint: forbidden: 'sorry'`.

RESULT: STALLED

## Leg 1: gemini  (15:46, 3 min, ended: exit)
File stats: proved lemmas 24, sorries 1, lines 489 (was 24 / 1 / 489)
(the model wrote no notes; see partial_gemini.lean)
