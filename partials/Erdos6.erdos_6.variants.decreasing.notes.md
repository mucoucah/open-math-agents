
## Site hints (erdosproblems.com, added 23:34 Nov 26)
Proved (Banks–Freiberg–Turnage-Butterbaugh). A public Lean formalization exists (plby/lean-proofs, ErdosProblems/Erdos6.lean). Thiago's rule: use it ONLY as a hint for the proof strategy; write your own proof, do not copy that file.

## Leg 1: grok  (23:43, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (23:44, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 33 (was 0 / 1 / 10)
# Erdos6 decreasing — opus leg 2
Approach: the statement is faithful (primeGap n = nth prime (n+1) minus nth prime n, standard 0-indexed). It is the full BFT15 theorem, which needs Maynard-Tao bounded gaps plus a CRT/sieve tweak. There is no loophole: m=0 is trivial, and m=1 alone (infinitely many d_n > d_{n+1}) already needs analytic density input.
Compiled (lake env lean, only warning is the sorry): OMA.dec_mono (a longer run implies a shorter one), OMA.dec_zero (m=0), and OMA.solution glue (m=0 by dec_zero, m>0 by dec_core).
Remaining gap: exactly ONE sorry, OMA.dec_core m (the BFT15 statement for m>0).
Dead ends: none worth repeating. Maynard sieve is not in Mathlib; a plby/lean-proofs formalization exists (hint only, do not copy).

## Leg 3: codex  (23:50, 6 min, ended: exit)
File stats: proved lemmas 14, sorries 1, lines 421 (was 3 / 1 / 33)
## Codex leg 3

- Approach: factorial-scaled reflected powers of two give offsets whose every ordered triple has decreasing gaps. A CRT progression forces all other offsets in the window composite. Local admissibility follows by choosing a safe residue in ZMod p. Prime counts turn any prime-rich window into consecutive prime indices.
- Checked: previous `OMA.dec_mono` and `OMA.dec_zero` retained. New `OMA.dec_run_of_window`, `OMA.exists_dec_offsets`, `OMA.dec_cover`, and `OMA.dec_admissible` have only allowed dependencies. `OMA.dec_core` and the unchanged `OMA.solution` statement compile with the dependency below.
- The m=1 case is proved independently by `OMA.dec_gap_pos`, `OMA.dec_nth_succ`, `OMA.dec_not_constant`, `OMA.dec_gap_growth`, `OMA.dec_summable_of_monotone`, and `OMA.dec_one`. A run of 2(d+1) equal gaps d would contain a prime with proper divisor d+1. Eventual nondecreasing gaps thus force at least n^(3/2) growth, contradicting divergence of prime reciprocals. The axiom audit of `OMA.dec_one` passed.
- Exact remaining gap: `OMA.dec_maynard` is the sole placeholder. For each r, find k such that any locally admissible finite family of at least k distinct forms M*x+b+a with M>0 gives at least r prime values for arbitrarily large x. The final theorem uses this for r ≥ 4.
- Dead end: the pinned Mathlib and local formal-conjectures sources have no usable Maynard sieve theorem. The handover's external formalization was unavailable under the no-network rule.
- Final CI verdict: rejected at lint, forbidden `sorry`. Direct Lean compiled the full partial file and its axiom audit.

## Leg 4: fable  (23:53, 2 min, ended: exit)
File stats: proved lemmas 14, sorries 1, lines 421 (was 14 / 1 / 421)
## Fable leg 4

- Outcome: no new lemma. The file is unchanged from leg 3 and I re-verified it: direct `lake env lean` compiles in 6 s with exactly one `sorry` warning (line 368, `OMA.dec_maynard`) and one harmless deprecation warning. check.sh was not rerun (it rejects at lint on `sorry` without compiling).
- Approach (unchanged, sound): `OMA.solution` = m=0 (`dec_zero`) + m=1 (`dec_one`, elementary, fully proved) + m>=2 (`dec_core`, proved from `dec_maynard` via `exists_dec_offsets`, `dec_cover`, `dec_admissible`, `dec_run_of_window`).
- Exact remaining gap: `OMA.dec_maynard r` = Maynard-Tao for admissible affine forms with a common slope: for each r there is k such that for every finite H with at least k elements, every M > 0 and b, if no prime p divides all values of prod (M*x+b+a) (a in H), then for every N some x > N has at least r primes among M*x+b+a. `dec_core` uses it with r = m+2 (so r >= 4).
- I checked the placeholder is a TRUE statement, not a trap: it is Maynard, Dense clusters of primes in subsets, Theorem 3.1 with fixed forms and x -> infinity (delta is about 1 independent of M, so k depends on r only). The hypothesis already forces gcd(M, b+a) = 1.
- Why I stopped: the gap is the whole Maynard-Tao theorem (multidimensional Selberg weights plus a positive level of distribution, i.e. Bombieri-Vinogradov type input). Even m=2 was an open Erdos-Turan question from 1948 until BFT15, so there is no elementary bypass. Not session-sized.
- Searched and found nothing usable: all wt*/proofs (1051 files), repo/proofs, lemmas/src, formal-conjectures, pinned Mathlib. Mathlib `NumberTheory/SelbergSieve.lean` has only the setup and the upper-bound Moebius lemmas. Mathlib does have Dirichlet (`Nat.forall_exists_prime_gt_and_eq_mod`), which would give only r <= 1 of `dec_maynard` (useless: r >= 4 is needed).
- Sibling: wt10 `Erdos6.erdos_6.variants.increasing` is stuck on the same theorem (`OMAE6.MaynardCommonSlope`, stated over `Fin k -> N` strictly monotone instead of a Finset). A proof of either placeholder closes both files after a short conversion.
- Dead ends (do not repeat): record-gap / Westzynthius / divergence-of-reciprocals arguments only reach m=1; Dirichlet handles one form at a time; the plain n+h Maynard statement without a residue class would NOT suffice (the cover needs x in a fixed class mod M).
- Advice for the next leg: do not spend time here unless a Maynard-Tao port is supplied; nothing short of that changes the sorry count.
