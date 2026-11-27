# Relay notes for Erdos1140.erdos_1140.variants.at_most_one_exception (prize: )


## Leg 2: codex  (17:13, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:25, 2 min, ended: exit)
File stats: proved lemmas 18, sorries 1, lines 362 (was 0 / 1 / 10)
# notes_opus: Erdos1140 at_most_one_exception (relay leg 1, opus, 2026-11-27)

Approach: restored the OWN partial (lemmas/partial/...ref.lean) into the proof file, which had been
reset to a 10-line skeleton (backup: .oma/scratch/skeleton_1140_backup.lean). The header and the
OMA.solution statement are unchanged.

Compiled (lake env lean, 80 s, the only warning is the sorry in OMA.solution): namespace OMA1140:
prime_of_prop, not_prop_of_factor, not_prop_of_dvd, fin_B0..2, fin_B, fin_A0..2, fin_A,
exists_sqrt_half, structure_of_prop, no_square_mod, jacobi_eq_neg_one, large_family,
reduction_families, reduction_tatuzawa.

Exact remaining gap: OMA.solution needs at most one n of the form 2k^2-1 or 2k^2-2k+1 with k > 3000
and every odd prime q with q^2+1 < 2n inert in Q(sqrt(2n)). That is Tatuzawa (one exceptional
real character) + the Dirichlet class number formula; neither is in Mathlib. reduction_tatuzawa
states exactly these hypotheses.

Dead ends (do not retry): sieving by small primes (CRT survivors always remain); there is no
elementary interaction between two exceptions; one decide for all k < 3001 overflows the kernel.
Useful next step: a reduction (R1 candidates in .oma/scratch/reductions/), not a direct proof.
