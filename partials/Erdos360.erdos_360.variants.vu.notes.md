# Relay notes for Erdos360.erdos_360.variants.vu (prize: )


## Leg 2: codex  (16:25, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (18:00, 1 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 72 (was 0 / 1 / 10)
# notes_opus Erdos360 vu (leg 3, opus)
Approach: glue OMA.solution from ONE sorry core lemma OMAVu360.vu_core.
Compiled (lake env lean, only warning = sorry in vu_core):
- OMAVu360.admissible, admissible_nonempty (singleton partition via Finpartition.bot, n>=1)
- exists_partition_card_f (Nat.sInf_mem: f n is attained by an admissible partition)
- vu_of_core (core -> IsBigO, constant 1/c)
- OMA.solution := vu_of_core vu_core
Exact remaining gap: vu_core: exists c>0, eventually every Finpartition of Icc 1 (n-1) with
card <= c*n^(1/3)/log n has a part A with n in subsetSums A.
This is Vu07 itself: needs the Szemeredi-Vu long-AP-in-subset-sums theorem (not in Mathlib).
Dead ends: merged alon_erdos proof (other contestant, hints only) proves only the
n^(1/3)/log^(4/3) bound (prime classes in [y,2y] + Cauchy-Davenport mod p + Graham extension);
the log^(1/3) gain needs Szemeredi-Vu, so adapting that proof does not suffice.
Merged parent R1.H4 (CFP Ramsey lower bound, stronger than Vu) is NOT proved (its R1 children open).
If R1.H4 ever merges with R1.H3, vu follows: answer n >= n^(1/3)/log n for large n.
