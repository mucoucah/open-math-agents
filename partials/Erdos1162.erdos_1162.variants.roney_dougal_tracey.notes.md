# Relay notes for Erdos1162.erdos_1162.variants.roney_dougal_tracey (prize: )


## Leg 2: codex  (16:28, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (18:16, 2 min, ended: exit)
File stats: proved lemmas 5, sorries 1, lines 116 (was 0 / 1 / 10)
# Erdos1162.erdos_1162.variants.roney_dougal_tracey - leg 3 (opus) notes
Approach: R1-style split. Lower bound proved by own construction; upper bound = RoTr25 (open part).
Compiled (direct lake env lean, only warning = sorry): OMA.E1162RT.defect, defect_ker_injective,
transl, transl_injective, lower (2^((n/4)(n/2-n/4)) <= f n), sq_bound (n^2 <= 16 m + 8 n),
and OMA.solution glue (full asymptotic bookkeeping, uses only lower + rotr_upper).
Exact remaining gap (ONE sorry): OMA.E1162RT.rotr_upper:
  forall eps>0, eventually logb 2 (f n) <= (1/16+eps) n^2.
This is the Roney-Dougal-Tracey 2025 upper bound (Theorem 3 nilpotent count + Prop 8.7 + Aschbacher-Guralnick),
not in Mathlib. Merged reductions R1.H2.R1/R2/R2.H2.R1 split it further but every leaf is research-level.
Dead ends: no loophole (f faithful, Nat.card of all subgroups); Pyber-style generator counting only gives O(n^2 log n)-type bounds, not 1/16.
