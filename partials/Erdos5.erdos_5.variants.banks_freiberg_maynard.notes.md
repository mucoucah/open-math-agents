# Relay notes for Erdos5.erdos_5.variants.banks_freiberg_maynard (prize: )


## Leg 3: opus  (18:33, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 54 (was 0 / 1 / 10)
# Erdos5 banks_freiberg_maynard - leg 3 (opus)
Target = full BFM16 Thm 1.1 (Maynard-Tao sieve + Erdos-Rankin). Faithful; no loophole
(repeated beta gives difference 0, and 0 in S is itself GPY/Maynard-level).
Plan this leg: own glue Monotone -> StrictMono (zero_mem from strict case + isClosed_limitPointSet),
one sorry nine_point_strict (strict, nonneg, log n normalization).
DONE (direct lake env lean, compiles, only warning = sorry): OMA.BFMNine.zero_mem_of_strict,
OMA.BFMNine.main_of_strict; OMA.solution := main_of_strict nine_point_strict.
Exact remaining gap: nine_point_strict (beta : Fin 9 -> R, nonneg, StrictMono => some beta j - beta i
in limitPointSet), i.e. BFM16 Thm 1.1 itself. Optional: split it as merged R1 does (H1 in log p_n
normalization + H2 log p_n/log n -> 1, H2 already merged in proofs/...R1.H2.lean), but H1 is the
Maynard-Tao sieve + Erdos-Rankin, not in Mathlib.
Dead ends: no loophole (repeated beta needs 0 in S = GPY-level). check.sh rejects any sorry file at lint.
