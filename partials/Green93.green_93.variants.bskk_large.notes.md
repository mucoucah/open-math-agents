# Relay notes for Green93.green_93.variants.bskk_large (prize: )


## Leg 3: opus  (19:19, 2 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 77 (was 0 / 1 / 10)
# notes_opus: Green93.green_93.variants.bskk_large (leg 3)
Approach: glue only. The proof file compiles (checked with lake env lean) with ONE sorry: BSKKLarge.core.
Compiled: BSKKLarge.monicPoly_coeff_zero (constant coeff = a 0 for n>=1),
  BSKKLarge.eligible_nonempty (conditioning set nonempty for M>=1), OMA.solution glue
  (prob = |I|/|E|, |I| + |E filter not irreducible| = |E|, so 1 - n^-c <= prob).
Remaining gap = core: exists c>0, n0 such that for all M>=34, n>=n0, (log M)^3<=n:
  #(eligible and not Irreducible) <= n^(-c) * #eligible. This is the full BSKK23 Thm 1(a).
Dead ends: the merged proofs/Green93.green_93.lean (Kogler Odlyzko-Poonen port, 7.5k lines) is specific
  to 0/1 coefficients (mod 2 reduction, Bool words, -1 root analysis), so it does not give a bound
  uniform in M up to exp(n^(1/3)). There is no statement loophole: n0 is uniform, M is unbounded, and the
  conditioning is present. STALLED.
