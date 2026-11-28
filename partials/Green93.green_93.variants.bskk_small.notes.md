# Relay notes for Green93.green_93.variants.bskk_small (prize: )


## Leg 3: opus  (18:20, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 37 (was 0 / 1 / 10)
# Green93.green_93.variants.bskk_small — opus leg 3 notes
Approach: finite-M glue. File proofs/Green93.green_93.variants.bskk_small.lean compiles (lake env lean) with ONE sorry.
Compiled: OMA.BSKKSmall.upto (induction on K <= 33, min delta / max n0), OMA.solution (from upto 33).
Remaining gap: OMA.BSKKSmall.single_M : for fixed 1<=M<=33, exists delta>0, n0, forall n>=n0, delta <= irreducibleProb M n
  (= BSKK23 Thm 1(b) for one M; full research theorem).
Notes / dead ends:
- M=1 follows from merged green_93 (proofs/Green93.green_93.lean, 7749 lines, Kogler odlyzko-poonen port), but that
  proof is Bool-word specific (wordPolynomial, binaryProbability); does not generalize to {0..M}. Copying it is forbidden anyway.
- M>=2 needs the BSKK23 machinery (no shortcut found). No loophole: statement faithful (coeff0 != 0 conditioning, monic, Irreducible in Z[X]).
