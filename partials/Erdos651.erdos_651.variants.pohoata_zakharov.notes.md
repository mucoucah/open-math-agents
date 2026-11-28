# Relay notes for Erdos651.erdos_651.variants.pohoata_zakharov (prize: )


## Leg 3: opus  (18:27, 2 min, ended: exit)
File stats: proved lemmas 6, sorries 1, lines 165 (was 0 / 1 / 10)
# notes_opus leg3 Erdos651 pohoata_zakharov
Approach: glue = (dim-3 core, ONE sorry) + Valtr projection cardSet k -> k+1 (own proof) + f_le.
COMPILED (lake env lean, only sorry is core3): OMA.PZ.pullback, OMA.PZ.lift_convex,
  OMA.PZ.projection, OMA.PZ.raise, OMA.PZ.raise_all, OMA.solution (glue).
Remaining gap: OMA.PZ.core3 : forall eps>0, eventually n, exists N in cardSet 3 n, N <= 2^(eps n).
  This is exactly Pohoata-Zakharov 2022 Thm 1.1 in R^3 (research; Ramsey only gives tower bounds).
  Merged R1 reduction already phrases it as H1 (t^(Cn/t) bound for bad sets in R^3).
Dead ends: none new; the core needs the full PZ22 argument (lifting + many monochromatic clusters), infeasible here.
