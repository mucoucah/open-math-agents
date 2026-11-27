# Relay notes for Green97.green_97.variants.simkin (prize: )


## Leg 3: opus  (17:50, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 38 (was 0 / 1 / 10)
# notes_opus: Green97.green_97.variants.simkin (leg 3)
Approach: glue alpha := -log L. File compiles (lake env lean) with ONE sorry.
Compiled: OMA.Simkin.glue (limit L in (exp(-1.9449), exp(-1.94)) -> target), OMA.solution.
Remaining gap: OMA.Simkin.rate_limit = full Simkin 2023 Thm 1.1 (limit existence via
entropy upper bound + random greedy/absorber lower bound, plus numerical certificates
1.94 < alpha < 1.9449, cf. merged R2 H1/H2/H3). Not feasible in a leg.
Dead ends: no loophole (numQueens honest count, strict numeric window). Do not retry fast.
