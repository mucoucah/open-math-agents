# Relay notes for Erdos877.erdos_877.variants.balogh_liu_sharifzadeh_treglown (prize: )


## Leg 2: codex  (16:27, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (18:15, 3 min, ended: exit)
File stats: proved lemmas 10, sorries 1, lines 151 (was 0 / 1 / 10)
# Erdos877 balogh_liu_sharifzadeh_treglown, leg 3 (opus)
Approach: lower bound (own Cameron-Erdos-style seed construction, 2^(n/2/2) <= fm n) + glue
(tendsto_order squeeze) + BLST upper bound as one sorry lemma.
Compiled (lake env lean, no errors): seed, mem_seed, seed_sub, seed_free, exists_maximal,
recover, lower, fm_pos, logb_lower, main, OMA.solution (= main).
Exact remaining gap: ONE sorry, lemma OMA.E877BLST.upper :
  forall eps>0, eventually (fm n : R) <= 2^((1/4+eps)*n).  This is the BLST15 container theorem
  (Green/Sapozhenko containers for sum-free sets + counting maximal independent sets in link graphs).
Dead ends: none elementary known; no Lean formalization in plby/lean-proofs (only luczak_schoen, c<1/2,
which is too weak). Not feasible in a leg.
