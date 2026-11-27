# Relay notes for Erdos703.erdos_703.variants.frankl_furedi (prize: $250)


## Leg 1: grok  (00:24, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (00:26, 2 min, ended: exit)
File stats: proved lemmas 4, sorries 1, lines 121 (was 0 / 1 / 10)
# notes_opus: Erdos703.erdos_703.variants.frankl_furedi (leg 2)
Verdict: full Frankl-Furedi 1984 theorem for every fixed r (n large), statement faithful
(checked: extremal families avoid intersection r incl. A=B; r=0 case reduces to 2^(n-1)).
No loophole. Not session-sized for r>=1.
Plan: prove r=0 case as compiled lemma, leave one sorry for r>=1.
## Compiled (lake env lean, only warning = the sorry)
In proofs file, namespace OMA703: half_card (involution halves a finite type), T0_eq
(T n 0 = card S for any 0-avoiding S with 2*card S = 2^n, via Intersecting.card_le),
odd_case, even_case (r=0 target for n odd / n even, n>=1). OMA.solution splits r=0
(fully proved, eventually from n>=1) vs r>=1.
## Remaining gap
ONE sorry: r>=1 branch of OMA.solution = Frankl-Furedi 1984 itself (for fixed r>=1,
n large, T n r equals the stated family size). Needs the FF84 delta-system/shadow argument;
not in Mathlib. Lower bound (family is valid) is easy; the upper bound is the research part.
## Dead ends
No loophole: statement faithful, A=B condition just excludes size-r sets, as in FF84.

## Leg 3: codex  (00:41, 14 min, ended: exit)
File stats: proved lemmas 33, sorries 1, lines 917 (was 4 / 1 / 121)
# Codex relay, leg 3

Preserved `half_card`, `T0_eq`, `odd_case`, `even_case`, the exact first import and `OMA.solution` statement. Added the cached Mathlib Pochhammer import. No external sources consulted.

## Compiled progress

- `card_le_T`, `odd_lower_bound`, `even_lower_bound`, `candidate_le_T`: full lower bound by the union bound, erasing zero in the even case. The inherited `r=0` and new `r=1` branches are complete (`card_le_shadow_of_avoids_one`, `T_le_candidate_one`).
- `compl_shadow_notMem`, `sized_compl_shadow`, `card_slice_add_card_shadow_le`: complements of the r-fold shadow of slice k are excluded from slice n+r-k. `card_middle_slice_le` proves the even middle-layer bound using Kruskal–Katona. `candidate_eq_card_base_add`, `card_le_candidate_of_missing`, `card_le_candidate_of_shadow` assemble the other layers.
- `det_scalar_add_int_matrix_ne_zero`, `eval_eq_sum_choose`, `sum_choose_inter_powersetCard`, `card_le_shadow_of_eval_det_ne_zero`, `exists_forbidden_intersection_polynomial`, `card_le_shadow_of_large_rank`: shadow expansion for k>r+r! via a degree k-r polynomial and the rational-root theorem. The scaled evaluation matrix is `r! I + (k-r) Z` with integral Z, hence invertible. `card_le_candidate_of_no_small_member` handles admissible families with no member of size in `[r,r+r!]`.
- `exists_involutive_inter_card`, `card_add_card_le_of_involution`, `card_add_card_le_of_cross_avoids`: matching for cross-forbidding families, except on sets that fail the balanced-block condition.

## Exact remaining gap

The sole `sorry` is `hsmall` in `OMA.solution`. For each fixed `r ≥ 2`, eventually in n, an admissible F containing some A of size `r ≤ d ≤ r+r!` has `F.card ≤ candidate n r`. Admissibility implies `d ≠ r`. The CI checker rejects the remaining `sorry` at lint.

## Mathematical plan for hsmall

1. Partition F into sections `F_S` of outside sets on `[n] \ A`, indexed by traces `S ⊆ A`. All traces of size r are empty by the forbidden intersection with A itself.
2. For sections S,T with `|S∩T| ≤ r`, the outside sections cross-avoid `s=r-|S∩T|`. Use `card_add_card_le_of_cross_avoids` with disjoint 2s-blocks in the outside ground. Its involution keeps the first balanced block, complementing outside it. For s=0 use the ordinary complement. For s>0 the bad fraction is `(1 - choose(2s,s)/2^(2s))^floor((n-d)/(2s))`; formalize by decomposing into a product over disjoint blocks and arbitrary leftover points. Only a fixed number of blocks (depending on r and desired error) is needed.
3. Fix an empty trace R of size r. Cycle `R → A\R → … → R`, closing the path by adding R's points one at a time then deleting `A\R`'s points one at a time. Fix traces off this cycle. For this permutation g every `|S\g(S)|≤r`. Set `π(S)=A\g(S)` so `π(R)=R` and `|S∩π(S)|≤r`. Sum the cross bounds over `(S,π(S))`, with zero for R. This gives `|F| ≤ (1/2 - 2^(-d-1) + o(1))*2^n`, uniformly over bounded d.
4. For the candidate, use the same block involution with `s=r+1` on the full ground. On success its paired sizes sum to n+r+1 (the union is the full ground). At least one member has size strictly above `(n+r)/2`; the candidate contains all such sets. Therefore its size is at least `(1/2-o(1))*2^n`.

Dead end: demanding nonshrinking r-shadow in every lower layer is false for r≥2. A packing of (r+1)-sets with intersections below r can outnumber its singleton shadow. The bounded-size trace argument above addresses these layers.

## Leg 4: fable  (00:46, 5 min, ended: stalled)
File stats: proved lemmas 33, sorries 1, lines 917 (was 33 / 1 / 917)
(the model wrote no notes; see partial_fable.lean)
