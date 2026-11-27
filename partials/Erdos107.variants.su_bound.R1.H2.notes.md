# Relay notes for Erdos107.variants.su_bound.R1.H2 (prize: )


## Leg 1: grok  (03:42, 5 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (03:42, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 9 (was 0 / 1 / 9)
# notes_opus: Erdos107.variants.su_bound.R1.H2
Approach: none feasible. H2 = Suk 2017 bound ES(n) <= 2^{n+o(n)} restricted to odd n (eventually in n, any eps in (0,1)).
Faithful, no loophole: N is existential but must be >= ES(n) (general-position sets with distinct x of size ES(n)-1 avoid convex n-gons), so needs the full Suk theorem.
Erdos-Szekeres cups-caps gives only binom(2n-4,n-2)+1 ~ 4^n, too weak for eps<1.
Compiled: nothing new; the file is still the 9-line sorry skeleton. Earlier work (wt11 proofs Erdos107.variants.su_bound) has cups-caps + coordinate bridge with one sorry (the planar Suk theorem for eps<1).
Gap: the whole of Suk 2017 (positive-fraction Erdos-Szekeres + transitive colouring + Dilworth-type argument). Not session-sized.
Dead ends: cups-caps (4^n); parity split does not help (odd case is just as hard).

## Leg 3: codex  (03:58, 15 min, ended: exit)
File stats: proved lemmas 65, sorries 1, lines 1436 (was 0 / 1 / 9)
# Codex relay notes

Approach: use a fixed number of cyclically ordered pockets depending on ε. In a pocket with clockwise anchors a,p,b, project to u=x/y, v=(1-x)/y after affine normalization. Increasing u gives two cases. An antichain has decreasing v, so both anchor determinants are negative and outward caps from nonadjacent pockets can be joined. A chain has increasing v, so the determinant toward a preceding pocket is negative and toward a following pocket positive. Reverse the order of a positive-turn chain in the preceding pocket and join it to the negative-turn chain in the next one. Use anchors beyond both neighboring pockets, and leave a gap when joining outward caps. Oversized chains have positive and negative maximum sizes aᵢ,bᵢ with aᵢ+bᵢ≥(1+δ)n via the asymmetric binomial bound ≤2^(aᵢ+bᵢ); failure of a consecutive join forces aᵢ to increase by δn each step. Large antichains need only outward caps of size n/t, using the asymmetric binomial bound and sufficiently large fixed t.

Compiled: orient_cycle, orient_flip, orient_basis, orient_lt_of_sector, orient_lt_of_preceding, orient_pos_of_following, convex_subset, exact_convex_size, growth_along_blocks. The local Lean command is bash .oma/scratch/lean_local.sh proofs/Erdos107.variants.su_bound.R1.H2.lean.

Remaining gap: solution still contains one hole. Need extraction of a fixed number of positive-fraction oriented pockets and integration of the local chain/antichain and asymmetric cups-caps bounds with the geometry and density argument. Use own partial_su.lean for cups_caps_planar, dense_subsets, large_completion_regions, chain_or_antichain.

Dead ends: symmetric cups-caps gives 4^n. Parity does not improve it. Requiring a directed cycle of chain pockets is unnecessary and may fail when antichain pockets interrupt the cycle. The positive ε surplus instead forces a join along a sufficiently long consecutive run.

09:52 checkpoint: local Lean exit 0 with only the solution hole. New checked lemmas include convex_of_clockwise, convex_of_clockwise_blocks, convex_of_clockwise_union, projected_fst_lt, projected_snd_lt, projected_orientation, projected_image_general, projected_turn, orient_ne_of_distinct, orient_angular_interval, chain_or_antichain, and the reused own cups_caps_planar suite. Projection reverses the orientation of triples, so the original clockwise cap corresponds to the positive-turn option in the projected plane.

Extraction idea: count clockwise convex 3k-subsets using dense_subsets and the classical bound for fixed size 3k. Fix the two anchor vertices per group and leave the middle vertex free. For each group its region consists of all possible replacements preserving signs with any pair of anchors. Prove all mixed signs by orient_angular_interval: viewed from an anchor outside one pocket, a free point lies between the rays to its two endpoint anchors, and disjoint intervals inherit the anchor orientations. Iterate to replace the remaining fixed endpoints with free points. Counting completions of a fixed anchor tuple uses large_completion_regions; all constants may depend on k.

09:54 checkpoint: local Lean exit 0 with only solution hole. Also compiled pocket_chain_or_outward, pocket_cups_caps, pocket_large_turn_sum, pocket_convex, consecutive_pocket_chains, convex_of_outward_pockets, convex_from_chain_run, pocket_outward_or_convex, and convex_from_outward_covers. These prove both assembly cases under their explicit geometry and size hypotheses.

Final check: local Lean exit 0, with one hole. Also compiled sparse_binomial_bound, orient_two_angular_intervals, convex_of_large_layout, finite_suk_bound, and the full OMA.solution body conditional on the hole. Prescribed checker rejected at lint: forbidden sorry. Sole remaining gap is layout_positive_fraction at line 1320: for each fixed k extract a PocketLayout X k with every part larger than L whenever C*(L+1) < X.card, for a constant C depending only on k.

To fill that gap:
1. Put m = 3*(k+2). Use cups_caps_planar with s=t=m-2 to get a clockwise-ordered m-subset from every M-subset, where M=choose(2*(m-2),m-2)+1. Use ascending x for a cap, descending x for a cup. Apply own dense_subsets in partial_su.lean. For N >= 2*m, Nat.pow_le_choose over ℝ gives choose(N,m) >= N^m/(2^m*m!). For each good subset choose a clockwise enumeration. Fix the entries in slots 3i and 3i+2 (all i<k+2), leaving slot 3i+1 free. The anchor capacity is N^(2*(k+2)). The own large_completion_regions lemma applies with good subsets as configurations and N^((k+2)-1) as the remaining completion factor. The region of a free slot consists of points satisfying all clockwise signs with pairs of anchors. Choose C ≥ max(M, 2*m, 2^m*m!*choose(M,m)).
2. The regions inherit the clockwise signs and are disjoint. Each lies on the outward side of its narrow anchor edge and all other regions lie on the inward side of that edge. For one anchor and two free points, use orient_two_angular_intervals from the anchor as pivot when it is outside both free slots’ narrow anchor pairs. If that pivot is itself an endpoint for one of those free slots, apply orient_angular_interval only to the other slot, using the first slot’s cell signs. For three free points p,q,r in order, use orient_angular_interval at pivot p, replacing the rays to q’s endpoints by the ray to q. The required signs are from the one-anchor/two-free argument and from the cell signs.
3. Keep free slots 3*(i+1)+1 for i<k. Use wide anchors at positions 3*i and 3*(i+2)+2. A neighboring free slot lies between the pocket and the corresponding wide anchor. Every nonneighboring free slot lies outside that wide interval. The clockwise triple signs (and orient_cycle/flip) then give all PocketLayout fields. The k+2 indexing leaves one buffer pocket on each end.

## Leg 4: fable  (04:03, 5 min, ended: stalled)
File stats: proved lemmas 65, sorries 1, lines 1436 (was 65 / 1 / 1436)
# notes_fable (leg 4) : Erdos107.variants.su_bound.R1.H2
Approach: keep codex file (all compiles, ONE sorry = layout_positive_fraction, the positive-fraction
Erdos-Szekeres with pockets). Plan to fill it:
 (A) clockwise m-tuple from cups_caps_planar (cap ascending x, cup descending x);
 (B) counting: dense_subsets + large_completion_regions (both in .oma/scratch/partial_su.lean, own work);
 (C) geometry: full-product lemma = any choice of cell points (cells defined by one free point + two anchors
     signs) is again a clockwise tuple; proof by orient_angular_interval, pivot at an anchor (2 free + 1 anchor),
     then pivot at a free point (3 free).
Status at start of leg 4: nothing new compiled yet (see below for updates).
