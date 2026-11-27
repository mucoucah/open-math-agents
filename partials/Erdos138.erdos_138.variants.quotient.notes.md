# Relay notes for Erdos138.erdos_138.variants.quotient (prize: $500)


## Leg 1: grok  (04:27, 6 min, ended: stalled)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_grok.lean)

## Leg 2: opus  (04:28, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos138.erdos_138.variants.quotient — leg 2 (opus) notes
Approach: audited faithfulness. Target: Tendsto (W(k+1)/W k : Q) atTop atTop, W = 2-colour van der Waerden number (sInf of guarantee set).
Loophole check: Set.IsAPOfLength needs ENat.card s = l, so d=0 is excluded; W is the genuine vdW number.
(If the guarantee set were empty, sInf = 0 and ratios become 0/0 = 0, so the target would be FALSE, not easier;
nonemptiness is vdW theorem, still sorry upstream.)
Status: genuine OPEN Erdos question (Er81), $500. Known: W(k+1)-W(k) -> inf (difference variant), W(k)^(1/k) -> inf (OAI26),
but no growth-ratio result is known. No compiled lemmas; file is the untouched sorry skeleton.
Dead ends: none worth trying; even a disproof would need exact W values for infinitely many k.
Recommendation: FAILED fast pass, stop at once.

## Leg 4: fable  (04:56, 28 min, ended: max25)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_fable.lean)

## Leg 1: gemini  (14:30, 9 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
# Erdos138.erdos_138.variants.quotient — Gemini leg 1 notes

## Formalization Audit
- Target (`FormalConjectures/ErdosProblems/138.lean:120`):
  `atTop.Tendsto (fun k => ((W (k + 1) : ℚ) / (W k))) atTop`
- Verified exact definitions:
  - `W k = sInf (monoAP_guarantee_set 2 k)`
  - `monoAP_guarantee_set 2 k = { N | ∀ c : Finset.Icc 1 N → Fin 2, ContainsMonoAPofLength c k }`
  - `ContainsMonoAPofLength` uses `Set.IsAPOfLength` which enforces `ENat.card s = k`, excluding `d = 0` for `k ≥ 2`.
  - `monoAP_guarantee_set_nonempty 2 k` is true (van der Waerden's theorem, already proved in `proofs/Erdos138.monoAP_guarantee_set_nonempty.lean`).
- Conclusion: 100% faithful to the open Erdős (1981) problem asking whether `W(k+1)/W(k) -> ∞`. No formalization loopholes.

## Compiled Lemmas
- None added; `proofs/Erdos138.erdos_138.variants.quotient.lean` remains untouched.

## Dead Ends & Obstructions Analyzed
1. **Known upper/lower bounds**: OAI26 (`W(k) > k^{c k}`) vs Gowers (`W(k) ≤ tower_5`) only gives `limsup W(k+1)/W(k) = ∞`, not `liminf = ∞`.
2. **Deterministic black-box lifting (`[1, N] -> [1, 2N]`, `N = W(k)-1`)**:
   - The only affine embeddings of `[1, N]` into `[1, 2N]` are intervals or odd/even residue classes.
   - Interval tiling (with shift, flip, or reflection) fails on boundary-crossing `(k+1)`-APs (splitting as `~k/2 + ~k/2`); forced collisions only cover rare steps `d` (e.g., `d | N` for shift, `2a ≡ C (mod d)` for reflection).
   - Residue-class interleaving (`c'(2j-1) = c(j)`, `c'(2j) = 1 - c(j)`) kills even `d` and `d = 1`, but fails for odd `d ≥ 3` (which splits into two `~k/2`-APs in `c`).
   - Mixed-radix / product XOR (`c'(qN+r) = c(q) ⊕ c(r)`): step `d = N + 1` with `q₀ = r₀` gives an `N`-AP of 0s; AND (`c(q) ∧ g(r)`) gives an `N`-AP of 0s on every `r` with `g(r) = 0`.
3. **Probabilistic lifting**:
   - Random color flips `σ_r` per residue class mod prime `p`: deterministically kills `p | d`, but `p ∤ d` only gets probability `2^{1 - min(p, k+1)}`, which cannot beat `(pN)^2 ≥ W(k)^2 ≫ 2^{2k}` (and all `p` bits are global, so LLL gives no gain over union bound).
   - Local random flips destroy `k`-AP-freeness; random shifts between residue classes yield `≫ 1` expected mono `(k+1)`-APs because `N^2 / (k 2^k) ≫ 1`.
4. **Off-diagonal stepping (`W(a, b) -> W(a, b+1)`)**:
   - Appending `{0, 1}` gives `W(k+1) ≥ W(k) + 2`; color-matching at `N` gives `+3`; DeepMind proved `W(k+1) ≥ W(k) + k`.
   - Any uniform black-box bound `W(a, b+1) ≥ (1 + ε) W(a, b)` is false because `W(3, k)` is sub-exponential (Kelley-Meka), forcing `liminf_{k→∞} W(3, k+1)/W(3, k) = 1`.

## Exact Remaining Gap / Blocker
- Genuine open research problem (Erdős 1981, `@[category research open]` in FormalConjectures as of late 2026): proving `lim_{k→∞} W(k+1)/W(k) = ∞` (even `liminf_{k→∞} W(k+1)/W(k) ≥ 2`, or `> 1`, is open).

## Leg 2: codex  (14:46, 8 min, ended: exit)
File stats: proved lemmas 16, sorries 1, lines 347 (was 0 / 1 / 10)
# Codex relay on Erdős 138 quotient

Approach: for every fixed natural m and all sufficiently large k, it is equivalent to construct a 2-coloring of [1, m * W k] avoiding (k+1)-APs. A cyclic coloring of modulus p avoiding nonzero-step monochromatic (k+1)-APs lifts to [1, k * p]. For k ≥ 2 this is exact for the periodic lift, by reversing any cyclic AP whose step representative exceeds p / 2.

A second construction uses a cyclic coloring modulo p with at least three disagreements with each constant color along every nonzero-step (k+1)-AP. Take a coprime prime q between (k+1)/2 and k+1 and flip colors at multiples of q. Along a step nonzero modulo q, there are one or two flips. Along a step zero modulo q the flip is constant. This yields a coloring avoiding (k+1)-APs on [1, k * p * q].

Compiled: mono_of_affine_points, affine_points_of_mono, guarantee_nonempty (Mathlib Hales–Jewett), includeInterval, guarantee_mono, exists_avoiding_iff_lt, length_le_W, quotient_iff_eventually_avoiding, progression_span_le, periodic_avoids_of_cyclic, avoiding_of_cyclic, mono_of_short_cyclic_step, periodic_avoids_iff_cyclic, quotient_of_eventually_cyclic, cyclic_zero_positions, avoiding_of_robust_cyclic, quotient_of_eventually_robust_cyclic. OMA.solution applies the exact interval reduction and has one placeholder. The CI checker returned rejected with reason lint: forbidden: 'sorry'. A direct kernel check verified the helpers. The audit of guarantee_nonempty, quotient_iff_eventually_avoiding, periodic_avoids_iff_cyclic, and quotient_of_eventually_robust_cyclic reported only propext, Classical.choice, and Quot.sound.

Exact gap: prove eventual existence of the colorings on [1, m * W k], or prove sufficient relative bounds for suitable cyclic periods. In the first construction need k * p ≥ m * W k. With the three-disagreement condition need k * p * q ≥ m * W k. Available absolute bounds do not compare these periods to W k.

Dead ends: interval concatenation, random residue flips, and inference from absolute growth were avoided. Ordinary avoidance does not imply cyclic avoidance, even for prime modulus. For example {2,4,5,7} and {1,3,6} avoid ordinary 3-APs on [1,7], but 5,7,2,4 is a monochromatic cyclic 4-AP. Ordinary cyclic avoidance also does not give three disagreements along a longer AP. The second construction needs that stronger input.
