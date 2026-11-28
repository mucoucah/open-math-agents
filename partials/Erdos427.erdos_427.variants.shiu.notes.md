# Relay notes for Erdos427.erdos_427.variants.shiu (prize: )


## Leg 2: codex  (17:14, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 1: opus  (17:28, 3 min, ended: exit)
File stats: proved lemmas 5, sorries 1, lines 113 (was 0 / 1 / 10)
# Erdos427 variants.shiu - opus leg 1 notes
Target is the faithful full Shiu 2000 theorem (no loophole; ShiuTheorem checked).
Compiled in proofs/Erdos427.erdos_427.variants.shiu.lean (direct lake env lean, only sorry warning):
- OMA.nth_prime_odd, OMA.shiu_small (q = 1, 2 cases fully proved)
- OMA.card_split, OMA.run_of_excess (pigeonhole: excess of good indices gives k-run; = R1.H2)
- OMA.solution glue: q<=2 via shiu_small; q>=3 via density_excess + run_of_excess.
Remaining gap: ONE sorry OMA.density_excess (q>=3) = R1.H1 density excess, Shiu/Maynard strength.
Dead end: no elementary route; needs Maynard-Tao sieve in APs (Banks-Freiberg-Turnage-Butterbaugh) or Shiu sieve. Not in Mathlib.

## Leg 1: gemini  (21:51, 20 min, ended: cap20_sorry_unchanged)
File stats: proved lemmas 10, sorries 1, lines 430 (was 5 / 1 / 113)
# Erdos427.erdos_427.variants.shiu - gemini leg 1 notes

## Current status of `proofs/Erdos427.erdos_427.variants.shiu.lean`
Verified with `tools/lint.py` (only error: `forbidden: 'sorry'`) and `lake env lean` (compiles cleanly with 0 errors and 1 sorry at `OMA.maynard_affine`, line 407; 430 lines, 21,106 bytes).

### Compiled lemmas (all kept intact)
- `OMA.nth_prime_odd`, `OMA.shiu_small` (q = 1, 2 cases)
- `OMA.card_split`, `OMA.run_of_excess` (pigeonhole run lemma)
- `OMA.nth_prime_ge_add_two`
- `OMA.MaynardAffine` (definition matching `Erdos6.erdos_6.variants.decreasing.R1.H2`)
- `OMA.exists_bftb_crt`, `OMA.exists_mul_add_zmod`
- `OMA.density_excess_of_maynard_affine` (full Banks-Freiberg-Turnage-Butterbaugh 2015 reduction from `OMA.MaynardAffine` to `OMA.density_excess`)
- `OMA.density_excess` (from `OMA.maynard_affine`)
- `OMA.solution` (from `OMA.shiu_small`, `OMA.density_excess`, `OMA.run_of_excess`)

## Exact remaining gap & hard blocker (512 KiB single-file cap)
The sole remaining sorry is `OMA.maynard_affine : OMA.MaynardAffine` (or equivalently Shiu's theorem for `q >= 3`).

This target **cannot** be closed as a monolithic `proofs/Erdos427.erdos_427.variants.shiu.lean` file under `tools/lint.py`'s rules (`len(raw) <= 512 KiB`, and only `FormalConjectures.ErdosProblems.«427»` + `Mathlib` imports allowed):
1. **Merged Maynard-Tao + Bombieri-Vinogradov proofs in this repo exceed 512 KiB even stripped of all whitespace:**
   - `proofs/Erdos427.erdos_427.variants.shiu.lean`: 21.1 KiB raw / 14.1 KiB non-whitespace
   - `proofs/Erdos6.erdos_6.variants.decreasing.R1.H2.lean` (Maynard-Tao from BV): 229.6 KiB raw / 166.5 KiB non-whitespace (99.4% live)
   - `proofs/Erdos6.erdos_6.variants.decreasing.R1.H1.R1.H2.R1.H2.lean` (Vaughan + Large Sieve): 226.5 KiB raw / 159.5 KiB non-whitespace (96.8% live)
   - `proofs/ElliottHalberstamConjecture.elliott_halberstam.variants.bombieri_vinogradov.R1.H1.R1.H1.lean` (orthogonality + induction): 56.4 KiB raw / 44.0 KiB non-whitespace
   - `proofs/ElliottHalberstamConjecture.elliott_halberstam.variants.bombieri_vinogradov.R1.H1.R1.H2.R1.H1.lean` (Siegel-Walfisz): 457.6 KiB raw / 341.1 KiB non-whitespace (87.3% live)
   - **Total (excluding PNT 285.6 KiB and reduction glue ~46 KiB):** 991 KiB raw / ~800 KiB renamed+cleaned / **708.3 KiB pure non-whitespace** vs **512.0 KiB limit**.
2. **Dead ends:**
   - Dropping Siegel's theorem (lines 6360-9610 of Siegel-Walfisz, ~130 KiB) in favor of Page's theorem + Maynard-Tao avoiding one exceptional modulus still leaves ~300 KiB (Perron/contour/ZFR) + 210 KiB (Vaughan/LS) + 220 KiB (Maynard-Tao) + 65 KiB (orthogonality/BFTB) = ~795 KiB > 512 KiB.
   - Shiu's original 2000 proof requires Gallagher's PNT (log-free zero-density estimate + Deuring-Heilbronn + zero-free region) + Selberg sieve / Brun-Titchmarsh, none of which is in Mathlib or this repo and is even larger than BV + Maynard-Tao.
   - No elementary route exists and `ShiuTheorem` in `FormalConjectures/ErdosProblems/427.lean` is faithful (no loophole).

## Recommended path outside this monolithic-file leg
Use OMA's reduction mechanism (`reductions/Erdos427.erdos_427.variants.shiu.R1.H1.R1.lean` or `R2`): put `OMA.density_excess_of_maynard_affine` in the reduction `main` splitting into `H1 = BV` (closed via the existing `ElliottHalberstamConjecture...bombieri_vinogradov` reduction tree, or Chebyshev-centered variant) and `H2 = BV -> MaynardAffine` (closed via `proofs/Erdos6.erdos_6.variants.decreasing.R1.H2.lean`, 229 KiB <= 512 KiB).
