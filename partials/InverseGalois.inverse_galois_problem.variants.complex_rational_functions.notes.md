# Relay notes for InverseGalois.inverse_galois_problem.variants.complex_rational_functions (prize: )


## Leg 2: codex  (16:29, 0 min, ended: exit)
File stats: proved lemmas 0, sorries 1, lines 10 (was 0 / 1 / 10)
(the model wrote no notes; see partial_codex.lean)

## Leg 3: opus  (18:22, 1 min, ended: exit)
File stats: proved lemmas 2, sorries 1, lines 46 (was 0 / 1 / 10)
# notes_opus: InverseGalois complex_rational_functions (leg 3)
Approach: target = regular IGP over C(t) = Riemann existence (or Harbater patching). Known dead end, no loophole:
any field iso to C(t) is K(s), K alg closed (unique max alg closed subfield), so non-standard Algebra instances do not help.
Noether/Hilbertian specialization route fails (Noether problem false in general; K alg closed not Hilbertian).
Plan this leg: glue reducing to quotient-realizability core (surjection Gal ->> G), one sorry core.
## Result leg 3
Compiled (lake env lean, only warning = sorry): OMA.IGComplexRat.realizable_of_galois_surj (fixed field of kernel,
any base field K : Type), OMA.solution glue. ONE sorry: OMA.IGComplexRat.riemann_existence_core
(every finite G is a quotient of Gal(L/C(t)) for some finite Galois L : Type). check.sh: rejected, lint sorry only.
Exact gap = Riemann existence theorem / regular IGP over C(t); not in Mathlib; infeasible in a leg.
