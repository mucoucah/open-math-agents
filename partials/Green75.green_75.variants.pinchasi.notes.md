# Relay notes for Green75.green_75.variants.pinchasi (prize: )


## Leg 3: opus  (17:46, 1 min, ended: exit)
File stats: proved lemmas 3, sorries 1, lines 104 (was 0 / 1 / 10)
# Green75 pinchasi, opus leg 3 (2026-11-27)
Approach: shear + reduction R1 glue, own proof; ONE sorry G75Pin.pinchasi_core (= R1.H2, Pinchasi bound for line arrangements with distinct slopes).
Compiled (lake env lean, only warning is the sorry): G75Pin.cross_shear, G75Pin.shear, OMA.solution glue.
Remaining gap: pinchasi_core. Merged R1.H2.R1 splits it into H1 (discrete sweep; open PR 13628 by another contestant proves it, 383 lines, hints only)
and H2 (Pinchasi centered-block bound for allowable sequences) = the real research core of [Pi03], about 20 pages. Not doable in a leg.
Dead ends: none new; do not try to prove pinchasi_core directly in a short leg.
