# Relay notes for SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt (prize: )


## Leg 3: opus  (18:30, 2 min, ended: exit)
File stats: proved lemmas 5, sorries 1, lines 71 (was 0 / 1 / 10)
# notes_opus: SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt (leg 3)
Approach: glue in proofs/...zero_mem_of_lt.lean (it compiles via lake env lean, ONE sorry).
Compiled (namespace OMA.ZML): grade_succ_eq_bot, grade_eq_bot_of_le, fin0_const (C(x_1..x_0) elements
are constants, via IsFractionRing.div_surjective + isEmptyAlgEquiv), m_zero (grade 1 = bot for m=0),
OMA.solution (reduces to n = m+1, case m=0 done).
Remaining gap: OMA.ZML.core : 1 <= m -> p prime -> grade (MvRatFunc (Fin m) C) p (m+1) = bot.
 - m=1 (Tsen, K_2(C(x))/p=0) is elementary: units = const * prod (x-a)^e, Steinberg on (x-a)/(b-a)+(x-b)/(a-b)=1,
   -1 and constants are p-th powers. Merged R1 reduction (Nick Graham) has this as grade_two_one_var (hint only).
 - m=2 odd p and m>=3 odd p need Bass-Tate norms or cd=m + Bloch-Kato: infeasible. p=2 all m via
   quadratic forms (Lang u-invariant 2^m), open PR 10131 (hint only).
Dead ends: none new; full target is a deep theorem (Voevodsky / Merkurjev-Suslin for odd p).
