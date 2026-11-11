r2/g08 ANALYSIS: which elements are the holes at (6,13), and is the plateau forced?

Method. Re-evaluated saved states with haar_big0 EVAL, UNCPRINT=1 (no search). Costs reproduced:
sl61x97 24, sl67x73 12, sl59x109 44, sl47x211 72, sl277x1 2 (d=6); sl163x37 2 (d=7); sl409x13 2 (d=8).
Frame: for f=0, EVAL normalises S to T = S s0^-1, which moves the holes. Converted to the orbit frame:
first-kind (untagged) H_S = s0^-1 H_T s0; second-kind (tagged) unchanged. In that frame alpha (conjugation
by g, z -> r z) fixes (e,A) and every hole set is alpha-closed. Scripts: ana/holes2.py, ana/gamma.py.

Lemma (checked on 10 SL states, no failures). Holes are closed under Gamma = <alpha, inverse>, per kind.
Blocks: 6 elements (generic: one trace, one <r,-1>-class of z), 2 (inverse pair of alpha-fixed elements),
or 1 (-I). So cost = 3 x (generic alpha-orbits) + (alpha-fixed holes); cost mod 3 = fixed holes mod 3.

24-plateau (sl61x97): four 6-blocks, two per kind. First kind: trace 33 on one z-class, trace 41 on another.
Second kind: trace 3 and trace 45. No central, involution or alpha-fixed hole. Orders 60/62 and 30/31.
Others: sl67 (12) = two blocks, second kind only. sl59 (44) = seven 6-blocks (central (I,C6) in each
kind, four more in the second kind, one more in the first) plus (-I,0) once per kind. sl47 (72) = twelve 6-blocks, half central (I,z) and (-I,z) on whole z-classes. sl277 (2) = an
inverse pair of alpha-fixed elements in C(g). sl409x13 (2) = alpha-fixed pair with z=0. sl163x37 d=7 (2) = (-I,0)
in both kinds.

Floor from alpha-fixed holes. Fixed set = C(g) x {z : rz = z}, size fx (p -/+ 1). A fixed x is covered by words
in alpha-orbits of size 3, so P(uncovered) ~ exp(-lambda/3). Predicted fixed holes per kind ~ fx (mu/n)^(1/3).
Predicted total / observed: sl61 1.2/0, sl67 1.3/0, sl59 1.3/2, sl47 0.9/0, sl277 4.6/2, sl281 5.8/6,
sl89x31 1.7/0, sl101x21 5.6/4 (fx=3). For small n the floor is 1-3 holes per kind; cost 0 then needs luck.

Is the plateau forced? No lemma gives 24. Random symmetric S at sl61x97 (400 samples): min 42, median 174.
Search reached 24 (12 at sl67). In run g2 the current cost was 24 in 685 of 800 steps, changing only 7 times.
Energy = cost/3, so a +6 move costs 2 units: at T ~ 0.25 that is ~e^-8. One orbit move re-randomises the holes,
so the chain freezes in a block-level local minimum. Constant cost = bad luck of the landscape, quantised by 6.

Hypothesis H. Odd D, SL(2,p) x Z_n: cost = 6 x (generic blocks) + (alpha-fixed holes). The plateau is the
frozen block count; the fixed-hole floor ~ fx (mu/n)^(1/3) per kind dominates only for small n.
Test next: block-level moves (replace a whole Gamma-block) or fixed-hole screening at n >= 61.

Side finding (not my card; checked only by haarcheck_gen): r1/e4 files d6D13_sl_83_37_e4.out and
d6D13_sl_89_31_e4.out EVAL to cost 0 and haarcheck_gen says VALID: SL(2,83)xZ37 (2N=42306096),
SL(2,89)xZ31 (2N=43702560). Not analysed: psl 103x39 (cost 10), psl 107x35 (cost 12).
Outputs: ev/*.txt (EVAL listings), ev/chk83_37.txt, ev/chk89_31.txt.
