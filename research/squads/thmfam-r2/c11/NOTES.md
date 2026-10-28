# c11 (wildcard: nonlinear equivariant labels for LPS x Z_m)

Code: gen_nl.py (self-contained copy of the LPS matrices, S_p reps and r; rules below). Scores: p5_summary logs
(run_p5.sh -> p5_summary.txt, run_pw_p5.sh -> pw_p5.txt, scan_t_p5.sh -> t_scan_p5.txt, run_p7_p13.sh -> p7_p13_summary.txt).
Grid: p=5 q in {13,17,19,23}, m in {7,13,19,31,37,43}; p=7 q in {11,13,17,19}; p=13 q in {17,19}.

Rule family: z = sum_k F(a_k) r^(k-1) mod m (slot form), or z = sum_k G(a0,a_k) r^(k-1) (coupled). Equivariant on the
nose because sigma keeps S_p closed (a0 stays > 0 for all p = 5, 7, 13: checked), so no sign flips occur.
Constant shifts of F vanish (c(1+r+r^2)=0), so F(a)+a0 is the same rule as F(a) (the rule a+a0 IS linear).

p=5 results (mean excess over the 24 cells; FULL in all 24):
  lin (= arith) 3.068 | cube, absa, sgn, inv, cubic, sqa0, sgna0, ab: 3.068 (identical graphs)
  tri 2.901 | mod3 2.818 (best uniform rule) | sq 3.943 | mixc 3.943 | par: not FULL (all labels 0)
  pw:1:t scan (uniform over m, t fixed): best 2.818 at t=2, 1/2, -2, -1/2; t=1 3.943; t=0 3.110.
  Per-m oracle over t (for m=7..37, all t): best t per m gives 2.625, 2.74, 2.755, 2.70, 2.591 (m=7,13,19,31,37);
  m=43 scanned only for t <= 7 (best 2.747). These per-m choices are not a uniform rule.

Structure found (the reason the p=5 rules collapse): every p=5 quaternion in S_5 has a0 = 1 and exactly one nonzero
slot a_k in {+2,-2} (6 elements), so slot rules give labels (F(2)-F(0)) r^(k-1) and (F(-2)-F(0)) r^(k-1). Up to a unit
scaling only t = (F(-2)-F(0))/(F(2)-F(0)) mod m matters. Linear F has t = -1, mod3 has t = 1/2. The a0 coupling is
trivial at p=5 (a0 = 1), so only the even/odd split of F matters.
p=7: S_7 has a0 = 2 and a_k in {+1,-1}; any F then reduces to F(1)-F(-1) times a linear rule (unit scaling), so every
nonzero-odd slot rule equals lin (2.905 for all). An even F gives all labels 0 (sq: not FULL).
p=13: S_13 has a0 in {1,3} and a_k in {0,+2,-2}; the a0-coupling is the only new freedom (sqa0, ab, mixc differ).

p=7 (24 cells: 4 q x 6 m): lin 2.905, pw families 2.905 (identical), sq not FULL.
p=13 (12 cells, 2 q x 6 m): lin 2.539 (best of the list), pw ratio 1/2 or 2 2.623, ab 2.623, sqa0 2.706, sq 3.289, mixc 3.289.

Verification: best uniform rule (mod3) re-checked with verify_cover.py at (q,m) = (13,13) diam 9 and (23,7) diam 10,
matching haar_ecc. No cell beats the 2013 table (best vs_table 0.513 / 0.800 / 0.833 at D = 8, 9, 10).

Conclusion: the nonlinear freedom is real only at p=5 (where the even part of F matters) and at p=13 (a0 coupling);
at p=5 the best uniform rule (mod3, f(a) = a mod 3) improves mean excess from 3.068 to 2.818, but it is still
above the record-level excess (records ~2.0-2.3 at Delta 6-8).
