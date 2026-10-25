# raise-d6D10: raising the (6,10) record above 524,160

Job "raise-6-10" (Haiku worker, 2026-10-25). Record to beat: **524,160** vertices = 2N with
N = |prod sl 5 psl 7 x Z_13| = 262,080, orbit search k = 3, m = 2, f = 0 (file
research/frontier/sols/d6D10_prod_sl_5_psl_7_13_orb3f0_s1.txt; table 452,032).

## Method

Orbit-symmetric connection sets (research/structured/haar_sym, `ORBIT="3 2 0"`), as in STRUCTURE.md §8. Every
group that could beat the record is a group order N > 262,080. Their Poisson mean mu = N exp(-W/N) with
W(6,10) = 2,441,406 is about 24 to 30 there. Planning (tools/mu_plan.py): 2N = 525,032 at mu = 24, 533,003 at
mu = 28, 540,096 at mu = 32. So each unit of mu is worth about 0.4 % of vertices.

Tooling is the same as the earlier sessions: `tools/orb_screen.py 6 10 262081 276000 "3 2 0" --list` lists the
candidate orders; the screen's RANDORB tails rank them. Calibration: the record group under RANDORB (3000
samples) has min 3, p1 16, p10 37, median 281 (scratch log, not committed). The candidates at mu 24 to 25 have
min 14 to 33, p1 36 to 63. So the record group has the better tail, and the candidates need more evaluations.

## Attempts

(filled in below as runs finish)
