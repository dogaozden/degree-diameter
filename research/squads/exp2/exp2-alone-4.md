# exp2-alone-4: report (draft, updated as runs finish)

Job: raise (7,7), (9,7) or (11,7) at diameter 7 (table values 23,436; 117,648; 398,580 vertices). Arm: one Haar worker,
no subagents. Start 2026-10-24 16:56 UTC.

## Best valid size per cell (vertices; each checked by research/frontier/build_haar2.py, diameter 7, max = min degree)

| cell | table | our best | ratio | group, orbit parameters |
|---|---|---|---|---|
| (7,7) | 23,436 | 19,152 | 0.817 | SL(2,8) x Z19 (N=9,576), k=3, m=2, f=1 |
| (9,7) | 117,648 | 82,992 | 0.705 | SL(2,13) x Z19 (N=41,496), k=3, m=3, f=0 (and f=3) |
| (11,7) | 398,580 | 266,448 | 0.668 | SL(2,13) x Z61 (N=133,224), k=3, m=3, f=2 |

No cell beaten. (Status at time of drafting; see the final section.)

## What I tried

1. Random-S annealing (haar_gen3) at (7,7), groups of order 11,718 to 12,144 (SL(2,23), PSL(2,13) x Z11, PGL(2,11) x Z9,
   PSL(2,23) x Z2). Four 240 s runs ended at cost 64 to 149 (uncovered count), i.e. far from solved. These groups are
   above the table, so this is the case that would beat it. Predicted mean uncovered count at these orders: mu about 110 to 120.
2. Orbit-symmetric S (haar_sym, from branch claude/structured-search-orbit-w5dd4f, which I fetched, not written by me).
   S is invariant under an automorphism of order 3 (conjugation times z -> rz). This is the method that worked. It
   solved every rung up to about mu = 30 within seconds to minutes. Wall-clock runs of 20 to 30 minutes stalled at
   mu about 38 to 50 (cost 6 to 12, never 0).
3. Size law: for D = 7 the binding word count is W = 1 + sum_i Delta(Delta-1)^(2i-1) (i = 1..3) per side. Then mu = N e^(-W/N).
   Table entries are reached only if N exceeds the table/2, which gives mu of about 100 for (7,7), 350 for (9,7) and
   750 for (11,7) under random S. Orbit search stays feasible at about mu 30 to 40.

## What worked

- Orbit search on SL(2,q) x Z_n with every prime factor of n congruent to 1 mod 3 (so an order-3 automorphism exists).
- Odd D needs two covering conditions; I used SL rather than PSL to avoid the extra involution misses noted in STRUCTURE.md.
- (11,7) climbed from mu 11 (sl 11 x Z91, solved in 0.2 s) to mu 32 (sl 13 x Z61, solved in 68 s).

## What did not work

- (7,7): SL(2,7) x Z31 (N = 10,416, mu 48) stuck at cost 6 for 9 minutes (57 M evaluations). Would have been ratio 0.889.
- (9,7): SL(2,7) x Z127 (mu 38, cost 12 after 14 M evaluations) and SL(2,9) x Z61 (mu 48, cost 8) stuck.
- (9,7) SL(2,7) x Z127 with f = 3 (cost 150) and PROD SL(2,4) x SL(2,9) (cost 22) were poor.
- (11,7) SL(2,8) x Z277 with f = 2 (cost 66 after 90 s) was poor; SL(2,8) x Z271 is running.

## Files

- research/frontier/sols/d7D7_sl_11_7_orb3_s1.txt (18,480 vertices), d7D7_sl_8_19_orb3_s1.txt (19,152), d7D7_sl_9_13_orb3_s1.txt (18,720)
- research/frontier/sols/d9D7_sl_13_19_orb3f0_s1.txt (82,992), d9D7_sl_13_19_orb3f3_s1.txt (82,992), d9D7_sl_11_31_orb3f0_s1.txt (81,840)
- research/frontier/sols/d11D7_sl_11_91_orb3f2_s1.txt (240,240), d11D7_sl_13_61_orb3f2_s1.txt (266,448)

## Budget

(filled in at the end from tools/session_usage.py)
