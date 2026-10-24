# exp2-alone-4: final report

Job: raise one of (7,7), (9,7), (11,7) at diameter 7 (table values 23,436; 117,648; 398,580 vertices).
Arm: one Haar worker, no subagents. Start 2026-10-24 16:56 UTC, stop 18:10 UTC (wall time 1 h 14 min).
Budget (tools/session_usage.py, this session): budget_units 0.009 of the 1.5 cap (log: research/squads/usage/exp2-alone-4.jsonl).

## Result: no cell beaten

Every graph below is a Haar graph H(G,S) on 2|G| vertices. Each was checked with research/frontier/build_haar2.py (two BFS, exact
diameter 7, max degree = min degree = d, no duplicate edges). Ratio = our vertices / table value.

| cell | table | best valid | ratio | group G (|G|), orbit parameters (k, m, f) |
|---|---|---|---|---|
| (7,7) | 23,436 | 19,152 | 0.817 | SL(2,8) x Z19 (9,576), k=3, m=2, f=1 |
| (9,7) | 117,648 | 85,344 | 0.725 | PGL(2,7) x Z127 (42,672), k=3, m=3, f=0 |
| (11,7) | 398,580 | 266,448 | 0.668 | SL(2,13) x Z61 (133,224), k=3, m=3, f=2 |

Other valid finds (in research/frontier/sols/, all verified):
- d7D7: sl 11 x Z7 (18,480), sl 9 x Z13 (18,720)
- d9D7: sl 13 x Z19 (82,992, f=0 and f=3), sl 11 x Z31 (81,840)
- d11D7: sl 11 x Z91 (240,240)

Files: d7D7_sl_8_19_orb3_s1.txt, d7D7_sl_9_13_orb3_s1.txt, d7D7_sl_11_7_orb3_s1.txt, d9D7_pgl_7_127_orb3f0_s1.txt,
d9D7_sl_13_19_orb3f0_s1.txt, d9D7_sl_13_19_orb3f3_s1.txt, d9D7_sl_11_31_orb3f0_s1.txt, d11D7_sl_11_91_orb3f2_s1.txt,
d11D7_sl_13_61_orb3f2_s1.txt.

## What I tried

1. Random-S annealing (haar_gen3) at (7,7), groups of order 11,718 to 12,144 (the sizes that would beat the table):
   SL(2,23), PSL(2,13) x Z11, PGL(2,11) x Z9, PSL(2,23) x Z2. Four 4-minute runs ended at cost 64 to 149 (uncovered
   vertices). Size law: mu = N e^(-W/N) is about 110 to 120 here, and random annealing cannot reach 0 at that mean.
2. Orbit-symmetric S (haar_sym, ORBIT="k m f"). The code is from branch claude/structured-search-orbit-w5dd4f
   (research/structured/haar_sym.c); I did not commit it to this branch. S is invariant under an automorphism of
   order 3 (conjugation times z -> rz on Z_n), so the words fall into orbits. This is the method that worked here.
   Every group I used satisfies: every prime factor of n is 1 mod 3.

## What worked

- Orbit search on SL(2,q) and PGL(2,q) x Z_n, with the parameters listed above. Rungs solved in seconds to minutes up
  to mu about 30 to 35 (mu = N e^(-W/N), with W the D=7 binding-word count).
- The (11,7) ladder: sl 11 x Z91 (mu 11, 0.2 s), sl 13 x Z61 (mu 32, 68 s).
- The (9,7) gain came from PGL(2,7) x Z127 (mu 38, solved after 12.5 min, 2.0e7 evaluations). Its SL version stalled at cost 12.

## What did not work (floors and stalls)

- (7,7): SL(2,7) x Z31 (N = 10,416, mu 48) stalled at cost 6 for 9 min (5.8e7 evaluations). PGL(2,7) x Z31 stalled at cost 6
  as well, which suggests a structural floor for this group order. Would have been ratio 0.889.
- (7,7): SL(2,9) x Z13 and SL(2,11) x Z7 solved, but are below the best (19,152).
- (9,7) above 42,672: SL(2,9) x Z61 (cost 8), PGL(2,9) x Z61 (cost 3 after 2 runs of 20 min), PSL(2,19) x Z13 (cost 2),
  PSL(2,23) x Z7 (cost 3, ratio would be 0.724), PGL(2,5) x Z361 (cost 72), PROD SL(2,4) x SL(2,9) (cost 22).
- (9,7): SL(2,7) x Z127 with f = 3 (cost 150).
- (11,7) above 133,224: SL(2,11) x Z103 (cost 6), PGL(2,11) x Z103 (cost 11), SL(2,8) x Z271 (cost 18 and 36 with a second seed),
  SL(2,7) x Z397 (cost 60, start cost 33,990).

## Reading

- The orbit method's practical wall in these families is mu about 35 to 40 at about 10^7 evaluations. That leaves the
  table out of reach: for (7,7) it needs mu about 100, for (9,7) about 350, for (11,7) about 750 under random S, and the
  orbit method gains only a factor of about 2 in mu. So none of the three cells is beaten here.
- Verification is the bottleneck for big graphs: build_haar2.py took 2 to 5 min at 85k to 266k vertices.

## Limits

- Random-S annealing and orbit search are the only constructions tried. No voltage lifts, no theory-based constructions.
- The searches were one core each, 20 to 30 minutes per rung, with mostly one seed each.
