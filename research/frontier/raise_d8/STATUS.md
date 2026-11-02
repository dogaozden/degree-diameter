# raise-d8b status at stop (2026-11-02, 01:12 UTC; stopped on Doğa's instruction for budget)

## Found (all checked with haarcheck_gen, BFS from both sides; solutions in research/frontier/sols/, logs in
## research/frontier/beyond/checks/*.gen.txt; rows in research/frontier/beyond/BEYOND_TABLE.md)

| cell | before | now | gain | group, S (orbit type k-m-f) |
|---|---:|---:|---:|---|
| (17,8) | 41,373,072 | 43,463,280 | +5.1 % | PSL(2,41) x Z631, 7-2-3 (sols/d17D8_psl_41_631_orb7-2-3_r3e01.txt) |
| (18,8) | 57,637,680 | 64,792,896 | +12.4 % | PSL(2,97) x Z71, 7-2-4 (sols/d18D8_psl_97_71_orb7-2-4_r2d06.txt) |
| (19,8) | 86,317,296 | 92,599,320 | +7.3 % | PSL(2,59) x Z451, 5-3-4 (sols/d19D8_psl_59_451_orb5-3-4_s3.txt) |
| (20,8) | 122,739,120 | 131,610,120 | +7.2 % | PSL(2,59) x Z641, 5-4-0 (sols/d20D8_psl_59_641_orb5-4-0_r4f04.txt) |

D = 7: (19,7) 11,316,940 and (20,7) 15,795,219 (job conics-2's graphs) now have every all-pairs source range VALID
(16/16 and 24/24; checks/d19D7_n11316940_ranges_complete.txt, checks/d20D7_n15795219_ranges_complete.txt). (18,7)
7,309,092 and (17,7) 5,693,959 are the conics-2 values. No new D = 7 graph from this job.

## What made it work
Generator sets closed under an automorphism of order 5 or 7 instead of 3. Search cost follows mu/k (fit over 74 runs:
evals ~ exp(1.0 + 1.21 mu/k)). Few fixed letters (they commute). With f = 0 the last holes are alpha-fixed, fixed by
ORBW=5 weighting (haar_big0w.c) plus a group with a small torus.

## Left open
- All four D = 8 cells sit at mu/k ~ 7-8, the practical wall at ~0.2 core per search. More CPU per run (one core for an
  hour) should reach mu/k ~ 9: roughly +1-2 % per cell.
- Unsolved near misses worth one more dedicated run: (20,8) PSL(2,41) x Z1931 5-4-0 ORBW (mu 45.8, cost 5 = one fixed
  hole) and PSL(2,31) x Z4441 (mu 41.6, cost 5); (17,8) SL(2,71) x Z61 5-3-2 (mu 43.9, one fixed hole) and PSL(2,31) x
  Z1481 (mu 50.2, cost 5); (19,8) PSL(2,79) x Z191 5-3-4 (mu 49.3, cost 5). States in runs/ and the squad folders.
- A fast D = 8 fixed-hole screen for f >= 1 exists but was not used in a search: research/squads/raise_d8b/r6/h15/
  haar_big0w8.c (0.015-0.025 s per candidate at d = 17-20, checked equal to full evaluation).
- The 2013 table's D = 8 family (3(q^6 - 1) at (q+2, 8); 5 floor((q+5)/2) |H(q)| at (q+3, 8)) would give ~1.2-1.9x the
  Haar values at (19,8) and (20,8) if its construction were known (BEYOND_TABLE.md, section raise-d8b).
