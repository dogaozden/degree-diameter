# c5 notes (multi-orbit coset graphs with mcos)

Goal: bipartite max degree 6, diameter 5, n > 684.

## Facts (checked)
- mcos degree rule: an A-orbit with stabiliser order s needs sum_b n_ab = 6/s; so for a feasible type the reciprocal
  sums must agree: sum_A 1/s = sum_B 1/s = c, and n = 2*c*|G|. Types "1,1|2,2" (card) are infeasible (c=2 vs c=1).
- For n in 686..760 with c = 1: |G| in 343..380 (types "1|2,2", "2,2|2,2", "1|3,3,3", "2,3,6|1", ...).
- Calibration: TYPE "1|1" on SmallGroup(342,12) = C6 x (C19:C3): cost 0 (the 684 graph) in 30 s. Log: c5/cal_1_1_342_12.log.
- mcos cost is a count of (orbit representative, vertex) violations, not bad pairs; costs are not comparable to check.sh.

## Tools in c5/
- groups/: multiplication tables (gap_tables.g) for orders 342, 344, ... (generate with `gap -q -c 'ORDER:=N; OUTDIR:="groups";' ../shared/gap_tables.g`).
- scan.sh TYPE SECS RANDCOMB ORDER...: runs mcos on every non-abelian group of the orders; results appended to scan/<TYPE>.tsv
  (order, group, name, type, best cost). Logs scan/<TYPE>.<group>.log, cost-0 edge lists scan/<TYPE>.<group>.best.edges.

## Results so far
- 344#7 (C43:D8): "1|2,2" best 80 (8 s); "2,2|2,2" best 72 (6 s, 6 combos).
- 344#6 (C2 x (C43:C4)): "1|2,2" best 557; "2,2|2,2" random combos 1604 (bad combos).

## Running
- 15:50: background screen "1|2,2", SECS 1.5, RANDCOMB 3, orders 344..380 (scan/1_2-2.tsv), about 9 groups/min.
- 15:53 partial best (mcos cost, 1.5 s x 3 combos): 348#6 C3:(C29:C4) 18; 350#1 C7 x D50 21; 348#5 22; 348#9 25.

## Screen 1|2,2 (orders 344..380, 1.5 s x 3 random combos per group; scan/1_2-2.tsv)
- 428+ groups done (order 360 partly; scan hit its 2700 s budget). Best mcos costs: 348#6 C3:(C29:C4) 18,
  360#119 C3xS5 18, 360#133 20, 350#1 C7xD50 21, 348#5 22, 352#4 22. Order 343 has no involutions (skipped).
- Deep runs (60 s per combo, 2 combos): 348#6 -> 17, 360#119 -> 18. Plateau: the annealer does not get near 0.
- Converted to bad pairs: 348#6 best edge list has bad = 2088 far pairs at n = 696 (check score65). Scoreboard line added.
- Note: mcos cost counts (orbit representative, vertex) violations; bad pairs are ~100x larger, so the two scales differ.

## Screen 2,2|2,2 (background, started 16:47, timeout 25 min): orders 348 350 344 352 376 372 380 374 366 370 354 356 358 346
   (scan/2_2-2_2.tsv).

## Screen 2,2|2,2 (orders 344-380 subset, 1.5 s x 3; scan/2-2_2-2.tsv, 266 groups)
- Best: 348#5 cost 26 (bad 2262 at n=696). Not better than 1|2,2.

## Screen 1|3,3,3 (orders 348, 354, 366, 372; scan/1_3-3-3.tsv)
- Best at 1.5 s: 366#2 = SmallGroup(366,2) = C2 x (C61:C3), cost 21. Its n = 3*|G|... n = 732 (2|G|).
- 60 s per combo: 366#2 combo (0,1,1) -> cost 7, bad = 915 far pairs (deep/1_3-3-3.sg_366_2.best.edges).
  The 4 valid combos (all class choices) after 40 s each: 7, 13, 13, 17. 240 s on (0,1,1) stays at 7.
  Seed 99 on (0,0,0), 200 s: 11 (bad also 915 in the saved file; the cost-7 file is deep/1_3-3-3.sg_366_2.best.edges).
- 372#11 (C-group order 372, n=744), 60 s: cost 16, bad 1240.
- Best overall for my card: n = 732, bad = 915 (mcos cost 7), type 1|3,3,3 on C2 x (C61:C3).

## Lessons
- Costs from 1.5 s screens are noisy: 366#2 went 21 -> 7 with 60 s per combo. Long runs on the top screen groups matter.
- RANDCOMB=1 with CLS silently gives no combination (random combo can be invalid); use RANDCOMB=0 with CLS.
- Tables for order 360 (162 groups) and 352 (51 groups) take minutes; the 1|2,2 screen ran out of its 2700 s budget in order 360.

## Status at 17:23 UTC
- No bad=0 found; no graph above 684 beaten by fewer than 915 far pairs. Scoreboard lines: 696/2088, 732/1769, 732/915.
- Nothing left running from c5 at the end (checked).

## Next (if continued)
- Deep runs (60 s per combo, several seeds) on 366#2 with other types of 3-orbits, 1|6,6,6,6,6,6 and 2,3,6|1 on groups of order 360-380 with elements of order 6.
- Replace the default balanced n_ab split with a random one for 1|3,3,3 (only (2,2,2) is feasible here, so no change expected).

## (older) Next
- Screen "2,2|2,2" and "2,3,6|1"-type mixes with the same scan; take the best 10 groups and run them 60-120 s per combo.
- Calibrate longer runs on the best group before trusting any ranking.
- 17:25 final check: seed 3, combo (0,1,1), 120 s -> 11 (best over all runs stays 7 / bad 915). Stopped searching at 17:25 (no bad=0).
- 17:28 type 2,3,6|1 (A orbits of stabiliser order 2,3,6, B regular): 366#1 screen 47, 60 s/combo 33 (bad 4392). Worse than 1|3,3,3.
- Final best for c5: n=732 (SmallGroup(366,2), type 1|3,3,3), bad=915, mcos cost 7; edge list deep/1_3-3-3.sg_366_2.best.edges.
