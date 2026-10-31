# c25 notes (card: 1,6|1,6 on orders 318..342, n = 7|G|/3 = 742..798)

## Setup (19:45-19:55)
- groups/: GAP tables for ALL SmallGroups of orders 318 (4), 324 (176), 330 (12), 336 (228), 342 (18) (shared/gap_tables.g).
- has6_all.txt: element-order counts. Groups with an element of order 6: 318: 2, 330: 6, 324: 174, 336: 224, 342: 14.
- t18.c, t18 binary: copied from c18 (unchanged). screen18.sh SECS SEED DEADLINE TABLE...: t18 "1,6|1,6" N=5,1,1,0 per table,
  appends scan/screen.tsv (table, order, n, best, time-of-best, secs). Resumable (skips tables already in screen.tsv).
- Command for one run: TLIM=100 ./t18 groups/sg_294_11.txt 6 5,1,1,0 SEED 100000000 12 OUT.edges  (H,K random unless HGEN KGEN given)

## Calibration
- 294_11 (n=686): t18 seed 8, 100 s -> cost 4 (c18 got 2 at 144 s). seed 1, 20 s -> cost 9.
- Machine contention: about 4-5 tabu steps/s (each step scans all single-element moves, ~7*|G| cost evaluations).

## Screen results (10 s, seed 1 for 324; 20 s for 318/330/342)
- 318: 2 groups with order-6 elements: costs 256, 338.
- 330: best 87 (330_1), 90 (330_5), others 105..366.
- 342: best 49 (342_10), 64 (342_11), 90 (342_12); 342_10 with 60 s seed 1 -> 46 (stagnant).
- 324 (first 25 groups at 10 s): best 34 (324_108 and 324_118), then 42, 51, 52, 53.
- Reading: these orders are far worse than the 294_11 outlier (cost 9 at 20 s vs 34..90 at 10-20 s for ord 318-342).

## Next ideas
- Finish the 324 and 336 screens; deep runs (300 s, 2-3 seeds) on the best 3-5.
- If every group stays above 20, the family is probably dead at n >= 742: report the floor and stop.
