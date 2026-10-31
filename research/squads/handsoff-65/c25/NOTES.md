# c25 notes (card: 1,6|1,6 on orders 318..342, n = 7|G|/3 = 742..798)

## Status 20:59 UTC (final for this round)
- Best: SmallGroup(324,53), n = 756, cost 18 (bad = 2106 far pairs by check.sh), deep/g324_53_s3.edges (seed 3, 230 s).
  Scoreboard line written. Not a record: bad > 0. Nothing above 684 with cost 0 found.
- No background processes. All runs were foreground, timeout 300, nice 10.

## Setup
- groups/: GAP tables (shared/gap_tables.g) for ALL SmallGroups of orders 318 (4), 324 (176), 330 (12), 336 (228), 342 (18).
- has6_all.txt: groups with an element of order 6: 318: 2, 330: 6, 324: 174, 336: 224, 342: 14.
- t18.c / t18 (copied from c18, unchanged). screen18.sh SECS SEED DEADLINE TABLE...: t18 "1,6|1,6" N=5,1,1,0 per table,
  appends scan/screen.tsv (table, order, n, best, time-of-best, secs). Resumable.
- Run: TLIM=230 ./t18 groups/sg_324_53.txt 6 5,1,1,0 SEED 100000000 TENURE OUT.edges (H,K random; OUT.edges.par = state).
  Restart: INIT=OUT.edges.par TLIM=.. ./t18 TABLE 6 5,1,1,0 SEED ... (the .par file is an INIT file).

## Screen results (t18, 10 s per group for 324, 20 s for 318/330/342, seed 1)
- 324 (all 174 with order 6 done): best 30 (324_131), 31 (324_53), 32 (324_56), 33 (324_129, 324_55), 34 (324_108, 324_118).
- 330 (6 groups): best 87 (330_1), 90 (330_5). 342 (14 groups): best 49 (342_10), 64 (342_11). 318: 256, 338.
- 336 NOT screened (ran out of time; 224 groups with order-6 elements).

## Deep runs (230 s each)
- 324_53 seed 3 tenure 12 (fresh): cost 18 at step 129, then no gain. BEST.
- 324_53 restart from the cost-18 state (INIT, seed 5): no gain (18).
- 324_53 seed 7 tenure 20: cost 20 at step 536.
- 324_53 seed 9 tenure 12, 200 s: cost 18 again at step 521 (deep/g324_53_s9.edges), same floor as seed 3.
- 324_53 seed 11 tenure 30, 200 s: cost 23 at step 697 (tenure 30 is worse than 12 or 20 here).
- 324_56 seed 4 tenure 20: cost 23.
- 324_129 seed 3 tenure 12: cost 26 at step 22, then stuck.
- 324_131 seed 2 tenure 12: cost 30 at step 22, then stuck (bad=3105).

## Calibration
- 294_11 (n=686, c18's family best): t18 seed 8 100 s -> cost 4 (c18 reached 2 at 144 s); seed 1 20 s -> cost 9.
- 342_10 60 s seed 1 -> cost 46 (stalled after step 188).
- Speed: about 4-5 tabu steps/s on the shared machine; every step scans all single-element moves.

## Reading
- Costs on orders 318-342 are far above the 294_11 outlier (which is 9 at 20 s, 2 at 144 s). The best 324 group at 230 s
  is 18. Improvements stop after the first 20-130 steps in most runs, so the tabu gets stuck early.
- Next ideas (not tried): (1) a cheaper move evaluation (incremental BFS) to get 5-10x more steps; (2) sampled moves
  instead of full neighbourhood; (3) bigger perturbations than 2 random slots after 400 stall steps; (4) screen 336 (224
  groups); (5) H, K fixed to generators from the best 294_11 state mapped to order-324 groups (no map exists).
