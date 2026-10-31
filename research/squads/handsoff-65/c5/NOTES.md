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

## Next
- Screen "2,2|2,2" and "2,3,6|1"-type mixes with the same scan; take the best 10 groups and run them 60-120 s per combo.
- Calibrate longer runs on the best group before trusting any ranking.
