# c4 notes: bi-coset graphs B(G;H,K), |H| = |K| = 2 (n = |G|) and 3 (n = 2|G|/3)

Tools: `sweep.sh MODE H DELTA SECS ORDER ID...` (MODE ex = exhaustive dcenum over unions of double cosets with
total degree 6; sa = dcenum annealing for SECS seconds per (H,K) class pair). It exports the class pairs with
shared/dc2_lib.g (ExportPairs, core-free subgroups of order H) and runs shared/dcenum. Lines go to results.txt,
cost-0 graphs to HITS/ (and HITS.txt).
`list_orders.sh LO HI STEP` lists SmallGroups counts (orders3.txt, orders2.txt). Library lacks some orders (1089, 1088,
1092, ...), those are skipped.

Calibration: sa on SmallGroup(720,439), pair (1,1): best 8 in 6-15 s (matches the prior best 8). Pair (1,2): 635,
pair (2,2): 38. SA variance is large (seed 2 at 6 s: 16).
Cost: exhaustive on n=720 pair (1,1) (216 double cosets, ~1.7M unions) takes >2 min; 3|3 exhaustive is a few seconds.

Plan (15:55): (1) exhaustive 3|3 on all 32 groups of orders 1083..1149 (driver3.sh). (2) SA 2|2 sweep over the 705
even-order groups of 722..766 in random order (driver2.sh), 6 s per pair, as far as time allows.

## Status 15:56
- 3|3 exhaustive: orders 1083, 1086, 1095 .. 1149 (library has 32 groups in range, see orders3.txt). Groups 1083 (6),
  1086 (6), 1101, part of 1113 done: best 182 (722 vertices) so far. Stopped at 1113: the exhaustive union count explodes
  when many partial double cosets (contribution 1) exist (timeout 300 s per pair). Remaining 3|3 groups: use sa mode.
- 2|2 SA sweep started 15:56 (driver2.sh, tasks2.txt = 705 even-order groups in random order, 6 s per pair, one seed).
  results.txt lines "sa h2 ...". Expect ~300 groups by 17:30.
- No cost-0 graph yet. Best 2|2 cost so far: see results.txt (grep 'sa h2').
