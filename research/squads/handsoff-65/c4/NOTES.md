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

## Status 16:15
- Switched the 2|2 sweep to diagonal class pairs only (H = K as conjugacy classes, sweep_diag.sh; driver2e.sh over
  tasks2e.txt). Mixed pairs were much worse in every case seen (720/439: 635, 38 vs 8; 760/18: 250, 344 vs 128).
- Each group: GAP export (~2 s) + SA 6 s per diagonal pair. Groups with NOPAIRS: no core-free involution subgroups.
- Best so far: SmallGroup(756,74) pair (1,1): dcenum cost 12 (bad = 2268 far pairs by shared/check.sh), saved as
  best/g756_74_p1_s1.edges. A 60 s anneal gave the same 12 (converged). Next: 756,69 cost 52; 726,6 cost 38.
- deepen.sh ORDER ID PAIR SECS SEED re-exports the group and anneals the diagonal pair (edges to best/).
- Costs are noisy: most groups 90..600 with 6 s SA. No cost-0 graph; no HIT so far.

## Status 17:16
- Diagonal 2|2 sweep: about 390 SA result lines total (about 180 groups of the 705 even-order groups of 722..766,
  random order; the rest untouched). Best cost 12: SmallGroup(756,74) (pairs 1,1 and 2,2 both give 12, 60 s SA
  also 12). Next best: 18 (744,11 p2), 24 (756,79), 28 (756,84), 38 (726,6), 52 (756,69). Many groups 50..600.
- Exhaustive dcenum on 756,74 pair (1,1) (216 double cosets) did not finish in 8 min: exhaustive is only feasible for
  small double-coset counts (3|3 at 1083 ran in seconds; 3|3 at 1113 blew up).
- 3|3 (|G| 1083..1149): exhaustive done for 1083 (groups 1..6, best 182 at 722 vertices), 1086..1101 partly;
  stopped at 1113. Not pursued further (best 182 far from 0).
- No cost-0 graph; no HIT. Scoreboard: one line for c4 (756, cost 12, bad=2268, best/g756_74_p1_s1.edges).

Ideas not done: SA with more seeds on the 756 family (it looks richest: cost 12 twice); mixed class pairs (H != K) for
groups where diagonal pairs are poor; |H| = |K| = 4 (n = |G|/2 .. ) which the card did not cover; a tabu instead of SA
over unions (the landscape looks plateau-like: many runs stop exactly at 12, 24, 28).

## Final 17:30
- Sweep stopped by timeouts (no processes left). About 470 SA result lines covering roughly 230 groups (diagonal
  class pairs). Best cost 12 at SmallGroup(756,74) (best/g756_74_p1_s1.edges, shared/check.sh bad = 2268 far pairs).
- No cost-0 graph, no HIT. tmp/ removed (results.txt keeps every line).
- 17:33 last check: SmallGroup(756,74) p(1,1) with seed 7, 120 s anneal: still cost 12.
