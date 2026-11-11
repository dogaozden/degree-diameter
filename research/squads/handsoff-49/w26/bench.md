# w26 size benchmark: (3,7) at ~170 vertices, (6,5) at ~686, (4,9) at ~4,970

Machine: 4 cores shared by 8 workers. The 1-minute load average was 6.7 to 8.2 throughout (uptime readings), so these
are the rates a worker sees on the shared box, not an idle-machine figure. All
commands were run with `nice -n 10`, one process at a time. Sizes deviate from the card in two places, both forced:
(3,7) uses N = 84 (n = 168) because the only group of order 85 is cyclic and cyclic Z_85 stalls at cost 96; (6,5) uses
N = 343 (n = 686) as asked, but its solvable reference instance is Z_17 x| Z_16 at N = 272 (n = 544).

## 1. Checker cost (median of 20 runs, wall time including process start)

| graph | n | apsp median | score48 median | verdict line |
|---|---|---|---|---|
| 4-regular bipartite (seeds/valid4970.edges), d=4 D=9 | 4,970 | 38.9 ms | 32.3 ms | VALID |
| 3-regular bipartite, random (w26/rand3_170.edges), d=3 D=7 | 170 | 3.3 ms | 3.3 ms | (random, not a record) |
| 6-regular bipartite, random (w26/rand6_686.edges), d=6 D=5 | 686 | 3.8 ms | 3.8 ms | (random) |
| process start only (4-vertex graph, apsp) | 4 | 5.3 ms | | |

Spread (min to max over 20 runs): apsp 21 to 158 ms at n = 4,970; 2 to 9 ms at n = 170 and 686.

## 2. Search speed (30 s each, RESULT line of each run)

| tool, instance | (d, D, N) | n | evals in 30 s | evals/s | us per eval | best at end |
|---|---|---|---|---|---|---|
| haar_tab, meta 7 12 3 (Z_7 x| Z_12) | (3,7,84) | 168 | 25,850,121 | 862 k | 1.16 | 2 |
| haar_tab, meta 49 7 8 (Z_49 x| Z_7) | (6,5,343) | 686 | 24,685,009 | 823 k | 1.21 | 6 |
| haar_tab, meta 71 35 1 (Z_71 x Z_35) | (4,9,2485) | 4,970 | 384,617 | 12.8 k | 78 | 4,352 |
| flift, 2+2 base d=3 (w26/base22_d3.txt), meta:43:1:1 | (3,7,43) | 172 | 32,057,161 | 1.07 M | 0.94 | 24 |
| flift, 2+2 base d=6 (w26/base22_d6.txt), meta:43:4:1 | (6,5,172) | 688 | 10,796,409 | 360 k | 2.78 | 32 |
| flift, 2+2 base d=4 (tools/bases/b22_t1.txt), meta:1243:1:1 | (4,9,1243) | 4,972 | 239,112 (30.2 s) | 7.9 k | 126 | 3,866 |

haar_tab counts candidate evaluations; flift counts voltage moves, so compare flift rates only with each other.

## 3. Evaluations to cost 0 on known-solvable instances (haar_tab stops at cost 0)

| instance | n | seeds 1..5: evals to cost 0 | median evals | median time |
|---|---|---|---|---|
| (4,9) meta 71 35 49 (Z_71 x| Z_35, N = 2485, the table graph) | 4,970 | 491,177; 263,753; 607,489; 294,849; 462,113 | 462 k | 5.0 s |
| (6,5) meta 17 16 3 (Z_17 x| Z_16, N = 272) | 544 | 10,457; 833; 20,105; 25,121; 2,593 | 10 k | 0.2 s |
| (3,7) meta 11 5 3 (Z_11 x| Z_5, N = 55) | 110 | 9; 9; 1; 1; 1 | 1 | 0.0 s |

No cost-0 instance was found at the target orders within the budget:
- (3,7) meta 7 12 3 (N = 84): floor 2 (seed 1, 45 s, 41.7 M evals; seed 2, 30 s, 25.9 M evals). Other N = 84 groups
  tried, 8 to 20 s each: Z_28 x| Z_3 floor 10 (40 s), Z_21 x| Z_4 floor 22, Z_14 x| Z_6 floor 14, Z_6 x| Z_14 floor 16,
  Z_3 x| Z_28 floor 22, Z_42 x| Z_2 floor 96; cyclic Z_85 floor 96 (20 s).
- (6,5) meta 49 7 8 (N = 343): floor 6 (40 s, 33.1 M evals; 30 s speed run also 6). Cyclic Z_343 floor 168, Z_7 x Z_49
  floor 168, Heisenberg(7) table floor 10 (8 s), Frobenius Z_19 x| Z_18 (N = 342) floor 8 (25 s).

## Exact commands

```
cd /home/user/degree-diameter/research/squads/handsoff-49/w26
nice -n 10 python3 mkgraphs.py                          # rand3_170.edges (seed 1), rand6_686.edges (seed 2)
nice -n 10 python3 time_checkers.py                     # apsp/score48 x 3 graphs x 20 runs (checker_times.txt)
nice -n 10 python3 baseline_spawn.py                    # process-start baseline (tiny4cycle.edges)
T=../tools
nice -n 10 $T/haar_tab 3 7 30 2 8 speed37.sol meta 7 12 3 1          # RESULT: evals=25850121 time=30.0
nice -n 10 $T/haar_tab 6 5 30 2 8 speed65.sol meta 49 7 8 1          # RESULT: evals=24685009 time=30.0
nice -n 10 $T/haar_tab 4 9 30 2 8 speed49.sol meta 71 35 1 1         # RESULT: evals=384617 time=30.0
nice -n 10 $T/flift base22_d3.txt meta:43:1:1 3 7 30 1               # RESULT: evals=32057161
nice -n 10 $T/flift base22_d6.txt meta:43:4:1 6 5 30 1               # RESULT: evals=10796409
nice -n 10 $T/flift base22_d4.txt meta:1243:1:1 4 9 30 1             # RESULT: evals=239112 time=30.2
for s in 1 2 3 4 5; do nice -n 10 $T/haar_tab 4 9 15 $s 8 solve49_s$s.sol meta 71 35 49 1; done
for s in 1 2 3 4 5; do nice -n 10 $T/haar_tab 6 5 8 $s 8 solve65_s$s.sol meta 17 16 3 1; done
for s in 1 2 3 4 5; do nice -n 10 $T/haar_tab 3 7 8 $s 8 solve37_s$s.sol meta 11 5 3 1; done
```

Base files: base22_d3.txt (K_{2,2} with multiplicities 1,2 / 2,1; 6 edges), base22_d6.txt (2,4 / 4,2; 12 edges),
base22_d4.txt (copy of tools/bases/b22_t1.txt, multiplicities 1,3 / 3,1; 8 edges).

## What changes with size

The checker is never the bottleneck: at n = 170 and 686 the all-pairs check is at the process-start floor (3 to 4 ms,
level with the separately measured 5 ms start baseline),
and at n = 4,970 it adds about 35 ms, which is small next to a search doing 12.8 k evaluations per second there. The
search is where size bites: one evaluation costs about 1.2 us at N = 84 and 343 but 78 us at N = 2,485, and the work to
reach cost 0 jumps from 1 to 10^4 to 5 x 10^5 evaluations as N goes from 55 to 272 to 2,485, while at the target orders
of (3,7) and (6,5) the annealer stalls at a small nonzero floor in every group we tried, so at those sizes instance
solvability, not evaluation speed, is the limit.
