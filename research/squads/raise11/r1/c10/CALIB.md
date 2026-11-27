# c10: search-schedule calibration at (7,11), group sl 29 x Z_229, ORBIT "3 2 1" (N 5,578,440, mu 12.52)

All runs: THREADS=1, `haar_big0 7 11 <secs> <seed> <K> <out> sl 29 229`, final "best" = lowest cost reached (cost = holes).
Machine was shared (user CPU about 30 % of wall time), so arms are compared at equal wall time, not equal CPU.
Solve = best=0. Median is over the runs listed; n is very small.

| arm | knobs | secs/run | seeds | runs | solves | lowest cost | median final cost | evals (total) |
|-----|-------|----------|-------|------|--------|-------------|-------------------|---------------|
| a | default, K=4 | 95 | 2000, 2001 | 2 | 0 | 50 | 53 | 5496 |
| b | default, K=4 | 20 | 2010-2017 | 8 | 0 | 42 | 66 | 4593 |
| c | K=8, TARGP=100 | 95 | 2020, 2021 | 2 | 0 | 42 | 49 | 4390 |
| d | K=2, TARGP=30 | 95 | 2030, 2031 | 2 | 0 | 48 | 54 | 3822 |
| e | REHEATSTEPS=15, TMAX=0.8, K=4 | 95 | 2040, 2041 | 2 | 0 | 50 | 55 | 2812 |
| f | resume chain from a_2000.sol.best, then chained | 95 + 95 | 2050 -> 2051 | 2 | 0 | 50 | 50 | 1643 |

Chain (f) costs: start 56 (a_2000 best) -> 50 (2050) -> 50 (2051, no gain).
Raw costs by run: a 56, 50; b 68, 50, 72, 66, 74, 42, 48, 66; c 56, 42; d 48, 60; e 60, 50; f 50, 50.

Best state file (lowest cost, 42): /home/user/degree-diameter/research/squads/raise11/r1/c10/c_2021.sol.best

## Finding
No arm solved. Lowest cost 42 (about 3.4 x mu). All arms land in the 42-74 band; with 2-8 runs per arm the
differences between schedules are inside the noise, so no schedule is ranked by solve rate. Short runs (20 s) are
not worse per wall second than 95-s runs at this scale (median 66 vs 49-55), which is weak evidence for many short
lineages. The costs are far from 0, so at mu 12.5 this group needs much more search than 6 min per arm.
Verdict: the schedule question is not answerable at (7,11) with this budget; the next step is more lineages per arm,
or a different group with lower cost at the start.
