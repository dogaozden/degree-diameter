# h5 notes (round 2): family "1,1,3|1,1,3", n = 686 on SmallGroup(147,x)
Start 03:22 UTC, stop by 04:22 UTC. Single-threaded; every command under 110 s.
Files: tabu3.c (round-1 copy; one change: env KICK = number of random slots re-randomised at a perturbation, default 2),
twoch.c (exact 2-change enumerator, #includes tabu3.c), p3.sh (seed runner), groups/sg_147_1..6.txt (GAP tables),
best_147_3_a4_bad294.edges(.par) (the round-1 state), edges/ (outputs), logs/p3.log (seed runs), bin/ (binaries).
Cost everywhere = 2 * bad (score65 bad pairs), so cost 588 = bad 294.

## 1. Exact 2-change neighbourhood of the bad-294 state (147_3, a = 4)
Command: ./bin/twoch groups/sg_147_3.txt 4 best_147_3_a4_bad294.edges.par 0 100000 edges/twoch_full.hist edges/twoch_best.edges
- 2032 single changes (10 element slots, 4 coset slots, H and K over the 7 subgroups of order 3), all pairs of changes on
  distinct slots: 1,917,016 evaluated (1,716 invalid because the second value duplicates an element of its block). 77 s.
- Histogram (edges/twoch_full.hist, 506 distinct costs; "cost count"): base 588 (bad 294) 132 pairs (plateau, no change
  in cost); next 2646 (bad 1323) 14 pairs; then 2940 (1470) 8, 3038 (1519) 16, 3234 (1617) 20; the bulk is above bad 2000.
  No pair goes below bad 294. The 132 plateau pairs were not checked for isomorphism.
- Conclusion: the bad-294 state is an isolated minimum in the 2-change neighbourhood (the nearest cost is 4.5 times
  higher).

## 2. Tabu restarts from the bad-294 state with kicks and tenures (28 s each, INIT=.par)
Command: INIT=best_147_3_a4_bad294.edges.par KICK=k ./bin/tabu3 groups/sg_147_3.txt 4 SEED 1000000 T 28 OUT STALL
| KICK | tenure T | stall | seed | result |
| 3 | 4 | 150 | 1 | 588 (no change) |
| 4 | 4 | 150 | 2 | 588 |
| 6 | 4 | 150 | 3 | 588 |
| 3 | 2 | 150 | 4 | 588 |
| 5 | 8 | 300 | 5 | 588 |
| 6 | 12 | 300 | 6 | 588 |
About 720-920 steps per run. No run left the floor: 0 improvements.

## 3. Seeds (22 s each, a = 4 and a = 3, tenure 4, stall 600, random start); best cost per group (cost/2 = bad)
Command: bash p3.sh GROUP A "SEEDS" 22 (log in logs/p3.log, 56 runs in total, plus 4 runs of 40 s on 147_3 a=4)
- 147_3 a=4 (seeds 11-20): best 882 (bad 441); the other costs 1274, 1568 (x2), 1666, 1764, 1862 (x2), 2058 (x2).
- 147_3 a=3 (seeds 11-14): best 1862 (bad 931); 2254 (x3).
- 147_5 a=4 (seeds 11-20): best 1764 (bad 882); 2058 (x3), 2352 (x4), 2646 (x2).
- 147_5 a=3 (seeds 11-14): best 1764 (bad 882); 2058 (x3).
- 147_4 a=4 (seeds 11-20): best 1470 (bad 735, seeds 16 and 17); 1764 (x3), 2058 (x3), 2352 (x2).
- 147_4 a=3 (seeds 11-14): best 1470 (bad 735, seed 14); 2058 (x2), 2352.
- 147_1 a=4 (seeds 11-20): best 1764 (bad 882); 2058 (x5), 2646, 2352.
- 147_1 a=3 (seeds 11-14): best 1764 (bad 882); 2058, 2352 (x2).
- 147_3 a=4 with 40 s runs: seed 51 gives 588 (bad 294; reproduces the round-1 state exactly), seed 52 1078, seed 53 1470,
  seed 54 1666.
- The 22 s runs do not share a common floor: the best values differ across seeds, and the same value repeats at most
  2-3 times in 10 seeds. The 294 state was reached by seed 51 at 40 s (seeds 52-54 at 40 s did not reach it, and seeds
  11-20 at 22 s did not). Round-1 notes report that the same settings with other seeds gave costs 588-1862.
- Caveat: 22 s runs are shorter than the 40 s run that found 294, so the group ranking at 22 s is only a rough guide.
  Group 147_3 with a = 4 still has the lowest floor found (cost 588, from the round-1 run and the 40 s replay of seed 51).
- No graph with cost 0 was found, so apsp was not run.

## Output files
- edges/twoch_full.hist (histogram), edges/twoch_best.edges (not written: no pair beat the base).
- edges/p3_g*_a*_s*.edges and edges/p3b_*.edges: best graph of each run (".par" beside them not written for p3 runs).
