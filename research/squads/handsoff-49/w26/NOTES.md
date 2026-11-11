# w26 notes (size benchmark, card in ../cards.md)
Start: 02:28 UTC. Deadline for bench.md: 03:05 UTC. Machine load at start ~7 on 4 cores (shared with 7 workers): all timings are under contention; load is logged next to each block.
Plan: (1) checker timing on 4970 / 170 / 686 graphs, 20 reps, median; (2) haar_tab and flift evals per second, 30 s each; (3) seeds to cost 0 on solvable instances at each size.
02:45 UTC: bench.md written (w26/bench.md). Checker timings: checker_times.txt. Solvable references: (4,9) meta 71 35 49; (6,5) meta 17 16 3 (N=272); (3,7) meta 11 5 3 (N=55, trivial). No cost-0 at target (3,7) N=84 (floor 2) or (6,5) N=343 (floor 6). No records found or claimed; nothing written outside w26/.
