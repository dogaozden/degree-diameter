# d10D8 grind-2: six-hour run (2026-10-26)

Four `haar_sym2` orbit searches (`ORBIT="3 3 1"`, `RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`, `timeout 30000`), started 16:59 UTC and stopped with SIGTERM at about 22:52 UTC (runtime about 5.9 h each). Built from the committed `sym2/haar_sym2.c` with `gcc -O3 -march=native -fopenmp -lm`. No method or code changes.

| run | seed | group | descents (CHAIN) | RESULT best (ORBW energy) |
|---|---|---|---|---|
| g2a | 2001 | psl 23 x Z_97 | 459 | 9 |
| g2b | 2002 | prod psl 7 sl 8 7 (poly x^3+x+1) | 465 | 9 |
| g2c | 2003 | psl 23 x Z_97 | 461 | **7** |
| g2d | 2004 | prod psl 7 sl 8 7 (poly x^3+x+1) | 462 | 9 |

- Descents run: 1847 (CHAIN lines). Evaluations: 158.0 million.
- Lowest energy seen: 7 (g2c). The other three reached 9. Energy is the ORBW=3 weighted uncovered count, so 0 is the target.
- Solutions: none. No `runs/g2?.txt` was written and no cost-0 line appeared.
- Against the cell notes' estimate (about 2.5e-4 per fresh descent), 1847 descents give about 0.46 expected solutions. Seeing none is consistent with that rate (probability about 0.63 of zero), so this run neither confirms nor rules out the estimate.
- No verification was run because nothing to verify was produced.

Progress tails were committed every 30 minutes as `research/d10D8/runs/g2_progress.txt`. Raw checkpoints, logs and `.out` files stay local, excluded in this clone's `.git/info/exclude`.
