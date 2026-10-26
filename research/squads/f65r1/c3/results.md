# c3 results: voltage lifts of 6-regular bipartite bases by non-abelian groups

Tool: lift.c (copy in this folder), `./lift search BASE 5 SECS SEED 8 OUT GROUP`. Cost = (source, lift vertex) pairs at
distance > 5, summed over the base vertices (lift.c's `best`); 0 = valid candidate. Lower is better.
Bases (bases/): r1, r2 = random 6-regular on h+h (bases.py random); d3, d4 = three random matchings each doubled
(double edges); K66 = K_{6,6}, h=6 only.

## Screen: 30 s per base, seed 1

| combo | group (order) | h | n | K66 | r1 | r2 | d3 | d4 | best |
|---|---|---|---|---|---|---|---|---|---|
| A5 | psl 5 (60) | 6 | 720 | 119 | 145 | 147 | 170 | 583 | 119 |
| Z11:Z4 | meta 11 4 10 (44) | 8 | 704 | - | 119 | 122 | 1142 | 322 | 119 |
| Z13:Z3 | meta 13 3 3 (39) | 9 | 702 | - | 180 | 156 | 516 | 514 | 156 |
| Z9:Z4 | meta 9 4 8 (36) | 10 | 720 | - | 208 | 196 | 1046 | 778 | 196 |
| D16 | dih 16 (32) | 11 | 704 | - | 344 | 315 | - | 4179 | 315 |
| D15 | dih 15 (30) | 12 | 720 | - | 341 | 323 | 2408 | 1733 | 323 |
| D13 | dih 13 (26) | 14 | 728 | - | 493 | 570 | 3457 | 1763 | 493 |
| SL(2,3) | sl 3 (24) | 15 | 720 | - | 334 | 438 | 3240 | 2728 | 334 |

(No D16 d3 result: that run left no log. Entries "-" = not run.)

## 120 s, seed 7, best two combos plus one more base

| combo | base | cost after 120 s |
|---|---|---|
| A5 | K66 | 142 |
| Z11:Z4 | r1 | 126 |
| Z11:Z4 | r2 | 130 |
| Z13:Z3 | r2 | 152 |

No cost-0 lift found. Longer runs did not improve on the 30 s runs (the annealer plateaus at 120 to 150).

Saved near miss: runs/best704.edges (Z11:Z4 on base h8_r1, n = 704, 6-regular, bipartite). Its apsp check gives
diameter 6 (INVALID), lift cost 133 (a rerun of the 119 screen run with WRITEBEST=1, different timing).

Most promising: Z11:Z4 (meta 11 4 10) on random bases, n = 704, and A5 = PSL(2,5) on K_{6,6} (n = 720). Both plateau
near cost 120, well above 0.
