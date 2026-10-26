# c2: voltage lifts of larger 6-regular bipartite bases (h+h, k = 2h)

Lift: `lift search BASE 5 SECS SEED 8 OUT GROUP`. Cost = sum over base vertices of lift vertices at distance > 5
from (u,1) (lift.c's cost; lower is better, 0 = diameter <= 5). Lift order n = 2h * |G|.

## Screen: 30 s per run, 4 bases per (h, group)

Bases: `rand_hH_sS` = random 6-regular (bases.py random); `heawood_m6` = Heawood + 3 random matchings (h=7);
`pappus_m6` = Pappus + 3 matchings (h=9); `desargues_m6` = Desargues + 3 matchings (h=10);
`K77_minus_pm` = K_{7,7} minus a perfect matching (simple, h=7); `K99_minus_pappus` = complement of Pappus in K_{9,9};
`circ10` / `circ12` = circulant bipartite (Z_h, S of size 6).

| h | group | n | best cost per base (4 bases) | min cost | min / k |
|---|-------|---|------------------------------|----------|---------|
| 7 | cyc 49 | 686 | rand 74, 76; K77-I 98; heawood 70 | 70 | 5.0 |
| 7 | cyc 7 x cyc 7 | 686 | rand 94, 92; K77-I 92; heawood 104 | 92 | 6.6 |
| 9 | cyc 39 | 702 | rand 184, 138; K99-pappus 162; pappus 144 | 138 | 7.7 |
| 10 | cyc 35 | 700 | rand 172, 148; circ10 188; desargues 170 | 148 | 7.4 |
| 12 | cyc 29 | 696 | rand 208, 220, 200; circ12 196 | 196 | 8.2 |
| 14 | cyc 25 | 700 | rand 306, 382, 242, 228 | 228 | 8.1 |
| 14 | cyc 5 x cyc 5 | 700 | rand 290, 376, 230, 274 | 230 | 8.2 |
| 18 | cyc 20 | 720 | rand 415, 491, 446, 400 | 400 | 11.1 |
| 19 | cyc 19 | 722 | rand 452, 416, 458, 542 | 416 | 10.9 |

Observation: cost grows with h (about 5 per base vertex at h=7, 11 at h=18-19). The h=7 bases are clearly best.
The structured bases (Heawood + matchings, K_{7,7} minus a matching) are the best h=7 bases.

## Follow-up: 120 s runs on h=7 (see screen_results.txt for the raw lines)

LONG_TABLE_PLACEHOLDER

## Notes
- No cost-0 lift found in any run. Nothing to check with apsp.
- The annealer at 30-120 s is far from the cost-4 level reached on small bases in earlier work (lift annealing of
  bases with at most 6+6 vertices). Larger bases make each sweep costlier and seem to leave more uncovered pairs.
