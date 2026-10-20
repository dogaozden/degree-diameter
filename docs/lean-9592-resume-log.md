# Lean 9592 resume log

Fresh container: Mathlib from the cache, then every module rebuilt via `scripts/guarded.sh` (started 2026-10-20 14:43 UTC, 4 h limit).
Each build is alone; times are wall-clock, memory is peak RSS.

| module | rc | seconds | peak GB |
|---|---|---|---|
| Staged (Mathlib cache) | 0 | 10 | 1.8 |
| Graphs.G9592 | 0 | 155 | 2.6 |
| Graphs.G9592_lev1 / lev2 / lev3 / lev4 / lev5 / levs | 0 | 411 / 306 / 159 / 115 / 186 / 6 | <1 |
| Stages.G9592_loc0..loc7 | 0 | 65 / 70 / 70 / 86 / 75 / 60 / 66 / 66 | 5.8-7.2 |
| Stages.G9592_local | 0 | 6 | 1.8 |
| Stages.G9592_s0 | 0 | 216 | 11.3 |
| Stages.G9592_s1 | 0 | 441 | 11.7 |
