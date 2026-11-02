# s17 table: (17,9) shapes at mu 14-20, RANDORB cost statistics (random symmetric S, no search)
Method: `ORBIT="k m f" RANDORB=n THREADS=1 haar_big0 17 9 60 seed 1 /dev/null sl p n`, 3-4 samples per pair
(each sample 10-25 s wall under load ~20; cost = uncovered count, lower is better). Raw lines: raw.log.
Median of 4 is the mean of the middle two. Small samples: treat differences under ~10 as noise.

| group | ORBIT | mu | seed | samples | min | p10 | median | mean | memory |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| SL(2,193) x Z38 (control, mu 14.2) | 3 5 2 | 14.23 | 1 | 4 | 26 | 26 | 44 | 40.5 | 0.24 GB |
| SL(2,193) x Z38 (control) | 3 5 2 | 14.23 | 2 | 4 | 14 | 14 | 38 | 31.0 | 0.24 GB |
| SL(2,199) x Z35 | 3 5 2 | 16.86 | 1 | 4 | 34 | 34 | 40 | 42.0 | 0.24 GB |
| SL(2,199) x Z35 | 3 4 5 | 16.86 | 1 | 3 | 44 | 44 | 56 | 73.3 | 0.24 GB |
| SL(2,199) x Z35 | 3 3 8 | 16.86 | 1 | 3 | 1314 | 1314 | 1536 | 2258 | 0.24 GB |
| SL(2,197) x Z36 | 3 5 2 | 16.24 | 1 | 4 | 36 | 36 | 62 | 61.0 | 0.24 GB |
| SL(2,313) x Z9 | 3 5 2 | 17.04 | 1 | 4 | 34 | 34 | 54 | 49.0 | 0.29 GB |
| SL(2,277) x Z13 | 3 5 2 | 17.39 | 1 | 3 | 32 | 32 | 38 | 37.3 | 0.27 GB |
| SL(2,277) x Z13 | 3 4 5 | 17.39 | 1 | 3 | 60 | 60 | 90 | 82.0 | 0.27 GB |
| SL(2,653) x Z1 (mu 19.9) | 3 5 2 | 19.92 | 1 | 3 | 34 | 34 | 38 | 38.0 | 0.52 GB (over the 300 MB cap; not run further) |

Anneals (K = 4, THREADS=1, ~85 s; the machine was at load ~20 so each eval took 15-20 s, i.e. only 5 evaluations):
- SL(2,277) x Z13, ORBIT "3 5 2": start cost 16, best 16 after 5 evals (an_sl277_13_352.log).
- SL(2,199) x Z35, ORBIT "3 5 2": start cost 30, best 30 after 5 evals; process killed by KILL at 100 s before RESULT
  (an_sl199_35_352.log).

Reading: "3 3 8" (f = 8 random alpha-fixed generators) is hopeless (cost ~1300); "3 4 5" is worse than "3 5 2" on both
groups (median 56 vs 40, 90 vs 38). Among the 17-rung groups, SL(2,277) x Z13 "3 5 2" has the best minimum (32) and the
best anneal start (16). The mu 14.2 control SL(2,193) x Z38 has the lowest random minima (14-26), so the mu gap is real
at this size; the RANDORB medians (38-62) do not separate the groups.
- Second anneal, SL(2,277) x Z13 "3 5 2", seed 11, 80 s: start cost 36, best 36 after 5 evals (an2_sl277_13_352.log).
