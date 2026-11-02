# TABLE (s18). cost statistics of random symmetric S (haar_big0 RANDORB), seconds per sample ~25-30 under load
group | ORBIT | mu | samples | min | p10 | median | mean | seed
| group | ORBIT | mu | samples (cost) | min | p10 | median | mean | seed |
|---|---|---:|---|---:|---:|---:|---:|---|
| SL(2,241) x Z31 (N 433,915,680; mem 0.39 GB) | "3 6 0" | 16.57 | 16, 18, 24 | 16 | 16 | 18 | 19.3 | 11 |
| SL(2,241) x Z31 | "3 6 0" | 16.57 | 38, 58, 50 | 38 | 38 | 50 | 48.7 | 12 |
| SL(2,241) x Z31 | "3 5 3" | 16.57 | 36, 48, 26, 52 | 26 | 26 | 48 | 40.5 | 1 (4 samples, 1 run) |
| SL(2,241) x Z31 | "3 5 3" | 16.57 | 38, 30, 26 | 26 | 26 | 30 | 31.3 | 12 |
| SL(2,241) x Z31 | "3 4 6" | 16.57 | 132, 108, 138 | 108 | 108 | 132 | 126.0 | 11 |
| SL(2,193) x Z61 (N 438,520,704; mem 0.37 GB) | "3 6 0" | 20.03 | 56, 38, 38 | 38 | 38 | 38 | 44.0 | 11 |
| SL(2,397) x Z7 (N 437,992,632; mem 0.47 GB, OVER the 400 MB cap) | "3 6 0" | 19.60 | 60, 36 (3rd sample killed) | 36 | - | - | - | 11 |
| SL(2,761) x Z1 (N ~4.4e8) | "3 6 0" | 21.9 | see note below | | | | | 11 |

Pooled for SL(2,241) x Z31 "3 6 0" (6 samples): 16,18,24,38,50,58 (median 31). "3 5 3" (7 samples): 26,26,26,30,36,38,48,52 (median 36).
Anneal, 90 s, K=4, THREADS=1, fresh seed (5 evals each, load avg ~20, one eval ~25-30 s):
- SL(2,241) x Z31 "3 6 0" seed 21: start 32 -> best 18 (an1.log; an_sl241x31_360.sol.best)
- SL(2,193) x Z61 "3 6 0" seed 22: start 68 -> best 36 (an2.log; an_sl193x61_360.sol.best)
- SL(2,761) x Z1 (mu 21.89, memory 0.82 GB, over cap) "3 6 0" seed 11, 2 samples: 58, 72 (median 72, rand761.log). The earlier background attempt gave no output (killed before flush).
- SL(2,397) x Z7: memory 0.47 GB (over the 400 MB cap); samples 60, 36 (run_log.txt).
