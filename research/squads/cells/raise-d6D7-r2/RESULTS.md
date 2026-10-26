# Round 2 orbit-pair screen, (6,7), N in [4441, 5300]: alpha of order 3, S = two free alpha-orbits (ORBIT="3 2 0", f = 0)

min = fewest uncovered elements over the sampled alpha-invariant generator sets (RANDORB, haar_sym cost). A 0 would be a solution.
Rows sorted by min. Each row is one group with one scaling r (AR, both cube roots of unity where n is prime; "-" = automatic).
Fast groups: 1.5e7 samples against ~1e6 orbit pairs, so every pair is seen with probability > 1 - 1e-5.
Small-Q groups (SL/PSL/PGL(2,3)) use the slow generic evaluator: 2e6 samples, covers ~80% of the space; their minima
(>= 246) are far above zero, so the coverage gap does not change the verdict.

| min | N | group | mu | fix(alpha) | samples | scan | job |
|---|---|---|---|---|---|---|---|
| 14 | 4620 | psl 11 7 | 67.4 | 5 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_2_psl_11_7 |
| 14 | 4620 | psl 11 7 | 67.4 | 5 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_4_psl_11_7 |
| 24 | 5208 | psl 7 31 | 122.5 | 2 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_25_psl_7_31 |
| 24 | 5208 | psl 7 31 | 122.5 | 2 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_5_psl_7_31 |
| 25 | 4680 | psl 9 13 | 72.1 | 8 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_3_psl_9_13 |
| 25 | 4680 | psl 9 13 | 72.1 | 8 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_9_psl_9_13 |
| 28 | 4896 | sl 17 1 | 90.7 | 17 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_-_sl_17_1 |
| 46 | 5160 | pgl 5 43 | 117.2 | 5 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_36_pgl_5_43 |
| 46 | 5160 | pgl 5 43 | 117.2 | 5 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_6_pgl_5_43 |
| 48 | 5040 | sl 9 7 | 104.6 | 17 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_2_sl_9_7 |
| 48 | 5040 | sl 9 7 | 104.6 | 17 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_4_sl_9_7 |
| 52 | 5040 | pgl 9 7 | 104.6 | 8 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_2_pgl_9_7 |
| 52 | 5040 | pgl 9 7 | 104.6 | 8 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_4_pgl_9_7 |
| 54 | 4740 | pgl 4 79 | 77.0 | 2 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_23_pgl_4_79 |
| 54 | 4740 | pgl 4 79 | 77.0 | 2 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_55_pgl_4_79 |
| 54 | 4740 | psl 5 79 | 77.0 | 2 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_23_psl_5_79 |
| 54 | 4740 | psl 5 79 | 77.0 | 2 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_55_psl_5_79 |
| 66 | 5040 | prod psl 3 sl 4 7 | 104.6 | 8 | 2000000 | small-Q, 2e6 samples | 3_2_0_2_prod_psl_3_sl_4_7 |
| 66 | 5040 | prod psl 3 sl 4 7 | 104.6 | 8 | 2000000 | small-Q, 2e6 samples | 3_2_0_4_prod_psl_3_sl_4_7 |
| 72 | 5160 | sl 5 43 | 117.2 | 5 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_36_sl_5_43 |
| 72 | 5160 | sl 5 43 | 117.2 | 5 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_6_sl_5_43 |
| 112 | 4896 | pgl 17 1 | 90.7 | 17 | 15000000 | exhaustive-scale, 1.5e7 samples | 3_2_0_-_pgl_17_1 |
| 246 | 4632 | pgl 3 193 | 68.3 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_108_pgl_3_193 |
| 246 | 4632 | pgl 3 193 | 68.3 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_84_pgl_3_193 |
| 396 | 4776 | pgl 3 199 | 80.0 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_106_pgl_3_199 |
| 396 | 4776 | pgl 3 199 | 80.0 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_92_pgl_3_199 |
| 510 | 5064 | pgl 3 211 | 107.0 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_14_pgl_3_211 |
| 510 | 5064 | pgl 3 211 | 107.0 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_196_pgl_3_211 |
| 588 | 5208 | pgl 3 217 | 122.5 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_-_pgl_3_217 |
| 588 | 5208 | pgl 3 217 | 122.5 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_25_pgl_3_217 |
| 790 | 4632 | sl 3 193 | 68.3 | 5 | 2000000 | small-Q, 2e6 samples | 3_2_0_108_sl_3_193 |
| 790 | 4632 | sl 3 193 | 68.3 | 5 | 2000000 | small-Q, 2e6 samples | 3_2_0_84_sl_3_193 |
| 1222 | 4776 | sl 3 199 | 80.0 | 5 | 2000000 | small-Q, 2e6 samples | 3_2_0_106_sl_3_199 |
| 1222 | 4776 | sl 3 199 | 80.0 | 5 | 2000000 | small-Q, 2e6 samples | 3_2_0_92_sl_3_199 |
| 1338 | 5064 | sl 3 211 | 107.0 | 5 | 2000000 | small-Q, 2e6 samples | 3_2_0_14_sl_3_211 |
| 1338 | 5064 | sl 3 211 | 107.0 | 5 | 2000000 | small-Q, 2e6 samples | 3_2_0_196_sl_3_211 |
| 1694 | 5208 | sl 3 217 | 122.5 | 5 | 2000000 | small-Q, 2e6 samples | 3_2_0_-_sl_3_217 |
| 1694 | 5208 | sl 3 217 | 122.5 | 5 | 2000000 | small-Q, 2e6 samples | 3_2_0_25_sl_3_217 |
| 3388 | 4476 | psl 3 373 | 57.0 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_284_psl_3_373 |
| 3388 | 4476 | psl 3 373 | 57.0 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_88_psl_3_373 |
| 3532 | 4548 | psl 3 379 | 62.1 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_327_psl_3_379 |
| 3532 | 4548 | psl 3 379 | 62.1 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_51_psl_3_379 |
| 3964 | 4764 | psl 3 397 | 79.0 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_34_psl_3_397 |
| 3964 | 4764 | psl 3 397 | 79.0 | 2 | 2000000 | small-Q, 2e6 samples | 3_2_0_362_psl_3_397 |
| 5952 | 4464 | prod psl 3 psl 3 31 | 56.2 | 8 | 2000000 | small-Q, 2e6 samples | 3_2_0_25_prod_psl_3_psl_3_31 |
| 5952 | 4464 | prod psl 3 psl 3 31 | 56.2 | 8 | 2000000 | small-Q, 2e6 samples | 3_2_0_5_prod_psl_3_psl_3_31 |
| 9240 | 5208 | pgl 3 217 | 122.5 | 92 | 2000000 | small-Q, 2e6 samples | 3_2_0_32_pgl_3_217 |
| 9632 | 5208 | sl 3 217 | 122.5 | 185 | 2000000 | small-Q, 2e6 samples | 3_2_0_32_sl_3_217 |
| 9982 | 5040 | prod psl 3 psl 5 7 | 104.6 | 719 | 2000000 | small-Q, 2e6 samples | 3_2_0_2_prod_psl_3_psl_5_7 |
| 9982 | 5040 | prod psl 3 psl 5 7 | 104.6 | 719 | 2000000 | small-Q, 2e6 samples | 3_2_0_4_prod_psl_3_psl_5_7 |

## f = 3, m = 1 (ORBIT="3 1 3", 3e6 samples; the space is ~1e4 sets, so effectively exhaustive)

```
sl 5 37: N=4440 k=3 m=1 f=3 fix=5 samples=3000000 min=924 p1=924 p10=966 median=1950 mean=3930.84 var=9160497.8 mu=54.57 time=32.9
sl 5 43: N=5160 k=3 m=1 f=3 fix=5 samples=3000000 min=1686 p1=1686 p10=1914 median=2796 mean=4958.04 var=10039116.9 mu=117.17 time=32.6
psl 11 7: N=4620 k=3 m=1 f=3 fix=5 samples=3000000 min=186 p1=219 p10=324 median=1224 mean=2832.79 var=8958814.4 mu=67.40 time=76.4
sl 17 1: N=4896 k=3 m=1 f=3 fix=17 samples=3000000 min=144 p1=360 p10=696 median=2096 mean=2713.20 var=4405574.9 mu=90.65 time=83.6
psl 9 13: N=4680 k=3 m=1 f=3 fix=8 samples=3000000 min=258 p1=258 p10=324 median=822 mean=2401.34 var=9290313.3 mu=72.08 time=86.3
pgl 5 43: N=5160 k=3 m=1 f=3 fix=5 samples=3000000 min=972 p1=972 p10=1008 median=1788 mean=3162.42 var=8010325.3 mu=117.17 time=19.0
sl 9 7: N=5040 k=3 m=1 f=3 fix=17 samples=3000000 min=96 p1=150 p10=294 median=1456 mean=3199.73 var=12351015.4 mu=104.58 time=54.3
pgl 9 7: N=5040 k=3 m=1 f=3 fix=8 samples=3000000 min=120 p1=183 p10=246 median=5055 mean=4380.28 var=11689099.5 mu=104.58 time=57.5
```
