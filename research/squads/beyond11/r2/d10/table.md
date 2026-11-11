# d10 table: n-dependence at odd D (budget 40 s per run, ORBIT as in the card, K=4, THREADS=1)

mu is the size law from haar_big0 (lambda ~ 13 at (11,9), ~ 15 at (13,9)); mu was matched only approximately (see notes).

## (11,9), ORBIT "3 3 2" (Delta 11)
| group | N | mu | seed 1 best (evals) | seed 2 best (evals) | seed 3 best (evals) |
|---|---|---|---|---|---|
| PSL(2,257) x Z_1 | 8,487,168 | 17.50 | 107 (133) | 80 (149) | 104 (145) |
| PSL(2,131) x Z_7 | 7,867,860 | 5.79 | 3 (401) | 6 (430) | 7 (418) |
| PSL(2,83) x Z_31 | 8,861,412 | 31.77 | 34 (514) | 86 (461) | 42 (486) |
| PSL(2,31) x Z_547 | 8,139,360 | 9.59 | 12 (923) | 18 (968) | 20 (1019) |
| SL(2,107) x Z_7 | 8,574,552 | 20.21 | 14 (349) | 12 (378) | not run |
| SL(2,199) x Z_1 | 7,880,400 | 5.93 | 2 (177, unsolved) | SOLVED (13 evals, 2.7 s) | SOLVED (85 evals, 18 s) |

Solutions of SL(2,199) x Z_1 (seeds 2 and 3) pass haarcheck_gen: VALID, diameter 9, 11-regular, 15,760,800 vertices.

## (13,9), ORBIT "3 4 1" (Delta 13)
| group | N | mu | seed 1 best (evals) | seed 2 best (evals) | seed 3 best (evals) |
|---|---|---|---|---|---|
| PSL(2,401) x Z_1 | 32,240,400 | 15.48 | 87 (45) | 111 (41) | 113 (45) |
| PSL(2,53) x Z_433 | 32,220,396 | 15.33 | 24 (185) | 12 (169) | 21 (193) |
| PSL(2,127) x Z_31 | 31,747,968 | 12.16 | 12 (157) | 6 (269) | 6 (245) |

## Notes
- n = 509 is not usable with k = 3 (509 = 2 mod 3, no order-3 action on Z_509); n = 547 (= 1 mod 3, prime) used instead.
- n = 127 was not run at (11,9) (time). The best mu-matched PSL options at (11,9) are far from mu 15 (mu is very steep in N near 8e6), so
  the PSL n-series there is only roughly matched; the SL n = 1 point (mu 5.9) is not matched to the PSL n = 1 point (mu 17.5).
- Speed confound: evals per 40 s differ by 4x between n = 1 and n = 433 at (13,9) (about 1 s vs 0.2 s per eval, row layout), so
  costs are compared at equal wall time, not equal evals.
- Prediction test: at (13,9) with mu matched (~15), n = 1 is WORSE than n = 433 (best 87-113 vs 12-24). This contradicts the
  "small n best at odd D" prediction, unless the speed confound dominates. At (11,9), the small-n SL group (2 central elements
  +-I) solved twice while the PSL n = 7 group (7 central elements) at similar mu did not solve in 3 seeds (best 3-7).
  That is consistent with fewer central elements being easier, but SL vs PSL and n are confounded here.
