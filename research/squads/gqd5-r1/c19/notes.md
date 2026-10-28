# c19: whole-graph repair of one non-friendly transition (all levels type H, Q(4,5), no hubs)

Setup. G = gqlib.Q4(5) (156 points, 156 lines). Levels all type H (A = points, B = lines); every transition is
non-friendly. Transition t0 = (0,1) (level 0 -> level 1). R = random s-subset of points on t0, M_t0 = random bijection,
R freed. All other matchings are random bijections, then annealed (swap two images in one matching, SA on the number of
ordered vertex pairs at distance > 5 in the WHOLE graph, no hubs). Distances: bit-parallel BFS in c19/bad.c (cross-checked
against plain BFS). Two-level count: repair.brute_bad(G,'H','H',M_t0,R). (E1)-(E3): repair.exact_conditions.

## Bad pairs, two-level vs whole graph (random other matchings, before annealing; mean of 3 draws unless noted)

r=2 (5 levels, degree 8, n=1560)
| s=|R| | whole | two-level |
|---|---|---|
| 1 | ~52 | ~82 |
| 2 | ~122 | ~180 |
| 5 | ~272 | ~442 |
| 8 | ~443 | ~729 |
| 20 | ~1298 | ~2075 |
| 50 | ~4050 | ~6650 |
| 80 | ~8570 | ~13980 |

r=3 (7 levels, degree 9, n=2184)
| s=|R| | whole | two-level |
|---|---|---|
| 1 | ~19 | ~88 |
| 2 | ~40 | ~167 |
| 5 | ~99 | ~443 |
| 8 | ~155 | ~731 |
| 20 | ~437 | ~2066 |
| 50 | ~1330 | ~6627 |
| 80 | ~2893 | ~13961 |

So the other levels already cut the bad pairs by a factor of about 4 to 5 before annealing. The two-level count is
0 exactly when (E1)-(E3) hold (checked by brute force in the earlier tests); here it is never 0 for s >= 1.

## Annealing results (other matchings only, M_t0 and R fixed; apsp-verified where marked)

| r | s | result | apsp |
|---|---|---|---|
| 2 | 1 | 0 bad (seed 2, 20000 steps) | VALID (d=8, D=5) |
| 2 | 2 | 0 bad (seed 12, 25000 steps) | VALID |
| 2 | 8 | 0 bad (seed 18) | VALID |
| 2 | 16 | not reached: best 42 after 25000 steps (seed 46) | - |
| 3 | 8 | 0 bad (seed 48) | VALID (d=9, D=5) |
| 3 | 16 | 0 bad (seed 56, 25000 steps max) | VALID (d=9, D=5, n=2184) |

For each valid state, R violates (E2) and (E3) of Theorem E (and (E1) fails in some random draws at larger s). The two-level
test therefore says each of these transitions is NOT repairable inside its own two levels (two-level bad pairs 77 to 1574),
but the whole level graph is repaired by the other matchings. So with many levels, (E1)-(E3) are not necessary for
diameter 5 in this construction. Score (largest |R| on one non-friendly transition with the whole graph of diameter 5): 16
(r=3, n=2184, degree 9). It is not yet known whether 24 or 32 works; r=2 stalled at 16 in the time budget.

Files: best.edges = r=3, s=16 graph (edge list, apsp-checked: RESULT VALID d=9 D=5 n=2184).
State pickles (M, R, t0): state_r3_s16_seed56.pkl, state_r3_s8_seed48.pkl, state_r2_s8_seed18.pkl, state_r2_s2_seed12.pkl,
state_r2_s1_seed2.pkl. Scripts: common.py (graph builder, C bad-pair counter via libbad.so), anneal.py (SA), verify.py
(apsp check), summ.py (two-level vs whole, E1-E3). Command for the best: python3 anneal.py 3 16 25000 56 1.0.
