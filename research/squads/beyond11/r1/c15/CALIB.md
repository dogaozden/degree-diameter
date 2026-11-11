# c15: size-law calibration at D >= 10 from lab run logs

Analysis only (no search run, score 0). Scripts in this folder: `parse_logs.py` (logs -> `runs.csv`),
`analyze.py` (KM table, AFT attempt), `fit_within.py` (logistic models), `predict.py` (mu -> group-order caps).

## Data
- Sources: 50 logs under `research/frontier/beyond/runs/` (git blob of `origin/claude/new-cells-beyond-etos3t`),
  108 logs under `research/structured/runs/`, 5 logs under `research/frontier/beyond11/runs/` (this job).
  174 log entries parsed, 161 unique runs (duplicates removed), 128 with k = 3 orbits (the main case), 97 of those solved.
- mu is recomputed as N exp(-W/N) with W from `pick.py`; it matches the logged mu on all 54 logs that print it.
- A run is "solved" if its RESULT line has best = 0. Unsolved runs (budget or time stop, or killed) are right-censored
  at their last eval count. Full table: `runs.csv` (columns src, file, d, D, group, N, mu, orbit, start, best, evals, time, status, solved).

## Solve probability by mu (k = 3, Kaplan-Meier, censoring as above)
| mu bin | runs | solved | median evals (solved) | P(<=300) | P(<=1000) | P(<=3000) |
|---|---|---|---|---|---|---|
| 2.5-3.5 | 14 | 14 | 5 | 0.93 | 0.93 | 1.00 |
| 3.5-4.5 | 2 | 2 | 430 | 0.50 | 1.00 | 1.00 |
| 4.5-6 | 9 | 5 | 21 | 0.56 | 0.56 | 0.56 |
| 6-9 | 6 | 6 | 57 | 1.00 | 1.00 | 1.00 |
| 9-15 | 22 | 20 | 385 | 0.41 | 0.64 | 0.77 |
| >= 15 | 71 | 48 | 17609 | 0.00 | 0.10 | 0.20 |

## Logistic models of P(solved within E | mu), conditional labels (runs stopped before E without solving are dropped)
- E = 300, n = 126 (36 solved): logit P = 4.28 - 2.17 ln mu. P = 0.5 at mu = 7.2, P = 0.8 at mu = 13.6.
- E = 1000, n = 126 (49 solved): logit P = 4.15 - 1.80 ln mu. P = 0.5 at mu = 10.0, P = 0.8 at mu = 21.6.
- Start cost is strong evidence beyond mu: adding ln(start+1) raises loglik from -45.4 to -30.0 (E = 300) and from -59.8
  to -39.2 (E = 1000). Coefficients: E = 300: 9.67 - 1.78 ln mu - 1.90 ln(start+1); E = 1000: 9.15 - 0.96 ln mu - 1.99 ln(start+1).
- Start cost is measured after the first eval, so it works as an early-stop rule. For mu >= 8 (conditional labels):
  start < 10: P(solve <= 1000) = 1.00 (n = 3); 10-30: 0.76 (n = 21); 30-100: 0.08 (n = 36); >= 100: 0.03 (n = 35).
- Median start cost by mu: 12 (mu < 4), 19 (4-8), 28 (8-12), 25 (12-16), 66 (16-25), 164 (>= 25).
- The lognormal AFT fit of ln(evals) on ln mu was rejected: sigma = 4.8, residuals strongly cell-dependent. Not used.

## D >= 11 runs (the target cells), k = 3, mu <= 16
| d | D | group | mu | start | evals | solved |
|---|---|---|---|---|---|---|
| 10 | 12 | PSL(2,193) x Z487 | 3.05 | 15 | 5 | yes |
| 11 | 12 | SL(2,307) x Z181 | 3.20 | 3 | 5 | yes |
| 6 | 11 | PSL(2,53) x Z13 | 3.20 | 42 | 9 | yes |
| 11 | 11 | SL(2,251) x Z37 | 3.31 | 2 | 53 | yes |
| 9 | 11 | PSL(2,197) x Z19 | 3.34 | 27 | 1269 | yes |
| 12 | 11 | SL(2,263) x Z79 | 3.43 | 6 | 5 | yes |
| 6 | 11 | PSL(2,47) x Z19 | 4.13 | 24 | 41 | yes |
| 9 | 12 | SL(2,199) x Z67 | 4.44 | 6 | 430 | yes |
| 8 | 12 | SL(2,163) x Z31 | 4.63 | 12 | 21 | yes |
| 10 | 11 | SL(2,193) x Z31 | 5.05 | 6 | 5 | yes |
| 6 | 12 | SL(2,47) x Z43 | 5.12 | 19 | 9 | yes |
| 7 | 11 | SL(2,23) x Z433 | 5.35 | 115 | 1391 | no (best 31) |
| 7 | 12 | PSL(2,163) x Z13 | 5.40 | 30 | 21 | yes |
| 9 | 11 | PSL(2,199) x Z19 | 5.70 | 69 | 1835 | no (best 3) |
| 8 | 11 | SL(2,89) x Z31 | 6.16 | 32 | 113 | yes |
| 7 | 11 | SL(2,43) x Z67 | 6.42 | 18 | 25 | yes |
| 6 | 12 | SL(2,71) x Z13 | 9.32 | 11 | 65 | yes |
| 6 | 11 | PSL(2,31) x Z73 | 14.30 | 1524 | 122353 | yes (slow) |
| 6 | 12 | SL(2,43) x Z61 | 16.48 | 57949 | 24689 | no (best 2) |
| 4 | 12 | PSL(2,11) x Z39 | 0.85 | 21 / 25728 | 1.1e7 each | no (d = 4: f = 1 leaves one orbit, structurally tight) |
Read: at D >= 11 and mu <= 9.3 (d >= 6), 16 of 19 solved within 1000 evals; the three misses had start cost 69-115 or 1269 evals.
The D >= 11 indicator in the logistic fit is negative (-0.9 at E = 300, -1.2 at E = 1000) but rests on 23 labels, mostly driven by
the two mu > 14 misses, so it is not trusted.

## Prediction (largest mu likely to solve)
- Within 300 evals: mu ~ 7 at P = 0.5 (all data); ~ 6 to 7 at D >= 11 (small sample). P = 0.8 only at mu ~ 13 (low confidence).
- Within 1000 evals: mu ~ 10 at P = 0.5; ~ 7 to 10 at D >= 11. P = 0.8 only near mu ~ 20 (low confidence).
- Practical rule with the start cost: at mu >= 8, abandon a run whose first start cost is > 30; the rest solve at 0.76 within 1000.

Group-order caps from mu (N exp(-W/N) = mu, `predict.py`). mu changes steeply with N (d ln mu / d ln N = 1 + W/N ~ 20 here),
so a 2 % change in N moves mu by about 50 %:
| cell | W | N cap at mu 7 (300 evals, P=0.5) | N cap at mu 10 (1000 evals, P=0.5) | 2N at mu 10 | groups with mu in [7,10] (pick.py, k=3) |
|---|---|---|---|---|---|
| (11,11) | 1.111e10 | 6.08e8 | 6.19e8 | 1.24e9 | 38 |
| (12,11) | 2.853e10 | 1.49e9 | 1.51e9 | 3.03e9 | 45 |
| (13,11) | 6.755e10 | 3.38e9 | 3.44e9 | 6.87e9 | 65 |
| (14,11) | 1.493e11 | 7.20e9 | 7.32e9 | 1.46e10 | 81 |
| (11,12) | 1.111e11 | 5.43e9 | 5.52e9 | 1.10e10 | 59 |
Current solved mu: (11,11) 3.31 (N 5.85e8), (12,11) 3.43, (11,12) 3.20. Director runs in progress: (13,11) at mu 3.15 and (14,11) at mu 3.06.
So the mu 7 to 10 band is open at every cell listed; the cap of the 300-eval band is about 2x the current record mu.

## Caveats
- Logs mix code versions, orbit forms (k = 2, 3, 5; f = 0..3) and search budgets. Only k = 3 is fitted; the runs with
  START chaining are not separated. Some censored runs have time limits, not eval limits.
- Solves at mu > 15 exist for D <= 10 (e.g. 20 to 60 at D = 7 to 9), so mu is only a rough scale across cells.
  The fits rest on about 40 solved runs at mu >= 8 and only 16 at D >= 11 with mu <= 9.3.
