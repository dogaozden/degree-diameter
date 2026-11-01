# e14: fit of the odd-D hole model at (d,D) = (11,9), ORBIT "3 3 2", RANDORB=20

Setup: W = 111111111 (odd-D formula), lambda = W/N, h = 4, mu = N exp(-lambda). 22 groups (11 SL, 11 PSL), seed 1, random
symmetric S (20 samples each). Cost = uncovered elements on both sides, so measured per side = cost/2. Measured value =
median over the 20 samples (tails are heavy). Raw logs: ro_<group>.txt / ro_<group>.err. fit.py computes everything from the logs.
Model terms per side: I e^(-l/2) + C e^(-l/4) + F e^(-l/3), I = involutions, C = central elements (SL: 2n, PSL: n),
F = alpha-fixed elements = |C_G(g)| (SL: p-1 if p = 1 mod 3, else p+1; PSL: half). F brute-checked for p <= 31 (verify_fixed.py).
The PSL I term uses I = p(p+eps)/2, eps = +1 if p = 1 mod 4, else -1. The +-I central elements are also alpha-fixed, so C and F
overlap in the card's formula.

| group | N | lambda | mu | I | C | F | I e^-l/2 | C e^-l/4 | F e^-l/3 | pred side, card (mu/3) | pred side, mu | meas side (median) | meas/pred(mu) | max cost |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| SL(2,199) x Z1 | 7880400 | 14.10 | 5.93 | 1 | 2 | 198 | 0.00 | 0.06 | 1.80 | 3.84 | 7.79 | 8.5 | 1.09 | 48 |
| PSL(2,251) x Z1 | 7906500 | 14.05 | 6.23 | 31375 | 1 | 126 | 27.86 | 0.03 | 1.16 | 31.13 | 35.29 | 46.8 | 1.32 | 574 |
| PSL(2,131) x Z7 | 7867860 | 14.12 | 5.79 | 8515 | 7 | 66 | 7.30 | 0.21 | 0.60 | 10.04 | 13.90 | 18.8 | 1.35 | 69 |
| PSL(2,107) x Z13 | 7962084 | 13.96 | 6.93 | 5671 | 13 | 54 | 5.29 | 0.40 | 0.52 | 8.51 | 13.13 | 13.5 | 1.03 | 55 |
| SL(2,29) x Z331 | 8063160 | 13.78 | 8.35 | 1 | 662 | 30 | 0.00 | 21.12 | 0.30 | 24.21 | 29.78 | 57.5 | 1.93 | 1230 |
| SL(2,43) x Z103 | 8184792 | 13.58 | 10.41 | 1 | 206 | 42 | 0.00 | 6.92 | 0.46 | 10.84 | 17.78 | 21.0 | 1.18 | 23550 |
| PSL(2,53) x Z109 | 8110908 | 13.70 | 9.11 | 1431 | 109 | 27 | 1.52 | 3.55 | 0.28 | 8.38 | 14.46 | 21.0 | 1.45 | 186 |
| SL(2,37) x Z157 | 7946712 | 13.98 | 6.73 | 1 | 314 | 36 | 0.00 | 9.52 | 0.34 | 12.11 | 16.59 | 25.0 | 1.51 | 4980 |
| SL(2,29) x Z307 | 7478520 | 14.86 | 2.64 | 1 | 614 | 30 | 0.00 | 14.96 | 0.21 | 16.06 | 17.82 | 30.0 | 1.68 | 36156 |
| PSL(2,59) x Z73 | 7494180 | 14.83 | 2.73 | 1711 | 73 | 30 | 1.03 | 1.79 | 0.21 | 3.95 | 5.77 | 6.2 | 1.08 | 54 |
| SL(2,41) x Z109 | 7507920 | 14.80 | 2.81 | 1 | 218 | 42 | 0.00 | 5.39 | 0.30 | 6.63 | 8.50 | 11.0 | 1.29 | 108 |
| SL(2,37) x Z151 | 7643016 | 14.54 | 3.71 | 1 | 302 | 36 | 0.00 | 7.97 | 0.28 | 9.49 | 11.97 | 18.5 | 1.55 | 288 |
| PSL(2,43) x Z193 | 7668276 | 14.49 | 3.91 | 903 | 193 | 21 | 0.64 | 5.16 | 0.17 | 7.27 | 9.88 | 17.0 | 1.72 | 666720 |
| PSL(2,41) x Z223 | 7680120 | 14.47 | 4.00 | 861 | 223 | 21 | 0.62 | 5.99 | 0.17 | 8.12 | 10.78 | 13.5 | 1.25 | 672 |
| SL(2,43) x Z97 | 7708008 | 14.42 | 4.23 | 1 | 194 | 42 | 0.00 | 5.28 | 0.34 | 7.04 | 9.86 | 9.5 | 0.96 | 54 |
| PSL(2,37) x Z307 | 7769556 | 14.30 | 4.78 | 703 | 307 | 18 | 0.55 | 8.60 | 0.15 | 10.90 | 14.09 | 17.2 | 1.22 | 47142 |
| SL(2,29) x Z349 | 8501640 | 13.07 | 17.93 | 1 | 698 | 30 | 0.00 | 26.60 | 0.38 | 32.96 | 44.91 | 92.0 | 2.05 | 1668906 |
| SL(2,107) x Z7 | 8574552 | 12.96 | 20.21 | 1 | 14 | 108 | 0.00 | 0.55 | 1.44 | 8.72 | 22.20 | 31.0 | 1.40 | 144 |
| SL(2,43) x Z109 | 8661576 | 12.83 | 23.25 | 1 | 218 | 42 | 0.00 | 8.82 | 0.58 | 17.16 | 32.66 | 51.0 | 1.56 | 452 |
| PSL(2,97) x Z19 | 8669472 | 12.82 | 23.55 | 4753 | 19 | 48 | 7.83 | 0.77 | 0.67 | 17.12 | 32.82 | 41.2 | 1.26 | 135 |
| SL(2,29) x Z367 | 8940120 | 12.43 | 35.79 | 1 | 734 | 30 | 0.00 | 32.83 | 0.48 | 45.24 | 69.10 | 131.0 | 1.90 | 118290 |
| PSL(2,37) x Z349 | 8832492 | 12.58 | 30.39 | 703 | 349 | 18 | 1.30 | 15.03 | 0.27 | 26.74 | 47.00 | 95.2 | 2.03 | 2007666 |

## Fit (medians per side; 100 samples (seed 2) for 12 groups, 20 samples (seed 1) for the rest; F term dropped, see below)

Refit with the 100-sample medians (`ro100_*.err`, fit.py and the inline check; the table above is from the 20-sample logs):

| group | samples | lambda | mu | I e^-l/2 | C e^-l/4 | median side (100-sample) | meas / pred(mu) |
|---|---|---|---|---|---|---|---|
| SL(2,29) x Z367 | 100 | 12.43 | 35.79 | 0.00 | 32.83 | 155.5 | 2.25 |
| PSL(2,37) x Z349 | 20 | 12.58 | 30.39 | 1.30 | 15.03 | 95.2 | 2.03 |
| SL(2,29) x Z349 | 100 | 13.07 | 17.93 | 0.00 | 26.60 | 85.0 | 1.89 |
| SL(2,29) x Z331 | 100 | 13.78 | 8.35 | 0.00 | 21.12 | 53.0 | 1.78 |
| SL(2,43) x Z109 | 100 | 12.83 | 23.25 | 0.00 | 8.82 | 48.0 | 1.47 |
| SL(2,37) x Z157 | 100 | 13.98 | 6.73 | 0.00 | 9.52 | 24.0 | 1.45 |
| PSL(2,53) x Z109 | 100 | 13.70 | 9.11 | 1.52 | 3.55 | 20.5 | 1.42 |
| PSL(2,251) x Z1 | 100 | 14.05 | 6.23 | 27.86 | 0.03 | 50.0 | 1.42 |
| SL(2,43) x Z103 | 100 | 13.58 | 10.41 | 0.00 | 6.92 | 24.5 | 1.38 |
| SL(2,199) x Z1 | 100 | 14.10 | 5.93 | 0.00 | 0.06 | 11.0 | 1.41 |
| SL(2,43) x Z97 | 100 | 14.42 | 4.23 | 0.00 | 5.28 | 13.0 | 1.32 |
| PSL(2,97) x Z19 | 100 | 12.82 | 23.55 | 7.83 | 0.77 | 44.0 | 1.34 |
| PSL(2,107) x Z13 | 100 | 13.96 | 6.93 | 5.29 | 0.40 | 16.0 | 1.22 |
| SL(2,107) x Z7 | 100 | 12.96 | 20.21 | 0.00 | 0.55 | 28.0 | 1.26 |

Least squares, measured ~ a mu + b I e^-l/2 + c C e^-l/4 (22 groups, F dropped): a = 1.69, b = 1.29, c = 2.20.
(Earlier 20-sample fit: a = 1.59, b = 1.22, c = 2.13. Groups with mu <= 10 only: a = 1.07, b = 1.43, c = 1.96.)

- Card's generic term mu/3 is wrong: with it the model is too low by 2.5x on average. Cost counts elements, so the generic
  uncovered count per side is mu. With mu the model underpredicts by about 1.3-1.5x for mu up to 25 and by about 2.0-2.3x at mu
  30-36. So the generic term grows faster than mu at higher mu.
- Involution term: about 1.3x exp(-lambda/2) (PSL groups with mu 6-24 are 1.2-1.4x). SL(2,199) x Z1 with 100 samples: median side 11 (ratio 1.41); its zero-cost graph is verified.
- Central term: about 2x exp(-lambda/4); the central-heavy SL groups (n = 331-367) are the worst (1.8-2.3x).
- Alpha-fixed term: not fitted (F is 15-40 per group, lambda barely moves, and the free fit gave an unstable sign).
- Ranking of shapes is right: the card's model ranks groups correctly (SL with large n and the mu-driven groups are the
  hardest), but the absolute rates are about 1.3-2x the card's.

## Caveats

- Heavy tails: some samples are huge (SL(2,29) x Z349 max 1.67e6; PSL(2,37) x Z349 max 2.0e6; PSL(2,37) x Z307 4.7e4;
  SL(2,29) x Z367 1.2e5; SL(2,43) x Z103 2.4e4). These look like S that do not generate G x Z_n (disconnected graphs), not
  like the hole model. Medians are used; not investigated further.
- lambda varies only 12.4-14.9 (mu is tied to N), so the test separates terms weakly. n values: 1, 7, 13, 19, 73, 97, 103, 109, 151, 157, 193, 223, 307, 331, 349, 367 (see the table).

## Side result (zero-cost S found)

- SL(2,199) x Z1, N = 7880400: zero-cost S on samples 7 and 8. haarcheck_gen VALID (11-regular, 15760800 vertices, diameter 9).
  File: research/squads/beyond11/r3/e14/e14_sol_sl_199_1.sol
- PSL(2,59) x Z73 (N = 7494180), SL(2,41) x Z109 (N = 7507920), SL(2,43) x Z97 (N = 7708008): zero-cost S, NOT checked
  (files e14_sol_psl_59_73.sol, e14_sol_sl_41_109.sol, e14_sol_sl_43_97.sol). The verified SL(2,199) graph is the largest (2N = 15760800).
