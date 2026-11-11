# c14: hole anatomy at (d,D) = (5,13), h = 6

Setup: random symmetric S (ORBIT "3 1 2": e, one alpha-fixed generator, one alpha-orbit of size 3), RANDORB samples
(300 per group, no search). anat.c is haar_big0.c plus a HOLESFILE dump (uncovered elements of samples with cost <= 20000).
classify.py tallies holes by class. lambda = W/N with W = 22,369,621 (d=5, D=13), N = |G| (vertices = 2N).
Entries count both sides (A and B), so "per element" rates are per side-element pair, roughly half per side.

## Cost statistics (RANDORB, 300 random S)  [stats_*.txt]
| group | N | lambda | mu (pick) | min | median | mean |
|---|---|---|---|---|---|---|
| SL(2,113) x Z1 | 1.44e6 | 15.50 | 0.27 | 0 | 36 | 3.8e4 |
| SL(2,61) x Z7 | 1.59e6 | 14.08 | 1.22 | 0 | 34 | 4.4e5 |
| SL(2,37) x Z31 | 1.57e6 | 14.26 | 1.01 | 0 | 96 | 2.6e5 |
| SL(2,53) x Z13 | 1.93e6 | 11.56 | 18.4 | 15222 | 87322 | 7.6e5 |
| SL(2,29) x Z97 | 2.36e6 | 9.47 | 182.8 | 11130 | 25104 | 1.7e5 |
| PSL(2,151) x Z1 | 1.72e6 | 13.00 | 3.91 | 54 | 256 | 7.8e4 |
| PSL(2,79) x Z7 | 1.73e6 | 12.97 | 4.04 | 3 | 79 | 4.5e5 |
| PSL(2,47) x Z31 | 1.61e6 | 13.91 | 1.47 | 0 | 59 | 1.2e5 |
| PSL(2,31) x Z97 | 1.44e6 | 15.50 | 0.27 | 264 | 3066 | 2.5e5 |
| PSL(2,67) x Z13 | 1.95e6 | 11.44 | 20.9 | 24881 | 112047 | 9.1e5 |
Note: cost 0 occurs in some samples for the groups with mu ~1 (not saved; out=/dev/null). The median cost is 10-30 times
the pick.py mu (mu counts generic holes only).

## Holes per sample by class, low-cost samples (cost <= 40)  [classify_low.txt, classify_low2.txt]
Miss rate = entries / (samples x |class|). Fit c = lambda / ln(1/rate), i.e. rate = exp(-lambda/c).
| group | samples | -I (SL) per sample / rate / c | central(z!=0) per sample / rate / c | alpha-fixed per sample / rate / c | involution (PSL) per sample / rate / c | order4 (SL, trace 0) per sample / rate / c | other per sample / rate / c | total holes per sample |
|---|---|---|---|---|---|---|---|---|
| SL(2,61) x Z7 | 142 | 0.46 / 0.46 / 18.4 | 0.85 / 0.070 / 5.3 | 2.79 / 0.050 / 4.7 | - | 0.32 / 8.6e-5 / 1.5 | 11.6 / 7.3e-6 / 1.2 | 16.0 |
| SL(2,113) x Z1 | 151 | 0.20 / 0.20 / 9.6 | - | 8.61 / 0.077 / 6.0 | - | 0.16 / 1.2e-5 / 1.4 | 9.5 / 6.7e-6 / 1.3 | 18.5 |
| SL(2,37) x Z31 | 92 | 0.28 / 0.28 / 11.3 | 8.35 / 0.139 / 7.2 | 0.89 / 0.028 / 4.0 | - | 0.17 / 1.2e-4 / 1.6 | 10.2 / 6.5e-6 / 1.2 | 19.9 |
| PSL(2,79) x Z7 | 95 | - | 0.13 / 0.021 / 3.4 | 1.14 / 0.030 / 3.7 | 10.9 / 3.5e-3 / 2.3 | - | 14.5 / 8.4e-6 / 1.1 | 26.7 |
| PSL(2,47) x Z31 | 99 | - | 3.76 / 0.125 / 6.7 | 1.39 / 0.063 / 5.0 | 4.7 / 4.3e-3 / 2.6 | - | 12.3 / 7.7e-6 / 1.2 | 22.1 |

Class sizes: -I: 1; central(z!=0): 2(n-1) (SL), n-1 (PSL); order4 ~ p^2 (SL); involutions ~ p^2/2 (PSL);
alpha-fixed: 22-112 (z = 0). Generic "other" is about 1.5-1.6 million elements.
All-sample run for SL(2,61) x Z7 (no cost cutoff, 223 samples, printed only): 229k hole entries, generic class about
1000 per sample, so the mean is set by a few bad samples; the -I rate there is 0.43.
High-cost groups (SL 53x13, SL 29x97, PSL 151x1, PSL 31x97, PSL 67x13): not classified (time box; their samples
have cost in the thousands).

## Findings
1. -I (SL) is the single most-missed element: a hole in 20-46% of random S (rate exp(-lambda/c) with c = 9-18, far
   above the generic rate of ~1e-5). Its cost is small, though: 0.2-0.5 holes per sample out of 16-20.
2. Central elements with z != 0 (SL and PSL) fit c = 3-7 (the h = 6 model is roughly right). Their total grows with n:
   n = 31 gives 3.8-8.4 holes per sample, n = 7 gives 0.1-0.9. Small n is better.
3. PSL involutions (trace 0, z = 0; ~p^2/2 of them) are the main PSL cost: about 5-11 holes per sample, c ~ 2.3-2.6.
   SL order-4 elements (trace 0, ~p^2) are missed at 1e-4 per element (c ~ 1.5), so about 0.2-0.3 per sample.
   So the PSL shape is not better at D = 13: it has 22-27 holes per sample against 16-20 for SL at similar lambda.
4. The generic class is the bulk of the holes (about 10-15 per sample at lambda 13-15), and the miss rate per element
   is not a clean exp(-lambda). The fitted prefactor K = rate / exp(-lambda) is 3.6 (PSL 79x7), 9.5 (SL 61x7) and 35
   (SL 113x1). Holes are correlated (alpha-orbits of size 3, both sides), so cost is not Poisson in mu.
5. Recommendation for (9,13) (N ~ 4e9, lambda ~ 16-26): keep SL(2,p) x Z_n with small n (n = 1 or 7) and avoid PSL.
   -I costs one hole, and at lambda ~ 20 it is missed with probability ~0.3 (extrapolated), so it is not fatal.
   Candidates, with lambda from W(9,13) = 78,536,544,841: SL(2,827) x Z7 (N = 3.96e9, lambda 19.8),
   SL(2,1583) x Z1 (N = 3.97e9, lambda 19.8), PSL(1039) x Z7 (N = 3.93e9, lambda 20.0) as the control.
   Compare them by RANDORB (min and median cost) before any annealing. Extrapolation from lambda 13-15 is unverified.
