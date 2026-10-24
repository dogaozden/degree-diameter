# B7 plan: (11,10) orbit runs, predicted frontier at 4 single-thread core-hours

Planning only (heavy budget 0). Every number below is a model prediction from `plan_b7*.py` in this folder.

## Model used

- W = 1,111,111,111 (= 11 · (1 + 10² + 10⁴ + 10⁶ + 10⁸)), N = |G| = |H|·n, vertices = 2N, λ = W/N, μ = N e^(−λ).
- μ_A = (μ − F e^(−λ))/k + (F − 1) e^(−λ/k), F = |Fix| including e. Conjugation: the torus of order p − 1 or p + 1
  (whichever k divides), halved for PSL. Frobenius: F = 6 for SL(2,32), F = 12 for PSL(2,243).
- evals = 1e5 · exp((μ_A − 13)/2). Seconds per eval = 0.25 (k = 5) or 0.09 (k = 3), scaled by N/75e6. Hours = evals · s / 3600.
- k = 5: f = 1 (S = e + two orbits of size 5). k = 3: f = 2 (S = e, t + three orbits of size 3).
- Candidates: all primes p with k | p−1 or k | p+1, all n with every prime factor ≡ 1 mod k, N in [76M, 80M]. 12,978 candidates.

**One addition to the card model (class saturation).** For G = H × Z_n every walk's Z-part is a fixed linear form in the
orbit Z-values, so walks with the same exponent vector share one Z-value. There are at most K' distinct exponent vectors
(K'_5 = 3,317,445 for k = 5, K'_3 = 1,462,563 for k = 3). With x = W/(K' |H|), the effective exponent is
λ_eff = λ (1 − e^(−x))/x, and μ_A is recomputed with λ_eff. This uses uniform class multiplicities, which is the most
favourable case, so the correction is a lower bound on the loss. Runs with x > 0.03 are not ranked.

## 1. Largest graph each family should reach in 4 core-hours

| family | k | card model, raw (no class check) | class-safe (x ≤ 0.03), corrected | corrected hours |
|---|---|---|---|---|
| conj PSL(2,p) × Z_n | 3 | 153.99M, PSL(2,5) × Z1283257 (x = 12.7: excluded) | 152.96M, PSL(2,89) × Z217 | 2.61 (raw 2.36) |
| conj SL(2,p) × Z_n | 3 | 153.97M, SL(2,5) × Z641557 (x = 6.3: excluded) | 153.17M, SL(2,59) × Z373 | 3.42 (raw 2.87) |
| conj PSL(2,p) × Z_n | 5 | 157.33M, PSL(2,11) × Z119191 (x = 0.51: excluded) | 155.05M, PSL(2,41) × Z2251 | 2.65 (raw 1.89) |
| conj SL(2,p) × Z_n | 5 | 157.06M, SL(2,11) × Z59491 (x = 0.25: excluded) | 154.98M, SL(2,29) × Z3181 | 3.96 (raw 2.42) |
| Frobenius SL(2,32) × Z_n | 5 | 155.89M, SL(2,32) × Z2381 | 155.89M, SL(2,32) × Z2381 | 2.78 (raw 1.90) |
| Frobenius PSL(2,243) × Z_n | 5 | no run ≤ 4 h: only n = 11 fits, N = 78.9M (157.8M) | none | 6.56 (over budget) |

Best k = 3 is about 153.2M, against about 155.9M for k = 5. The k = 3 runs are cheaper per evaluation (0.09 s) but need
μ_A ≈ 13.6 at their frontier, and their f = 2 fixed letter is not in the μ_A formula.

## 2. Ten best runs to do (x ≤ 0.03, corrected hours ≤ 4, ranked by vertices)

| # | group | k | N | vertices | μ | μ_A raw | μ_A corr | evals raw | evals corr | hours raw | hours corr | x | checker |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | SL(2,32) × Z2381, Frobenius | 5 | 77,944,416 | 155,888,832 | 50.2 | 10.33 | 11.09 | 2.6e4 | 3.9e4 | 1.90 | 2.78 | 0.010 | none for GF(32) |
| 2 | SL(2,32) × Z2371, Frobenius | 5 | 77,617,056 | 155,234,112 | 47.1 | 9.70 | 10.42 | 1.9e4 | 2.8e4 | 1.38 | 1.98 | 0.010 | none for GF(32) |
| 3 | PSL(2,41) × Z2251 | 5 | 77,524,440 | 155,048,880 | 46.2 | 10.33 | 11.01 | 2.6e4 | 3.7e4 | 1.89 | 2.65 | 0.010 | haarcheck_psl |
| 4 | SL(2,29) × Z3181 | 5 | 77,489,160 | 154,978,320 | 45.9 | 10.83 | 11.81 | 3.4e4 | 5.5e4 | 2.42 | 3.96 | 0.014 | hcsl |
| 5 | PSL(2,71) × Z431 | 5 | 77,114,520 | 154,229,040 | 42.6 | 10.43 | 10.55 | 2.8e4 | 2.9e4 | 1.97 | 2.10 | 0.002 | haarcheck_psl |
| 6 | SL(2,31) × Z2591 | 5 | 77,108,160 | 154,216,320 | 42.6 | 10.14 | 10.88 | 2.4e4 | 3.5e4 | 1.71 | 2.47 | 0.011 | hcsl |
| 7 | PSL(2,59) × Z751 | 5 | 77,097,660 | 154,195,320 | 42.5 | 10.12 | 10.33 | 2.4e4 | 2.6e4 | 1.69 | 1.88 | 0.003 | haarcheck_psl |
| 8 | SL(2,32) × Z2351, Frobenius | 5 | 76,962,336 | 153,924,672 | 41.3 | 8.55 | 9.18 | 1.1e4 | 1.5e4 | 0.77 | 1.06 | 0.010 | none for GF(32) |
| 9 | PSL(2,31) × Z5171 | 5 | 76,944,480 | 153,888,960 | 41.2 | 9.02 | 10.48 | 1.4e4 | 2.8e4 | 0.97 | 2.03 | 0.023 | haarcheck_psl |
| 10 | PSL(2,29) × Z6311 | 5 | 76,867,980 | 153,735,960 | 40.6 | 8.89 | 10.69 | 1.3e4 | 3.1e4 | 0.91 | 2.24 | 0.027 | haarcheck_psl |

- All ten lie within 1.4% of each other in vertices, so the choice among them matters less than the checker status.
  Rows 3–7, 9 and 10 have a checker in `research/structured/tools` (haarcheck_psl for PSL, hcsl for SL, prime p). Rows 1, 2
  and 8 need a GF(2^5) checker first. haar_sym has an `AFROB` option for these groups, which is untested here.
- Row 4 sits at the 4 h edge in corrected hours (3.96). Row 1 is at 2.78 and the others have more headroom.
- Suggested order: row 3 (PSL(2,41) × Z2251, `ORBIT="5 2 1"`, prime p, checker ready), then rows 5, 7, 6, 4.
- Excluded from the raw top: PSL(2,11) × Z119191 (157.33M), SL(2,11) × Z59491 (157.06M), PSL(2,19) × Z22961 (157.05M).
  Their |H| is 660–3420. The corrected μ is 5 to 21 times the card value for the p = 11 runs and 2 times for PSL(2,19),
  which puts them far outside 4 h.

## 3. Main uncertainty

The largest uncertainty is whether the Poisson law holds when Z_n is large against H. Only the solved (11,10) records
(SL(2,79) × Z133 and PSL(2,149) × Z43, |H| ≥ 4.9·10^5, x < 0.002) test it, and both are far from the regime that decides
the ranking. For the top-10 runs the class correction raises μ by 3 to 22% (rows 9 and 10 most), which moves their hours by up
to 2.5×. For the excluded p = 11 families it is a factor 5 to 21 in μ, so the card's raw top is not believable until a light test
confirms or rejects the correction. A cheap one: random S on A5 × Z_13200 at (11,8). There x = 0.23, the same as SL(2,11) at
(11,10), and λ = 14.03. The uncovered mean should be 0.64 without the correction and 2.9 with it, which a few hundred samples
(about 0.1 s each in C) can separate. The second uncertainty is the effort law's scatter: its residual sd is 1.65 in ln(evals), about a factor
5, with mean residual −0.39 on the calibration set. A run predicted at 2–4 h therefore finishes inside 4 h with roughly
60–75% probability. Smaller items: the cost per eval is assumed linear in N and equal across families (GF(32) arithmetic may
differ), and μ_A ignores the f = 2 fixed letter t of the k = 3 family.

## Files (all in this folder)

- `plan_b7.py`: card model over all candidates, per-family frontier (`plan_b7_out.txt`).
- `plan_b7_struct.py`: class counts K' and the saturation ratio at each |H| (`plan_b7_struct_out.txt`).
- `plan_b7_corr.py`: raw and class-corrected predictions (`plan_b7_corr_out.txt`).
- `plan_b7_final.py`, `plan_b7_tables.py`: the tables above (`plan_b7_final_out.txt`, `plan_b7_tables_out.txt`).
