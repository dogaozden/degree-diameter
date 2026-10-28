# c14: larger q, LPS p=5 vs random alpha-closed baseline (Delta = 6)

Commands (run from research/theorems/haar_families, sequential, nice -n 10):
- LPS: family_score.py --gen "./gen_lps.sh 5 {q}" --group pgl --qrange 23 112 --json  (21 primes)
       family_score.py --gen "./gen_lps.sh 5 {q}" --group pgl --qrange 113 199 --json (17 primes)
- Random: family_score.py --gen "python3 gen_random_orb.py {q} 0 2 SEED" --group psl --qrange 23 112 / 113 199, SEED = 1,2,3
  (driver: run_random.sh). Fit: fit.py -> fit_results.json. Raw rows: lps_*.json, rand_s*_*.json.

Convention: |G| = vertices // 2 where vertices = component of (e,A) (scorer convention). For LPS with PGL, the
Haar graph is always disconnected (connected=no in every row): <S^-1 S> is the index-2 subgroup PSL, so the
component of (e,A) is one of two copies of H(PSL,S). Its size |PGL| = vertices, so |G| = |PSL| (same G as the random PSL runs).

Results (x = log_5 |G|, y = excess, 38 primes in [23,199] per family):
- LPS p=5 (pgl): slope 0.410, intercept 0.965, residual SD 0.477, mean excess 4.26. Prediction 1/3 = 0.333 (within ~1 SE, SE ~ 0.07).
- Random (psl), seeds 1,2,3: slopes 0.046, -0.140, -0.023 (mean -0.039); intercepts 2.81, 4.49, 3.55; residual SD 0.37, 0.63, 0.47.
  Mean excess 3.18, 3.37, 3.37. Prediction log_5 log|G| gives slope about 0.09 over this x-range; measured value is within ~1.5 SE.
- Score = slope(LPS) - mean slope(random) = 0.410 - (-0.039) = 0.449.
- LPS best order vs 2013 table at Delta=6: D=8 0.41, D=9 0.21, D=10 0.33 (below the table; LPS is not competitive at these D).
