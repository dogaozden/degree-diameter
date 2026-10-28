# c11 notes (non-liftable uniform families, alpha = conj by w)

Generator: gen_c11.py q m VARIANT DELTA (VARIANT 1..15; DELTA 6 = O(X)+O(Y); DELTA 8 = {I,w}+O(X)+O(Y)).
Entries are powers of t = g^k (g least primitive root), t^((q+1)/2), constants 2,3,5, companion matrices
[[0,-1],[1,tau]] with tau = t^n + t^-n (Dickson D_n(t+1/t)), and the Legendre sign.

Screen (q = 29,41,53,61; mean_excess): D6 V1 3.115, V2 3.115, V6 3.115, V7 3.115, V11 3.115, V13 3.115, V14 3.115,
V8 3.365, V9 3.365, V3 3.865, V4 4.865, V15 4.615. D8 V3 3.013, V7 3.013, V6/V9/V10 3.263 (most others tie at 3.263).

Full scores (psl, q in [23,113], 22 primes; run_full.sh, log full_scores.log):
- D6 V1 3.313, V7 3.131 (best), V11 3.449
- D8 V3 3.163 (best), V7 3.208, V6 3.253
- random alpha-closed D6 (gen_random_orb 0 2, seeds 1-3): 3.177, 3.495, 3.404 (mean 3.359)
- random alpha-closed D8 (gen_random_orb 2 2, seeds 1-3): 3.253, 3.299, 3.435 (mean 3.329)

Reading: the best uniform families beat the random mean by about 0.2 at both Delta but stay about 0.8-0.9 above the
records (2.0-2.3). Many variants produce identical integer diameters on the screen, so the screen is coarse.
Machine load (~20 on 4 cores) made each full-range run take many minutes.
