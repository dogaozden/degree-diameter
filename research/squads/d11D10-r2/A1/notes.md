# A1: k = 10 pairing screen on PSL(2,243) x Z11 (round d11D10-r2)

## Result

- No pairing separates from the others. Paired differences of the bulk costs (same draws) are within about one standard error (about 5 clumps' worth of cost units, i.e. 0.5 clumps). The four AR=2 pairings have the same degenerate draws (13 %).
- AR=6 and AR=7 (with AFROB=1) are not new pairings. They generate the same cyclic groups as AFROB=4 with AR=2 and AFROB=3 with AR=2. With the same seed their costs equal those pairings sample by sample (40/40 identical).
- Nominal best: AFROB=3 AR=2 (best bulk median and mean, not significant). No cost 0 in 480 samples. Lowest cost 20 (AFROB=1 AR=2), i.e. 2 clumps. This is not a solution (score 0).

## Commands

- Source: `research/structured/haar_sym.c` copied to `A1/haar_sym_A1.c`. The only change: after `if (v[t] < 0) v[t] = RANDBV;` one line prints `SAMPLE t cost` when the env var `RANDLOG` is set. Build (inside the gate): `gcc -O3 -march=native -fopenmp -o haar_sym_A1 haar_sym_A1.c -lm`. Syntax was checked before (`-fsyntax-only`, only a pre-existing AVX warning).
- Driver: `run_all2.sh`, run as `gate.sh 1200 bash A1/run_all2.sh`. Queued 13:04:39, slot taken 13:06:29, finished 13:11:34. Slot time about 5.1 min (budget 7), including the build (4 s).
- Each screen: `env -u THREADS OMP_NUM_THREADS=1 RANDLOG=1 ORBIT="10 1 1" AFROB=j AFROBH="0 1 2 0" AR=r RANDORB=n RANDB=1000000 A1/haar_sym_A1 11 10 60 31 8 A1/d11D10_psl_243_11_orb10_afrob<j>_ar<r>_s31.txt psl 243 11`, with n = 100 for (j, r) = (1..4, 2) and n = 40 for (1, 6) and (1, 7). Seed 31 for all runs.
- `RANDB=10^6`: a sample whose cost reaches 10^6 is aborted and counted as 10^6. Such samples are the "degenerate" class of the card. All other costs are exact.
- Deviation: `run_all.sh` (150 samples per screen) was queued at 12:53:31 and had not started by 13:04:39, so I cancelled it (no output) and ran the shorter `run_all2.sh`.
- `algcheck.py` (pure Python, GF(3^5) = GF(3)[x]/(x^5+2x+1), 40 random matrices of GL(2,243)): phi4^9 = phi1, phi3^7 = phi1, phi1^7 = phi2, phi1^9 = phi4 and phi1^10 = id, all 40/40 as projective matrices. Here phi_j(M) = h Frob^j(M) h^-1 with h = mat(0,1,2,0).
- `analyse.py` and `analyse2.py` compute the statistics from the SAMPLE lines. They agree with haar_sym's own RANDORB line (min, median, mean).

## Numbers

ORBIT "10 1 1", AFROBH "0 1 2 0", seed 31. mu = 60.61. |Fix(alpha)| = 3 (+e) for every pairing.
"Bulk" = non-degenerate with cost < 310. "Intermediate" = 310 <= cost < 10^6, which the card's threshold counts as non-degenerate.

| pairing | samples | degenerate (>= 1e6) | intermediate | bulk n | bulk mean | bulk median | bulk sd | min | p10 | P(cost<=40) | P(cost<=60) | time (s) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| AFROB=1 AR=2 | 100 | 13 (13.0 %) | 5 (5.0 %) | 82 | 102.61 | 100.0 | 39.2 | 20 | 51 | 3.0 % | 11.0 % | 44.7 |
| AFROB=2 AR=2 | 100 | 13 (13.0 %) | 6 (6.0 %) | 81 | 105.56 | 101.0 | 39.3 | 30 | 61 | 1.0 % | 8.0 % | 44.0 |
| AFROB=3 AR=2 | 100 | 13 (13.0 %) | 5 (5.0 %) | 82 | 99.48 | 97.5 | 40.3 | 21 | 51 | 3.0 % | 14.0 % | 46.7 |
| AFROB=4 AR=2 | 100 | 13 (13.0 %) | 5 (5.0 %) | 82 | 104.15 | 100.5 | 36.7 | 41 | 63 | 0.0 % | 5.0 % | 43.9 |
| AFROB=1 AR=6 (= AFROB=4 AR=2) | 40 | 3 (7.5 %) | 3 | 34 | 114.82 | 110.0 | 37.4 | 63 | 72 | 0.0 % | 0.0 % | 17.2 |
| AFROB=1 AR=7 (= AFROB=3 AR=2) | 40 | 3 (7.5 %) | 3 | 34 | 92.00 | 87.5 | 34.5 | 35 | 51 | 2.5 % | 15.0 % | 19.1 |

The AR=6 and AR=7 rows are the first 40 samples of the matching AR=2 run, so they are not independent data.

Histogram of cost/10 over the non-degenerate samples (bins 0..30; bin 31 = intermediate, cost >= 310). Bins start at 0. The first nonzero bin is 2 (cost 20-29) for AFROB=1 and 3, bin 3 for AFROB=2 and bin 4 for AFROB=4:

- AFROB=1 AR=2: 0 0 1 2 2 5 4 5 9 12 9 7 5 7 5 2 2 2 0 1 1 0 0 1 0 0 0 0 0 0 0 | 5
- AFROB=2 AR=2: 0 0 0 1 1 5 3 10 9 7 9 10 7 3 7 0 2 2 1 2 1 0 0 0 1 0 0 0 0 0 0 | 6
- AFROB=3 AR=2: 0 0 1 2 4 4 7 8 4 11 7 10 5 6 3 5 2 1 0 0 0 1 0 0 0 1 0 0 0 0 0 | 5
- AFROB=4 AR=2: 0 0 0 0 2 3 6 11 13 4 8 7 7 6 4 1 5 0 2 3 0 0 0 0 0 0 0 0 0 0 0 | 5

Cost-0 count: 0 in every run. Costs at or below 40: 3 samples (AFROB=1), 1 (AFROB=2), 3 (AFROB=3), 0 (AFROB=4).

## Structure found

1. Equivalence of the pairings. G = PSL(2,243) x Z11 gives Aut(G) = Aut(PSL) x Aut(Z11), and Out(G) = (Z2 x Z5) x Z10 is abelian. So the image of alpha in Out(G) is invariant under conjugation. alpha_(j,r) = (conj_h o Frob^j, z -> r z) has image (sigma^j, r). For r in {2,6,7,8} the cyclic groups split into four classes:
   - {(1,2),(4,6),(2,7),(3,8)}
   - {(2,2),(3,6),(4,7),(1,8)}
   - {(3,2),(2,6),(1,7),(4,8)}
   - {(4,2),(1,6),(3,7),(2,8)}
   So the four AR=2 pairings are pairwise non-conjugate. AFROB=1 AR=6 is class 4 (alpha_(1,6) = alpha_(4,2)^9), and AFROB=1 AR=7 is class 3 (alpha_(1,7) = alpha_(3,2)^7). The sample-by-sample identity confirms this.
2. The bad draws are shared. For the same seed, the degenerate samples are the same indices in all four AR=2 pairings: 2, 3, 22, 55, 58, 67, 72, 77, 78, 79, 81, 86, 90. The intermediate samples fall on the same indices too (8, 14, 17, 52, 70; index 83 only for AFROB=2), with similar sizes (index 70: 183k-207k). So the degeneracy comes from the drawn orbit generator x, not from the Frobenius twist. This is one seed and one run of 100, so it is a hypothesis for A2.
3. Paired comparison (bulk, same draws), mean difference +- standard error: AFROB=2 minus AFROB=1: +4.0 +- 5.1. AFROB=3 minus AFROB=1: -3.1 +- 5.0. AFROB=4 minus AFROB=1: +1.5 +- 4.9. AFROB=3 minus AFROB=4: -4.7 +- 4.8. Correlations of the bulk costs across pairings on the same draws are only 0.30-0.36.

## Ranking (bulk median, then mean; all within noise)

1. AFROB=3 AR=2 (median 97.5, mean 99.5, P(cost<=40) 3 %)
2. AFROB=1 AR=2 (median 100.0, mean 102.6, P(cost<=40) 3 %, lowest cost 20)
3. AFROB=4 AR=2 (median 100.5, mean 104.2, P(cost<=40) 0 %, lowest cost 41)
4. AFROB=2 AR=2 (median 101.0, mean 105.6, P(cost<=40) 1 %, lowest cost 30)

AR=6 and AR=7 add nothing beyond AFROB=4 and AFROB=3 with AR=2.

## Next

- Do not spend more k = 10 Frobenius screens on this group. The four twists are equivalent within noise. If a long k = 10 run is wanted, AFROB=3 AR=2 is the nominal choice.
- The 13 degenerate draws are the same for all twists at seed 31, so a filter for the bad draws (A2) transfers across these pairings. Check it on a second seed.
- A5 (AFROBD outer twist) and A6 need their own screens. This card does not compare them.
