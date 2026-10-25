# Cell (13,8): raise the Haar record (job raise-13-8)

Record to beat: 6,814,080 vertices = 2N with N = |SL(2,64) x Z_13| = 3,407,040 (13-regular Haar graph, k = 3, m = 4,
f = 1, conjugation orbits; file research/frontier/sols/d13D8_sl_64_13_orb3_s1.txt). Table value 5,314,680.
Moore bound 78,178,490. Model: W(13,8) = 39,089,245, mu = N exp(-W/N) (SIZE_LAW, mu_plan.py); the record has mu = 35.5.

Branch: claude/raise-d13d8-haar-7qqnoz. Working notes: this file (kept current); scratch in the session scratchpad.

## Plan

- Groups of order N in (3,407,040, ~3,500,000] whose Z-factor is 1 or has only primes = 1 mod 3 (so that z -> rz,
  r of order 3, is available). Each +1 % in N is +1 % in vertices; mu grows about 13 % per +1 % in N here, so the
  reachable window is a few percent above the record.
- Screen with RANDORB (orb_screen.py, 300 samples), then anneal the best candidates on 4 cores (THREADS=1).
- Verify with build_haar2.py (< 20M vertices), the low-memory checkers above.

## Candidate orders (k = 3 compatible), 3,407,041 .. 3,480,000

orb_screen.py 13 8 3407041 3480000 "3 4 1" --samples 300 (k = 3 compatible n only; 35 candidates; ranked by (p1+p10)/2):

| rank | N | 2N | mu | fix | p1 | p10 | median | group | mu_A = mu/3 + fix e^(-lambda/3) |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 3,450,720 | 6,901,440 | 41.5 | 77 | 23 | 36 | 53 | sl 79 7 | 15.6 |
| 2 | 3,416,952 | 6,833,904 | 36.8 | 41 | 27 | 33 | 51 | sl 43 43 | 13.2 |
| 3 | 3,427,200 | 6,854,400 | 38.2 | 89 | 25 | 38 | 59 | prod sl 5 sl 16 7 | 14.7 |
| 4 | 3,442,800 | 6,885,600 | 40.4 | 149 | 25 | 38 | 55 | sl 151 1 | 16.9 |
| 5 | 3,416,952 | 6,833,904 | 36.8 | 41 | 27 | 37 | 59 | pgl 43 43 | 13.2 |
| 6 | 3,450,720 | 6,901,440 | 41.5 | 77 | 27 | 37 | 59 | pgl 79 7 | 15.6 |
| 7 | 3,437,280 | 6,874,560 | 39.6 | 17 | 24 | 42 | 66 | prod psl 7 psl 11 31 | 13.6 |
| 8 | 3,453,840 | 6,907,680 | 42.0 | 80 | 29 | 39 | 60 | psl 81 13 | 15.8 |
| 9 | 3,407,520 | 6,815,040 | 35.5 | 14 | 30 | 42 | 66 | psl 31 229 | 12.1 |
| 10 | 3,412,800 | 6,825,600 | 36.2 | 53 | 30 | 42 | 74 | prod sl 5 psl 9 79 | 13.2 |
| 11 | 3,447,360 | 6,894,720 | 41.0 | 161 | 32 | 40 | 64 | prod sl 8 sl 19 1 | 17.3 |
| 12 | 3,476,496 | 6,952,992 | 45.5 | 23 | 30 | 42 | 69 | psl 47 67 | 15.7 |
| 13 | 3,412,800 | 6,825,600 | 36.2 | 53 | 28 | 46 | 78 | prod psl 5 sl 9 79 | 13.2 |
| 14 | 3,412,800 | 6,825,600 | 36.2 | 53 | 30 | 46 | 77 | prod sl 4 sl 9 79 | 13.2 |
| 15 | 3,430,224 | 6,860,448 | 38.6 | 125 | 31 | 46 | 70 | prod psl 3 psl 83 1 | 15.7 |
| 16 | 3,447,360 | 6,894,720 | 41.0 | 80 | 33 | 44 | 66 | prod psl 9 sl 8 19 | 15.5 |
| 17 | 3,443,328 | 6,886,656 | 40.4 | 17 | 30 | 49 | 79 | prod psl 7 sl 7 61 | 13.9 |
| 18 | 3,446,940 | 6,893,880 | 41.0 | 14 | 30 | 51 | 78 | psl 29 283 | 14.0 |
| 19 | 3,436,752 | 6,873,504 | 39.5 | 23 | 34 | 51 | 81 | sl 23 283 | 13.7 |
| 20 | 3,463,200 | 6,926,400 | 43.4 | 35 | 36 | 49 | 81 | prod psl 3 psl 25 37 | 15.3 |

Reference, the record group SL(2,64) x Z_13 (150 samples, same screen): N = 3,407,040, mu = 35.5, fix = 62, p1 = 18, p10 = 30, median = 49; mu_A = 13.2.

The screen ranks random symmetric S only. mu_A is the model's effective mean (SIZE_LAW / BEYOND_RANDOM): it predicts the anneal's difficulty, and the random-sample stats are noisy, so the anneal decides.

## Log

- 08:06 UTC: binaries built (research/structured/haar_sym, haar_fast). Screen above (35 candidates).
- 08:10 UTC: round 1 started, ORBIT="3 4 1", THREADS=1, 7200 s, seed 1, four groups:
  sl 43 x Z43, prod psl 7 psl 11 x Z31, psl 31 x Z229, prod sl 5 sl 16 x Z7.
- 10:10 UTC: round 1 ended for sl 43 x Z43 (best 3, 838,105 evals) and prod psl 7 psl 11 x Z31 (best 3, 944,737 evals).
  psl 31 x Z229 and prod sl 5 sl 16 x Z7 still running (end ~10:12). No solution in round 1.
- 10:10 UTC: round 2 started, ORBIT="3 4 1" ORBW=3 (uncovered fixed element weighs 3), seed 2, 7200 s:
  sl 43 x Z43 and prod psl 7 psl 11 x Z31.
- Live logs are not tracked (ignored, runs/raise13/*.log); checkpoints are committed as *.snap.log.
- 10:10 UTC: round 1 ended for psl 31 x Z229 (best 3, 1,234,185 evals) and prod sl 5 sl 16 x Z7 (best 4, 1,019,801 evals).
  No solution in round 1 (all four groups).
- 10:12 UTC: round 2b started, ORBIT="3 4 1" ORBW=3, seed 2, 7200 s: psl 31 x Z229 and prod sl 5 sl 16 x Z7.
  Round 2 now has four runs (two started 10:10, two started 10:12).
- 10:19 UTC: SOLVED. Round 2 (ORBW=3, seed 2) on sl 43 x Z43 (N = 3,416,952): cost 0 after 32,177 evaluations (267 s).
  Solution research/frontier/sols/d13D8_sl_43_43_orb3_ORBW3_s2.txt, 6,833,904 vertices (+19,824 over 6,814,080, +0.29 %).
  Checks: haar_sym full diameter check OK; haarcheck_sl VALID; build_haar2.py VALID (13-regular, no duplicate edges,
  edge-list sha256 cd5d3aedbaa36ae1d5431dd927395ea2219c1e24c692db2e6776144767331b4f). Check text in runs/raise13/*.check.txt.
  Awaiting the coordinator's independent re-check.
- Round 2 still running for prod psl 7 psl 11 x Z31, psl 31 x Z229, prod sl 5 sl 16 x Z7 (ORBW=3, seed 2).
