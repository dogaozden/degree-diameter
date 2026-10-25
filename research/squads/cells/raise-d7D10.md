# Cell (Δ, D) = (7, 10): raise job "raise-7-10"

Haiku worker session on `claude/raise-d7d10-record-7d5zrr` (2026-10-25). Goal: beat our own record at (7,10),
which is a bipartite Haar graph with 2,237,760 vertices (N = |G| = 1,118,880; 7-regular; diameter 10).

Reference values: table 1,987,380 (DS14v2); bipartite Moore bound 24,186,470.

## Record to beat

| vertices | N | group | file | checks |
|---|---|---|---|---|
| 2,237,760 | 1,118,880 | PSL(2,5) × SL(2,8) × Z37 (GF(8) poly x^3+x+1) | research/frontier/sols/d7D10_prod_psl_5_sl_8_37_orb3_s15.txt | build_haar2.py, bigcheck_indep (harvest_check_2026-10-24.txt) |

Other (7,10) files in research/frontier/sols/: psl 49 × Z19 at 2,234,400 (orbit k=3, f=1), psl 29/31/49/67/71 etc. (older).

## Method and parameters

- Structured orbit search (`research/structured/haar_sym.c`, STRUCTURE.md §2–3): Δ = 7 = f + 3m with f = 1, m = 2,
  `ORBIT="3 2 1"`, K = 8, single thread per run. Compiled into the scratchpad (not committed).
- Cost model (SIZE_LAW §2.2): W = 12,093,235 binding words, μ = N·exp(−W/N). At N = 1,118,880 μ ≈ 22.6.
  Each +1 % in N raises μ by ≈ 12 % (d ln μ / d ln N = 1 + W/N ≈ 11.8), so μ ≈ 23.5 is about N = 1,128,000.
- Random symmetric S at μ ≈ 22.6 on the record group: 2 ms per sample, min cost 9, median 169 (300 samples).
- Candidate list: `python3 research/structured/tools/orb_screen.py 7 10 1118881 1200000 "3 2 1" --list` (69 groups with
  n prime factors ≡ 1 mod 3). Lower-tail screen (`--samples 2000`) output is in the scratchpad, see progress below.

## Progress

Round 0 (setup): record verified by its checkers. Three annealing runs started on the top screen candidates
(900 s each): psl 131 × 1 (N = 1,123,980, μ 23.9), sl 17 × Z229 (N = 1,121,184, μ 23.2), and the record group
again as a control (prod psl 5 sl 8 × Z37, seed 2).

## Resume

- Scratchpad binaries are gone in a fresh container: rebuild with
  `gcc -O3 -march=native -fopenmp -o haar_sym research/structured/haar_sym.c -lm` (and haar_fast, haarcheck_psl from
  tools/haarcheck_psl.c).
- Run one candidate: `ORBIT="3 2 1" THREADS=1 ./haar_sym 7 10 900 SEED 8 out.txt <group spec> n`, e.g.
  `prod psl 5 sl 8 37`, `sl 17 229`, `psl 131 1`. Then `python3 research/frontier/build_haar2.py out.txt`.

## Round 1 results (2026-10-25, ascending-N ladder, ORBIT="3 2 1", K=8, single thread)

| group | N | μ | result |
|---|---|---|---|
| prod psl 5 sl 8 × Z37 (record group, control) | 1,118,880 | 22.6 | **solved** in 275 s (232,553 evals), a re-find of the record order, not an improvement |
| psl 131 × 1 | 1,123,980 | 23.9 | best 1 after 900 s (677,569 evals), not solved |
| pgl 17 × Z229 | 1,121,184 | 23.2 | best 7 after 240 s |
| sl 17 × Z229 | 1,121,184 | 23.2 | best 9 after 900 s (1.28M evals) |
| prod sl 5 sl 9 × Z13 | 1,123,200 | 23.7 | best 5 after 240 s |
| prod psl 5 psl 5 × Z313 | 1,126,800 | 24.6 | best 21 after 240 s (fix = 8) |
| prod sl 3 sl 7 × Z139 | 1,120,896 | 23.1 | best 40 after 240 s (bad mixing) |

Reading: the record-order group solves quickly, but the neighbouring orders at μ ≈ 23–24 stall at cost 1–10 within
15 minutes. A 240 s rung is too short to decide a group. The ladder over the remaining 60+ candidates is still running.
