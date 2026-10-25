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

## Round 2: NEW RECORD (7,10): 2,247,960 vertices (previous 2,237,760)

- File: `research/frontier/sols/d7D10_psl_131_1_orb3_s3.txt` (sha256 b4aca323f32309903d00aaabf4912ba47ea73c94ef7e78f051aabedaba9e9d0b).
- Group: PSL(2,131), no Z factor, N = |PSL(2,131)| = 1,123,980. Structured orbit search `ORBIT="3 2 1"`, K = 8, seed 3:
  solved after 95,193 evaluations (129 s), μ = 23.9, |Fix(α)| = 65.
- Checks (all on the same file):
  - haar_sym's own full diameter check: OK (run log `research/structured/runs/d7D10_psl_131_1_orb3_s3.log`).
  - `research/frontier/build_haar2.py`: VALID, n = 2,247,960, 7-regular, no duplicate edges, ecc 10 from (e,A) and (e,B), edge-list sha256 `8a068585ebd6d2f60cbb36c4947b715823c3f80ae5b0b32d118b9b5d2b14b9bb` (`research/structured/runs/d7D10_psl_131_1_orb3_s3.rebuild.txt`).
  - `research/structured/tools/haarcheck_psl.c` (built from source): VALID, ecc 10 from both sides.
  - The all-pairs checker `research/theorems/coordinator_check/apsp.c` is not run: at 2.2M vertices all-pairs BFS is far too slow. The two-BFS Haar check above is the rule for Haar graphs.
- Same group, seed 2, 30 min: unsolved (best 2) (`research/structured/runs/d7D10_psl_131_1_orb3_s2_unsolved_30min.log`). Seed 1 900 s: best 1. So success at this μ is seed-dependent.

Also still running at the time of writing: psl 131 seed 2 (30 min), sl 25 × Z73, prod psl 7 psl 9 × Z19 (both 30 min; best so far 3–4).

## Round 3: NEW RECORD (7,10): 2,277,600 vertices (N = 1,138,800)

Two solutions at the same order, both VALID by build_haar2.py (diameter 10, 7-regular, no duplicates):

| file (research/frontier/sols/) | group | seed | evals | edge-list sha256 |
|---|---|---|---|---|
| d7D10_sl_25_73_orb3_s2.txt | SL(2,25) × Z73 (GF(25) = GF(5)[x]/(x²+2)) | 2 | 1,928,289 (1,465 s) | 35d028f938f09908973354c19b7e9dae9fdadf0c79621b2b1eb684fca28e26ae |
| d7D10_pgl_25_73_orb3_s2.txt | PGL(2,25) × Z73 | 2 | 1,327,417 (1,048 s) | 9ee144249480df01c63a09e36a71c708497c924b8fcd614de81a8c4bd6c6df26 |

- Search: `ORBIT="3 2 1"`, K = 8, single thread, N = 1,138,800 (μ ≈ 27.8), |Fix(α)| = 23.
- Checks: haar_sym's own full diameter check (logs in research/structured/runs/d7D10_sl_25_73_orb3_s2.log, d7D10_pgl_25_73_orb3_s2.log); build_haar2.py VALID for both (rebuild outputs in research/structured/runs/*.rebuild.txt).
- `haarcheck_sl` only accepts prime q, and `haarcheck_psl` only PSL: neither covers GF(25) here, so build_haar2.py is the only independent check for these two.
- Unsolved, same order and budget: prod psl 7 psl 9 × Z19 (N = 1,149,120) reached cost 1 after 30 min (1.55M evals), and psl 131 × 1 seed 2 reached cost 1 after 30 min.

## Round 4: NEW RECORD (7,10): 2,298,240 vertices (N = 1,149,120)

- File: `research/frontier/sols/d7D10_prod_sl_7_psl_19_1_orb3_s2.txt`. Group SL(2,7) × PSL(2,19), no Z factor, k = 3, m = 2, f = 1, seed 2.
  Solved after 323,521 evaluations (510 s).
- build_haar2.py VALID: n = 2,298,240, 7-regular, no duplicates, ecc 10 from both (e,A) and (e,B). Edge-list sha256
  `d977a1225993a74ae9c26e3c021d40a3e287407595eea0e499c11e74c14cd0fe` (`research/structured/runs/d7D10_prod_sl_7_psl_19_1_orb3_s2.rebuild.txt`).
- Unsolved at 30 min, same order: prod psl 7 psl 9 × Z19 seed 3 (best 1), prod psl 7 sl 19 seed 2 (best 3), prod sl 5 sl 8 × Z19 seed 2 (best 3).

## Round 5: no solve above N = 1,149,120 (30–60 min runs)

Single-thread runs, `ORBIT="3 2 1"`, seed as shown (best cost in brackets):

| group | N | μ | budget | result |
|---|---|---|---|---|
| sl 19 × Z169 (s2) | 1,155,960 | 33.1 | 30 min | best 9 |
| pgl 19 × Z169 (s2) | 1,155,960 | 33.1 | 30 min | best 12 |
| psl 19 × Z337 (s2) | 1,152,540 | 32.0 | 30 min | best 18 |
| prod psl 3 × sl 11 × Z73 (s2) | 1,156,320 | 33.2 | 30 min | best 13 |
| prod psl 5 × sl 27 × 1 (s1) | 1,179,360 | 41.5 | 60 min | best 8 (fix = 161) |
| psl 23 × Z193 (s1) | 1,171,896 | 38.7 | 60 min | best 6 (fix = 11) |
| psl 31 × Z79 (s1) | 1,175,520 | 39.9 | 60 min | best 3 (fix = 14) |
| sl 17 × Z241 (s1) | 1,179,936 | 41.8 | 60 min | best 21 |

Also at N = 1,149,120 (not above the record): prod psl 7 × psl 9 × Z19 seed 3, 30 min, best 1 (cost-1 plateau; 1.48M evals).

Reading: the ladder has reached the wall of this method, roughly μ ≈ 30–34 with ~10⁶ evaluations (about 15–25 min on one core
for a solve, and a clear plateau above that). Groups at μ ≈ 38–42 plateau at cost 3–21 after 3–5 M evaluations.
The next attempts (ORBW=3 on psl 31 × Z79 and psl 23 × Z193, four 75-minute runs) are in the table of the final round.

## What a fresh session should do next

1. Rebuild the binaries (see Resume) and check the three records above with build_haar2.py before building on them.
2. The current record is 2,298,240 (SL(2,7) × PSL(2,19), file `d7D10_prod_sl_7_psl_19_1_orb3_s2.txt`).
3. Above μ ≈ 33, the k = 3 orbit method with plain annealing plateaued in this session. Routes not tried here:
   ORBW weighting on the μ ≈ 38–42 groups beyond the final round, k = 5 orbits (fixed-point counts are large in the
   window, see SIZE_LAW), and metacyclic/voltage lifts (research/lifts/).
