# raise-d5D8: beat 9,576 at (Δ, D) = (5, 8)

Status: in progress (Haiku worker, job raise-5-8). Notes are kept current so a fresh session can resume.

## Baseline
- Ours: 9,576 = Haar graph of Z266 ⋊₁₇ Z18 (|G| = 4,788, S = {(0,0),(51,5),(129,13),(156,5),(110,11)}),
  `research/lifts/sols/d5D8_n9576_haar_meta266_18_17.txt`. Table 9,234 (Loz); Moore bound 43,690.
- Beating it means any Haar graph (or lift) with 2N ≥ 9,578, i.e. |G| = N ≥ 4,789 (|G| is always the half).

## Why this cell is hard for random-like S
- For Haar graphs with D = 8 the binding side is the odd side: the B-vertices within distance 7 are the
  non-backtracking walks of length 1, 3, 5, 7, i.e. Δ(Δ−1)^6 + … = 21,845 walks (= the bipartite Moore side) to cover N
  elements. At N ≈ 4,800 the coupon-collector model gives μ ≈ 50 uncovered, so random S fail (SIZE_LAW §3.3, −7 %).
- The record is structured: metacyclic groups (Z_m ⋊_r Z_k) screen far better than SL/PSL at this order.
- Calibration of the screen (haar_gen3 RANDSAMPLE, 2000 samples, p1 = 1st percentile of uncovered counts):
  solved Z266⋊17Z18 (N 4788) p1 = 16; solved Z259⋊33Z18 (N 4662) p1 = 12; solved Z137⋊16Z34 (N 4658) p1 = 12;
  stalled Z133⋊17Z36 (N 4788) p1 = 18. So p1 separates weakly; it is a ranking, not a verdict.

## Tools (all in research/squads/raise_d5D8/)
- `enum_meta.py LO HI`: metacyclic groups of each order in the window, canonical r (not a full isomorphism test).
  4,789–5,000: 5,745 groups.
- `screen.py HAAR GROUPS OUT [SAMPLES] [WORKERS]`: RANDSAMPLE statistics for every group (about 60 s for 5,745 groups
  at 2,000 samples on 4 cores).
- `anneal.py HAAR CANDS OUTDIR SECONDS SEED K WORKERS RESULTS`: haar_gen3 on a candidate list; writes the solution
  file only on cost 0 (haar_gen3 checks the full diameter before writing).
- haar_gen3 is built from research/frontier/haar_gen3.c (`gcc -O3 -march=native -fopenmp`), THREADS=1 per run.
- Verification: `research/frontier/build_haar2.py SOL EDGES` (groups rebuilt from definitions with numpy), then
  `apsp EDGES` (assumption-free all-pairs BFS; source from research/lifts/apsp.c on origin/claude/voltage-lifts-search-6lfotq).

## Batch log
