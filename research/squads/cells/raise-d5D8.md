# raise-d5D8: beat 9,576 at (Δ, D) = (5, 8)

Status: **record raised to 9,760** (Haar graph of Z_61 ⋊₈ Z_80, |G| = 4,880). Search continues for |G| ≥ 4,881.

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

### Batch a1 (600 s per run, seed 1, K = 8, 4 workers): top 24 by screen, N 4816–4920
- Result: **SOLVED** at N = 4880, Z_61 ⋊₈ Z_80 (`meta 61 80 8`), 9,760 vertices. The other 11 finished runs stalled at cost 1–3.

### Record: 9,760 (new)
- Solution: `research/frontier/sols/d5D8_n9760_haar_meta61_80_8_s1.txt` (haar_gen3 format, `d D spec n NCYC N NTOT`).
  S = {(0,0), (17,76), (45,49), (0,16), (11,62)} in meta(a, j) coordinates, from the haar_gen3 description lines.
- Verification:
  1. `research/frontier/build_haar2.py` (groups rebuilt from definitions with numpy): VALID, n = 9760, 24,400 edges,
     5-regular, no repeated edges, ecc from A = 8, from B = 8, 0 unreached. Edge-list sha256 de5d9e3d…fd82cb.
  2. `apsp` (assumption-free all-pairs BFS, research/lifts/apsp.c from claude/voltage-lifts-search-6lfotq):
     n = 9760, bipartite, connected, 9,760 sources, **diameter 8**.
- Beats 9,576 by 184 vertices (+1.9 %). Table 9,234; Moore 43,690.

### Next
- Only |G| ≥ 4,881 can beat 9,760. Lower orders were stopped (killed) at the switch.

### Batch a3 (600 s, seed 1, K = 8): top 40 by screen with N ≥ 4,881 (N 4,920–4,970)
- 0 solved. Best cost over the run: 2 (4 runs), 3 (18), 4 (11), 5 (5), 6 (2). None reached cost 1.
- Screen values: the best p1 for N ≥ 4,881 was 19–22 (the record group had 16), so these orders are harder in the screen.

### Batch a4 (done): all 30 N ≥ 4,881 candidates of batches a1 and a3, rerun with seed 2, 600 s each
- 0 solved. Best cost: 1 (1 run), 2 (5), 3 (7), 4 (11), 5 (4), 6 (2).
- Note: the list was meant to hold only the cost-1 candidates, but the filter read the seed column, so it took all 30.
  The cost-1 filter was not applied.
- Tables: `runs/a1.tsv`, `runs/a3.tsv`, `runs/a4.tsv` in the session scratchpad (not in the repo).

## Status at the end of this session (2026-10-25, about 6 h)
- **Record: 9,760** (Z_61 ⋊₈ Z_80, N = 4,880), verified twice. Pushed.
- Since then: 40 + 30 further metacyclic candidates at N = 4,881–4,970 (600 s each) and no solve.
- Total compute on the N ≥ 4,881 search: about 70 runs of 600 s on 4 cores. The record came from batch a1 (1 solve in
  24 runs, seed 1); batches a3 and a4 (70 runs) found none.
- Not tried: longer runs (1800 s+) on the cost-1 candidates; more seeds on the best-screened groups of N 4,881–4,900;
  non-metacyclic families at these orders (the watch branch's SL/PSL runs at 4,620–4,896 stalled at cost 2–9, so they are
  weak); base graphs with more than 2 vertices (lift.c, research/lifts) at N ≥ 4,881.
- The lifts branch's notes say the 4,761–4,900 sweep ran 600 s per run. Our new orders 4,881–4,970 are above it.
- Recommendation for a fresh session: keep the metacyclic screen (enum_meta.py, screen.py, anneal.py). Give each
  candidate that reaches cost ≤ 2 a 1800 s run on two new seeds, and sweep N = 4,881–4,900 more widely (about 1,000
  candidates, 600 s each, roughly 4 h on 4 cores).

---

# Round 2 (job raise2-5-8, branch claude/raise2-5-8-record-kf4cn1)

Record entering round 2: **9,760** (Z_61 ⋊₈ Z_80, N = 4,880). Target: N ≥ 4,881 (n ≥ 9,762).

## Read from round 1 (not repeated)
- Round 1 ran 70 metacyclic candidates at N = 4,881–4,970, 600 s each: 0 solves. Best costs 1–6.
- Its untried list: longer runs on cost-1 candidates, more seeds on the best-screened groups at 4,881–4,900,
  non-metacyclic families, base graphs with more than 2 vertices.
- Watch branch `watch-d5D8w1-auto` (1,800 s each, not in this branch): PGL(2,17) at 4,896 best 12–15, PSL(2,17) × Z_2
  at 4,896 best 11–15, SL(2,17) at 4,896 best 3–4, PSL(2,11) × Z_7 at 4,620 best 1–2 (below our bar),
  PGL(2,5) × Z_41 at 4,920 best 11–12. So the simple/almost-simple families are weak here. Not re-run.
- Lift branch (`claude/voltage-lifts-search-6lfotq`, RESULTS.md §2.0, §3.5): 2+2 and rich lift sweeps at n = 9,236–9,250
  found nothing (that bar was 9,234, far below ours). Random model says larger bases lose about 10–15 % at this size.
  Not re-run.

## Round-2 tools (copied from round 1, unchanged)
- `research/squads/raise_d5D8/enum_meta.py`, `enum_meta_cyc.py`, `screen.py`, `anneal.py`.
- Build: `gcc -O3 -march=native -fopenmp -o SCRATCH/bin/haar_gen3 research/frontier/haar_gen3.c -lm` (binary kept outside the repo).

## Candidate pool, N = 4,881–4,900
- Metacyclic (`enum_meta.py`): 576 (canonical r only; some duplicates across factorisations).
- Metacyclic × Z_n, n ≥ 2 (`enum_meta_cyc.py`): 1,631.
- Screened with `screen.py`, 4,000 random S per group, 30 s on 4 cores. Best p1 is 20 (N = 4,887, Z_181 ⋊₃₉ Z_27 ... see TSV).
  Round 1 reported best p1 19–22 for N ≥ 4,881, so the pool is no better than round 1's.

## Batch a1 (300 s, seed 1, K = 8, 4 workers): top 100 by screen, N = 4,884–4,900
- Result: **0 solves**. Best cost 2 (2 groups), cost 3 (8), 4 (7), 5 (12), 6 (10), 7 (5), ...
- Cost-2 groups: `4887 181 27 39` (Z_181 ⋊₃₉ Z_27) and `4896 51 96 5` (Z_51 ⋊₅ Z_96).
- The top-100 list was 63 × N = 4,896 and 28 × N = 4,884. The canonical reduction is incomplete, so many entries are
  probably the same group under different factorisations. A later pass should dedupe by an isomorphism test.
- Tables: `research/squads/raise_d5D8/runs/screen_4881_4900.tsv` (all 2,207 groups) and `runs/a1.tsv`.

## Batch a2 (1,800 s, seeds 2 and 3, K = 8): the two cost-2 groups of a1
- Result: **0 solves**. `4887 181 27 39`: best cost 1 at seeds 2 and 3 (1,800 s each), so it stalls at cost 1 again.
  `4896 51 96 5`: best cost 2 at both seeds. `runs/a2.tsv`.

## Batch a3 (240 s, seed 1, K = 8, 4 workers): screen ranks 101–200 (N = 4,884–4,900)
- Running at the time of this note. The 84 entries at N = 4,896 are distinct groups: their screen statistics are not repeated among the top 200.
