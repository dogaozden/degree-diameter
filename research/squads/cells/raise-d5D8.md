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
- Stopped at 28 of 100 (about 1 h in) because the best cost was 17, far behind the top ranks (a1's best was 2).
  The 84 entries at N = 4,896 are distinct groups: their screen statistics are not repeated among the top 200.

## Batch a4 (3,600 s, cores on the two best groups): finished, 0 solves
- `4887 181 27 39` on seeds 4, 5, 6 (cost 1 at 1,800 s on seeds 2 and 3).
- `4896 51 96 5` on seed 4 (cost 2 at 1,800 s on seeds 2 and 3).
- Results: 4887 seeds 4/5/6 ended at best 2 / 1 / 1; 4896 seed 4 at best 2. Runs table: `runs/a4.tsv`.

## Round-2 result and stop decision (about 4.5 h in)
- **Record unchanged: 9,760** (Z_61 ⋊₈ Z_80, N = 4,880). No solve at N ≥ 4,881.
- Total search this round: about 16 core-hours. 100 runs at 300 s (a1), 4 at 1,800 s (a2), 28 at 240 s (a3, stopped),
  4 at 3,600 s (a4). Metacyclic and metacyclic × Z_n groups of order 4,881–4,900 only.
- Closest leads: Z_181 ⋊₃₉ Z_27 at N = 4,887 (cost 1 on 4 runs, 1,800–3,600 s, seeds 2, 3, 5, 6; cost 2 on the others).
  Z_51 ⋊₅ Z_96 at N = 4,896 (cost 2 on 3 runs).
- Stop reason: the cost stalls at 1–2 for the strongest candidates even at 3,600 s, and the lower-ranked ones reach
  only 17+ at 240 s. Seeds and time have not closed the gap. Route-level alternatives were checked from notes and
  do not look better: non-metacyclic simple/almost-simple families at 4,896 (watch branch: best 3–15 at 1,800 s); larger-base
  lifts (lift branch §3.5, §2.0; their random model says they lose at this size).
- Not tried, and the only ideas left with a plausible edge: (a) a full isomorphism dedupe of the metacyclic list, so that
  no core goes to a repeated group; (b) a different anneal (larger K, longer REHEAT) on the four cost-1/2 groups; (c)
  the lift.c 2+2 base at n ≥ 9,764 (not tested at this size). Each would need about 4 core-hours to test properly.
- Recommendation: the coordinator should decide whether to spend (b) or (c). Otherwise this cell is at its
  practical limit with these tools.

---

# Round 3 (job raise3-5-8, branch claude/raise3-5-8-record-uv1d39)

Record entering round 3: **9,760** (Z_61 ⋊₈ Z_80, N = 4,880). Target: N ≥ 4,881 (n ≥ 9,762).

## Read from round 2 (not repeated)
- Round 2 searched only metacyclic and metacyclic × Z_n groups at N = 4,884–4,900 (about 16 core-hours): no solve.
  Best: Z_181 ⋊₃₉ Z_27 (N 4,887, cost 1 on several seeds), Z_51 ⋊₅ Z_96 (N 4,896, cost 2).
- Its untried list: (a) isomorphism dedupe, (b) different anneal parameters on the cost-1/2 groups, (c) lift.c 2+2 base
  at n ≥ 9,764.

## New families this round (not in rounds 1–2)
1. **Direct products of two split metacyclic groups**, `prod meta … meta …` (enum_prod.py): 4,241 groups at
   N = 4,881–4,900. Dropping pairs with a cyclic factor (already in enum_meta_cyc) leaves 1,373.
2. **Products with non-metacyclic small bases** (enum_prod.py bases + csl/tpgl): SL(2,3), S4 = PGL(2,3), A4 = AGL(1,4),
   AGL(1,9) times split metacyclic partners; csl 3 (n = 408) and tpgl 3 (n = 204) at N = 4,896. 337 groups in total.
3. **Non-split metacyclic groups** ⟨a,b | a^m, b^k = a^s, bab⁻¹ = a^r⟩ with gcd(m,k) > 1 (enum_nmeta.py), new
   group type `nmeta m k r s` in haar_gen3_nm.c (multiplication carries s when j + l ≥ k). Checked: associativity and
   inverses on 300,000 random triples per parameter set, and b^k = a^s. 1,443 groups at N = 4,881–4,900.

## Screen (RANDSAMPLE, 2,000 samples, lower p1 is better; tools screen_gen.py, anneal_gen.py)
- Products (1,373 non-cyclic): best p1 22 (Z_5 × Z_89⋊Z_11 was top overall but has a cyclic factor). Best non-cyclic
  p1 27 (S3 × Z_51⋊Z_16 at 4,896), 29 (4,884), 31, 32.
- Non-metacyclic bases: best p1 26 (A4 × meta(51,8,2), N 4,896), 27 (S3 × …), 23 (SL(2,3) × Z_17⋊Z_12 at 4,896 is
  p1 36, rest worse).
- Round-2 metacyclic best was p1 20 (N 4,887). So the new families screen no better at the top, and the screen is a
  weak predictor (record group p1 16).

## Round-3 batches
- **b1** (56 candidates, 300 s, seed 1, K = 8): 40 non-cyclic direct products (top by screen) + 16 base products
  (SL(2,3)/S4/A4/AGL(1,9)/S3 × metacyclic). **0 solves**. Cost distribution: 3 (3 runs), 4 (9), 5 (10), 6 (8), 7 (5),
  8+ (21). Best: (Z_11 ⋊ Z_4) × (Z_37 ⋊ Z_3) at N 4,884 (`prod meta 11 4 10 meta 37 3 10`), and two N = 4,896 products
  (`prod agl1 4 meta 51 8 38`, `prod sl 2 meta 51 16 5`), all at cost 3. Runs table `runs/b1.tsv`.
- **b2** (40 non-split `nmeta` candidates, 300 s, seed 1, K = 8, top by screen p1): started after b1, table `runs/b2.tsv`. Note: the queued start waited on a pgrep pattern that matched its own
  command line, so b2 did not begin until 03:47 (about 30 min lost). Restarted by hand.
- **b2 finished** (40 non-split `nmeta` candidates, 300 s, seed 1): **0 solves**. Cost distribution: 2 (2 runs), 3 (4),
  5 (4), 6 (4), 7 (2), more above. Best: `nmeta 543 9 43 181` (N 4,887) and `nmeta 306 16 71 153` (N 4,896), both cost 2.
  The non-split class is no better than split metacyclic at 300 s, and it is similar to the product class.
- **b3** (the two cost-2 non-split candidates, 1,800 s, seeds 2 and 3, K = 8; started 04:38): last test of longer runs.
  Table `runs/b3.tsv`.
