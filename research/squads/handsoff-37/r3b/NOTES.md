# r3b NOTES (Haiku worker r3b, squad handsoff-37, card r3b: breakout weights on the non-free symmetric search)

Start: 2026-10-31T19:06:11Z (date -u). Keep going until at least 21:06Z; stop about 21:21Z.

## Files
- symbo.c / symbo (binary): focused breakout local search over G-invariant cubic bipartite graphs. Same group-file format
  and orbit 2-switch moves as r2f/symloc.c, plus VOLTAGE moves (see below), a breakout weight W[rep][vertex] on violated
  pairs (bumped at local minima of the weighted cost), tabu on re-adding removed edges.
  usage: symbo GROUP GRAPH SECONDS SEED OUTPREFIX [K=40] [TEN=10] [PF=0.7] [BUMP=1] [WCAP] [PV=0.5]
  writes OUTPREFIX_best.edges at every new best raw far (unordered same-side pairs at distance > 6, orbit-weighted).
- mkgroup.py (copy of r2f): group + SAT degree-only start for (M, K, ALPHA, sigma_A, sigma_B).
- grp168_f21.txt, grp182_f21.txt (copy of r2f n182_f21hot), grp182_f21b.txt (fresh F21, 1 fixed per side), grp196_f21.txt.
- start182_f21_far210.edges, start196_f21_far224.edges (r2f's best, used as starts).

## Engine (what changed from symloc / symtabu)
1. Breakout cost: wc = sum over reps r, violated same-side v of wrep[r] * W[r][v]. Every step: pick a random violated
   pair (r, v); sample K candidate moves whose removed edges lie within radius 3 of r or v (prob PF), else anywhere; take
   the best non-tabu candidate. If no candidate lowers wc, bump W of all violated pairs (breakout) and still apply the best
   candidate (walk, as r2e BOWALK).
2. Voltage moves (new, not in symloc): remove the G-orbit of an edge (x,p) and add the G-orbit of (x, G[h] p), i.e. the
   matching between two orbits gets a new G-equivariant voltage. symloc's orbit 2-switches never change a voltage without
   changing the base, so this neighbourhood was missing. (PV = probability of a voltage move per candidate.)

## 19:06-19:17Z: calibration and first runs
- Calibration n = 168, F21 (grp168_f21.txt, sigma A 3 fixed + three 3-cycles, B four 3-cycles, alpha 4), from a SAT start
  (far 13104): 2-switches only: far 0 in 3 s (out/cal168_s1). With voltage moves: far 0 in 2 s (out/cal168v_s1). Verified
  by score37 (far 0 diam 7, connected).
- n = 182 F21 (grp182_f21b.txt, sigma A 1 fixed + four 3-cycles, B same, alpha 2), SAT start, 90 s, K 40, PV 0.5:
  far 210 (diam 8). The same 210 appears with K 200 (90 s), and with the old 2-switch-only moves at PV 0 from the r2f
  start (r2f: 210). Violated pairs at the 210 graph: 8 size-21 orbits with 2-3 bad ordered partners each, the size-7
  orbits (fixed points of s) have none (out/badpat.py). Breakout walk: bumps on ~60% of steps; raw drifts up to ~500
  between bests (the weights grow fast), so the best is only kept by the logged file.
- n = 182 plain Z7 (no s), SAT start, 80 s: far 245. Slower than r2e lift2 (126 after 1500 s with voltages + bo).
  Speed: about 14-30k candidate evaluations per second (full cost from 10-26 orbit reps each).

## 19:17-19:19Z: sigma variants and the elite-restart engine
- F21 n=182 with sigma A = B = 1,1,1,1,3,3,3 (4 fixed + three 3-cycles per side), SAT start, 70 s: raw 567 (score37 far 609).
  Much worse than 1 fixed point per side (210). Fixed points of s do not help here.
- symbo2.c: symbo plus an elite restart (STALL steps without raw improvement: restore the best graph, reset W and tabu).
  Batch 1 (out/batch1.sh log in out/batch1.log) runs D5, F20 at n=170 and F21 10-fixed at 182 with symbo.
- F21 n=182 with sigma A = B = 1 x10, 3 (10 fixed + one 3-cycle): dead. The SAT start is disconnected (far 13328) and the
  breakout never finds a valid improving move (bump on every step, raw 6664 for 70 s). Discarded.
- 19:19Z: D5 n=170 (alpha 4, sigma 2^8 1 both, symbo, 70 s, seed 1): far 185 (raw 185, 1.4M evals). The breakout walk
  drifts (raw 400-600 between bests). r3a's SA reached 155 with the same group (T 40 -> 4). So the breakout walk is worse
  than SA for D5 at 170.
- Plan (19:20Z): batch2 = symbo2 with elite restart (STALL 400: restore the best graph, reset weights) on F21 196 (from the
  r2f 224 start), F21 182 (from the 210 start) and D5 170 (80 s each).
- 19:21Z: F20 = Z5 x| Z4 at n=170 (alpha 2, sigma 4,4,2,2,2,2,1 both sides), symbo 70 s, seed 1: far 160 (diam 8; the file is the best state, final current raw was 190), best
  reached at ~24 s, then flat. Logged to scoreboard (r3b/best/n170_F20_far160.edges). Better than D5 (185 in the same
  setup) but not better than r3a's D5 155 (symloc, T schedule). Batch1 D5 seed 2 still running.
- Batch1 summary (70 s each, symbo, K 40, TEN 10, PF 0.7, PV 0.5): F21 182 (4 fixed per side) 609; F21 182 (10 fixed)
  dead; D5 170 185 (seeds 1 and 2); F20 170 160 (logged). Breakout walk drifts; F20 reaches 160 at ~24 s then stalls.
- symbo3.c = symbo2 + MARG option (restore the best graph when raw > best + MARG). Built, not yet run.
- Batch2 (symbo2, elite restart after 400 steps without a raw improvement, 80 s each): F21 196 from the r2f 224 start:
  no change (224; 102 restarts). F21 182 from the r2f 210 start: no change (210; 134 restarts). Restarts alone do not move
  these basins; the 210 and 224 graphs are local minima for orbit 2-switch + voltage moves with breakout.
- Violated pairs of the F20 170 graph (out/badpat.py): concentrated on orbits with nontrivial stabilizer (size-5 orbit with
  stabilizer 4 has 6 bad partners per vertex; size-10 orbits with stabilizer 2 have 1-6). Generic orbits are almost fine.
- Batch2 D5 170 with elite restart (seed 7, 80 s): far 175 (raw 175; 1.7M evals). Better than the 185 of the no-restart
  runs with seeds 1, 2 but still above r3a's D5 155 and our F20 160.
- Batch3 (running at 19:27Z): F20 170 with elite restarts (STALL 400 / 150), seeds 3 and 5 from a fresh SAT start, and
  sigma 4,4,4,4,1 (seed 4). Early numbers: seed 3 best 290 at 11 s (the seed-1 run reached 160 at 24 s; the spread across
  seeds is large, so several seeds are needed).
- Batch3: F20 seed 3 (elite restarts, 80 s) stuck at 290 (restarts keep returning to the same bad best); a sigma 4,4,4,4,1
  setup for F20 failed in mkgroup (the degree-only SAT is UNSAT for alpha 2). Seed 3 is a bad basin, so several seeds per
  config are needed. Batch5 = seed sweep of the seed-1 F20 config (seeds 21-26, 70 s each, symbo) to see the spread.
- Batch4 (symbo3, raw margin restart): F20 170 with MARG 30 (seed 11, 80 s): far 190 (score37 200). Worse than the plain
  symbo seed-1 run (160). MARG restarts keep the walk near the best but do not help; not pursued.
- Z15 = Z5 x Z3 at n=170 (alpha 1, sigma 3,3,3,3,3,1,1 both sides): degree-only start is disconnected (far 13600, as r2f
  found). Batch6 runs it with symbo (2 seeds, 70 s) to see whether breakout connects and descends.
- Batch5 (F20 170, seed sweep, symbo, 70 s, same start as seed 1): seeds 21 and 22 both reach far 160 (diam 8), but the
  graphs differ (md5 of sorted edge lists differ from seed 1). So 160 is a plateau reached by several distinct graphs,
  not one lucky graph.
- Batch6: Z15 at 170 (2 seeds). Batch7: other F20 sigma cycle types at 170 (4,4,4,2,2,1 / 4,4,4,1,1,1,1,1 / 4,4,2,2,2,1,1,1).
- Batch5 final: F20 170 seeds 21-26 all end at far 160 (six runs, 70 s each). Strong plateau for this group/sigma.
- Batch6 Z15 at 170 (2 seeds, 70 s): dead. Final far 1500 (score37 far 3000, disconnected). The breakout cannot connect the
  degree-only start under the Z3 part with fixed points. Matches r2f's Z15 result. Dropped.
- Batch7 (F20 170, other sigma cycle types, seed 1, 70 s): sigma 4,4,4,2,2,1 -> far 175 (connected). sigma 4,4,4,1,1,1,1,1
  -> disconnected, far 7030 (dead: five fixed base points per side). Sigma 4,4,2,2,2,2,1 (the 160 config) stays the best F20 type.
- Batch7 third type 4,4,2,2,2,1,1,1: far 380 (connected). So among F20 sigma types tried at 170, 4,4,2,2,2,2,1 (far 160)
  is best, 4,4,4,2,2,1 gives 175, 4,4,2,2,2,1,1,1 gives 380.
- Batch8 n = 180 (M = 5, K = 18): D5 (alpha 4, sigma 2^9 both): far 330 (seed 1). F20 (alpha 2, sigma 4,4,4,4,2 both): far 270
  (seed 1). Both worse than r3a's symloc results at 180 (D5 185, F20 250). The breakout walk is not better than SA here.
- Batch9 (F20 170, 90 s each, parameter variants): PV 0.8 (seed 31) -> 160; PV 0.2 (seed 32) -> 160. Other variants below.
- Batch9 (F20 170, parameter variants, 90 s each): PV 0.8, PV 0.2, PF 0.3, TEN 30: all 160. The F20 floor does not move.
- Batch10 (fresh SAT starts): F21 196 (sigma 1,1,3,3,3,3): 224 twice (same as the r2f start). F21 182 (K 80, PV 0.8): 210.
  D5 170 (alpha 4, sigma 2^8 1 both sides, K 40, PV 0.8, seed 9): FAR 155 (diam 8). This is the first D5 result close to
  r3a's 155 and it beats my F20 160. The PV 0.5 runs of D5 gave 175-185, so the voltage moves matter a lot for D5.
  Logged: r3b/best/n170_D5_PV08_far155.edges (score37 far 155; not a diameter-7 graph, so apsp is not expected to pass).
- Batch13 (queued): D5 170 with PV 0.8 (seeds 10, 11, 13) and PV 0.95 (seed 12), 90 s each, to see whether the 155 falls.
- Batch13 (D5 170, PV 0.8): seeds 9, 10, 11 all end at far 155 (90 s each). The 155 is a plateau for D5 under PV 0.8, as the
  160 was for F20. (Seed 12 with PV 0.95 and seed 13 still running at the time of writing.)
- Batch11 mixAB (F20 170 with sigma A 4,4,2,2,2,2,1 and sigma B 4,4,4,2,2,1): far 190. Worse than the same sigma on both sides (160).
- Stopped the queued batch11 mixBA / batch12 (plain SA comparison) to free the CPU for the D5 runs.
- Batch13 final: D5 170 with PV 0.8 (seeds 10, 11, 13) and PV 0.95 (seed 12): all far 155 (five runs in total with seed 9). Plateau.
- Batch14 (queued 20:12Z): D5 at n=180 (alpha 4, sigma 2^9, PV 0.8, seeds 14, 15), and D5 at 170 with K=80 (120 s, seed 16).
- Batch14 (20:12-20:17Z): D5 at n = 180, PV 0.8 (seeds 14, 15): far 185 both (the same value as r3a's D5 185 at 180; logged
  r3b/best/n180_D5_PV08_far185.edges). D5 at 170 with K = 80 (seed 16): 155 again.
- Batch15: F20 at 180 with PV 0.8, seed 17: 270 (same as PV 0.5). Seed 18 running.
- Batch16 (queued): other D5 involution types with PV 0.8: 170 with sigma 2^7 1^3 (seed 19), 2^6 1^5 (seed 20); 180 with 2^8 1^2 (seed 21).
- Batch16 (D5, PV 0.8, 90 s): sigma 2^7 1^3 at n = 170 (3 fixed base vertices per side, seed 19): FAR 110 (diam 8). New best
  for r3b at 170 (logged: r3b/best/n170_D5_2to7_1to3_far110.edges). Sigma 2^6 1^5 (seed 20): 140. Sigma 2^8 1 gave 155
  (seeds 9-16). So the number of fixed base vertices matters; 3 was best of the three tried.
- Batch18 (queued): D5 at 170 with 2^5 1^7 (seed 31), 2^4 1^9 (seed 32), 2^7 1^3 with seed 34 (variance), and D5 at 180 with
  2^7 1^4 (seed 33).
- 20:24-20:27Z (coordinator redirect: symbo on r3a's D5 sigma 2^7 1^3 group, n = 170): r3a's far-60 graph
  (r3a/best/n170_D5_7_7_far60.edges) is G-invariant under my group file (order 10). symbo from it: PV 0.8 seed 51 -> 60;
  PV 0.5 seed 52 -> 60 (no change). Fresh SAT starts seeds 53..60 (PV 0.8, 90 s each) are running (out/b19).
- Fresh SAT starts on the D5 2^7 1^3 group (symbo, PV 0.8, 90 s): seed 53 -> 90, 54 -> 120, 55 -> 110, 56 -> 60
  (out/b19/fs56/best_best.edges, score37 far 60; a different graph from r3a's far-60 file by md5 of the sorted edge list).
  So the 60 floor is reached from fresh starts by the breakout engine too (1 in 4 seeds so far).
- Batch19 summary (fresh SAT starts 53..60, same group and settings): far 90, 120, 110, 60, 90, 90, 110, 90. Only seed 56 reached
  60; no run went below 60. So on this group the breakout engine reaches the 60 floor about once in eight fresh starts, and
  it does not descend below it from the far-60 states (PV 0.8 / 0.5 from 60: no change).
- Batch21 (fresh SAT starts 61..68 on the D5 2^7 1^3 group, PV 0.5, K 80, 90 s): far 60, 90, 60, 60, 60, 60, 60, 90.
  Six of eight reach 60; none below 60. Batch20 (K 200 / PV 0.95 / STALL 300 from the far-60 graph): all 60.

## Final summary (r3b, 19:06Z -> 20:57Z)
- n = 170, best far 60: D5 = Z5 x| Z2 (alpha 4), sigma 2^7 1^3 on both sides (the r3a group). Breakout symmetric search
  (symbo) reaches 60 from fresh starts in about 1 of 3 seeds and never goes below 60 from the 60 states (PV 0.2-0.95, K 40-200,
  elite restarts). Files: r3b/best/n170_D5_2to7_1to3_far60_fresh56.edges (fresh) and r3a's r3a/best/n170_D5_7_7_far60.edges.
- Other logged bests: n = 170 D5 sigma 2^8 1 far 155 (PV 0.8); F20 (Z5 x| Z4, alpha 2, sigma 4,4,2,2,2,2,1) far 160;
  n = 180 D5 sigma 2^8 1 far 185 (PV 0.8), F20 (sigma 4^4 2) far 270; n = 182 F21 far 210; n = 196 F21 far 224.
- Verdict: no graph below 46 at n = 170 from this search; the 60 floor is robust across seeds, PV, K and restarts.
