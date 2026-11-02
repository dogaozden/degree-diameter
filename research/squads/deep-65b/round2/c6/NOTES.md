# round2 c6 (deep-65b): tabu15f, a faster tabu with the same search rule

Start 23:55 UTC (time box 60 min). Machine load was 7-9 on 4 cores during the run, so timings are noisy;
paired runs (same seed, same wall time, back to back) are the fair comparison.

## Code: tabu15f.c (this folder)
- Build: `gcc -O3 -march=native -Wall -o tabu15f tabu15f.c -lm` (clean, no warnings).
- Same search rule as shared/tabu15.c: full scan of 10 positions x m candidates, tabu tenure 10+rnd%5,
  aspiration against best_all, random tie-break with the same rnd() calls, restart after 1500 non-improving steps.
- Faster evaluation (exact set identities, no approximation):
  - EE^-1 = QM u QF u X u X^-1 and E^-1E = PM u PF u Y u Y^-1 with X = M F^-1, Y = M^-1 F (M = moved 5-set, F = fixed).
    That is 50 products instead of 100 for the two big sets.
  - everything depending on the fixed side only (QF, PF, QF^2, PF^2, QF F, lists) is cached once per step.
  - cheap conditions first (C2, C3, C5, C6), squares C1 and C4 last.
  - early abort: a candidate is abandoned once the partial miss sum exceeds thr = bv (non-tabu) or
    min(bv, best_all-1) (tabu). Such a candidate can never be chosen or tie, so the trajectory is unchanged.
- Modes: `tabu15f TAB SEED SECS [EDGES_OUT]` (RES line as tabu15), `tabu15f TAB cost e1x5 e2x5`, `tabu15f TAB check N`.

## Checks
1. Self-test: `./tabu15f ../../groups/sg_176_23.tab check 200` -> states=200 moves=6000 mismatches=0
   (fast total equals the reference total for both roles, and for every single-element move with and without threshold).
2. 20 random states (states20.txt, python seed 65) against `shared/split15 TAB cost ...`: all six counts equal
   (cmp20.txt; regex check: 20 lines, 0 mismatches).
3. Same trajectory as tabu15: seed 3 on sg_176_23 gives iters=411, E1=55,34,136,108,115 E2=37,122,162,26,46 in both programs.
4. Graph of seed 3 (seed3_176_23.edges): score65 bad=0, maxdeg 6, diameter 5, `apsp ... 6 5` RESULT VALID n=704.
   This re-finds the known 704 record; it is not a new record.

## Speed (sg_176_23, paired runs, same seed, same wall time)
- seed 1, 10 s: tabu15 1103 steps (110/s); tabu15f 3670 steps (367/s): 3.3x (paired_speed.txt).
- seed 3, run to zero: tabu15 8.92 s (411 steps, 46/s); tabu15f 2.55 s (161/s): 3.5x. Second run of tabu15f: 1.24 s.

## Time-to-zero on sg_176_23 (tabu15f, seeds 1..10)
- seed 3: zero at 2.55 s / 411 steps (cap 40 s; the only zero).
- seeds 1,2,4,5,6,7,8,9,10 (cap 20 s each): no zero; best costs 2, 7, 3, 3, 7, 5, 5, 3, 5 (ttz_176_23.txt).
- Round 1 tabu15 found zero at seed 3 in 5.75 s; the step sequence is identical, so the speedup is the whole gain.

## Order 192 (n = 768), non-abelian groups with ids 1..127 (not in c3/c4 lists)
- Export: `shared/gapw -c 'ORDER:=192; IDS:=[1..127]; OUTDIR:="round2/c6/tabs";' tools/gap_fast.g` (run from
  research/squads/deep-65b; about 1 s per group; the GAP syntax warnings are harmless). Ids 2 (C192) and 127 are abelian: skipped.
- Scan: `round2/c6/scan192.sh` (resumable; todo192.txt; 2 seeds x 8 s per group with tabu15f; no new group after 80 s per call),
  results in raw192.txt (id seed best t_best name); zeros in hits/HITS.txt with edges in hits/.

## Order 192 result (ids 1..127, 125 non-abelian groups; ids 2 and 127 abelian; c3/c4 ids not touched)
- 2 seeds x 8 s per group with tabu15f (raw192.txt). No zero. Best cost per group: min 8 (ids 58, 105, 106),
  then 9 (11, 53), 10 (20, 37, 102, 117), 11 (71); median 17; max 288 (id 7, D192, both seeds the same).
- Scale: at m = 176 the tabu reaches 2 (sg_176_23) and at m = 192 the best is 8, so no order-192 group in ids 1..127
  is near 0 with this budget. Ids 58, 105, 106 are the ones to re-run with more seeds.
- Not done (time box): ids 128..1543 at order 192 (c3/c4 cover 128-1535 partly), and longer runs on the best groups.

## Files
- tabu15f.c, NOTES.md, cmp20.txt, states20.txt, paired_speed.txt, ttz_176_23.txt, seed3_176_23.edges (704-vertex graph,
  verified: score65 bad=0, apsp RESULT VALID), scan192.sh, todo192.txt, raw192.txt, hits/ (empty), tabs/ (order 192 tables, ids 1..127).
