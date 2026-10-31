# c24 notes (card: free local search on whole 686-vertex graphs)

Tools (copied from c7 and compiled here): gsa (guided SA over 2-switches), ft (focused tabu), tab2, scan3 (exhaustive
2-switch scan), sa, lns, symsa, and lahc (copy of gsa with late-acceptance hill climbing; env LAHC, DELTA).
hot.sh START SEED T0 T1 SECS TAG: one guided-SA restart (writes hot_TAG.edges / .log, prints the verified score).
Command pattern (always foreground, one at a time):
  INFILE=b686_159.edges OUT=x.edges SEED=22 T0=4 T1=0.4 SECS=240 timeout 300 nice -n 10 ./gsa > x.log

Results (20:00-20:26):
- Start graphs: t294_686.edges (c18, bad 294), best686_bad177.edges (c7, bad 177), t728.edges (c17, bad 546).
- Landscape is very rugged: scan3 on the 294 graph (1.2M valid 2-switches): no improving switch, smallest increase +20.
  From 294 and 177 the guided moves almost never go down or sideways (gsa T 1.5 -> 0.2: 0 accepted in 600k steps).
- Focused tabu (ft, K=200, TT=25) from 294 drifts up to cost ~4200 and never returns (best 294).
- LAHC (history threshold 15 or 40) from 177 or 294: 0 to 11 accepted moves per 1M steps. Useless here.
- Hot SA DOES work: gsa with T0 = 3 -> 0.4 from the c7 177 graph reached 172 (new best, b686_172.edges), then
  T 5 -> 0.5 from 172 gave 170 (b686_170.edges), then T 4 -> 0.4 from 170 gave 159 (b686_159.edges, verified).
  Restart from 159 at T 4 -> 0.4 (seed 22): no gain.
- Hot SA from 294 (T 8 -> 1.3): cost drifts to ~3300 and does not come back in 240 s (best 294).

Scoreboard: c24 lines for 172, 170, 159, 158, 144 (all verified with shared/score65).
Next ideas: more hot restarts from 159 with different T0 (2, 6) and seeds; longer cooling (T1 0.3); keep the best.

Later runs (20:26-20:49), all via hot.sh (guided SA restarts):
- From 159: T 2.5->0.3 (no gain), T 6->0.5 (no gain: only 41 accepted moves in 680k steps, cur stays 178-183),
  T 3->0.3 seed 51 gave 158 (b686_158.edges, recorded on scoreboard). From 158: T 3->0.3 and T 2->0.2: no gain.
- Acceptance is very low even at T 6 (proposals cost +20 or more), so the proposal generator is the bottleneck, not the
  temperature. Each run is about 0.4 ms per evaluation (full bit-parallel BFS), about 2.4k proposals/s.

State at 20:50: best bad=158 at 686 vertices (c24/b686_158.edges, verified by shared/score65). No record (bad > 0).
Next idea (not done): incremental cost (only pairs touched by the switch) or a proposal that picks, for a far pair,
the z/p pair that minimises the damage (exhaustive over the 12k switches at one far pair, then accept the best).
- 20:53: T 4 -> 0.3 from 158 (seed 81) gave 144 (c24/b686_144.edges, verified, on scoreboard). Best so far: bad=144.
  Restart schedules with T0 3-4 keep finding small gains; T0 2 and T 6 did not.
- 20:58: T 4 -> 0.3 from 144 (seed 91, 250 s): no gain. Final state: best bad=144 at n=686 (c24/b686_144.edges).
  No bad=0, no record. Processes: none left from c24.
- 21:01: T 3.5 -> 0.3 from 144 (seed 101, 180 s): no gain. Stopped at 21:01 with bad=144 (c24/b686_144.edges).
