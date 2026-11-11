# h7 notes (round 2, deep-65): non-abelian voltage groups of order 50 on 14-vertex bases

Start 03:22 UTC, stop 04:22 UTC. Work dir: research/squads/deep-65/round2/h7.

Setup
- tabu.c, score65.c, apsp.c copied from shared/ and built (gcc -O3 -march=native ... -lm).
- Bases (voltages stripped to 0, INIT=random): base294.vl (from lift_294_11_cost12.vl), base147.vl (from
  lift_147_3_cost12.vl), crown.vl (K7,7 minus a perfect matching). All 14 vertices, 42 edges, 6-regular.
  Note: the two lift bases are multigraphs (e.g. three parallel edges 0-9); parallel edges get distinct voltages.
- Group tables by GAP: gap -q -c 'ORDER:=50; OUTDIR:="groups";' tools/gap_tables.g (and ORDER:=49).
  groups/sg_50_1..5 are the five groups of order 50, groups/sg_49_1 = C49, sg_49_2 = C7 x C7.
- Single-vertex-change tabu: SECS per run <= 100, one command per run or chain with total time <= 100 s.

Calibration
- The lift files need their own C7xC7 tables: with c7xc7_from_294_11.grp the lift_294_11 start cost is 12, with
  c7xc7_from_147_3.grp lift_147_3 is 12 (cost function verified). With groups/sg_49_2.txt (a different labelling of
  C7xC7) the same voltages give 542 and 342, so those voltages are only meaningful with the matching table.
- Tabu speed: about 0.3-0.6 s per step (29 free edges x 49-50 values per step, full cost). 140-440 steps per run.
- Random-start tabu on the abelian control C7xC7 reaches 74-102 in 40-90 s, never near the known 12. Differences of
  about 15-20 between seeds are noise. Only runs of this length were affordable in the time box.

Runs (tabu.c, INIT=random, cost = uncovered (base vertex, element) pairs; all logs in runs/, results in runs/*.res
or the last "best" line of runs/*.log for runs whose RESULT went to the terminal)
cost seeds (SECS)           base294 (n=700 / control 686)   base147                       crown K7,7-PM
D50 (sg_50_1)               211 (s1, 90)                    138 (s1,s2; 45)               123 (s1 127, s2 123; 45)
C50 (sg_50_2)               98 (s1), 107 (s2) (45)          95 (s1, 45)                   86 (s1), 92 (s2) (45)
C5xD10 (sg_50_3)            84 (s1), 101 (s2) (45)          100, 96 (45), 82 (s3, 90)     96 (s1), 97 (s2) (45)
(C5xC5):C2 (sg_50_4)        215 (s1), 205 (s2) (45)         140 (s1, 45)                  117 (s1, 45)
C10xC5 (sg_50_5)            103 (s1), 89 (s2) (45)          76 (s1), 95 (s2), 88 (s3, 95) 95 (s1), 99 (s2) (45)
C49 control (sg_49_1)       88 (45)                         72 (40)                       78 (35)
C7xC7 control (sg_49_2)     102 (40), 82 (45), 74 (s4, 90)  82 (45)                       82 (45)

Findings
- No cost-0 lift for any base or group; no export or apsp run was needed.
- Dihedral (D50) and (C5xC5):C2 are worst on every base (117-215 vs 76-107 for C50, C10xC5). Their random starts are
  also higher (about 600-740 vs 400-500).
- C5xD10 (non-abelian, C5 x D5) is level with the abelian groups (82-101). So non-abelian groups do not help in this
  test; the two cyclic-containing abelian groups and the C49/C7xC7 controls are as good as C5xD10.
- Caveat: the random-start search is the bottleneck (it does not reach the known 12 even for the abelian C7xC7
  case), so these numbers rank search difficulty, not the best attainable cost.

Mistakes and fixes
- One chained run (C49 then C7xC7, 40 s each on base147) hit the 105 s timeout; C7xC7 on base147 was rerun alone.
- Scoreboard END line score 72 is from the C49 control (n 686), not an order-50 group: the best order-50 value is 76
  (base147, C10xC5, seed 1). A correction line is appended to scoreboard.jsonl.
