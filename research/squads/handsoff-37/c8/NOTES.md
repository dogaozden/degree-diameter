# c8 notes (wildcard)

Start: 2026-10-31 15:44:44 UTC (date -u). Stop about 17:44 UTC.

## Chosen approach

Large-neighbourhood search with exact re-matching ("ruin and recreate" on stubs), unstructured cubic bipartite graphs.
Pick a ball of radius 1..3 around a vertex (biased to vertices with far pairs), remove s edges inside it, and
enumerate ALL s! ways to re-pair the 2s freed stubs (A-stubs to B-stubs, simple graph kept). Score each re-pairing with
an all-pairs bit-parallel BFS (about 5-10 us at n = 170), then choose one by Boltzmann (heat-bath) sampling at
temperature T. Neighbourhood per move = s! graphs, far bigger than the 2-switch neighbourhood of c7 and c1.
Other cards: c7 uses 2-switch tabu; this card uses exhaustive k-switch rewiring of a local region.

Also considered and not started: SAT (python-sat is installable here) with a Z_p lift. The walk-reachability encoding
needs about 3M auxiliary variables at n = 170, so it was left aside.

## Log

### 15:50 calibration, n = 150, 30 s runs, one seed (far = unordered pairs at distance > 7, after 30 s)
| s (edges removed) | T | pb | R | far |
|---|---|---|---|---|
| 6 | 0.5 | 0.5 | 2 | 65 |
| 6 | 2 | 0.5 | 2 | 84 |
| 7 | 1 | 0.5 | 2 | 58 |
| 5 | 1 | 0.5 | 2 | 39 |
Speed: about 126k leaves/s at s = 6 (all-pairs BFS per leaf, n = 150).
### 15:58 second calibration batch, n = 150, 30 s, seed 7 (same metric)
| s | T | pb | R | far |
|---|---|---|---|---|
| 3 | 1 | 0.5 | 2 | 26 |
| 4 | 1 | 0.5 | 2 | 29 |
| 5 | 0.5 | 0.5 | 2 | 46 |
| 5 | 2 | 0.5 | 2 | 74 |
| 5 | 1 | 0.5 | 1 | 35 |
| 5 | 1 | 0.2 | 2 | 51 |
Reading: small regions and T about 1 win. Large s (7, 8) is slower per move and worse at equal time (58, 91). So the
exhaustive re-matching only helps when it is cheap; the engine behaves like annealing with 3-switches.
Insight: far = 0 at n >= 170 needs excess R(v) <= 42 at every vertex, which needs about 42 collisions per radius-6
even tree. With girth 12 that means about 42 twelve-cycles through each vertex (the 168 graph has this). Random
cubic graphs have about 61 excess, so unstructured search is far from 0 from the start.
Start for n = 170: conder168 plus one inserted pair (random choice of the 2 deleted edges, mkins.py): far = 66.

### 16:00 batch 3, n = 150, 30 s, seed 7 (same metric)
| s | T | pb | R | far |
|---|---|---|---|---|
| 2 | 1 | 0.5 | 2 | 30 |
| 3 | 0.7 | 0.5 | 2 | 28 |
| 3 | 1.3 | 0.5 | 2 | 38 |
| 3 | 1 | 0.8 | 2 | 30 |
| 3 | 1 | 0.5 | 3 | 35 |
Noise is about +-4 between seeds. Default chosen: s = 3, T about 1 (cooled), pb = 0.5, R = 2.

### 16:02 n = 170, 120 s from conder168 + one inserted pair (mkins.py seed 1, start far 66): far 46.
Logged as the first c8 graph at n = 170 (c1 has the same far 46 from exhaustive surgery).
File: c8/best170_far46.edges (score37: far=46, diam=8).

### long batch launched 15:59 (c8/long1.sh, log c8/out/long1.log, each 540 s):
L1 continue from the 46 graph, T 0.8 -> 0.3; L2 insertion seed 2, T 1 -> 0.3; L3 random cubic start, T 1 -> 0.3.

### 16:08 long batch L1 (continue from the far-46 graph, T 0.8 -> 0.3, 540 s): NO accepted move in 8.1 M moves, far stays 46.
Diagnosis (histogram of leaf far minus current far, out/dbg runs): around the far-46 graph almost every re-matching of
3, 4, 5 or 6 removed edges either leaves far unchanged (about 40% for s = 3, 6% for s = 6) or raises it by 10 or more.
Nothing in between. So the 46 graph is a deep isolated well for LNS moves, and cooling to 0.3 freezes it.
The L2 run (insertion seed 2) was stopped for the same reason. Lesson: LNS from structured starts stalls; the
annealing temperature has to stay near 1 or the start must be unstructured.
Also: all 46 far pairs are same-side (opposite-side far = 0), spread over 76 vertices, at most 2 per vertex.

### 16:08-16:17 random start and kicks
- Random cubic start at n = 170 (LNS, s = 3, T = 1, 240 s): far 1995 -> 132 in 100 s, then flat at 132-135.
  Unstructured search is far from the target at 170, as the card warned.
- Kick tests (ils1.sh): one random 2-switch on the far-46 graph raises far to 110-150; a 40 s LNS descent (T 0.6) returns
  to 46 (twice), 48 (once). The 46 basin is an attractor. Note that 46 is also the exhaustive best single-pair insertion
  into conder168 (c1 log), so the LNS reproduces the c1 optimum and does not go beyond it.
- Insertion starts from conder168 (mkins.py, seeds 3..8): far 60..73 before repair (c8/out/ins170_s*.edges).

### 16:17 wildcard seed: the GH(2,2) incidence graph (Tutte 12-cage), built from the split Cayley hexagon H(2)
gh2.py: points = the 63 points of Q(6,2) (x0x4 + x1x5 + x2x6 + x3^2 = 0 over GF(2)), lines = the totally singular
lines satisfying the six Tits equations on Plucker coordinates (315 singular lines, 63 satisfy them). Result:
n = 126 cubic bipartite, girth 12 (checked), diameter 6 (score37: far 0, diam 6). File: c8/out/gh126.edges.
Plan: grow it to 170 by 22 pair insertions, each followed by a 15 s LNS repair (grow.sh).

### 16:20 greedy growth GH(2,2) -> 170 (ggrow.sh; insbest.c = exhaustive best 2-edge insertion over all 17k-20k
choices, then 15 s LNS repair at T 0.8, s 3)
far by n: 128..136 = 0; 138: 2; 140: 6; 142: 7; 144: 15; 146: 28; 148: 36; 150: 49; 152: 63; 156: 59; 160: 84;
164: 119; 168: 159; 170: 170. Each insertion adds far; the 15 s repair cannot keep up after n = 138.
So the GH(2,2) seed does not lead to the 168 structure; the GH route is a dead end for 170.
(The random-insertion variant of this (grow.sh, killed at n = 144) was similar: 9 at 138, 19 at 144.)
Comparison at n = 150: random-start LNS 26 in 30 s, GH-grown 49.

### 16:30 insertion-seed runs (ins2.sh, 240 s each, T 1 -> 0.4, s = 3)
seed 7 (start far 60): 48. seed 5 (start 63): 46. Cheap invariant (invariant.py, sorted vertex distance profiles):
the far-46 graphs from the first insertion run (t2f), the L1 continuation, and seed 5 have the same invariant
(hash 93596860, 11 profile classes), so they are very likely the same graph. Seed 7's 48 is a different graph.
So from conder168 + one pair the LNS keeps finding one attractor at 46, which c1's exhaustive insertion also reaches.
Seeds 3 and 8 (16:30-16:41): seed 3 -> 48 (same invariant as seed 7, a second basin), seed 8 -> 46 (same invariant as
seed 5, the 46 basin). So over 8 insertion seeds plus the first run, the 46 graph is reached 4 times, the 48 graph 2 times.
The 46 graph is the only far < 48 found by LNS from the 168 family, and it equals c1's exhaustive best.

### 16:40-16:50 n = 172 and medium kicks
- Two exhaustive best insertions from conder168 (insbest twice): n = 170 far 46, then n = 172 far 80. LNS 240 s at 172
  (T 1 -> 0.4): no progress at all (80 stays 80, 2.6 M moves). Logged as c8 172 far 80 (c8/best172_far80.edges).
- Medium kicks (3 random 2-switches on the 46 graph, then 60 s LNS at T 0.8 -> 0.3): far after descent 46, 174, 156, 127
  (seeds 11..14). Most descents end in high-far basins, so the 46 well is only one of many, and LNS does not climb down.

### 16:52-17:00 structured reductions and multi-insertions (all end at the same 46 graph)
- red2ins.py: all 504 choices of a reduction of conder168 by one vertex pair (remove adjacent a-b, reconnect the four outer
  neighbours in the 2 possible ways: n = 166), then two exhaustive best insertions (n = 170). 292 valid options: far 46
  for ALL of them.
- red3.py: 120 random sequences of two reductions (n = 164) then three greedy insertions (n = 170): far 46 in 120 of 120,
  and the invariant hash (93596860) is the same as for the 46 graph found by LNS. So from the 168 family the greedy
  and LNS chains all land on one graph of far 46.
- networkx VF2 could not count automorphisms of the 46 graph within 40 s (not pursued).

### 17:02-17:06 conder168 with 2 random 2-switches, then insertion, then 30 s LNS (kick168.sh, 8 seeds)
After the insertion: far 85..198. After LNS: 48, 48, 48, 46, 48, 48, 48, 46. The 46 runs have the 46 invariant
(hash 93596860); the 48 runs have the 48 invariant (hash 56193482). So the search funnels into exactly two graphs.

### 17:07 campaign red3lns.py (60 trials: random two reductions, three greedy insertions, 20 s LNS) (out/rl2.log)
Running at the time of writing; each trial starts from the 46 family and stays at 46 (see out/rl2.log).

## Summary (for the coordinator)
- Best n = 170: far 46 (c8/best170_far46.edges, score37 verified). c1 (exhaustive insertion) gets the same 46, and c7 too.
- LNS (exact stub re-matching, s = 3, heat bath T about 1) is a sound engine but it does not beat 46.
  Calibration: n = 150, 26 far in 30 s from random; n = 170 random start: 132 after 4 min (flat).
- The 46 graph is a strong attractor: from 3 insertion seeds, 2 reductions + 3 insertions, kicked conder168, and
  the 292 single-reduction options, LNS and greedy chains end at 46 or 48. Two basins, no others below 80 seen.
- Walls: at the 46 graph (and near 48) every re-matching of 3..6 removed edges either keeps far or adds at least 10.
  Cooling does not help (the 540 s continuation run made 0 accepted moves in 8.1 M).
- GH(2,2) (Tutte 12-cage, built from Q(6,2) with the Tits equations, gh2.py) grown by pair insertions with repair: far
  stays 0 to n = 136 and then climbs to 170 at n = 170. Dead end.
- n = 172: far 80 (c8/best172_far80.edges; two exhaustive insertions from conder168; LNS made no progress).
- Reformulation for whoever uses it: for a cubic bipartite graph, the condition for one side is that the hypergraph with
  B-vertices as 3-edges on A-vertices has primal (2-section) diameter <= 3. Both sides are needed.

### 17:27 campaign result (red3lns.py, 60 trials, 20 s LNS after 2 reductions + 3 insertions): far 46 in 60 of 60 trials.
Final: no graph below 46 at n = 170 from this family. Stop time 17:44 UTC (about 2 hours).

Files: lns.c (LNS engine), insbest.c (exhaustive 2-edge insertion), gh2.py (GH(2,2) builder), kick.py, mkins.py,
red2ins.py, red3.py, red3lns.py, kick168.sh, ggrow.sh, invariant.py (cheap isomorphism invariant), best170_far46.edges,
best172_far80.edges. Everything else is under out/ (not committed).
