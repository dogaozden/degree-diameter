# c20 notes (downward surgery from near misses above 684)

Card: go DOWN from graphs above 686 with few far pairs (720 Haar near miss, 704 lift, 732 graph), delete vertices, repair
degrees, local search at fixed n >= 686. Target bad 0.

## Files
- analyze.py: all-pairs BFS, far-pair structure (`python3 analyze.py EDGES`, 0.5 s at n=720).
- dsa.c / dsa: DOWNWARD SA. env INFILE, DELA / DELB (vertices deleted from side A / side B), DELMODE greedy|rand
  (greedy: exact cost after each candidate deletion, SAMPLE candidates per step), SECS, T0, T1, SEED, OUT, TARGET.
  Moves: 2-switch (degree-preserving), greedy ADD between deficient opposite-side vertices (never raises cost).
  Max degree 6 is kept; deficits left after deletion are filled by ADD.
  Cost = unordered pairs at distance > 5 (bit-parallel BFS, ~0.3 ms per evaluation at n=720, ~3000 moves/s).

## Structure of the 720 Haar near miss (c6/h360_53.edges, SmallGroup(360,53), bad 360)
- All 360 far pairs are at distance exactly 6, all inside one side (vertices 360..719). Every vertex of that side has exactly
  2 far partners (a 2-regular graph, union of cycles); the other side has none. So the defect is one-sided: same-side
  even distances 6 instead of <= 4. Covering all 360 by deleting vertices would need about 180 vertices (n ~ 540): not
  possible inside 686..720; only rewiring can fix it.

## Downward runs (19:05-20:05)
Tools: dsa.c (deletion + fill + SA with 2-switch and deficit moves), mkunbal.py (add vertices of one colour and rewire),
greedyz.py / cover.py / mkcover.py (covering start for a new vertex), farstat.py / analyze.py / fibres.py (far-pair structure).

| start | n | start cost | after SA | file / note |
|---|---|---|---|---|
| 720 Haar (c6), delete 17 A + 17 B greedy, random fill, SA 150 s | 686 | ~1300 | 1274 | (not kept) |
| same, greedy fill (60 samples per edge), SA 230 s, T 0.6 -> 0.1 | 686 | 1134 | 1116 | (not kept) |
| 720 Haar, delete 10 + 10 greedy, SA T 0.6->0.1 / 2.5->0.4 / 8->1 | 700 | 900 | 899 / 900 / 900 (hot run drifts to 3700) | d700_720*.edges |
| c7 guided SA (gsa) from the 700 start, 120 s | 700 | 900 | 891 | g700_from720.edges |
| 704 lift (c1), delete 9 + 9 greedy, SA cold / hot | 686 | 696 | 690 / 683 | d686_704*.edges |
| 684 Haar + 2 B-vertices (sides 342+344, 12 B-deficits), deficit SA 200-260 s | 686 | 743 | 392 | ub686_s*.edges |
| 684 Haar + 1 A-vertex (sides 343+342, 6 A-deficits), random rewire, SA 150 s (3 seeds) | 685 | 743 | 193, 195, 195 | u685_a*.edges |
| same, covering start (6 B-vertices whose 3-balls cover all 342 A-vertices), random drops | 685 | 362 | 185 | u685_cov1_sa.edges (verified bad 185) |
| covering start, greedy choice of the dropped edges (greedyz.py) | 685 | 226 | 187 | u685_gz1_sa.edges |

Findings:
1. Every start from the 720 Haar near miss or the 704 lift is far worse than the 684-based one: deleting 17+17 vertices (or
   9+9, or 10+10) and refilling gives 700-1300 far pairs, and the SA cannot descend. A random 2-switch on these states costs
   about +50..+100 (checked with DBG=1), so the 2-switch neighbourhood is very rugged there; T0 = 0.6 never accepts and
   T0 = 8 drifts up to about 3700. Guided moves (c7 gsa) move 900 -> 891 in 120 s. No descent.
2. Structure of the 720 Haar near miss (c6/h360_53.edges): all 360 far pairs are at distance 6, all on one side, and each
   vertex of that side has exactly 2 far partners (a 2-regular Cayley-type relation, so the missing set is 2 group
   elements). The 704 lift (c1/best704.edges) is the same: 176 far pairs inside fibre 0 and 176 inside fibre 3, each
   vertex in exactly 2 of them. The defect is one-sided and fibre-local: one missing element per side, not spread out.
3. Non-regular family (max degree 6 is the goal, so regular is not required). A 685-vertex graph with parts 343 + 342,
   6 vertices of degree 5 on the 343 side and a full 342 side: every far pair is same-side at distance 6 (see farstat.py).
   Covering start (new vertex u adjacent to 6 B-vertices whose 3-balls cover all 342 A-vertices: found by cover.py in 36
   random greedy trials, ball3 size 140 each) gives 185 after 180 s. That is the best so far in this family: no bad 0.
   The 686 unbalanced family (342 + 344) is worse (392): more deficits hurt more.
4. Reading: the 2-switch / deficit SA always lands in the 177-195 band for 685/686 starts built from the 684 graph
   (balanced 686: 177, c7; unbalanced 685: 185). Starts built from 704/720 stay above 680 and do not descend.

Next ideas if time: exhaustive 2-switch scan on u685_cov1_sa.edges (scan3-style) to test strict local minimality;
covering starts with 2 new vertices at 686 (A and B), each with its own covering set chosen so the two cover sets overlap
the removed edges least.

## Later runs (20:00-20:20)
- 686 regular with two covering new vertices (cover2.py: u in A adjacent to 6 B-vertices whose 3-balls cover A, v in B
  adjacent to 6 A-vertices whose 3-balls cover B; 6 removed edges, no uv edge): start 348, SA 180 s -> 314 (u686_cov2_sa.edges).
- c7-style 686 (cover3.py: 5 removed edges, u adjacent to 5 w's and v, v adjacent to 5 z's and u; covering search reached
  336/342 and 334/342): start 253, SA 150 s -> 221 (u686_cov3_sa.edges). Both worse than c7's 177 insertion.
- 685 unbalanced, covering start (u685_cov1.edges): T 1.5 -> 0.25, DEFP 0.3, 240 s, seed 77 -> 184 (u685_cov1_s77.edges,
  verified bad 184). Best of the 685 family so far. Same start, T 1.0 -> 0.2, seed 1 -> 185.
- 685 from greedy-z start (u685_gz1.edges), T 1.5 -> 0.25, seed 88 -> 191.
Summary of the 685 family (6 deficits on the 343 side): 184..195 over 7 runs; floor not broken.

## Best so far at n = 685 (20:30-20:41): delete a vertex from c7's 686 graphs
- c7/best686_bad177.edges has 19 far pairs at its new B-vertex (id 685). Deleting it gives a 685-vertex graph with 6 A-side
  deficits and start cost 214. dsa SA (DEFP 0.3, T 1.0 -> 0.2, 200 s, seed 121) -> 165 (del685_0_sa.edges, verified
  bad 165). Seed 131 (T 1.5 -> 0.25, 240 s) also 165. Scoreboard line written at 20:30.
- Deleting the worst B-vertex (22 far pairs) of c7/best686_bad178.edges: start 217 -> 165 (del685_178_sa.edges).
- Deleting the worst A-vertex (684, 20 far pairs) of the 177 graph: start 219 -> 183.
- Reading of the 165 graph (farstat.py): all 165 far pairs are same-side at distance 6, 40 of them touch the new A-vertex
  684 (degree 4 after the deficit moves), 89 touch a degree-5 vertex, 498 vertices lie on no far pair.
- Two different starts reach the same 165 value: this looks like a basin floor for the 685 family built from c7's graph.
- Final runs (20:42-20:49): del686_0 with DEFP 0.5, T 0.8 -> 0.12, seed 161 -> 194; del686_178 with T 1.2 -> 0.2, seed 171 -> 191.
  Best stays 165 (del685_0_sa.edges).

## Final state (20:50 UTC)
- Best n > 684: 685 vertices, bad 165 (del685_0_sa.edges; verified with shared/score65). Not a record: bad must be 0.
- Best n = 686 is not in this folder: the 686 graphs are the squad's c7 ones (177). My 686 starts gave 221-314.
- Scoreboard lines from c20: 393 (686), 185 (685), 184 (685), 165 (685); 392 was a 686 run (not logged separately).
- Mechanisms that were confirmed: the 720 and 704 near misses cannot be pushed down; from the 684-based 686/685 family
  the SA floor is 165-195 depending on start.
- Ideas not run: a 2-switch exhaustive scan on del685_0_sa.edges (strict local minimum test); deletion of two vertices
  from a 688 graph (c10/c13 graphs) to test whether 686 can be reached from a different basin.
