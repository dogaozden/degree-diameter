# c1 NOTES (card c1: grow the 168 graph by surgery)

Start: 2026-10-31T15:44:23Z (date -u). Stop about 17:44Z.

Plan:
1. Exhaustive 2-edge and 3-edge insertions at n = 170 (fix first edge, conder168 is arc-transitive). Record far histogram.
2. Repair: 2-switch local search (SA / tabu) on best insertions, restricted then unrestricted.
3. n = 172+: beam of insertions + repair.

## 15:48Z results

Code: g37.h (graph + far_cost via radius-7 reach sets, verified equal to score37), surgery.c, sa2sw.c (SA), tabu2sw.c (tabu).

Exhaustive surgery at n = 170 (base conder168, first edge fixed, A/B by BFS colouring; new a = 168 in A, b = 169 in B):
- 2-edge + a~b version: 247 graphs. best far = 46 (2 graphs, verified by score37), histogram 46:2, 54:8, 55:4, 57:4, 58:10, ...
- 3-edge version (no ab edge): 29891 graphs. best far = 48, 48:12, 56:12, 58:6, 59:12, 60:6, ...
- Both exhaustive families stay well above 0 (no far=0 candidate at 170 from one insertion of 2 vertices).
- Logged to scoreboard as c1 n=170 far=46 (c1/s170_k2_far46.edges).

Repair experiments (start = 46 graph):
- SA over 2-switches, T0..T1 = 3..0.2, 200k iters: 0 accepted, stuck at 46.
- SA T 30..3, 300k iters: drifts up to 295 (too hot). T 8..0.5 (3M iters): best stays 46, final 153.
  Note: random 2-switches on this graph raise far by 50..200, so SA at T <= 3 cannot move at all.
  Pure SA from a random local optimum lands near 140..170 at n = 170 (matching the calibration ceiling).
- Tabu over all admissible 2-switches (steepest non-tabu move, TT = 10): about 0.28 s per step at n = 170 (full
  neighbourhood ~ 32k moves). 20 steps: best 46, cur 54.
- 15:53Z: tabu2sw R=3 (candidate edges within distance 3 of the inserted pair, 500 s, TT 10): no improvement on far 46.
  Per-vertex unreached counts of the 46 graph: 94 vertices 0, 60 vertices 1, 16 vertices 2 (sum 92 = 2*46).
- Insertion from the 46 graph to n = 172 (insert.c, all 31875 edge pairs, a~b): best far = 80, histogram 80:1 84:2 87:6 88:5 ...
  The far roughly doubles per insertion before repair; repair is needed at every level.
- 15:55Z: tabu2sw R=3 finished: 100000 steps in 219 s CPU (candidate set is small), best stays 46, the walk wanders at cur 53..99.
  No improving move was found within the radius-3 neighbourhood of the inserted pair.
- 16:03Z: tabu3 full neighbourhood (MODE 0 and MODE 2, which is also full at 170 because 76 vertices are bad) from the
  46 graph: 1000 steps, best 46 (no move below 46 found; cur wanders 48..58). Tabu from the n=172 insertion of the 46 graph
  (far 80): 800 steps, best 80, cur 87..94. Single 2-switch tabu does not descend from these surgery graphs.
- Next: large-neighbourhood move (lns.c): remove an adjacent pair a~b, reconnect its 4 outer neighbours (2 ways), then
  re-insert a pair optimally over all edge pairs; first-improvement descent.
- 16:08Z: lns.c (remove adjacent pair, reconnect 4 outer neighbours in 2 ways, re-insert best pair over all edge pairs).
  One full pass on the 46 graph (510 moves, 101 s CPU): no improving move. The 46 graph is a local optimum for this move too.
- 16:13Z: ins4.c random insertion of 2 A-side + 2 B-side vertices (n = 168 -> 172), all 16 internal patterns, 400k random
  choices each: best far 82 (internal pattern 0110 = path-like H, 4 deletions). Not better than the 2-pair chain (80).
  Random 6-edge deletions are clearly worse than the structured 2-pair insertions at this size.
- 16:14Z: CALIBRATION of the repair at n = 168 (known solution exists): a copy of conder168 with 6 random 2-switches
  (far 465..584) is repaired to far 0 by full tabu (tabu3 MODE 0, TT 10) in 6 steps. With 20 random 2-switches
  (far ~1000), 60 s of tabu stalls at 137 and 158. So the single-switch tabu has a small basin of attraction.
- 16:23Z: the 6-switch calibration copy was repaired back to conder168 exactly (same 252 edges), so the repair only
  undoes perturbations; tabu tenure 3 / 10 / 40 on the 20-switch copy: best 163 / 137 / 123 after 60 s.
- 16:27Z: tabu tenure 40 from the 46 graph (200 s budget, ~800 steps): best 46 again.
- 16:35Z: iterated tabu (ils.sh: kick by 3 random 2-switches, tabu TT 40 for 45 s, accept if not worse), 5 rounds:
  every kicked run returned to far 46 (the tabu undoes the kick and lands on the same graph). 46 is a strong attractor.
- 16:40Z: repairs from the 48 (k3) and 54 (k2) surgery graphs (tabu TT 40, 50 s each, ~270 steps) all descend to far 46,
  and all four 46 graphs (also from the earlier runs) have an identical distance-profile signature (md5 of the sorted
  per-vertex distance-count vectors): tabu funnels to ONE far-46 graph (probably one isomorphism class).
- 16:48Z: two-level beam: exhaustive 2-pair insertion into the top 40 n=170 graphs (from conder168, k=2 and k=3 pools):
  best n=172 far = 80 again. Exhaustive 3-edge insertion (no ab edge, 2.6M triples) from the 46 graph to n=172: best 80 (4 graphs).
  So far 80 at n=172 is a floor for one insertion step from all the 170 candidates tried.
  Repairs of the n=172 insertions with tabu (TT 40, 50 s): from 84 -> 82; from the 4-vertex insertion (82) -> 82; from 80 -> 80.
- 16:50Z: n=174: pair insertion (exhaustive) into the n=172 far-80 graph gives far 125 (best of 32637). Tabu (TT 40, full
  neighbourhood, 60 s) -> 109; continued 300 s -> 107 (c1/s174_tabu_far107.edges, logged). Repair still descends at n = 174,
  slowly, so the descent is not stuck at this size.
- 17:05Z: chain of exhaustive pair insertions with tabu repair (TT 40, full neighbourhood):
  n=170: 46 (surgery, floor found in all searches); n=172: 80 (insertion, repair does not improve);
  n=174: 125 (insertion) -> 109 (tabu 60 s) -> 107 (tabu 300 s more);
  n=176: 143 (insertion from the 107 graph) -> 122 (tabu 150 s). Logged c1/s176_tabu_far122.edges.
  Each insertion roughly adds 20..40 to far, and tabu recovers only part of it; far grows with n along this chain.

## Summary (17:15Z)

Logged files (all checked with bin/score37; none has far 0 at n >= 170, so none went to records/):
| n | far | file | how it was made |
|---|-----|------|------------------|
| 170 | 46 | s170_k2_far46.edges | conder168, delete x1y1 and x2y2, add a~y1,y2, a~b, b~x1,x2 (first edge = edge 0, exhaustive over 247 second edges) |
| 172 | 80 | s172_ins_far80.edges | pair insertion into the 46 graph (all 31875 edge pairs) |
| 174 | 107 | s174_tabu_far107.edges | pair insertion into the 172 graph (far 125), tabu 60 s (109) then 300 s (107) |
| 176 | 122 | s176_tabu_far122.edges | pair insertion into the 174 graph (far 143), tabu 150 s (122) |

Rebuild: `./surgery ../shared/seeds/conder168.edges 2 out/x` writes the 46 graph as out/x_k2_top0_far46.edges
(identical to s170_k2_far46.edges); `./insert FILE 2 0 3 PREFIX` then gives the 172/174/176 insertions (top file = _r00_).

Negative results (all with numbers above):
- Exhaustive 2-edge+ab (247), 3-edge (29891) surgery at 170: min far 46 / 48. Two-level beam (top 40 of 170 graphs,
  then pair insertion): min 172 far 80. Exhaustive 3-edge insertion (no ab) from the 46 graph to 172: min 80.
- Random 4-vertex insertions (2 A + 2 B new vertices, 16 internal patterns, 400k samples each) at 172: min 82.
- Local repair at 170 never descends below 46: 2-switch SA (any temperature), tabu (R=3 focus: 100k steps; full
  neighbourhood: 1000+ steps), LNS remove-pair/reinsert-pair (full pass 510 moves: no improving move from 46 or 48),
  ILS (kick 3 switches + tabu 45 s, 5 rounds: always back to 46).
- Tabu from several different 170 starts (48, 54, 48) all descend to 46, and the four 46 graphs have the same
  distance-profile signature (one attractor). At 172, starts 84 -> 82, 82 -> 82, 80 -> 80 (no gain).
- Calibration: from conder168 + 6 random 2-switches (far 465), tabu returns to conder168 exactly in 6 steps. From
  + 20 random 2-switches (far ~1000) 60 s of tabu reaches only 123 (TT 40), 137 (TT 10), 163 (TT 3).
  So the repair only undoes small damage; a far-0 target has to be within a few switches to be found.
- Conclusion for c1: the surgery family around conder168 has a floor at 46 (n=170); no far-0 graph at n >= 170 found.
  Beyond 170 the chain grows about 20-40 per inserted pair and tabu recovers only part of it.

Most promising next step (not done): a repair that can move far from a start (e.g. LNS with bigger removed sets
or SAT on the radius-6 neighbourhood of the inserted pair), or other 168 far-0 graphs as bases (tabu only ever
returns to conder168 from perturbations of it).
- 17:23Z: long tabu (280 CPU-s, 1494 steps, TT 40) from the n=172 far-80 graph: no improvement (best 80). Stop here.
Final: c1 best n=170 far 46; logged n=172 80, n=174 107, n=176 122. No far-0 graph, nothing for records/.
