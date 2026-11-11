# c5: path-split Haar graphs (3+3 lifts), round 1

Start 23:09:50 UTC (60-minute box). Work only in this folder; no git.

## Construction
Each vertex of a degree-14 Haar graph is split into a path of 3 vertices: side X vertex -> A0 - B0 - A2 (A0, A2 ends
with 5 external edges, B0 middle with 4), side Y vertex -> B1 - A1 - B2 (A1 middle with 4 external, B1, B2 ends with 5).
Base (quotient) multigraph, blocks A0 A1 A2 | B0 B1 B2:
  internal (voltage 1): A0-B0, A2-B0, A1-B1, A1-B2
  external: A0->B1 (a darts, set S0), A0->B2 (5-a, S1), A2->B1 (5-a, S2), A2->B2 (a, S3), A1->B0 (4, S4)
Lift by a group G of order m: (u,g) ~ (v, g*s) for s in S(u->v), n = 6m, every vertex has degree 6 (checked: score65
reports maxdeg=6, bipartite=yes, simple=yes). n > 684 needs m >= 115.

Symmetry: swapping the path ends A0 <-> A2 maps base(a) onto base(5-a), so a=3 is isomorphic to a=2 and only a=1 and
a=2 were run. Switching on the Y blocks normalises the identity into S0, so S0 keeps the identity fixed.

## Evaluator (code/pathsplit.c)
G acts on each block by left translation, so distances from (u,g) equal distances from (u,1) relabelled. Cost is
sum over the 6 block representatives of the number of vertices at distance > 5 (6 BFS of depth 5, neighbours computed
from the voltage slots, no adjacency rebuild). Unordered bad pairs = m * cost / 2.
Check against score65 (3 random states, 120_1, a=1):
  EVAL cost 340, 296, 244  -> bad 20400, 17760, 14640
  score65 bad 20400, 17760, 14640 (exact match)
Tabu search: 150 sampled candidate moves per iteration (single voltage replaced), tenure 5-12, aspiration, restart after
300 non-improving iterations. About 450-600 iterations per 8 s on the shared machine.

## Commands
- Group tables: `shared/gapw -c 'ORDER:=N; OUTDIR:="tabs";' tools/gap_tabaut.g` for N = 115..127, 129, 130 (run in this
  folder). Order 128 (2328 groups) was NOT exported: out of the time box. Order 115 and all abelian groups skipped.
- Build: `gcc -O3 -march=native -o pathsplit pathsplit.c`
- Screen (run_jobs.sh over jobs.txt, 146 jobs = 73 non-abelian groups x a in {1,2}):
  `timeout 105 nice -n 15 ./pathsplit tabs/sg_<o>_<id>.tab <a> 1 8 - 150`, results in screen.txt; summary in
  screen_summary.txt, screen_best_per_group.txt, per_order_best.txt.
- Confirmation runs: `./pathsplit tabs/sg_<o>_<id>.tab <a> <seed> <secs> long/... 150`
- walks.py: non-backtracking walk counts on the base.

## Results (best cost over 6 reps; bad pairs = m*cost/2; screening 8 s, seed 1)
Best per order (cost, group, a):
  116: 42  C29:C4 (116_1), a=2   [40 s seed 21: 34]
  117: 30  C13:C9 (117_1), a=1   [45 s seed 11: 30; 40 s seed 21: 32]
  118: 125 D118 (118_1), a=2     [40 s seed 21: 120]
  120: 32  C5 x (C3:Q8) (120_21), a=1   [45 s seed 11: 39; 40 s seed 21: 42]
  122: 142 D122 (122_1), a=2
  124: 74  C31:C4 (124_1), a=2
  125: 48  (C25:C5, 125_4), a=2
  126: 48  C2 x (C7:C9) (126_2), a=1
  129: 68  C43:C3 (129_1), a=2
  130: 89  C13 x D10 (130_1), a=2
Overall best: 117_1, a=1, cost 30, n = 702, bad = 1755 pairs. No run reached cost 0, so no graph above 684 was found by
this search (not a proof of absence: the search is a sampled tabu with short runs). Dihedral groups are the worst
(cost 120-160); metacyclic groups C_p:C_k and similar were the best.
Random states cost 240-340 at m = 120, so tabu gets roughly 8x below random but plateaus at 30-40.

## Walk counts (walks.py)
Non-backtracking base walks, same-side targets, length <= 4 (includes length 0 for the source block):
  min over sources/targets = 241 (a=1 at A0->A0; a=2 at A1->A1). Opposite side, length <= 5: min 1254.
So a block can in principle be covered for m up to 241 (n up to 1446): the counting bound does NOT exclude m = 115..130,
the family has room by counting. The searches still did not reach 0, so this is evidence only, not a proof either way.

Confirmation batch (5 runs, seed 21, 40 s each): 116_1 a=2: 34; 117_1 a=1: 32; 118_1 a=2: 120; 120_21 a=1: 42;
122_1 a=2: 157 (screen 142 stands as the 122 best). Saved edge files in long/ (best_117_1_a1.edges, bad 1755 by score65;
best_116_1_a2_s21.edges, bad 1972; best_120_21_a1_s21.edges, bad 2520; all match m*cost/2).

## Process incidents (honest record)
- One confirmation command (5 runs of 40 s, ~200 s total) exceeded the 110 s command limit; the tool moved it to the
  background. It ran alone and finished with exit 0. No second copy was started.
- One command included `sleep 0` while waiting for that job (no delay). Not used otherwise.
- Score65 check file names: long/best_117_1_a1.edges (seed 11, 45 s) and long/best_116_1_a2_s21.edges were scored.
