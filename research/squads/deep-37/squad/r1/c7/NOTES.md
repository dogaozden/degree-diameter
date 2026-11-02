# c7 (wildcard): odd-n route, n = 169 (single vertex added or deleted)

Idea: at n = 169 (sides 85 + 84) a cubic bipartite graph is impossible, so the sides need three degree-2 vertices.
Two concrete ways to get there from known graphs, none of which the other cards run:
- insertion: add ONE vertex x to a side and rewire 3 edges (x adjacent to three distinct vertices of the other side,
  each losing one neighbour). This is exhaustive over all such choices; orbit representatives come from
  Aut(base) (colour-preserving orbits, src/reps.py), so the search is complete up to automorphism.
- deletion: remove one vertex from an n = 170 graph (all 170 choices).

Code (all in this folder):
- src/c7odd.c (build: gcc -O3 -march=native -o c7odd src/c7odd.c): modes ins and del. Env SIDE, REPS.
- src/reps.py BASE OUT: colour-preserving orbit representatives (uses src/gutil.py via dreadnaut).
- src/c7sa.c: SA over 2-switches (M1) and deficiency moves (M2: a degree-2 vertex takes a neighbour from a degree-3
  vertex). Objective far (env EXC=1 switches to the smoother excess sum of max(0, dist-7)).
- src/c7tabu.c: sampled tabu over the same moves (tried, poor: the sampled best neighbour is always far worse).
- src/complete170.py: adds a degree-3 vertex on the other side joined to the three degree-2 vertices (169 -> 170).

Numbers (far = unordered pairs at distance > 7, checked with bin/score37):
- insertion into C168.1 (x on side A, exhaustive up to Aut, 91,881 objects): floor far 126. Histogram starts at 126.
- insertion into the girth-8 168 graph: 137 (x on side A), 141 (x on side B), both exhaustive up to Aut.
- deletion of one vertex from inputs/c1_s170_k2_far46.edges: best 131 (of 170 choices).
- SA (7 seeds/schedules, 1M to 2M steps each) from the 126 graph: best 123 (out/sa_t_3.edges, saved in best/).
  Hot schedules (T 15 -> 1.5) never got below the start; the excess objective (EXC=1) never improved either.
- completing the 123 graph to n = 170 by a degree-3 vertex: far 78 (worse than the 46 of the pair insertion).

Conclusion: at 169 the single-vertex route floors at 126 (exhaustive) and the local search only reaches 123, so this
is about 3x the far count of the 170 routes (46). The 169 case looks structurally harder than 170; the best 170 route
stays the pair insertion (floor 46, already known).

Files: best/n169_far123_c1ins_sa.edges (far 123, n = 169), best/n169_far126_c1ins_exhaustive.edges (far 126).

Later checks:
- Exhaustive one-move scan of the far-123 graph (src/c7scan.c): all 30,855 2-switch and deficiency moves; best
  one-move far is 125, so 123 is a 1-move local minimum (no improving move at all).
- SA seeds 31 and 32 from the 126 graph (T 4 -> 0.5, 2M steps): both stay at 126.
- SA from the 131 deletion graph (seed 33, T 4 -> 0.5, 2M steps): stays at 131.
- Scoreboard lines for these are in squad/r1/scoreboard.jsonl (card c7).
