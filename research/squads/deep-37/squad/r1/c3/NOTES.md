# c3 (n = 169, (3,7) bipartite candidate), squad deep-37 round 1

Target: 85 + 84 vertices, B cubic, three degree-2 vertices in A. far = pairs at distance > 7 (score37 convention).

What was built
- c3sa.c: simulated annealing over G-invariant bipartite graphs with prescribed degrees. Moves are 2-switches applied
  to whole G-orbits (exact degree check, simple by construction); cost = far via bit-parallel BFS to depth 7.
  Options: PT (fraction of moves aimed at far same-side pairs), COSTK (smoother cost, sum of far at radii 7..6+COSTK),
  optional start graph. Trivial group used for the best result; C3 group file made by mkc3.py (order-3 element cycling the
  degree-2 vertices 0,1,2; fixed point 84 in A).
- c3ins.c: exhaustive constructions. `ins3` inserts a new A-vertex joined to the ends of 3 removed edges (C168.1 and the
  girth-8 168 graph); `vdel` deletes one B-vertex of a 170 graph.
- lns.c: exact LNS (re-pair K removed edges, all K! ways).

Numbers (far at n = 169)
- Exhaustive ins3 into inputs/c1_base168.edges: best 126 (2.5M triples, 15 s). Into records/n168_new_girth8: 137.
- vdel from inputs/c1_s170_k2_far46.edges: 131. From the far-60 D5 graphs (r3a, r3b): 136.
- C3-symmetric SA from random: 147 (30 s), 162 (85 s, other seed). Unsymmetric SA from random: about 187 (30 s).
- SA from the ins3 start (targeted moves, low to constant T): 122 (best), verified with bin/score37: far = 122,
  maxdeg 3, simple, bipartite, connected. Saved as best_far122_n169.edges (not a candidate: far > 0, apsp not run).
- LNS (K = 7, 8, exact re-pairing near far pairs) on the 126 graph: no improvement.

Observations
- Far pairs of the 122 graph: 113 at distance 8, 11 at 9, 2 at 10; 98 vertices involved; the three degree-2
  vertices have the most far partners (22, 18, 14).
- Constant-temperature walks at T = 2 settle around far 130; T = 2.5 drifts to 300. Random 2-switches from these
  states are almost always uphill, so the SA is stuck in a deep basin. Larger exact LNS did not escape.
- Prior best for n = 169 was 144. Nothing here reaches far = 0; no n = 169 candidate found.
