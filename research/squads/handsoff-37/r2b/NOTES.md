# r2b NOTES (card r2b: exact region re-solve, LNS with exact inner solver)

Start: 2026-10-31T17:25:21Z (date -u). Stop about 19:25Z at the earliest, stop at about 19:40Z.

Plan:
1. Inner solver: remove the internal edges R of a region S (ball of radius r around a centre), leaving K = |R|
   A-stubs and K B-stubs. Every re-matching of A-stubs to B-stubs (simple, bipartite, cubic) is a valid rewiring;
   enumerate all K! (DFS with pruning) and score the full graph (far = same count as bin/score37).
   This contains every 2-switch among the region edges, so it is a strict superset of the tabu neighbourhood of c1.
2. Scan: for every centre of the 170 far-46 graph, the best re-matching at radius 2 (K = 9 for a tree ball).
3. If no improvement: larger regions (radius 2 plus boundary edges, K = 10..12, random sampling), and an LNS walk
   that accepts equal-far moves (plateau) to leave the 46 basin.

## 17:33Z results

Code: reg.c (exhaustive DFS over all re-matchings of a region's internal edges, scored by full far), satreg.py
(exact SAT re-solve: x_ab variables for the region's new edges, exact degree cardinality, walk-DP encoding
W_k(u,z) for same-side pairs, cardinality bound on same-side violations; pysat cd19), lns_sat.py (LNS driver).
Start graph: start46.edges (= c1/s170_k2_far46.edges, far 46). All 46 far pairs are same-side at distance 8.

1. Exhaustive radius-2 scan (reg scan start46.edges 2): for ALL 170 centres the ball has K = 9 internal edges
   and 116640 valid re-matchings; best far over all of them = 46 (no improvement; identity included).
   Full output: out/scan2.txt.
2. SAT calibration on the radius-2 ball at centre 0: T = 45 -> UNSAT (0.1 s), T = 46 -> SAT with far 46 (score37
   agrees). So the encoding is consistent with the exhaustive enumeration.
3. Radius 3 and 4 balls at centre 0, T = 45: running (see below).
- 18:06Z: radius 3 at centre 0, T = 45: NO ANSWER in 500 s (|S| = 22, K = 21, 105 x-vars, 1070 violation
  literals, 278k clauses; encoding 0.4 s). Radius 4 (|S| = 45, K = 45, 450 x-vars, 2169 violation literals,
  1.6M clauses): NO ANSWER in 500 s. The cardinality bound "<= 45 violations" is the hard part: the solver
  does not prove UNSAT, so exact SAT region solves beyond radius 2 are too slow in this form.
  Next: plateau walk (reg walk, equal-far moves accepted) in the foreground, and SAT with a per-call time limit.
