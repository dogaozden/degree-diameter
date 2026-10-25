# Referee checks for D7_HEXAGON.md (job referee-d7, 2026-10-25)

Written from scratch for the referee report research/referee/d7-2026-10-25.md; no code shared with
research/theorems/d7hex_tests/ or d7hex_lemma41/ (branch claude/d7-hexagon-theorems-4w1prt). Output of every run is in
checks.log. Run everything from one scratch directory (the scripts read and write H{q}.pkl, D{q}.npy, sets{q}.pkl there).

- hex.py q (prime q): builds H(q) from the quadric and Tits' equations of D7_HEXAGON.md §1.1, checks point/line counts,
  q+1 per line and point, the distance profile from every vertex (girth 12, diameter 6) and (F4) on all pairs; saves the
  hexagon and its distance matrix. q = 2, 3 in seconds, q = 5 in a few minutes.
- tests.py 3: SL(3,q) action (and that GL fails), Hermitian spread (Lemma 1.2(b)), elliptic quadric section (Lemma
  1.2(a)), random maximal segment sets (Prop. 1.4), Lemma 4.1 on all ordered pairs with negative controls.
- thmB.py 3 SEED SIZE: Theorem B with M built as in Proposition 5.2 from a non-collinear R with distance-4 pairs and a line
  set R* with the same distance-4 pattern; negative control breaking (H3) at one point.
- levels.py: Theorem A (random bijections, types HHH, HDH, HDHDH, q = 3) and Theorem C / Remark 4.2 in a two-level graph,
  by BFS from every vertex.
- nums.py: all numbers of §0, §6, §7, §9 (table values, kappa, Corollary 9.x crossovers, slot vectors).
- cor91.py q r OUT [seed]: the explicit graph of Corollary 9.1 (all levels H, sigma from Prop. 5.2 on an elliptic quadric
  section and Hermitian spread lines, hub graph of Lemma 7.1), written as an edge list.
- bfs.c (gcc -O2 -o bfs bfs.c): reads "n" and edge lines; checks loops and multiple edges, bipartite, degrees, BFS from
  every vertex; prints the diameter and the number of ordered pairs at distance > 7.

The record graphs (7,7) and (9,7) were rebuilt with the lab's research/d13D7/hexgen2.c and
research/d13D7/tools/multi_sol.py (multi.c) from the solution files on master and checked with bfs.c.
