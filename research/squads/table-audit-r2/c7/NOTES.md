# c7 (wildcard) notes

## What was built
`sa_bip.c` (compiled to `sa_bip`): simulated annealing over cubic bipartite graphs on n vertices.
- Bipartition A = {0..n/2-1}, B = {n/2..n-1}. A move picks two edges (a,b), (c,d) and replaces them by (a,d), (c,b).
  This keeps every vertex at degree 3 and keeps the graph bipartite. Moves that would create a repeated edge are skipped.
- Start: the Haar graph H(Z_h, {0,a,b}) with random distinct nonzero a, b (or three repaired random matchings, init=1).
- Cost = number of unordered vertex pairs at distance > 10. Distances are computed with bitset balls:
  R_k(v) = R_{k-1}(v) OR (OR over neighbours u of R_{k-1}(u)), for k = 1..10. One evaluation is about 0.1 ms at n=600.
- Acceptance is Metropolis with a geometric temperature schedule T0 -> T1.

## Results (scorer: bin/apsp FILE 3 10)
- n=200, 400, 500: VALID. The n=500 graph is `t500.txt` (checked by the scorer: RESULT VALID, bipartite, cubic, diameter 10).
- n=600: best cost 28 pairs after 1.2M iterations (`err600.log`). Not valid.
- n=800: best cost 1625 pairs after 300k iterations (`err800.log`). Far from valid.

## What was NOT done
The compound (Delorme-Gomez-Quisquater style) idea from the brief was not implemented. The method above is plain
annealing over bipartite 2-switches, which is close to what card c1 does. The only deviation from c1 is the bitset cost
and the Haar start. No compound gadget was built, no Kautz/de Bruijn digraph was used, and no matching was tuned by hand.

## Ideas for the next round
- Start from `t500.txt` with extra vertices and anneal at n=520..600 with a reheating schedule. The cost reached 28 at 600
  in a single run, so a longer run or restarts may close the gap.
- Compound start: copies of a gadget with three ports, joined along a bipartite cubic base H, then annealed. This is the
  part that is still untested.
