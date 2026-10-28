# c14: hub surgery on the doubled-matching lift, q = 4

## Base lift (valid, 0 hubs)
- W(4) via research/d10D7/gqgen.c (gq/gq_q4.bin, 85 points, 85 lines).
- dmfast, seed 11, ITERS=3000000 SECS=400 TEMP0=0.5 TEMP1=0.05 SWAPP=0.002, BASE=gq/gq_q4.bin NPOLY=4 (cost 0 at ~2.9M iters).
  Other seeds 12, 13, 14 also reach cost 0; seeds 1-4 with SWAPP=0 stall at 18-26.
- Solution: dm_q4.sol (lift2 format). Edge list: dm_q4.edges.gz (n = 1020, 3570 edges, 7-regular, bipartite).
- apsp (research/theorems/d5gq/apsp dm_q4.edges 7 5): RESULT VALID d=7 D=5 n=1020. D=4 fails (149,364 pairs).

## Hub surgery (no valid hub found)
Degree budget: a vertex has degree 7 = q+3. Free slots only come from deleting matching edges (each deletion frees one
point-slot and one line-slot). A line-hub (adjacent to points only) needs its neighbours to cover all 510 lift lines
within distance 3; a point-hub symmetric. Coverage alone is easy (a point copy reaches about 217 lines within distance
3, and 6 neighbours suffice in the base graph), so the bottleneck is the deletion damage.

- Deleting one matching edge (x,y) makes exactly the pairs at x and y (about 12 + 12) go to distance 6; every bad pair
  touches x or y (checked for edge 919). A hub on x repairs the pair (x,P) only if some other hub neighbour lies within
  distance 2 of P.
- Star surgery (delete all 12 matching edges at a base point, hubs on the six copies of p and of sigma(p)):
  all points 85 hubs with 2 each -> 133k-153k bad pairs; too much damage.
- Random 1 line-hub on 7 deletions: best of 40 trials 155 bad pairs.
- Annealing over 7 deleted matching edges (cost = pairs at distance > 5):
  - 1 line-hub + 1 point-hub on the same 7 deletions: best 73 (seed 4), 95 (seed 1, 1.5k steps).
  - 6 deletions, 1 line + 1 point: best 99.
  - 7 deletions, 1 line-hub only (point-ends used, line-ends left at degree 6): best 109.
  None reaches 0, so no hub was attached to a valid graph.

Result: 0 hubs fit (score 0 over 12(q+1)(q^2+1) = 1020, q = 4). The DM lift itself is valid at 1020.

Files: gen.py (star surgery), surg.py (matching-edge list, build/bad), dcount.c (pairs at distance > D),
anneal_hub.py K NL NP STEPS SEED (hub annealer), inspect1.py, cover.py, del1.py, try1.py.
Next: a SAT or exhaustive check of the 7-neighbour condition B(x) subset of the distance-2 balls of the other neighbours,
or q = 5 (degree 8 gives one more slot per hub, Z6 lift of W(5) = 1872 base cell).
