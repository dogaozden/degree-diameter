# c2 (grow) round 1 notes

Result: no far below 46 at n = 170. Best file: squad/r1/c2/best_far46_design_d06.edges (far 46, verified with bin/score37).
It is in the same isomorphism class as inputs/c1_s170_k2_far46.edges (nauty, src/iso.py).

## Search engine (ls.c)
- Moves: 2-switches on a cubic bipartite graph. Cost: far (pairs at distance > 7), exact, 7-step bitset balls.
- Mode 0 (weighted tabu walk) and mode 1 (breakout only): drift to far 250 to 500, dropped.
- Mode 2 (simulated annealing on far, focused proposals: add p-q with p within 3 of one end of a far pair and q within 3
  of the other end; 70 percent focused): works. About 70k proposals per second.
- Calibration from C168.1 plus one random pair: 7 s runs, seeds 11 to 20: far 46 in 3 runs, 48 in 4, 58 in 3.
  Longer runs (27 s, three seeds) and slow cooling (42 s) stop at 46 or 48. Uniform proposals: 48. Fully focused: 58.
- All seven far-46 results from annealing are one isomorphism class (the same class as the Opus file).

## Seeds
- C168.1: 2-edge insertions: exhaustive floor 46 (252 of about 31k pairs reach it); the 20 best (insert20.c) all 46;
  repaired, all 46. 3-edge insertions: the 20 best are all 48; repaired, all 48.
- Girth-8 168 seed (records/n168_new_girth8_aut168.edges): random insertion repaired to 92 to 109 in 6 s runs; designs before repair 120,
  repaired to 92. Not competitive.
- c1 census so far (squad/r1/c1/classes.tsv): two 168 classes (girth 8 Aut 168, girth 12 Aut 504). No new seed.

## Designed insertion (design.c)
- Edge loads on C168.1: every edge has load 36 (unique-geodesic same-side distance-6 pairs), so there are no low-load edges to exploit.
- C168.1 has no 8-cycles and 659 12-cycles. The girth-8 seed has 42 8-cycles.
- Designs with 4 removed edges (x joins 3 b's, y joins 3 a's, the leftover ends joined): 127512 designs from the 24 lowest-load edges,
  best 58 before repair. Random 12-cycle alternating 6-sets with x, y and a matching of leftovers: 48953 designs, best 58.
- Top 14 designs repaired by annealing: one to 46 (same class), twelve to 48, one to 61.

## Pair relocation (relocate.c)
- Delete the pair x-y of an edge of the far-46 graph, reconnect the four freed ends (2 ways, new edges only), then score every
  2-edge insertion into the resulting 168 graph. 510 combinations: best 46 for all (the result is the same class).

## Not done
- Two-pair relocation (about 260k combinations of 0.35 s each) and 3-edge reinsertion after relocation.

Note: designs_buggy_ignore/ comes from the first design.c run, before the vertex-count fix (n stayed 168, so far values near 570 are wrong). Ignore it; designs_v2/ and designs_g8/ are the valid runs.
