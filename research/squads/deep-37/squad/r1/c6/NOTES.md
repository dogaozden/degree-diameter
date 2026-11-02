# c6 lns-exact (squad deep-37 round 1)

Result: far 43 at n = 170 (from the far-60 start). Independent check: bin/score37 on best_far43.edges gives
n=170 edges=255 maxdeg=3 simple=yes bipartite=yes connected=yes far=43. Far-46 start: no improvement (46).
Best 43 graph is one isomorphism class (3 separate chains reached it, see below); the chain that stopped at 44 is another class (best_far44.edges).

## Code
- lns.c (copy in this folder; working copy in work/): region = random far pair (u,v), candidate edges with an endpoint
  within RADIUS of u or v, remove a random set S of 8..12 edges (or unions of G-orbits of edges for a nontrivial group G,
  so S and the completion stay G-invariant). EXACT enumeration of all completions (DFS, canonical branching on the first
  deficient vertex, orbit of each chosen pair added at once). Each completion scored by bit-parallel far count (as insert.c).
  Pruning: R + T + all admissible pairs among deficient vertices is a supergraph of every completion, so its far count
  is a lower bound; subtrees with bound > threshold are cut (exact for completions with far <= threshold).
  Move: uniform random completion with far <= max(cur, best + DELTA) (DELTA=0 is a plateau walk).
- grp_id170.txt: trivial group. grp60_F20.txt: F20 (order 20, from dreadnaut via gutil.aut_gens).
- The far-46 graph has an automorphism group of order 2 (not used; trivial group used).

## What was run (exhausted = whole completion set enumerated or pruned exactly, not time-capped)
Far-46 start (c1_s170_k2_far46), trivial group:
- unpruned k=8: 310 regions exhausted, min far 46 in every region, no move to a different far value.
- unpruned k=9: 1 region; k=10: 4 regions (about 0.9M completions each), min 46.
- pruned k=10,11,12: 153 regions exhausted; only the identity completion has far <= 46 in each.
- pruned band walk (DELTA 8, k=10..13): 69 moves; cur drifted to 54, best stayed 46.
- pruned k=16..24: 9 regions tried with a 3 s cap each; none finished (bound too weak at that size).
Far-60 start (r3a_best_n170_D5_7_7_far60), F20 orbit unions (symmetric completions):
- unpruned, orbit-union sizes 5..20: 1439 + 2893 + 2229 + 84514 regions exhausted; all min far 60.
- unpruned, sizes 30..64: 734 regions exhausted (avg leaves 171 to 5175); all min far 60.
- pruned band walk (DELTA 4, sizes 35..60): 1363 regions exhausted; all min 60; cur stayed 60.
  => the F20-invariant neighbourhoods of the far-60 graph contain no completion with far < 60 (F20 settled family).
Far-60 start, trivial group (non-symmetric), pruned, k=8..12, radius 2:
- seed 14: 785 regions exhausted -> far 44 (best_far44.edges).
- seed 21: 296 -> 57, chained: 441 -> 50, 677 -> 43 (best_far43.edges), 866 more regions at 43: no move.
- seed 31: 444 -> 43; chained 782 regions: no move. seed 41: 528 -> 43.
- from 43 (all chains): about 1750 regions, no move; includes radius 3 k=9..12, 702 regions; band DELTA 3, 165 iterations: no move;
  k=13..15 pruned: 24 regions, k=13 4 exhausted, k=14 8 of 10 exhausted, k=15 2 of 10 exhausted: no move.
- from 44: k=8..12, 1017 regions exhausted: no move; radius 3 band DELTA 4, 340 regions: no move; band DELTA 8: cur 49, no gain.
Isomorphism (src/iso.py): the far-43 graphs from seeds 21, 31 and 41 are one class; the far-44 graph is another.

## Validation
- Unpruned completion counts matched an independent Python brute force on 300 regions (k=4) and 40 regions (k=6),
  trivial group; orbit-based brute force matched on 6 symmetric regions (sizes 20 to 40).
- Pruned search min far matched a brute force (Python far count over all completions) on 25 regions (k=5,6) of the far-46 graph.
  The same check on far-60 regions was started and killed (too slow); the far-43 and far-44 results are verified only by bin/score37.

## Caveats
- Records none: far 43 is not a (3,7) candidate. Not a far-0 graph at n >= 169.
- Plateau and band walks rarely moved; the 43 and 44 graphs are strict local minima for all completions of up to 13 removed edges (radius 2 or 3).
