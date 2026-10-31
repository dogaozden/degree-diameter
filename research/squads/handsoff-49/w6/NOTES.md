# w6 notes (surgery on the valid 4,970 graph and on near misses)

Started: 2026-10-31 21:41 UTC. Deadline: about 23:41 UTC. Updated: 21:55 UTC.

## Facts measured
- Valid 4,970 graph (seeds/valid4970.edges) is a Haar graph H(G,S), G = meta 71 35 49 (order 2,485). Right multiplication
  by G is an automorphism group with 4 edge orbits, so only 4 edge types exist up to symmetry.
- Deleting ONE edge of the valid graph creates 179 far pairs (edgecrit, all 4 orbit representatives give 179).
  So every 2-switch on it costs about +350 far pairs before any gain.
- near4992 (seeds/near4992_meta104_24_7.edges): 4,992 far pairs, all at distance exactly 10 (no unreachable pairs).
  Deleting one edge there adds 270 far pairs. Far-pair degrees: 2,496 vertices have 3 far partners, 2,496 have 1.
- Surgery (delete 4 disjoint edges, a in A joined to their B ends, b in B joined to their A ends, n = 4,972):
  a random choice gives 441 far pairs (diameter 10). Annealing over the CHOICE of the 4 deleted edges (surgsa.c)
  gets to 181 far pairs in 90 s. 181 is about the cost of one edge, so the four deletions overlap heavily.
- Tools: sa.c (annealing over 2-switches and targeted shortcut moves), tabu.c (best-of-K tabu), surgsa.c (annealing over
  the removed-edge choice), surg.py (one random surgery), far pairs via tools/farlist.

## Tried
1. sa.c on the 441 surgery graph, T 3 -> 0.1: 44k proposals, 1 accepted. Every 2-switch is strongly uphill.
2. tabu.c (best of 150 targeted switches per step, tenure 40): steps always go uphill (441 -> 3,021 in 60 s). Dead end.
3. surgsa.c (choice of the 4 removed edges, 2-switches not used): 181 far pairs after 90 s, 160 after 210 s (240 s run).
   The best state's far pairs are all at distance exactly 10 (same side), 268 vertices involved, 12 of them involve a or b.
4. Queued: Haar graphs of the other groups of order 2485 (Z_71 x|5 Z_5 x Z_7, Z_71 x|7 Z_7 x Z_5, Z_2485) as extra valid
   bases (run_haar_groups.sh, outputs in groups/summary.txt). Each cost-0 base would be a new surgery start.

## Best
- n = 4,972, far pairs = 160 (not valid), file w6/tmp/surgsa4.edges (edges of the rebuilt surgery graph; verified by score48 later).

## Next
- Longer surgsa runs with several seeds, mode 3 (3 removed edges + edge ab), and a 2-switch polish at T near 0.
- Look at the far pairs of the best state: if they all involve the new vertices, try different attachments
  (a joined to only some of the freed B ends, the rest rewired).
