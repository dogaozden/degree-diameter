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

## Final results (23:55 UTC)

Best near miss: n = 4,972, far pairs = 160 (diameter 10, not valid). File: w6/tmp/surgsa4_best160.edges. Rebuild:
`surgsa2 seeds/valid4970.edges OUT 240 11 4 6 0.5` (mode 4: 4 removed edges, a and b added). Scoreboard line appended
(valid_claim "no"). Mode 3 (3 removed edges + edge ab) also floors at 160 (seed 21, stopped at 160).

Edge criticality (edgecrit, far pairs created by deleting one edge; the 4 edges of vertex 0 are the 4 orbit representatives):
- valid4970 (meta 71 35 49, seeds/valid4970.edges): 179 for all 4 orbits.
- near4992 (meta 104 24 7): 270 for all 4 orbits.
- other cost-0 solutions of meta 71 35 49 (bases/mv_11..14.sol, verified RESULT VALID n=4970 by score48):
  mv_11: 174, mv_12: 168, mv_13: 176, mv_14: 176. mv_12 has the most slack, but it is still close to 170.
  Those four are not checked for automorphism equivalence to the seed (solutions were found with different seeds).
  Surgery was NOT run on them (the coordinator asked for no new searches).

Other groups of order 2,485 (groups/): meta 71 5 5 x Z_7 best cost 14, meta 71 7 20 x Z_5 best cost 8, cyclic Z_2485
best cost 4,352 (40 s, 2 seeds each). No cost-0 base there.

Order-2,484 bases (n = 4,968, for the 4-vertex surgery to 4,972; bases/summary.txt, 45 s, 1 seed each, none cost 0):
meta 207 12 22 best 90 (closest); meta 23 108 22: 1,496; meta 69 36 22: 1,508; meta 27 92 26: 1,516; meta 46 54 45:
1,752; meta 36 69 13: 3,162; meta 69 36 47 and 138 18 47: 3,226. So the 4-vertex route (surgsaK.c, process_base.sh MODE 8)
was never run: no valid order-2,484 base was found.

Did not work:
- 2-switch annealing (sa.c) and best-of-K tabu (tabu.c) from surgery graphs: every move is uphill by hundreds
  (441 -> 3,000+ in 60 s). A 2-switch removes two edges that each carry about 170 to 180 critical pairs.
- Annealing over random 2-switches on the valid graph itself: the same problem.

Conclusion: local surgery on these Haar graphs is blocked by edge criticality (about 170 far pairs per deleted
edge). The best surgery floor is 160 far pairs at n = 4,972. A new record needs a new global structure, not local
repair. Next idea (not run): search valid bases of order 2,484 or lower with more seeds and longer runs, then run
surgsaK on the one with the lowest criticality.
