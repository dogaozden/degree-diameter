### Δ = 3, 4 at D = 9..14 (job raise-small-d, 2026-11-01/02)

Job raise-small-d (Opus director + Haiku squads, cloud session, branch claude/raise-d-delta-3-4-5wyh9b). Goal: raise
the lab's values at Δ = 3, 4 and D = 9..14. Files: research/frontier/raise_small/ (tools/, sols/, checks/, runs/;
README.md); squad cards and scoreboards research/squads/raise-small/r1..r__; log research/squads/LOG.md.

**Results.** (3,12) 2,368 -> **2,436**, (3,13) 3,400 -> **4,324** (+27 %), (3,14) 5,706 -> **7,008** (+23 %; the
Foster census graph CSS(6272,7) has 6,272), (4,14) 497,042 -> **498,798**. Unchanged: (3,9) 506 (2013 table), (3,10)
810, (3,11) 1,474, (4,9) 4,970 (2013 table), (4,10) 12,416, (4,11) 30,334, (4,12) 74,066, (4,13) 192,382.
Every cubic value is a regular voltage lift, rebuilt from its solution file by tools/sol2edges.py (group product
recomputed from (m, k, r), not read from the search's table) and checked by research/lifts/coordinator_check/apsp.c
(VALID at D, INVALID at D - 1); edge lists and checks in research/frontier/beyond/graphs/. The (4,14) graph is a Haar
graph (solution in research/frontier/sols/), checked by metacheck.py from both sides and by apsp (diameter 14).

**Method: joint base+voltage annealing with small bases.** own-small's salift_s anneals a p+p cubic bipartite base
multigraph (three perfect matchings, multi-edges allowed) and its voltages in a group G together; the lift has
n = 2pN vertices, and since left multiplication by G is a semiregular automorphism group with the fibres as orbits,
a bit-parallel BFS from the 2p roots (u, e) gives the exact number of far (root, vertex) pairs. The job added group
tables for any metacyclic group Z_m x|_r Z_k (x Z_c) (tools/gtab.py; own-small used GAP's SmallGroups, which are
not installed here) and ran it at D = 12..14 for the first time. Results by base size:
- 2+2 bases (p = 2, n = 4N): best at D = 12 and D = 13: 2,436 over Z29 x|_7 Z21 (order 609) and 4,324 over the
  Frobenius group Z47 x|_2 Z23 (order 1,081), both on the first short screen of the group.
- 3+3 (n = 6N): best at D = 14 (7,008 over Z73 x|_10 Z16), level with 2+2 there (7,004 over Z103 x|_8 Z17).
- 4+4 (n = 8N): the first raise of (3,13) (3,648, 3,696, 3,744) but stops near N = 470 at D = 13 and N = 816 at D = 14.
- 5+5 and larger (up to 12+12): worse at every size tried (cost 6-60 just above the values).
At the same n the small bases have fewer free voltages but a larger, less abelian group; large r-order d (Frobenius-like
groups, m prime, d = k) matters most: groups with k = 6 or small d stay at cost 18-130, and many groups have a hard
floor (every seed and every chain ends at the same cost, e.g. 18 for Z93 x|_5 Z12 and 2 for Z55 x|_2 Z20 at D = 13,
also with targeted moves). Non-metacyclic groups (AGL(1,q), SL(2,3) x Z20, A5 x Z_c, AGammaL(1,8) x Z5, wreath and
Heisenberg groups) were not better.

**What did not work.**
- Δ = 4 with the same idea (salift4 / table-free salift4m, 2+2 and 3+3 quartic bases): cost 18 at (4,9) n = 4,992-5,040
  (but Haar random S at the same n: 150), 30 at (4,10) 12,480, 36 at (4,11) 30,360, 80 at (4,12). Haar graphs of
  metacyclic groups with random S (hmeta) stay the method at Δ = 4; near misses (4,12) Z2861 x|_1385 Z13 cost 2
  (74,386), (4,13) cost 2-4 (192,550 and 193,058).
- (3,10), (3,11), (3,12) below the 2+2 threshold: 3+3 cost 2 at (3,10) n = 816 (Z17 x|_4 Z8, an exact 2-move local
  minimum), 4+4 cost 2 at (3,11) n = 1,536 (Z48 x|_5 Z4, exact local minimum), 3+3 cost 12 at (3,12) 2,448.
- Fixed bases with metacyclic voltages (GQ(3,3) at (4,11): cost 1,208), cubic Cayley graphs of three involutions
  (PGL(2,q), S_7: diameter ~log2 n + 2), orbit-constrained lifts (voltages equivariant under a base rotation and a
  group automorphism of order 3: cost 60 where the free lift reaches 2), a 1-move tabu finisher and targeted voltage
  moves (a far pair is made close by solving for one voltage on a walk of length <= D): no gain over plain annealing.
