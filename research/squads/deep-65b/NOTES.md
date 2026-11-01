# deep-65b working notes (Opus, Nov 1-2 2026)

Target: bipartite, maximum degree 6, diameter 5, more than 684 vertices. Start 22:39 UTC (usage/deep-65b.start).
Read first: handsoff-65 REPORT (branch claude/bipartite-d6-d5-search-80gtg5) and deep-65 REPORT + NOTES (branch
claude/deep-65-bipartite-d6-d5-8dgdq1). Their tools are copied to prior/ (not committed; they live on those branches).

## Where things stood

- Haar graphs: closed on 686-900 vertices (six-five-384 + s65). So any record above 684 up to 900 is not a Haar graph.
- deep-65 closed the hub family 1,6|1,6 exactly (all groups of order 294, 300, 306, 312) and k = 3, 4 on a few groups.
- 2+2 base lifts (n = 4m): only annealed/tabu-searched (handsoff c1, orders 171-180; best cost 4 at 704 on C11:Q16).
  c1's own calibration: tabu did not re-find the 684 record, which IS a 2+2 lift (Haar graph of C6 x (C19:C3) = lift of
  [[3,3],[3,3]] by its index-2 subgroup C3 x (C19:C3) of order 171). So "floor 4" there says little.
- At (5,5) the record 384 (and 360 before it) came from EXACT searches of 2+2 lifts (beyond-haar-d5 b4a1x/b4a2x, base
  [[1,4],[4,1]] at order 96). The best Haar graphs at (5,5) stop at 352, so the 2+2 family beat Haar by 9% there.
  The same ratio at (6,5) would give about 745. This is the lead I chose first.

## Walk counts (scratch: walks.py)

Non-backtracking walks of length 0, 2, 4 from a base vertex, by target (the per-sheet bound on |G|):
[[1,5],[5,1]] self 411, other 370; [[2,4],[4,2]] 381 / 400; [[3,3],[3,3]] 403 / 378; K6,6 151 / 126 x5;
K7,7 - I 121 / 110 x6. Every family has the same Moore bound (781 per vertex); the record is at 43.8% of it.
At (5,5) the 384 lift sits at 58% of its binding count (165 for [[1,4],[4,1]]).

## The [[1,5],[5,1]] family in closed form (tools/split15.c)

Normalise both single edges (A0-B0, A1-B1) to voltage 1. Then the lift is
  A0_h ~ B0_h,  A1_h ~ B1_h,  A0_h ~ B1_{h e} (e in E1),  B0_h ~ A1_{h e} (e in E2),
i.e. the degree-10 Haar graph H(G, E1 u E2) with every vertex split into an edge. The voltage of the A1-B1 edge that
b4a1x solved for is only a relabelling of A1 u B1. With E = E1 u E2, diameter <= 5 iff
  C1 (A0)  E E^-1 u (E1 E1^-1)^2 = G            C2 (B0)  E E^-1 u (E2 E2^-1)^2 = G
  C3 (A1)  E^-1 E u (E2^-1 E2)^2 = G            C4 (B1)  E^-1 E u (E1^-1 E1)^2 = G
  C5 (A0-A1)  E u E1E1^-1E1 u E1E1^-1E2 u E1E2^-1E2 u E2E2^-1E2 = G
  C6 (B0-B1)  E u E1E1^-1E1 u E2E1^-1E1 u E2E2^-1E1 u E2E2^-1E2 = G
Checked against BFS on the built graph (split15 rand): 300 random pairs on C11:Q16, 2000 each on A5, C30 x C2,
C25:C4, per-condition miss counts identical, 0 mismatches, 485 valid graphs among them.
Symmetries: (E1, E2) -> (t phi(E1) h, t phi(E2) h) (t, h in G, phi in Aut G), the swap (E2, E1), and (E1^-1, E2^-1).

Exact search: E1 over classes of 5-sets containing 1 (union-find over all 4-subsets of G \ {1} with the Aut generators,
the 4 re-normalising translations and inversion). For fixed E1, UA = G \ (E1E1^-1)^2 and UB = G \ (E1^-1E1)^2 must be
covered by E1E2^-1 u E2E1^-1 u E2E2^-1 and E1^-1E2 u E2^-1E1 u E2^-1E2. E2 is built by branching on the first uncovered
element (10 linear choices, 2k quadratic with a chosen element, or a new pair: m choices for two slots). Swap symmetry:
q(class) = |UA| + |UB|; E1 is always the worse set (q(E2) <= q(E1), ties by class id), checked at the leaf with a
class lookup before the four remaining conditions.
Checks: the branching search finds exactly the E2 that brute force over all C(176,5) sets finds (C1 and C4 only), for
E1 with 0, 0, 1, 131,660, 771,352 and 2,140,076 partners on C11:Q16 (runs/bf_176_17_*.txt).
On C11:Q16 there are 11,327 E1 classes (37.75M 4-subsets, union-find 23 s).
