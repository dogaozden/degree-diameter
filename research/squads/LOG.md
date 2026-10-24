# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 ~18:20 UTC, session thm-d8table (claude/d8-numerology-ocg3xq), round r1-d8

Goal: a structured lift of the hexagon H(q) plus two extra point-line matchings with many copies and diameter 8
(explain/beat the Delorme–Gómez–Quisquater D = 8 cells). Test bed q = 5: random lifts reach M ~ 12, DGQ's formula
gives 25, M >= 27 would beat (8,8). Scorer: research/theorems/d8/liftdiam (exact BFS over all sources).
Cards (research/squads/r1-d8/cards.md):
- c1 hyperplane-pencil labels on hops: best M=10 with 16 unreached; worse than random labels. Found a real bug in
  liftdiam (disconnected lifts reported as 0 unreached); fixed in the shared file, all zeros rechecked.
- c2 square-class/quadratic holonomy on flags: M=10 ok, M=15 178 unreached (random 192); lowers geodesic variety.
- c3 annealing of Z_k labels (Z_5 polygon part fixed): no M above random.
- c4 torus-invariant labels: no M above random.
- c5 colour-class voltages in a cyclic group: best 2 unreached at M=14 (best of the round; random ~12).
- c6 j=1 designs: only the M=4 baseline verified; M=5 annealing left 1566 unreached.
- c7 apartment-projection labels: worse than random (potential-type labels collapse one-hop walks).
- c8 non-abelian/permutation voltages (own checker gperm, agrees with liftdiam): no gain over abelian.
Kept: c5's colour voltages (closest), c7's lesson (labels must be locally injective), c1's bug fix.
Next: nothing in the round approached 25 at q=5; I wrote up the analysis (research/theorems/D8_NUMEROLOGY.md) and
continued with annealing on the exact diameter for j=1 at q=3,4 myself. Honest verdict: the squad added breadth and
a bug fix, no construction.
