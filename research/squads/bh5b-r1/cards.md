# Round bh5b-r1 (job beyond-haar-d5b, Oct 30 2026, ~04:25 UTC)

Goals (bipartite degree-diameter, D = 5): beat (7,5) 1,200, (6,5) 684, (8,5) 2,048. Any valid graph above these counts
(Haar or not).

- c1 (7,5): longer annealing of orbit-type coset graphs at 1210 (SmallGroup(1210, 12/13/15), |H| = 2), the
  (C11 x C11):C5 near miss (cost 2), with many seeds and temperature settings.
- c2 (7,5): coset graphs with |H| = 3 for SmallGroups of order 1848..1980 (1232..1320 vertices), orders with <= 60 groups.
- c3 (7,5): coset graphs with |H| = 4 (or 6) of constructed groups of order 2404..2640 or 3606..3960 (outside the
  SmallGroups library): direct/semidirect products with SL(2,5), A5, S5, PSL(2,7), SL(2,7), AGL(1,q).
- c4 (7,5): non-Haar lifts (vl annealer) of 7-regular 2+2 and 3+3 bases over groups of order 301..330 / 201..220.
- c5 (6,5): coset graphs with |H| = 2 for SmallGroups of order 686..720 (Delta = 6).
- c6 (6,5): lifts (vl annealer) of 6-regular 2+2 / 3+3 bases over groups of order 172..190 / 115..125.
- c7 (8,5): coset graphs with |H| = 2 of constructed groups of order 2050..2200 (SL(2,13), PGL(2,13), PSL(2,13) x C2,
  AGL(1,q) products) and |H| = 3 / 4 variants.
- c8 wildcard: an approach none of c1..c7 uses, for any of the three goals.
