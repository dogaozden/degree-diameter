# w3 notes: lifts of W(3) (GQ(3,3) incidence graph, 80 vertices) over groups of order 63..80

Start: 2026-10-31 21:42 UTC. Planned end: about 23:42 UTC.

## Plan
- base: points of PG(3,3) (40) and totally isotropic lines (40) for the form x0y1-x1y0+x2y3-x3y2; 160 edges.
- lift over G: voltage on each base edge, tree edges fixed to identity, 81 free voltages.
- cost = number of (root u in base, target w, element x) not reached by a walk of length <= 9 with voltage x.
- cyclic G: bitset of group elements, left multiplication = rotation (fast). Other G: generic table.
- Expected walk mass: same-side pairs get about 3.9 walks per element at n = 5040 (the bottleneck).

## Status
(in progress)
