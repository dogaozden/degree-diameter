# Round 4 cards (Opus, 2026-10-24 ~23:30 UTC). Brief: README.md here. Score with tools/setcheck.

c1 H(8) PARTIAL OVOID, LOCAL SEARCH. Largest set of pairwise opposite points of H(8) (greedy: 67). Tabu / (1,2)-swap
   / simulated annealing on the "not opposite" conflict graph (precompute it, or use B(x,y) != 0 from the coordinates).
c2 H(8) PARTIAL OVOID, ALGEBRA. Same goal via structure: points of Q(6,8) on sections (Q(4,8) ovoid = elliptic quadric
   gives 65; try elliptic Q^-(5,8) sections, orbits of a Singer-type or Frobenius group, unions of compatible pieces),
   then extend greedily. Pairwise opposite = B(x,y) != 0 (README).
c3 H(8) PARTIAL SPREAD (pairwise opposite LINES; greedy 68). Local search like c1 on lines (distance 6 in the
   incidence graph); a line's 3-ball and the projection structure may help.
c4 H(9) NON-COLLINEAR SET. Largest set of points of H(9) with no two on a common line (greedy random 2,821; Hoffman
   bound 6,643 = a distance-2 ovoid). Try min-degree greedy, local search (remove 1 add 2), structure (points on a
   hyperplane section, orbits). Score with `setcheck hex_q9.bin FILE points noncollinear`.
c5 H(7) PARTIAL OVOID AND SPREAD for (9,7): maximise min(|P|, |L|) (greedy 56, 57). Any method.
c6 H(5) PARTIAL OVOID AND SPREAD for (7,7): maximise min(|P|, |L|) (greedy 39, 32). Small enough for exact or ILP-style
   search (python-mip/pulp if installed, else your own branch and bound).
c7 WILDCARD: q = 8 BEYOND OPPOSITE PAIRS. Freed points may also lie at distance 4 if the paired lines lie at distance 4
   and the midpoint w of the two points is mapped to the midline m of the two lines (M(w) = m), consistently for all
   pairs. Find a construction (e.g. "stars": points on distinct lines through w, lines through distinct points of m)
   that packs more pairs than K = 67, and test it on H(5) with apsp (build X(M) yourself or extend d7hex's b2 mode in a
   copy). Score: K with apsp VALID at q = 5 (beat 32) or a plan with numbers for q = 8.
c8 WILDCARD: anything else that raises the number of freed pairs at q = 8, e.g. pairs that use a different exact
   cover for some freed points, or literature knowledge on large partial ovoids of H(q)/Q(6,q) for q even. Must be
   scored by setcheck or apsp.
