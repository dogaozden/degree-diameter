# Round 5 cards (Opus, 2026-10-24 ~23:50 UTC). Brief: README.md. Score: setcheck ... points opposite (q = 8).
c1 ILS FROM THE 134 SET: start from best134.txt; iterated local search (remove r random points, greedily/tabu re-add,
   accept if not smaller), or (1,2)-swaps with a fast incremental conflict count. Goal 135+.
c2 FRESH TABU, MANY SEEDS: copy research/squads/d10D7-r4/c1/pov.c; run seeds 5.. with longer runs and varied tabu
   tenure/perturbation (seeds 1-4 gave 86, 134, 80, 84 — find what made seed 2 special), one process at a time.
c3 STRUCTURED CANDIDATES: field reduction. V(6,8) = V(3,64); a Hermitian form h on V(3,64) gives the symplectic form
   B(x,y) = Tr_{64/8}(w h(x,y)) for a suitable w. The 513 points of a Hermitian curve in PG(2,64) are pairwise
   non-orthogonal for h; each gives a line (9 points) of PG(5,8). Choose one point per line so that all pairs stay
   non-orthogonal for B (a CSP with 9 choices per variable: annealing), map to H(8) point ids (match the B form of
   the README up to a change of basis, or search for the right w), extend greedily. Also try other structured seeds.
c4 ORBITS OF OTHER SUBGROUPS: copy research/squads/d10D7-r4/c2/ (torus orbits + exact max clique gave 76, +greedy
   85). Try the order-73 Levi torus, T_3, products with the Frobenius, or stabilisers of a flag; exact clique on the
   orbit graph, then extend with tabu (c2's best was not combined with tabu: do that too).
c5 THE q = 7 STRUCTURE: research/squads/d10D7-r4/c5/points_best.txt is a set of 288 = (q-1)(q^2-1) pairwise opposite
   points of H(7) (research/d10D7/hex/hex_q7.bin). Find its structure (stabiliser, which subspaces/quadric sections
   it meets how, orbit decomposition) and build the analogue in H(8) (441 would be huge). Score on q = 8.
c6 H(9) NON-COLLINEAR (spin-off (11,7), +2 per point): start from research/d10D7/sets/P9_c4_noncollinear.txt (3,911;
   Hoffman bound 6,643) and push higher (c4's code research/squads/d10D7-r4/c4/mis.c; LNS / larger perturbations;
   structure such as a distance-2 ovoid of the subhexagon H(3) extended). Score: setcheck hex_q9.bin FILE points noncollinear.
