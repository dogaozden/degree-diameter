# c157b-r1 cards (read COMMON.md first)

c1 (P, local search engineering): beat 8,645 points with a better plain local search on all 177,156 points. Start from
   research/d15D7b/pack.c; improve it: stronger perturbations (force-insert 3-6 points at once in a small region, i.e.
   points within distance 4 of each other), plateau (1,1)-swaps with tabu, ARW acceptance rules, restarts from RH.txt with
   a random 5-10% removed. Run from RH.txt (and compare to random starts).
c2 (P, orbit search under SUBGROUPS of the order-133 group): RH is invariant under g (order 133), hence under g^7
   (order 19) and g^19 (order 7). Orbits of g^19 have 7 points, of g^7 have 19. Build the orbit graph (orbits that are
   internally non-collinear; two orbits conflict if some points are collinear), start from RH (as a union of small
   orbits) and run an orbit-level local search / ILS (weights = orbit size). More freedom than 133-orbits, much smaller
   than the full space. Goal > 8,645.
c3 (L, same as c2 for LINES): orbit graph of lines under g^19 (order 7) and g^7 (order 19), start from RL.txt,
   orbit-level ILS. Goal > 8,246 lines.
c4 (P, OTHER groups): orbit searches for points under different collineation groups: e.g. the Singer normaliser (g
   together with an order-3 element of SL(3,11) normalising <g>, order 399), elements of SL(3,11) of orders 120, 110,
   100, 60, 40, 24, 12 (orbits of mixed sizes are fine: weighted independent set on the orbit graph, orbits must be
   internally non-collinear), and the swap (v, a, w) -> (w, -a, v) combined with others. Use shared/gperm.py to get
   permutations. For small orbit graphs (< 1,000 orbits) try an exact or near-exact weighted MIS. Goal > 8,645.
c5 (L, OTHER groups): the same as c4 for LINES. Goal > 8,246.
c6 (P, k-fixed tabu / penalty search): fix the target size K (start K = 8,646) and minimise the number of conflicting
   lines (lines with >= 2 chosen points) by moving one chosen point at a time (tabu tenure, aspiration); when 0 conflicts,
   save and raise K. Initialise from RH.txt plus K - 8,645 random points. Write it in C. Goal > 8,645.
c7 (m, mirrored sets): the mirrored set R' (768 points, shared/Rp.txt) with sigma (shared/sigma.txt) satisfies (N1)
   R' non-collinear, (N2) sigma(R') non-concurrent, (L) sigma(Gamma_2(x)) = Gamma_2(sigma(x)) for x in R'. Scorer:
   `python3 shared/chkmirror.py RP.txt SIGMA.txt`. Read research/theorems/MIRRORED_SURGERY.md and
   research/cell147/mirror/README.md (tools there: mirror_sa5.py, mirror_build2.py, ext1.py). The structure: the
   distance-4 graph of R' (with midpoints) must be mirrored by sigma(R') (with connecting lines). 768 = 756 pairwise
   opposite points + 12 extras looked like a plateau. Try a different idea: e.g. drop 10-30 base points to admit more
   extras, or a different base, or build R' greedily from scratch allowing midpoint stars of size 2-3. Each extra point
   is worth +4. Goal > 768.
c8 (wildcard, P or L): an approach none of c1-c7 uses: e.g. algebraic sets from the geometry (H(11) points are all
   points of the quadric Q(6,11); hexagon lines are some of its lines; the SL(3,11)-orbit types: a = 0 & w = 0 (133
   points), a = 0 & v = 0 (133), a = 0 & v.w = 0 (flags), a != 0); unions of whole SL(3,11)-substructures, hyperplane
   sections, exact solving of a quotient by integer programming (if a solver is installed: check `python3 -c "import
   pulp"` / `glpsol` / `scip`; pip may not have network), or combining two good sets (bimerge idea: research/squads/
   cells/d16D7/bimerge.py). Goal > 8,645 points or > 8,246 lines.
