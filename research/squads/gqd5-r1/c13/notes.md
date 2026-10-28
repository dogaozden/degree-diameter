# c13: diameter 5, Delta 5, GQ(2,4) = Q(5,2) (squad gqd5-r1)

## Degree budget (forces the layout)
Q(5,2) incidence graph: 27 points of degree 5 (= Delta), 45 lines of degree 3 (2 spare slots each).
Any matching edge at a point would give degree 6 unless an incidence edge is deleted. So at Delta = 5 the only
layouts without deleting incidences are "points none, lines carry matchings" (task (b)). H(3,4) is the same
bipartite graph with sides swapped (45 low vertices of degree 3, 27 of degree 5): no new option. Q(5,3) has points
of degree 10 > 5, so it cannot be used at Delta = 5 without deleting half of the incidences.

Consequences:
- (a) injective point -> line maps (3 levels) cannot be used: a point would get degree 6.
- Every level is a Q(5,2) incidence graph; levels are joined only by line-line bijections, or partial matchings with
  at most 2 matching edges per line.

## Parity
Colour of a vertex in level j: [is line] + g_j (mod 2). A line-line matching between levels j, j' is bipartite iff
g_j != g_j'. So the level graph (levels as vertices, one edge per matched pair of levels) must be bipartite.
An odd cycle of levels (e.g. 5 levels in a cycle, which would give 360 > 354) is impossible.

## Count of levels reachable (cycle of L levels, every line in two matchings)
Let p be a point of level 0, Lambda(p) its 5 lines, sigma_0 : lines(0) -> lines(1), etc.
- Level 1 (adjacent): lines of level 1 at distance <= 4 from p are all 45 (5 at distance 2, 40 at distance 4), so every
  point of level 1 is at distance <= 5. No constraint.
- Level 2 (L = 4, distance 2 both ways): the only lines of level 2 at distance <= 4 are the 10 lines
  T(p) = sigma_1 sigma_0 (Lambda(p)) union sigma_2^{-1} sigma_3^{-1} (Lambda(p)) (5 from each side, distance 3).
  Points of level 2 at distance <= 5 from p are exactly the points on T(p). So T(p) must cover all 27 points.
- Counting: 10 lines have 30 incidences, covering 27 points, so the excess is exactly 3: sum over points of
  (cover multiplicity - 1) = 3. Hence T(p) has at most 3 intersecting pairs of lines, i.e. it is a partial spread of
  size 10 with 3 coincidences (spread of Q(5,2) = 9 lines covers 27 points exactly; 9 + 1 line gives excess 3).
- Equivalently (dual of Q(5,2) = H(3,4)): each pencil Lambda(p) (5 concurrent lines = a line of H(3,4)) must map to
  an almost-partial spread. Needed for all 27 points p, for both halves.
- So L = 4 (n = 288) needs a bijection of the 45 lines of level 0 onto level 2 that sends each of the 27 pencils to an
  almost-disjoint line set. This is a nontrivial combinatorial condition; the hill climb in search_cyc.py tests it.

## Results so far
See scoreboard line for c13 and edges/. Level cycles L = 2 (double matching, repeated edge in the random draw),
L = 4 random: diameter 6 (n = 288); L = 6 random: diameter 7 (n = 432). Bipartite random partial matchings on
P5, C6 (degree cap 2) have diameter 11 and 9. K_{2,3} with greedy partial matchings was disconnected (one level
got no matchings; a greedy bug or capacity issue, not analysed further).

## Not done
- Hub vertices: all lines are saturated in the L = 4 cycle, so hubs need a different layout (free spare slots).
- (a) with injective maps and surgery on degree-5 points: would need deleting incidences; not explored.

## Update: valid construction and L = 4 status
- VALID: L = 2 levels, sigma and tau two line bijections between the levels (every line has two matching edges, one
  to each copy of its level; points none). Built by l2.py; checked with apsp: n = 144, degree 5, bipartite,
  diameter 5. File: edges/best_valid_n144.txt (also edges/l2_s1.txt). Score 144/354 = 0.41.
- L = 4 cycle (C4 of levels, the only connected 2-regular bipartite level graph): random bijections diameter 6;
  hill climb on the 45-line bijections (search_cyc.py, single-threaded) stalled at about 1,100 unreached ordered pairs
  after ~2,500 swaps (logs_hc_L4_s1.txt, logs_hc_L4_s2.txt). No valid L = 4 graph found. The counting condition
  above (T(p) covers level 2, i.e. pencils of Q(5,2) mapped to near-partial spreads for all 27 points) looks like the
  obstruction; I did not prove it infeasible.
- Odd L (5 levels, n = 360 > 354) is excluded by bipartiteness for the cycle layouts. Bipartite level graphs with 5
  levels (K_{2,3}, P_5) need partial matchings and have diameter > 5 in the random versions tested (P_5: 11).
