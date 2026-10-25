# (14,7): the polygon cover GH(11) + 2 matchings over Z5 with "units"

Session cell-14-7 (Opus), 2026-10-24. Cell (14,7): bipartite, maximum degree 14, diameter 7. Table value 1,771,560
(Delorme-Gomez-Quisquater: GH(11) incidence graph + 2 point->line perfect matchings, lifted by Z5; polygon edges
voltage 0, matching t voltage t; research/lifts/LITERATURE.md section 5 on branch claude/voltage-lifts-search-6lfotq).

## Session 2 (2026-10-24 afternoon): the type-2 design, hundreds of units

**Type-2 design.** Take the unit's line THROUGH its point (an incident flag p ∈ l = sigma_t(p)) and let
W = the q² points collinear with p off l, K = the q² lines meeting l off p. If sigma_t maps W onto K (any bijection),
both unit endpoints keep eccentricity 7:
- a point y opposite p lies on a unique line N at distance 4 from l (its path to l avoids p, since d(y,p) = 6), and N
  meets a unique K ∈ K (the line on N's path to l); with w = sigma_t^-1(K) ∈ W the route
  (p,c) –2– (w,c) –hop– (K,c+h) –3– (y,c+h) has length 6;
- a line T opposite l contains a unique point y at distance 4 from p not via l; y is collinear with a unique w ∈ W, and
  (l,c+h) –2– (sigma_t(w),c+h) –hop– (w,c) –1– · –1– (y,c) –1– (T,c) has length 6.
So a unit costs q² = 121 prescribed assignments instead of 14,641 (the older design via points at distance 4, whose
3-ball analogue is what d7hex.c's type-2 pre-pass approximated with lines at distance 5 from p). Units of one matching
need pairwise disjoint zones {p} ∪ W and {l} ∪ K (and no freed point in another W): zones of two units can never be
shared consistently (it would need a 10-cycle in the hexagon), so this is a packing problem. Hubs of the same side are
kept within distance 6 by a random hub graph (each hub has Δ − m = 9 spare slots at (14,7)).

**Checks.** `uhcheck.c` (generalizes ucheck12 to any small graph on the new vertices: hub links, super-hubs) and
`apsp_cyc.c` (independent: works on the edge list, verifies that the copy shift is an automorphism, then all-pairs BFS
from one copy plus the new vertices). Both agree on every small case tried, valid and invalid (e.g. 7 units at q = 5:
58 pairs beyond 7 without hub links in both, VALID with Fano links in both).

**Tools.** `t2design.c` (type-2 units: random, SCAN or FLAGS placement; BOTH=1 lets a point carry units of several
matchings), `pack.c` (packings of zones: annealing, compact growth, CHECKONLY validator), `randhub.py` (random hub
graph, same-side diameter <= 6), `unit_edges2.py` (edge list with hub links), `t2cell.sh` (whole pipeline for any DGQ
D = 7 cell), `flowdesign.c` (older type-4 designs by max-flow between constraint types: 5 units per matching exactly),
`hexbin2txt.py` (H(9) from research/p4/d6/hexgen.c).

**Hermitian-spread packings (spreadpack.c).** The best packings are not found by local search on flags but by
geometry. Points of H(q) are at distance <= 4 iff they are orthogonal on the quadric Q(6,q). Take an elliptic hyperplane
section E = Q(6,q) ∩ v^perp (v = e0 + c e4, i.e. X4 = -c X0 with -c a non-square; c = 1 at q = 7, 11, c = 2 at q = 5,
c = 11 at q = 13). The hexagon lines inside E form a spread: q^3+1 pairwise opposite lines partitioning the points of
E (checked by the program). Flags (p, spread line through p) never conflict on the line side (line zones lie in the
disjoint 2-balls of the spread lines), and they do not conflict on the point side when the points are pairwise
non-orthogonal. So a packing = a partial ovoid of the elliptic quadric Q^-(5,q) = E; an iterated local search on the
orthogonality graph of E (degree q(q^2+1)) finds 48 (q = 5), 84 (q = 7), 155 (q = 11), against 30-34, 47 and 91 for the
best local searches on flags. (At q = 3 the optimum, 28, is an ovoid of H(3) with a dual spread instead; ovoids of H(q)
exist only for q = 3^h.) Flag sets: sols/flags_q*_spread*.txt.

**Orbit packings (secantclique.c, phaseils.c, orbitclique.c).** Partial ovoids that are unions of orbits of an
isometry of E do better at q = 11. E's 6-space is A ⊥ V4 with A = (x0,x3) anisotropic and V4 = (x1,x2,x5,x6)
hyperbolic. The rotations of A (order q+1) have orbits O_b = {[a:b] : N(a) = Q4(b)}, one per point b of PG(3,q) off the
quadric Q4 = 0. Two orbits are compatible iff B4(b,b')^2 - 4 Q4(b) Q4(b') is a nonzero square, i.e. the line bb' is a
secant. The maximum is 17 orbits at q = 11, proven by exhaustive branch and bound (the graph is vertex-transitive); with 12
fixed points [0:b] (b singular) this gives 216, which is maximal. Isometries that also move V4 do better. A random
order-4 element (squad card r3c3) and an order-8 element give 240 = 60 x 4 = 30 x 8 by clique search on their orbit
compatibility graphs. That is the current (14,7) packing. At q = 5, 7 plain local search wins (48, 84 against 36, 72
for rotation orbits); at q = 13 the rotation orbits give 252 (17 x 14 + 14, not proven optimal) against 205.

## The unit

A unit (p, t) on that lift deletes the 5 lifted copies of the matching edge (p, l), l = sigma_t(p), and adds two new
vertices: z joined to the 5 copies (p, c) and z' joined to the 5 copies (l, c). Degrees stay <= 14 (z, z' have degree
5). Net +2 vertices.

Why the diameter can stay 7. In the DGQ lift every pair has a route using at most one matching edge, located at the
source, at the target, or at a neighbour of the source (with q+1 choices of neighbour). Deleting (p, l) in every copy
therefore only breaks
1. routes from (p, c) to points opposite p (hexagon distance 6) in copy c + h_t (everything else in that copy is
   reached through z: (p,c) - z - (p,c+h_t) then <= 4 or <= 5 hexagon steps), and
2. routes from (l, c + h_t) to lines opposite l in copy c (dually, through z').
Repair of 1: for a line M through p, the 14,641 lines at distance 4 from M whose projection onto M is not p partition
the 161,051 points opposite p (11 each). If sigma_t maps points at distance 4 from p onto those lines, every opposite
point y has the route (p,c) -4-> (x,c) -hop-> (sigma_t(x), c+h_t) -1-> (y, c+h_t) of length 6. Dually for 2 with the
points at distance 4 from a point N of l whose projection is not l. DGQ is valid for any matchings, so prescribing
sigma_t on these sets costs nothing; a greedy assignment always exists (|A&B| = |F1&C| in every case tried).
The cyclic shift of copies is an automorphism fixing z and z', so it suffices to check the sources (x, 0) and z, z'.

## Result: 1,771,562 vertices (one unit)

- State (matchings): `u11_one.state.gz` (glift state format: header, then per point "sigma_1 h_1 sigma_2 h_2",
  then per line its flag voltages, all 0); unit file `u11_one.units` ("1000 1": point 1000, matching 1).
- Build:
  ```
  cd research/cell147 && gcc -O2 -o gh_build gh_build.c && ./gh_build 11 > data/gh_11.txt   # sha256 e3a4d834...6eb9d
  cd units && gunzip -c u11_one.state.gz > u11_one.txt
  python3 unit_edges.py ../data/gh_11.txt u11_one.txt u11_one.units u11_one.edges        # sha256 5375337d...fd97f30
  ```
  The edge list has n = 1,771,562 vertices and 12,400,925 edges (first line n, then "u v").
- Check (`ucheck12`, written for this job from the definitions, all 354,312 base sources plus the 2 unit vertices,
  every lift vertex being equivalent to one of them under the cyclic shift): `d14D7_n1771562_ucheck.txt`:
  pairs beyond distance 7 = 0. The same checker agrees with apsp on the small cases below (valid and invalid).

## Small cases checked with apsp (all-pairs, no symmetry assumed)

| base | units | vertices | Delta | apsp |
|---|---|---|---|---|
| GH(3) + 2 matchings over Z5 | 1 | 3,642 | 6 | VALID D=7 |
| GH(5) + 2 matchings over Z5 | 1 | 39,062 | 8 | VALID D=7 |
| GH(5) + 2 matchings over Z5 | 2 (far apart) | 39,064 | 8 | INVALID D=8 (new vertices too far apart; ucheck agrees) |
| GH(5) + 2 matchings over Z5 | 20 (clustered, udesign) | 39,100 | 8 | VALID D=7 |

## Every Delorme–Gómez–Quisquater cell, with one unit per matching (+2j vertices)

`do_cell.sh NAME BASE n j POINT` builds the polygon cover of a generalized n-gon (n = 4: W(q) from
`../gq_build.py`; n = 6: H(q) from `../gh_build.c`, q = 8, 9 from the GF(q) version in
research/squads/d14D7-r1/c3/gh_build.c) with j matchings over Z_{2j+1}, plus units (POINT, t) for t = 1..j, all at one
point. Units on different matchings never compete for prescribed assignments; their lines are chosen pairwise within
distance n − 2, so the new vertices stay within reach of each other. Files are in `cells/`: `NAME.units`, `NAME.state.gz`
(matchings), `NAME.edges.gz` (small graphs) or `NAME.edges.sha256`, and the check output.

| cell | table (DGQ) | base | j | ours | check |
|---|---|---|---|---|---|
| (10,5) | 4,000 | W(7) | 2 | **4,004** | apsp VALID (`cells/d10D5.apsp.txt`) |
| (11,5) | 5,850 | W(8) | 2 | **5,854** | apsp VALID |
| (12,5) | 8,200 | W(9) | 2 | **8,204** | apsp VALID |
| (13,5) | 11,480 | W(9) | 3 | **11,486** | apsp VALID |
| (14,5) | 14,760 | W(9) | 4 | **14,768** | apsp VALID |
| (15,5) | 20,496 | W(11) | 3 | **20,502** | apsp VALID |
| (7,7) | 23,436 | H(5) | 1 | **23,438** | apsp VALID |
| (9,7) | 117,648 | H(7) | 1 | **117,650** | apsp VALID |
| (10,7) | 224,694 | H(8) | 1 | **224,696** | apsp VALID |
| (11,7) | 398,580 | H(9) | 1 | 398,582 | apsp running |
| (12,7) | 664,300 | H(9) | 2 | 664,304 | apsp queued |
| (13,7) | 1,062,936 | H(11) | 1 | 1,062,938 | unit endpoints pass; ucheck12 queued |
| (14,7) | 1,771,560 | H(11) | 2 | **1,771,562** (1 unit) / 1,771,564 (2 units) | ucheck12 VALID (1 unit); 2 units running; apsp running |
| (15,7) | 2,480,184 | H(11) | 3 | 2,480,190 | unit endpoints pass; ucheck12 queued |
| (16,7) | 4,022,340 | H(13) | 2 | 4,022,344 | unit endpoints pass; ucheck12 queued |

Rebuild any of them: `gunzip -k cells/NAME.state.gz && python3 unit_edges.py BASE cells/NAME.state cells/NAME.units
OUT.edges` (BASE as in the table, from gh_build / gq_build), then `apsp OUT.edges d D`.
