# deep-65b records

## (6,5): 704 vertices (table value 684)

`d6D5_n704_split_c11xm16.edges` (sha256 85b88c13999f3b0f36798a43a57e5f8cca11e7bf93888f3e37a4232d1335aece):
a 6-regular bipartite graph on 704 vertices with diameter 5.

Construction: G = Z11 x M16 = SmallGroup(176,23) ("C11 x (C8 : C2)", M16 = <x, y | x^8 = y^2 = 1, y x y^-1 = x^5>).
Lift of the 2+2 base [[1,5],[5,1]] by G: vertices A0_h, A1_h, B0_h, B1_h (h in G), edges A0_h - B0_h, A1_h - B1_h,
A0_h - B1_{h e} (e in E1), B0_h - A1_{h e} (e in E2), with (element (a,i,j) = a x^i y^j)
  E1 = {(7,5,1), (9,7,0), (4,4,1), (6,0,0), (1,1,0)},  E2 = {(7,1,1), (8,0,1), (6,1,0), (9,0,1), (5,4,0)}.
Equivalently: the degree-10 Haar graph H(G, E1 u E2) with every vertex split into an edge. Not a Haar graph: every
Haar graph of degree 6 and diameter 5 on 686-900 vertices is excluded (research/six-five-384/README.md).

Rebuild: `python3 build_d6D5_n704.py OUT.edges` (self-contained: the group by its formula, no table or GAP; runs its own
BFS check). Checks (d6D5_n704_checks.txt): research/lifts/coordinator_check/apsp.c RESULT VALID at d = 6, D = 5 and
INVALID at D = 4; score65 bad = 0; the builder's own BFS: diameter 5.

Found: deep-65b round-1 Haiku card c1 (tabu over (E1, E2) with the six covering conditions of tools/split15.c, seed 3 on
SmallGroup(176,23)); the family, its closed form and the exact search are Opus's (NOTES.md). Rebuilt and checked by
Opus from the formula above.

Structure checks (records/, Python BFS on the edge list): distance profile from an A0 vertex (1, 6, 30, 140, 321, 206),
from an A1 vertex (1, 6, 30, 139, 321, 207); B1 matches A0 and B0 matches A1. So no automorphism maps A0 to A1: the
graph is not vertex-transitive and its colour-preserving automorphism group is not transitive on either side, which
shows directly that it is not a Haar graph. Girth 6 (66 closed walks of length 4 at every vertex = no 4-cycles).

Second description (build_d6D5_n704_z88.py): G = Z11 x M16 = Z88 :_45 Z2 ((t, j)(s, l) = (t + 45^j s, j + l)), so the
normal subgroup Z88 acts freely with 8 orbits and the graph is a cyclic Z88-lift of an 8-vertex base (A0^j, A1^j, B0^j,
B1^j, j = 0, 1; the script prints the 24 darts and their voltages). The script lifts that base and gets exactly the
record's edge set (2112 edges, identical under the relabelling (a, i, j) <-> (CRT(a, i), j)).
