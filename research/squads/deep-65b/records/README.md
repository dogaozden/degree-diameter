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
