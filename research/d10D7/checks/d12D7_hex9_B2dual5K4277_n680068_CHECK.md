# (12,7) 680,068: 5-level cover of H(9), duality matchings, 4,277 freed points, hub graph = 2-level cover of H(5) with B2 hubs

Spin-off of the cell-10-7 job (Opus, 2026-10-25). The table value is 664,300 (DS14v2). This beats our 679,924
(d12D7_hex9_B2dual5K3911_n679924_CHECK.md) by 144.

The main graph is the same as for 679,924 (`research/d10D7/dual/x5gen2.c`, or `dual/xgen.c` with LV = 5, which gives an
identical edge list). Vertices are (v, i), with v a point or line of H(9) and i in Z5. Hexagon edges are present in
every level, plus (p,i) ~ (phi(p), i+1) and (p,i) ~ (phi(p), i+2), where phi is the duality. The freed points are the
4,277 pairwise non-collinear points of research/d10D7/sets/P9_r5c6_4277.txt. Each freed point owns at most 2 hubs per
side. A hub is adjacent to its owner (or to phi of its owner) in all five levels.

The new part is the hub graph (`dual/mkhubs_h5b2.py`). It has 7,884 + 7,884 hubs, and each hub has hub-graph degree
at most 7. It is the 2-level cover of H(5) built with the matching M of our (7,7) solution
d7D7_hex5_B2K72_n23580.sol:
- two copies A and B of the incidence graph of H(5);
- (p,A) ~ (M(p),B) and (p,B) ~ (M(p),A) for every non-freed point p;
- for each of the 72 freed pairs (p, l = M(p)) of that solution, which satisfy the B2 condition, the two cover edges
  are removed and two extra hubs added: z_p ~ (p,A), (p,B) and z'_l ~ (l,A), (l,B);
- the z's are linked by that solution's degree-4 hub graph.

Two copies plus one matching give 7,812 vertices per side (the doubled H(5) used for 679,924); the B2 hubs add 72.
The hub graph alone is a bipartite graph with 15,768 vertices, Δ = 7 and diameter 7 (apsp below). So any two
same-side hubs are within 6 and any two hubs within 7, without using the main graph.

n = 10·66,430 + 2·7,884 = 680,068. Owners: hub j is owned by freed point j mod 4,277, so 3,607 points own 2 hubs per
side and 670 own 1.

Files:
- research/frontier/sols/d12D7_hex9_B2dual5K4277_n680068.sol: M = phi on points and the 4,277 freed points. It is the
  same file as d11D7_hex9_B2dualK4277_n407134.sol; x5gen2 ignores the 3-level hub edges inside it.
- research/frontier/sols/d12D7_hex9_B2dual5K4277_n680068.hubs: the hub layout ("HL HP m", owners, hub-graph edges).

Rebuild and check (from research/d10D7):
    python3 dual/mkhubs_h5b2.py ../frontier/sols/d7D7_hex5_B2K72_n23580.sol 4277 HUBS hg.edges   # = the .hubs file
    ./apsp hg.edges 7 7                                                                          # hub graph alone
    gcc -O2 -o dual/x5gen2 dual/x5gen2.c
    dual/x5gen2 hex/hex_q9.bin ../frontier/sols/d12D7_hex9_B2dual5K4277_n680068.sol ../frontier/sols/d12D7_hex9_B2dual5K4277_n680068.hubs g.edges
    ./apsp g.edges 12 7        # about 15 min, 1 core

Hub graph alone: n=15768 edges=55116 degree min=6 max=7 bipartite=yes diameter=7, RESULT VALID d=7 D=7.

apsp output (all pairs, no symmetry assumed), 2026-10-25 00:4x UTC:
    n=680068 edges=4076986 degree min=11 max=12 bipartite=yes diameter=7
    RESULT VALID d=12 D=7 n=680068
The symmetry-reduced pre-check `dual/apsp_sym ... 132860 664300` (sources: level 0 and all hubs) gave the same line.
Edge list sha256 9d14db3f125bc024962f183a9d3398311f7df21764b47014a33760dfd9302bf4 (x5gen2 and xgen LV=5 give the same
file). sha256 of the .sol abe318b79b5fcc43417894fced2de0204ab53ba2f42ba7baeaee789dec8dd124 and of the .hubs file:
2f8cafbac6d2c49672414297ca66acfc7fa02b8d7911752a99967faf3973ae4a
