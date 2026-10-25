# (12,7) 664,412: the 5-level cover of H(9) with both matchings equal to a duality, 28 absolute flags freed (112 hubs)

Spin-off of the cell-10-7 job (Opus, 2026-10-24). Table value 664,300 = 5·|H(9)| (DS14v2; Delta = q+3, two matchings,
Z5 levels with shifts 1 and 2). We did not hold this cell before.

Construction (`research/d10D7/dual/x5gen.c`). Vertices (v, i), v a point or line of H(9), i in Z5. Hexagon edges in every
level; (p,i) ~ (phi(p), i+1) and (p,i) ~ (phi(p), i+2), with phi the duality of `dualfind.c` (the same M as the (11,7)
graph d11D7_hex9_dualK28_n398636.sol). Diameter <= 7 for any two matchings (polygon-cover theorem,
REGULARITIES.md §1.3); here both are phi, which keeps the graph simple because the two edges go to different levels.
For each of the 28 absolute flags (p, l = phi(p), phi(l) = p) delete the 10 extra edges of p and add two line-side hubs
~ (p, i) for all i and two point-side hubs ~ (l, i) for all i: +4 vertices per flag; hubs are linked by a random
4-regular bipartite hub graph (56 + 56 hubs, research/d10D7/dual/hg56_d4.txt, same-side distance <= 6).

Why it works. The level shift (v,i) -> (v,i+1) is an automorphism. A freed point (p,0) reaches the points opposite p at
levels +1 and +2 by (p,0) ~> (u,0) -> (phi(u), j) -> (x, j) with u in S'(p): phi maps S'(p) onto S(l), whose lines
partition the points opposite p. The freed line (l,0) reaches the lines opposite l at levels -1 and -2 by
(l,0) ~> (L,0) -> (phi^-1(L), -j) -> (t, -j) with L in S(l). Everything else is reached through the hubs, by the
other vertices' extra edges, or by the level symmetry (a freed target is the same condition as a freed source).
These are the conditions of the 3-level (11,7) graph; with sigma_1 = sigma_2 the freed-source conditions coincide.

Files: research/frontier/sols/d12D7_hex9_dual5K28_n664412.sol (M = phi on points and the 28 freed points; same content
as the (11,7) solution) and d12D7_hex9_dual5K28_n664412.hubgraph (56 + 56 hubs). x5gen ignores the hub edges inside the
.sol and reads the .hubgraph file.

Rebuild and check (from research/d10D7):
    gcc -O3 -o hexgen2 hexgen2.c && ./hexgen2 9
    gcc -O2 -o dual/x5gen dual/x5gen.c
    dual/x5gen hex/hex_q9.bin ../frontier/sols/d12D7_hex9_dual5K28_n664412.sol ../frontier/sols/d12D7_hex9_dual5K28_n664412.hubgraph g.edges
    gcc -O3 -o apsp ../lifts/coordinator_check/apsp.c && ./apsp g.edges 12 7        # about 17 min, 1 core

apsp (all pairs, no symmetry assumed), 2026-10-24 23:13 UTC:
    n=664412 edges=3986304 degree min=9 max=12 bipartite=yes diameter=7
    RESULT VALID d=12 D=7 n=664412
Edge list sha256: 622c177ba895ab10f065d6d8bf5deb01ecd889746b2ee64d0a4885d4bcbae3fa
