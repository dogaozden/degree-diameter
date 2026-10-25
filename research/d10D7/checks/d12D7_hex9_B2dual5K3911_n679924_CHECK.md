# (12,7) 679,924: 5-level cover of H(9) with both matchings equal to the duality phi, 3,911 freed points, 15,624 hubs

Spin-off of the cell-10-7 job (Opus, 2026-10-25). The table value is 664,300 = 5·|H(9)| (DS14v2). This beats our own
664,412 (checks/d12D7_hex9_dual5K28_n664412_CHECK.md) by 15,512 vertices.

Construction (`research/d10D7/dual/x5gen2.c`): the same 5-level graph as the 664,412 one. Vertices are (v, i), with v a
point or line of H(9) and i in Z5. Hexagon edges are present in every level, plus (p,i) ~ (phi(p), i+1) and
(p,i) ~ (phi(p), i+2), where phi is the duality from `dual/dualfind.c`. There are two changes from the 664,412 graph:

1. **Freed points.** These are the 3,911 pairwise non-collinear points of research/d10D7/sets/P9_c4_noncollinear.txt
   (squad round 4, card c4). Earlier we used only the 28 absolute points of phi. Because phi is a duality, it maps
   B2(p) onto B2(phi(p)) for every point. So any set of pairwise non-collinear points can be freed: the B2 condition
   of research/d10D7/checks/B2_hubs_CHECK.md, the same as for the (11,7) graph d11D7_hex9_B2dualK3911_n406402. Each
   freed point p loses its 10 matching edges. That leaves 10 free slots at the (p, i) and 10 at the (phi(p), i).
2. **Hubs.** There are 7,812 line-side hubs and 7,812 point-side hubs. A line-side hub owned by p is adjacent to
   (p, i) for all five i. A point-side hub owned by p is adjacent to (phi(p), i) for all i. Each freed point owns at
   most 2 hubs per side: 3,901 points own 2 and 10 own 1. The hub graph (`dual/mkhubs_h5x2.py 3911 1`) is two copies
   A and B of the incidence graph of H(5), which has degree 6 and diameter 6. On top of these are two perfect
   matchings: line-side(A) ~ point-side(B) and point-side(A) ~ line-side(B). Hub degree is 5 + 7 = 12. A hub reaches
   every same-side hub of its own copy within 6 steps inside H(5). It reaches every same-side hub of the other copy
   within 1 + 5 = 6 steps, through its matching edge. An earlier random hub graph of degree 7 on 5,642 hubs per side
   left same-side pairs at distance 8; the structured graph avoids that.

n = 10·66,430 + 2·7,812 = 679,924. Degrees: 11 at freed (p, i) that own one hub per side, 12 everywhere else.

Files:
- research/frontier/sols/d12D7_hex9_B2dual5K3911_n679924.sol: the d7hex solution, which lists M = phi on points and
  the 3,911 freed points. Its content is the same as runs/b2/b2dual_q9_c4b.sol. x5gen2 ignores the 3-level hub edges
  stored inside it. sha256 c0656ff630f97bbfb815eec1fdd662063aeb5a3811c4311c2ef4a3a163d7b51d.
- research/frontier/sols/d12D7_hex9_B2dual5K3911_n679924.hubs: the hub layout. Its first line is "HL HP m", followed
  by the owner of each line-side hub, the owner of each point-side hub, and the m hub-graph edges.
  sha256 57befa05050ad23ef5fda6fca9910791b0860e52b4c3d950ced58be8c44cac43.

Rebuild and check (from research/d10D7):
    gcc -O3 -o hexgen2 hexgen2.c && ./hexgen2 9
    gcc -O2 -o dual/x5gen2 dual/x5gen2.c
    dual/x5gen2 hex/hex_q9.bin ../frontier/sols/d12D7_hex9_B2dual5K3911_n679924.sol ../frontier/sols/d12D7_hex9_B2dual5K3911_n679924.hubs g.edges
    gcc -O3 -o apsp ../lifts/coordinator_check/apsp.c && ./apsp g.edges 12 7        # about 15 min, 1 core

apsp output (all pairs, no symmetry assumed), 2026-10-25 00:03 UTC:
    n=679924 edges=4079494 degree min=11 max=12 bipartite=yes diameter=7
    RESULT VALID d=12 D=7 n=679924
The symmetry-reduced pre-check `dual/apsp_sym` (sources: level 0 plus all hubs) gave the same line first.
Edge list sha256 c3ee8add713bbd4162374971357d9afdbdf4b528c22edaa9f83cf3fd81f7e186. A rebuild from the two saved files
gives the same hash.
