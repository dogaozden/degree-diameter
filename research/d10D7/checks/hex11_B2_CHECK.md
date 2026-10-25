# (13,7), (14,7), (15,7): B2 hubs on the hexagon covers of H(11)

Spin-offs of the cell-10-7 job (Opus, 2026-10-25). The table values (DS14v2) are all hexagon covers of the split
Cayley hexagon H(11), with N = 177,156 points and N lines:
- (13,7) 1,062,936 = 6N: 3 levels, one matching (X(M), Delta = q+2);
- (14,7) 1,771,560 = 10N: 5 levels, two matchings with shifts 1 and 2 (Delta = q+3);
- (15,7) 2,480,184 = 14N: 7 levels, three matchings with shifts 1, 2, 3 (Delta = q+4).

Construction. Take all matchings equal to one bijection M from points to lines. Vertices are (v, i), with v a point or
line and i in Z_LV. Hexagon edges are present in every level, and (p, i) ~ (M(p), i+s) for s = 1..j, where LV = 2j+1.
A freed pair (p, l = M(p)) loses its j extra edges in every level. That frees j slots at each (p, i) and at each
(l, i), so up to j line-side hubs ~ (p, i) for all i and j point-side hubs ~ (l, i) for all i can be added. By the
B2 condition (B2_hubs_CHECK.md), a pair needs nothing else when M maps the q(q+1) points at distance 2 from p onto the
q(q+1) lines at distance 2 from l. With pairwise opposite freed points and pairwise opposite freed lines this holds
for all pairs at once. The 3-level case is exactly our (10,7) construction. The 5-level case is the (12,7)
construction, without the duality.

Sets (q = 11, both checked by `research/squads/d10D7-r4/tools/setcheck`):
- lines: research/d10D7/sets/L11_spread.txt, the 1,332 = q³+1 H(11)-lines inside a hyperplane with an elliptic
  section of Q(6,11), pairwise opposite (`sets/hspread.py hex/hex_q11.bin 11 11 1 1`);
- points: research/d10D7/sets/P11_tabu_s1.txt, 135 pairwise opposite points (`ovoid/potabu2`, a k-fixed tabu that
  computes conflicts on the fly; greedy gives 103).
So K = 135. `d7hex b2` pairs them and builds M; the solution is research/frontier/sols/d13D7_hex11_B2K135_n1063206.sol.

| cell | table | n | hubs | hub graph | file |
|---|---|---|---|---|---|
| (13,7) | 1,062,936 | 1,063,206 | 135 + 135 | d7hex, degree 8 (≤ 10) | d13D7_hex11_B2K135_n1063206.sol |
| (14,7) | 1,771,560 | 1,772,100 | 270 + 270 | random, degree 8 (≤ 9), diameter 6 | d14D7_hex11_B2K135_n1772100.hubs |
| (15,7) | 2,480,184 | 2,480,994 | 405 + 405 | random, degree 7 (≤ 8), diameter 6 | d15D7_hex11_B2K135_n2480994.hubs |

The (14,7) and (15,7) graphs use the same .sol (M and freed points) as (13,7):
    gcc -O3 -o hexgen2 hexgen2.c && ./hexgen2 11
    ./d7hex edges hex/hex_q11.bin ../frontier/sols/d13D7_hex11_B2K135_n1063206.sol g13.edges
    gcc -O2 -o dual/xgen dual/xgen.c
    dual/xgen hex/hex_q11.bin ../frontier/sols/d13D7_hex11_B2K135_n1063206.sol ../frontier/sols/d14D7_hex11_B2K135_n1772100.hubs 5 g14.edges
    dual/xgen hex/hex_q11.bin ../frontier/sols/d13D7_hex11_B2K135_n1063206.sol ../frontier/sols/d15D7_hex11_B2K135_n2480994.hubs 7 g15.edges
Hub layouts: `python3 dual/mkhubs_rand.py 270 135 8 1 HUBS hg.edges 2` and `... 405 135 7 1 HUBS hg.edges 3`. The hub
graphs alone have diameter 6 (apsp), so every two hubs are within 6 through the hub graph.

Checks:
