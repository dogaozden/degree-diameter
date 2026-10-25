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
- points: research/d10D7/sets/P11_r6c7_756.txt, 756 pairwise opposite points. Squad card r6/c7 built it from the
  E7 lattice mod 11: the Weyl group W(E7) acts on E7 ⊗ GF(11), which carries a non-degenerate 7-dimensional quadratic
  form. The card took an exact maximum-weight clique over compatible orbits of a subgroup, then mapped the result to
  Q(6,11) by an isometry. The set is maximal: no point of H(11) is opposite to all 756. For comparison, a k-fixed tabu
  search (`ovoid/potabu2.c`) reaches only 135, and greedy 103. The q = 7 analogue is the 288 set.
So K = 756. `d7hex b2` pairs them and builds M; the solution is research/frontier/sols/d13D7_hex11_B2K756_n1064448.sol.

| cell | table | n | hubs | hub graph | file |
|---|---|---|---|---|---|
| (13,7) | 1,062,936 | 1,064,448 | 756 + 756 | d7hex, degree 8 (≤ 10) | d13D7_hex11_B2K756_n1064448.sol |
| (14,7) | 1,771,560 | 1,774,584 | 1,512 + 1,512 | random, degree 8 (≤ 9), diameter 7 | d14D7_hex11_B2K756_n1774584.hubs |
| (15,7) | 2,480,184 | 2,484,720 | 2,268 + 2,268 | random, degree 8 (≤ 8), diameter 7 | d15D7_hex11_B2K756_n2484720.hubs |

The (14,7) and (15,7) graphs use the same .sol (M and freed points) as (13,7):
    gcc -O3 -o hexgen2 hexgen2.c && ./hexgen2 11
    ./d7hex edges hex/hex_q11.bin ../frontier/sols/d13D7_hex11_B2K756_n1064448.sol g13.edges
    gcc -O2 -o dual/xgen dual/xgen.c
    dual/xgen hex/hex_q11.bin ../frontier/sols/d13D7_hex11_B2K756_n1064448.sol ../frontier/sols/d14D7_hex11_B2K756_n1774584.hubs 5 g14.edges
    dual/xgen hex/hex_q11.bin ../frontier/sols/d13D7_hex11_B2K756_n1064448.sol ../frontier/sols/d15D7_hex11_B2K756_n2484720.hubs 7 g15.edges
Hub layouts: `python3 dual/mkhubs_rand.py 1512 756 8 1 HUBS hg.edges 2` and `... 2268 756 8 1 HUBS hg.edges 3`. Each
hub graph on its own is bipartite with diameter 7 (apsp), so any two same-side hubs are within 6 of each other through
the hub graph. `d7hex b2` reports "same-side hub violations 25776" for (13,7). That counts pairs at hub-graph distance 6,
which its conservative test rejects; distance 6 is enough. The all-pairs check is what counts.

Checks:
- sha256: sets/P11_r6c7_756.txt d2544943d51505466ece6f93a4f3afc4107756a683a5c050c2d6eb3315cd4eae, sets/L11_spread.txt
  5456ee503751ed74c08ffb95ab9110d5c8599f28cd871bbd1ca733824f50f003, d13D7 .sol
  44d6099531c265851d7029bddd860f2835a33eaf5fe25a6a3f4c564e582bb3f8, d14D7 .hubs
  85e64b14afcebb2934b6cd9661864a6ebd1b6706df7783542c8b2956605ea298, d15D7 .hubs
  f3171ef3140100af8af5851c5a54b0aff40ce5e49443a873bb9a30d55c842d5d.
- **(13,7) 1,064,448: all-pairs check VALID** (2026-10-25 01:18 UTC). The check used `checks/apsp_range.c`, which is
  apsp.c with the BFS sources restricted to a range, run as three processes covering [0, n):
      n=1064448 edges=6917400 degree min=11 max=13 bipartite=yes sources [0,354816) eccentricity max=7
      ... sources [354816,709632) eccentricity max=7; ... sources [709632,1064448) eccentricity max=7
      RESULT VALID (range) d=13 D=7 n=1064448 (all three)
  Edge list (`d7hex edges`) sha256 1e499a0f3bda8685f3b6eac8f9ec9f938603c38abde10030abd2c160365a197e.

## (16,7) over H(13)

The table's (16,7) value 4,022,340 = 10·402,234 is the 5-level cover of H(13). The same construction applies:
- lines: sets/L13_spread.txt, 2,198 = q³+1 opposite lines (sha256 12b5cb57a1239671ef6b6e24a92b36418208f6d74cfea545ce2a7ff46c8e991b);
- points: sets/P13_E7sub_E6_792.txt, 792 pairwise opposite points (sha256
  2a7933aac3cf83cdb21643f9e19cf0cdcf655957d75af4c7a08654c3e631a5f8). This is the best union of orbits of the reflection
  subgroup W(E6) ≤ W(E7) acting on E7 ⊗ GF(13) (`ovoid/e7/subq.py 13 E6`, orbits of sizes 72 + 720). W(E7) itself
  has no pairwise opposite orbit at q = 13. Greedy gives 131.
Solution research/frontier/sols/d16D7_hex13_B2K792_n4025508.sol (sha256
56438ae0d1f99fcdc5269d9d3a04c36920a4a9aee7b2805737e9d4cd5c227e76) and hub layout d16D7_hex13_B2K792_n4025508.hubs
(sha256 78cfb244d6f491b32be1d7af67f698ac125fc7d6912f90a6b715bc475e3d4bd9; `mkhubs_rand.py 1584 792 8 1 HUBS hg 2`; the
hub graph alone has diameter 7). `dual/xgen hex/hex_q13.bin SOL HUBS 5 g.edges` gives n = 4,025,508, 32,199,312
edges.
- **(14,7) 1,774,584: all-pairs check VALID** (2026-10-25 02:19 UTC). apsp_range was run as four processes covering
  [0, n) (`checks/run_ranges.sh`):
      n=1774584 edges=12420576 degree min=13 max=14 bipartite=yes sources [0,443646) eccentricity max=7
      ... [443646,887292) max=7; [887292,1330938) max=7; [1330938,1774584) max=7
      RESULT VALID (range) d=14 D=7 n=1774584 (all four)
  Edge list (`dual/xgen ... 5`) sha256 97e726f453799b8fffabf3fa2c5623b5a33f99b43a8cdd20b2e8d6a7ec454dcb.
