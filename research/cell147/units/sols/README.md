# Solution files (cell (14,7) and related DGQ cells), type-2 units

## d14D7_n1772520 (current best): bipartite (14,7) on 1,772,520 vertices (table 1,771,560, +960)

Same base and file formats as below; 480 type-2 units = the 240 flags of `flags_q11_orbit4_240.txt` (a partial ovoid of
the elliptic section X4 = -X0: 60 orbits of size 4 of an order-4 isometry, squad card r3c3; each flag = a point and the
Hermitian-spread line through it) used on BOTH matchings; circulant hub graph of degree 9 (randhub.py, NU 480, seed 1).
Rebuild: `gunzip -k sols/d14D7_n1772520.state.gz && python3 unit_edges2.py ../data/gh_11.txt sols/d14D7_n1772520.state
sols/d14D7_n1772520.units sols/d14D7_n1772520.hubs d14D7_n1772520.edges` (12,407,640 edges, sha256 in .edges.sha256).
Checks: `d14D7_n1772520_uhcheck.txt` (all 354,312 base sources + 960 new vertices: 0 pairs beyond 7); independent
apsp_cyc: `d14D7_n1772520_apsp_cyc.txt`.

## d14D7_n1771870 (earlier): bipartite (14,7) on 1,771,870 vertices (table 1,771,560)

DGQ polygon cover of H(11) (research/cell147/gh_build.c, `./gh_build 11`, sha256 e3a4d834...6eb9d) with 2 matchings over
Z5, plus 155 type-2 units (75 on matching 1, 80 on matching 2; README.md one level up) and a hub graph.
- `d14D7_n1771870.state.gz`: the matchings (glift state format: "glift q j m D", "cyc m", then per point
  "sigma_1(p) 1 sigma_2(p) 2", then per line its flag voltages, all 0).
- `d14D7_n1771870.units`: units "p t l" (freed point p, matching t, l = sigma_t(p), a line through p).
- `d14D7_n1771870.hubs`: hub links in uhcheck EXTRAS format ("0" super-hubs, then "a b": line-side hub of unit a/2 ~
  point-side hub of unit (b-1)/2).
- Rebuild the edge list (n = 1,771,870, 12,403,090 edges, sha256 in `d14D7_n1771870.edges.sha256`):
  ```
  cd research/cell147 && gcc -O2 -o gh_build gh_build.c && mkdir -p data && ./gh_build 11 > data/gh_11.txt
  cd units && gunzip -k sols/d14D7_n1771870.state.gz
  python3 unit_edges2.py ../data/gh_11.txt sols/d14D7_n1771870.state sols/d14D7_n1771870.units sols/d14D7_n1771870.hubs d14D7_n1771870.edges
  ```
  Vertex ids: lift vertex (x, c) = 5x + c (points x < 177,156, lines 177,156 + line index), hubs from 1,771,560 on.
- Checks: `uhcheck ../data/gh_11.txt STATE UNITS HUBS 7 3` (all 354,312 base sources and the 310 new vertices; the copy
  shift is an automorphism fixing the new vertices): `d14D7_n1771870_uhcheck.txt`, 0 pairs beyond 7. Independent:
  `NB=1771560 ./apsp_cyc d14D7_n1771870.edges 14 7 5 THREADS` (verifies the shift automorphism on the edge list, then
  BFS from one copy and all new vertices).

## Other D = 7 cells (same construction; DGQ cover with j matchings over Z_{2j+1}, type-2 units, hub graph)

Rebuild any of them like (14,7): `gunzip -k sols/NAME.state.gz && python3 unit_edges2.py BASE sols/NAME.state
sols/NAME.units sols/NAME.hubs NAME.edges`, with BASE the hexagon file below; check with `uhcheck BASE STATE UNITS HUBS 7
THREADS` and `NB=<2*P*m> ./apsp_cyc NAME.edges Delta 7 m THREADS`. Every row uses the same flag set on all j matchings
(t2cell.sh with FLAGSFILE, BOTH=1), so units = j × flags. n = 2·P·(2j+1) + 2·units.

Base files: H(q) for q = 5, 7, 11, 13 from `research/cell147/gh_build.c` (`./gh_build q`; gh_5 sha256 bb73813e..., gh_7
6a7fbe5a..., gh_11 e3a4d834..., gh_13 8838410e...); H(8) from research/squads/d14D7-r2/c15/gh8.c (GF(8), sha256
1703336b...); H(9) from research/p4/d6/hexgen.c via `hexbin2txt.py` (gh_9 sha256 c26865bd...).

| cell | file | vertices | previous | base, j, units | flags per matching | checks |
|---|---|---|---|---|---|---|
| (7,7) | d7D7_n23532 | 23,532 | 23,484 (master) | H(5), j = 1, 48 | flags_q5_spread48.txt (spread ILS, C = 2) | uhcheck all sources, apsp_cyc VALID |
| (9,7) | d9D7_n117824 | 117,824 | 117,650 (master) | H(7), j = 1, 88 | flags_q7_orbit88.txt (order-4 orbits, card r4c5) | uhcheck all sources, apsp_cyc VALID |
| (10,7) | d10D7_n224946 | 224,946 | 224,694 (table) | H(8), j = 1, 126 | flags_q8_spread126.txt (GF(8) section X4 = X0 + X3, card r4c7) | uhcheck all sources, apsp_cyc VALID |
| (11,7) | d11D7_n398880 | 398,880 | 398,606 (master) | H(9), j = 1, 150 | flags_q9_orbit5_150.txt (order-5 isometry orbits of X4 = -8 X0 over GF(9), card r4c6) | uhcheck all sources, apsp_cyc VALID |
| (12,7) | d12D7_n664900 | 664,900 | 664,300 (table) | H(9), j = 2, 300 | flags_q9_orbit5_150.txt | uhcheck all sources, apsp_cyc VALID |
| (13,7) | d13D7_n1063416 | 1,063,416 | 1,062,936 (table) | H(11), j = 1, 240 | flags_q11_orbit4_240.txt | uhcheck all sources |
| (15,7) | d15D7_n2481624 | 2,481,624 | 2,480,184 (table) | H(11), j = 3, 720 | flags_q11_orbit4_240.txt | uhcheck all sources |
| (16,7) | d16D7_n4023516 | 4,023,516 | 4,022,340 (table) | H(13), j = 2, 588 | flags_q13_phase294.txt (order-7 phase classes, C = 11) | uhcheck: see d16D7_n4023516_uhcheck.txt |

Superseded files kept for the record: d9D7_n117816 (84 spread flags), d10D7_n224798 (52 units, random scan),
d11D7_n398856 and d12D7_n664852 (138 GF(9) spread flags), d16D7_n4023348 (252 secant flags). All of them were checked the
same way when committed.
