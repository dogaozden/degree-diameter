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
THREADS` and `NB=<2*P*m> ./apsp_cyc NAME.edges Delta 7 m THREADS`.

| cell | file | vertices | previous | base, j, units | flags | checks |
|---|---|---|---|---|---|---|
| (7,7) | d7D7_n23532 | 23,532 | 23,484 (master) | H(5) `gh_build 5`, j = 1, 48 units | flags_q5_spread48.txt (spread, c = 2) | uhcheck all sources, apsp_cyc VALID |
| (9,7) | d9D7_n117816 | 117,816 | 117,650 (master) | H(7) `gh_build 7`, j = 1, 84 units | flags_q7_spread84.txt (spread, c = 1) | uhcheck all sources, apsp_cyc VALID |
| (10,7) | d10D7_n224798 | 224,798 | 224,694 (table) | H(8): research/squads/d14D7-r2/c15/gh8.c (GF(8); output sha256 1703336b...f21c5), j = 1, 52 units (random scan) | — | uhcheck all sources (card c15), apsp_cyc VALID (Opus) |
