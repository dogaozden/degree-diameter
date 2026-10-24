# Solution files (cell (14,7) and related DGQ cells), type-2 units

## d14D7_n1771870: bipartite (14,7) on 1,771,870 vertices (table 1,771,560)

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
