# (10,5) ≥ 4,804: the 4,800 doubled-matching lift of W(7) with one freed point–line pair and 4 hubs

Base: the 4,800 graph (research/d10D7/DM_D5.md, research/d10D7/checks/d10D5_n4800_CHECK.md): Z6-lift of the incidence
graph of W(7) plus a bijection sigma (point -> line) doubled with voltages 1 and 4, flag voltages in {0, 3}.
Freed point p = 0: its 12 lift edges (p,h)-(sigma(p),h+1), (p,h)-(sigma(p),h+4) are deleted; two hubs are joined to
the fibre (p,0..5) and two to the fibre (sigma(p),0..5). sigma and nu were re-annealed (dmhub.c) so that the result
has diameter 5. 4,804 vertices, 24,012 edges, max degree 10 (hubs have degree 6).

Files: `graphs/d10D5_n4804_gqdm_hub1.sol` (dmhub format: header, freed points, sigma, mv0, mv1, flag voltages in
gqgen line order), `graphs/d10D5_n4804_gqdm_hub1.edges.gz` (edge list, first line n).

Rebuild and check (from research/squads/d10D5/hubs):
    gcc -O2 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7          # writes gq/gq_q7.bin
    python3 build_hub.py gq/gq_q7.bin graphs/d10D5_n4804_gqdm_hub1.sol x.edges     # independent of dmhub.c
    gcc -O3 -o apsp ../../../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5

Result (2026-10-25, cloud session): `n=4804 edges=24012 degree min=6 max=10 bipartite=yes diameter=5`,
`RESULT VALID d=10 D=5 n=4804`; with D=4 `RESULT INVALID` (diameter exactly 5).
sha256 of the edge list (build_hub.py and dmhub.c write the same file):
40c569d1135ec296b27bb67f2405268ba3bb4b60d4a3d2d0ec44bed818e65517
