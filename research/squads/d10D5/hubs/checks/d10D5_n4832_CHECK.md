# (10,5) ≥ 4,832: DM lift of W(7) with 8 freed flags (an orbit of an order-8 element), 32 hubs, 55 hub-hub edges

Same construction as d10D5_n4820_CHECK.md with 8 freed flags (p, l = sigma(p), p on l):
266:64 41:289 225:350 65:202 263:330 283:130 398:292 253:247 — one orbit of a semiregular element of order 8 of
PGSp(4,7) (squad round 1 card c5, research/squads/d10D5/r1/c5/), whose exact-coverage matching is perfect.
Coverage holes from collinear freed points / concurrent freed lines (37 targets) are patched by hub edges
(a line-side hub of flag i joined to a point-side hub of flag j reaches every point of l_j in 4 steps, all sheets);
13 such group edges are required and present. The coset-0 condition was annealed by dmfast_hub.c with targeted moves
(PTARG: flips on geodesics of bad pairs, and sigma swaps that make sigma(v), sigma(u) of a bad pair meet), keeping
the relaxed coverage (RELAX=1 PATCH=1). 4,832 vertices, 24,151 edges, max degree 10, hubs of degree 6..10.

Files: `graphs/d10D5_n4832_gqdm_flags8.sol` (dmhub format, includes the hub graph), `graphs/d10D5_n4832_gqdm_flags8.edges.gz`,
`graphs/d10D5_n4832_gqdm_flags8.lift2.sol` (sigma and nu in lift2 format, input of dmhub).

Rebuild and check (from research/squads/d10D5/hubs):
    gcc -O2 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7
    python3 build_hub.py gq/gq_q7.bin graphs/d10D5_n4832_gqdm_flags8.sol x.edges
    gcc -O3 -o apsp ../../../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5

Result (2026-10-25, cloud session): `n=4832 edges=24151 degree min=7 max=10 bipartite=yes diameter=5`,
`RESULT VALID d=10 D=5 n=4832`; with D=4 `RESULT INVALID` (diameter exactly 5).
sha256 of the edge list (build_hub.py and dmhub.c write the same file):
407137c5a7406fac0efee194f07a2c3ec858edc686627421c615a2270e8678dc
