# (10,5) ≥ 4,836: DM lift of W(7) with 9 freed flags, 36 hubs, 59 hub-hub edges

Same construction as d10D5_n4832_CHECK.md with a 9th freed flag 19:139 (flags 266:64 41:289 225:350 65:202 263:330
283:130 398:292 253:247 19:139; sigma(p) for each freed p is the line after the colon). The exact-coverage matching
of these 9 flags is not perfect (395/400); coverage is "relaxed": every freed point reaches coset 1 of each opposite
point by some length-4 route, counting the hub routes (p_i,0) -> z_i -> z'_j -> (l_j, h) -> points of l_j, and dually
for freed lines. The hub graph was built FIRST (exact same-side hub distances <= 4 using hub edges and lift shortcuts)
and then annealed jointly with sigma (dmhub HGFIRST=1 HGDIST=1 HGFILL=1 PHUB=0.1); coset-0 by dmfast_hub (RELAX=1 with
HUBADJ = this hub graph's flag adjacency, PTARG targeted moves) and a short hot polish. 4,836 vertices, 24,167 edges.

Files: `graphs/d10D5_n4836_gqdm_flags9.sol` (dmhub format with the hub graph), `.edges.gz`, `.lift2.sol` (sigma, nu).

Rebuild and check (from research/squads/d10D5/hubs):
    gcc -O2 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7
    python3 build_hub.py gq/gq_q7.bin graphs/d10D5_n4836_gqdm_flags9.sol x.edges
    gcc -O3 -o apsp ../../../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5

Result (2026-10-25, cloud session): `n=4836 edges=24167 degree min=7 max=10 bipartite=yes diameter=5`,
`RESULT VALID d=10 D=5 n=4836`; with D=4 `RESULT INVALID` (diameter exactly 5).
sha256 of the edge list (build_hub.py and dmhub.c write the same file):
3b3883600cd8be3a0d3ac34668ef03a6e74ab94523fefefa4409ebb459f0f7f8
