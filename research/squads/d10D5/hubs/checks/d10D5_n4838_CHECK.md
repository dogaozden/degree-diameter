# (10,5) ≥ 4,838: DM lift of W(7), 9 freed flags, one of them with its flag edge deleted (FLAGDEL), 38 hubs

Construction: the 4,836 graph of d10D5_n4836_CHECK.md (Z6 doubled-matching lift of W(7), freed flags 266:64 41:289
225:350 65:202 263:330 283:130 398:292 253:247 19:139, two hubs per side per freed flag), with one change at the flag
41:289 (index 1 in the "free" line): its own flag edge 41-289 is deleted as well (the 6 lift edges (41,h)-(289,h+ν)),
so every vertex of the fibres of 41 and 289 has 3 spare degrees and that flag gets 3 hubs per side. The deleted edge is
rerouted through the flag's own hubs (each line-side hub of flag 1 is adjacent to a point-side hub of flag 1 and vice
versa). sigma and nu were re-optimised (coverage, the FLAGDEL "D1" condition and coset-0; research/squads/cells/d10D5.md,
section FLAGDEL). 4,838 vertices, 24,190 edges, 10-regular, bipartite.

Files: `graphs/d10D5_n4838_flagdel1.sol` (dmhub format with H = 3 hub numbering: hub index 3i+t; the third hub of
flags other than 1 does not exist; last line "fdset 1"), `graphs/d10D5_n4838_flagdel1.edges.gz` (written by
build_fd.py).

Rebuild and check (from research/squads/d10D5/r4; build_fd.py is independent of dmhub2.c):

    gcc -O2 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7
    python3 build_fd.py gq/gq_q7.bin ../hubs/graphs/d10D5_n4838_flagdel1.sol "1" x.edges
    gcc -O3 -o apsp ../../../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5

Result (2026-10-25, cloud session session_01QqmMPMEBdPHeTrrfhst9b1): `n=4838 edges=24190 degree min=10 max=10
bipartite=yes diameter=5`, `RESULT VALID d=10 D=5 n=4838`; with D=4 `RESULT INVALID` (diameter exactly 5). The
exact cost of dmhub2_f (bit-parallel BFS from all sources (v,0) and the hubs, FLAGDEL=1 FDSET=1) is also 0.
sha256 of the edge list written by build_fd.py:
fd13e3e4c59b24b0d34827d549b78e29bf181c31532cfb34613b1e371693634a

How it was found: r4/mkhubF.py (hub graph) -> r4/fdrun.sh (coverage + D1, dmhub2_f) -> r4/dmfast_fd3 penalty mode
(coset-0 down to 2 opposite pairs) -> r4/lns2.py FLIPS=1 BESTFLIP=1 (flip the least damaging nu on a bad pair's
geodesic, then repair the newly unmixed pairs by exact CP-SAT on sigma; 2 -> 1 -> 0).
