# (10,5) ≥ 4,840: DM lift of W(7), 9 freed flags, two of them with their flag edges deleted (FLAGDEL), 40 hubs

Same construction as d10D5_n4838_CHECK.md with a second converted flag: flags 41:289 (index 1) and 398:292 (index 6)
have their own flag edges deleted and 3 hubs per side; the other 7 freed flags (266:64 225:350 65:202 263:330 283:130
253:247 19:139) keep 2 hubs per side. sigma and nu re-optimised from the valid 4,838 state (coverage and D1 by
dmhub2_f + exact CP-SAT, hub graph repaired by hubfix.py, coset-0 by dmfast_fd3 in three passes 128 -> 4, then
lns2.py best-flip 4 -> 3 -> 1 -> 0). 4,840 vertices, 24,197 edges, bipartite, max degree 10 (min 8: some hubs keep
spare slots).

Files: `graphs/d10D5_n4840_flagdel2.sol` (dmhub format, H = 3 hub numbering, last line "fdset 1 6"),
`graphs/d10D5_n4840_flagdel2.edges.gz` (build_fd.py), `graphs/d10D5_n4840_flagdel2.lift2.sol` (sigma, nu).

Rebuild and check (from research/squads/d10D5/r4; build_fd.py is independent of dmhub2.c):

    gcc -O2 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7
    python3 build_fd.py gq/gq_q7.bin ../hubs/graphs/d10D5_n4840_flagdel2.sol "1 6" x.edges
    gcc -O3 -o apsp ../../../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5

Result (2026-10-25, cloud session session_01QqmMPMEBdPHeTrrfhst9b1): `n=4840 edges=24197 degree min=8 max=10
bipartite=yes diameter=5`, `RESULT VALID d=10 D=5 n=4840`; with D=4 `RESULT INVALID` (diameter exactly 5). The
exact dmhub2_f cost (FLAGDEL=1 FDSET="1 6") is also 0. sha256 of the edge list written by build_fd.py:
98ae0ec26df3a81b3e866384dd16d17fb75bfede1af94d22cfc618f1f6e76e83
