# (10,5) ≥ 4,842: DM lift of W(7), 9 freed flags, three of them with their flag edges deleted (FLAGDEL), 42 hubs

Same construction as d10D5_n4840_CHECK.md with a third converted flag: flags 41:289 (index 1), 398:292 (index 6) and
283:130 (index 5) have their own flag edges deleted and 3 hubs per side; the other 6 freed flags (266:64 225:350
65:202 263:330 253:247 19:139) keep 2 hubs per side. 4,800 + 9·4 + 3·2 = 4,842 vertices, 24,209 edges, bipartite,
max degree 10 (min 9: some hubs keep spare slots).

How it was found (cloud session session_01ThanGg64Z6Jg1KgXK34ssq, Oct 26; tools in research/squads/d10D5/r4/):
fresh.sh from the valid 4,840 state with the corrected coverage model (a converted flag's own deleted edge carries no
coverage route) and hub routes in the coset-0 models: coverage + D1 by dmhub2_f (fdrun.sh), coset-0 by three
dmfast_fd3 passes 134 -> 14 -> 7 -> 5, then lns3.py (exact CP-SAT with sigma and nu variable, FOCUS mode with uphill
moves) 5 -> 3 -> 2, lns2.py 2 -> 1, and tabu.sh (cumulative hard-pair walk: each time one bad pair is left it is
held good as a hard constraint and the exact search re-descends) 1 -> 0 in two rounds.

Files: `graphs/d10D5_n4842_flagdel3.sol` (dmhub format, H = 3 hub numbering, last line "fdset 1 6 5"),
`graphs/d10D5_n4842_flagdel3.edges.gz` (build_fd.py), `graphs/d10D5_n4842_flagdel3.lift2.sol` (sigma, nu).

Rebuild and check (from research/squads/d10D5/r4; build_fd.py is independent of dmhub2.c):

    gcc -O2 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7
    python3 build_fd.py gq/gq_q7.bin ../hubs/graphs/d10D5_n4842_flagdel3.sol "1 6 5" x.edges
    gcc -O3 -o apsp ../../../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5

Result (2026-10-26): `n=4842 edges=24209 degree min=9 max=10 bipartite=yes diameter=5`,
`RESULT VALID d=10 D=5 n=4842`; with D=4 `RESULT INVALID` (diameter exactly 5). The exact dmhub2_f cost (FLAGDEL=1
FDSET="1 6 5") is also 0, and a separate Python BFS (r4/failpairs.py, sources (x,0) and all hubs) finds no pair at
distance > 5. sha256 of the edge list written by build_fd.py:
b772d709adc9bcbec299b7c185a0911e6362d568ba893d63a039ae0f1ba87b9b
