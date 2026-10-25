# (10,5) ≥ 4,800: doubled-matching lift of the generalized quadrangle W(7)

Graph: Z6-lift of the incidence graph of W(7) (400 points, 400 lines, 8-regular, diameter 4) plus one perfect
matching sigma (point -> line) whose edges are doubled with voltages 1 and 4; flag voltages 3*nu, nu in {0,1}.
Lift vertex (x, h) = 6x + h (x < 400 points, 400 <= x < 800 lines). 10-regular, bipartite, 4,800 vertices.

Files: `graphs/d10D5_n4800_gqdm_q7.sol` (lift2 solution format: sigma twice, matching voltages, flag voltages),
`graphs/d10D5_n4800_gqdm_q7.edges.gz` (edge list for apsp.c, first line n).

Rebuild and check (from research/d10D7):
    gcc -O2 -o gqgen gqgen.c && mkdir -p gq && ./gqgen 7                  # W(7) -> gq/gq_q7.bin
    python3 export_lift.py gq/gq_q7.bin graphs/d10D5_n4800_gqdm_q7.sol x.edges
    gcc -O3 -o apsp ../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 5
    gcc -O3 -march=native -o lift2 lift2.c -lm
    BASE=gq/gq_q7.bin D=5 GROUP="cyc 6" J=2 DM=1 IN=graphs/d10D5_n4800_gqdm_q7.sol ITERS=0 ./lift2 7

Results (2026-10-24, cloud session, this branch):
- apsp.c (all pairs, no symmetry): `n=4800 edges=24000 degree min=10 max=10 bipartite=yes diameter=5`,
  `RESULT VALID d=10 D=5 n=4800`; with D=4: `RESULT INVALID` (diameter exactly 5).
- lift2 (exact, fibre-transitive): `vertices 4800 ... fullcost_final_state 0 DIAMETER_OK`.
- sha256 of the uncompressed edge list (as written by export_lift.py): 856a70311507138f93ca446bd2caa74ecbacfe87feef365bf85a4ba9049a5f89

Table value (DS14v2): 4,000 = 5·|W(7)| (polygon cover, Δ = q+3). This graph: 6·|W(7)|.
Found by dmfast (BASE=gq/gq_q7.bin NPOLY=4): joint annealing of nu and sigma, seed 4 (SWAPP=0.0005) then
continued with seed 5 (TEMP0 0.35, SWAPP 0.002) to cost 0.
