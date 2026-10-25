# (11,5) ≥ 7,032: doubled-matching Z6 lift of W(8) plus one point-line pair

Graph: Z6-lift of a 9-regular bipartite base B (586 points, 586 lines) plus a perfect matching sigma (point -> line)
whose edges are doubled with voltages 1 and 4; base flag (p, l) has voltage 3*nu(p, l), nu in {0,1}. Lift vertex
(x, h) = 6x + h (x < 586 points, 586 <= x < 1172 lines). 11-regular, bipartite, 12 * 586 = 7,032 vertices.
Previous best: 7,020 (W(8) itself, research/d10D7/checks/d11D5_n7020_CHECK.md); table (DS14v2): 5,850.

Base: W(8) (gq_q8.bin numbering of research/d11D5/w8.json) with a 9-flag switch (point 585 = x* on 9 old lines,
line 585 = l* through their 9 removed points) and later flag swaps; sigma differs from the polarity on all but 7
points. Found by: r2 annealing (cost 2) -> squad r3 card c2's clause-weighting search wpo (structural cost 0) ->
inc/nujoint.c (nu by simulated annealing; SIGFIX sigma swaps; targeted-sigma annealing, TARGET=1).

Files (this folder): `d11D5_n7032_dmplus1.in` (base and sigma, plusopt format: "n dg", n lines of point ids, n sigma
values), `d11D5_n7032_dmplus1.nu` (one bit per flag, flag id = line*9 + slot), `d11D5_n7032_dmplus1.volt` (all Z6
voltages: flags, then the two copies of each matching edge), `d11D5_n7032_dmplus1.edges.gz` (edge list, first line n).

Rebuild and check (from research/d11D5/inc):
    gcc -O3 -march=native -o /tmp/z6 z6lift.c -lm
    gcc -O3 -o /tmp/apsp ../../lifts/coordinator_check/apsp.c
    ./finish.sh ../graphs/d11D5_n7032_dmplus1.in ../graphs/d11D5_n7032_dmplus1.nu /tmp/x 11 5

Results (2026-10-25, cloud session session_018TRrddhVEdN311drmbPpBK):
- z6lift (exact, fibre-transitive BFS on the lift): `lift vertices 7032, cost 0`.
- apsp.c (all pairs, no symmetry): `n=7032 edges=38676 degree min=11 max=11 bipartite=yes diameter=5`,
  `RESULT VALID d=11 D=5 n=7032`; with D=4: `RESULT INVALID` (diameter exactly 5).
- simple graph: 38,676 distinct edges, no loops, no repeated edges.
- sha256 of the uncompressed edge list: 4355f1459a14a841e5df28dc670014fca5a75d3f0370820d94165decdd0a2ba5
