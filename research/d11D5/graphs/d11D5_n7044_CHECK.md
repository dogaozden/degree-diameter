# (11,5) ≥ 7,044: doubled-matching Z6 lift of W(8) plus two point-line pairs (K22 switch)

Graph: Z6-lift of a 9-regular bipartite base B (587 points, 587 lines) plus a perfect matching sigma (point -> line)
whose edges are doubled with voltages 1 and 4; base flag (p, l) has voltage 3*nu(p, l), nu in {0,1}. Lift vertex
(x, h) = 6x + h (x < 587 points, 587 <= x < 1174 lines). 11-regular, bipartite, 12 * 587 = 7,044 vertices.
Previous lab value: 7,032 (W(8) plus one pair, d11D5_n7032_CHECK.md, not yet recorded by the coordinator);
recorded record 7,020; table (DS14v2): 5,850.

Base: W(8) (point and line numbering of research/d11D5/w8.json) with one "K22 switch" (squad round r5, card c8):
two new points x* = 585 and y* = 586 and two new lines l* = 585 and m* = 586, with x* and y* both on l* and on m*.
x* replaces one point on each of the old lines 6, 54, 81, 95, 104, 119, 128 (these come from a hyperbolic line h1:
the lines delta(R), R in h1, minus two points); y* likewise on 13, 37, 176, 197, 295, 316, 371. The 14 removed points
go to l* = {248, 394, 250, 112, 323, 207, 349} + {x*, y*} and m* = {89, 225, 181, 313, 10, 359, 43} + {x*, y*}.
All other lines are those of W(8). The start had sigma = delta o C (delta the polarity of W(8), C a non-symplectic
collineation of PG(3,8) keeping the switch lines isotropic, research/d11D5/dc/README.md); the search moved sigma
away from it (it now agrees with the polarity on one point). sigma(x*) = 109, sigma(y*) = 288, sigma(353) = l*,
sigma(120) = m*.

How it was found (job resume4-cell-11-5, session_01YVUXzZUE2Fjy42D4zug9Gh, Oct 26):
1. start (research/squads/r5-d11D5/c8/k22.py, structural cost 414) -> po7 annealing T0 2 -> 0.15 (card c8): 18;
2. cold po7 annealing (T0 0.6 -> 0.08): 12;
3. wpo with LMAX 3000, DECAY 10 (longer local search, fast weight decay): 8, then 2 (one coset-0 demand pair: switch
   line 104 and line 532 through the moved point 250), then structural cost 0 (research/d11D5/dc/n587_k22_struct0.in);
4. nu stage: inc/nujoint.c TARGET=1 (T0 0.4 -> 0.05, PS 0.02, WS 50) from a random nu: 0 violated parity pairs in
   89 CPU s (seed 2; 67 sigma swaps).

Files (this folder): `d11D5_n7044_k22.in` (base and sigma, plusopt format: "n dg", n lines of point ids, n sigma
values), `d11D5_n7044_k22.nu` (one bit per flag, flag id = line*9 + slot), `d11D5_n7044_k22.volt` (all Z6
voltages: flags, then the two copies of each matching edge), `d11D5_n7044_k22.edges.gz` (edge list, first line n).

Rebuild and check (from research/d11D5/inc):
    gcc -O3 -march=native -o /tmp/z6 z6lift.c -lm
    gcc -O3 -o /tmp/apsp ../../lifts/coordinator_check/apsp.c
    ./finish.sh ../graphs/d11D5_n7044_k22.in ../graphs/d11D5_n7044_k22.nu /tmp/x 11 5

Results (2026-10-26, cloud session session_01YVUXzZUE2Fjy42D4zug9Gh):
- z6lift (exact, fibre-transitive BFS on the lift): `lift vertices 7044, cost 0`.
- apsp.c (all pairs, no symmetry): `n=7044 edges=38742 degree min=11 max=11 bipartite=yes diameter=5`,
  `RESULT VALID d=11 D=5 n=7044`; with D=4: `RESULT INVALID` (diameter exactly 5).
- independent numpy check (research/d11D5/dc/bitcheck.py: simple graph, regularity, 2-colouring, 64-source
  bit-parallel BFS from every vertex): `n=7044 edges=38742 degree=11 bipartite=yes sides=3522,3522 diameter=5`.
  Sanity: it gives 7 for the 14-cycle, 5 for the 7,032 graph, and 6 after any of 5 random edge 2-switches.
- simple graph: 38,742 distinct edges, no loops, no repeated edges.
- sha256 of the uncompressed edge list: 125fb687290ffacddf847e9b16a9b11863ad95b0cf2498b41edb6f1f6bd1569e
