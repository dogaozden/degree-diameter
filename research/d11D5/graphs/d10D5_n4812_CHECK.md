# (10,5) ≥ 4,812: doubled-matching Z6 lift of W(7) plus one point-line pair

Graph: Z6-lift of an 8-regular bipartite base B (401 points, 401 lines) plus a perfect matching sigma (point -> line)
whose edges are doubled with voltages 1 and 4; base flag (p, l) has voltage 3*nu(p, l), nu in {0,1}. Lift vertex
(x, h) = 6x + h (x < 401 points, 401 <= x < 802 lines). 10-regular, bipartite, 12 * 401 = 4,812 vertices.
Previous best: 4,800 (W(7) itself, research/d10D7/checks/d10D5_n4800_CHECK.md); table (DS14v2): 4,000.

Base: W(7) in the numbering of research/d10D7/gqgen.c (gq/gq_q7.bin) with one 7-flag incident switch and nothing else:
the new point 400 (x*) replaces one point on each of the old lines 72, 109, 123, 152, 183, 210, 274 and also lies on the
new line 400 (l*), whose points are the 7 removed points 21, 82, 250, 306, 324, 361, 395 and x*. sigma: the sigma of the
4,800 record, changed by annealing.
Found by (job resume3-cell-11-5, a side result of the (11,5) work): research/d11D5/inc/addpair.py (switch), po7
annealing (structural cost 1,266 -> 0, T0 20 -> 0.4), inc/nujoint.c TARGET=1 from the 4,800 nu (0 violated parity
pairs after 1.4 M moves); pipeline research/d11D5/inc/pipeline.sh.

Files (this folder): d10D5_n4812_dmplus1.in (base and sigma, plusopt format), .nu (one bit per flag, flag id = line*8 +
slot), .volt (all Z6 voltages: flags, then the two copies of each matching edge), .edges.gz (edge list, first line n).

Rebuild and check (from research/d11D5/inc):
    gcc -O3 -march=native -o /tmp/z6 z6lift.c -lm
    gcc -O3 -o /tmp/apsp ../../lifts/coordinator_check/apsp.c
    ./finish.sh ../graphs/d10D5_n4812_dmplus1.in ../graphs/d10D5_n4812_dmplus1.nu /tmp/x 10 5

Results (2026-10-25, cloud session session_018TRrddhVEdN311drmbPpBK):
- z6lift (exact, fibre-transitive BFS on the lift): lift vertices 4812, cost 0.
- apsp.c (all pairs, no symmetry): n=4812 edges=24060 degree min=10 max=10 bipartite=yes diameter=5,
  RESULT VALID d=10 D=5 n=4812; with D=4: RESULT INVALID (diameter exactly 5).
- simple graph: 24,060 distinct edges, no loops, no repeated edges.
- sha256 of the uncompressed edge list: 178bf2107be0ad38be5f68d26e57c524a7b32be0cebb74c6baf176278dcf3d1b
