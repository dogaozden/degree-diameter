# (12,5) ≥ 9,852: doubled-matching Z6 lift of W(9) plus one point-line pair

Graph: Z6-lift of a 10-regular bipartite base B (821 points, 821 lines) plus a perfect matching sigma (point -> line)
whose edges are doubled with voltages 1 and 4; base flag (p, l) has voltage 3*nu(p, l), nu in {0,1}. Lift vertex
(x, h) = 6x + h (x < 821 points, 821 <= x < 1642 lines). 12-regular, bipartite, 12 * 821 = 9,852 vertices.
Previous best: 9,840 (W(9) itself, research/d10D7/DM_D5.md); table (DS14v2): 8,200.

Base: W(9) in the numbering of research/d10D7/gqgen.c (gq/gq_q9.bin) with one 9-flag incident switch and nothing else:
the new point 820 (x*) replaces one point on each of the old lines 99, 109, 142, 154, 212, 219, 457, 466, 655 and lies
on the new line 820 (l*), whose points are the 9 removed points 123, 139, 283, 308, 412, 577, 746, 776, 798 and x*.
sigma: the sigma of the 9,840 record, changed by annealing.
Found by (job resume3-cell-11-5, side result of the (11,5) work): research/d11D5/inc/pipeline.sh: addpair.py (switch),
po7 annealing (2,924 -> 32 -> 16), wpo clause weighting (16 -> 0), nujoint TARGET=1 from the 9,840 nu (113 -> 0).

Files (this folder): d12D5_n9852_dmplus1.in (base and sigma, plusopt format), .nu (one bit per flag, flag id =
line*10 + slot), .volt (all Z6 voltages: flags, then the two copies of each matching edge), .edges.gz (edge list, first
line n).

Rebuild and check (from research/d11D5/inc):
    gcc -O3 -march=native -o /tmp/z6 z6lift.c -lm
    gcc -O3 -o /tmp/apsp ../../lifts/coordinator_check/apsp.c
    ./finish.sh ../graphs/d12D5_n9852_dmplus1.in ../graphs/d12D5_n9852_dmplus1.nu /tmp/x 12 5

Results (2026-10-25, cloud session session_018TRrddhVEdN311drmbPpBK):
- z6lift (exact, fibre-transitive BFS on the lift): lift vertices 9852, cost 0.
- apsp.c (all pairs, no symmetry): n=9852 edges=59112 degree min=12 max=12 bipartite=yes diameter=5,
  RESULT VALID d=12 D=5 n=9852; with D=4: RESULT INVALID (diameter exactly 5).
- simple graph: 59,112 distinct edges, no loops, no repeated edges.
- sha256 of the uncompressed edge list: 403909c2f451e6be12dbdcaca0a3821934532775e7bc85677d6dac4cb6f3ff64
