# (12,5) ≥ 9,840: doubled-matching lift of the generalized quadrangle W(9)

Same construction as checks/d10D5_n4800_CHECK.md, over W(9) (820 points, 820 lines, 10-regular, diameter 4;
GF(9) from x^2+1): Z6-lift with one doubled matching (voltages 1 and 4) and flag voltages in {0,3}. 12-regular,
bipartite, 6·1,640 = 9,840 vertices. Lift vertex (x, h) = 6x + h.

Files: `graphs/d12D5_n9840_gqdm_q9.sol`, `graphs/d12D5_n9840_gqdm_q9.edges.gz`.
Rebuild: `./gqgen 9`, `python3 export_lift.py gq/gq_q9.bin graphs/d12D5_n9840_gqdm_q9.sol x.edges`, `./apsp x.edges 12 5`;
exact lift check: `BASE=gq/gq_q9.bin D=5 GROUP="cyc 6" J=2 DM=1 IN=graphs/d12D5_n9840_gqdm_q9.sol ITERS=0 ./lift2 9`.

Results (2026-10-24, cloud session):
- apsp.c: `n=9840 edges=59040 degree min=12 max=12 bipartite=yes diameter=5`, `RESULT VALID d=12 D=5 n=9840`;
  with D=4: `RESULT INVALID`.
- lift2: `vertices 9840 ... fullcost_final_state 0 DIAMETER_OK`.
- sha256 of the uncompressed edge list: cd26e09e93272fa53fe2c62d28b01e4e44f5d1cf35e496e07902f5bc3c5929c9
Table value (DS14v2): 8,200 = 5·|W(9)|; our previous record 8,748 (route-chart lift, master, Oct 24). Found by dmfast
(BASE=gq/gq_q9.bin NPOLY=4), one joint annealing run (seed 1, 900 s budget, SWAPP 0.0002) from random to cost 0.
