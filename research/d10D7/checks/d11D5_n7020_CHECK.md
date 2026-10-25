# (11,5) ≥ 7,020: doubled-matching lift of the generalized quadrangle W(8)

Same construction as checks/d10D5_n4800_CHECK.md, over W(8) (585 points, 585 lines, 9-regular, diameter 4; GF(8)
from x^3+x+1): Z6-lift with one doubled matching (voltages 1 and 4) and flag voltages in {0,3}. 11-regular,
bipartite, 6·1,170 = 7,020 vertices. Lift vertex (x, h) = 6x + h.

Files: `graphs/d11D5_n7020_gqdm_q8.sol`, `graphs/d11D5_n7020_gqdm_q8.edges.gz`.
Rebuild: `./gqgen 8`, `python3 export_lift.py gq/gq_q8.bin graphs/d11D5_n7020_gqdm_q8.sol x.edges`, `./apsp x.edges 11 5`;
exact lift check: `BASE=gq/gq_q8.bin D=5 GROUP="cyc 6" J=2 DM=1 IN=graphs/d11D5_n7020_gqdm_q8.sol ITERS=0 ./lift2 8`.

Results (2026-10-24, cloud session):
- apsp.c: `n=7020 edges=38610 degree min=11 max=11 bipartite=yes diameter=5`, `RESULT VALID d=11 D=5 n=7020`;
  with D=4: `RESULT INVALID`.
- lift2: `vertices 7020 ... fullcost_final_state 0 DIAMETER_OK`.
- sha256 of the uncompressed edge list: 50cb13b81cae977ee1c5bac5ab180ec298048acde416f6ac3f4cdc65e128fa95
Table value (DS14v2): 5,850 = 5·|W(8)|. Found by dmfast (BASE=gq/gq_q8.bin NPOLY=4), joint annealing of nu and
sigma: seed 1 (600 s) to cost 1, then seed 2 (TEMP0 0.3, SWAPP 0.001) to cost 0.
