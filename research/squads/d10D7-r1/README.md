# Squad round d10D7-r1 (cell (10,7), Opus job "cell-10-7", 2026-10-24)

Shared testbed for every card: **lifts of GH(3) + 1 perfect matching by a group of order 4**, target diameter 7.
That is a bipartite graph with 2*364*4 = 2,912 vertices and max degree 5. The table's (10,7) graph is the same
shape with GH(8) and a group of order 3 (3 sheets); we need a 4th sheet. Random-like voltage assignments cannot
do it (log #assignments ~ 4.3k nats vs ~22k expected misses), so a cost-0 solution here is evidence of
*structure* that might scale to GH(8) (299,592 vertices at (10,7), table 224,694).

Tools (do not edit; copy into your card folder if you want to change code):
- `research/d10D7/lift2` (source lift2.c, header documents every env var), base files `research/d10D7/hex/hex_q{2,3,4,5,7,8}.bin`
- `research/d10D7/onefactor.py q j out seed m`: solution file whose matchings are 1-factors of the hexagon (doubled flags)
- Run lift2 from inside research/d10D7 (it reads hex/...), writing outputs to your own folder (absolute paths).

Scorer (exact): `cd /home/user/degree-diameter/research/d10D7 && GROUP="cyc 4" J=1 IN=<your.sol> ITERS=0 ./lift2 3`
(or GROUP="prod 2 2"). The RESULT line's `fullcost_final_state` is the score; 0 prints DIAMETER_OK.
