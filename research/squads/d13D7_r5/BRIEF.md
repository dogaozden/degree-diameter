# Squad round 5 (job cell-13-7): orbit unions at q = 8 and non-collinear sets of H(9)

Background: research/squads/d13D7_r4/BRIEF.md (read it) and the orbit-union code of rounds 3-4
(research/squads/d13D7_r3/c3/: orbl.py, wclq2.c, replay2.py; ports to other q in research/squads/d13D7_r4/c2, c3).
Rules as in round 4: one heavy process at a time, single thread, `timeout 900 nice -n 10`, <= 600 s CPU per run,
<= 1.5 GB, no git, write only in research/squads/d13D7_r5/<card>/, best set as <card>/best_idx.txt, one JSON line in
research/squads/d13D7_r5/scoreboard.jsonl, reply in <= 5 lines, time box about 30 minutes.

c1 (q = 8, cell (10,7), +2 vertices per point): pairwise-opposite points of H(8) (research/d13D7/hex/hex_q8.bin, 37,449
points; current best 84 from local search, research/d13D7/q8/R84_q8_idx.txt; bound 513). GF(8) arithmetic as in
research/d13D7/hexgen2.c: element = bit vector b0 + 2 b1 + 4 b2 of a polynomial, addition = XOR, multiplication mod
x^3+x+1. Opposite iff B(x,y) != 0 with the CHARACTERISTIC-2 polar form B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2 (no x3
term); Q(x) = x0x4 + x1x5 + x2x6 + x3^2. Isometries: products of orthogonal transvections t_v(x) = x + (B(x,v)/Q(v)) v
for Q(v) != 0 (they preserve Q in characteristic 2). Scorer: `research/d13D7/tools/oppcheck research/d13D7/hex/hex_q8.bin
P FILE` (pure BFS; ignore its "criterion" line).

c2 (q = 9, cell (11,7), +2 vertices per point): large sets of pairwise NON-COLLINEAR points of H(9) (no two on a common
line of research/d13D7/hex/hex_q9.bin; 66,430 points; bound 6,643; current best 3,859 from local search,
research/d13D7/q9/R3859_noncollinear_idx.txt). Group: collineations of H(9) we have explicitly: alpha = delta^2 where
delta is the explicit duality (research/d13D7/q9/dual_pt2line.txt: point -> line, dual_line2pt.txt: line -> point;
alpha(p) = line2pt[pt2line[p]] is a permutation of the points preserving collinearity), and the Frobenius map phi
(apply x -> x^3 to every coordinate; F_9 = F_3[al], al^2 = 2, element a + 3b, so x^3 of a + b al is a - b al; points
from hexlib.load). Compute the orders of alpha and phi, orbits of <alpha>, <alpha^k>, <alpha, phi>, keep orbits with no
two collinear points, build the orbit compatibility graph (no collinear pair across), max-weight independent set /
clique (wclq2.c), then greedy fill with single points and the local search research/d13D7/tools/ncol_ils.c (it accepts
no seed file; copy and add one if useful). Scorer (write it yourself, it is simple): no line of H(9) contains two points
of the set (lines = rows of the line table in hex_q9.bin).
