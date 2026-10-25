# Round d12D7-r2 cards (8 Haiku cards)

Preamble: PREAMBLE.md (read it first). Scoreboard: scoreboard.jsonl. Folders: c1/ ... c8/.
Cards c1-c3 try to reach the cap (more hubs per side than 14,400). Cards c4-c6 test ways past the cap. c7 and c8 are
wildcards.

**c1 - order 14,600, Frobenius-type groups.** 14,600 = 2^3 * 5^2 * 73 = the cap exactly (730 cosets of an order-20
subgroup). Every group of this order has a normal Z73. Build several nonabelian ones as PGRP files (Python: elements as
tuples, left multiplication by 2-4 generators as permutations of 0..N-1, plus 40-80 subgroups of order 20, each with an
involution): for example (Z73 x Z5^2) x| Z8 with Z8 acting faithfully on both factors (r of order 8 mod 73, omega of
order 8 in GF(25)*), (Z73 x| Z8) x (Z5^2 x| Z8)-quotients, (Z73 x| Z4) x AGL(1,5) x Z..., etc. Order-20 subgroups: Z5 x| Z4
(AGL(1,5)-type) and their conjugates, especially conjugates by elements of Z73, so that the subgroups move the Z73
coordinate. Run `clhaarP G.pgrp 7 5 600 SEED OUT` for several seeds per group. Score: 14,600 if some run reaches cost 0
(then build the graph with x5gen3 and run srccheck; valid = SOURCES OK), else report the best cost and the group.

**c2 - order 14,520 = 2^3*3*5*11^2.** SL(2,11) x Z11 stalls at cost 88 (its order-20 subgroups never move Z11). Try groups
whose order-20 subgroups do move every coordinate, for example the affine group Z11^2 x| SL(2,5) (SL(2,5) inside SL(2,11)
acting on GF(11)^2; order 121*120 = 14,520; order-20 subgroups = dicyclic Q20 inside SL(2,5) and their conjugates by
translations), Z11^2 x| (other groups of order 120 in GL(2,11)), PSL(2,11) x Z22, and anything else of this order you
can build. Same scorer as c1, score 14,520.

**c3 - other orders between 14,401 and 14,600 divisible by 20.** Candidates: 14,440 = 19^2 * 40 (e.g. the Frobenius group
GF(361) x| <w>, w of order 40 in GF(361)*; order-20 subgroups <w^2> and conjugates by translations), 14,420, 14,460,
14,480, 14,500, 14,540, 14,560, 14,580. First list which orders have nonabelian groups with order-20 subgroups that are
not inside a direct factor, then build and run clhaarP as in c1. Score: the largest |Gamma| with cost 0 (valid after
x5gen3 + srccheck).

**c4 - freeing beyond the spread: measure and look for zero-damage edges.** Opus measured: freeing one extra point
(point 0) on top of the 7,300 spread points breaks 82,720 ordered main-main pairs (the new point misses 1,620 targets,
1,981 other sources miss 2-144 each). Test finer moves with orbcat (no hubs; build with mksol.py + x5gen2.c from
research/d10D7/dual/, or write your own variant): (a) free only the shift-1 edges of one extra point; (b) free single
matching edges (one point, one level, one shift) — note this breaks the level symmetry, so use srccheck from the
affected vertices or write a small BFS; (c) choose the extra point to minimize damage (points near / far from the
spread). Score: the number of extra freed matching edges (beyond 73,000) with 0 broken main-main pairs (valid = the
check you ran shows 0). If none, report the smallest damage per extra freed edge and where it comes from.

**c5 - hubs with only 4 main edges.** A hub with owners at 4 levels (skipping level j) leaves 5 main slots of capacity
for 4 hubs, so up to 18,250 hubs per side (about 700,800 vertices) if it worked. It must reach every line of level j
within 6 through its hub-graph neighbours' owners or through cross-level main routes. Experiment: build the 693,100 graph
(x5gen3 with research/frontier/sols/d12D7_hex9_spread730_clhaarPSL9x40_n693100.hubs3), delete ONE owner edge of one
hub (write a filter on the edge list), and run srccheck from that hub only (a = hub id, b = a+1) to count its misses.
Then try to reduce them by changing that hub's hub-graph neighbours (keep degrees <= 12). Score: the smallest number of
misses for a hub with 4 main edges (0 = the idea is alive).

**c6 - non-Haar hub graphs that fill all 14,600 slots.** Any construction is fine as long as each hub has one owner per
level, at most 2 hubs per freed vertex, hub degree <= 12, and all same-side hubs end up within 6. Ideas: a voltage lift
of a small base graph over the 730 spread lines; a Haar graph on 14,400 plus 200 extra hubs per side wired by local
search; random hub graphs + repair. Write the layout in the .hubs3 format (see x5gen3.c), build with x5gen3, check with
srccheck. Score: hubs per side with SOURCES OK (more than 14,400 beats the current record).

**c7 - wildcard: a different construction.** Find an approach to (12,7) that none of the other cards uses and that is not
"5 levels of H(9) + hubs" (the other cards: c1-c3 bigger groups for the hub graph, c4 more freed edges, c5 hubs with 4
main edges, c6 non-Haar hub graphs, c8 small-q test bed). Test it at a size you can check (apsp on small analogues:
research/lifts/coordinator_check/apsp.c). Score: whatever measures your idea best; say what it would give at (12,7).

**c8 - wildcard: the small-q test bed.** Build the same construction at q = 3 (H(3) is self-dual: 364 points; Delta =
q + 3 = 6; 5 levels give 3,640 vertices; spread of H(3) = 28 lines, 112 points; cap 3,640 + 4*112 = 4,088). Use it to
try, exhaustively or by search, anything that might get past the cap: extra freed points with repairs, hubs with 4 main
edges, deleted vertices, extra vertices of other kinds. At this size apsp takes seconds. You will need your own H(3)
and duality (hexgen2.c handles q = 3; a duality of H(3) can be found by a small search, see research/d10D7/dual/dualfind.c).
Score: the largest valid (6,7) graph you get from this family at q = 3, with apsp VALID (the cap is 4,088; anything
above it means a way past the cap).
