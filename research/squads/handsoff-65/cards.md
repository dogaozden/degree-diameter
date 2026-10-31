# handsoff-65 direction cards (round 1)

Goal for every card: a bipartite graph with maximum degree 6 and diameter 5 on MORE than 684 vertices (686 or more;
the table value 684 is a Haar graph of C6 x (C19:C3), order 342). Bipartite Moore bound 1,562.
Scorer: `research/squads/handsoff-65/shared/check.sh EDGES` (bad = unordered vertex pairs at distance > 5; bad = 0 and
n > 684 is a record candidate). Tools and prior results: `shared/README.md`. Group tables: GAP (`gap -q`).
"small" / "large" marks whether the card works with small structures (small bases, few parameters, local edits) or
large ones (big groups, group theory, exhaustive families).

## c1 (small): 2+2 voltage lifts by all groups of order 172-180, tabu
Lifts of 6-regular bipartite base multigraphs on 2+2 vertices by groups G of order 172..180 (688-720 vertices), using
`shared/tabu` (and `vl` / `kdesc` to polish). The closest known graph above 684 is such a lift (SmallGroup(176,17) =
C11:Q16, base [[1,5],[5,1]], lift cost 4, `shared/near704_c11q16.edges`). Enumerate every base (edge multiplicities
between the 2+2 vertices with row and column sums 6, connected) and every group of each order (GAP gap_tables.g;
order 176 has 42 groups, 180 has 37, 172/174/175/178 have few), run tabu with many seeds, and spend long runs on the
best (group, base) pairs. Calibrate first: tabu must find cost 0 for a 2+2 base by a group of order 171 (684 = 4 x 171)
or another known solvable case.

## c2 (small): lifts with bigger bases (3+3 .. 8+8) by small groups, tabu
Base graphs on b+b vertices (b = 3..8, max degree 6, multi-edges allowed) lifted by groups of order m with 2bm in
686..720 (for example b = 4, m = 86..90; b = 6, m = 58..60; b = 8, m = 43..45; b = 3, m = 115..120). Groups: cyclic,
dihedral, metacyclic, all SmallGroups of those orders. Choose bases with many short cycles (4-cycles help cover fibres;
a lift of a girth-6 base cannot have diameter 5). Use `shared/tabu` (base size limit MAXB 64 in tabu.c) and random-restart
base switches. Prior: 3+3 lifts by tabu reached cost 14 at 696.

## c3 (large): bi-coset graphs of almost simple groups, |H|, |K| >= 4
Bi-coset graphs B(G;H,K): side A = G/H, side B = G/K, xH ~ yK iff x^-1 y in a union of double cosets HgK; degree 6
from the double-coset sizes. Take almost simple groups and small extensions where 2|G|/|H| is 686..800, e.g.
A7 with |H| = 7 (720 vertices), S7 with |H| = 14, PSL(2,19) (3420) with |H| = 9 (760), PSL(2,q) and PGL(2,q) for
q = 11, 13, 16, 17, 19, 23, 25, 27, products PSL(2,q) x C_k, PSL(3,3) (5616) with |H| = 16, PSU(3,3) (6048) with
|H| = 16, M11, and others you find (search GAP for groups G and subgroups H, K with |G|/|H| in 343..400). Use
`shared/bicoset.g` + `shared/bicoset` or `dc_export.g` + `dcenum` for exhaustive unions; anneal when there are too
many. The A3(2) chamber graph (630, PSL(4,2) with a Borel subgroup) is such a graph: rebuild it first as a calibration.

## c4 (large): bi-coset graphs |H| = |K| = 2 and 3 on groups of order 722..766 (and 1083..1149)
`shared/mcos` TYPE "2|2" (|G| vertices) for every group of order 722..766 except 768 (orders 686..720 are done: best 8
at SmallGroup(720,439)); skip pairs (H, K) that give Haar graphs (mcos/dcenum have SKIPHAAR). Then TYPE "3|3"
(2|G|/3 vertices) on groups of order 1029..1149 that were not done (only 1050/1053/1080 were tried). Many orders have
thousands of groups: rank groups by few involutions / small centre first, and record a per-order best.

## c5 (large): multi-orbit coset graphs ("1|2,2", "2,2|2,2", "1|3,3,3", "1,1|2,2", ...) with mcos
`shared/mcos` families where G acts with several orbits per side. Pick types and group orders so the vertex count is
686..760 (for "1|2,2": 2|G| with |G| 343..380; for "2,2|2,2": 2|G|; for "1,1|1,1" (a 2+2 lift): 4|G|; for
"1|3,3,3": 2|G|; for "3|1,1,1"-like mixes compute it). Calibration: "1|1" must re-find the 684 graph on SmallGroup of
order 342 (C6 x (C19:C3)) in about a minute. Prior best "1|2,2": 27. Try many types and groups; non-abelian groups of
order 343..380 with few involutions first.

## c6 (small): Haar graph plus a twisted matching
Graphs on G x {A, B} with 5 translation edges a_x ~ b_{x s_i} (i = 1..5) plus ONE twisted edge a_x ~ b_{phi(x) t},
where phi is an automorphism, an anti-automorphism (x -> x^-1, or x -> alpha(x)^-1) or another fixed permutation of G.
phi = identity gives the Haar graphs (calibration: re-find the 684 graph with phi = id on the order-342 group). The
graph is not vertex-transitive in general, so score with all-pairs BFS (score65 on the edge list, or your own
bit-parallel C). Groups of order 343..380 (non-abelian, few hundred); start with those where Haar searches came
closest (SmallGroup(360,53), (352,50), (372,1), (351,*), (342,*)). Write the annealer / tabu in C.

## c7 (large): surgery and local search on whole graphs
Start from the 684 table graph (rebuild it: Haar graph of the order-342 group C6 x (C19:C3), found by `mcos` "1|1"
or `haarex3`), and from near misses (`shared/near704_c11q16.edges`, bad 352). Moves that keep max degree <= 6:
edge 2-switches, deleting an edge pair and inserting a new vertex pair, splitting/merging vertices. Objective:
far pairs (incremental BFS in C). Targets 686, 688, 690, ... and 704 (fix the 352 bad pairs of the C11:Q16 lift).
Prior: vertex deletion + rewiring reached 1428 bad at 686, so make the moves smarter (keep the group structure where
possible: do surgery on every orbit at once, i.e. on the quotient / voltage graph, so the result is still a lift).

## c8 (wildcard, large): generalized-polygon pieces, or anything the others do not try
Other cards: c1 2+2 lifts; c2 big-base lifts; c3 almost simple bi-coset graphs; c4 |H|=2,3 bi-coset; c5 multi-orbit
coset graphs; c6 Haar + twisted matching; c7 surgery on whole graphs. Ideas for you: pieces of generalized polygons
(GQ(5,5) incidence graph: 312 vertices, diameter 4, degree 6; GH(5,5): 7,812, diameter 6; PG(2,5): 62, diameter 3)
glued, extended or rewired; level graphs; compound graphs (replace each vertex of a small graph by a copy of a
diameter-2/3 graph); Cayley graphs of groups that are not Haar (for example G with an index-2 subgroup and S in the
other coset); cyclic or dihedral lifts with partly fixed structure. Pick the idea you think most promising, then go
deep.
