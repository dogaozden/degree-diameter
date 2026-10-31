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

## c9 (small, replaces c8 at 16:25): re-lift quotients of the record graph
The 684 table graph is a Haar graph H(G, S) with G = C6 x (C19:C3) (order 342). For every normal subgroup N of G
(orders 2, 3, 6, 19, 57, 114, ...), the quotient is a base multigraph on 2|G/N| vertices with voltages in N, and the
684 graph is its lift by N. Keep the base (it has the record's local structure) and lift it instead by OTHER groups M
of slightly larger order (|M| > |N|, vertex count 2|G/N||M| in 686..800): for example base 6+6 (N of order 57) lifted
by every group of order 58..66; base 18+18 (N = C19) by groups of order 20, 21, 22; base 2+2 or 3+3 likewise. Do the
same with the base of the 704-vertex near miss (shared/near704_c11q16.edges: a 2+2 lift by SmallGroup(176,17)).
Steps: find S (GAP: search 6-subsets of SmallGroup(342, i) for the diameter-5 Haar graph with mcos "1|1" or haarex3,
or ask GAP for the group and anneal), write the quotient base in vl format, calibrate (tabu on the base by N itself
must re-find cost 0), then run tabu over M. Base size limit: tabu.c MAXB 64.

# Round 2 (17:55-19:50 UTC). Round 1 results: c7 surgery 686: bad 177 (2-opt local minimum; 140 of 177 far pairs
# between old vertices, single-edge deletion of the 684 graph costs 44-83 pairs); c5 mcos 1|3,3,3 on C2 x (C61:C3) 732:
# bad 915 (cost 7); c1 2+2 lift C11:Q16 704: cost 4 (= prior, same 2 missed fibres every time); c4 2|2 at 756: cost 12;
# c2 3+3 lift 696: cost 14; c6 Haar + twist: no twist beats the Haar floor (360 at 720); c3 almost simple bi-coset:
# 4320+; c8 GH(5,5) quotients: 9520 at 686. Read any round-1 folder (c1..c9, NOTES.md) for code and lessons.

## c10 (small): augmented quotient bases (structured surgery)
Quotient the 684 graph H(G,S), G = SmallGroup(342,12) (c7/h684.edges, c5 has the S), by a normal subgroup N: a base
on 2(342/|N|) vertices with voltages in N whose lift by N is the 684 graph. ADD j new vertex pairs to the BASE (j = 1,
2), rewire a few base edges to give them degree 6, and lift by N again: n = 684 + 2j|N| (N = C19: 722; N = C6: 696;
N = C3: 690; N = C2: 688; N = C19:C3 or C57: 798). Every move is now N-equivariant, so the surgery keeps a symmetry and
the search is over a small base. Start voltages from the 684 graph, run shared/tabu (copy tabu.c and raise MAXB/MAXE
if the base is bigger than 64 vertices). Calibrate: the unaugmented base by N must give cost 0.

## c11 (small): 2+2 lifts with an imposed swap symmetry
c1 found that SmallGroup(176,17) and (176,40) 2+2 lifts (base [[2,4],[4,2]]) stall at cost 4 always missing the same
two fibres at A1 and B2 (the base's swap pair). Impose the base automorphism A1<->B2, A2<->B1 combined with a group
automorphism or anti-automorphism on the voltages (half the free voltages), and run tabu in that smaller space; do it
for all groups of order 176, then 180, 184, 186, 188, 190 (704-760 vertices). Also try other bases with a swap.

## c12 (large): mixed-orbit coset graphs with mcos, beyond 1|2,2
mcos needs equal reciprocal sums on the two sides. c5's best type 1|3,3,3 (732: cost 7). Types to try: 1|3,3,3 on
all groups of order 343..400 with elements of order 3 (not 384), 1|2,3,6, 1|4,4,2, 1|4,4,4,4, 1|6,6,6,6,6,6,
3,3,3|3,3,3, 2,2|2,2 variants. Screen by bad pairs (score65 on the exported edges), 60 s per combo, then long anneals
on the best 5. c5's notes: research/squads/handsoff-65/c5/NOTES.md.

## c13 (small): continue the surgery lead (c7)
Start from c7/best686_bad177.edges and c7's code. Things c7 did not try: iterated local search (kick with k random
2-switches, re-descend, accept if not worse); choosing the new vertices' neighbours by an exact covering search
(their 3-balls must cover the opposite side); symmetric insertion of 2 or 3 vertex pairs as an orbit of a subgroup
(688, 690); removing a vertex pair of the 684 graph and inserting 2 pairs elsewhere. Target bad 0 at 686.

## c14 (small): re-coordinatise near misses as lifts with bigger bases
The 704 lift by C11:Q16 (c1/best704.edges, 2+2 base) is a 2-opt local minimum. Write it as a lift of a 4+4 base by an
index-2 subgroup (order 88), an 8+8 base by an index-4 subgroup (44), or 22+22 by an order-16 subgroup
(shared/haar2liftN.py, normlift.py show how for Haar graphs); the bigger base gives more voltage freedom near the
same graph. Run tabu/kdesc from that start. Same for c5's 732 graph and the 720 Haar near miss of SmallGroup(360,53).

## c15 (large): bi-coset |H| = |K| = 2 on the rest of orders 722..766
c4 swept 206 of 705 even-order groups (diagonal class pairs, dcenum SA 6 s per pair): best 12 at SmallGroup(756,74).
Sweep the remaining groups (c4/results.txt says which are done), then rerun the best 10 with long anneals. Use
c4's scripts (c4/NOTES.md).

## c16 (wildcard): a family nobody tried
Tried so far (this job and before): Haar graphs (closed 686-800 except 768), 2+2/3+3/4+4.. lifts, bi-coset |H|=2,3
and almost simple, multi-orbit mcos types, bi-Cayley, tri-Cayley, Haar + twist, surgery on the 684 graph, GH(5,5) and
GQ(5,5) pieces, quotient re-lifts (c9). Find a different construction you think can reach 686+ with diameter 5,
argue it in NOTES.md, implement it, score it.

## c17 (large, added 18:20): tabu search for coset graphs
mcos is an annealer; on lifts, tabu beat annealing (cost 4 vs 8 at 704). Write a tabu search for mcos-type coset
graphs (copy shared/mcos.c into your folder: same cost function, but each step scans all single changes of one double
coset and takes the best non-tabu move, with aspiration and restarts as in shared/tabu.c). Calibrate on "1|1" with
SmallGroup(342,12) (the 684 graph). Then run it on the best (type, group) pairs of c5 and c12: first
1|3,3,3 on SmallGroup(366,2) (c5: cost 7, 732 vertices), then c5/scan and c12 tables for the next ones.

## c18 (large, added 18:20): Haar graphs with hub orbits, types "1,k|1,k"
A Haar graph of degree 5 leaves one free degree at every vertex; hubs fill it. In mcos terms: each side is a regular
orbit plus an orbit G/H with |H| = k, type "1,k|1,k": a regular vertex has 5 edges to the other regular orbit and 1
into the other side's hub orbit; a hub has k... (mcos's degree rule: a double coset between orbits a and b adds
|H_a| to every a-vertex and |H_b| to every b-vertex). n = 2|G|(1 + 1/k): "1,6|1,6" needs |G| >= 294 (n 686..);
"1,3|1,3": |G| >= 258; "1,2|1,2": |G| >= 229; "1,4|1,4": |G| >= 275. Also "1,1|2,2,2,2" (n = 4|G|, |G| >= 172) and
other mixes with regular orbits on both sides. Check mcos accepts the type, calibrate with "1|1" on SmallGroup(342,12),
then screen groups (non-abelian first, elements of order k needed) at 30-60 s per (type, group), deep runs on the best.

## c19 (large, added 18:20): close the Haar graphs on 802-840 vertices
Haar graphs H(G,S), |S| = 6, are closed for 686-800 vertices except 768 (another job does 768). Extend the closure to
orders 401..420 (802..840 vertices; abelian groups are out by the counting bound 542, generalized dihedral by 524):
for every non-abelian group, run shared/haarex3 exhaustively (read its header and branch claude/squad-6-5-rounds-ts5nxk
research/s65/haar/STATUS.md for how it was run: `git show origin/claude/squad-6-5-rounds-ts5nxk:research/s65/haar/STATUS.md`).
Groups with few involutions first. Keep a per-group log (VALID / side-A covers / closed) in c19/STATUS.md. Any VALID
set is a record: export the Haar graph and run apsp_ref.
