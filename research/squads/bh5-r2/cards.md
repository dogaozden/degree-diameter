# bh5-r2 cards (read COMMON.md first)

c1 (5,5) bi-coset, h = 2, |G| divisible by 4, |G| in 356..400 except 384 (vertices = |G|). All conjugacy classes of
   subgroups H, K of order 2 (H = K and H != K). Enumerate S (unions of double cosets HgK, degree exactly 5 on both
   sides; check the K side degree too when H != K) EXHAUSTIVELY when feasible. Start from bh5-r1/c8/bicoset.c.
   Report the best cost per order; a cost-0 graph is a candidate record (save edges, run apsp).
c2 (5,5) long annealing on the round-1 near misses: b=4 (2+2) bases [[a,5-a],[5-a,a]] a=1,2 over all 10 groups of
   order 90 (SmallGroup(90,5) gave cost 6 in 40 s), and over the groups of order 92, 93, 94 (b=4: 368..376); b=6
   (3+3) over all 13 groups of order 60 with the record base [[2,1,2],[1,2,2],[2,2,1]] and with other 3+3 5-regular
   bases (rows/columns summing to 5). vl (non-INC is fastest for b <= 6), SWAP=0.03, many seeds, 120-300 s runs on
   the 3-4 best (group, base) pairs after a short screen.
c3 (7,5) bi-coset, h = 2, |G| divisible by 4 in 1156..1200 (skip orders with more than about 200 groups; 1152 is
   not above the record). Degree 7 from double cosets of size 1 and 2. The number of double cosets is about |G|/4,
   so anneal the choice of S (swap one double coset for another of the same size) on the cost (unreached vertices
   from the two base cosets). Also h = 3 (|G| = 1.5 N, N > 1152) if time allows.
c4 (7,5) mixed route-chart lift. Read research/theorems/chartlift/graphs/build_d8D5_n2048.py (the (8,5) record:
   controller K44 voltage-lifted by a group of order 16, fibre F_2^4, each controller edge of colour c gives the q=2
   fibre edges u -> A_c u + lam b_c, lam in F_2; degree 4 x 2 = 8). Degree 7 needs mixed colours: 3 "chart" colours
   (lam in F_2, 2 edges each) + 1 "plain" colour (one edge u -> A u + b0). Build such graphs for fibre F_2^3 or F_2^4
   with controllers of 37..80 vertices per side (order 2 x C x 2^n > 1152), e.g. controller = K44 (or another
   4-regular 4-edge-coloured base) lifted by a group of order g. The whole graph is a regular voltage lift (by the
   controller group) of the base (controller base x fibre), so write that base as a vl base file and anneal the
   controller voltages with vl INC=1 (the lifted edges of one controller edge may share or not share a voltage; try
   both), also try random A_c, b_c. Report the best cost and order.
c5 (7,5) and (5,5) wildcard: find an approach none of the other cards (above, and round 1: random small-base lifts,
   GQ lifts, surgery on records, bi-coset graphs, route charts) uses. One idea, coded and scored. Examples of
   directions (pick one or your own): lifts over a base with a vertex of a different degree (non-regular), graphs
   from a (5,6) or (7,6) structure with one level removed, Cayley-sum graphs, lifts of K_{d,d} minus a perfect
   matching with extra structure, permutation-voltage (non-regular) lifts by a transitive permutation group.
c6 (5,5) wildcard: a second, different new idea for (5,5) only (target 356+). Same rules as c5; do not repeat c5's
   idea (you do not know it, so pick something unusual), and do not use the families of c1-c4 or round 1.
