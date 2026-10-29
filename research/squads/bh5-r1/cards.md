# bh5-r1 cards (read COMMON.md first)

c1 (7,5) b=4 lifts. Base 2+2, 7-regular multigraph with multiplicity matrix [[a,7-a],[7-a,a]], a = 1, 2, 3. Groups of
   order 290..300 (lift 1160..1200), non-abelian first (GAP). One vl run per (a, group), SECS 60-120, several seeds;
   T0/T1 tuned to the cost scale. Report the lowest cost per order.
c2 (7,5) b=6 lifts. Bases 3+3, 7-regular multigraphs (rand_base.py 3 7 SEED OUT 3, several seeds, and K33 + 4 perfect
   matchings), vl with SWAP=0.05 so the base can change. Groups of order 194, 195, 196, 198, 200 (lift 1164..1200),
   non-abelian first.
c3 (7,5) b=8, 10, 12 lifts. rand_base.py with k = 4, 5, 6 (7-regular), vl SWAP=0.05. Groups: k=4 order 145..150
   (147, 148, 150 first), k=5 order 116..120 (120: SL(2,5), S5, 2xA5 ... first), k=6 order 97..100 (98, 100 first).
c4 (7,5) generalized quadrangles, INC=1. W(4) incidence + 2 matchings (plain, and DOUBLE) over Z7 (1190) and the 5
   groups of order 8 (1360); W(5) + 1 matching over Z4 and Z2xZ2 (1248); W(3) + 3 matchings over order 15 and 16
   (1200, 1280). Short runs first to see which family reaches the lowest cost, then spend the time on the best one.
c5 (5,5) small-base lifts (5-regular). b=4 (rand_base 2 5 or [[a,5-a],[5-a,a]]) over Z89 (356) and order 90 (360);
   b=6 over all 13 groups of order 60 (360), A5 = SmallGroup(60,5) included; b=8 over order 45/46; b=10 over 36;
   b=12 over 30; W(2)+2 matchings over order 12 (360). Calibration: the record 354 is a Z59-lift of the 3+3 base with
   multiplicities [[2,1,2],[1,2,2],[2,2,1]], and a 2-minute vl run does NOT re-find it (reaches cost 4-16), so expect
   to need many seeds and long runs; report best cost per (b, order).
c6 (5,5) surgery on graphs/rec354.edges and graphs/rec352.edges with ga (DELTA=5, D=5). grow.py K=1 (n=356) with
   random deletions reaches about 150 far pairs in 90 s. Make the deletion choice smart (delete the 5 edges whose loss
   creates the fewest far pairs, or edges on the most short cycles), try other T0/T1/FOCUS, and other surgeries
   (delete a vertex pair then add two pairs, add a single vertex 355 with 4 rewired edges, ...).
c7 (7,5) surgery on graphs/rec1152.edges (Haar, PGL(2,3)xZ24) and graphs/rec1140.edges with ga (DELTA=7, D=5):
   add one vertex pair (1154) or one vertex (1153); smart deletion choice as in c6; also try joining two copies of a
   smaller D=5 graph by rewiring.
c8 (wildcard) bi-coset graphs (GAP). A group G, subgroups H, K (core-free, |H| = |K| = h >= 2, small), vertices G/H
   and G/K, (Hx) ~ (Ky) when x y^-1 in a chosen union S of double cosets H g K; degree of every vertex = sum over chosen
   double cosets of |HgK|/|K| (must be <= Δ on both sides). G acts transitively on each side, so the diameter is the
   max of the eccentricities of the two base cosets (two BFS). Targets: Δ=5 with |G:H| in 178..200, Δ=7 with
   |G:H| in 578..650. Avoid orders with huge numbers of groups (2-power orders). Enumerate S exhaustively when the
   number of double cosets is small, else anneal. Write your own GAP/Python/C, check the best with apsp.
