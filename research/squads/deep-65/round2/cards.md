# deep-65 round 2 cards (3 Haikus, 03:28-04:28 UTC). Common rules: as in ../round1/cards.md (single-threaded, every
# command under 110 s via `timeout 105 nice -n 10`, chain runs, never background or sleep, own folder only, no git,
# NOTES.md, append JSON lines to research/squads/deep-65/round2/scoreboard.jsonl, final reply at most 5 lines).

## h5: go deep on "1,1,3|1,1,3" (two regular orbits + C3 hubs, n = 14m/3, m = 147 gives 686)
Round 1 (round1/h3, tabu3.c, NOTES.md there) found bad 294 at 686 on SmallGroup(147,3) (a = 4), a graph with
automorphism group of order exactly 147, not isomorphic to the other bad-294 graph (the 1,6|1,6 graph on
SmallGroup(294,11), which also lies in this family over SmallGroup(147,5)). Opus checked: as C7xC7 lifts both have no
diameter-5 graph within 2 voltage changes. Task: (1) exact 2-change neighbourhood of the bad-294 state in tabu3's own
parameter space (every pair of parameter changes; report the histogram of costs); (2) tabu restarts from it with
larger kicks (3-6 random changes) and different tenures; (3) more seeds (10+) of tabu3 at a = 4 and a = 3 on
SmallGroup(147,3), (147,4), (147,5), (147,1); report the best cost per group and whether several seeds hit the same floor.

## h6: wider sweeps of the hub family with hubtabu (round1/h4/hubtabu.c and NOTES.md there)
Family "Haar degree 5 + hubs of size k + hub graph of degree 6-k" (tools/hubk.c), n = 2m(1 + 1/k). Round 1:
k = 4 on SmallGroup(280,35) cost 3 (n = 700); k = 2 best 7 (234_1). Opus runs exact searches on 276 and 280_34/35.
Task: hubtabu screens (5-10 s per group, then deep runs on the best 3 per order) on: k = 2, m = 236, 238, 240
(n = 708-720; 240 has 208 groups: screen only nonabelian ones with a non-normal subgroup of order 2 if you need to cut);
k = 4, m = 284, 288 (n = 710, 720); k = 3, m = 261, 264, 267, 270 (n = 696-720). Report the best cost per (k, m).

## h7: does a non-abelian voltage group help? Lifts of 14-vertex hub bases by groups of order 50 (n = 700)
Opus's reading of the 294_11 near miss: the two missing elements always lie in the abelian normal C7 x C7, in the
zero-weight (closed-walk) part, where commutativity makes walks collide; the 684 record has a non-abelian core
(C19:C3 under a C6 quotient). Test it: take the 14-vertex bases of shared/lift_294_11_cost12.vl and
shared/lift_147_3_cost12.vl (ignore their voltages) and the crown graph K7,7 minus a perfect matching, and run
shared/tabu.c (INIT=random, several seeds, SECS <= 100) with every group of order 50 (D25, C5 x D5, (C5xC5):C2, C50,
C5 x C10; n = 700) and, as a control, C7 x C7 and C49 (n = 686). Report the best lift cost per (base, group) and
whether the non-abelian groups do better than the abelian ones. Lift cost is (base vertex, group element) pairs
uncovered; 0 means diameter 5 (then export the lift with the tool of your choice and run score65 and apsp).
