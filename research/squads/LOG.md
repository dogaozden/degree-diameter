# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-30, job squad-6-5 (Opus cloud session, branch claude/squad-6-5-rounds-ts5nxk), goal: bipartite (6,5) > 684

Continued from claude/squad-6-5-bipartite-l3l6dn (bicay.c, scorer score65, exports; no round had been run). Scorer for
every card: research/s65/tools/score65 (unordered pairs at distance > 5); each card also reports its internal cost.

### Round s65r1 (06:55-07:27 UTC, 8 cards, research/squads/s65r1/)
Cards: c1 tri-Cayley (3-orbit, colour-mixing) graphs, |G| = 230-240 · c2 semi-exact 2+2 lifts (last voltage solved
by tallying), |G| = 176-192 · c3 3+3 lift screen, |G| = 116-120, all 17 base matrices · c4 exhaustive alpha-invariant
2+2 lifts (alpha in Aut(G) of order 3/4), |G| = 172-180 · c5 |H| = 2 bi-coset graphs, orders 686-702 · c6 bi-coset
graphs of non-solvable non-almost-simple groups (720 |H| = 2, 1080 |H| = 3) · c7 vertex deletion + rewiring of near
misses · c8 wildcard (two 344-vertex degree-5 lifts joined by annealed matchings).
Best per card (internal cost; score65 bad, all re-scored by the director, none valid): c1 10 at 690 (bad 1150) ·
c2 14 at 704 (1232; no gain over plain vl at equal time) · c3 28 at 696 (1624) · c4 38 at 720 (3420; 111 of 143
alpha-spaces exhaustive) · c5 6 at 702 (SmallGroup(702,47), H = K; 4 s anneals) · c6 8 at 720 (SmallGroup(720,411)
= C3 x (SL(2,5):C2); bad 1440) · c7 1428 bad at 686 · c8 1986 bad at 688.
Director's checks: exhaustive dcenum over all degree-6 unions of double cosets: 720_411 H = K (3,584,484 unions)
optimum 8; 720_415 optimum 14; 720_416 (1,1) optimum 12. Both best coset hits are Haar graphs in disguise: if an
index-2 subgroup N does not contain H (|H| = 2), N acts regularly on both sides, so B(G; H, H) is a Haar graph of N.
702_47 = (C3)^3:C26 gives Haar graphs of SmallGroup(351,12) and 720_411 Haar graphs of C3 x SL(2,5) = SmallGroup(360,51),
both already excluded exhaustively (fresh-6-5). Lesson: |H| = 2 sweeps must drop such H (dc2_lib.g SKIPHAAR).
Director's own line meanwhile: new annealer research/s65/tools/mcos.c for multi-orbit coset graphs (G regular on one
side and B = G/K1 u G/K2 with |K_i| = 2, etc.; re-finds the 684 Haar graph in 47 s and the cost-2 Haar wall of
SmallGroup(351,5) in 20 s); first short runs on orders 344-350 ("1|2,2", "2,2|2,2"): best 60-80, worse than the Haar
wall; bi-Cayley exhaustive campaign too slow under load (600 s per configuration, PARTIAL), paused.
Kept for round 2: non-Haar |H| = 2 bi-coset graphs (the family of the vertex-transitive (5,5) 384 graph) at orders
704-720, |H| = 3/4 coset graphs, and the unfinished exhaustive Haar search at orders 352-360 (69 low-involution
groups never run).

### Round s65r2 (07:37-08:05 UTC, 8 cards, research/squads/s65r2/)
Cards: c1/c2 non-Haar |H| = 2 bi-coset graphs (dc2_lib SKIPHAAR), order 704 (two halves of the 1387 groups) · c3 the
same at 706-718 and 720 (ids 1-450) · c4 non-Haar |H| = 3, orders 1035-1077 · c5 non-Haar |H| = 3, order 1080 · c6
non-Haar |H| = 4, orders 1372-1436 · c7 exhaustive Haar (haarex2), the 69 never-run low-involution groups of order
352-360 · c8 mcos multi-orbit families ("1|2,2", "1,1|2,2,2,2", ...) on orders 352-360 and 172-180.
Best per card (internal cost; none valid): c1, c2 48 (704) · c3 8 (SmallGroup(720,439) = Dic3 x (C15:C4), non-Haar;
25M director anneal steps also stay at 8) · c4 150 (only 1050/1053 have non-Haar |H| = 3 pairs) · c5 12 (3.A6 =
SmallGroup(1080,260); director's exhaustive check: optimum 12 over all 7,140 unions) · c6 none (orders 4p have only
Haar-type H; other exports timed out) · c7 closed 360_52, 54, 55, 56, 57 (no Haar graph; 360_55/56 have side-A covers,
side B >= 4 short) and ran 360_53 halfway (side-A covers with side B 2 short, bad 360) · c8 "1|2,2" plateaus at 27
where Haar graphs of the same groups reach 6.
Director: finished SmallGroup(360,53) exhaustively (pairs 57-1698 in research/s65/haar/h360_53/; 168M sets in all, no
Haar graph). Lift calibration (research/s65/calib/): annealing + exact 2-opt (kopt K=2) gives VALID (6,5) lifts on
640 vertices (order 160; apsp VALID, score65 bad 0; calibration only); 672 (order 168) is stuck at cost 6, a strict
2-opt local minimum (new tools/kdesc.c: exact steepest descent over all 1- and 2-changes). Self-dual Haar graphs
(phi(S) = S^-1 for an involutory automorphism phi, which makes side B automatic; tools/sdhaar.c) fail the positive
control: on the 684 record's own group no such S covers side A (best 7 missing, 51M sets), so the family was dropped.
Kept: exhaustive Haar at 352-360 (decisive, minutes per group) and the lift tools; non-Haar cosets dropped.

### Round s65r3 (08:01-08:38 UTC, 8 cards, research/squads/s65r3/)
Cards: c1-c4 exhaustive Haar (haarex2) on four interleaved quarters of the open low-involution groups of order 352-360
· c5 annealing + exact 2-opt pipeline at 704/720 (orders 176/180, three 2+2 bases) · c6 a better lift local search
(tabu over single-voltage changes with exact best-move selection) · c7 bi-Cayley annealing over the bc files of
orders 344-360 · c8 Haar annealing over the 260 never-run groups of order 352-360 with more than 3 involutions.
Best per card: c1-c4 closed 45 more groups (13 + 8 + 13 + 11), none valid and none with a side-A cover; best side-A
miss 1 (352_50), then 2 (352_55, 352_57, 360_76, 360_88, 360_89) · c5 lift cost 4 at 704 (C11:Q16 = SmallGroup(176,17),
base [[1,5],[5,1]]), no 2-opt fix · c6 TABU beats annealing: 672: 4 vs 8; 704 (C11 x Q16): 6 vs 12-14 (bad 528) ·
c7 cost 4 at 704 (SmallGroup(352,141), a = b = 3; bad 704), a quarter of the space covered · c8 best 4 (360_125,
360_136; 9 involutions), cost grows with the involution count.
Director: wrote haar2lift.py / bicay2lift.py / normlift.py (Haar and bi-Cayley graphs as 2+2 lifts by an index-2
subgroup; checked: same score65 as the original graphs) and ran exact 2-opt from the 12 side-A covers of 360_53
(lift cost 4 each, bad 360): no cost-0 neighbour in any of them; nor from the 704 bi-Cayley and tabu near misses.
Status of the exhaustive Haar campaign: research/s65/haar/STATUS.md (50 of 69 groups closed after this round).

### Round s65r4 (08:42-09:22 UTC, 8 cards, research/squads/s65r4/)
Cards: c1-c3 exhaustive Haar (haarex2) on the open groups of order 352-360 (resumes of partial runs, the 352 list, a
mixed list incl. 360_125/136) · c4 exhaustive Haar at orders 361-380 (low-involution groups, large |Aut| first) · c5
tabu from the 12 Haar near misses of 360_53 written as 2+2 lifts · c6 bi-Cayley annealing on untried bc files, then
tabu in the lift space · c7 tabu from random starts at 704/720, exact 2-opt on the finals · c8 tabu on 3+3 lifts.
Best per card: c1 closed 360_95 (minA 4) · c2 closed 352_56/64/84/100/139/154 (minA >= 7) · c3 closed 352_163, 354_1,
360_23/93/103/113/125/136; 360_125 and 360_136 (9 involutions) have side-A covers, side B >= 4 short · c4 closed 31
groups of order 363-380 (726-760 vertices), none valid; 372_1 = C31:C12 covers side A (side B >= 4 short) · c5 tabu
never left cost 4 from the 360_53 near misses (5 starts x 90 s) · c6 bi-Cayley best 6 at 704 (bad 1056) · c7 tabu
best 6 at 704 (C11:Q16, bad 528), no 2-opt fix · c8 tabu 3+3: 14 at 696 (annealing in round 1: 28; bad 812).
Director: the 360_53 near miss also written as 3+3, 4+4 and 8+8 lifts (subgroups of index 3, 4, 8; tools/haar2liftN.py):
no cost-0 exact 2-opt neighbour in any (about 1M candidates each); tabu in the 8+8 form never left its start (16).
Tabu on Haar graphs finds the 684 record in 0.9 s but stops at 6 on the 351_5 wall group (annealing: 2), so Haar search
stays with haarex2/mcos. Haar annealing over all non-abelian groups of order 362-380 (research/s65/haar/
anneal_362_380.txt): best 6 (372_1, 372_9). Exhaustive Haar status after this round (research/s65/haar/STATUS.md): 96 of
99 searched groups of order 352-380 complete, none valid.
Calibrated the search that found the vertex-transitive (5,5) record: non-Haar |H| = 2 bi-coset graphs of C3 x P128 over
the 602 groups P of order 128 with <= 11 involutions (231 pairs H = K, 2 s anneals): one cost-0 pair (the record) and
12, 30, 34, 44, ... (median ~56 of 384) for the rest. Its (6,5) analogue, C3 x P256 on 768 vertices (2.03 walks per
target, more slack than the record's 1.78), is round 5 (4,284 groups P with <= 11 involutions).

### Round s65r5 (09:22-09:52 UTC, 8 cards, research/squads/s65r5/)
Cards: c1-c6 the (6,5) analogue of the vertex-transitive (5,5) record search: non-Haar |H| = 2 bi-coset graphs of
G = C3 x P, P of order 256 with <= 11 involutions (4,284 groups in six parts; 768 vertices) · c7 exhaustive Haar
remainder (orders 352-360, then 361-380) · c8 the semidirect variants C3 : P256 (P acting on C3 by inversion through an
index-2 subgroup), P with 1 or 3 involutions.
Best per card (coset cost of 768; none valid): c1 48 (P = SmallGroup(256,113), 180 pairs from ids 2-164) · c2 48
(256_3019 and 256_3504, 302 pairs, all of part 1) · c3 66 (75 pairs, half of part 2) · c4 60 (81 pairs, all of part
3) · c5 67 (33 pairs, all of part 4) · c6 none (part 5, ids above 26,245: no non-Haar pair at all) · c7 closed 360_98,
360_28, 360_108, 360_100, 352_169 and 375_2, 375_5, 376_10, 378_23, 378_27, 378_48, 378_54: no Haar graph; the
exhaustive search now covers ALL 93 groups of order 352-360 with <= 3 involutions (none works) · c8 62 (57 pairs).
Reading: about 670 C3 x P256 pairs annealed, costs 48-1160, median ~100 of 768; the (5,5) calibration had its lone
cost-0 pair among 231 pairs with the rest at 12+, so the (6,5) distribution (best 48 = 6% of the vertices, against 12/384
= 3% for the (5,5) runner-up) looks worse, not merely unlucky. Round 6 finishes the sweep anyway (part 0 rest and part
2 rest), adds P with 15 involutions, and moves the non-Haar |H| = 2 sweep to orders 722-760 and 720 (ids 451-840).
Director meanwhile: 2+2 lifts by few-involution groups of order 192 (768 vertices, the lift analogue of the (5,5) order-96
records) under tabu: 22-36, far behind order 176 (6); dropped.

### Round s65r6 (09:53-10:23 UTC, 8 cards, research/squads/s65r6/)
Cards: c1-c3 the rest of the C3 x P256 sweep (P with <= 11 involutions) · c4 C3 x P256 with 15 involutions (first 400) ·
c5 exhaustive Haar, the slow low-involution groups of order 361-380 · c6/c7 non-Haar |H| = 2 bi-coset graphs at orders
722-740 / 742-760 · c8 the same at 720, ids 451-840.
Best per card (coset cost; none valid): c1 **14 of 768** for C3 x SmallGroup(256,357), pair (1,1), in a 2 s anneal
(416 pairs, median 108; its neighbours 256_362 and 256_413 give 22, 256_356 and 256_361 give 34) · c2 52 (328 pairs) ·
c3 68 (69 pairs) · c4 34 (450 pairs, 15 involutions) · c5 slow groups partly run (see its table) · c6 20 at 732
(SmallGroup(732,10), exhaustive optimum 20; only 47 non-Haar pairs in 722-740; orders 2 x odd have none) · c7 22 at
756 (SmallGroup(756,86); 56 pairs in 742-760) · c8 12 at 720 (SmallGroup(720,557) and (720,560); 261 runs, ids
451-840 done).
Card c7 noted that dc2_lib's SKIPHAAR drops a class H when ANY index-2 normal subgroup misses it, so pairs (H, K) with
only H outside N (half-Haar: N regular on one side only) were skipped; those are the mcos "1|2,2"-type graphs, which
were weak (round 2), so nothing is lost for the conclusions.
Kept: the C3 x SmallGroup(256,357) cluster (2-generator groups of class 5, like the (5,5) record's P128 =
SmallGroup(128,139)); the director runs long anneals on it and sweeps all 2-generator groups of order 256 (ids
1-541, any involution count). Round 7: the whole squad closes the Haar family at 352-360 with the new haarex3.

### Round s65r7 (10:21-10:40 UTC, 8 cards, research/squads/s65r7/)
Cards: c1-c8 exhaustive Haar search with the director's new haarex3 (research/s65/tools/haarex3.c: the sixth element of S
solved exactly instead of enumerated; validated against haarex2 on SmallGroup(342,12), the 684 record group: same 28
side-A covers and the same 10 VALID sets, and on SmallGroup(360,53); about 4x faster) over the 255 open groups of order
352-360 with more than 3 involutions (research/s65/haar/hi_list_0..7.txt).
Result: all 255 finished (each card 31-33 groups in 13-17 minutes; high-involution groups have large automorphism
groups and run fast); no VALID set. Side-A covers only in SmallGroup(360,126) (4 sets) and (360,138) (44 sets), side B
at least 4 short in all (card c2, whose report went out before these runs finished). Two cards reran the 342_12 control.
**Haar closure:** with rounds 2-6, this job's director runs (360_53, 352_43, 360_61, 360_74, 360_52 rerun) and job
fresh-6-5's 24 groups, every one of the 353 non-abelian groups of order 352-360 is now closed exhaustively (check:
research/s65/haar/all_352_360.txt against the logs); abelian groups give at most 542 vertices (fresh-6-5's counting
bound). With fresh-6-5's theorem for orders 343-351: there is no Haar graph of degree 6 and diameter 5 on 686-720
vertices. Round 8 extends this to orders 361-380.
Director meanwhile: long anneals of the best C3 x P256 pair (C3 x SmallGroup(256,357), H = K): three seeds x 120 s all
stop at cost 14 (bad 2688), found in the first minute; its group is a 2-generator class-5 group like the (5,5)
record's P128 but contains no copy of SmallGroup(128,139). Sweep of all 2-generator groups P of order 256 (ids 1-541)
not swept before is running.

### Round s65r8 (10:38-10:50 UTC, 8 cards, research/squads/s65r8/)
Cards: c1-c8 haarex3 over the 111 non-abelian groups of order 361-380 not closed in round 4 (research/s65/haar/
r8_list_0..7.txt). Result: all 111 finished (8-17 minutes per card), no VALID set, no side-A cover (111 logs, all
Acovered=0). Cards c2 and c7 finished their groups but wrote no scoreboard line; their logs are complete.
**Haar closure, final:** every non-abelian group of order 343-380 has been searched exhaustively (343-351: fresh-6-5;
352-360: rounds 2-7; 361-380: rounds 4 and 8; check: research/s65/haar/all_352_360.txt, all_361_380.txt against the
logs), and abelian groups stop at 542 vertices. So no Haar graph of degree 6 and diameter 5 has 686-760 vertices;
the 684 record is the largest Haar graph below 762 vertices.

### Director's close (10:55 UTC)
No graph above 684. Eight rounds, 64 Haiku cards. What the squad added: breadth in rounds 1-3 (every non-Haar family
tried came out far from 0: tri-Cayley 10, coset graphs 8-150, lifts 4-38, bi-Cayley 4, multi-orbit 27, rewiring 1428
bad pairs), the tabu search that beats annealing on lifts (card s65r3-c6), and raw throughput on the decisive
exhaustive Haar runs once the director had calibrated tools (rounds 3-8: about 600 exhaustive group runs). The decisive
steps were the director's: the "Haar graphs in disguise" lemma that cleared the coset near misses, the calibration of
the (5,5) vertex-transitive record search (and its (6,5) analogue C3 x P256, best 14 of 768 for C3 x SmallGroup(256,357)),
and haarex3 (4x faster, validated), which made the full Haar closure at 686-760 vertices possible in two rounds.
Honest reading: the squad was most useful as parallel hands for well-calibrated exhaustive work; as a source of new
ideas it produced one (tabu). Next for this cell, if anyone returns: non-Haar constructions only (Haar graphs are
closed through 760); the C3 x P256 class-5 cluster (ids 330-420) at cost 14-22 is the closest non-Haar family to the
(5,5) analogy, and an exhaustive bi-coset search with symmetry reduction there would settle it.
