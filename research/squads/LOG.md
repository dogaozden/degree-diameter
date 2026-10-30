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
