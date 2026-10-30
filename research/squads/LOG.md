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
