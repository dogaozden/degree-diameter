# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-26, hunt-d5 (Opus, cloud session_01G9FwCXeEt4mUvAMjcr9j11), round 1: (5,5), (7,5), (9,5)

Goal: bipartite diameter-5 graphs above our 354 / 1,152 / 2,662, searched in the windows Haar order 193–224 / 606–630 /
1,378–1,410 (and lifts of the same sizes). 16 Haiku cards (model haiku, effort high), 13:40–14:20 UTC, 4 shared cores.
Director tools first (research/squads/hunt-d5/tools): GAP SmallGroups tables, haar5 (D = 5 Haar annealer with
automorphism orbits), flift/lift from b48. Cards, scoreboard and work folders: research/squads/hunt-d5/r1/.

Cards: a1 (5,5) Haar 193–207 · a2 (5,5) Haar 208–224 · a3 (5,5) 3+3 lifts over 65–75 · a4 (5,5) 2+2 / 4+4 lifts ·
a5 (5,5) wildcard (6+6 lifts) · b1 (7,5) Haar 606–622 · b2 (7,5) Haar 608–630 · b3 (7,5) 5+5 / 6+6 lifts · b4 (7,5)
2+2 / 3+3 / 4+4 lifts · b5 (7,5) wildcard (products, 7+7, 11+11) · c1 (9,5) Haar "3 3 0" orbits 1378–1400 · c2 (9,5)
other orbit shapes · c3 cubic route-chart controllers · c4 (9,5) small-base lifts · c5 (9,5) wildcard (GQ + matchings)
· x1 global wildcard (bi-coset graphs, lifts of PG(2,4)).

Best per card (cost = uncovered pairs; 0 would be a graph): a1 8 (C41⋊C5, 204/6, 200/40; 3 s screens) · a2 15
(210/2) · a3 30 (Z65; 1 s runs) · a4 16 (100/7, 104/3) · a5 82 · **b1 4 (SmallGroup(615,1))** · b2 12 (624/134) · b3 79
· b4 30 (meta 61:5:9, 19:16:18) · b5 13 (S₄ × Z₂₇) · c1 none (no usable automorphism at 1392) · c2 8 (C197⋊C7,
1379) · c3 controllers m = 16 (m = 17: 6) · c4 16 (C53⋊C13, 2+2 base, n = 2,756) · c5 5,234 · x1 834.
No valid graph in the windows.

Director meanwhile: a 3-letter route chart over F₃⁴ with every non-backtracking pattern nonsingular and both pencil
conditions (also over F₄⁴), so any cubic bipartite controller with same-side distance ≤ 4 and a 4-cycle at every
vertex lifts to a (9,5) graph on 162m vertices (m = 12, 16 checked all-pairs). Controllers stop at m = 16 (three
annealers stall at 6 for m = 17): 2,592 < 2,662, so not a record. Non-abelian coset fibres (order 81): worse.

Kept for round 2: metacyclic-type groups (615/1, C197⋊C7, C41⋊C5), K_{Δ,Δ} lifts (new), the m = 17 controller,
q = 2 route charts for (6,5) (a cell we do not hold), exhaustive orbit certificates (new haar5 exho mode).

## 2026-10-26, hunt-d5 round 2: metacyclic Haar groups, K_{Δ,Δ} lifts, m = 17 controller, (6,5)

16 cards, 14:12–14:35 UTC (research/squads/hunt-d5/r2/). New cell this round: (6,5) (published 684, we hold nothing).
Cards: a1 (5,5) exact search on metacyclic groups 193–215 · a2 (5,5) 3+3 lifts with Z₅₉ calibration · a3 (5,5) K₅,₅
lifts over 39–45 · a4 (5,5) 2+2 lifts deep · b1 (7,5) 615/1 deep · b2 (7,5) metacyclic screen 606–660 · b3 (7,5) 609,
610, 612, 624 deep + orbit certificates · b4 (7,5) 2+2 / 3+3 lifts over metacyclic groups · b5 (7,5) K₇,₇ lifts · c1
(9,5) metacyclic 1378–1420 · c2 (9,5) 2+2 lifts over C53⋊C13 · c3 (9,5) K₉,₉ lifts · c4 m = 17 controller (tabu) · x1
(6,5) Haar 343–360 · x2 (6,5) q = 2 route charts · w1 coset-union S.

Best per card: a1 stopped (director's sweep covers it; D97 exact minimum 194) · a2 10 (Z₅₉ not reproduced) · a3 62 ·
a4 12 (104/3, 2+2) · b1 4 (615/1, 41 seeds; 1- and 2-swap local minima) · b2 none (GAP listing too slow) · b3 6
(609/1, 610/2) · b4 26 · b5 147 · **c1 4 at SmallGroup(1378,2) = C2 × (C53⋊C13)** · c2 14 · c3 173 · c4 m = 17: 6
(two far pairs + two vertices on no 4-cycle, from every start) · **x1 2 at C71⋊C5 (355, (6,5))** · x2 26 · w1 worse
than plain annealing (dropped).

Director: haar5 exho (exact orbit-symmetric spaces): 615/1 all ≥ 12; exhp (exact, probe-accelerated, 9 s per group of
order 200) sweeping every group of order 193–215 at (5,5); exact 3-swap neighbourhood of 615/1's cost-4 set found
**cost 2** (S = 0 206 135 343 507 543 593); haar_fast (research/structured) is 13× faster than haar5 on metacyclic
groups, so round 3 uses it. Kept: metacyclic seed farms in all four cells, exact neighbourhoods, (5,5) 216–224 sweep.

## 2026-10-26, hunt-d5 round 3: haar_fast seed farms on metacyclic groups, (5,5) exact sweeps, (6,5)

16 cards, 14:35–14:50 UTC (research/squads/hunt-d5/r3/). Tool: haar_fast (research/structured), 13× haar5 here.
Cards: c1/c2/c3 (9,5) farms on (Z53⋊Z13)×Z2 with three settings · c4 (9,5) screen of 53 metacyclic specs 1378–1430 ·
c5 Z197⋊Z7, Z463⋊Z3 farms · b1/b2 (7,5) farms on (Z41⋊Z5)×Z3 · b3 screen of 45 specs 606–658 · b4 609/610 farms · d1
(6,5) screen of 55 specs · d2 (6,5) 357/351 farms · d3 (6,5) non-metacyclic 343–360 · a1 (5,5) exact 216 · a2 (5,5)
exact 217–224 · x1 tabu from the cost-4 sets · w1 wildcard (2-switch repair from the 615 graph).

Best per card: **c2 2 (Z53⋊₁₆Z26, seed 1016, K = 32, COOL = 40)** · **c3 2 (seed 2035; histogram over 60 short
seeds 2:1, 4:9, 6:20, 8:25, 10:5)** · c1 4 (11/24 seeds) · c4 6 (meta 31 15 16 3, 1395) · c5 4 (Z197⋊Z7) · b1 4 · b2 4
(10/36) · b3 4 (Z103⋊Z6, 618) · b4 4 ((Z61⋊Z5)×Z2, 610) · d2 4 (357) · a2 none in 217–223 (exact; best 16) · x1, w1 4
(no progress; CPU starved). d1, d3, a1 reported after this entry (see the cell file).

Director: **certificate: SmallGroup(355,1) = C71⋊C5 has no Haar graph of diameter ≤ 5 at Δ = 6** (exact search over
S ⊇ {e, r}, r one representative per Aut(G)-orbit: 5 × 6.4·10⁸ sets; minimum 2). The cost-2 set of 615/1 has no
solution within 3 swaps (exact). haar_fast patched to keep near misses (tools/haar_fast_sb.c, SAVEBEST=1) and
tables in its numbering (tools/metatab.py), so farms feed the exact neighbourhood search (haar5 lns / complete).

## 2026-10-26, hunt-d5 round 4: farms with near-miss saving + exact LNS; (6,5) screens; **(9,5) 2,756**

16 cards, 15:08–15:30 UTC (research/squads/hunt-d5/r4/). New tools: haar_fast/haar_tab SAVEBEST, metatab.py, haar5 lns.
Cards: c1/c2 (9,5) Z53⋊Z26 farm + LNS (switched to Z197⋊Z7 and Z463⋊Z3 after the director's find) · c3 Z197⋊Z7 · c4
other 1378 forms, 1395, 1405 · b1 615 farm + LNS · b2 610, 618 · b3 non-metacyclic 606–650 · d1/d2 (6,5) screens
343–368 · d3 per-edge F₂ route charts on mixed controllers · d4 360/51 farm + LNS + 3-swap · d5 (6,5) 2+2 / 3+3 lifts ·
a1 (5,5) exact order 224 · a2 (5,5) exact 225–232 · w1 pattern-then-fill · w2 genetic search.

Best per card (reported so far): c1 **2 on Z197⋊Z7 (1379) in 2 of 26 seeds** · c2 10 (1389) · c4 8 (1395) · b1 4 · b2
4 (610: 5/16 seeds; 618) · d3 controllers with 4-cycles only (512 vertices at m = 16; mixed controllers fail at the
4-cycle-free vertices) · d4 4 by annealing, 2 in the exact 3-swap neighbourhoods · w1 2 (plateau) · w2 no better than
farms. Others still running at this entry.

**Director: (9,5) 2,756 vertices**: Haar graph of Z53 ⋊₁₆ Z26 = C2 × (C53 ⋊ C13), found by the director's farm (seed
7058, 15 s runs, K = 16, COOL = 10, REHEAT = 40; ~200 seeds in all; cost 0 after 0.2 s of that seed). build_haar2.py
VALID, apsp VALID d=9 D=5 n=2756. The squads found the group (r2 c1: cost 4; r3 c2, c3: cost 2), the director's tools
and farm closed it. Also exact certificates: (6,5) SmallGroup(351,12) and (357,1) have no Haar graph.
