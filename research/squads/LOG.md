# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-29, job beyond-haar-d5 (Opus cloud session), goal (5,5) > 354 and (7,5) > 1,152 without Haar graphs

### Round bh5-r1 (18:55 UTC, 8 cards, research/squads/bh5-r1/)
Cards: c1 (7,5) 2+2 lifts, orders 290-300 · c2 (7,5) 3+3 lifts, orders 194-200 · c3 (7,5) 4+4..6+6 lifts, orders
97-150 · c4 (7,5) GQ lifts (W(4)+2 over order 7/8, W(5)+1 over order 4, W(3)+3 over 15/16) · c5 (5,5) small-base
lifts (2+2 over 89/90, 3+3 over 60, 4+4..6+6, W(2)+2) · c6 (5,5) surgery on 354/352 · c7 (7,5) surgery on 1152/1140 ·
c8 bi-coset graphs (wildcard).
Best per card (cost = uncovered pairs, 0 = valid): c2 28 at 1176 · c3 36 at 1176 · c5 6 at 360 (2+2 over
SmallGroup(90,5)), 8 at 356 (Z89) · c6 152 far pairs at 356 · c7 436 far pairs at 1154 · c8 8 at 366 (order 366,
|H| = 2; but |G| = 2 x odd makes it a Haar graph of the index-2 subgroup) · c1, c4: see below.
Kept: the (5,5) small-base near misses; bi-coset graphs with |G| divisible by 4. Dropped: surgery (rigid records),
bases with more than 8 vertices (worse, as the coupon-collector law predicts).
Opus alone meanwhile: exhaustive search of all Z89-lifts of the 2+2 base [[2,3],[3,2]] (exh/cyc22.c, 22 CPU-min):
no solution, so no 356-vertex graph of that form. Solutions exist up to Z80 at least (320 vertices).
Round-1 c1 and c4 did not report back (no scoreboard line); their folders hold logs only.

### Round bh5-r2 (19:17 UTC, 6 cards, research/squads/bh5-r2/)
Cards: c1 (5,5) bi-coset h=2, |G| divisible by 4, orders 356-400 · c2 (5,5) long anneals of the round-1 near
misses (2+2 over order 90/92-94, 3+3 over order 60) · c3 (7,5) bi-coset h=2, orders 1156-1200 · c4 (7,5) mixed
route-chart lifts (3 chart colours over F2 + 1 plain) · c5 wildcard (both cells) · c6 wildcard (5,5).
Best per card: c2 cost 2 at 360 (2+2 base [[1,4],[4,1]] over C9 x D10 and C5 x ((C3 x C3):C2)), 4 at 360 (3+3 over
SmallGroup(60,3)), 6 at 376 · c3 58 at 1188 (metacyclic only; SmallGroups data for 1156-1200 was missing then) · c4
896 at 1216 (chart structure no better than random lifts) · c5 44 at 360 (K66 minus a matching over order 30), 142
at 1184 · c6 1868 pairs at 356 (Z5-symmetric with fixed points, dead end) · c1: pending at the time of writing.
Kept: the cost-2 lifts at 360 (Opus: basin sampling, i.e. many short anneals, each near miss checked by exact
2-opt/3-opt, src/kopt.c). Dropped: route charts at Δ=7, large bases, fixed-point actions.
Opus alone meanwhile: exhaustive coset graphs of almost simple groups (coset/dcenum.c). Best (7,5): PSL(2,17),
|H| = |K| = 4, 1224 vertices, cost 14 (all 12,156 unions). Best (5,5): A6 h=2 and S6 h=4 at 360, cost 20. Annealing
the Z17-lift description of the PSL(2,17) graph from that start did not improve it.
Round-2 c1 finished its sweep (best cost 8 at 360, SmallGroup(360,120) and (360,124), h=2) but did not report back.

### Round bh5-r3 (19:55 UTC, 3 cards, research/squads/bh5-r3/)
Cards: c1 (7,5) coset graphs h=3 over all SmallGroups of order 1731..1845 · c2 (5,5) coset graphs h=3 (orders
534..558) and h=4 (712..744) · c3 (7,5) coset graphs of constructed products (A5 x A5 h=6, PGL(2,7) x C7 h=4, ...).
Best: c1 cost 2 at 1210 ((C11 x C11):C15), but that graph is a Haar graph of the normal index-3 subgroup
(C11 x C11):C5 with an S closed under an order-3 automorphism; best non-Haar C199:C9 at 1194, cost 18 · c2 cost 6
at 372 and 8 at 366, both with H normal (Haar graphs of G/H); core-free cases worse · c3 A5 x A5 h=6, cost 24 at
1200; the larger products stalled in GAP's subgroup lattice.
Opus meanwhile: core-free filter and a fast subgroup finder in the exporters (a bug of mine broke the exports for
4 minutes; c1, c2 told to redo those orders); exact searches: all lifts of the 2+2 base [[1,4],[4,1]] over every group
of order 89..95: none (so the cost-2 plateau at 360 is an obstruction); 2-opt around the 1210 Haar near miss.
Kept: (5,5) 3+3 record-type base over order-60 groups (basins + exact k-opt); (7,5) coset graphs h=2 at 1176/1200.

### Round bh5-r4 (20:40 UTC, 2 cards, research/squads/bh5-r4/)
Cards: c1 (7,5) coset graphs h=2 for the non-solvable SmallGroups of order 1176 and 1200, then small solvable orders
· c2 (5,5) record-type 3+3 base over the other non-abelian groups of order 60, basins with exact 2/3-opt.
Round-4 results: c1 (7,5) coset graphs h=2: C5 x (SL(2,5):C2) = SmallGroup(1200,475), cost 8 at 1200 (non-Haar: its
index-2 subgroups contain H; capped at 2M unions); C7 x PSL(3,2) = SmallGroup(1176,212), cost 14 at 1176 (non-Haar);
other non-solvable groups of order 1200: 28-38 · c2 (5,5) record-type 3+3 base over other order-60 groups: see
its scoreboard line.
Opus meanwhile: coset graphs of C2 x A6 with |H| = 4 (order 720 sweep): cost 4 at 360, exhaustive (176 unions),
non-Haar (no subgroup of order 180); exact search for the other 2+2 base [[2,3],[3,2]] (exh/b4a2x.c, w solved from
the own-fibre conditions; filtered = brute force on SmallGroup(72,30)) running over the groups of order 90;
annealing of the SmallGroup(1200,475) coset unions; solvable groups of order 1176 with h=2 (Haar-type subgroups
skipped).
Round-3 c1 final: (7,5) h=3 orders 1731..1845 except 1764, 1776, 1800, 1824, 1836 (too many groups); best cost 2 at
1210 (the Haar case above); many pairs capped at 2M unions, so not exhaustive.
Opus (20:45): solvable groups of order 1176 with h=2 and Haar-type subgroups skipped: (C7 x C7):C24 =
SmallGroup(1176,213) reaches cost 4 at 1176 within the first 2M unions; full enumeration (about 57M unions) running.
Round-4 c2 final: record-type 3+3 base over C3 x (C5:C4), (60,1), (60,9): best cost 6 at 360; no k-opt fix.
Squad tally (r1-r4, 19 cards): no valid graph. The squads' main contributions were the cost-2 lifts at 360 (r2-c2),
which led to the exact 2+2 search, and the coset-graph sweeps (r3-c1, r4-c1), which found the closest (7,5)
near misses (SmallGroup(1200,475) cost 8, and the 1210 Haar case). The best (7,5) result so far came from an Opus
sweep that skips Haar-type subgroups, built on the round-4 tools.

### Hit (21:29 UTC): (7,5) 1,200 vertices
Annealing over unions of double cosets (coset/dcenum.c SA=1, 15 CPU-min, seed 1) for SmallGroup(1200,475) =
C5 x (SL(2,5):C2) with H = a non-central involution (the pair squad r4-c1 had left at cost 8 after a 2M-union cap)
reached cost 0: a 7-regular bipartite graph of diameter 5 on 1,200 vertices (our value was 1,152). apsp.c VALID
(INVALID at D = 4), independent Python BFS VALID, nauty |Aut| = 2400. It is a Haar graph: the index-2 subgroup
C5 x SL(2,5) acts regularly, so it is Haar(SL(2,5) x Z5, S) with S closed under an involutory automorphism;
research/frontier/build_haar2.py on the "sl 5 n 5" solution file: VALID d=7 D=5. Files in
research/beyond-haar-d5/records/. The squad's contribution: r4-c1 found the group and the cost-8 pair; Opus ran the
long anneal and the checks.

### Hit (found about 21:50, noticed about 22:33 UTC): (5,5) 360 vertices, not a Haar graph
The exact search exh/b4a2x.c for the 2+2 base [[2,3],[3,2]] over SmallGroup(90,6) = C15 x S3 printed 16 solutions
in its first branch (x = 6) before the run was stopped; nobody looked at the .sol file until about 22:33. Every solution
is a 5-regular bipartite graph of diameter 5 on 360 vertices (our value was 354): apsp.c VALID (INVALID at D = 4)
for all 16, independent Python BFS VALID. Two isomorphism classes (nauty): 12 solutions with |Aut| = 180 =
S3 x D30, 4 with |Aut| = 90. Neither is a Haar graph: the colour-preserving automorphism group is C15 x S3 itself
(order 90, four orbits), and the |Aut| = 180 class has side-swapping automorphisms but two vertex orbits (A0 u B1,
A1 u B0), so it is not vertex-transitive. Files in research/beyond-haar-d5/records/ (d5D5_n360*). Lineage: squad
r2-c2's cost-2 lifts at 360 on 2+2 bases led to the exact 2+2 searches (b4a1x, then b4a2x). Next: b4a2x over the
groups of orders 91..95 (364..380 vertices), running now.
Opus (22:37-23:38): b4a2x over 23 groups of order 90..102 (364..408 vertices, 4 CPUs, 20 min cap): no solution
beyond order 90. Exhaustive and empty: C23:C4, D92, C31:C3, D94, C4 x C4 x S3, D98, D100; the rest partial (see
research/beyond-haar-d5/README.md, end). The (7,5) coset sweeps at 1204..1320 were stopped at 22:37 to free the
CPUs (best costs 18-36, no hit). Session totals: (5,5) 360 (non-Haar), (7,5) 1,200 (Haar via the coset route).

## 2026-10-30, job beyond-haar-d5b (Opus cloud session), goals (7,5) > 1,200, (6,5) > 684, (8,5) > 2,048

### Round bh5b-r1 (04:25 UTC, 8 cards, research/squads/bh5b-r1/)
Cards: c1 (7,5) long anneals of coset graphs of SmallGroup(1210, 12/13/15), |H| = 2 · c2 (7,5) |H| = 3, SmallGroups of
order 1848-1980 · c3 (7,5) |H| = 4/6 of constructed product groups (order 2404+) · c4 (7,5) 2+2 / 3+3 lifts over
orders 301-330 / 201-220 · c5 (6,5) |H| = 2, SmallGroups of order 686-720 · c6 (6,5) 3+3..5+5 lifts over orders
115-125 / 86-95 / 69-75 · c7 (8,5) coset graphs of SL(2,13), PGL(2,13), products (order 2050+) · c8 wildcard.
Best per card (cost 0 = valid): c1 18 (tabu, SmallGroup(1210,13)) · c2 338 (SmallGroup(1878,2), 1252) · c3 14
(PSL(2,17), |H| = 4, 1224, exhaustive) · c4 20 (C43:C7, [[3,4],[4,3]], 1204) · c5 926 (box overloaded, 5 s anneals)
· c6 32 (C5 x SL(2,3), 3+3 all-2 base, 720) · c7, c8: see below.
Kept: c1's observation that dcenum's SA mode rewrote its edge file on every evaluation: fixed in
research/beyond-haar-d5b/coset/dcenum.c (4.6x more evaluations; the 1,200 graph is re-found in 15 s), and every (7,5)
anneal after 04:27 uses the fix. Meanwhile (not from the squad) the exact lift searches found (5,5) graphs on 384
vertices (research/beyond-haar-d5b/README.md). Honest reading: the squad found no graph, but its one bug report
was worth the round.

### Round bh5b-r2 (04:45 UTC, 8 cards, research/squads/bh5b-r2/)
Context given to the cards: (5,5) 384 had just been found by exact search (2+2 lifts by groups of order 96 = 2^5 x 3)
and dcenum's annealer was 4.6x faster. Cards: c1 (7,5) fast re-anneal of SmallGroup(1260, 61/62), (1320, 133..138),
|H| = 2 · c2 (7,5) |H| = 3 near misses SmallGroup(1806, 15/2), (1830, 2) · c3 (7,5) |H| = 2 sweep from order 1318
downward · c4 (7,5) 2+2 lifts over 2-rich groups of order 304-320 · c5 (6,5) 2+2 lifts over groups of order 176/192
· c6 (8,5) 2+2 lifts over groups of order 516-560 · c7 (5,5) > 384 with 3+3 lifts over groups of order 64-72 · c8
wildcard (it chose surgery on the 384 graphs: add two vertices and rewire with the 2-switch annealer).
Best per card (cost 0 = valid): c1 16 (SmallGroup(1260,61/62)), 30 at 1320 · c2 13 (1806,15), 16 (1830,2) · c3 263
(1316) · c4 34 (SmallGroup(312,55)) · c5 15 (order 176) · c6 123 (SmallGroup(544,221)) · c7 31 at 384 (annealing does
not even reach the known order-64 level; 118 at 432) · c8 no valid graph.
The machine was overloaded (load 11-14 on 4 cores from the exact searches plus 8 cards), which cut every card's
effective budget; several cards overran the time box. Reading: no new graph and no new idea; the squad confirmed that
annealing is far off for (6,5), (7,5), (8,5) lifts and for 3+3 (5,5) lifts. Two rounds in a row without a graph, so
no third round; the remaining time went to exhaustive bi-coset sweeps (|H| = 2, 3, 4 at (5,5); |H| = 3 at (6,5) and
(7,5)) and to finishing the exact lift searches.
