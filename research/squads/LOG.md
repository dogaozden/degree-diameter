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
