# w16 NOTES (handsoff-49 round 2): grow the 4,970 graph through its quotients

Start: 2026-10-31 23:54 UTC. Planned end: about 02:00 UTC. Card: cards.md, "## w16". Last update: 01:30 UTC.

## Result in one paragraph
No record (no valid lift with n > 4,970). The quotient bases of the 4,970 Haar graph rebuild the valid 4,970 graph
exactly, but annealing over voltages of these bases does not find cost 0 even over the group where the known solution
lives (order 497). Over the groups of order 498..530 (5+5 base), 356..380 (7+7) and 72..80 (35+35) the best costs are
82 (n = 5,040), 137 (n = 5,040) and 911 (n = 5,040). The optimizer, not the group, is the wall for lifts of bases with
at least 10 vertices.

## Quotients (quot.py, lift_check.py) - verified
- G = Z_71 x|_49 Z_35 (index a + 71 j), S = {(0,0),(6,18),(30,19),(30,22)}, product (a,j)(b,l) = (a + 49^j b, j + l).
- N_k = {(a, k t)} is normal of index k (k | 35); G/N_k = Z_k. The quotient base is H(Z_k, {s_j mod k}): k + k vertices,
  4k simple edges, for k = 5, 7, 35. Voltages in N_k = meta:71:(35/k):(49^k mod 71):
  k = 5: meta:71:7:45 (order 497, base bases/q5.base, voltages bases/q5.volt);
  k = 7: meta:71:5:54 (order 355, bases/q7.*); k = 35: meta:71:1:1 (order 71, bases/q35.*).
- Rebuild (each gives VALID n = 4,970 by apsp, cost 0 by flift eval):
  `python3 quot.py 5 bases/q5.base bases/q5.volt && python3 lift_check.py bases/q5.base bases/q5.volt 71 7 45 out/lift_q5.edges && ../tools/apsp out/lift_q5.edges 4 9`
  (out/lift_q5.edges, out/lift_q7.edges, out/lift_q35.edges). Not a record: n = 4,970 is the table value.
- Only the 5+5 and 7+7 bases are 4-regular and simple; the 35+35 base has 70 roots.

## Calibration: the optimizer is the bottleneck
Cost = number of (root, lift vertex) pairs at distance > 9; far pairs = cost * K / 2 (checked with score48).
- flift SA, 5+5 over meta:71:7:45, 60 s, random start: cost 92. tabu (TABU=1), 60 s: cost 68.
- wl2 (w8's SA, bitsets over roots), 5+5 over meta:71:7:45: 60 s cost 98; 400 s cost 84 (seed 11, 604k moves).
  So the known cost-0 lift is not rediscovered from random voltages (11 free voltages in a group of order 497).
- 7+7 over meta:71:5:54: tabu 30 s cost 126.
- 35+35 over Z_71 (71 free voltages): wl2 120 s cost 810; flift is about 50x slower there (it loops over roots
  separately, b^2 work per evaluation) so use wl2 for b > 20 (`bases/q*.wl` = base files without the m token).
- Per root, the far count is about 8 (5+5), 10 (7+7), 12 (35+35): random-like lifts sit near 0.2% far pairs, but
  nothing reaches zero by annealing.

## Scans (wl2, one seed; full tables in scan5.tsv, scan7.tsv, scan35.tsv; deepened in deep.tsv and deep5.tsv)
- 5+5 base, all 298 metacyclic groups of order 498..530 (5 to 6 s each). Mean cost 211; best:
  meta:14:36:3 (504) 82; meta:21:24:13 (504) 90; meta:9:56:8 (504) 90; meta:50:10:11 (500) 92; meta:21:24:20 (504) 94.
  Deepened 60 s (seed 7): 86 to 118, so the screen values were partly luck; the plateau is about 80 to 100.
- 7+7 base, 186 metacyclic groups of order 356..380 (4 s each). Best: meta:30:12:17 (360) 137; meta:90:4:17 (360) 139;
  meta:20:18:9 (360) 142. Deepened 60 s: 123 and 150.
- Non-metacyclic groups of order 360 (7+7 base, 5 s, nonmeta7.tsv): A5 x cyc 6 233; A4 x cyc 30 129; SL(2,3) x cyc 15 130.
- 35+35 base, 42 metacyclic groups of order 72..80 (10 s each). Best: meta:3:24:2 (72) 911; meta:9:8:8 911-942.
  Deepened 90 s: 1,072 (worse than the screen).
- Non-metacyclic groups of order 498..530 (5+5 base, 6 s, nonmeta5.tsv): psl2 7 x cyc 3 (504) 133; agl1 23 (506) 153;
  sl2 3 x cyc 21 (504) 104; semi 5 20 2 0 0 3 (500) 132; semi 3 56 0 1 2 0 (504) 103; S4 x cyc 21 (504) 126.
  None beats the metacyclic groups.
- Seed spread of the best group (meta:14:36:3, order 504, 5+5, 45 s, seeds 21-24): 112, 96, 139, 97. So the 82 of the
  6 s screen is a lucky short run; the realistic floor of these runs is about 95.

## Smooth objective (wsmooth.c) and where the far vertices sit
- wsmooth: SA with cost = far + LAM * sum over (root, vertex) of exp(-walks_<=9 / TAU) (walk counts, exact).
  On 5+5 over meta:71:7:45, 40 s: 82 to 108 for (LAM, TAU) = (0.01, 2), (0.05, 1), (0.2, 0.5), (1, 1.5).
  On 5+5 over meta:14:36:3 (order 504), 300 s, LAM 0.01, TAU 2: far 106 (the 82 screen was lucky).
  So the smooth term does not break the plateau.
- farclass.py on the best 497 state (out/long5_497.best.edges, cost 84): far vertices spread over all 7 classes
  of the abelianisation Z_7 of M, and over all 10 base vertices (per root 3 to 12 far). No Z_7 parity obstruction
  (unlike the 2+2 lifts in w5/w13).

## Best near miss (not valid)
- n = 5,040, cost 82, far pairs 20,664 (score48), 5+5 base over meta:14:36:3, 6 s wl2 seed 1 (best ever seen on
  this group: 96 to 139 with longer runs).
  File: /home/user/degree-diameter/research/squads/handsoff-49/w16/out/wl_q5_meta_14_36_3.best.edges
  (diameter 10). Rebuild: `wl2 bases/q5.wl grp/meta_14_36_3.bin 9 6 1 OUT` with grp from `groups.py "meta 14 36 3"`.

## What did not work
- Plain SA (flift), tabu (w5's tabu), and wl2 SA from random voltages: all stall at 68 to 98 on the 497 group where
  cost 0 is known to exist. More time (400 s) does not help.
- Other groups in the 498..530 range are no better than 82; the scans show no group with a clearly lower floor.

## Final state (01:30 UTC)
Best near miss: n = 5,040, cost 82 (6 s screen; 96 to 139 on longer seeds). No cost-0 lift with n > 4,970 found.
Scoreboard: two lines appended (the 4,970 rebuild, marked not a record; the cost-82 near miss).

## Next idea (not run)
Give the annealer a smoother cost before scanning more groups: sum over roots of the excess (dist - 9)+ together with
the number of far vertices, or the walk-count deficit at radius 9. Test it first on the 5+5 base over meta:71:7:45:
if it rediscovers cost 0 in 60 s, scan the groups of order 498..530 with it. If not, stop the quotient route.
