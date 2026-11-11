# c7 notes: non-metacyclic solvable groups of the missing orders

Goal: Haar graphs H(G,S), |S| = 4, diameter <= 9, on non-metacyclic solvable groups G (|G/G'| <= 309, d(G) <= 3)
of orders 2488..2528 without SmallGroups data. Vertices per graph = 2|G|.

## Result
All 368 groups tested with exhaustive `hx ... 0 9` (LIMIT 0): every one prints `MIN >0`, i.e. no Haar set of cost 0.
Calibration: the record group Z_71 x| Z_35 (metacyclic, N = 2485) gives HIT0 at once with the same tool.
Exact minima were not computed (score recorded as '>0').

| order | family | groups | exhaustive |
|---|---|---|---|
| 2488 | C311 : H, H in SmallGroups(8) | 2 | yes |
| 2492 | C89 : H, H in SmallGroups(28) | 1 | yes |
| 2499 | C17 : H, H in SmallGroups(147) | 2 | yes |
| 2502 | C139 : H, H in SmallGroups(18) | 2 | yes |
| 2504 | C313 : H, H in SmallGroups(8) | 2 | yes |
| 2508 | C19 : H, H in SmallGroups(132) | 9 | yes |
| 2511 | C31 : H, H in SmallGroups(81) | 28 | yes |
| 2512 | C157 : H, H in SmallGroups(16) | 20 | yes |
| 2516 | C37 : H, H in SmallGroups(68) | 1 | yes |
| 2496 | (C13:C_k) x Y, k in {4,6,8,12}, Y in SmallGroups(48/32/24/16) | 74 | yes |
| 2500 | direct products C2^2 x P, C4 x P, SmallGroups(20) x SmallGroups(125) (P order 625) | 14 | yes |
| 2500 | C4 : P, P in SmallGroups(625), 4 sampled order-4 actions per P | 48 | NO (sample) |
| 2520 | SmallGroups(24)xSmallGroups(105), (12)x(210), (56)x(45), (40)x(63) | 52 | yes |
| 2528 | C79 : H, H in SmallGroups(32) | 113 | yes |

Filters applied in GAP: normal cyclic prime-order subgroup C_m (characteristic Sylow), |G/G'| = prod AbelianInvariants <= 309,
d(G) = Length(MinimalGeneratingSet) <= 3, non-metacyclic (no normal cyclic M with cyclic G/M, checked via NormalSubgroups).
Iso classes of C_m : H = Aut(H)-orbits on Hom(H, Aut(C_m)) (exact because C_m is characteristic). Not deduplicated for
the direct-product families (duplicates possible; harmless).
Not covered: 2496 with H of order 192 in general (1543 groups) except products with C13:C_k; 2500 P:C4 beyond samples;
2520 products other than the four listed pairs; non-split groups (the C_m-normal decompositions above are all split).

## Rerun
- Enumerate: `gap -q --quitonbreak drv2488.g < /dev/null` (drvNNNN.g call RunOrder(ORD, m, hsz, [1..NrSmallGroups(hsz)]) from lib2.g).
- Products: famlib.g with PairFam, f2496*.g, f2520*.g, f2500*.g, sampled P:C4 in p625c4.g (seeded).
- Table + search per group: `python3 tools/build_tab.py exp/NAME.exp w/NAME` then `tools/hx w/NAME.tab w/NAME.aut 0 9`.
  Tables (12 MB each) were deleted after use; re-create them as needed.
- Scoreboard lines: fix_scoreboard.py (rewrites only the c7 lines in r1/scoreboard.jsonl).
