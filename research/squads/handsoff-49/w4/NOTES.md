# w4 NOTES (card: lifts of the split Cayley hexagon H(3), 728-vertex incidence graph)

Start: 2026-10-31 21:41 UTC (note: PG(2,3) entries below are 22:01 UTC) (2 h budget, until about 23:41 UTC).

## Files
- gen_base.py -> base.edges / base.txt: incidence graph of H(3) from seeds/hexagon_q3.json (points 0..363, lines 364..727,
  1456 edges). Checked: 4-regular, bipartite, diameter 6 (apsp VALID at D=6).
- hx.c / hx: annealer over voltages of Z_k (or a .bin table) lifts. Voltage bitsets over roots (728 bits), walks <= 9.
  cost = 2 * (far pairs) / k, checked exactly against score48 on a random Z_7 lift (97986 = 2*342951/7).
  Usage: ./hx cyc:7 SECONDS SEED T0 T1 OUTPREFIX [INITSOL]; WRITE_EDGES=1 forces writing OUTPREFIX.edges.
- find_aut.py: random automorphisms of the incidence graph by distance-preserving backtracking (looking for a
  fixed-point-free automorphism of order 13 or 7, to use voltage invariance and cut the problem down).

## Results so far
- Z_7 lift (n = 5,096), plain annealing over 729 cotree voltages: random start cost 97,986 (diameter 12);
  best 84,900 after 60 s; ~87,000 after 400 s at T 200 -> 2. Plain SA barely moves the cost (about 120 far vertices
  per root). Not promising as is.

## KEY FINDING (21:58 UTC): the H(3) card cannot reach diameter 9
- The incidence graph of H(3) has girth 12 (checked: no closed non-backtracking walk of length 1..9 at any root).
- Fiber argument (holds for ANY covering, regular or not): a lift path from (u,e) to (u,x), x != e, projects to a
  closed non-backtracking walk of length L at u in the base (covering maps are locally bijective, shortest paths are
  non-backtracking). Such a walk needs L >= girth = 12. So every lift of H(3) has diameter >= 12, for every group.
- Consistent with the data: the Z_7 lift cost is at least 6*728 (fibers) + 12*6*728 (distance-2 same-side targets have
  only ONE non-backtracking walk of length <= 9, so 6 of 7 voltages are unreachable): floor 56,784 full cost.
  Annealing reached 82,420 (cyclic 7, full), 82,420 (symmetric, order-13 automorphism invariant, 57 variables).
- The order-13 and order-7 fixed-point-free automorphisms of H(3) do exist (found by apartment-pinned search,
  find_aut2.py, auts_13.txt / auts_7.txt), but symmetry does not help against the girth obstruction.
- Pivot: bases must have girth <= 9 (closed walks of length <= 9 at every vertex carry the voltages).
  Next: lifts of the PG(2,3) incidence graph (26 vertices, girth 6, 4-regular): groups of order 192..200 give
  n = 4,992..5,200. Generic evaluator hg.c (any base file with <= 64 vertices).

## PG(2,3) pivot (22:10 UTC)
- pg23.txt: incidence graph of PG(2,3), 26 vertices (points 0..12, lines 13..25), 4-regular, girth 6, diameter 3.
  Lifts over Z_192 give n = 4,992 (> 4,970). Random cost 880 (= 2*far/k, checked by score48). hg (generic annealer)
  reached cost 253 in 40 s (Z_192, T 30 -> 0.5), 27 free voltages.
- singer.py -> auts_pg13.txt: 3 Singer automorphisms (order 13, fixed-point-free, 2 vertex orbits, 4 edge orbits).
  hgs (symmetric version of hg): voltages constant on <s>-orbits, 3 free values in Z_192, EXH=1 scans all of them
  (first value over divisors of 192, i.e. up to unit automorphisms of Z_192).

## Facts established 22:08 UTC
- PG(2,3) (girth 6): closed non-backtracking walks at a root of length <= 9: 108 (len 6) + 648 (len 8). Same-side
  targets have ~757 walks of length <= 8 each; line targets from a point are covered by random voltages (odd walks).
  Random-voltage miss rate ~2% per same-side constraint, for ANY base with b*k ~ 5000 (walks per target = 19.7k/b).
- Singer-invariant lifts of PG(2,3) (3 free values, EXH scan over all 516k choices): best full cost 110,838.
  Structural: invariance makes all walk voltages small integer combinations of 3 values; bad.
- K_{4,4} over Z_622 (n = 4,976): start 1,252, SA best 204-221 in 30-40 s (8 roots).
- Nonabelian screen over groups of order 192..196 on PG(2,3) is running (run_groups.sh -> run_groups.log).
- Fiber-closed-walk counts (closedcount.py, closed NB walks of length <= 9 at a root): K44 2520 (k=622 needs 621),
  K55-matching 1908, rb12 1628, rb14 1426, PG(2,3) 756 (k=192 needs 191). So fibers are not the bottleneck for these.
- Nonabelian screen (40 s each, PG(2,3)): dih 96 -> 516 (cyclic Z_192 ~253 at 40 s). Rest: see run_groups.log.
- hgi = hg + ILS=1 mode (best-response over every cotree voltage, restart from best with 2-4 random resets).
  K44 over Z_622: ILS 192 in 40 s (SA 204 in 30 s).
- Cost unit used everywhere in w4 (hg/hgi/hgs): cost = sum over base roots u and lift vertices (v,x) of [dist > 9 from (u,e)]
  = 2 * (far unordered pairs in the lift) / k. Cost 0 <=> diameter <= 9. Verified with score48 (far=...).
- Queue run_ils2.sh (started 22:11): ILS on the 2+2 multigraph bases b22t1 (multiplicities 1,3;3,1) and b22t2
  (2,2;2,2) over Z_1243, Z_1245, Z_1250 (n = 4972, 4980, 5000), then K44 and PG(2,3) baselines. Output: run_ils2.log.
  Reason: an earlier card reported 2+2 lifts at n=5,020 with cost 24 in its own unit; I need to compare units.
