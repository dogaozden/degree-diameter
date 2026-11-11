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
- CORRECTION (22:14): closedcount.py used vertex-level backtracking, which is wrong for multigraphs. The edge-level
  count (closedcount_edge.py) gives b22t1: 4956 closed walks of length <= 9 at a root, b22t2: 4960 (K44 2520,
  PG(2,3) 756). The fiber bound needs >= k-1 closed walks, so the 2+2 bases are NOT ruled out (k = 1243..1250 is fine).
  The run_ils2 queue stays as planned.

## Status 22:15 UTC
- Best near miss so far: K44 (8 vertices) over Z_622, n = 4,976, cost 192 (hgi ILS, 40 s). Not valid.
- Long ILS runs queued in run_long.sh: K44 Z_622 for 420 CPU-s (seed 41), then PG(2,3) Z_192 for 420 CPU-s (seed 42).
  Results go to run_long.log (DONE_LONG marks the end). The ILS stalls at a basin after ~3 sweeps; a better move
  set (joint moves or accepting worse states) is the next thing to try.
- Cost floor reminder: a lift of a girth-12 base (H(3) incidence graph) has diameter >= 12 for any group, so the
  card's hexagon family cannot give n > 4,970 with diameter 9. The same applies to any base of girth >= 10.

## 22:26 UTC: best so far
- K44 (8 vertices, the complete bipartite graph K_{4,4}) lift over Z_622, n = 4,976: ILS cost 156 (far = 48,516 unordered
  far pairs, checked by score48 and apsp: INVALID at D=9). Rebuild: WRITE_EDGES=1 ./hgi k44.txt cyc:622 0 1 1 1 OUT
  long_k44_z622_s41.best (the .best holds the voltages "e g" per edge of k44.txt). Edge list: k44_z622_156.edges.
  Scoreboard line appended (22:25).
- Multi-start ILS (run_ms.sh, 45 s per seed, seeds 100..., until 23:15) is running; results in ms.log.

## New card from the coordinator (22:45 UTC; reply at 23:55)
Filter (filter.py, edge-level non-backtracking walks, multigraph safe): for every root u, closed walks of length <= 9 at u
must number >= |G|-1 and every target v needs >= |G| walks of length <= 9 (parity is forced in bipartite bases).
Results: d4D5_162 (162 vertices, 4-regular, bipartite): min closed walks 76, min walks per target 76 -> passes for |G| <= 40.
PG(2,3): 756 -> passes up to 756. K44: 2520. b22t1: 4956 (degenerate in practice). rb12: 1628; rb14: 1426.
The filter is necessary only; it does not separate the bases: the actual lift costs are what matter (see below).
hgw.c: generic walk-bitset evaluator (any base <= 256 vertices), ILS with best responses; checked against score48
on d4d5.txt over Z_31 (cost 9060 = 2*140430/31).
Queues (started 22:46): run45.sh (d4D5 over dih17, dih18, dih19, meta13-3-3, meta9-4-8, dih16, meta5-8-2, agl1 5 x 2,
60 CPU-s each) -> run45.log; runpg.sh (PG(2,3) over sl2_3xZ8, meta14-14-13, dih100, semi7-4, meta13-16-5, agl1 7 x 5,
heis3 x Z8, sl2_3 x Z9, meta7-28-6) -> runpg.log; run66.sh (rb12 over meta13-32-5, meta19-22-18, meta7-60-3; rb14 over
meta7-51-2, meta9-40-8) -> run66.log.
(4,5) base d4D5_162 over non-abelian groups, ILS 60 CPU-s each (run45.log): dih16 (n=5184) 3408; dih17 (5508) 4754;
dih18 (5832) 6708; meta9-4-8 (5832) 6069; dih19 (6156) 9435; meta13-3-3 (6318) 9814; meta5-8-2 (6480) 11488;
agl1 5 x Z2 (6480) 11857. Cost grows fast with |G|; 60 s is far too short for 163 free voltages (about 20 sweeps).
hgws.c = hgw.c plus SA=1 mode (single random moves, T from argv[5] down to env T1). About 0.55 ms per move on d4D5.
Queue runq2.sh (started 22:56): dih16 for 240 s, then PG(2,3) over sl2_3xZ8, meta14-14-13, heis3xZ8, agl1 7x5 (60 s each),
rb12 over meta13-32-5 and rb14 over meta7-51-2 (60 s each). Results in runq2.log.

## 23:21 UTC: new best (replaces the K44 cost 156)
- rb12.txt (6+6 random 4-regular bipartite, 12 vertices, 24 edges, girth? see closedcount) over meta 13 32 5
  (order 416): n = 4,992. ILS 60 s: cost 97; refined 240 s from that state: cost 80 (r12m13_80.edges,
  far = 16,640, apsp INVALID at D=9). Scoreboard lines appended at 23:12 and 23:17.
  Rebuild: ./hgw rb12.txt g66/meta_13_32_5.bin 0 1 1 OUT r12m13_80.sol (edges with WRITE_EDGES=1).
- Other 6+6 groups at 60 s: meta 7 60 3 (order 420, n = 5040): 91; meta 19 22 18 (order 418): 123.
- 7+7 random base rb14 over meta 7 51 2 (order 357, n = 4998): 120 at 60 s.
- PG(2,3) over non-abelian groups at 60 s: sl2 3 x Z8 (192): 248; meta 14 14 13 (196): 311;
  heis 3 x Z8 (216): 609; agl1 7 x Z5 (210): 540. Cyclic/meta 8 24 3 were about 250 as well.
- d4D5_162 over dih16 (n = 5184), 240 s: 3229.
- Queue run4.sh (480 s refinement of the order-416 candidate) and run5.sh (360 s refinement of the order-420 one).
- 23:30: 480 s refinement of the order-416 candidate: cost 76 (r12m13_76.edges, far 15,808; scoreboard 23:30).
- 23:36: 360 s refinement of the order-420 candidate (meta 7 60 3): no change (91). Its file: r12m7_91.sol.
- 23:37: last refinement queued (run6.sh, 300 s, order 416 from cost 76), result in run6.log.
Filter status for the coordinator's card: all bases tried pass the walk-count filter for their group orders; the filter
does not discriminate, and the real limit is the walk-voltage coverage (about 2% of (root, target, voltage) triples are
uncovered at random; ILS brings the 6+6 base down to 76 at n = 4,992).
- 23:43: SA (T 3 -> 0.5, 400 s) from the cost-76 state started, output r7_sa.* (r7_sa.log).
- 23:50: final SA refinement (T 3 -> 0.5, 1.24M moves) from cost 76: no accepted move, still 76.

## Final state at 23:50 UTC
Best near miss: rb12 (6+6 base) over meta 13 32 5 (order 416), n = 4,992, cost 76 (far 15,808), INVALID at D=9.
File: /home/user/degree-diameter/research/squads/handsoff-49/w4/r12m13_76.edges (solution r12m13_76.sol; rebuild with
hgw rb12.txt g66/meta_13_32_5.bin 0 1 1 OUT r12m13_76.sol and WRITE_EDGES=1). No record found (no cost 0).
Next idea: an order-416 or order-420 symmetric ansatz on the 6+6 base (base automorphisms as in hxs), and more
6+6 random bases (girth 4-6) over meta groups of order 416-420, since the 6+6 family beat K44 and PG(2,3).
