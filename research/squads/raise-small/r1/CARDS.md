# Round 1 cards (raise-small-d, 2026-11-01)

Common: read research/squads/raise-small/HEADER.md first. $RS = research/frontier/raise_small.

## Already found / ruled out (every card gets this list)

- Round 0 (director): joint base+voltage annealing (salift_s) of 4+4 cubic bases over metacyclic groups solves D = 13 in
  seconds at group order N = 440-456 (Z19 x|_8 Z24: n = 3,648 VALID, now the value). 100-s probes at D = 13, p = 4:
  N = 544 cost 37, 602 cost 119, 666 cost 235, 732 cost 530. At D = 14, p = 4 (70 s): N = 812 (Z29 x|_2 Z28) and 816
  (Z17 x|_3 Z48) cost 6, 880 cost 20, 930 cost 36.
- The director runs p = 4 at D = 13 for N = 457-560 and at D = 14 for N = 785-860 (all metacyclic groups from glist.py).
  Cards: do not repeat those (p, D, N) bands.
- Earlier jobs: cyclic Z_n lifts of fixed bases (GP(10,3) x Z170 = 3,400 at D = 13, Pappus x Z317 = 5,706 at D = 14) are
  capped by the lift bound; Haar graphs (p = 1) A6 x Z4 (2,880, D = 13), PSL(2,7) x Z15 (5,040, D = 14) are far below;
  non-abelian voltages on a FIXED GP(10,3) base reached cost 2 at 3,300. (3,12) 2,368 and (3,11) 1,344 came from 4+4
  joint annealing over SmallGroup(296,3) = Z37 x|_6 Z8 and SmallGroup(168,1); (3,11) 1,474 is a metacyclic Haar graph
  Z67 x|_9 Z11 (exhaustive pairs). (3,10) 810: 5+5 joint annealing over C3 x He3; at 812-880 every state found was an
  exact 2-move local minimum (cost 4-20). (3,9) 506: no cubic Haar graph of any group of order 254-382, no VT graph
  508-1,280, no edge-transitive graph up to 10,000.
- Δ = 4: metacyclic Haar graphs with random S (hmeta) made (4,10)-(4,14); SL/PSL orbit sets are 13-17 % worse at odd D;
  cyclic lifts of K4,4, PG(2,3), GQ(3,3), the biplane stayed below Haar; salift4 over SmallGroups: cost 64+ at (4,8)
  n ~ 2,200 and 224+ at (4,9) n = 5,000 over groups of order 625 (p-groups). (4,9) near miss Z101 x|_5 Z25 (5,050) at
  cost 2 is an exact 2-opt local minimum; metacyclic Haar scans of (4,9) orders 2,486-2,800 found nothing (best cost 2).
  (4,12) near miss Z2861 x|_1385 Z13 (74,386) at cost 1.

## Cards

- **c01 (3,13), 3+3 bases.** salift_s with p = 3 at D = 13 over metacyclic groups of order N >= 609 (n = 6N > 3,648);
  go up from 609 while it solves. Compare cost vs n with the 4+4 numbers above.
- **c02 (3,13), 5+5 and 6+6 bases.** p = 5 (N >= 365) and p = 6 (N >= 305), D = 13. Find the largest n that solves.
- **c03 (3,13), big bases.** p = 8 (N >= 229), p = 10 (N >= 183), p = 12 (N >= 153), D = 13. More base freedom,
  smaller groups. Find the largest n that solves.
- **c04 (3,13), non-metacyclic groups.** Write a table generator (same format) for groups outside Z_m x|_r Z_k:
  AGL(1,q) = F_q x| F_q^* for prime powers q, (Z_p)^2 x| Z_k with a 2x2 matrix of order k, direct products of two
  non-abelian metacyclic groups, SL(2,q)/PSL(2,q) x Z_c, A5 x Z_c, etc. Run salift_s p = 4 at D = 13 for N in 457-600.
- **c05 (3,14), 5+5 and 6+6.** p = 5 (N >= 628) and p = 6 (N >= 523), D = 14, target n > 6,272 (census). Go up.
- **c06 (3,14), 3+3 and 2+2.** p = 3 (N >= 1,046) and p = 2 (N >= 1,569), D = 14.
- **c07 (3,14), 4+4 high band.** p = 4 at D = 14 for N = 861-1,000 (above the director's band); use chained runs
  (START=...best) on the 2-3 most promising groups (pick by short 60-s screens first).
- **c08 (3,14), non-metacyclic groups.** As c04 but D = 14, p = 4 (N >= 785) or p = 5 (N >= 628).
- **c09 (3,12) > 2,368.** salift_s at D = 12 with metacyclic groups (and Z_c products): p = 4 (N >= 297), p = 5
  (N >= 237), p = 6 (N >= 198), p = 3 (N >= 395). Polish cost <= 4 states (bin/polish is fine at N < 400).
- **c10 (3,11) > 1,474.** As c09 at D = 11: p = 4 (N >= 185), p = 5 (N >= 148), p = 6 (N >= 123), p = 3 (N >= 246),
  p = 2 (N >= 369). Polish cost <= 4 states.
- **c11 (3,10) > 810 and (3,9) > 506.** Joint annealing over metacyclic groups and Z_c products the own-small job did not
  use (it used all SmallGroups of orders 68-90 etc.): D = 10 with p = 2..8 at n = 812-900; D = 9 with p = 2..6 at
  n = 508-560. Polish everything at cost <= 4.
- **c12 (4,9) > 4,970 and (4,10) > 12,416: quartic joint lifts.** bin/salift4 (p+p 4-regular bases, base and voltages
  free) over metacyclic groups with LARGE r-order d (Frobenius-like, not p-groups): (4,9) p = 2 (N >= 1,243), p = 3
  (N >= 829), p = 4 (N >= 622); (4,10) p = 2 (N >= 3,105), p = 3 (N >= 2,070), p = 4 (N >= 1,553). Compare with hmeta
  Haar on the same n.
- **c13 (4,11) > 30,334 and (4,12) > 74,066: quartic joint lifts.** salift4, p = 2..4, metacyclic with large d; the
  table file for N ~ 4,000-10,000 is big (N^2 entries): if gtab.py is too slow, write the table in C or add a metacyclic
  product directly to a copy of salift4 (no table).
- **c14 (4,13) > 192,382.** Haar graphs with bin/hmeta (d = 4) on Frobenius / metacyclic groups of order 96,192-99,000
  with k in 13-61 (odd order preferred at odd D), chained START runs. Check finds with tools/metacheck.py and
  tools/meta2edges.py + bin/apsp.
- **c15 (4,14) > 497,042.** Same at D = 14, order 248,522-256,000; even D, so even orders and k up to ~100 are fine.
- **c16 wildcard Δ = 3.** Find an approach none of the other cards uses (they all use salift_s lifts or Haar graphs of
  metacyclic groups): for example cubic Cayley graphs Cay(G, {a, b, c}) generated by three involutions, which are
  bipartite when a, b, c lie outside an index-2 subgroup (PGL(2,q), S_n, Coxeter quotients), bi-coset graphs, or
  two-stage lifts (lift a lift). Target (3,13) > 3,648 or (3,14) > 6,272.
- **c17 wildcard Δ = 4.** Find an approach none of the other cards uses (they use hmeta random-S Haar graphs and
  salift4 joint lifts): for example fixed-base lifts of the (4,6) Moore graph (generalized hexagon GH(3,3), 728
  vertices) or of GQ(3,3) (80 vertices) over metacyclic (non-abelian) voltage groups, or Cayley graphs generated by four
  involutions. Target (4,13) > 192,382 or (4,14) > 497,042 (or (4,11)/(4,12)).
