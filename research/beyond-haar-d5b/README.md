# beyond-haar-d5b: exact lift searches for (5,5), coset annealing for (7,5)

Job "beyond-haar-d5b" (Opus cloud session, Oct 30 2026, from 03:35 UTC). Follow-up to beyond-haar-d5
(`../beyond-haar-d5/README.md`; its tools and logs were brought into this branch unchanged). Goal: raise (5,5) above
360 and (7,5) above 1,200, and try the same tools at (6,5) (table 684, not beaten here) and (8,5) (ours 2,048).

**NEW (5,5): 384 vertices (our value was 360).** 5-regular bipartite graphs of diameter exactly 5 on 384 vertices:
regular voltage lifts of 4-vertex bases by groups of order 96, found by the exact searches below.

| graph | base | group | voltages (element numbers of `records/g96_<i>.txt`, identity 0) | Aut | Haar? |
|---|---|---|---|---|---|
| `records/d5D5_n384_a2_g96_17.edges` | [[2,3],[3,2]] | SmallGroup(96,17) = C3 : (Q8 : C4) | x 6, y 1 2, z 39 45 81, w 20 | 192, vertex orbits 192 + 192 | no |
| `records/d5D5_n384_a1_g96_31.edges` | [[1,4],[4,1]] | SmallGroup(96,31) | g 1 2 84, d 2 27 85, c 41 | 192, orbits 192 + 192 | no |
| `records/d5D5_n384_a1_g96_51.edges` | [[1,4],[4,1]] | SmallGroup(96,51) | first line of `records/b4a1x_96_51.sol` | 768, vertex-transitive | no (not Cayley either) |
| `records/d5D5_n384_a1_g96_66.edges` | [[1,4],[4,1]] | SmallGroup(96,66) = Q8 : (C3 : C4) | first line of `records/b4a1x_96_66.sol` | 96, 4 orbits | no |

Base [[2,3],[3,2]]: A0-B0 voltages {1, x}, A0-B1 {1, y1, y2}, A1-B0 {z0, z1, z2}, A1-B1 {1, w}. Base [[1,4],[4,1]]:
A0-B0 {1}, A0-B1 {1, g2, g3, g4}, A1-B0 {1, d2, d3, d4}, A1-B1 {c}. Edges are oriented A -> B and a base edge a -> b
of voltage g joins (a, h) and (b, h g); lift vertex (v, h) has index v*96 + h (A0, A1, B0, B1 = 0, 1, 2, 3).

Checks (`records/d5D5_n384_checks.txt`): `../lifts/coordinator_check/apsp.c` on each edge list: degree 5, bipartite,
diameter 5, RESULT VALID at D = 5 and RESULT INVALID at D = 4; independent Python all-pairs BFS
(`records/check_bfs.py`): VALID, diameter 5. Rebuild without our tables: `records/build_lift_perm.py` takes the
voltages as permutations (`records/d5D5_n384_*.perm`, written by `records/perm_voltages.g`, which also checks that
our table is the multiplication table of SmallGroup(96, i) in that numbering), generates the group by closure and
builds the lift; its output is isomorphic to the saved edge list (nauty) and BFS VALID. With GAP:
`exh/gap_tab_gens.g` writes the tables, `exh/lift_edges.py TABLE "SOL ..." OUT.edges` the edge list.

Not Haar graphs (`records/aut_haar.sh`, output `records/d5D5_n384_aut.txt`, nauty + GAP): a Haar graph on 384
vertices needs a colour-preserving automorphism group containing a subgroup of order 192 that is regular on each
colour class. For the (96,17), (96,31) and (96,66) graphs the colour-preserving group is the voltage group itself
(order 96). The (96,51) graph is vertex-transitive (|Aut| = 768, colour-preserving part of order 384), but none of the
3 conjugacy classes of subgroups of order 192 of the colour-preserving part is transitive on both sides, so it is not
a Haar graph, and not a Cayley graph (a bipartite Cayley graph is the Haar graph of the colour-preserving index-2
subgroup of its regular group).

## Tools (this folder)

| file | what it does |
|---|---|
| `exh/b4a2y.c` | exact search over all lifts of [[2,3],[3,2]] by a group of order <= 128 (same lifts and final test as `../beyond-haar-d5/exh/b4a2x.c`). More symmetry: Aut(G) by generators (union-find on the (x, {y1, y2}) states), x -> x^-1, the three tree-edge choices in the A0-B1 class (Y -> Y y^-1), w -> w^-1, and the base rotation A0 <-> A1, B0 <-> B1 (x' = w, w' = z0 x z0^-1, so cls(x) <= cls(w) for the Aut-and-inversion classes). Loop order: the second A1-B1 voltage w is fixed outside the z loops, closed walks at A0 and B0 are grouped by which z slots they use, and counting bounds prune z0, z1, z2. |
| `exh/runs/VALIDATION.md` | b4a2y against b4a2x: SmallGroup(72,30) exhaustive in both, the same 362 isomorphism classes (b4a2x 25,740 solutions in 1,331 s, b4a2y 3,481 in 190 s; 99 s with the rotation symmetry, same classes); SmallGroup(90,6): the same 2 classes. |
| `exh/b4a1x.c` | copy of the previous job's exact search for [[1,4],[4,1]]; `exh/gap_tab_autlist.g` gives it all of Aut(G) when |Aut| <= 5000, else 5000 elements including the identity (a subset keeps the canonical test complete, it only keeps more representatives). |
| `exh/haar5x.c` | exhaustive search of all Haar graphs of valency 5 and diameter 5 of a group of order <= 256 (S = {1, a, b, c, d}, a the smallest element of its Aut-orbit, incremental bitset cover of S^-1 S S^-1 S and S S^-1 S S^-1). |
| `exh/run_one.sh`, `exh/run_one_a1.sh`, `exh/run_one_h.sh` | per-group drivers (GAP export, search, one line per group in `exh/runs/<prog>_<order>.txt`, hits in `exh/runs/HITS.txt`). |
| `exh/sol2g6.py`, `exh/lift_edges.py` | graph6 / edge lists of solutions (nauty-labelg for isomorphism classes). |
| `coset/dcenum.c` | the previous job's coset-graph enumerator/annealer with a fix: in SA mode it rewrote the edge file on every evaluation (test() resets the running best); now it writes only on improvements. 4.6x more evaluations per second; the 1,200 (7,5) graph is re-found in 15 s (SEED=3) instead of 15 CPU-min. RESULT lines now report the number of evaluations. |
| `coset/sweep.sh`, `coset/queue75.sh`, `coset/focus1210.sh` | (7,5) annealing sweeps over SmallGroups with core-free H of order 2 (Haar-type H kept: any valid graph counts). |
| `records/` | the record graphs, tables, solution files, checks, the Haar test, the permutation rebuild. |

## Exact (5,5) results so far

A colour-preserving group acting freely with 4 orbits on a 4k-vertex graph makes it a lift of one of the two 2+2
bases [[1,4],[4,1]] and [[2,3],[3,2]] by a group of order k. A Haar graph of a group of order 2k that has an index-2
subgroup K is such a K-lift (its quotient by K is a 2+2 base with |S n K| and |S \ K| parallel edges), so these
searches also cover those Haar graphs.

- Orders 91, 92, 93, 94, 95 (364-380 vertices): every group, both bases: no (5,5) lift (b4a1x: previous job;
  b4a2y: this job, `exh/runs/b4a2y_9[1-5].txt`). With the Haar searches below this rules out every (5,5) graph on
  364, 368, 372 (except 3+3 and larger bases), 376, 380 vertices whose free colour-preserving automorphisms include a
  group of order N/4 or N/2.
- Order 96 (384 vertices): solutions (table above). Groups with solutions so far: b4a2y (96,17), (96,23); b4a1x
  (96,31), (96,51), (96,66). Runs continue (status at the end of this file).
- Haar graphs (haar5x, every group): orders 181-191 and 193-194 so far: none (362-388 vertices).

## (7,5)

Coset-graph annealing (|H| = 2) over SmallGroups of order 1202-1320 (`coset/logs/sw_*.txt`), a focused rerun of the
1210 near misses with the fixed annealer, and a squad round (below). No graph above 1,200 yet.

## Squad round bh5b-r1 (04:25 UTC)

Cards and scoreboard: `../squads/bh5b-r1/`. Best per card (cost 0 = valid): c1 (7,5) 1210 tabu over SmallGroup(1210,13):
18; c3 (7,5) |H| = 4 of PSL(2,17) (1224, exhaustive): 14; c4 (7,5) 2+2 lifts at 1204 over C43:C7: 20; c5 (6,5) coset
graphs of orders 686-718: 926 (the box was overloaded); c6 (6,5) 3+3 lifts at 720 over C5 x SL(2,3): 32. Useful
outcome: c1 found the dcenum SA write bug.

## Status

(updated during the session)
