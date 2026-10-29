# beyond-haar-d5: non-Haar constructions for (5,5) and (7,5)

Job "beyond-haar-d5" (Opus cloud session, Oct 29 2026). Goal: beat our values 354 at (Δ,D) = (5,5) and 1,152 at
(7,5) with graphs that are not Haar graphs (all Haar graphs of the relevant orders were searched elsewhere).

**NEW (7,5): 1,200 vertices (our value was 1,152).** A 7-regular bipartite graph of diameter exactly 5 on 1,200
vertices: the coset graph of G = C5 x (SL(2,5):C2) = SmallGroup(1200,475) on the right cosets of a non-central
involution subgroup H (600 per side), Hx ~ Hy iff x y^-1 in S, S = a union of 4 double cosets HgH (sizes 4, 4, 4, 2,
degree 2+2+2+1). Found at 21:29 UTC by annealing over unions of double cosets (coset/dcenum.c SA mode, seed 1).
Checked: research/lifts/coordinator_check/apsp.c gives degree 7, bipartite, diameter 5, RESULT VALID at D = 5 and
INVALID at D = 4 (records/d7D5_n1200_apsp.txt). Files: records/d7D5_n1200_coset_sg1200_475.edges (edge list),
records/sg1200_475_h2.dc2 (coset action data), rebuild: `python3 coset/dc2_edges.py records/sg1200_475_h2.dc2
OUT.edges 242 206 265 2`.
**It is a Haar graph** (correction, 21:40 UTC): the index-2 subgroup R = C5 x SL(2,5) of G meets every conjugate of H
trivially, so R acts regularly on both sides and the graph is the Haar graph of SL(2,5) x C5 with the 7-element
connection set T = S n R, which is closed under conjugation by the involution of H (an orbit-type set, as in
research/structured). nauty: |Aut| = 2400, vertex-transitive (some automorphism swaps the sides), colour-preserving
part = G. So this beats 1,152 but it is not a non-Haar construction; the earlier Haar searches missed this set.
As a Haar graph: records/d7D5_n1200_haar_sl5xc5.txt (format of research/frontier/sols, group "sl 5 n 5", N = 600,
S = 7 elements of SL(2,5) x Z5, edges (g,A) ~ (s g, B)); research/frontier/build_haar2.py on it: VALID d=7 D=5,
ecc 5 from both sides, no duplicate edges, sha256 a56affd8f9737984c8ae551fd4322fe1c5b2187d7f98bd8ad8b1aae6ba72adf0
(records/d7D5_n1200_build_haar2.txt); apsp.c on that edge list: VALID. Independent Python BFS on the coset edge
list: VALID (records/d7D5_n1200_check_independent.txt).

(5,5): no graph above 354 was found. Near misses are listed below (cost 0 would be a valid graph).

## Summary

- **Exact negative results (5,5).** No voltage lift of the 2+2 base [[1,4],[4,1]] by any group of order 89..95
  (356..380 vertices) has diameter 5 (exh/b4a1x.c, every group, seconds each; completeness checked against brute
  force). No Z89-lift of the other 2+2 base [[2,3],[3,2]] does either (exh/cyc22.c). Together with the Haar search
  this settles 356 for lifts: a colour-preserving group acting freely on a 356-vertex graph has order 1, 2, 89 or
  178 (the number of orbits must be even and divide 356); order 89 means a Z89-lift of a 4-vertex base (both bases
  fail, exhaustively) and order 178 means a Haar graph (searched elsewhere). So a (5,5) graph on 356 vertices could
  only have free colour-preserving automorphism groups of order 1 or 2. The annealers had reached cost 2 at 360 on the
  [[1,4],[4,1]] base (C9 x D10, C5 x ((C3 x C3):C2)); the exact search shows that plateau is an obstruction.
- **Closest (5,5) non-Haar structures at 360:** the record-type 3+3 base [[1,2,2],[2,1,2],[2,2,1]] lifted by C15:C4
  (cost 4; 3-opt neighbourhood exhausted, no fix), and the coset graph of C2 x A6 with |H| = 4 (cost 4; all 176
  unions exhausted, no fix).
- **Closest (7,5) non-Haar structures:** the coset graph of (C7 x C7):C24 = SmallGroup(1176,213) (a subgroup of
  index 2 in AGL(1,49)) with H = an involution: 1176 vertices, cost 4, and the full enumeration of all 56.6M unions
  of double cosets has no cost-0 member. Then C5 x (SL(2,5):C2) with |H| = 2 (1200, cost 8; partial), SmallGroup(1176,
  236) (cost 7, partial), PSL(2,17) with |H| = 4 (1224, cost 14; exhaustive), C7 x PSL(3,2) (1176, cost 14),
  C199:C9 with |H| = 3 (1194, cost 18), random 2+2 lifts over groups of order 290/291 (1160/1164, cost 20). A Haar graph of (C11 x C11):C5 at 1210 reached cost 2
  through the coset route (orbit-type S); its 2-opt neighbourhood has no fix.
- **Dead ends:** surgery on the records (+2 vertices: 150+ far pairs at (5,5), 436 at (7,5)); GQ lifts for (7,5)
  (W(4)+2 matchings over Z7, W(5)+1 over order 4: thousands; first-moment counts say no solutions exist); mixed
  route charts at Δ = 7; lifts of bases with 10+ vertices; products Q x C_k with central C_k (abelian-like).
- **Why it is hard.** At (5,5) a vertex has 341 non-backtracking walks of even length <= 4 for 178 same-side targets;
  every lift condition we looked at sits at a walk/sheet ratio of about 1.8-1.9, the same as the 354 record. At (7,5)
  the record is at the Haar size-law wall (ratio 0.37 of the walk count); structured families (coset graphs of
  PSL(2,q), affine and product groups) land within a few percent of it but not above it.

## What could still work

- Finish the exact search for the [[2,3],[3,2]] 2+2 base over the groups of order 90 (exh/b4a2x.c): done with no
  solution for SmallGroup(90,i), i = 9, 3, 5, 8, 1; not run for i = 7, 2, 6 (non-abelian) and 10, 4 (abelian), about
  10-100 CPU-min each; then orders 91..95.
- For (7,5) above 1,200: orbit-type Haar graphs (coset graphs with |H| = 2 and a normal complement) of more groups.
  Tried at 1210..1320 (2 x odd orders, the non-solvable groups of order 1260 and 1320): best costs 18-36 in short
  anneals; the 1,200 hit needed 15 CPU-min of annealing from a cost-8 start, so longer anneals are the obvious next
  step.
- Full enumerations (no 2M cap) for the coset graphs that were only partly searched: SmallGroup(1200,475) (about
  320M unions, a few CPU-hours), SmallGroup(1176,236) and (1176,229) (about 1 CPU-hour each); and the h = 2 sweep of
  the 1040 groups of order 1200 and 235 of order 1184 with Haar-type subgroups skipped (coset/sweep_nh.sh).
- Longer annealing (hours) of the 3+3 record-type base over C15:C4 and the other non-abelian groups of order 60.

## Tools (this folder)

| file | what it does |
|---|---|
| `src/vl.c` | annealer over regular voltage lifts of a bipartite base multigraph by a group (multiplication table). Exact cost: uncovered (source, target sheet) pairs over one source per base vertex. Modes: full evaluation with early abort, `INC=1` incremental walk counts (fast for big bases), `TABU`, `FOCUS`, `GIBBS`, `SWAP` (base 2-switches). |
| `src/kopt.c` | exact k-opt neighbourhood of a lift: every way of changing k voltages, early-abort diameter test. |
| `src/ga.c` | whole-graph annealer by degree-preserving 2-switches, cost = ordered pairs at distance > D; `MOVABLE` edges (third column 1) restrict the moves. |
| `src/gap_tables.g` | GAP: multiplication tables of all SmallGroups of an order (identity = 0). |
| `src/gq_base.py`, `src/rand_base.py`, `src/grow.py`, `src/export_lift.py` | GQ bases, random regular bases, surgery starts, lift export for `apsp`. |
| `exh/cyc22.c` | exhaustive search of all Z_n-lifts of a 2+2 base (unit-normalised, sorted parallel edges, last two voltages by 128-bit bitset rotations). |
| `exh/b4a1x.c` | exact search of all lifts of the 2+2 base [[1,4],[4,1]] by any group of order <= 128: the self-fibres of A0 and B0 must be all of G; their walks through the single A1-B1 edge c are g_i c^-1 d_j and inverses, so c is solved from the missed elements; automorphisms of G reduce the A0-B1 voltages; survivors get the full test. Validated on A5 (240 vertices: solutions found, confirmed by vl and apsp) and for completeness on SmallGroup(72,30): for a fixed g-set the filtered search and brute force over all 4.1M (d, c) give the same 60 solutions (`G_ONLY`, `NOFILTER` switches). |
| `exh/cycgen.c` | Z_n-lifts of any small base: random outer voltages + exact inner two; `SA=1` anneals the outer ones with the inner two minimised exactly. |
| `coset/dc_export.g`, `coset/dc2_lib.g`, `coset/sg_export.g` | GAP: bi-coset graph data (coset actions and double cosets HgK) for a group and all pairs of classes of subgroups of order h. |
| `coset/dcenum.c` | exhaustive enumeration of all unions of double cosets with total degree Δ; two BFS (G is transitive on each side). |
| `coset/run_group.sh`, `coset/sweep.sh` | one constructed group / every SmallGroup of an order. |
| `exh/b4a2x.c` | exact search of all lifts of the other 2+2 base [[2,3],[3,2]]: spanning tree A0B0, A0B1, A1B1, so every closed walk of length <= 4 at A0 and B0 uses the second A1-B1 voltage w at most once and w is solved from the missed elements (walk classes generated by a DFS, not by hand). Validated: filtered = brute force for one (x, y) of SmallGroup(72,30) (8 solutions, confirmed by vl). |
| `exh/hexx.c` | exact search for the two "hexagon of dipoles" 3+3 bases (pruning by partial own-fibre coverage); too slow at order 60 as written (the 4th dipole level explodes), kept for reference. |
| `coset/run_group2.sh`, `coset/sweep_nh.sh`, `coset/affine7.g`, `coset/affine2_4.g` | dc2-based drivers: fast subgroup finder (cyclic, V4, S3), core-free filter, optional Haar filter (SKIPHAAR: drop H with a normal complement), exhaustive up to 2M unions then annealing (dcenum SA=1); affine families F_7^2:K and F_2^4:K. |
| `coset/dc2_edges.py` | edge list of a coset graph from a .dc2 file and a list of double-coset ids (GAP-free builder: the .dc2 file holds the generator permutations). |
| `coset/lift_from_sym.py` | rewrites a graph with a free automorphism of order R as a Z_R-lift (to anneal from a structured start). |

Checks: `../lifts/coordinator_check/apsp.c` (all-pairs BFS, no symmetry assumed).

## Results so far

Coset graphs are Haar graphs when G has a subgroup R with |R| = |G:H| meeting every conjugate of H and K trivially (for example a normal complement of H); normal H gives a Haar graph of G/H. The exporters skip subgroups with a nontrivial core.

Cost conventions: lifts = uncovered (source, sheet) pairs summed over one source per base vertex; coset graphs =
vertices missed within distance 5 by the two base vertices; whole graphs = ordered pairs at distance > 5.

| cell | construction | vertices | best cost | note |
|---|---|---:|---:|---|
| (5,5) | Z89-lifts of the 2+2 base [[2,3],[3,2]] | 356 | none exists | exhaustive (exh/cyc22.c, 22 CPU-min); solutions exist up to Z80 at least |
| (5,5) | lifts of 2+2 base [[1,4],[4,1]] over every group of order 89..95 | 356-380 | none exists | **exhaustive** (exh/b4a1x.c, seconds per group); annealing had reached cost 2 at 360 over C9 x D10 and C5 x ((C3 x C3):C2), so that plateau is a real obstruction |
| (5,5) | record 3+3 base over SmallGroup(60,3) | 360 | 4 | squad r2-c2 |
| (5,5) | bi-coset graphs of A6 (h=2), S6, PGL(2,9), M10 (h=4) | 360 | 20 | exhaustive over all unions |
| (5,5) | bi-coset graphs, \|H\| = 2, all groups of order 356..400 divisible by 4 (central H skipped) | 356-400 | 8 | squad r2-c1 |
| (5,5) | bi-coset graphs, \|H\| = 3 and 4, SmallGroups of order 534..558 and 712..744 | 356-372 | 6 (Haar of G/H) | squad r3-c2; the cost-6 and cost-8 cases have H normal, i.e. Haar graphs of G/H; core-free cases are worse |
| (5,5) | coset graphs \|H\| = 4 of the 23 non-solvable groups of order 720 | 360 | 4 | C2 x A6 with H = C4: cost 4, all 176 unions (exhaustive); non-Haar (no subgroup of order 180); the others 20+ |
| (5,5) | all 10 5-regular 3+3 bases over all 13 groups of order 60 (screen), then basins + exact 2/3-opt | 360 | 4 | record-type base [[1,2,2],[2,1,2],[2,2,1]] over C15:C4 is best (squad r2-c2: 4); 3-opt of that lift: no fix |
| (5,5) | surgery on 354 / 352 (+2 vertices, rewiring) | 356 | 152 pairs | dead end |
| (7,5) | bi-coset graph of PSL(2,17), \|H\| = \|K\| = 4 | 1224 | 14 | exhaustive over all 12,156 unions; 7-regular, diameter 6 (apsp) |
| (7,5) | bi-coset graphs of PSL(2,16) h=6, A7 h=4, S7 h=8, PGL(2,17) h=8 | 1260-1360 | 34-64 | exhaustive |
| (7,5) | bi-coset graphs of PSL(2,19), \|H\| = 6 | 1140 | 6 | exhaustive (below 1152 anyway) |
| (7,5) | bi-coset graphs of A5 x A5, \|H\| = 6 | 1200 | 24 | squad r3-c3, partly capped |
| (7,5) | bi-coset graphs, \|H\| = 3, all SmallGroups of order 1731..1845 | 1154-1230 | 2 (Haar), 18 (non-Haar) | squad r3-c1 + exporter; best: (C11 x C11):C15 at 1210 with cost 2, but G has a normal subgroup R of index 3 meeting H trivially, so it is the Haar graph of R = (C11 x C11):C5 with an S closed under an order-3 automorphism (orbit-type Haar). Best non-Haar: C199:C9 (H inside every index-3 subgroup), 1194, cost 18 |
| (7,5) | products Q x C_k (A4, S4 with cyclic), coset graphs | 1164-1176 | 96-848 | central factors make them abelian-like lifts; weak |
| (7,5) | coset graphs \|H\| = 2 of the non-solvable groups of order 1176 and 1200 | 1176, 1200 | 8 | squad r4-c1: C5 x (SL(2,5):C2) = SmallGroup(1200,475), cost 8 (2M of ~320M unions, then annealing); C7 x PSL(3,2), cost 14; non-Haar (no regular subgroup of index 2) |
| (7,5) | coset graphs AGL(1,49) \|H\| = 4, A5 x C20 / C29 \|H\| = 2 / 3 | 1176, 1200, 1160 | 30-90 | |
| (7,5) | coset graphs \|H\| = 2 of the solvable groups of order 1176, Haar-type subgroups skipped | 1176 | **4** | (C7 x C7):C24 = SmallGroup(1176,213) (inside AGL(1,49)), H = an involution: cost 4; the full enumeration of all 56,600,280 unions finds no cost-0 graph (best 4). Non-Haar: no index-2 subgroup meets H trivially. Neighbours SmallGroup(1176,214..218): 10-35 |
| (7,5) | affine F_7^2 : K, K <= GL(2,7) of order 12h, \|H\| = h = 4, 6, 8, 12 | 1176 | 16 | coset/affine7.g |
| (7,5) | 1-dim affine F_q : C_k, H = <x -> -x> (non-Haar when 4 divides k): (61,20), (97,12), (293,4) | 1220, 1164, 1172 | 12, 20, 133 | |
| (5,5) | affine F_2^4 : K, \|H\| = 16; C2 x C2 x A6, \|H\| = 8 | 360 | 408; 4 | |
| (7,5) | random lifts of 3+3 / 4+4 bases over groups of order 147-196 | 1176 | 28-36 | squads r1-c2, c3 |
| (7,5) | W(4)+2 matchings over Z7, W(5)+1 matching over order 4 | 1190, 1248 | thousands | GQ lifts far off |
| (7,5) | surgery on 1152 (+2 vertices) | 1154 | 436 pairs | dead end |

Squad rounds and their scoreboards: `../squads/bh5-r1/`, `../squads/bh5-r2/`, `../squads/bh5-r3/`, log in
`../squads/LOG.md`.
