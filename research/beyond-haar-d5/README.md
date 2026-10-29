# beyond-haar-d5: non-Haar constructions for (5,5) and (7,5)

Job "beyond-haar-d5" (Opus cloud session, Oct 29 2026). Goal: beat our values 354 at (Δ,D) = (5,5) and 1,152 at
(7,5) with graphs that are not Haar graphs (all Haar graphs of the relevant orders were searched elsewhere).

**Status: no graph above 354 or 1,152 yet.** Best near misses are listed below (cost 0 would be a valid graph).

## Tools (this folder)

| file | what it does |
|---|---|
| `src/vl.c` | annealer over regular voltage lifts of a bipartite base multigraph by a group (multiplication table). Exact cost: uncovered (source, target sheet) pairs over one source per base vertex. Modes: full evaluation with early abort, `INC=1` incremental walk counts (fast for big bases), `TABU`, `FOCUS`, `GIBBS`, `SWAP` (base 2-switches). |
| `src/kopt.c` | exact k-opt neighbourhood of a lift: every way of changing k voltages, early-abort diameter test. |
| `src/ga.c` | whole-graph annealer by degree-preserving 2-switches, cost = ordered pairs at distance > D; `MOVABLE` edges (third column 1) restrict the moves. |
| `src/gap_tables.g` | GAP: multiplication tables of all SmallGroups of an order (identity = 0). |
| `src/gq_base.py`, `src/rand_base.py`, `src/grow.py`, `src/export_lift.py` | GQ bases, random regular bases, surgery starts, lift export for `apsp`. |
| `exh/cyc22.c` | exhaustive search of all Z_n-lifts of a 2+2 base (unit-normalised, sorted parallel edges, last two voltages by 128-bit bitset rotations). |
| `exh/b4a1x.c` | exact search of all lifts of the 2+2 base [[1,4],[4,1]] by any group of order <= 128: the self-fibres of A0 and B0 must be all of G; their walks through the single A1-B1 edge c are g_i c^-1 d_j and inverses, so c is solved from the missed elements; automorphisms of G reduce the A0-B1 voltages; survivors get the full test. Validated on A5 (240 vertices: solutions found, confirmed by vl and apsp). |
| `exh/cycgen.c` | Z_n-lifts of any small base: random outer voltages + exact inner two; `SA=1` anneals the outer ones with the inner two minimised exactly. |
| `coset/dc_export.g`, `coset/dc2_lib.g`, `coset/sg_export.g` | GAP: bi-coset graph data (coset actions and double cosets HgK) for a group and all pairs of classes of subgroups of order h. |
| `coset/dcenum.c` | exhaustive enumeration of all unions of double cosets with total degree Δ; two BFS (G is transitive on each side). |
| `coset/run_group.sh`, `coset/sweep.sh` | one constructed group / every SmallGroup of an order. |
| `coset/lift_from_sym.py` | rewrites a graph with a free automorphism of order R as a Z_R-lift (to anneal from a structured start). |

Checks: `../lifts/coordinator_check/apsp.c` (all-pairs BFS, no symmetry assumed).

## Results so far

Cost conventions: lifts = uncovered (source, sheet) pairs summed over one source per base vertex; coset graphs =
vertices missed within distance 5 by the two base vertices; whole graphs = ordered pairs at distance > 5.

| cell | construction | vertices | best cost | note |
|---|---|---:|---:|---|
| (5,5) | Z89-lifts of the 2+2 base [[2,3],[3,2]] | 356 | none exists | exhaustive (exh/cyc22.c, 22 CPU-min); solutions exist up to Z80 at least |
| (5,5) | lifts of 2+2 base [[1,4],[4,1]] over every group of order 89..95 | 356-380 | none exists | **exhaustive** (exh/b4a1x.c, seconds per group); annealing had reached cost 2 at 360 over C9 x D10 and C5 x ((C3 x C3):C2), so that plateau is a real obstruction |
| (5,5) | record 3+3 base over SmallGroup(60,3) | 360 | 4 | squad r2-c2 |
| (5,5) | bi-coset graphs of A6 (h=2), S6, PGL(2,9), M10 (h=4) | 360 | 20 | exhaustive over all unions |
| (5,5) | surgery on 354 / 352 (+2 vertices, rewiring) | 356 | 152 pairs | dead end |
| (7,5) | bi-coset graph of PSL(2,17), \|H\| = \|K\| = 4 | 1224 | 14 | exhaustive over all 12,156 unions; 7-regular, diameter 6 (apsp) |
| (7,5) | bi-coset graphs of PSL(2,16) h=6, A7 h=4, S7 h=8, PGL(2,17) h=8 | 1260-1360 | 34-64 | exhaustive |
| (7,5) | random lifts of 3+3 / 4+4 bases over groups of order 147-196 | 1176 | 28-36 | squads r1-c2, c3 |
| (7,5) | W(4)+2 matchings over Z7, W(5)+1 matching over order 4 | 1190, 1248 | thousands | GQ lifts far off |
| (7,5) | surgery on 1152 (+2 vertices) | 1154 | 436 pairs | dead end |

Squad rounds and their scoreboards: `../squads/bh5-r1/`, `../squads/bh5-r2/`, `../squads/bh5-r3/`, log in
`../squads/LOG.md`.
