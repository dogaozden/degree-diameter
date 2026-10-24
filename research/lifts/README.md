# research/lifts: voltage lifts of bipartite base graphs

A second construction beyond Haar graphs. A **regular lift** of a base multigraph B with voltages in a group Γ has:
- vertices (u, g), u ∈ V(B), g ∈ Γ;
- for every base edge e = {x, y} (x white, y black) with voltage a_e, the edges (x, g) ~ (y, a_e g).

Haar graphs are the case where B is a dipole with Δ parallel edges. The lift is bipartite when B is. Right
multiplication (u, g) ↦ (u, gh) is an automorphism, so

    diam(lift) = max over u ∈ V(B) of ecc((u, 1)),

which takes k = |V(B)| BFS runs.

Files: `LITERATURE.md` (how the table records were built), `RESULTS.md` (every cell tried), `sols/` (solution
files), `verify/` (checker outputs).

## Programs

| file | what it does |
|---|---|
| `lift.c` | the search. `gcc -O3 -march=native -o lift lift.c -lm` |
| `verify_lift.py` | independent rebuild of a solution file in Python, with its own group code. Writes the edge list and its sha256 |
| `apsp.c` | assumption-free all-pairs BFS on an edge list. `gcc -O3 -march=native -fopenmp -o apsp apsp.c` |
| `compare_iso.py` | exact isomorphism test (spectra, then complete backtracking) of a lift against a published adjacency list |
| `enum_bases.py` | all connected d-regular bipartite multigraphs on h+h vertices up to isomorphism (h ≤ 5, or h = 6 with d = 3) |
| `bases.py` | named bases (dipole, K_{a,b}, Heawood, Möbius–Kantor, Pappus, Desargues, Tutte 8-cage, cube) and random bases |
| `polygons.py` | incidence graphs of PG(2,q), W(q) and H(q) (q prime), optionally plus j perfect matchings, as base or solution files |
| `groups.py` | the group specs of a given order that lift.c implements (`--rich`: also aff groups and products of two non-abelian factors) |
| `summarize.py` | per-cell summary of `runs/*.tsv` |
| `run_cell.py` | parallel driver for one cell: orders × bases × groups, each job time-limited, results in `runs/TAG.tsv` |
| `haar_cell.py` | Haar graphs (dipole lifts) with haar_gen3 for one cell: candidates from research/frontier/sizelaw/small_cands.py, RANDSAMPLE screening scored by (p10 + median)/μ(N), annealing of the best |
| `haar2lift.py` | converts a haar_gen3 solution file to lift.c format (prime fields, meta, cyc) |
| `verify_haar.sh` | the four checks for a haar_gen3 solution: build_haar2.py, lift check, verify_lift.py, apsp |
| `exhaust_cell.py` | exhaustive lift search, every assignment, for one cell over small bases and all rich groups |
| `campaign1.sh`, `campaign2.sh` | the small-cell campaigns of this session (screened rich groups + wide bases; matrix-group Haar sweeps) |

### lift.c

```
lift search BASE D SECONDS SEED K OUT GROUP...   anneal; writes OUT (solution file) if the cost reaches 0
lift check  SOL [EDGES]                          exact BFS (integer distances) from every (u,1); optional edge list
lift sample BASE D M GROUP...                    cost quantiles of M random voltage assignments (screening)
lift exhaust BASE D OUT GROUP...                 every gauge-fixed assignment; first cost-0 lift to OUT (COUNTALL=1)
```

**Groups.** `GROUP := FACTOR [x FACTOR]...`, where FACTOR is one of:
- `cyc n`;
- `meta m k r`: Z_m ⋊_r Z_k, with (a,j)(b,l) = (a + r^j b, j + l), the Loz–Širáň convention;
- `dih n`;
- `aff p a b c d k`: Z_p² ⋊_M Z_k with M = [[a,b],[c,d]] and M^k = I mod p, where p is any modulus ≥ 2.
  M = [[1,1],[0,1]], k = p (p prime) gives the Heisenberg group of order p³, which is metabelian but not metacyclic.
  The (3,8) record uses `aff 3 0 2 1 0 8`;
- `sl p`, `psl p`, `pgl p`, for p prime ≤ 250.

Direct products cover Z_m × Z_n, metacyclic × cyclic, SL(2,p) × Z_n, SL × SL, and so on. Elements are written
componentwise, joined by `|`: `3`, `2,5`, `x,y,j` (aff), `1,2,0,1` (a matrix [[a,b],[c,d]]).

**Base file.** The first line is `k K`. Each edge is `e x y` (free voltage), `e x y = ELEM` (fixed), or
`e x y = 3|*` (partly fixed: components written `*` are free). B must be bipartite, connected and loopless.
Multi-edges are allowed; the search keeps parallel voltages distinct, so the lift is simple.

**Gauge fixing.** Free edges on a spanning forest that joins the components of the fixed edges get the identity.
Switching (v,g) ↦ (v, h_v g) changes a_e to h_y a_e h_x⁻¹, so this loses nothing.

**Cost.** The cost is the number of pairs (source (u,1), lift vertex w) with dist > D. It is computed by a bit-parallel
BFS: one 64-bit mask per lift vertex, sources of one colour per pass, updated in place by parity. A cost-0 run is
re-checked by `lift check` (plain BFS) before it is reported.

**Search.** Simulated annealing as in haar_gen3:
- each step picks one free edge and evaluates K candidate voltages;
- with probability TARGP, a candidate is *targeted*: it takes a random uncovered pair (u, w), random walks of
  lengths a and b from (u,1) and from w with a + b + 1 ≤ D, and sets the edge's voltage so that it joins the two
  walk ends;
- the best candidate is accepted by the Metropolis rule;
- after REHEAT seconds without improvement, the search returns to the best assignment.

Environment knobs: TMAX, TMIN, COOL, REHEAT, TARGP, UCAP, REPORT, NOGAUGE, WRITEBEST.

**Solution file.** Header `lift D .. Delta .. k .. N .. n ..`, then `group SPEC`, `k K`, and one `e x y = ELEM`
line per base edge (x white). `lift check`, `verify_lift.py` and `run_cell.py` all read it.

## Verification pipeline (every reported graph)

1. `./lift check SOL`: integer BFS from every (u,1) in lift.c's own lift.
2. `python3 -I verify_lift.py SOL EDGES [--full] [--no-bfs]`. This rebuilds the group from its definition, in
   different code, and builds the lift edge list. It reports:
   - n, edges, degrees, repeated edges;
   - bipartiteness and connectivity, by 2-colouring the lift itself;
   - that right translations by a generating set of Γ are automorphisms of the edge set;
   - the eccentricity of every (u,1), and hence the diameter.
   - `--full` adds a networkx all-pairs diameter (small n). `--no-bfs` skips the eccentricities when k is large.
3. `./apsp EDGES [threads]`: all-pairs BFS from every vertex on the edge list alone, with no symmetry assumption.

## haar_gen3

`haar_cell.py` and `verify_haar.sh` need a build of the repo's Haar search. Build it into a scratch directory:
`gcc -O3 -march=native -fopenmp -o SCRATCH/haar_gen3 ../frontier/haar_gen3.c -lm`. Pass it with `--bin`; the repo
file is not modified.

## Reproduce the rebuilds

```
gcc -O3 -march=native -o lift lift.c -lm && gcc -O3 -march=native -fopenmp -o apsp apsp.c
python3 polygons.py gq 7 2 5 sol > s.txt     # (10,5) 4000: W(7) + 2 matchings, Z_5
python3 polygons.py gh 5 1 3 sol > s.txt     # (7,7) 23436: H(5) + 1 matching, Z_3
./lift check s.txt
./lift check sols/rebuild_d7D3_hafner_loz_published.txt   # (7,3) 80 from the published voltages
```
