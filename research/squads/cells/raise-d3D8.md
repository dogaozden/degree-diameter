# Cell (Δ, D) = (3, 8): job raise-3-8 (raise our record)

Haiku worker, claude/raise-d3d8-record-zys8i9, started 2026-10-25. Table value 256 (DS14v2). Bipartite Moore bound 510.
Our record: **288** (voltage lift of the 4-vertex cubic base over Z3² ⋊_M Z8, M = [[0,2],[1,0]]; coordinator check
research/lifts/coordinator_check/check_2026-10-23.txt). Target: any bipartite cubic graph of diameter 8 on more than 288 vertices.

## Status (update at every push)

- Tool: `research/raise-d3D8/lift_ex.c` (voltage lifts over a group given by a short spec; exhaustive or annealing over the
  free voltages). Re-running it on the 288 lift (`zp2 3 8 0 2 1 0`, base `bases/b4_known.txt`, voltages 0 29 0 0 31 22) gives
  VALID, and exhaustive search over that group finds 2304 solutions in 1.5 s. apsp.c (all pairs) agrees.
- Haar graphs (base = 3 parallel edges, n = 2|G|): exhaustive over every group in the spec families (metacyclic,
  Z_p² ⋊ Z_k, products with a cyclic factor) for |G| = 145..180, i.e. n = 290..360: **1847 groups, 0 solutions**
  (runs/haar_145_180.log).
- 4-vertex base (the only connected 3-regular bipartite multigraph on 2+2 vertices, bases/b4_0.txt), exhaustive over the
  3 free voltages, |G| = 73..84 (n = 292..336): see runs/b4_73_84.log.

## Files

- `research/raise-d3D8/lift_ex.c`: the search tool (usage in its header). `gen_specs.py N --prod`: group specs of order N.
- `run_one.sh`, `sweep.sh`: run one spec / a range of orders (4 jobs). `base_enum.py k`: bipartite cubic base multigraphs
  on 2k vertices (k=2: 1 class, k=3: 3 classes, k=4: 8 classes); bases/ holds the lists.
- `runs/*.log`: one line per group spec, `RESULT ex ... solutions=N FOUND|none`.
- Solutions are written to the scratchpad (not the repo) until verified; verified finds go to research/frontier/sols/
  (d3D8_ prefix, Haar) or research/lifts/sols/ (lifts), with an apsp VALID line.

## Results and dead ends

(to be filled as runs finish)
