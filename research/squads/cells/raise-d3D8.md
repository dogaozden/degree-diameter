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
  3 free voltages, |G| = 73..84 (n = 292..336): **379 groups, 0 solutions** (runs/b4_73_84.log).
- 6-vertex bases (bases/b6_0..2, 3 classes), exhaustive over the 4 free voltages, |G| = 49..60 (n = 294..360): running,
  runs/b6_*.log.

## Files

- `research/raise-d3D8/lift_ex.c`: the search tool (usage in its header). `gen_specs.py N --prod`: group specs of order N.
- `run_one.sh`, `sweep.sh`: run one spec / a range of orders (4 jobs). `base_enum.py k`: bipartite cubic base multigraphs
  on 2k vertices (k=2: 1 class, k=3: 3 classes, k=4: 8 classes); bases/ holds the lists.
- `runs/*.log`: one line per group spec, `RESULT ex ... solutions=N FOUND|none`.
- Solutions are written to the scratchpad (not the repo) until verified; verified finds go to research/frontier/sols/
  (d3D8_ prefix, Haar) or research/lifts/sols/ (lifts), with an apsp VALID line.

- 4-vertex base, annealing (6 s per group, 1 seed), |G| = 73..100 (n = 292..400): **1142 groups, 0 solutions**;
  best cost 10 (runs/ann_b4_73_100.log).

- 6-vertex bases (b6_0, b6_1, b6_2), annealing (8 s per group, 1 seed), |G| = 49..60 (n = 294..360): **1086 runs
  (362 per base), 0 solutions**; best cost 12 (runs/ann_b6_*_49_60.log).

- 8-vertex bases (b8_0..7, 8 classes), annealing (8 s per group, 1 seed), |G| = 37..46 (n = 296..368): **1368 runs,
  0 solutions**. Best cost 8, but only for cyclic groups (Z_37); the best non-cyclic group is at cost 14 (runs/ann_b8_*).

## Current assessment (2026-10-25, about 3 h in)

No record. Every family the tool can build (Haar |G| = 145..180; b=4 |G| = 73..100; b=6 |G| = 49..60; b=8 |G| = 37..46)
gave no solution. Non-cyclic near misses sit at cost 12–20 (unreached pairs), far from zero, so a longer anneal of the
same groups is not a good use of compute. The next lever is a different group family (groups not built from metacyclic,
Z_p² ⋊ Z_k or cyclic products, e.g. PSL(2,7) or SL(2,3)-based), or a structured construction. Both are beyond what the
existing spec families reach. Coordinator: this cell should go to an Opus session, or it can be closed as "no further
gain from the lift and Haar annealing families at (3,8)".

## Method notes

- Exhaustive search over the free voltages is slow for bases with 4+ free voltages (b=6: ~20 groups per 4 minutes on 4
  cores), and the 6-vertex exhaustive sweep was stopped after 20 groups (runs/b6_0.log, all `none`).
- Annealing (`lift_ex ... anneal SECS SEED`, cost = unreached pairs within D) finds the known 288 lift in about 150
  iterations (3 seeds, verified by apsp). It is the screen for the larger base graphs; exhaustive only for small cases.
- Cyclic groups are bad as expected (best cost ~90 on Z_73, Z_74 at b=4).

## Results and dead ends

- Haar, |G| = 145..180: none (1847 specs). 4-vertex base, |G| = 73..84: none (379 specs). Both families are the
  group families the tool can build (metacyclic, Z_p² ⋊ Z_k, products with cyclic factors), not all groups of each order.
