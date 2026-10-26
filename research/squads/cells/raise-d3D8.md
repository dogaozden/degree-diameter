# Cell (Δ, D) = (3, 8): job raise2-3-8, round 2

Haiku worker, branch claude/raise-3-8-record-ua8d88, started 2026-10-25. Table value 256 (DGQ). Bipartite Moore bound 510.
Our record: **288** (voltage lift of the 2+2 cubic base over Z3² ⋊_M Z8, M = [[0,2],[1,0]], order 72; verified in
research/lifts/coordinator_check/check_2026-10-23.txt). Target: a bipartite cubic graph of diameter ≤ 8 on more than 288 vertices.

## Starting point (round 1, branch claude/raise-d3d8-record-zys8i9)

Round 1 found nothing in: Haar graphs |G| = 145..180 over its spec families (metacyclic, Z_p² ⋊ Z_k, products with a
cyclic factor), 4-vertex base |G| = 73..84 exhaustive and 73..100 annealed, 6-vertex bases |G| = 49..60 annealed,
8-vertex bases |G| = 37..46 annealed. Its suggested lever: groups outside those families (PSL(2,7), SL(2,3)-based, A5, ...).

## Round 2: what is new

The family-based sweeps left groups out. This round uses **every** group of each order, from GAP 4.12 with the
SmallGroups library (apt package gap-smallgrp), so the sweeps below are complete over the group list.

- `export_groups.g`: exports the multiplication table of every SmallGroup of orders 37–46, 49–60, 72, 73–90, 145–180
  (non-solvable groups by a fallback; identity = code 0). The tables are about 50 MB, so they are not committed; the
  script regenerates them.
- `tlift.c`: exhaustive lift search over any group table. It does not use the lift.c families. Gauge: BFS-tree edges get the
  identity; the free voltages run over all of G (or, with a reps file, the first one runs over Aut(G)-orbit
  representatives). Parallel edges must differ. Every BFS-from-base-vertex check is the all-pairs criterion (right
  translations are automorphisms).
- Positive control: order 72, base b4_0, D = 8 finds exactly one group (SmallGroup(72,19), the Z3² ⋊ Z8 of the record),
  2304 lifts, the same count as the voltage session's exhaustive run. K3,3 with Z43 finds 1008 lifts (the voltage
  session has N = 43 solutions there too).
- `verify_tl.py`: independent rebuild from the table and voltages, all-pairs BFS. Verifies the 288 control: n 288,
  cubic, simple, bipartite, connected, diameter 8.

## Results (complete sweeps, every group of the order, every base class)

| k (base vertices) | base classes | orders N (n = kN) | groups | voltage space | solutions |
|---|---|---|---|---|---|
| 2 (Haar, 3 parallel edges) | 1 | 145–180 (290–360) | 538 | N² per group | **0** |
| 4 (2+2 base) | 1 | 73–90 (292–360) | 130 | N³ per group | **0** |
| 6 (3+3 bases) | 3 | 49–60 (294–360) | 62 × 3 | N⁴ per group | **0** |
| 8 (4+4 bases) | 6 distinct (round 1's 8 files: b8_2≅b8_3, b8_6≅b8_7) | 37–46 (296–368) | 35 | N⁵ per group, first voltage over Aut(G)-orbit reps | **0** (all 280 base × group runs) |

Base classes: enumerated and checked by `enum_bip3.py` (h = 1, 2, 3, 4 give 1, 1, 3, 6 classes up to side swap).
The k = 6 and k = 8 runs use round 1's base files, which match.

Near misses. `tlift` records, per group, the best cost (unreached vertices at the first failing base source).
The cost-2 near miss (group 80#3, k = 4, n = 320) is **not** close: the full all-pairs cost (sum of (dist − 8)⁺ over
ordered pairs) is 800. Annealing with 2-switch moves (`sa_repair.c`, 60 000 iterations, hot schedule) never got
below 800. So local repair of structured lifts is not a route here.

## Not covered

- k ≥ 10 (n = 10N, N ≤ 36). Needs a base enumeration for 5+5 (my canonical-form script is too slow in Python for h = 5)
  and about 6 CPU-hours for N = 29–31 alone. Not run.
- Non-semiregular constructions and graphs with no semiregular colour-preserving group of order ≥ 37.


## Round 3 (job raise3-3-8, branch claude/raise-3-8-record-r3-6207dj, started 2026-10-26)

Record to beat: **288** (round 2 did not beat it). Tools: `research/raise-d3D8-r3/` (copies of round 2's `tlift.c`,
`verify_tl.py`, bases k=2,4,6,8; new: `enum3.py`, `export_groups.g`, `export_reps.g`, `run_k10.sh`).

- Environment: GAP 4.12 with SmallGroups installed from apt this round (`apt-get update` first).
- Tool check: positive control reproduced (order 72, base b4_0: SmallGroup(72,19) gives 2304 lifts, same as round 2).
- `enum3.py h` (row-sorted enumeration, canonical form = min over row permutations of column-sorted matrices):
  h = 2, 3, 4, 5, 6 give 1, 3, 6, 15, 48 classes. h = 3 and 4 agree with round 2's `enum_bip3.py`.
- Open lead from round 2 taken: **k = 10** (5+5 bases, 15 classes), orders N = 29..36 (n = 290..360). Each run
  costs about `d(N)·N^5` candidates with the Aut-orbit reps on the first free voltage (cyclic Z29: 60 s per base).
- Not affordable here: k = 12 (48 bases, N^7 candidates per base; about 8 CPU-hours per base at N = 25).

### Round 3 result: k = 10, orders 29, 31, 33 (complete, 45 base × group runs)

- Every run: all 15 bases × groups of order N, first free voltage over Aut(G)-orbit reps, D = 8, no skipped runs.
- **0 solutions.** Best near-miss cost (unreached vertices at the first failing source, over lifts within cost 2):
  cost 1 in 12 of 15 runs at N = 29, 8 at N = 31, 2 at N = 33; cost 2 in 2 runs at N = 31 and 2 at N = 33.
  Runs with best 2^30 had no candidate within cost 2 (the sentinel is not an error; `tlift` only tracks near-misses).
- Candidates per run: 4.1e7 (N = 29), 5.7e7 (N = 31), 1.6e8 (N = 33); about 1.5 µs each.
- Next: orders 30, 34, 35 (launched, driver `runs/k10_driver_b.log`). Order 36 (14 groups) and order 32 (51 groups)
  are open; their cost is 5–20× this batch.
