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

## Results

(see the table below; updated at each push)

