# (3,8) round 2: complete group sweep (tools)

- `export_groups.g` (GAP 4.12 + SmallGroups, `apt install gap-core gap-smallgrp`): multiplication tables of every group of
  the orders listed, written to `groups/g<n>.txt` (regenerated, not committed: about 50 MB). `export_reps.g`: Aut(G)-orbit
  representatives of G, written to `groups/reps_<n>.txt`. Run with `gap -q export_groups.g` then `perl -0pi -e 's/\\\n//g'`
  on the output (GAP wraps long lines with backslash continuations).
- `tlift.c`: exhaustive voltage-lift search over any group table (`gcc -O3 -march=native -o tlift tlift.c`).
  Usage in the file header. `run_full.sh` (k = 2, 4, 6 over orders 145–180, 73–90, 49–60) and `run_k8.sh` (k = 8,
  orders 37–46, first free voltage over Aut-orbit representatives).
- `verify_tl.py GROUPFILE N I SOL`: independent Python rebuild and all-pairs BFS of one solution.
- `bases/`: base multigraphs (`k E` then edges): `k2_3.txt` (Haar, 3 parallel edges), `b4_0.txt` (2+2), `b6_0..2.txt` (3+3),
  `b8_0..7.txt` (4+4). Both base lists come from round 1 (research/raise-d3D8 on claude/raise-d3d8-record-zys8i9).
