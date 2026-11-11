# Job beyond-small, squad round 3 — common header (read this first, then your card)

Machine rules, scorer and scoreboard format: unchanged from research/squads/beyond-small/r1/HEADER.md (read its "Machine
rules", "Scorer" and "Scoreboard" sections). Your folder: research/squads/beyond-small/r3/<card>/, scoreboard
research/squads/beyond-small/r3/scoreboard.jsonl. Keep every command under 100 s (`timeout 100 nice -n 10`), one thread.

## Goal: (17,5) beyond 34,848

Best so far: **34,848** (card r2/d06, director-verified with apsp and bfs_all): the (16,5) graph G (33,792 vertices,
16-regular, diameter 5) plus **48 Z22-orbits of hubs** = 1,056 hubs (27 orbits on side A, 21 on side B).
- A hub on side S is a new vertex joined to N ⊆ old vertices of the other side T (≤ 17; every old vertex in at most one
  hub). Conditions: (1) every S-vertex within distance 3 of N, (2) any two S-hubs have neighbours at distance ≤ 2,
  (3) hubs on opposite sides are within 5 (automatic in practice).
- Z22 symmetry: g → g+1 on the controller coordinate is an automorphism of G (vertex ((a_i,g),x) ↦ ((a_i,g+1),x)).
  An orbit = N and its 22 translates N+t; they are disjoint iff the keys (j, y) of N's vertices are distinct
  (768 keys per side), so at most 48 orbits of 16 per side: the cap is 2 × 48 × 22 = 2,112 hubs → **35,904**.
- d06's tool `research/squads/beyond-small/r2/d06/orb.c` (read its header): candidate key-distinct 4-line covers,
  orbit compatibility (N vs M+u for all u, and N vs N+u for u ≠ 0), greedy/plateau clique over orbits.
  `r2/d06/build_orbits.py ORBFILE OUT.edges` builds the graph (one orbit base N per line, global ids; A-orbits and
  B-orbits may be in one file). The 48 orbit bases of the 34,848 graph: research/squads/beyond-small/r3/orbAB_27_21.txt
  (first 27 lines: N ⊆ B, i.e. A-hubs; last 21 lines: N ⊆ A, B-hubs).
- Other round-2 results: adaptive single-hub growth (r2/d01/grow.c: each new hub must cover AND hit the distance-2 set of
  every existing hub) took 191 → 498 A-hubs; annealing over packings (r2/d15/anneal.c, moves insert/delete/replace/
  line-swap, energy −K + 1.5·conflicts) took 191 → 609 A-hubs; 17-neighbour hubs raise compatibility 0.937 → 0.957
  (r2/d04/hubpack17.c). Single hubs of different sides never conflict.
- Director's tools: research/squads/beyond-small/director/ (hubpack.c, merge_hubs.py; slab/scaffold design is the
  director's own line, do not duplicate).

Score = largest n with `research/squads/beyond-small/bin/apsp EDGES 17 5` → RESULT VALID. Save the orbit/hub files and
the exact build command.
