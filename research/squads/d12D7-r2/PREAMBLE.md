# Squad round d12D7-r2: shared preamble (read this first)

Job "cell-12-7" (Opus director, resumed session, 2026-10-25). Goal: a **bipartite graph of maximum degree 12 and
diameter 7** with as many vertices as possible. Table (DS14v2): 664,300. **Current best (this job): 693,100**, checked
all-pairs. The construction has a hard cap of 693,500, and this round looks for ways to reach the cap and to get past it.

## The construction (research/squads/d12D7/graphs/d12D7_n691660_CHECK.md and d12D7_n693100_CHECK.md)

1. **Main graph** (664,300 vertices): 5 copies ("levels" i in Z5) of the incidence graph of the split Cayley hexagon
   H(9) (66,430 points, 66,430 lines, 10 lines per point, 10 points per line, distance 6 between opposite elements),
   plus (p,i) ~ (phi(p), i+1) and (p,i) ~ (phi(p), i+2) for every point p, where phi is a duality (points -> lines).
   Vertex ids: (v, i) -> i*132860 + v, v < 66430 a point, v = 66430 + l a line.
2. **Freed points** F: the 7,300 points on the 730 lines of a Hermitian spread (pairwise opposite lines). A freed point
   loses its 10 matching edges, so each (p, i) and each (phi(p), i) gets 2 free slots. With F freed and nothing added,
   the main graph still has diameter 7. Freed points may be collinear (same spread line). The rule: F must contain no
   path p ~ u ~ w of collinear points on two different lines, because a freed point reaches its targets at another level
   through two hop points (at distance 2 and 4 on a geodesic), and that path frees both. The spread is the largest such
   set (7,300 = 66,430 * 10/91).
3. **Hubs**: a line-side hub is adjacent to one freed point vertex (p, i) at every level i (5 edges) plus up to 7 hubs
   of the other side; a point-side hub is adjacent to one freed line (phi(p), i) per level plus up to 7 hubs. A hub then
   reaches every main vertex within 7 and every hub of the other side within 7 through the main graph. Two hubs of the
   SAME side must be within 6: that is the only hard part.
4. **Hub graph = cluster-assisted Haar graph** (research/squads/d12D7/clhaar/): hubs (g, A) and (g, B), g in a group
   Gamma; edges (g, A) ~ (s g, B), s in S (|S| = 7). At each level the right cosets of an order-20 subgroup H_i sit on
   one spread line (2 hubs per point), so hubs of a coset are within 4 (2 if they share a point) through the main
   graph. All relations are left multiplications, so a single weighted BFS from e decides every pair; clhaar(P)
   anneals over S and the subgroups and reports cost = #elements of Gamma not within 6 (sides A and B). Cost 0 means
   a valid graph with n = 664,300 + 2|Gamma|.
   Results: PSL(2,9) x Z40 and PGL(2,9) x Z20 (|Gamma| = 14,400): cost 0 in seconds -> 693,100. PSL(2,19) x Z4
   (13,680): cost 0. SL(2,9) x Z20: stuck at 72. SL(2,11) x Z11 (14,520): stuck at 88, because every order-20
   subgroup there has trivial Z11 part, so clusters never change that coordinate. **Subgroups must "mix" the group.**
5. **Cap**: 730 spread lines x 20 slots = 14,600 hubs per side -> 693,500. Each hub needs 5 main edges (one per
   level), and 73,000 freed matching edges is the most the no-path rule allows.

## Tools (build with gcc -O2/-O3; sources in research/squads/d12D7/)

- `research/d10D7/hexgen2.c`: `./hexgen2 9` writes hex/hex_q9.bin (the H(9) incidence structure; run it in your folder).
- `clhaar/clhaarP.c`: `clhaarP PGRP 7 5 SECONDS SEED OUT` -> cost line; at cost 0 writes OUT and OUT.hubs3.
  PGRP format: `N r e h nsub`, then r lines of N ints (generator k as the permutation y -> g_k*y, LEFT multiplication),
  then nsub lines `c a_1 ... a_h` (a subgroup of order h = 20 given by its element indices, c an involution in it).
  `clhaar/grp2pgrp.py` converts gen_group.py output (matrix group x Z_n) into PGRP; `clhaar/gen_group.py` makes
  SL/PSL/PGL(2,q) x Z_n for q prime or 9.
- `clhaar/x5gen3.c`: `x5gen3 hex/hex_q9.bin SOL HUBS3 OUT.edges` builds the full graph (SOL =
  research/frontier/sols/d12D7_hex9_spread730_clhaarPSL9x40_n693100.sol).
- `tools/srccheck.c`: `srccheck EDGES 12 7 1 664300 n` BFS from every hub; "SOURCES OK" = all hub rows within 7
  (main-main pairs are already fine). About 1 minute per 30,000 sources on 1 thread; ~1 GB memory.
- `tools/orbcat.c`: `orbcat EDGES 7 1 5 B` counts pairs at distance > 7 by type, using the level shift (BFS from level
  0 and the hubs; B = vertices per level, 132,860). Needs the level shift to be an automorphism (no hubs, or hubs with
  the same owner at every level). About 5-8 minutes on 1 thread for the full graph.
- `tools/x5del.c`, `tools/mksol.py`: build variants (deleted base vertices; a new freed list with the same phi).
- Sets: `sets/L9_hspread730.txt` (spread line ids), `sets/F9_spread730_7300.txt` (freed points, line by line).

## Rules for every card

- Work only in `research/squads/d12D7-r2/<card>/`. No git commits. No edits outside your folder.
- The machine (4 cores, 15 GB) is shared by 8 cards and Opus: THREADS=1, `timeout 900 nice -n 10` for anything heavy,
  at most ~1.5 GB of memory, at most one heavy process at a time.
- Time box: about 40 minutes of work.
- When done, append ONE line of JSON to `research/squads/d12D7-r2/scoreboard.jsonl`:
  `{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <number>, "valid": true|false, "next": "<one line>"}`
  and reply in at most 5 lines. "valid" means you ran the checker named in your card and it passed.
