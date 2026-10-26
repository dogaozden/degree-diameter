# Squad d3D7, round 1: shared brief (read this first, then your card)

## Goal

Find a cubic (every degree ≤ 3) bipartite graph with diameter ≤ 7 on **n ≥ 170** vertices. The published record is
168 (Conder–Nedela, 2012). The bipartite Moore bound is 254. Any valid graph with n ≥ 170 is a new record. n is even,
and for a cubic bipartite graph both sides have n/2 vertices.

Useful fact: a cubic bipartite graph has diameter ≤ 7 iff every two vertices **on the same side** are at distance ≤ 6.

## Tools (repo /home/user/degree-diameter, folder research/d3D7/, all built)

Read `research/d3D7/README.md` (one screen). In short:
- `research/d3D7/bin/salift p GROUPS id seed secs [T0 T1 out.sol]`: anneals a voltage lift of a p+p cubic bipartite
  base multigraph over the group `id` in the table file GROUPS, moving base edges and voltages together. n = 2pN.
  Good temperatures: T0 = 10, T1 = 0.3 (the defaults). Source: `research/d3D7/salift.c` (~110 lines, easy to copy and change).
- `research/d3D7/bin/sa3 n seed secs [T0 T1 init.edges out.edges]`: anneals an unstructured cubic bipartite graph
  (edge switches), exact all-pairs cost in ~5 µs at n = 170. Source `research/d3D7/sa3.c`.
- `research/d3D7/bin/liftx BASE GROUPS 7`: exhaustive lifts of one base over every group in a file.
- Group tables: `research/d3D7/groups/g<N>.txt` for N = 2..64 and 85..127: blocks `G N id name` followed by N rows of the
  multiplication table (row a, column b = index of a·b; index 0 is the identity). `groups/a<N>.txt`: Aut(G)-orbit
  representatives. GAP 4 with the SmallGroups library is installed (`gap -q`), if you need other groups.
- `research/d3D7/seeds/conder168.edges`: the record graph (168 vertices). It is the lift of the 2+2 base
  (edges 0-2, 0-2, 0-3, 1-2, 1-3, 1-3) over SmallGroup(42,2) = C2 × (C7 ⋊ C3) with voltages 0 21 0 0 5 2
  (`python3 research/d3D7/liftedges.py research/d3D7/bases/b22.txt research/d3D7/groups/g42.txt 2 0 21 0 0 5 2`).
  |Aut| = 504 (arc-transitive), girth 12.
- `research/d3D7/bin/apsp FILE 3 7`: the independent checker. Edge-list format: first line n, then "u v" per edge.

## Already done (do not repeat)

- Exhaustive, every group of the order (GAP SmallGroups), all negative (no diameter-7 graph):
  every Haar graph (1+1 base) of every group of order 85–127 (this also covers every bipartite Cayley graph on
  170–254 vertices); every lift of the 2+2 base over every group of order 43–63; every lift of every 3+3 base over every
  group of order 29–42; 4+4 bases over groups of order 22–31 and 5+5 bases over 17–21 are running (no hit so far).
- Every vertex-transitive cubic graph on 170–254 vertices (Potočnik–Spiga–Verret census): none is bipartite with
  diameter 7. The best bipartite ones have diameter 8 (n = 180, 192, 216, 234).
- Plain annealing of unstructured graphs (sa3) reaches only ~130 vertices (cost 2 at n = 130, cost 58 at n = 150).
- salift calibration at n = 168: finds a diameter-7 graph with C7 ⋊ C3 (p = 4) in < 1 s and with C14 (p = 6) in ~45 s;
  with C7 (p = 12) it is stuck at cost 20 after 90 s. So small groups with big bases need a better search.
- An earlier lab job (Oct 23) annealed lifts of all bases up to 6+6 (200 random 7+7) over "generic" groups for orders
  170–200, 20 s each: best cost 10 (n = 176, a 4+4 base over Z22).

## Machine rules (important)

- 4 cores and 15 GB are shared with about 12 other processes. Run **at most one heavy process at a time**, always as
  `timeout 900 nice -n 10 <cmd>`, using at most 1.5 GB of memory. Single-threaded only.
- Work only in your folder `research/squads/d3D7-r1/<card>/` (you may read anything in the repo). No git commands
  that change anything (no commit, no checkout, no stash). No network.
- Time box: about 25 minutes of wall-clock in total. Then stop and report.

## Verify and report

- A claimed graph must be an edge list that passes `research/d3D7/bin/apsp FILE 3 7` with `RESULT VALID` and n ≥ 170.
  Save it in your folder.
- When done, append exactly ONE line of JSON to `research/squads/d3D7-r1/scoreboard.jsonl` (use `>>`, one line):
  `{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "n": <n of
  the best attempt>, "cost": <best cost at that n, 0 = valid>, "cost_def": "<what the cost counts>", "valid":
  true|false, "file": "<edge list path or empty>", "next": "<one line: what to try next>"}`
- Then reply in at most 5 lines.
