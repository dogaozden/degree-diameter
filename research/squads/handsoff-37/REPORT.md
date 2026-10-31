# handsoff-37: a hands-off Haiku squad on the bipartite (3,7) cell

Session on branch `claude/handsoff-37-d3d7-r13gzx`, Oct 31 2026, 15:39Z to about 21:30Z. Goal: a bipartite graph with
maximum degree 3, diameter 7 and more than 168 vertices. Experiment: Opus only coordinates (plans cards, checks in,
verifies, redirects); Haiku subagents do the searching. Target spend split about 50/50, measured by tools/session_usage.py.

## Result

**No record. The table value 168 stands.** No worker produced a graph with far = 0 at n >= 169, so nothing went to
`records/` and there was nothing for apsp.c to accept. Best per order (unordered pairs at distance > 7; every file
re-scored by the coordinator with `bin/score37`):

| n | best far | worker, structure | file |
|---|---|---|---|
| 169 | 144 | r2h, fixed radius-6 tree at a degree-2 vertex, involution | r2h/best169.edges |
| 170 | **46** | c1 (also c7, c8), C168.1 + one inserted vertex pair | c1/s170_k2_far46.edges |
| 172 | 76 | c6, polarity double cover, Z2 on a 43+43 base | c6/best172_polarity_z2.edges |
| 174 | 97 | c2, reduction of the n = 180 near miss | c2/best174.edges |
| 176 | 86 | c2, reduction of the n = 180 near miss | c2/best176.edges |
| 178 | 98 | c2, reduction | c2/best178.edges |
| 180 | 36 | r3c, S3 lift of a 15+15 base (same distance profile as the known C3 x S3 near miss: a rediscovery) | r3c/best/n180_S3_far36.edges |
| 182 | 126 | r2e, C7 lift of a 13+13 base, breakout tabu | r2e/best/n182_C7k13_far126.edges |
| 192 | 256 | r3f, C2 x C4 lift of a 12+12 base (old best 384) | r3f/best/n192_C2xC4k12_far256.edges |
| 196 | 224 | r2f, F21 = Z7 x| Z3 with a non-free order-3 part | r2f/best196_far224.edges |

Full board: `scoreboard.tsv` (FINAL_ROWS rows). Check-ins: `checkins.md`. Cards: `cards.md`.

## Spend (tools/session_usage.py, price-weighted "budget units")

FINAL_SPEND

Over time (from `checkins.md`):

| time (Z) | Opus | Haiku | Haiku share | note |
|---|---|---|---|---|
| 16:17 | 0.083 | 0.052 | 39% | setup was Opus-heavy |
| 16:46 | 0.102 | 0.076 | 43% | |
| 17:15 | 0.131 | 0.108 | 45% | |
| 17:37 | 0.193 | 0.142 | 42% | writing round-2 cards cost Opus 0.06 |
| 18:20 | 0.231 | 0.174 | 43% | |
| 18:47 | 0.275 | 0.200 | 42% | Haikus mostly waiting on long runs |
| 19:27 | 0.328 | 0.251 | 43% | "commands < 110 s" rule from 18:20 |
| 20:05 | 0.379 | 0.497 | 57% | Haiku spend rate about 10x round 1 |
| 20:43 | 0.434 | 0.804 | 65% | |

The split was set mostly by one operational detail, not by the cards. For subagents the Bash tool moves a foreground
command that runs longer than about 120 s to the background, and the Haiku then ends its turn and waits. In rounds 1 and 2
the Haikus ran 9-minute searches, so each spent most of its time idle: about 0.025 units per 30 minutes for all eight
together. From 18:20 the cards said "keep every command under 110 s and chain many runs". The Haikus then called tools
several times a minute, each call re-reading a context of 100-250k tokens, and the Haiku rate rose about tenfold (0.25 units
in 40 minutes). So the share went from 42% (under the 50% target) to 65% (over the 60% line) within an hour. On this meter
a Haiku token costs 1/40 of an Opus token, so 50/50 means the Haikus process about 40 times as many tokens as the
coordinator.

## Haiku runs

HAIKU_RUNS Haiku runs in three overlapping rounds (8 + 8 + 7), each with its own card, about 1h40-2h each, plus 3
resumes (nudges) and 1 redirect. Four were stopped or ended early: r2a (stopped by me while mid-run; it had written no
notes), r2b and r2d (idle for about an hour after their background runs ended; stopped), r3d (handed back early).

## What each card found

Round 1 (15:44-17:45Z):
- c1, surgery on C168.1 (exhaustive): every 2-edge insertion of a vertex pair (247) gives far >= 46, every 3-edge one
  (29,891) far >= 48. Repair (SA, tabu, LNS, ILS) never goes below 46; all starts funnel into the same far-46 graph.
  Growth by insertion + tabu: 172 far 80, 174 far 107, 176 far 122.
- c2, shrink the n = 180 near misses (beam of vertex-pair reductions + SA, ~150 restarts): 170 far 70. The near misses
  and all reduced graphs are strict local minima for 2-switches.
- c3, exact Z_p lifts as a randomized solver (jsearch, rsolve2, SAT with cadical / kissat): did not recover even the known
  Z7 lift of a 12+12 base at n = 168 (30M DFS nodes, Knuth estimate 2.4e11, SAT 8 min). Nothing at 170 or 182.
- c4, joint base + voltage tabu for lifts: finds 168 over C14 (6+6) in 14 s, stalls for bases with k >= 12; 192 far 272.
- c5, order-3 automorphisms with fixed vertices: 170 far 78. Found that C168.1 has 11 free order-3 subgroups and 56 with
  3 fixed vertices.
- c6, polarity double covers (canonical double covers of cubic graphs with loops) with a free Z5: diameter 7 is EASY at
  n = 140, 150, 160 (cost 0 in about a minute) but floors at far 80 at 170.
- c7, unstructured parallel tempering: calibration 150 far 19, 160 far 53; 170 far 46 from C168.1 + pair (same basin).
- c8, wildcard (LNS with exact re-matching; greedy growth of the Tutte 12-cage): 170 far 46 (same basin); cage growth is
  far 0 up to 136 and far 170 at 170.

Round 2 (17:25-19:40Z):
- r2a, other 160-168 seeds then insertion: stopped by me at 18:20 before it reported (it had made seeds at 160 but no
  notes); its question (does another seed have a better insertion floor?) was only partly answered by r3g.
- r2b, exact SAT repair of a region: radius-2 regions of the far-46 graph have no better completion (it is a local
  optimum); radius 3-4 instances do not finish in 500 s.
- r2c, polarity covers deeper: Z5 at m = 85 floors at cost 40 (far 80); exact re-solves of every 3-, 4-, 5-subset of base
  vertices (64.6M completions) and 210 6-subsets (404M) find nothing lower.
- r2d, Moore-tree / involution families: depth-2 plateau search from the far-46 graph (51M evaluations) finds nothing
  below 46; free-involution family at 168: far 106.
- r2e, lift tabu with breakout weights: best 182 (C7, 13+13) far 126 and 190 (C5) far 220.
- r2f, mixed free / non-free symmetry: C168.1 contains F21 = Z7 x| Z3 whose order-3 elements fix 3 vertices; a
  symmetric SA over F21-invariant graphs rebuilds a diameter-7 graph at n = 168 **in 3 s from scratch**, the only method in
  the job that did so without being given the graph. It does not carry over: 182 far 210, 196 far 224, 170 (D5) 155.
  SAT with the same symmetry did not solve 168 in 9 minutes.
- r2g, wildcard (orbit search for non-free colour-preserving groups of order 2 to 252): recovers C168.1 from its full
  colour-preserving group; at 170 nothing below far 165.
- r2h, n = 169 (the non-cubic case, fixed radius-6 tree at a degree-2 vertex): far 144 with an involution swapping the
  root branches.

Round 3 (18:20-21:15Z):
- r3a, non-free symmetric SA at 170 and 180: D5 (Z5 x| Z2, sigma 2^7 1^3) gives 170 far 60 (in 12 of 40 seeds); 180 far 180.
- r3b, breakout weights inside the symmetric search: R3B_RESULT
- r3c, breakout lift tabu at 170-180: C5 17+17 at 170 far 65; rediscovered the n = 180 far-36 near miss as an S3 lift
  (15+15) from scratch. R3C_EXTRA
- r3d, polarity covers with D5 symmetry: 170 far 130; the D5 restriction does not reach 0 even at m = 80.
- r3e, breakout weights with no symmetry from the n = 170 graphs: R3E_RESULT
- r3f, breakout at the 180 / 192 near misses: 192 far 256 (C2 x C4, 12+12; old best 384). R3F_EXTRA
- r3g, Z5-symmetric orbit insertion into n = 160 polarity covers: R3G_RESULT

## Small-structure versus large-structure cards

"Small" = few free parameters, exhaustive or exact methods, tight symmetry (c1, c2, c3, c5, r2b, r2f, r2g, r2h, r3a,
r3d). "Large" = big search spaces explored by local search (c4, c6, c7, c8, r2c, r2e, r3c, r3e, r3f, r3g).

- The Haikus did **better on the large cards** as engineering: they wrote, tuned and improved tabu / breakout /
  tempering engines steadily (c4 -> r2e -> r3c: C5 lift at 170 from far 110 to 65; the 180 near miss rediscovered from
  scratch; new bests at 182, 192, 196).
- On the small cards they were weaker whenever the card needed an exact solver to work: all SAT encodings (c3, r2b, r2f)
  and the randomized exact DFS (c3) failed even the n = 168 calibration, and the Haikus did not find the reformulations that
  would make them work. The small cards that needed only plain enumeration went well (c1's exhaustive surgery gave the
  best n = 170 of the job in its first 20 minutes; r2g's orbit DFS recovered C168.1).
- The one striking new fact came from a small card: r2f's non-free F21 symmetry makes the 168 graph easy to find.

## My view: hands-off versus an Opus-led squad

VIEW
