# Squad sd5-r1: shared rules (read first)

Goal: a bipartite graph with maximum degree 6 and diameter 5 on MORE than 684 vertices (cell (6,5); the table value
684 is unbeaten). A Haar graph H(G,S) with |S| = 6 needs |G| >= 343.

Background (read research/selfdual-d5/README.md and research/d75-raise/README.md, section "How: self-dual connection sets"):
Haar graph H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B). Diameter <= 5 iff X X = G, Y Y = G and Y Y S = G,
X = S^-1 S, Y = S S^-1. If S is a union of orbits of psi(x) = c^-1 beta(x)^-1 (an index-2 extension of G), the graph is
a bipartite Cayley graph and X X = G is enough. The director's tool research/selfdual-d5/src/sdk (K=6) enumerates ALL such
sets (types: f psi-fixed elements + m psi-pairs, f + 2m = 6) for every group, and is sweeping every non-abelian group of
order 343-450 right now; types with too many sets are only randomly sampled (SAMPLED in the TYPE lines). Do NOT re-run
sdk on plain SmallGroups lists; each card is a DIFFERENT family or method.
Known so far: a valid degree-6 diameter-5 graph on 672 vertices (SL(2,7) = SmallGroup(336,114), 38 sets, calibration;
research/selfdual-d5/logs/calib/K6_336_114.out). Closest at >= 686 vertices: SmallGroup(352,50) = C11 x (a group of
order 32), self-dual type (6,0) (6 involutions in the Cayley connection set): |G \ X X| = 1 (all of that type searched).
Most groups of order 343-370 miss by 4-30 elements. An earlier exhaustive search found NO Haar graph of degree 6 at all
on 686-720 vertices (|G| = 343-360), so look at |G| >= 361 for Haar graphs, or at non-Haar families.

Machine: 4 cores shared with the director's sweep (which has priority) and 7 other cards. THREADS=1; run anything heavy
as `timeout 900 nice -n 15 <cmd>`; at most ~1.5 GB of memory; no git commands that change anything (git show of other
branches is fine); write only inside research/squads/sd5-r1/<card>/ ; use TMPDIR=<your folder>/tmp. Time box: about 25
minutes of wall-clock.

Tools (repo root /home/user/degree-diameter):
- research/selfdual-d5/src: export_sd.g (GAP export: table, inverses, ALPHA/EXT extension records), sdk.c, brute.c, apsp.
- research/d75-raise/src: export.g (GAP export with automorphism classes of order 2, 3, 4, 5, 7 and centralizers),
  haar75.c (valency 7 hard-coded: exh = automorphism-invariant sets, anti = self-dual sets, order-4 types), bic75.c
  (bi-coset graphs |H| = |K| = 2, valency 7), lift22.c (4-vertex-base lifts), dd_meta.c (formula-only metacyclic).
- branch claude/d75-raise-optimization-v25kr8, folder research/squads/d75-r2/: c1/bsd75.c (self-dual bi-coset graphs),
  c2/sym22.c (self-dual 4-vertex-base lifts), c4/anneal.c (tabu inside the self-dual family; re-found the (7,5) records
  in 60 s). Get them with `git show origin/claude/d75-raise-optimization-v25kr8:research/squads/d75-r2/c4/anneal.c`.
- GAP 4.12 with the full SmallGroups library: `gap -q -c 'N:=360;; ID:=118;; OUT:="x.ht";;' <script.g>`.
Scorer: `research/selfdual-d5/src/apsp EDGES 6 5` -> last line "RESULT VALID d=6 D=5 n=N" (all-pairs BFS, no symmetry
assumed). Edge list format: first line = number of vertices, then "u v" per edge. Calibrate any new tool first (e.g. it
must re-find a valid graph on SL(2,7), 672 vertices, or another known case), and say whether it passed.

Scoreboard: append ONE line of JSON to research/squads/sd5-r1/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <vertices if valid, else best
cost (uncovered elements)>, "N": <vertices of the best graph or attempt>, "valid": true|false, "calibrated": "<one line>", "next": "<one line>"}
A VALID graph above 684 vertices: keep the edge list in your folder and set "valid": true. Reply in at most 5 lines.
