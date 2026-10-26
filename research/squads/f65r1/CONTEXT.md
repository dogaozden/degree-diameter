# Squad f65 round 1: shared context (read this first)

**Goal.** A bipartite graph with maximum degree ≤ 6 and diameter ≤ 5 on **at least 686 vertices**. The record is 684
(Loz, 2013 table). Bipartite Moore bound 1,562 (781 per side).

**Useful facts.**
- A connected bipartite graph has diameter ≤ 5 iff every two vertices on the same side are within distance 4.
- From one vertex at most 1 + 6·5 + 6·5³ = 781 same-side vertices lie within distance 4, so a side of ~343 vertices
  must be covered with redundancy ≈ 2.3. Random-like graphs leave ≈ 35 same-side vertices uncovered per vertex;
  only structure gets to 0.
- Haar graph H(G,S): vertices (g,A), (g,B), edges (g,A) ~ (s·g, B), s ∈ S, |S| = 6. Diameter ≤ 5 iff
  (S⁻¹S)² = G and (SS⁻¹)² = G. Voltage lift of a base multigraph B by group Γ: vertices (u,γ), edges (x,γ) ~ (y, a_e·γ).

**Already found / already ruled out (do not repeat these):**
1. Haar graphs by random-start annealing over hundreds of groups of order 343–362 (metacyclic Z_m⋊Z_k, Heis(7),
   Heis(3)×Z13, Z7⋊Z3×Z17, AGL(1,4)×Z29, AGL(1,5)×Z18, SL(2,5)×Z3, Z3³⋊Z13, …): best 2 uncovered elements. No more
   Haar annealing.
2. Voltage lifts by annealing (lift.c) of bases with ≤ 6+6 vertices, orders 686–714, ~60 groups (cyclic, metacyclic,
   affine, SL/PSL/PGL(2,p), products), 30 s runs: best cost 4.
3. FunSearch-style evolution of metacyclic lift/Haar programs (~2,300 Haiku calls): matched 684, never more.
4. Generalized polygons and buildings: GQ level graphs ≤ 510; all Weyl-distance graphs of buildings (q ≤ 5):
   best 630 (chambers of PG(3,2)); lifts of polygon incidence graphs fail (a cover of a girth-g graph has
   diameter ≥ g − 1); free quotients of the GH(5,5) incidence graph fail by counting; route-chart lifts ≤ 384.
5. The director is running, exhaustively, right now (do not duplicate): (a) every Haar graph H(K,S) with S invariant
   under an automorphism of K of order 2, 3, 5 or 6, for all non-abelian groups K of order 343–360 (best so far:
   cost 6, K = Z3³⋊Z13 with an order-3 automorphism); (b) bi-coset (coset) graphs of almost-simple groups such as
   PSL(2,13), PSL(3,3), A7, M11; (c) exhaustive Haar search over the five groups of order 343.

**Tools** (all in `/home/user/degree-diameter/research/fresh65/tools/`, already compiled; you may copy them into your
folder and modify the copies):
- `apsp EDGES 6 5`: the scorer. Edge-list file: first line n, then one `u v` per line (0-based). Prints
  `RESULT VALID d=6 D=5 n=…` or the reason (degree, not bipartite, diameter=6, disconnected).
- `lift`: voltage-lift annealer. `./lift search BASE 5 SECONDS SEED 8 OUT GROUP...`, `./lift check SOL EDGES`
  (writes the edge list), `./lift sample BASE 5 M GROUP...`. Groups: `cyc n`, `meta m k r` (Z_m⋊_r Z_k, r^k ≡ 1 mod m),
  `dih n`, `aff p a b c d k`, `aff3 …`, `sl p`, `psl p`, `pgl p` (p prime), products `G x H`. Base file: first line
  `k K` (K = number of base vertices, white ones listed as first endpoint), then `e x y` per edge (free voltage) or
  `e x y = ELEM`. Read the top of `lift.c` for details. `python3 bases.py random 2h 6 SEED` prints a random 6-regular
  bipartite base on h+h vertices.
- `bicoset.g` (GAP 4.12 is installed: `gap -q`) and `bicoset`: exhaustive scan of coset graphs. In GAP,
  `Read("bicoset.g"); ExportBicoset(G, L, R, "file.txt", "label");` (G a group, L, R subgroups of equal order) or
  `ExportOrbitHaar(K, alpha, "file.txt", "label");` then `MAXFIX=1 ./bicoset file.txt 6 5 OUTPREFIX` scans every
  union of L-orbits of total size 6 (prints a cost histogram; writes OUTPREFIX.edges for a cost-0 graph;
  `SAVEBEST=1` writes the lowest-cost one as OUTPREFIX.best.edges).
- Seeds in `/home/user/degree-diameter/research/fresh65/seeds/`: `d6D5_n684_evolve_g005c20.edges` (a valid 684-vertex
  graph, 6-regular), `d6D5_n630_A3_2_chambers.edges` (valid 630-vertex chamber graph of PG(3,2)),
  `d6D5_n702_orb3_351_12_nearmiss.best.edges` (702 vertices, 6-regular, diameter 6: each vertex has 3 same-side
  vertices beyond distance 4).

**Machine rules.** 4 cores are shared by ~17 processes. Single-threaded only; run anything heavy as
`timeout 600 nice -n 10 <cmd>`; at most ~1 GB of memory; no git commands; write only inside your own card folder
`/home/user/degree-diameter/research/squads/f65r1/cN/` (and append to the scoreboard). Total time box: about 25
minutes. Use Python only for setup; do the heavy loops in C (gcc -O3 is available) or numpy.

**Scoring and reporting.** Every candidate you claim must be written as an edge list and checked with `apsp`.
When done, append ONE line of JSON to `/home/user/degree-diameter/research/squads/f65r1/scoreboard.jsonl`:
`{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command>", "score": <n if VALID else 0>,
"valid": true|false, "best_invalid_n": <n of your best near miss>, "best_invalid_cost": <same-side ordered pairs at
distance > 4 in it, or uncovered count, say which in idea>, "next": "<one line: what to try next>"}`.
Then reply to the director in at most 5 lines.
