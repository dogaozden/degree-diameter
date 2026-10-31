# handsoff-37: direction cards (round 1)

Goal: a bipartite graph with maximum degree 3, diameter 7 and MORE than 168 vertices (table value 168, upper bound 248).
Coordinator: an Opus session that plans, checks the scoreboard and verifies. Workers: Haiku subagents, one card each.

## Common rules (every worker reads this)

**Facts (proved or exhaustively checked earlier; do not redo):**
- Above 168 only cubic graphs matter (except n = 169): sides of equal size m = n/2, 85 <= m <= 124, every vertex degree 3.
- Diameter <= 7 iff every pair of SAME-side vertices is at distance <= 6. From a vertex there are 1 + 6 + 24 + 96 = 127
  non-backtracking (NB) walks of even length <= 6, so the same-side ball has at most 127 vertices. Diameter <= 7 iff every
  vertex v has excess R(v) = 127 - |same-side ball of radius 6| at most delta = 127 - m (delta = 42 at n = 170, 43 at 168).
  This is a local condition: only the radius-6 ball matters.
- Girth: n >= 194 forces girth >= 6, n >= 226 forces girth >= 8, n >= 242 forces girth >= 10.
- EXCLUDED by exhaustive search (do not search these): graphs with an automorphism of prime order >= 11; graphs with a
  colour-preserving group acting freely with <= 11 orbits per side (so every Haar / bipartite Cayley graph, every lift of a
  base with <= 11+11 vertices over any group); vertex-transitive and edge-transitive graphs. So any graph beating 168 has
  |Aut| = 2^a 3^b 5^c 7^d, and a free colour-preserving group has order <= n/24 (<= 7 at n = 170, <= 10 at n = 240).
- Heuristic calibration from earlier jobs: unstructured annealing reaches diameter 7 only up to about 130 vertices
  (n = 150: 58 bad ordered pairs after 60 s). Joint base + voltage annealing finds the 168 graph over C7 x| C3 (2+2 base)
  in < 1 s, over C14 (6+6 base) in 45 s, but NOT over C7 with a 12+12 base (stuck at 20). Best near misses:
  n = 180 far = 36 (C3 x S3 lift of a 5+5 base), n = 180 far = 90 (C30, 3+3), n = 192 far = 384 (Haar graph of order 96).

**Shared tools** (paths relative to research/squads/handsoff-37/):
- `bin/score37 FILE` scores an edge list (first number n, then one edge "a b" per line, vertices 0..n-1). Prints
  `n=.. edges=.. maxdeg=.. simple=.. bipartite=.. connected=.. far=F diam=..`; far = unordered vertex pairs at distance > 7.
  far = 0 (with maxdeg 3, simple, bipartite, connected) means diameter <= 7. Source: shared/score37.c (copy its BFS into
  your own code for speed; bit-parallel BFS, 64 sources at a time).
- `bin/apsp FILE 3 7` is the acceptance checker (prints RESULT VALID / INVALID).
- `shared/seeds/`: conder168.edges (the 168 record, arc-transitive, |Aut| = 504, girth 12), the near misses above.
- `shared/prior/`: earlier programs to read and reuse: d3D7_salift.c (joint base + voltage annealing), d3D7_sa3.c
  (unstructured annealing), d3D7_tabulift.c, d3D7_shrink.c, exact_jsearch.c / exact_zplift.c / exact_glift.c (exact
  voltage-lift searches), exact_bases_bK.txt (all connected cubic bipartite multigraphs on K+K vertices, K = 1..8, nauty
  multig -T format), *_liftedges.py, exact_fano_cfg_sa.c, d3D7_README.md and exact_README.md (how they are used).
  No GAP or nauty is installed; Python 3 and gcc are. `pip install networkx` works if you need it.

**Machine (shared by 8 workers and the coordinator, 4 cores, 15 GB):**
- At most ONE heavy process of yours at a time (a second one only for < 2 minutes). Always `nice -n 10`.
- Run long jobs in the foreground as `timeout 540 nice -n 10 ./prog ...` (Bash tool timeout 600000) so you see the result;
  chain several 9-minute runs rather than one long one. Memory <= 1 GB per process.
- Work only inside your folder `research/squads/handsoff-37/<worker>/` (plus appending to the scoreboard and copying
  candidates to records/). No git commands. Keep files small (< 20 MB each; put bulky output in `<worker>/out/`, which is not
  committed).

**Scoreboard:** `research/squads/handsoff-37/scoreboard.tsv`, tab-separated, one line per improvement, append only:
`worker<TAB>strategy (short)<TAB>n<TAB>far<TAB>file<TAB>time (date -u +%FT%TZ)<TAB>note`
e.g. `printf 'c3\tZ7 lift 13+13 dfs\t182\t40\tc3/best182.edges\t%s\tdepth 21/27\n' "$(date -u +%FT%TZ)" >> research/squads/handsoff-37/scoreboard.tsv`.
An improvement = a lower far at some n >= 170 than your previous best at that n, or your first graph at a new n.
Calibration results (n <= 168) may be logged too, with "calib" in the note. Every logged file must be an edge list that
`bin/score37` scores exactly as you report.

**If you get far = 0 at n >= 170:** run `bin/apsp FILE 3 7`; if it says RESULT VALID, copy the file to
`records/<worker>_n<N>.edges`, log it with note CANDIDATE, write how to rebuild it in your NOTES.md, and keep going
(try a larger n).

**Working style:** you own your card for a long stretch. Run `date -u` first and write your start time at the top of
`<worker>/NOTES.md`. Keep iterating for up to 2 hours: write code, run it, read the result, improve the code or switch to
the next idea on your card (or your own idea in the card's spirit), log, repeat. Do not stop early and do not report back
early because one idea failed; a failed idea goes in NOTES.md with its numbers and you try the next. Update NOTES.md at
least every 20 minutes (what you ran, the numbers, what you will try next). Stop after about 2 hours (check `date -u`), or
earlier only with a verified record. Your final reply to the coordinator: at most 8 lines (best n and far, file, the idea
that worked best, the most promising next step).

---

## Card c1: grow the 168 graph (surgery; small structure, exhaustive)

Start: shared/seeds/conder168.edges (C168.1, arc-transitive: every edge is equivalent, so you may fix the first edge).
1. n = 170, exhaustive: delete edges x1y1, x2y2 (x in A, y in B), add a new A-vertex a ~ y1, y2, b and a new B-vertex
   b ~ x1, x2, a. Fix the first edge, try all 251 second edges. Then the 3-edge version: delete x1y1, x2y2, x3y3, add
   a ~ y1, y2, y3 and b ~ x1, x2, x3 (no edge ab); fix the first edge, try all pairs of the other two (about 31,000).
   Score all of them with an in-process BFS in C. Record the distribution of far.
2. Repair: take the best 50-200 and run local search with 2-switches (edges ac, bd with a, b in A -> ad, bc, keeping the
   graph simple), first restricted to edges within distance 3 of the surgery, then unrestricted; accept improving moves,
   with annealing or tabu to escape.
3. n = 172 and up: repeat insertions (beam search: keep the best 20 graphs after each insertion + repair).
4. Variants: insert more vertices at once (delete 6 edges, add a 4-vertex path or a 6-cycle wired to the 12 loose ends);
   start from the near misses in shared/seeds instead.

## Card c2: shrink the near misses (surgery from above; small structure)

Start: shared/seeds/nm180_c3xs3_b5_14.edges (n = 180, far 36), nm180_c30_b31.edges (180, far 90),
nm192_haar96_65.edges (192, far 384). Goal: far = 0 at some n in 170..178, or lower far at 180 / 192.
1. Reduction move: delete two adjacent vertices a ~ b; their other neighbours a1, a2 (in B) and b1, b2 (in A) are
   reconnected by two new edges (b1a1, b2a2) or (b1a2, b2a1), keeping the graph simple: n -> n - 2. Enumerate every
   reduction (270 edges x 2 ways), score each, keep the best 20-50 (beam search), repeat down to n = 170.
2. After each level, repair the beam with a short tabu search over 2-switches focused on vertices that have far pairs.
3. At n = 180 itself: iterated local search (kick: 3-5 random 2-switches near far pairs, then greedy repair; accept if not
   worse). Earlier annealing and tabu on the far-36 graph found no improving move, so you need kicks or bigger moves.
4. Other reductions: remove a 6-cycle or a 2-path and rewire; remove a whole orbit of the near miss's symmetry.

## Card c3: exact Z_p lift search run as a randomized solver (small structure, exhaustive with symmetry)

A graph with a free automorphism of order p is a Z_p lift of a cubic bipartite base with k + k vertices, n = 2kp.
Open cases: p = 7 with k = 13 (n = 182), 14 (196); p = 5 with k = 17 (170), 18 (180). The exact program
shared/prior/exact_jsearch.c (builds base and voltages together, exact pruning on walk collisions; env SHARD=i/m,
SHARDDEPTH=d, PROBE=N for a Knuth estimate; read exact_README.md and the source for the arguments) could not finish
p = 7 (estimated 10^9 to 10^12 nodes). Your job: use it as a randomized solution finder.
1. Build it (gcc -O3 -march=native). Calibrate: p = 7, k = 12, D = 7 (n = 168) must have solutions (C168.1 has an
   automorphism of order 7). How fast does it find the first one? Use PROBE to estimate tree sizes.
2. Add randomization: random shard order with large m, random value order / random restarts with a node limit, and keep
   the deepest partial assignment. Complete the deepest partials greedily (any cubic completion), write the lifted graph,
   score it with bin/score37, log the best far per n.
3. Run p = 7, k = 13 and p = 5, k = 17 for long stretches (several 9-minute runs), then p = 5, k = 18 and p = 7, k = 14.
   Put node rates, estimates and depths reached in NOTES.md.

## Card c4: joint base + voltage annealing over small groups with big bases (large structure, heuristic)

A lift: base = cubic bipartite multigraph on k + k vertices, each base edge carries a voltage in a group H of order N,
n = 2kN. Only N <= n/24 is still open. Cost for a lift: for every base vertex u, the number of same-side lifted vertices
NOT reached by the NB walks of even length <= 6 from (u, 1); sum over u (cost x N = ordered far pairs). This is cheap:
walks from k base vertices, not from n.
1. Calibration (most important): reach cost 0 at n = 168 with H = C7, k = 12 (exists: C168.1 has an automorphism of
   order 7); then C6 (k = 14), C3 (k = 28). Earlier salift (shared/prior/d3D7_salift.c) got stuck at cost 20 for C7,
   k = 12. Try tabu search, parallel tempering, restarts from many seeds, moves that change a base 2-switch and the
   voltages on the touched edges together, and incremental cost updates.
2. Then the open cases: n = 170 (H = C5, k = 17), 176 (C4 or C2 x C2, k = 22), 180 (C6 or S3, k = 15; C5, k = 18),
   182 (C7, k = 13), 192 (C8, D4, Q8, k = 12). Log the best cost per n (convert to far = cost x N / 2 for the board, and
   write the lifted edge list).

## Card c5: order-3 symmetry with fixed vertices (non-free action; never searched)

All earlier symmetric searches assumed free actions. An automorphism s of order 3 may fix vertices: a fixed vertex
has its 3 neighbours in one 3-cycle of s (if a fixed vertex had a fixed neighbour, connectivity would make s trivial),
so fixed vertices are pairwise non-adjacent. At n = 170 (85 per side, not divisible by 3) a free order-3 action is
impossible, but s with exactly 1 fixed vertex per side (or 4) is possible; also n = 176 (88 = 1 mod 3), 182 (91).
1. Encode such graphs by a quotient: regular orbits (size 3, vertices (o, 0..2)) and fixed vertices; an edge between
   regular orbits o, o' with voltage t joins (o, i) to (o', i + t); a fixed vertex is joined to all 3 vertices of one
   regular orbit of the other side. Each regular orbit has 3 half-edge slots in the quotient (an orbit adjacent to a
   fixed vertex uses one slot for it).
2. Anneal / tabu over quotients (2-switches on the quotient, voltage changes), cost = far of the lifted graph (n = 170:
   one BFS per orbit representative is enough: far from (o, 0) times 3, plus the fixed vertices).
3. Variants: f = 4 fixed vertices per side; S3 = <s, involution> fixing a root vertex (rotational symmetry around a
   vertex: the radius-6 tree around the root is symmetric); n = 176, 182; order-2 automorphisms with fixed vertices or
   fixed edges.

## Card c6: canonical double covers / polarity (large structure)

A cubic bipartite graph with a side-swapping involution of polarity type is the canonical double cover of a 3-regular
graph M with loops allowed (M a symmetric 0/1 matrix, row sums 3, a loop M_ii = 1 counts once): A_i ~ B_j iff
M_ij = 1, n = 2m. The double cover has diameter <= 7 iff every pair i, j (i != j) of M is joined by a walk of EVEN length
<= 6 in M (then odd distances <= 7 follow). M must be non-bipartite. Cayley graphs M give Haar graphs (excluded).
1. Write a fast cost: number of unordered pairs {i, j} of M with no even walk of length <= 6 (far of the double cover is
   twice that). Bitset BFS over the "even" relation is cheap for m <= 124.
2. Anneal / tabu over M on m = 85, 86, 88, 90, ... vertices: moves = degree-preserving switches including loops (a loop
   at i and a loop at j can become edge ij, and back; edges ab, cd -> ac, bd). Calibration: m = 84 (n = 168): how close?
3. Variants: impose a free cyclic symmetry of order t on M (t = 2, 3, 5, 7 with m/t >= 12) to shrink the search; start
   from good non-bipartite cubic graphs; write the double cover as an edge list and check it with bin/score37.

## Card c7: unstructured local search with a strong engine (large structure)

Pure local search over all cubic bipartite graphs at n = 170, no symmetry. Earlier: shared/prior/d3D7_sa3.c (simulated
annealing with exact all-pairs cost) reached 58 bad ordered pairs at n = 150 in 60 s; the ceiling was about 130 vertices.
Your job is a much better engine:
1. Incremental cost: after a 2-switch only vertices within distance 6 of the 4 touched vertices change their balls; or
   maintain for each vertex its number of unreached same-side vertices and recompute only the affected ones.
2. Tabu search over 2-switches with move selection focused on vertices whose excess exceeds delta; long runs.
3. Calibrate at n = 150, 160, 168 (log best far with note "calib"), then n = 170, 172, 176.
4. Starting points: random; C168.1 with two vertices inserted (delete 3 edges x_iy_i, add a ~ y1, y2, y3 and
   b ~ x1, x2, x3); girth-maximized random graphs (build girth >= 10 first, then optimize far).

## Card c8: wildcard

Find an approach none of the other cards use. The others: c1 grow the 168 graph by surgery; c2 shrink the n = 180/192
near misses; c3 exact Z_7 / Z_5 lift search randomized; c4 annealing of lifts over groups of order <= 10 with big bases;
c5 order-3 automorphisms with fixed vertices; c6 canonical double covers of cubic graphs with loops; c7 unstructured
tabu search. Ideas you may take: Moore-tree completion (fix the radius-6 tree around a root edge or vertex, which must be
nearly a tree, and search only for the matching of its leaves, perhaps with a symmetry of order 2, 3 or 7 around the root);
SAT/ILP with a symmetry assumption (check whether a SAT solver can be pip-installed, e.g. python-sat); generalized hexagon
GH(2) incidence graph (126 vertices, girth 12, diameter 6) extended by new vertices; involutions with fixed edges; lifts
where the group acts with some fixed points of order 2. Pick one, say which in NOTES.md, and give it the full 2 hours.
