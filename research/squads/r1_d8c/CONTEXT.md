# Squad round 1 of job own-d8-compound (2026-10-26): shared context for every card

Read this file, then your card. Work only in your card folder `research/squads/r1_d8c/cN/`.

## The problem

H(q) = split Cayley hexagon (generalized hexagon of order (q,q)): N = (q^6-1)/(q-1) points, N lines, q+1 lines per
point, q+1 points per line. I = I(H(q)) is its incidence graph: bipartite, (q+1)-regular, diameter 6, girth 12, 2N vertices.
Facts: if d(x,y) <= 5 there is ONE geodesic; if d(x,y) = 6 (x, y "opposite") there are q+1 geodesics, one through each
neighbour of x. Point-line distances are 1, 3, 5; same-type distances 0, 2, 4, 6. Sizes |Gamma_i(x)| = (q+1)q^(i-1)
(i <= 5), |Gamma_6(x)| = q^5. The lines through a point p lie in a plane pi_p of PG(6,q); points at distance <= 4 from
p are exactly the points of the quadric in the hyperplane p^perp (b(p, x) = 0).

Table values at diameter D = 8 (2013, credited to Delorme-Gomez-Quisquater "DGQ", construction unpublished/unknown):
(Delta, 8) = 5*floor((q+5)/2) * 2N(q) with Delta = q+3: (10,8) = 30*39,216 (q=7), (12,8) = 35*132,860 (q=9),
(14,8) = 40*354,312 (q=11), (16,8) = 45*804,468 (q=13), also (11,8) = 30*|I(H(8))| (q = 8: floor((8+5)/2) = 6).
So the graph is "m copies of I(H(q)) plus 2 extra edges per vertex", m = 5k, k = floor((q+5)/2) = 2 + floor((q+1)/2).
At small q the same formula gives m = 20 (q=3, Delta 6), 20 (q=4, Delta 7), 25 (q=5, Delta 8), 30 (q=7, Delta 10).

A bipartite graph has diameter <= 8 iff every vertex is within distance 7 of every vertex of the other colour class.

**Goal of this round:** find a STRUCTURED design (a rule, not a random draw) that reaches more copies than random
search does, ideally the DGQ value, so that we learn the mechanism. Then it must generalize to q = 7 (m >= 31 beats
the (10,8) table). Score of a card = the largest m with an EXACT check COST 0 (all sources, or a source set that meets
every orbit of a symmetry you can justify) at the card's q, at Delta = q+3 (or q+2 if the card says so).

## What is already known (do not repeat)

- Uniform random voltages (cyclic lift of I(H(q)) + 2 random matchings): m = 11-12 at q = 5, 10-12 at q = 7, 12-14 at q = 11.
  (Check here: q = 3 random Z_m lift works up to m = 16 at least.)
- Simulated annealing over all voltages: q = 3: m = 28 found (beats 20: q = 3 is too small to show structure);
  q = 5: m = 20 stalls at cost 900, m = 25 at cost ~19,000. Symmetric (Singer torus) annealing: m = 17 at q = 7 and 11.
- D = 7 level skeleton Z5 x Z_k (points at level i joined to phi(p) at levels i+1, i+2; zero hexagon voltages; random or
  annealed sheet shifts): fails (q = 5, k = 5: cost 17,887). 183 level skeletons Z_L x Z_k: <= 12 at q = 5.
- Random "rainbow bundle" hexagon voltages, projective-parameter-mod-m voltages, Singer index, ratio colours,
  geometric matchings (flag, distance 3, distance 5, involutions), non-abelian groups (dihedral, dicyclic, Frobenius,
  S4, Heisenberg): no better than random.
- Star product I(H) * C_m with rotations, and "same-element hops" (two semi-edges per element, dihedral lift):
  fail at m = 8-12.
- Lemma (proved, d10D8 notes): ANY two matchings sigma1, sigma2 with voltages 1 and 4 in Z_10 and zero hexagon
  voltages give diameter <= 8: 10 copies for free.
- Opus analysis (this job): with zero hexagon voltages (or any coboundary), the walks that reach a target for every
  choice of the matchings give at most about 2q + 7 copies; DGQ has 2.5q + 12.5. So DGQ must use non-trivial hexagon
  voltages (a genuine cover of I) and/or matchings with geometric structure, and/or vertices that are not copies.
- Guaranteed walks of length <= 7 from point p to line y with arbitrary matchings sigma_t (t = 1, 2): p~>y (1);
  p->sigma_t(p)~>y (1, or q+1 if y is opposite sigma_t(p)); p~>sigma_t^-1(y)->y (1 or q+1); p->l->sigma_t^-1(l)~>y for
  the q+1 lines l on p; p~>sigma_t(x)->x->y for the q+1 points x on y; plus 8 two-jump walks. Total 4q + 17 in the worst
  case. In the D7 skeleton (+1, +2) level 0 gets only ONE guaranteed walk: this is why that skeleton fails.
- Haar graphs (Cayley-type) for (10,8) are being ground elsewhere: do not run Haar searches.

## Counting hints (unexplained, maybe useful)

- k = floor((q+5)/2) = 2 + (number of disjoint pairs among q+1 objects); for even q one object is left over. So a
  natural guess: per level, 2 "plain" sheets + one sheet per PAIR of lines through a point (or points on a line).
- For odd q, m*2N = 5*(#flags + 4N): per level, the flags of H(q) plus 2 copies of the points and 2 of the lines.
- m = 10 + 5(q+1)/2: the free Z_10 lemma plus (q+1)/2 extra sheets per level.
- A route through a neighbour z of x that works for every target EXCEPT those whose geodesic from x starts at z would
  explain pairs: two neighbours in the same sheet always cover everything.

## Tools (all in research/squads/cells/d10D8_work/, already compiled; build commands in each file header)

- `hex/hex_q{q}.bin` for q = 2, 3, 4, 5, 7, 8, 9 (`./hexgen2 q` makes others). `hexlib.py`: `load(q)` returns
  N, LP (line -> its q+1 points), PL (point -> its q+1 lines), coord (7 coordinates over GF(q) per point; for q = p
  prime the field elements are 0..p-1; for prime powers see hexgen2.c field encoding). `dist_from_point(p, LP, PL)` BFS.
- `glift FILE [all|r:K:seed|i:list] [verbose]`: exact diameter-8 test of a lift by Z_m (m <= 64) or the dihedral group
  D_n (2n <= 64). File: "Z m" or "D n", then V, then V colours (0 point, 1 line), then darts "u v a" (voltage a;
  (u,g) ~ (v, g*a)). Example generator: `gen.py` (family lev = the D7 level graph; check: m = 5, 6 pass).
- `lifteval FILE 8 all` (Z_m, m <= 64) and `liftevalw` (m <= 1024): bipartite base "nA nB m" then "a b v" lines.
- `gcheck EDGES D [all|r:K:seed|range:a:b]`: explicit graph (first line n, then "a b" edges); counts pairs at distance
  > D from the chosen sources; OpenMP. Use this for designs that are not group lifts (permutation voltages, extra
  vertices, hubs). If your graph has a symmetry (e.g. the 5 levels), sources in one orbit-transversal give an exact
  answer.
- `apsp_mt EDGES d D T`: the coordinator's all-pairs checker (exact diameter, bipartite, max degree).
- pysat (CaDiCaL) is installed for SAT encodings.

## Machine rules

About 4 cores and 15 GB are shared by ~16 cards and Opus. So: `export OMP_NUM_THREADS=1`; run anything heavy as
`timeout 900 nice -n 10 <cmd>`; at most 1.5 GB of memory; no git commands; write only inside your card folder.
Time box: about 25 minutes of work in total. Prefer q = 3, 4, 5 for screening (exact checks take seconds) and q = 7
only for a design that already works at q = 5.

## Report

Append ONE line of JSON to `research/squads/r1_d8c/scoreboard.jsonl`:
`{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command that reproduces the best check>",
"q": <q>, "score": <largest valid m, or 0>, "cost_at_next": "<cost at the next m tried>", "valid": true|false,
"next": "<one line: what to try next>"}`
Then reply in at most 5 lines.
