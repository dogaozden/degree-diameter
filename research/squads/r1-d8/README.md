# Squad round r1-d8 (job thm-d8table): structured lifts of the generalized hexagon H(q) at diameter 8

## The problem
The bipartite degree-diameter table has, at D = 8, the cells (Δ, 8) = M·|GH(q)| with Δ = q+3 and
M = 30, 30, 35, 40, 45 for q = 7, 8, 9, 11, 13 (M = 5·floor((q+5)/2)), and (13,8) = 15·|GH(11)| (Δ = q+2).
|GH(q)| = 2(q^6-1)/(q-1) is the order of the incidence graph of the split Cayley hexagon H(q) (diameter 6, girth 12,
(q+1)-regular). The construction (Delorme–Gómez–Quisquater, unpublished) is unknown. Natural model: an M-fold lift of
B = H(q) + j extra point->line perfect matchings ("hops"), degree q+1+j, voltages in Z_M (or Z_M1 x Z_M2).

Random voltages fail badly (all sources checked, liftdiam):
- j=2, q=3,4,5: random lifts reach M ~ 18, 14, 12 (DGQ formula: 20, 20, 25). At q=7 random reaches ~13 vs DGQ 30.
- Z_5 x Z_k with polygon-cover Z_5 part (hop k gets (t_k, label), t=(1,2)) and random Z_k labels: k ~ 3, 3, 2 at q=3,4,5.
So DGQ is strongly structured. YOUR JOB: one structured idea, implemented and scored.

## Tools (all in research/theorems/d8/, run from there)
- `gh.py`: `H = gh.load(q)` (q = 2,3,4,5,7,8,9,11 cached). H.N points = H.N lines. H.lines[k] = the q+1 point ids
  on line k; H.through[p] = the q+1 line ids on point p; H.P[p] = the 7 coordinates (in GF(q), field tables in H.F:
  H.F.ADD, H.F.MUL, H.F.INV; for prime q plain mod-q arithmetic works) of point p on the quadric
  X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q). Vertex ids for lifts: points 0..N-1, lines N..2N-1.
  `gh.flags(H)` = list of (point, N+line). `gh.write_base(path, 2N, M1, M2, edges)` with edges (u, v, a, b) =
  dart u->v carrying voltage (a, b) in Z_M1 x Z_M2. `gh.distances(H)` = all-pairs distance matrix (q <= 5 only).
- `./liftdiam base.txt 8 THREADS [SRC_STEP]` (compile: `gcc -O3 -march=native -o liftdiam liftdiam.c -lpthread`):
  exact BFS from every base vertex (or every SRC_STEP-th) in the lift; prints `unreached_pairs` (0 = diameter <= 8)
  and `max_ecc`. q=5, M=25: about 2 s with 1 thread. q=7, M=30: minutes; use SRC_STEP 13 for quick looks.
- `models.py`, `models5k.py`: examples of building bases (random models). `unreached_profile.py base q srcs`:
  classify misses by (H(q)-distance, first group coordinate) — useful to see what your structure fails on.
- Symmetry available: the diagonal torus T = {diag(a0,a1,a2,1,1/a0,1/a1,1/a2): a0 a1 a2 = 1} of G_2(q) preserves H(q)
  in these coordinates ((q-1)^2 elements).

## What a lift needs (guaranteed walks)
For a point x and line y (opposite colour, need length <= 7), with hop k at point p: (p,g)->(s_k(p), g+t_k(p)) and
H(q)-voltage phi, these walks ALWAYS exist (they only use d(point,line)<=5, d(line,line)<=6, d(point,point)<=6):
x->s_k(x)~>y ; x->b->s_k^{-1}(b)~>y (b on x) ; x~>s_k^{-1}(y)->y ; x~>s_k(a)->a->y (a on y) ; x->s_k(x)~>s_l^{-1}(y)->y ;
x->s_k(x)->s_l^{-1}(s_k x)~>y (k!=l). Between opposite H(q)-elements there are q+1 geodesics (different voltages if
the H(q)-voltages have holonomy); otherwise geodesics are unique. Near pairs (H(q)-distance <= 3) have only one
H(q)-walk of length <= 7, so they must be reached through hops.

## Machine rules
4 cores and 15 GB shared by 9 sessions: THREADS=1, `timeout 900 nice -n 10 <cmd>` for anything heavy, <= 1.5 GB RAM,
no git commits, no edits outside your card folder `research/squads/r1-d8/<card>/` (you may copy tools into it).

## Scoreboard
Append ONE json line to `research/squads/r1-d8/scoreboard.jsonl`:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "q": Q, "j": J, "M": M,
 "unreached": U, "score": "<largest M with unreached 0 for this q,j, or best unreached at the target M>",
 "valid": true|false, "next": "<one line>"}
Then reply in at most 5 lines.
