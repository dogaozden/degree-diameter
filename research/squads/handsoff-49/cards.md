# handsoff-49: Haiku squad cards (round 1)

Goal of the whole squad: a bipartite graph with maximum degree 4, diameter 9 and **more than 4,970 vertices** (the table
value for the bipartite degree-diameter cell (4,9)). Any n >= 4,972 with diameter 9 is a new record.

## Shared rules (every worker reads this)

Repo root: /home/user/degree-diameter. Squad folder: research/squads/handsoff-49/ (below: `$H`).
You are one worker `wN`. Your own folder is `$H/wN/`; write all your code, logs and notes there.

**Tools** (already compiled in `$H/tools/`; copy a .c file into your folder before changing it):
- `apsp EDGES d D` : the independent checker (all-pairs BFS, 20 ms on 5,000 vertices). Prints `RESULT VALID d=4 D=9 n=...`
  or `RESULT INVALID` and the exact diameter. `verify.sh EDGES` runs it at D = 9 and D = 8.
- `score48 EDGES d D` : same checks, also counts far pairs (`far=`). `farlist EDGES D` lists far pairs. `edgecrit` = damage
  of deleting one edge.
- Edge-list format everywhere: first line `n`, then one edge `u v` per line, vertices 0..n-1.
- `haar_tab d D seconds seed K OUT GROUP... n` : annealing over Haar graphs H(G,S), |S| = d, S contains e; edges
  (g,A) ~ (s g, B). GROUP = `meta m k r` (Z_m x|_r Z_k), `tab FILE.bin` (any group table), `sl q`, `psl q`, `pgl q`, `agl1 q`,
  `prod G1 G2`, `cyc`; the trailing `n` multiplies by Z_n (use 1). Cost 0 = valid. Calibration: `haar_tab 4 9 30 1 8 out
  meta 71 35 49 1` finds the 4,970 table graph (cost 0) in 3.5 s. `python3 sol2edges.py SOL OUT.edges` turns a solution
  (meta or tab, n = 1) into an edge list.
- `python3 groups.py SPEC OUT.bin` : group multiplication tables (cyc, meta, dih, semi, sl2, psl2, pgl2, agl1, heis, perm,
  direct products "A x B"); `python3 groups.py SPEC` prints order, involutions, centre. `abc.py`: abelian-by-cyclic groups.
- `lift BASE GROUP d D seconds seed [K] [OUT]` and `flift ...` (faster, bipartite bases only): annealing over voltage
  assignments of a base multigraph (BASE text file: `b m` then m lines `u v`), GROUP = `cyc:n`, `meta:m:k:r` or a table
  .bin; OUT.edges = the lift. Both have MAXB 64 base vertices and MAXE 256 base edges (copy and raise them if needed).
  `flift BASE GROUP 4 9 eval < VOLTAGES` scores voltage lines; `exh_meta.py` enumerates Haar sets of a metacyclic group up
  to automorphism. Read the comment block at the top of each .c file for details.
- Seeds in `$H/seeds/`: `valid4970.edges` (the table graph, Haar of meta 71 35 49), `near4992_meta104_24_7.edges` (Haar
  graph of Z_104 x|_7 Z_24, n = 4,992, 4,992 far pairs: the central involution is far in every optimum),
  `hexagon_q3.json` (split Cayley hexagon H(3): 364 points, 364 lines, each line a list of 4 point ids),
  `d4D5_162.edges` (the (4,5) record graph, 162 vertices).

**Known from earlier squads (do not repeat as is):** metacyclic Haar graphs just above order 2,485: order 2,496 (meta 104
24 7) floor cost 4, order 2,525 (Z_101 x|_5 Z_25) proven minimum cost 2 (exhaustive). 15-minute cards got: Frobenius
Z_p x| Z_k 5,306 / cost 10; PSL/SL/PGL x Z_n 5,040 / 7; AGL(1,q) x Z_n 5,060 / 14; abelian-by-cyclic 5,256 / 10;
2+2 lifts 5,020 / 24; 3+3 and 4+4 lifts 5,022 / 36; Cayley 4,992 / 152; coset graphs 6,072 / 96. Those were short runs on
an overloaded machine; deeper, smarter runs are the point now.

**Machine:** 4 cores, 15 GB, shared by 8 workers. Always `nice -n 10`, THREADS=1, at most ONE heavy process at a time,
memory under 1.5 GB. Run searches in the foreground as `timeout 540 nice -n 10 <cmd>` (a Bash call can last at most 10
minutes). Do not use `sleep` to wait. Keep tool output short (`tail -3`, `grep RESULT`); never print big files.
No git commands. Do not edit files outside your folder, except appending to the scoreboard.

**Scoreboard:** every time you improve your own best, append ONE tab-separated line to `$H/scoreboard.tsv`:
`printf "%s\tw3\t<strategy, short>\t<n>\t<cost or far pairs>\t<VALID|no>\t<path of edges or solution>\n" "$(date -u +%H:%M)" >> $H/scoreboard.tsv`
Columns: time, worker, strategy, n, cost (your search's cost) or far pairs, VALID only if `apsp EDGES 4 9` printed
RESULT VALID, file. Prefer near misses with n > 4,970; the score to beat is "valid at n > 4,970", then lowest cost.

**Notes:** keep `$H/wN/NOTES.md` short and current (update it at least every 20 minutes): what you tried, best result,
what you would try next. The coordinator reads it instead of asking you.

**If you get RESULT VALID at d = 4, D = 9 with n > 4,970:** copy the edge list to `$H/records/wN_n<n>.edges`, put the
exact rebuild command in NOTES.md, add the scoreboard line, and **keep going** to raise n. Do not stop.

**Duration:** you own your card for a long stretch: keep iterating for **2 hours** from your start time (write it at the
top of NOTES.md; check `date -u`). Do not report back early, do not ask questions; decide yourself. When something does
not work, change the idea (a new group family, a new base, a new move, a smarter cost) rather than only re-running. At the
end, finish NOTES.md and reply in at most 5 lines: best n / cost, file, and the one idea you would try next.

---

## w1: Haar graphs of groups that are NOT metacyclic, orders 2,486..2,700

Haar graph H(G,S), |S| = 4, G of order N in 2,486..2,700 (n = 2N > 4,970). The table graph is a Haar graph of a
metacyclic group, and metacyclic groups just above it are stuck at cost 2-4, so look at other group shapes:
Z_p^2 x| Z_k (`semi p k a b c d`, a 2x2 matrix of order dividing k), abelian-by-cyclic (abc.py), Heisenberg-like
groups x cyclic, AGL(1,q) x Z_n, SL/PSL/PGL(2,q) x Z_n with q small, direct products of two non-abelian groups,
Z_m x| Z_k x Z_l with non-coprime factors, groups given by permutations. Build tables with groups.py (order <= 65,535),
run `haar_tab 4 9 ... tab FILE.bin 1`. Plan: enumerate many groups, screen each for about 20 s with 2 seeds, rank by
cost, then give the best 5 longer runs (3-5 min, several seeds), and keep adding new group shapes. Note which group
properties (number of involutions, centre, abelianization size) go with low cost: an abelian quotient that is too big
forces cost > 0.

## w2: Haar graphs of metacyclic groups, a complete sweep of orders 2,486..2,600

All groups Z_m x|_r Z_k with m*k = N in 2,486..2,600, r^k = 1 mod m, r != 1 (one r per cyclic subgroup <r> of the units
is enough; also include r with gcd(r-1, m) != 1), plus non-split ones you can build as tables. Screen each with
`haar_tab 4 9 15 seed 8 OUT meta m k r 1`, 2 seeds; keep a table (m, k, r, best cost) in your folder. Deepen the best 10
(5 min, 4 seeds). For any group whose floor is 1-2, try to prove or break the floor: run `exh_meta.py m k r | flift
<base> meta:m:k:r 4 9 eval` with `LIMIT=1 ONLYLOW=1` (base = two vertices joined by 4 parallel edges: file "2 4" then
four lines "0 1"; read exh_meta.py's header). Order of work: N just above 2,485 first.

## w3: lifts of the generalized quadrangle W(3) (the (4,4) Moore graph, 80 vertices) over groups of order 63..80

Base: the point-line incidence graph of the symplectic quadrangle W(3): points = the 40 points of PG(3,3); lines = the 40
lines that are totally isotropic for the form x0 y1 - x1 y0 + x2 y3 - x3 y2. 80 vertices, 160 edges, girth 8, diameter
4. Lift it over a group G of order 63..80 (n = 80 |G| = 5,040..6,400): each base edge gets a voltage, edges
(u, x) ~ (v, g x). Groups: cyclic, meta (e.g. Z_7 x|_2 Z_9 = meta 7 9 2, Z_13 x|_4 Z_6 = meta 13 6 4), Z_8 x Z_8, heis 4? (use groups.py), etc.
Copy flift.c or lift.c into your folder and raise MAXB to 128 and MAXE to 512. Write the base file yourself. Ideas
beyond plain annealing: put voltage 0 on a spanning tree; restrict to voltage assignments invariant under a symmetry of
the base (a subgroup of PSp(4,3) acting on points and lines, so you search fewer voltages and need fewer roots); also
lift the incidence graph of other 4-regular bipartite girth-8 graphs if you find them.

## w4: lifts of the split Cayley hexagon H(3) (the (4,6) Moore graph, 728 vertices) over small groups

Base: `$H/seeds/hexagon_q3.json` (364 points, 364 lines, each line = 4 point ids): incidence graph, 728 vertices, 1,456
edges, girth 12, diameter 6. Lift over Z_7 (n = 5,096), then Z_8, Z_9, Z_3 x Z_3, Z_10, ... (n = 728 k). Why it might
work: same-side pairs in the lift need walks of length <= 8 in the base covering all k voltages, opposite-side pairs
walks of length <= 9; for k = 7 there are about 25 base walks of length <= 8 per same-side pair, so random voltages
fail on ~15% of pairs and an optimizer may fix the rest. You must write your own evaluator: for each root u (728 of
them) a BFS over the base where each base vertex carries a k-bit mask of reached voltages (one machine word, the group
acts by rotation for cyclic groups); cost = number of (root, vertex, voltage) triples not reached within 8 (same side)
or 9 (other side). Make it incremental or at least fast in C (-O3), then anneal (or tabu search) over the 729 cotree
voltages. Reduce the work with symmetry: H(3) has automorphisms of order 7 and 13 (find one acting freely, e.g. by
searching for a permutation of points that maps lines to lines); voltages invariant under it need roots only per orbit.

## w5: lifts of mid-size bases (5+5 to 8+8 vertices) over non-abelian groups of order 311..500

Our (3,10) record 810 came from a 5+5 cubic base lifted over C3 x He3. Same recipe at degree 4: base = a 4-regular
bipartite multigraph on b = 10..16 vertices (simple or with parallel edges; e.g. K_{4,4} plus structure, the
4-regular bipartite circulants, the incidence graph of a (b/2)_4 configuration, random 4-regular bipartite graphs of
large girth), group G of order N with b N > 4,970: b = 10 needs N >= 498, b = 12 N >= 415, b = 14 N >= 356, b = 16
N >= 311. Groups: heis p x cyc, meta, semi, agl1 q x cyc, psl2 7 x cyc 3 (504), sl2 5 x cyc n, products (groups.py
tables). Use flift (bipartite bases, fast). Screen many (base, group) pairs for 20-30 s, deepen the best. Prefer groups
with few involutions and a small abelianization.

## w6: surgery on the valid 4,970 graph and on near misses

Start from `$H/seeds/valid4970.edges` and add vertices: delete 4 edges, add two new vertices a (side A) and b (side B),
join them to the freed endpoints (each new vertex gets 4 edges; keep it bipartite and simple), giving n = 4,972, then
run a local search with degree-preserving bipartite 2-switches (replace edges xy, uv by xv, uy) that minimizes the
number of far pairs (pairs at distance > 9). Write it in C; a full all-pairs count is ~20 ms (bit-parallel BFS as in
apsp.c), and a faster incremental count (only BFS from vertices near the changed edges, or sampled roots first) will let
you try many more moves. Choose the 4 deleted edges well (far apart, low edgecrit damage). Also try: start from the
near miss `near4992_meta104_24_7.edges` (4,992 far pairs, each vertex has one far partner) and look for switches that
fix many far pairs at once, e.g. equivariant switches under a subgroup of the graph's symmetry.

## w7: bi-coset graphs (Haar graphs over cosets of a small subgroup)

Generalize Haar graphs: group G, subgroup H of order 2 or 3, both sides = the right cosets Hg, and (Hg, A) ~ (H s g, B)
for s in a set S that is a union of (H,H)-double cosets, chosen so that every vertex has degree 4 (count neighbours,
not elements). n = 2 |G| / |H|, so |G| must be > 2,485 |H| (about 4,972..5,400 for |H| = 2, 7,458..8,000 for |H| = 3).
Groups: SL/PSL/PGL(2,q) x Z_n, S_5 x Z_n, A_5 x Z_n, meta, semi, products (groups.py; also meta with even k so that an
involution exists). Write a fast evaluator in C (BFS on the coset graph, using vertex-transitivity on each side: only
two roots are needed), then anneal over the choice of double cosets. An earlier 15-minute card reached n = 6,072 with
cost 96, so this family has room at larger n.

## w8: wildcard: an approach none of the other cards uses

The other cards are: w1 Haar graphs of non-metacyclic groups; w2 metacyclic Haar sweep; w3 lifts of the GQ(3,3)
incidence graph over groups of order 63-80; w4 lifts of the GH(3,3) incidence graph over groups of order 7-13; w5 lifts
of 10-16-vertex bases over groups of order 311-500; w6 surgery (add vertices to the valid 4,970 graph, then 2-switch
local search); w7 bi-coset graphs. Pick something else and go deep. Options if you have no better idea: lifts of the
(4,5) record graph `d4D5_162.edges` over groups of order 31..40 (n = 5,022..6,480); lifts of the PG(2,3) incidence graph
(26 vertices, the (4,3) Moore graph) over groups of order 192..220; lifts of 2+2 or 3+3 bases over non-abelian groups
of order 830..1,300 with a smarter optimizer than plain annealing; canonical double covers of non-bipartite 4-regular
graphs of diameter <= 8 with suitable odd girth.
