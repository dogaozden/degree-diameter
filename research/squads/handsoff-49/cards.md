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

---

# Round 2 cards (added as round-1 workers finish; same shared rules, 2 hours each)

## w9: bi-coset graphs of simple and perfect groups with larger stabilizers (follows w7)

Read `$H/w7/NOTES.md` first (w7's code `bicos.c`, `bicos2.c` and its table of exact minima). w7's lessons: a central H
just gives a Haar graph of G/H; connectivity needs <S^-1 S, H> = G; perfect groups without cyclic factors do best
(PSL(2,25) with |H| = 3: n = 5,200, cost 30, exact minimum; PSL(3,3), H an involution: n = 5,616, cost 64). Now go to
groups and stabilizers w7 did not try, with n = 2 |G| / |H| in 4,972..6,000:
M_11 (order 7,920) with |H| = 3 (n = 5,280); S_7 and A_7 x Z_2 (5,040) with H an involution (n = 5,040); A_8 (20,160)
with |H| = 8 (n = 5,040); PSL(2,q) with |H| = 3..6: q = 27 (|H| = 3: 6,552), q = 29 (|H| = 4: 6,090), q = 31 (|H| = 5:
5,952); PSigmaL(2,25) or PGL(2,25) (15,600) with |H| = 6 (5,200). With |H| > 2 a single double coset H s H can give
several neighbours (|H s H| / |H| = |H : H cap s H s^-1|), so the degree count must be done per double coset. Groups this
big do not fit a full multiplication table (N^2 x 2 bytes): represent elements as permutations (M_11 on 11 points, A_8 on
8, PSL(2,q) on the q+1 points of the projective line), index cosets by a canonical form (e.g. the image of a base set
under the element, or the smallest element of the coset), and build the coset graph directly. Then exhaustive search
(small |H| with few double cosets) or annealing over the choice of double cosets.

## w10: Haar graphs of centreless groups with small abelianization (follows w1)

Read `$H/w1/NOTES.md` first (w1's tables and code; A_7 is exhaustively ruled out, minimum cost 6). w1's lesson: low cost
goes with a small centre and a small abelianization G/G'. Groups nobody has tried yet, all centreless with |G/G'| <= 11
(n = 2|G| > 4,970): A_5 x AGL(1,7) (2,520), S_5 x (Z_7 x| Z_3) (2,520), Frobenius Z_17^2 x| Z_9 (2,601; Z_9 acting as
an element of order 9 in GF(289)*, as a 2x2 companion matrix over Z_17), Z_29^2 x| Z_3 (2,523), Z_3^5 x| Z_11 (2,673;
Z_11 acting on GF(243) by multiplication with an element of order 11, as a 5x5 matrix over Z_3), Z_19^2 x| Q_8 (2,888;
Q_8 inside SL(2,19)), Z_11^2 x| SL(2,3) (2,904; SL(2,3) inside SL(2,11)), ASL(2,5) = Z_5^2 x| SL(2,5) (3,000, perfect),
products of two Frobenius groups (e.g. (Z_7 x| Z_3) x (Z_13 x| Z_12), 3,276). Build tables with groups.py (`semi`,
`perm`, products) or your own generator (check closure, order and the centre), screen each with haar_tab for 60 s with
3 seeds, deepen the best. For any group at cost <= 4, write an exhaustive search up to automorphism like w1's exh.c.

## w11: exhaustive certification of the best metacyclic groups (works next to w2)

`$H/w2/` holds a screen of all 1,519 metacyclic groups Z_m x|_r Z_k of order 2,486..2,600 (files screenA.tsv,
screenB.tsv: N m k r |G/G'| best_cost seconds; deep.tsv: longer runs). Annealing floors were true minima in earlier
work, but a group whose cost-0 sets are rare could be missed by a 1.5-60 s anneal. Make it certain for the best groups:
for every group with screen cost <= 10 (start with the lowest), run the exhaustive search `python3 $H/tools/exh_meta.py
m k r | LIMIT=0 ONLYLOW=1 $H/tools/flift DIPOLE meta:m:k:r 4 9 eval` (DIPOLE = base file "2 4" then four lines "0 1";
read exh_meta.py's and flift.c's headers; exh_meta needs gcd(r-1, m) = 1: write your own orbit reduction for the other
groups, e.g. using automorphisms (a, j) -> (u a, j) only). Time one group first and estimate; split the work with
`--slice i/n` into foreground chunks of at most 540 s. Keep a table certified.tsv (m k r, minimum or "no cost 0",
seconds). Any cost-0 set is a record: build the edge list (sol2edges.py or flift OUT.edges) and run apsp at once.
Do not run haar_tab screens yourself (w2 does that); talk to no one, just read w2's files.

## w12: lifts of small bases over simple and centreless groups, with tabu (follows w8)

Read `$H/w8/NOTES.md` (w8's tools: wl2.c annealing and wt.c tabu for any base and group tables up to 4,096 elements;
tabu beat annealing by ~30% on a 2+2 base) and the shared lesson from w1 and w7: groups with a small centre and a small
abelianization do best. Earlier lifts in this squad used solvable groups (best: 3+3 base, n = 4,992, cost 4; 2+2 base
over AGL(1,13) x Z_8, cost 15). Lift k+k bipartite 4-regular bases (multigraphs allowed; enumerate them as w5 did in
`$H/w5/gen_matrix_bases.py`) over simple or centreless groups with b |G| > 4,970: PGL(2,11) (1,320) with 2+2 bases
(n = 5,280); PSL(2,11) (660) with 4+4 bases (5,280); PSL(2,8) (504) with 5+5 bases (5,040); A_6 (360) with 7+7 bases
(5,040); PGL(2,7) (336) or S_6 / PGL(2,9) / M_10 (720) with 8+8 or 4+4 bases (5,376 / 5,760); PSL(2,13) (1,092) with
3+3 bases (6,552). Build tables with groups.py (psl2, pgl2, perm). Screen many (base, group) pairs briefly, then run
tabu with restarts on the best 3. Report cost and far pairs.

## w13: the cost-4 wall at n = 4,992 (follows w5)

Several families stop at exactly n = 4,992 with cost 4: Haar graphs of meta 104 24 7 and meta 208 12 3 (w2; earlier
squad: the central involution (52, 0) is far in every optimum), and 2+2 lifts with base [[2,2],[2,2]] over meta 13 96 5
and meta 39 32 31 (w5: `$H/w5/out/t_mh2_1_1248_s31.edges`; w5 says the far pairs are only same-side pairs with
j = 0 mod 4). Read `$H/w5/NOTES.md`. Step 1 (analysis, at most 30 minutes): with farlist on two or three of these
graphs, find the exact obstruction: which group elements separate the far pairs, whether they lie in the centre, in a
characteristic subgroup, or in the kernel of a small abelian quotient. Step 2 (search): choose groups of order 1,248
(2+2 lifts), 832 (3+3), 624 (4+4) and 2,496 (Haar) that avoid the obstruction (e.g. no central involution, a 2-part that
is not cyclic, a different abelianization), and also orders a little higher (1,250..1,300 for 2+2), build them with
groups.py (products, semi, perm) or your own generator, and run w5's tabu (`$H/w5/tabu.c`, TABU=1) or flift on them.
A cost below 4 at n >= 4,972 is progress; cost 0 is a record.

## w14: bi-coset graphs of larger simple groups with bigger stabilizers (next to w9)

w7 and w9 work on bi-coset graphs (both sides = cosets of a subgroup H, edges by a union of double cosets; read
`$H/w7/NOTES.md`). w9 takes M_11, S_7, A_8 and PSL(2,q). You take other simple groups with |H| between 4 and 24, so
that a single double coset can give 2 or 4 neighbours and the graph is close to edge-transitive: PSL(3,4) (20,160)
with |H| = 7 (n = 5,760) or 8 (5,040), Sz(8) (29,120) with |H| = 10 (5,824) or 8 (7,280), PSU(3,4) (62,400) with
|H| = 24 (5,200), PSL(2,16) x| Z_4 = PSigmaL(2,16) (16,320) with |H| = 6 (5,440), PSL(2,49) (58,800) with |H| = 24
(4,900: too small) or 20 (5,880). Work with permutation representations (PSL(3,4) on the 21 points of PG(2,4); Sz(8) on
65 points; build the group from matrix or permutation generators and check its order), index cosets by a canonical
form, and count degree per double coset. Exhaustive over small sets of double cosets first, then annealing.

## w15: Haar graphs of order 2,500 = 4 x 5^4: P x| Z_4 with a fixed-point-free action (n = 5,000)

Lesson so far (w1, w7, w10): low cost goes with a small centre and a small abelianization. Order 2,500 is just above
2,485 and has many groups P x| Z_4 (P of order 625) that are centreless with abelianization Z_4 (when the generator
t of Z_4 acts on P with no non-trivial fixed points for t, t^2, t^3). Only the metacyclic ones (P = Z_625, and Z_m x| Z_k
shapes) were screened before. Build and screen the others with haar_tab (`tab FILE.bin`, 60 s, 3 seeds each):
- P abelian: Z_5^4, Z_25 x Z_5^2, Z_25^2, Z_125 x Z_5, with t acting as an automorphism of order 4 without fixed
  points: scalar x -> 2x on Z_5^4 (2 has order 4 mod 5), x -> 7x on Z_25 parts (7^2 = -1 mod 25), x -> 57x mod 125
  (57^2 = -1 mod 125), and non-scalar 4x4 matrices A over Z_5 with A^2 = -I (e.g. block diagonal [[0,-1],[1,0]] twice,
  or [[0,-1],[1,0]] with [[2,0],[0,2]] blocks); different A give different groups. Elements (v, a), product
  (v, a)(w, b) = (v + A^a w, a + b). Check the order, the centre (should be trivial) and closure.
- P non-abelian of order 625 (e.g. Heisenberg group mod 5 times Z_5, or mod 25 variants) with an order-4 automorphism
  acting without fixed points (e.g. (x, y, z) -> (2x, 2y, 4z) on the Heisenberg group, z the central coordinate).
- Also the same idea at order 2,496 = 2^6 x 3 x 13 and 2,508 = 4 x 3 x 11 x 19 if time allows (centreless,
  abelianization small).
Deepen the best 3 (5 min runs, several seeds), and write an exhaustive search up to automorphism (like w1's exh.c,
`$H/w1/`) for any group at cost <= 4.

## w16: grow the 4,970 graph through its quotients (follows w6)

The table graph `$H/seeds/valid4970.edges` is the Haar graph H(G,S) of G = Z_71 x|_49 Z_35 with S = {(0,0), (6,18),
(30,19), (30,22)} (pairs (a,j), product (a,j)(b,l) = (a + 49^j b, j + l); solution file `seeds/valid4970_meta71_35_49.sol`).
G has normal subgroups N = Z_71 (index 35), Z_71 x| Z_5 (index 7) and Z_71 x| Z_7 (index 5). So the same graph is a
voltage lift of the quotient H(G,S)/N: a 35+35 base (70 vertices) with voltages in Z_71, a 7+7 base with voltages in a
group of order 355, and a 5+5 base with voltages in a group of order 497. Plan:
1. Build the three quotient bases with their voltages (vertices (gN, side), edges (gN, A) ~ (s g N, B) with the voltage
   read off from coset representatives) and check that the lift rebuilds a VALID 4,970 graph (apsp).
2. Calibration: start flift / w5's tabu (`$H/w5/tabu.c`) / w8's wt.c from random voltages on these bases over the same
   groups. Do they find cost 0 again? If not, the optimizer is the bottleneck for bases this size (record how close).
3. Re-lift the same bases (and small modifications: change one or two base edges) over slightly larger groups: the
   5+5 base over groups of order 498..530, the 7+7 base over 356..380, the 35+35 base over groups of order 72..80.
   Prefer groups of the same shape (Z_p x| Z_k Frobenius, centreless, small abelianization). Start each search from the
   known voltages mapped into the new group where that makes sense.
A cost-0 lift with n > 4,970 is a record.

## w17: mixed-orbit graphs: G regular on side A, stabilizers of order 2 or 4 on side B (follows w9)

Haar graphs have G regular on both sides; bi-coset graphs (w7, w9, w14) have the same stabilizer H on both sides. New
family: G (order N >= 2,486, n = 2N) acts regularly on A = G and with point stabilizers of order 2 or 4 on side B, which
is a union of orbits G/H_i. An edge orbit G (e, s H_i) gives the edges (g, g s H_i): each A-vertex gets 1 neighbour from
it and each B-vertex xH_i gets |H_i| neighbours (g in x H_i s^-1). Degree 4 everywhere, |B| = N:
- type (2,2): B = G/H_1 + G/H_2 with |H_1| = |H_2| = 2, two edge orbits (s_1, s_2) into each;
- type (4,4,4,4): four orbits G/K_i with |K_i| = 4, one edge orbit each;
- type (2,4,4): one involution orbit with two edge orbits and two order-4 orbits with one each.
H_i must not contain a central element (a central involution z makes x and xz twins with the same neighbours, which
wastes vertices; the quotient then needs a 4-regular graph of diameter 4 on N/2 vertices, impossible). Use groups with
many non-central involutions or Klein subgroups and a small centre: A_7 (Haar minimum 6, w1), the order-2,496 and
2,520 metacyclic groups with even k, PGL(2,q) x Z_n, S_5 x F_21, A_5 x AGL(1,7), and w10's and w15's best groups
(read their NOTES.md). Roots: e in A and one point per B-orbit (G acts transitively on each orbit), so one evaluation
is 2-5 BFS runs. Exhaustive over (s_i) for fixed H_i when small, annealing otherwise. Compare with the Haar minimum of
the same group.

## w18: auditor: re-check every claim on the scoreboard (follows w13)

Do not trust any worker's numbers. For every line of `$H/scoreboard.tsv` (skip the header): check that the file exists
(if the path is a solution or voltage file, find the matching .edges file in the worker's folder or rebuild it with the
worker's documented command from its NOTES.md), then run `$H/tools/score48 FILE 4 9` and `$H/tools/apsp FILE 4 9` and
record: worker, claimed n, actual n, claimed cost, actual far pairs, actual diameter, max degree, bipartite, VALID or not,
and whether the claim holds (far pairs consistent with the claimed cost: for Haar/lift costs far = cost x N / 2 or as the
worker's NOTES.md defines it). Write `$H/w18/audit.tsv` (one line per scoreboard line) and a short `$H/w18/NOTES.md`
with the per-worker best verified near miss (smallest far pairs at n > 4,970 and lowest cost), and every discrepancy.
Also list, per worker folder, the certified (exhaustive) negative results claimed in NOTES.md with the command that
proves them. Re-run the audit on new scoreboard lines every 20 minutes until 02:50 UTC.
If any line is VALID at d = 4, D = 9 with n > 4,970: copy it to `$H/records/` at once and write it first in NOTES.md.

## w19: refinement ladder from the best Haar near misses (follows w12)

A Haar graph H(G,S) is also a voltage lift of a k+k base over ANY subgroup K of index k in G (restrict the right
action of G to K; the quotient has k vertices per side). The k+k voltage space is strictly larger than the Haar space,
so its minimum is <= the Haar minimum, and anything lower is a new non-Haar structure. Start from the best near misses:
- Z_101 x|_5 Z_25 (N = 2,525, n = 5,050, exact Haar minimum cost 2, w11): subgroups of index 5 (Z_101 x| Z_5, order
  505: a 5+5 base), index 25 (Z_101: 25+25) and index 101 (Z_25: 101+101; too big?);
- Z_104 x|_7 Z_24 and Z_208 x|_3 Z_12 (N = 2,496, n = 4,992, exact Haar minimum cost 4): subgroups of index 2, 3, 4, 6, 8
  (2+2 over 1,248 is w5's family, where cost 4 is also the floor; go to 3+3, 4+4, 6+6, 8+8).
Steps: (1) take an optimal S (w11's certified searches in `$H/w11/` or haar_tab with a few seeds; w13's file
`$H/w13/best_haar_104_24_7_c4.edges`), build the k+k base and its voltages over K (w16 in `$H/w16/` is writing similar
quotient code: read it, do not edit it), and check that the lift rebuilds the same graph with the same far pairs;
(2) run tabu (`$H/w5/tabu.c` TABU=1, `$H/w8/wt.c`, or `$H/w12/wtt.c` which aims moves at far pairs) from those voltages,
with restarts and perturbations; (3) also try the same from several different optimal S. Report the lowest cost per
(group, k). Cost below the Haar minimum at the same n is progress; cost 0 is a record.

## w20: a complete certificate for metacyclic Haar graphs of order 2,486..2,520 (follows w11)

Goal: the statement "no metacyclic group of order 2,486..2,520 has a Haar graph of degree 4 and diameter 9", proved by
computation. Read `$H/w11/NOTES.md` and `certified.tsv` (w11's exhaustive tool exh3 and its driver; 33 groups done) and
w2's group lists (`$H/w2/groups_all.txt`, `groups_ab.txt`, non-split list in w2/NOTES.md). (1) Derive and check a
D = 9 abelian-quotient bound like the D = 8 one in research/squads/big-squad-4-8.md (on branch
origin/claude/bipartite-4-8-squad-zmk3qt; the bound: in an abelian Haar graph with S = {0, s1, s2, s3}, count the values
reachable on each side within the allowed distances; a group with an abelian quotient larger than that count cannot
work). Verify the count by brute force. (2) List every metacyclic group (split and non-split) of order 2,486..2,520,
drop the ones the bound excludes, and certify the rest with exh3 (exhaustive up to automorphism), skipping those already
in w11's certified.tsv. Keep `$H/w20/certificate.tsv` (group, method: bound or exhaustive, minimum, seconds). A cost-0
set is a record: build the edge list and run apsp at once.

## w21: exhaustive minima for the best non-metacyclic groups (follows w10)

Annealing floors of the best non-metacyclic Haar groups are not yet proven. Make them exact with an exhaustive search
up to automorphism (w1's `$H/w1/exh.c`, w10's driver in `$H/w10/`; S = {e, r, b, c} with r over class representatives
under Aut(G), b and c over all elements): S_5 x F_21 (w10: classes 0..11 of 35 done, minimum 8 so far; finish 12..34),
then the best order-2,500 groups of w15 (read `$H/w15/NOTES.md`; do not edit its files), PGL(2,5) x Z_21 (w1: 7),
PSL(2,8) x Z_5 (8), A_5 x S_3 x Z_7 (8). Keep `$H/w21/exact.tsv` (group, order, minimum, classes covered, seconds).

## w22: wildcard: a family nobody in this squad has tried

Tried so far (do not repeat): Haar graphs of metacyclic, non-metacyclic, simple, centreless and order-2,500 groups;
lifts of 2+2 to 8+8 bases, of W(3), H(3) (impossible: girth 12), PG(2,3), the (4,5) 162 graph, random 6+6 bases;
bi-coset graphs with stabilizers of order 2-24 in PSL(2,q), PSL(3,3), PSL(3,4), M_11, S_7, A_8, Sz(8), PSU(3,3),
PSU(3,4); mixed-orbit graphs (w17); surgery on the valid 4,970 graph (floor 160 far pairs: every edge is critical for
~170 pairs); quotients of the 4,970 graph re-lifted over bigger groups (w16); index-k refinements of Haar near misses
(w19). Best near misses: Haar of Z_101 x| Z_25 at n = 5,050 with exact minimum cost 2; n = 4,992 cost 4 (central
involution far). Think of a different construction (for example a product-like or compound construction, a graph with
a non-regular group action not listed, a graph built from a finite geometry other than generalized polygons, or a
search over non-vertex-transitive graphs guided by the near misses), argue in NOTES.md why it might beat 4,970, then
build and test it.

## w23: order 2,500 groups P x| Z_4 (follows w15)

Read `$H/w15/NOTES.md` (tables in w15/tabs/, rebuild commands, auto15.py). w15's best: P = a maximal-class exponent-5
group of order 625 (inside U_4(F_5)) extended by Z_4 (group u4m_7): Haar cost 4 at n = 5,000, a floor across seeds.
(1) Make it exact: exhaustive search up to automorphism (w1's `$H/w1/exh.c` or w11's `$H/w11/exh3`; r over class
representatives under the automorphisms you can find, b and c over all elements). (2) Look at the far pairs of cost-4
states (farlist): which group elements separate them (central? an element of the Z_4 part?), and whether the same wall as
at 4,992 (a central involution) is at work. (3) Build the order-625 groups w15 did not cover (class-2 exponent-25
groups, other maximal-class ones), their order-4 automorphisms (auto15.py), and screen P x| Z_4 with haar_tab
(60 s, 3 seeds). Copy w15's files into your folder before changing anything.

## w24: an optimizer that can find known solutions on 5+5 bases (follows w16)

w16 found that the 4,970 table graph is a 5+5 lift over a group of order 497 (Z_71 x| Z_7, `meta:71:7:45`), and that
annealing, tabu and a smooth walk-count cost all stall at cost 68-98 on that base and group, where cost 0 exists. So for
bases bigger than 2+2 the optimizer is the wall. Read `$H/w16/NOTES.md` (quot.py builds the base and the known voltages).
Benchmark: from random voltages, reach cost 0 on that 5+5 base over meta:71:7:45. Ideas: large-neighbourhood search
(re-optimize 2 voltages exhaustively: 497^2 = 247,009 pairs, each evaluation is a few BFS runs on 4,970 vertices, so
a few seconds per pair with a bitset BFS); moves aimed at far pairs; solving first in the quotient Z_7 (the images of the
voltages in G/Z_71 must already give a good 5+5 lift over Z_7) and then lifting; restarts with a population (keep the
10 best, recombine voltages). Measure success rate and time on the benchmark. If a method reaches 0 on the benchmark,
run it on w16's best groups of order 498..530 (w16's tables) and the 7+7 base over orders 356..380.

## w25: final auditor and summary table (follows w18)

Part 1 (until 02:57 UTC): continue w18's audit (`$H/w18/audit.tsv`, `$H/w18/NOTES.md`; copy its method): every
scoreboard line added after 02:00 gets the same checks (score48 and apsp on the file, claimed vs actual n, far pairs,
diameter); append to `$H/w25/audit2.tsv`. Re-check every 15 minutes.
Part 2 (from 02:58 UTC, when the workers have finished): write `$H/w25/summary.md`: one row per worker w1..w24 (card
title from cards.md; start and end time; best n, cost and far pairs at n > 4,970, and whether the audit confirmed it;
exact or certified negative results with the command that proves them; the worker's own "next idea"), read from each
`$H/wN/NOTES.md`, the scoreboard and the audits. Then a short table per construction family (Haar metacyclic, Haar
other groups, lifts by base size, bi-coset, mixed-orbit, surgery, quotients/refinements): best verified near miss.
Also count lines of code each worker wrote (`wc -l` over its .c and .py files). Plain text, no claims you did not check.
Finish by 03:10 UTC and reply in at most 5 lines.
