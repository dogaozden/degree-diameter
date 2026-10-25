# chartlift tools (route-chart lifts at diameter 5)

The lift of a properly k-edge-coloured bipartite controller C by a chart (A_c, b_c) over F_q^4: vertex (u, x),
x in F_q^4; a controller edge u--v (u on side A) of colour c gives (u, x) ~ (v, A_c x + lam b_c), lam in F_q.
Degree k*q, order |V(C)| * q^4.  It has diameter <= 5 iff every same-side pair of fibres is joined by walks of
length 4 whose reachable sets cover the target fibre.  Controller-level sufficient conditions (CHART_LIFTS.md):
distance-4 pairs need a nonbacktracking 4-walk with a nonsingular colour pattern; distance-2 pairs are free when the
chart's pencil for their colour pair is complete; a vertex's own fibre needs a nonsingular 4-cycle unless the chart
covers the diagonal with backtracking walks.

Build: `gcc -O2 -o ctrl_search ctrl_search.c -lm` (same for chart_anneal.c, graph_anneal.c, square_anneal.c, apsp.c,
bfs_all.c).  Python: python3 with numpy only for nothing essential (stdlib suffices).

| file | what |
|---|---|
| gf.py, gftab.py | GF(q) tables (q = 2,3,4,5,7,8,9,11,13,16); `python3 gftab.py q tables/gfq.txt` |
| chartlib.py | Chart class; reachable sets from the walk rules; singular patterns, pencils, diagonal, 4-cycle patterns |
| chart_anneal.c | anneal a chart: `./chart_anneal tables/gfQ.txt K SECONDS SEED WS WP WD out.txt` (cost = WS*singular + WP*pencil misses + WD*diagonal misses; WD=0 when controllers have 4-cycles). Wall-clock seconds; writes out.txt on every improvement |
| chartflags.py | `python3 chartflags.py CHART.txt q k out.flags` (singular patterns, pencil and diagonal flags for ctrl_search) |
| ctrl_search.c | anneal voltages of a base multigraph over a group: `./ctrl_search BASE GROUP FLAGS SECONDS SEED [outprefix]`. BASE: "r" then r*k lines "i j [colour]"; GROUP: `cyclic:N` or a table from groups.py; FLAGS: from chartflags.py or the word `universal`. Prints best_cost (0 = the lift has diameter <= 5 by the sufficient conditions) and writes outprefix.volt / outprefix.ctrl when cost is 0. `VOLT=v1,v2,... ./ctrl_search ...` evaluates given voltages |
| bases.py | `python3 bases.py k r outdir`: all connected k-regular bipartite base multigraphs on r + r vertices |
| groups.py | `python3 groups.py NAME out.txt`: cyc:n, dih:n, dic:n, prod:a:b, meta:m:n:t, q8, s3, a4, s4, a5, sl:p, psl:p, gl:p |
| lift.py | `python3 lift.py CONTROLLER.ctrl CHART.txt q k out.edges` builds the lift (apsp.c format) |
| apsp.c, bfs_all.c | independent all-pairs checkers: `./apsp out.edges DELTA 5` must print RESULT VALID |
| make_builder.py | writes a self-contained builder for a found lift |
| graph_anneal.c, square_anneal.c | edge-switch annealers for k-regular controllers with 4-cycles everywhere (universal charts) |

Charts: `charts/r2_kK_qQ.txt` (pencil-complete, fewest singular patterns found): (3,3) 0, (3,4) 0, (4,2) 48 (diagonal
covered, so no 4-cycles needed), (4,3) 26, (4,4) 22 (the squad's `chart_u8_squad165.txt` has 8), (5,2) 230, (5,3) 112.

## Round 3 tools (`r3/`, CHART_LIFTS.md Lemma 5, Theorem 11, Propositions 12–13, Theorem 14)

| file | what |
|---|---|
| r3/mkgroups.py | `python3 r3/mkgroups.py LO HI outdir`: Cayley tables of every cyclic, Z_a x Z_b, dihedral, dicyclic and metacyclic (`meta:M:N:t`) group of order LO..HI |
| r3/batch.sh | `BIN=... PAR=n SEED=s r3/batch.sh JOBFILE FLAGS SECONDS OUTDIR`: runs ctrl_search jobs ("BASE GROUPFILE TAG" lines) n at a time |
| r3/chart_anneal2.c | chart_anneal with env INIT (start chart), T0, STALL, TAU |
| r3/chart_anneal3.c | chart_anneal2 plus env MOVES=star: moves are transvections fixing b_c (change only the star collineation), right transvections and b entries; output gauged to A_0 = I |
| r3/chart_shear.c, r3/chart_eval.c | anneal only the shear/scale freedom (changes nothing at D = 5, Lemma 5); evaluate many charts from stdin |
| r3/cdesc/star_cd.py | coordinate descent: re-optimise one letter's star collineation over all of PGL(3,q) at a time |
| r3/cdesc/star_cd_ctrl.py | the same with a fixed controller in the objective (env CTRL=volt, GROUP=table) |
| r3/diag43/ | exhaustive both-diagonal searches: diag_exhaust3.py + diag_joint.c (k = 4, q = 3), diag_coinc.py (coincident points), diag_k3q2.py (k = 3, q = 2), diag_charts.py, diag43_allsing.py, classify_sing.py |
| r3/dpmin/ | dp_prep.py + dp_min.c: exact minimum of singular patterns over (4,2) charts covering both diagonals |
| r3/ctrl_exh.c | ctrl_search with EXH=1 exhaustive voltage scan (written by squad card r2-c6); r3/exh_d12.sh drives the (12,5) Haar scan |
| r3/gen_ctrl_cost.py | score any k-regular graph (JSON or edge list) as a controller for a diagonal-covering chart |
| r3/make_haar_builder.py | self-contained builder for a lift of a Haar graph of a metacyclic group (group law as a formula) |
| r3/allk_family.py | checks for Theorem 14 (pattern relabelling for k <= 8, exact controllers) |
| r3/alt_opt.sh | `r3/alt_opt.sh q k BASE GROUPFILE CHART ROUNDS T_ctrl T_chart OUTDIR`: alternate voltage annealing (chart fixed) and controller-aware chart descent until cost 0; r3/alt_opt2.sh adds env MAXC (stop after round 1 if the cost is above it) |
| r3/alt348.sh | the (4,3) version: score the voltages against all 348 labelled singular sets (r3/flags43/) instead of a chart descent |
| r3/alt_run10.sh, r3/alt_run10b.sh, r3/alt_run15.sh | one-group drivers for (10,5) and (15,5) Haar queues (job lists r3/alt_jobs_10*.txt, r3/alt_jobs_15.txt; summaries r3/alt_10.log, r3/alt_15.log; run folders r3/alt/) |
| r3/graphs/ | builders, edge files and check outputs of the round-3 records |
