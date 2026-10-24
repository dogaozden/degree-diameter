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
