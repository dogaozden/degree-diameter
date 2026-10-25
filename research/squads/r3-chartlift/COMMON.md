# Squad r3-chartlift: shared brief (read fully, ~4 minutes)

You are one of 8 Haiku agents in a research lab on the bipartite degree-diameter problem: build a bipartite graph of
maximum degree DELTA and diameter 5 with as many vertices as possible. Repo: /home/user/degree-diameter.
Tools: research/theorems/chartlift/ (README.md there) and research/theorems/chartlift/r3/ (new this round).
Work ONLY inside your card folder research/squads/r3-chartlift/cN/ (create it). No git commands. Do not edit anything
outside your folder except appending your one scoreboard line.

Machine: 4 cores shared by 9 agents. Run at most ONE heavy process at a time, single-threaded. Prefix heavy commands
with `timeout 900 nice -n 10`. Memory < 1.5 GB. Delete *.edges files after checking them. Never use `pkill -f` with a
pattern that could match your own shell; kill by PID if you must. Generate group tables only for the orders you need
(r3/mkgroups.py LO HI with a narrow range) and delete your gtab folder when you finish (they are regenerable).

## The construction (route-chart lift) and what changed this round
Controller C: k-regular bipartite, properly k-edge-coloured, m vertices per side. Chart: matrices A_c and vectors b_c
over F_q (fibre F_q^4). Lift: vertex (u, x), x in F_q^4; a controller edge u--v of colour c gives (u, x) ~ (v, A_c x +
lam b_c) for lam in F_q. Degree k*q, order 2*m*q^4. `ctrl_search` anneals voltages of a base multigraph over a group;
its cost counts controller pairs the chart fails to connect; **cost 0 means the lift has diameter <= 5**, which you then
confirm on the lift itself with the all-pairs checker.

NEW: a chart whose "diagonals" are covered (closed backtracking walks reach the whole fibre) and whose pencils are
complete lets the controller have NO 4-cycles. Then plain Haar graphs (base = k parallel edges, file
bases5/k5r1_000.txt for k=5, bases4/k4r1_000.txt for k=4; make your own `1` + k lines `0 0` for other k) over
metacyclic groups work very well: for (15,5) (k=5, q=3) the Haar graph of Z26 x|3 Z6 (order 156) gave 25,272 vertices
(old record 20,736). Metacyclic groups Z_M x|_t Z_N with N = 4..8 did best; dicyclic groups did badly.

## Commands (run from research/theorems/chartlift/)
- compile once into your folder F: `gcc -O2 -o F/ctrl_search ctrl_search.c -lm`; same for apsp.c, bfs_all.c and
  `gcc -O2 -o F/chart_anneal2 r3/chart_anneal2.c -lm`.
- groups: `python3 r3/mkgroups.py LO HI F/gtab` writes Cayley tables of all cyclic, Z_a x Z_b, dihedral, dicyclic and
  metacyclic (`meta:M:N:t`) groups of order LO..HI into F/gtab/ and prints "name file" lines.
- controller search: `F/ctrl_search BASE GROUPFILE FLAGS SECONDS SEED F/OUTPREFIX` (SECONDS wall clock, 40-120).
  Prints `best_cost=...`; writes OUTPREFIX.volt/.ctrl when cost is 0. m = r*|G| (r = first line of BASE).
- several jobs: `BIN=F/ctrl_search PAR=1 r3/batch.sh JOBFILE FLAGS SECONDS F/runs` (JOBFILE lines "BASE GROUPFILE TAG").
  Use PAR=1 (one process) because the machine is shared.
- chart flags: `python3 chartflags.py CHART.txt q k F/out.flags` prints "singular S pencil fails P diag A B"; you need
  pencil fails 0 and diag True True for Haar controllers.
- chart annealing: `INIT=start_chart.txt T0=6 STALL=60000 TAU=15000 F/chart_anneal2 tables/gfQ.txt k SECONDS SEED 1 100 100 F/out.txt`
  (cost = singular + 100*(pencil and diagonal misses)/q^2; INIT optional; it prints `best=... sing=S unc_pencil=0 unc_diag=0`
  when pencils and diagonals are fine). Then make flags with chartflags.py (must say pencil fails 0, diag True True).
- build and check a lift: `python3 lift.py F/OUT.ctrl CHART.txt q k F/x.edges` then `F/apsp F/x.edges DELTA 5` must
  print `RESULT VALID`; also `F/apsp F/x.edges DELTA 4` should print INVALID. Then `rm F/x.edges`.

Existing charts (pencil-complete, both diagonals covered; flags beside each, same name .flags):
- (4,3): r3/k4q3_diag_cls0.txt .. cls6.txt — PROVED: every (4,3) chart covering both diagonals has exactly 16 singular
  patterns; these 7 files are the 7 different singular sets up to relabelling letters. Use their .flags files.
- (5,3): r3/k5q3_pd_star23.txt (92 singular; best), r3/k5q3_pd102.txt (102), r3/k5q3_pd112.txt (112).
- (5,2): r3/k5q2_c5_216.txt (216 singular; flags: make them with chartflags.py), charts/r2_k5_q2.txt (230).
- (4,2): charts/c4s2_k4_q2.txt (48; PROVED optimal among coincidence-free configurations).
New chart annealer: r3/chart_anneal3.c; run with env MOVES=star (moves only the star collineations; much better than
single-entry moves): `MOVES=star INIT=start.txt T0=4 STALL=60000 TAU=20000 F/chart_anneal3 tables/gfQ.txt k SECONDS SEED 1 100 100 F/out.txt`.

Current best (vertices) and what is known:
- (12,5) 10,368 (Haar m=64). PROVED by exhaustive scan: no Haar graph of order 65..81 works with any of the 7 (4,3)
  chart classes (best cost 2). So m >= 65 needs a base with r >= 2 vertices per side (m = r*|G|).
- (15,5) 25,272 (Haar m=156, Z26 x|3 Z6). Order 160 (meta:20:8:13) reaches cost 2 with the 102 chart.
- (10,5) 4,032 (Haar m=126). Order 128 (meta:16:8:3) reaches cost 1 with the 216 chart.
- (14,5) table 14,760: needs m >= 462 with k=7, q=2; the only (7,2) chart so far has 1,314 of 3,024 singular.

When done (time box ~25 minutes of work), append ONE line of JSON to research/squads/r3-chartlift/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command reproducing your best>",
 "score": <best m with cost 0, or 0>, "lift": <2*m*q^4 or 0>, "best_cost_at_target": <lowest cost at the target m>,
 "valid": true|false, "next": "<one line>"}
"valid" is true only if apsp printed RESULT VALID for that lift. Then reply in at most 5 lines.
