# Squad r1_d14D8: shared context for every card (read this first)

**Goal.** A bipartite graph of maximum degree 14 and diameter 8 on more than **14,172,480** vertices (the table value).

**What the table graph is (decoded by Opus).** 14,172,480 = 40·|H(11)|, where H(11) is the incidence graph of the
split Cayley generalized hexagon of order 11 (354,312 vertices: 177,156 points + 177,156 lines, 12-regular,
diameter 6, girth 12). Every even-Δ D = 8 table value with Δ ≥ 10 is (5(q+5)/2)·|H(q)| with q = Δ − 3, i.e. the
"multiplier" m(q) = 5(q+5)/2: **q=3: 20, q=5: 25, q=7: 30, q=9: 35, q=11: 40**. So the record graph is H(q) blown
up m times with degree q+1+2. Beating the table = a degree-14 diameter-8 graph with > 40·|H(11)| vertices, e.g. an
H(11)-based family with **m ≥ 41**, or anything else that is larger.

**The family we can test fast: cyclic voltage lifts of H(q) + extra edges.** Base graph = H(q) incidence graph
(points = side A, lines = side B) plus extra point–line edges (e.g. two perfect matchings M_1, M_2: point x ~ line
M_j(x)), every base edge carrying a voltage in Z_m. Lift: vertices (v, g), g ∈ Z_m, edge (p, g) ~ (l, g + volt).
Degree = q + 1 + (extra edges per vertex); for Δ = 14 with q = 11 that is 2 extra edges per vertex.
The lift has diameter ≤ 8 iff from every (p, 0) every (l, g) is reached by a walk of length exactly 7.

**Tools** (do not edit; copy if you want to change code): `/home/user/degree-diameter/research/squads/cells/d14D8_work/`
- `hex/hex_q{3,5,7,9,11,13}.bin`: H(q). Load with
  `import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work'); from hexlib import load, write_base, hex_edges, dist_from_point`
  `N, LP, PL, coord = load(q)`: N points = N lines; `LP[l]` = the q+1 point ids on line l; `PL[p]` = the q+1 line
  ids through p; `coord[p]` = 7 coordinates over GF(q) of point p on the quadric x0x4 + x1x5 + x2x6 = x3² (q prime:
  ordinary integers mod q; q = 9 uses a + 3b encoding, avoid it unless you handle GF(9)).
- Base-graph file format (text): first line `N N m`, then one line `p l v` per edge (point id, line id, voltage).
  `write_base(fn, N, m, edges)` writes it; `hex_edges(LP, volt=None)` gives the hexagon edges (voltage array of shape
  (N, q+1) per line and position, default 0).
- Scorer: `./lifteval FILE 8 r:20:1` (m ≤ 64) or `./liftevalw FILE 8 r:20:1` (m ≤ 1024): COST = number of uncovered
  (line, level) pairs summed over 20 random sources; exit code 0 iff COST 0. `all` instead of `r:20:1` checks every
  source exactly (fine for q ≤ 7; q = 11 takes ~1 hour, do NOT run `all` at q = 11, Opus does the full checks).
  Speed: ~20 ms per source at q = 11, ~2 ms at q = 7.
- Examples: `mk_x0.py` (zero hexagon voltages, random matchings, constant shifts), `mk_x1.py` (random extra voltages),
  `mk_ratio.py` (extra voltages = ratio of two linear forms in the coordinates), `mk_star.py` + `lifteval2`
  (star product H(q) * C_m, cycle edges at each vertex).

**Already measured (do not repeat):**
- Zero hexagon voltages, 2 random matchings, constant extra voltages (1, 4): m = 10 always works (any q); m ≥ 11 fails.
- Zero hexagon voltages, random extra voltages ψ_j(x): q = 11 reaches only m ≈ 12–14 (μ ≈ 2 uncovered/source at 16).
- Ratio-of-linear-forms extra voltages (rainbow on almost every line): m = 24 nearly works, m ≥ 30 far off.
- Star product with rotation voltages: fails even at m = 12 (pairs at hexagon distance ≤ 4 get only ~7 levels).
- Random hexagon voltages are hopeless at m ≈ 40 (coupon collector): STRUCTURE is required.
- Walk supply: with 2 random matchings every point–line pair of H(11) has ≥ ~215 nonbacktracking walks of length ≤ 7
  (median 260 for lines at hexagon distance ≤ 3, 385 at distance 5). So m ≈ 40–60 is not ruled out by counting.
- Theory: with ZERO hexagon voltages the walks available for every pair give at most ~37 levels at q = 11. To go
  higher you need hexagon voltages, e.g. "bundles": two opposite lines (distance 6) are joined by exactly q+1
  geodesics (one through each point of the first line), a point and a line at distance 5 by 1 + q² walks of length
  ≤ 7. If the voltages of a bundle are all distinct, one bundle alone covers q+1 levels.

**Machine rules (shared 4 cores / 15 GB with 8 other agents):** single thread; prefix heavy commands with
`timeout 900 nice -n 10`; at most ~1.5 GB memory; no git commands at all; write only inside your card folder
`/home/user/degree-diameter/research/squads/r1_d14D8/<card>/`. Time box: about 20 minutes of work.

**Report.** Append exactly ONE line of JSON to `/home/user/degree-diameter/research/squads/r1_d14D8/scoreboard.jsonl`:
`{"card": "c1", "idea": "<one line>", "code": "<path>", "command": "<exact command that rebuilds and checks the best design>",
"q": <q>, "score": <largest m with COST 0 on r:20:1 (or all for q<=7)>, "vertices": <m*2N>, "dgq_m": <5(q+5)/2>,
"valid": true|false, "next": "<one line: what to try next>"}`
Then reply in at most 5 lines. A design only counts if its base file and generator are saved in your folder.
