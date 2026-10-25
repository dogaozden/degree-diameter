# Squad d16D8 round 2: common brief (read this first, then your card)

LONG GOAL: beat the bipartite (Δ,D) = (16,8) record 36,201,060 = 45 copies of the incidence graph of the generalized
hexagon H(13) with 2 extra edges per vertex (Delorme–Gómez–Quisquater, unpublished). Their family: m = 5·⌊(q+5)/2⌋
copies of a generalized polygon of order q, degree q+3, diameter = (polygon diameter) + 2. Random lifts reach only ~1/3 of
that, so DGQ use structure nobody here knows. We want a structure that gives MORE copies than 5·⌊(q+5)/2⌋.

THIS ROUND USES A FAST TESTBED, the generalized quadrangle W(q) (incidence graph I: diameter 4, girth 8, q+1-regular,
N = (q+1)(q^2+1) points and N lines). Problem: a Z_m-lift of I + 2 perfect matchings (points -> lines) with diameter 6
(= 4 + 2), degree q+3. Same degree and the same walk-count scaling as H(q) at diameter 8, but tiny: q = 13 has only
4,760 base vertices, so a full check takes 1-3 s, and q = 7 (800 vertices) takes 0.02 s.
DGQ-analog targets (5·⌊(q+5)/2⌋): q=5: 25, q=7: 30, q=11: 40, q=13: 45.
Baselines measured by Opus: random designs VALID up to m = 10 (q=5,7) and 12 (q=11,13); plain annealing (150 s) VALID
m = 16 at q = 7, and m = 20 stalls at ~300 uncovered.

SCORE: the largest m for which you have a VALID design at q = 13 (primary) and at q = 7 (secondary); q = 11 if you can.

TOOLS (in /home/user/degree-diameter/research/d16D8/, already built; do not edit them; copy if you need a variant):
- baselift (C): Z_m-lifts of any base multigraph. Base file: header "V m E", then E lines "x y c cls": edge x—y with
  voltage c in Z_m, i.e. (x,g) ~ (y,g+c). cls = 0 fixed, cls >= 1 voltage may be annealed, cls >= 100 the y-ends of two
  edges of the same class may be swapped. m <= 64.
    ./baselift eval FILE 6            -> "... uncovered=U ..." ; "VALID(all sources)" when U = 0 (all sources)
    ./baselift eval FILE 6 200        -> 200 random sources (screening only, never a VALID claim)
    MOVES=vvvM T0=2 T1=0.1 ./baselift anneal FILE 6 SECONDS SEED OUT     (v = voltage move, M = swap move; stops at 0)
    env FIXMOD=f: voltage moves keep c mod f (e.g. a Z_5 level skeleton inside Z_5k); NSRC=n samples n sources;
    SRCFILE=f lists sources (use only for screening).
- gq.py (Python): `import sys; sys.path.insert(0,'/home/user/degree-diameter/research/d16D8'); import gq`
    G = gq.load(q)   # dict: q, N, pts (4-tuples over F_q, normalized), lines (sorted point-index lists), plines
    base vertices: point p = p (0..N-1), line l = N + l. Symplectic form B(x,y) = x0y1-x1y0+x2y3-x3y2; collinear
    points have B = 0. gq.write_base(fn, 2*N, m, edges) with edges = list of (x, y, c, cls).
    gq.random_design(q, m, seed) -> (V, edges): random flag voltages (cls 1) + two random matchings (cls 100, 101).
    `python3 gq.py base q m seed OUT` writes a random design. (q must be prime: 3, 5, 7, 11, 13.)
  Every design must be: the flags of W(q) (each point-line incidence) + exactly 2 perfect matchings points -> lines
  (each point on 2 extra edges, each line on 2 extra edges), so every base vertex has degree q+3.
- Facts: in a Z_m lift, misses concentrate where few short walks exist. In I, a non-backtracking walk between
  vertices at distance d has length d or >= 8 - d, so pairs at distance 0 or 1 (same vertex / incident point-line) can
  only use the matchings to change sheet; far pairs have many walks.

MACHINE RULES (4 cores, 15 GB shared by 9 agents): THREADS=1 always; run anything longer than a few seconds as
`timeout 900 nice -n 10 <cmd>`; at most ONE heavy process at a time; <= 1.5 GB memory; no git commands; write only
inside your card folder /home/user/degree-diameter/research/squads/d16D8-r2/<card>/. Time box: about 25 minutes of work.

REPORT: append exactly ONE line of JSON to /home/user/degree-diameter/research/squads/d16D8-r2/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact check command for your best q=13 design>",
 "score": <largest VALID m at q=13, or 0>, "q7": <largest VALID m at q=7, or 0>, "q11": <or 0>, "valid": true|false,
 "best_design": "<path of the best VALID q=13 design file (else best q=7)>", "next": "<one line: what to try next>"}
Only claim VALID if `./baselift eval FILE 6` with no source count printed "VALID(all sources)". Then reply to Opus in
at most 5 lines.
