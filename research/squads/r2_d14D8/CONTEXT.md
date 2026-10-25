# Squad r2_d14D8: shared context for every card (read this first)

**Goal.** A bipartite graph of maximum degree 14 and diameter 8 on more than **14,172,480** vertices (table value).
14,172,480 = 40·|H(11)|: the table graph is the incidence graph of the split Cayley hexagon H(q), q = 11, blown up
m = 40 times with 2 extra edges per vertex. Across the table, the D = 8 values with Δ = q + 3 are m(q)·|H(q)| with
**m(q) = 5(q+5)/2: q = 5: 25, q = 7: 30, q = 11: 40.** Beating m(q) at ANY q is progress: m ≥ 31 at q = 7 would also be a
new record at (Δ, D) = (10, 8) (table 1,176,480 = 30·|H(7)|). Round 1 (research/squads/r1_d14D8, read its scoreboard) showed
that random-like voltages stop far below m(q) (q = 5: about 15-20; q = 11: about 16-17). STRUCTURE is required.

**The family.** Base graph = H(q) incidence graph (points = side A, lines = side B, ids 0..N-1 each) + extra point-line
edges (2 per vertex for Δ = q + 3), every edge carrying a voltage in Z_m. Lift: (p, g) ~ (l, g + v). Parallel edges are
allowed (same point and line, different voltages). For a bipartite graph, **diameter ≤ 8 ⟺ every point-copy reaches every
line-copy within 7 steps** (point-point within 8 then follows). The checker tests exactly this from every (p, 0).

**Opus analysis (use it).**
- The D = 7 table graph (5·|H(q)|, same degree q + 3) is: 5 levels i ∈ Z_5 of H(q), and (p, i) ~ (φ(p), i+1), (p, i) ~
  (φ(p), i+2) for ONE bijection φ: points → lines (φ doubled). Any φ works there. The D = 8 table graph is 8 = (q+5)/2
  times bigger with the same cross-distance rule (≤ 7), so it plausibly is "D7 levels × Z_k sublevels", k = (q+5)/2.
  Lift group Z_5 × Z_k = Z_{5k} (gcd(5,k) = 1, CRT). Hexagon flags carry (level 0, sub h), the two φ-edges (+1, sub a(p))
  and (+2, sub b(p)). Generator: `opus/mk_lev.py` (random sub-voltages).
- Random sub-voltages in this level family (exact, all sources): q = 5: k = 2 cost 8, k = 3 cost 100, k = 4 cost 3,699
  (the table needs k = 5); q = 7 at k = 6 (m = 30) has ~125 uncovered per source. `liftdiag` shows WHERE: level 0 at hexagon distance 3 (only the geodesic + pairs of
  detours), and levels ±1, ±2 at distance 5.
- Route families that exist for EVERY pair (p, L) (with matchings φ_k, voltages g_k on φ-edges, h on flags):
  (A) pencil-back p → y ∋ p → φ_k^{-1}(y) → geodesic → L (q+1 routes per k); (B) line-back p → geodesic → φ_k(z) → z ∈ L
  → L (q+1 per k); (C) jump-first p → φ_k(p) → one of the q+1 geodesics to L when φ_k(p) is opposite L (distance 6);
  (D) jump-last, the same at the other end; (0) the hexagon geodesic (+ q² walks of length 7 if d(p, L) = 5); with φ
  doubled also "detours" p → φ(p) → p by the two parallel edges (shift (±1, ±(b−a))), at any vertex of a route.
  About 8(q+1) guaranteed routes per pair vs m ≈ 41 needed: structure must make them land on DIFFERENT voltages.
- Perfect "rainbow bundles" (the q+1 geodesics between every opposite pair with distinct voltages in Z_{q+1}) are
  impossible (the cover would have girth 14 and exceed the girth-14 Moore bound). Approximate rainbows are allowed.

**Tools** (do not edit; copy into your folder to change): `/home/user/degree-diameter/research/squads/cells/d14D8_work/`
- `hex/hex_q{3,5,7,11}.bin`: H(q). `import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work');
  from hexlib import load, write_base, hex_edges, dist_from_point`; `N, LP, PL, coord = load(q)`: LP[l] = the q+1 points
  of line l, PL[p] = the q+1 lines through p, coord[p] = 7 coordinates over GF(q) (q prime) on x0x4 + x1x5 + x2x6 = x3².
- `hex/sym_q{q}.npz` (from `symq.py`): a cyclic group Σ = ⟨g⟩ ≤ G_2(q) acting semiregularly on points and lines,
  |Σ| = 31 (q=5), 19 (q=7), 133 (q=11); arrays gperm, glperm (g on point ids / line ids), orbP, shP, repP (point p =
  g^shP[p] · repP[orbP[p]]), orbL, shL, repL. A design invariant under Σ (h(gp, gl) = h(p, l), φ(gp) = gφ(p), ...)
  has Σ × Z_m as automorphisms, so the exact check needs only the |repP| orbit representatives as sources
  (`lifteval FILE 8 i:r1,r2,...` with the repP ids is then exact for the whole graph). Round-1 card c4 wrote a fast
  annealer for exactly this quotient at q = 11: `research/squads/r1_d14D8/c4/symsa.c` (+ `sym_setup.py`): read it.
- Base-graph file: first line `N N m`, then `p l v` per edge. `write_base(fn, N, m, edges)`; `hex_edges(LP, volt)`.
  liftdiag needs the hexagon flags FIRST (hex_edges order), then the extra edges.
- Scorers: `./lifteval FILE 8 all` (m ≤ 64, exact: q = 5 about 1.4 s, q = 7 about 40 s); `./liftevalw` (m ≤ 1024);
  `./liftevalw FILE 8 r:200:7` samples 200 sources (seed must not be 1). q = 11: never `all` (1 hour; Opus does it).
  `./liftdiag FILE q L r:100:3` = uncovered per source by hexagon distance (1, 3, 5) and by voltage mod L.
- Examples: `opus/mk_lev.py q L k seed s1,s2 rand|zero rand|zero same|indep out` (level family), `mk_ratio.py`
  (rainbow ratio-of-linear-forms voltages), `mk_digon.py` (matchings inside the flag set), round-1 cards' code.

**Machine rules (4 cores / 15 GB shared with 8 agents):** single thread; prefix heavy commands with `timeout 900 nice -n 10`;
at most ~1.5 GB memory; no git; write only inside `/home/user/degree-diameter/research/squads/r2_d14D8/<card>/`.
Time box: about 25 minutes of work. Do not run more than one heavy process at a time.

**Report.** Append exactly ONE line of JSON to `/home/user/degree-diameter/research/squads/r2_d14D8/scoreboard.jsonl`:
`{"card": "c1", "idea": "<one line>", "code": "<path>", "command": "<exact command that rebuilds and checks the best design>",
"best": {"q5": <largest m with exact COST 0 at q=5 or null>, "q7": <... q=7 or null>, "q11": <largest m with COST 0 on
r:200 at q=11 or null>}, "dgq": {"q5": 25, "q7": 30, "q11": 40}, "valid": true|false, "next": "<one line>"}`
Then reply in at most 5 lines. A design only counts if its generator and base file are saved in your folder.
