# Squad round bcd-d8-r1: large diameter-8 lifts of the generalized hexagon H(5)

Opus lead: project bigcheck-dist (branch claude/bigcheck-dist-h6r1g3), 2026-10-25.

## The problem
Build a bipartite graph with maximum degree Δ = 8 and diameter ≤ 8 with as many vertices as possible, as a **cyclic lift**
of a base graph built on the split Cayley hexagon H(5).

- H(5): 3906 points and 3906 lines; its incidence graph is 6-regular, bipartite, diameter 6, girth 12
  (point-line distances are 1, 3, 5; point-point and line-line distances 2, 4, 6).
- Base graph B: the incidence graph of H(5) plus 2 extra edges at every vertex (degree 8). Default design: two bijections
  sigma1, sigma2 from points to lines, edge p -- sigma_j(p).
- Lift over Z_M: every base edge u-v gets a voltage a in Z_M; lift vertices (u, g), g in Z_M; lift edges
  (u, g) ~ (v, g + a). The lift has 7812·M vertices, max degree 8, and is bipartite.
- Score: **cost** = number of pairs (source, lift vertex) at distance > 8, summed over one source per symmetry orbit.
  **cost 0 means the lift has diameter ≤ 8** (a valid graph with 7812·M vertices).

## Benchmarks (what is known; beat these)
- Random voltages + simulated annealing (tool x2s, two random bijections): M = 16 reaches cost 0 quickly; M = 20 gets
  stuck at cost 2; M = 25 gets stuck near 580. Random-voltage starting costs: M=16: ~8, M=20: ~70, M=25: ~1270,
  M=31: ~7800. Zero voltages on the incidence edges are much worse (M=25: ~8000).
- Delorme (1985) has a structured construction with the same shape giving **M = 25** at q = 5 (the published table
  value for Δ = q+3 at diameter 8 is 5·⌊(q+5)/2⌋ copies of H(q)). Its definition is not known to us.
- Our Haar-graph record at (8,8) is 239,904 = 30.7 copies of H(5). **M ≥ 31 at q = 5 would be a new (8,8) record.**
- **M ≥ 21 beats annealing, M ≥ 26 beats Delorme's method** (the same idea at q = 7 would then beat the (10,8) table,
  1,176,480 = 30 copies of H(7)).
- Where annealed solutions fail: (source, target) pairs at odd base distance 1, 3, 5 (point-line pairs), mostly 5.

## Tools (all already built; rebuild if missing)
- Hexagon files: /tmp/bcdt/hex/hex_q5.bin (H(5)), /tmp/bcdt/hex/singer_q5.bin (a torus tau of order 31 in
  Aut H(5), acting freely on points and on lines: 126 orbits each). Also q = 3 (tiny, 728 base vertices, torus order 13)
  and q = 7 (39,216 base vertices, torus order 19). Rebuild: research/d13D7/hexgen.c (`./hexgen 5` writes
  hex/hex_q5.bin) and research/projects/bigcheck-dist/d8/singer.py (needs research/d13D7/tools/hexlib.py on the path).
- **bcd** (exact checker and scorer for any cyclic lift): /tmp/bcd. Build:
  `gcc -O3 -march=native -fopenmp -o /tmp/bcd research/projects/bigcheck-dist/bcd.c`.
  Score: `/tmp/bcd lift SPEC 8 8 --cost --threads 1` prints `COST n`. Full check (no --cost) prints
  `RESULT VALID d=8 D=8 n=...` for a valid graph. Spec format is in the header of bcd.c: base edges `u v a`, and
  optional base automorphisms `aut u pi(0..NB-1) c(0..NB-1)` meaning (v, g) -> (pi v, u·g + c(v)); bcd verifies them
  and then uses one BFS source per orbit. A tau-invariant voltage assignment (same voltage on e and tau(e)) with
  `aut 1 tau 0...0` needs only 252 sources at q = 5 (about 0.1-0.3 s per score); without symmetry all 7812 base
  vertices are sources (about 5-10 s).
- **hexspec.py** (research/projects/bigcheck-dist/d8/hexspec.py): Python helpers. `H = hexspec.Hex(hexbin, singerbin)`
  loads H(q) (H.lines, H.plines, H.coord, torus H.tp/H.tl, orbits H.porb/H.ppos/H.prep), `equivariant_bijection(H, rng)`,
  `write_spec(path, H, M, edges)` (adds the torus automorphism), `bcd_cost(spec, 8, 8)`. Base numbering: points
  0..N-1, lines N..2N-1. See /tmp/bcdt/test_hexspec.py for a 30-line example that builds the default design with random
  tau-invariant voltages and scores it.
- **x2s** (research/projects/bigcheck-dist/d8/x2s.c): fast in-process simulated annealing for the family "C copies of
  H(q) + r tau-equivariant bijections with copy shifts s_j, voltages in Z_k" (C = 1: plain cyclic lift of B over Z_k).
  Build: `gcc -O3 -march=native -fopenmp -o x2s x2s.c -lm`. Run (C=1, r=2, M=20):
  `OMP_NUM_THREADS=1 ./x2s /tmp/bcdt/hex/hex_q5.bin /tmp/bcdt/hex/singer_q5.bin 1 2 0 0 20 8 SEED ITERS T0`
  (stderr shows progress; best solution goes to best_SEED.sol in the current directory). About 20-50 ms per
  evaluation at q = 5. Env FLAGS0=1 fixes incidence voltages to 0; ANALYZE=1 with ITERS=0 and a .sol prints the
  failing pairs by base distance. Read its header comment before changing it; copy it into your folder to modify.
- research/projects/bigcheck-dist/d8/nbwx.c: counts reduced walks between base vertex pairs (upper bounds on M).

## Machine rules (shared with the lead and 7 other cards)
- THREADS=1 everywhere (`OMP_NUM_THREADS=1`, `--threads 1`). Run heavy commands as `timeout 900 nice -n 10 <cmd>`.
- At most about 1.5 GB of memory. No git commands. Write only inside your card folder research/squads/bcd-d8-r1/cK/.
- Time box: about 15 minutes of work, then report.

## Report
Append ONE line of JSON to research/squads/bcd-d8-r1/scoreboard.jsonl:
`{"card": "cK", "idea": "<one line>", "code": "<path>", "command": "<exact command that reproduces the best>",
"score": <largest M with cost 0, or 0 if none>, "best_cost_at": {"M": <M>, "cost": <cost>}, "valid": true|false,
"next": "<one line>"}`
Keep the spec or .sol of your best result in your folder. Reply to the lead in at most 5 lines.
