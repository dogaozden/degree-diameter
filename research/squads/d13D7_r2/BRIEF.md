# Squad round 2 (job cell-13-7): more pairwise-opposite points of H(11) than 320

**Why it matters.** Our (13,7) record graph has 1,062,936 + 2|R| vertices, where R is a set of pairwise opposite points of the
split Cayley hexagon H(11) (research/d13D7/REPORT.md; the line side is never a problem: the Hermitian spread gives 1332
pairwise opposite lines). Current best |R| = 320 -> 1,063,576 (verified). **Every extra point = +2 vertices.** Beat 320.

**The problem.** Points of H(11) = points of the quadric Q(x) = x0x4 + x1x5 + x2x6 - x3^2 = 0 in PG(6,11) (177,156 points,
index 0..177155 in research/d13D7/hex/hex_q11.bin, coordinates first-nonzero = 1, sorted by code sum x_i 11^i).
Two points are opposite iff B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 != 0 (mod 11). Want: many points, pairwise B != 0
(a partial ovoid of the polar space Q(6,11); ovoids (1332 points) do not exist for q = 11; the true maximum is unknown).

**Affine model.** The points opposite e4 = (0,0,0,0,1,0,0) are x = (1, a, b, c, c^2 - ae - bf, e, f), (a,b,c,e,f) in F_11^5,
and B(x,x') = Q'(x - x') with Q'(a,b,c,e,f) = c^2 - ae - bf. So: a set T in F_11^5 with Q'(t - t') != 0 for all t != t',
plus the point e4 (opposite every affine point).

**The current best (fibration, round 1).** T = union of k whole affine lines t + F_11*u with u = (1,0,0,9,0) (Q'(u) = 2, a
non-square mod 11). Two lines t + F u, s + F u are compatible iff Q'(t - s + lam*u) != 0 for all lam in F_11 (a quadratic in
lam with no root). This depends only on the coset of t - s mod u, so the lines form a CLIQUE in the "coset graph" G on
F_11^5 / <u> (14,641 vertices; t ~ s iff compatible). G is a strongly regular Cayley graph (degree 6710, eigenvalues 6710,
55, -66; Delsarte clique bound 102). Best clique so far: 29 -> |R| = 1 + 11*29 = 320
(offsets in research/d13D7/sets/R320_offsets29_u1-0-0-9-0.txt). A clique of size k gives 1 + 11k points: k = 30 -> 331.
Coset representatives: offsets with a = 0, i.e. t = (0, b, c, e, f).

**Tools** (all in research/d13D7/):
- `tools/oppcheck hex/hex_q11.bin P FILE` — THE SCORER: FILE = one point index per line ('#' lines ignored); prints
  `RESULT VALID pairwise_opposite m`.
- `python3 tools/fiblift.py "1 0 0 9 0" OFFSETS OUT_IDX [OUT_COORDS]` — lifts offsets (one "a b c e f" per line) to e4 + the
  11 points of each line, writes point indices for oppcheck. (A 7-number line is copied as a point.) Any direction u works.
- `tools/hexlib.py` (load(), bilinear(), is_partial_ovoid()), `tools/povoid_ils.c` (ILS on the full problem, round 1: 133).
- `sets/R320_c8_idx.txt` (the 320 points), `sets/R320_coords...`.
- Card c8 only: `tools/linestar_check hex/hex_q11.bin FILE` (see its card).

**Rules (shared machine: 4 cores, 15 GB, 8 cards + Opus).** Single thread (OMP_NUM_THREADS=1). Every run longer than a few
seconds: `timeout 900 nice -n 10 <cmd>`, and give your programs an internal CPU-time limit (clock()) of at most 600 s so
they finish and print their best even when the machine is busy. At most 1.5 GB memory. No git commands. Write files only
inside research/squads/d13D7_r2/<your card>/. Time box: about 25 minutes in total.

**Output.** Save your best set as research/squads/d13D7_r2/<card>/best_idx.txt (point indices; for fibration cards also
best_offsets.txt), check it with oppcheck, then append ONE line of JSON to research/squads/d13D7_r2/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <m from the scorer>, "valid": true|false, "file": "<best file>", "next": "<one line>"}
and reply in at most 5 lines.

**Explicit coset graph (checked by Opus).** With u = (1,0,0,9,0), the coset graph G is
  G = Cay(F_11^4, {v = (s,b,c,f) : D(v) is a NON-SQUARE mod 11}),  D(s,b,c,f) = s^2 + 3c^2 + 8bf (mod 11),
squares mod 11 = {1,3,4,5,9}, non-squares = {2,6,7,8,10} (D = 0 is NOT an edge). Vertex v = (s,b,c,f) lifts to the offset
(a,b,c,e,f) = (0, b, c, s, f) for fiblift.py. Degree 6710. The 29-clique in these coordinates: research/d13D7/sets/
R320_offsets29_u1-0-0-9-0.txt converted by s = 2a + e (there a = 0, so s = e): first vertices (0,0,0,0), (8,1,4,9),
(0,2,7,4). G is vertex-transitive (translations), so WLOG a clique contains (0,0,0,0).
