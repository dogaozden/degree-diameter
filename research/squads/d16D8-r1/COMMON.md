# Squad d16D8 round 1: common brief (read this first, then your card)

GOAL (long run): beat the bipartite (Δ,D) = (16,8) record 36,201,060 vertices. That record is exactly 45 copies of the
incidence graph of the generalized hexagon H(13) (804,468 vertices, degree 14) with 2 extra edges per vertex
(Delorme, Gómez, Quisquater). The same family gives (10,8) = 30·|H(7)|, (12,8) = 35·|H(9)|, (14,8) = 40·|H(11)|:
m = 5·(ceil(q/2)+2) copies of H(q), degree q+3. At q = 3, 5, 7 that formula gives m = 20, 25, 30.

THIS ROUND: find a STRUCTURE of lifts of H(q) whose number of copies m grows faster with q than 5·(ceil(q/2)+2).
We test at small q because checks are fast there: q = 3 (728 base vertices, ~0.05 s per full check) and q = 5
(7,812 base vertices, ~5 s per full check). Score = the largest m that is VALID at q = 5 (primary; DGQ formula 25)
and at q = 3 (secondary; formula 20).

THE MODEL. Base vertices: hexagon points 0..N-1 and lines N..2N-1. The graph has vertices (x, g), g in the group
G = Z_m1 x Z_m2 (m = m1·m2 <= 64). Each hexagon flag (point p on line l) gives edges (p,g) ~ (l, g + s) for a
"flag shift" s; each point p has t = 2 extra edges (p,g) ~ (M_k(p), g + v_k(p)) where M_1, M_2 are bijections
points -> lines. Degree q+3, bipartite (points | lines). VALID = diameter <= 8, i.e. every (x,g) is within 8 of
every same-side vertex and within 7 of every other-side vertex.

KNOWN SO FAR (Opus, this session):
- Random designs (random bijections, random shifts in Z_m) are valid up to m ~ 16 at q = 3 and m ~ 13 at q = 5.
  Random flag shifts help a little. So random structure gets WORSE with q while the DGQ formula gets better.
- Plain annealing (hexlift2 anneal, MOVES=vMs) found VALID m = 26 at q = 3 in 5 minutes; at q = 5, m = 20 was
  still at ~40 uncovered (200 sampled sources) after 4 minutes.
- Almost all misses are point-line pairs at hexagon distance 5 (the farthest point-line distance; the walk budget is
  7 so there are only 2 spare steps). Same-side pairs are essentially never missed.

TOOLS (all in /home/user/degree-diameter/research/d16D8/, already built; do not rebuild or edit them, copy if needed):
- hexlift2 (C):  `./hexlift2 eval hex/hex_q5.bin DESIGN 8`  -> "... uncovered=U ... VALID(all sources)" when U = 0
  with all sources. `./hexlift2 eval hex/hex_q5.bin DESIGN 8 200` uses 200 random sources (fast screening).
  `./hexlift2 diag hex/hex_q3.bin DESIGN 8` prints misses by hexagon distance.
  `MOVES=vMs NSRC=200 T0=4 T1=0.3 ./hexlift2 anneal hex/hex_q5.bin DESIGN_IN 8 SECONDS SEED DESIGN_OUT` anneals
  (moves: v jump shift, s flag shift, M swap two matching targets, w / t change only the Z_m2 part of a jump /
  flag shift). It stops at cost 0. Read the header comment of hexlift2.c for the design file format.
- hexio.py (Python): `import sys; sys.path.insert(0,'/home/user/degree-diameter/research/d16D8'); import hexio;
  H = hexio.load(5)` gives lines, plines (lines through each point, in the order the design file uses), point
  coordinates; `hexio.dist_from(H, v)` hexagon distances; `hexio.write_design(fn, H, m1, m2, M, v, s)`.
- mkdesign.py: random designs (`python3 mkdesign.py rndsig hex/hex_q5.bin 20 2 SEED out.txt`).
- Hexagon files: hex/hex_q3.bin, hex_q5.bin, hex_q7.bin (q = 7 is 39,216 base vertices; a full check ~2-3 min).

MACHINE RULES (4 cores and 15 GB shared by 9 agents): THREADS=1 always; run anything longer than a few seconds as
`timeout 900 nice -n 10 <cmd>`; at most ONE heavy process at a time per card; <= 1.5 GB memory; no git commands;
write only inside your card folder /home/user/degree-diameter/research/squads/d16D8-r1/<card>/. Time box: about
25 minutes of work in total, then report.

REPORT: append exactly ONE line of JSON to /home/user/degree-diameter/research/squads/d16D8-r1/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact check command for your best design>",
 "score": <largest VALID m at q=5, or 0>, "q3": <largest VALID m at q=3, or 0>, "valid": true|false,
 "best_design": "<path of the best VALID design file>", "next": "<one line: what to try next>"}
Only claim VALID if `./hexlift2 eval hex/hex_qX.bin <file> 8` (no source count, i.e. ALL sources) printed
"VALID(all sources)". Then reply to Opus in at most 5 lines.
