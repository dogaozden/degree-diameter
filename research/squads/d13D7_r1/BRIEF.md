# Squad round 1 (job cell-13-7): largest partial ovoid of Q(6,11)

Every point added to R raises our (13,7) graph by 2 vertices (research/d13D7/tri.c: 1,062,936 + 2|R|).

Problem. Points of H(11) = points of the parabolic quadric Q(x) = x0x4 + x1x5 + x2x6 - x3^2 = 0 in PG(6,11)
(177,156 points, stored in research/d13D7/hex/hex_q11.bin, index 0..177155, 7 coordinates each, first nonzero = 1).
Find a large set R of points that are pairwise NON-orthogonal:
  B(x,y) = x0y4 + x4y0 + x1y5 + x5y1 + x2y6 + x6y2 - 2 x3y3  !=  0  (mod 11)  for all distinct x, y in R.
(Equivalently: pairwise opposite points of the hexagon H(11); a partial ovoid of the polar space Q(6,11).)

Known: random greedy ~100; an elliptic 3-space section (x1 = x5 = 0, x6 = 2 x2) gives 122 (maximal, cannot be
extended); our iterated local search research/d13D7/tools/povoid_ils.c reached 133 in 150 s
(research/d13D7/hex/R133_ils.txt). Upper bound q^3+1 = 1332 is NOT attainable for q = 11 (ovoids of Q(6,q) exist
only for q a power of 3); the true maximum is unknown.

Affine model (useful): the points with x0 = 1 are exactly the points opposite e4 = (0,0,0,0,1,0,0); write them
x = (1, a, b, c, c^2 - a e - b f, e, f) with (a,b,c,e,f) in F_11^5. Then B(x, x') = (c-c')^2 - (a-a')(e-e') - (b-b')(f-f').
So an affine solution is a set T in F_11^5 whose pairwise differences v satisfy Q'(v) = c^2 - a e - b f != 0; the
point e4 itself can always be added (it is opposite every affine point).

Tools: research/d13D7/tools/hexlib.py (load(), bilinear(), is_partial_ovoid()), research/d13D7/tools/povoid_ils.c.
To turn a coordinate vector into a point index: normalise so the first nonzero coordinate is 1 and look it up in the
coordinate table (hexlib.load() returns coord, an N x 7 array, rows sorted by the base-11 code sum x_i 11^i).

Scorer (the only score that counts):
  research/d13D7/tools/oppcheck research/d13D7/hex/hex_q11.bin P <file>
  (file: one point index per line, '#' lines ignored) prints "RESULT VALID pairwise_opposite <m>".

Rules (shared machine: 4 cores, 15 GB, shared with 8 agents and the coordinator):
- single-threaded only (OMP_NUM_THREADS=1); anything longer than a few seconds runs as `timeout 900 nice -n 10 <cmd>`;
- at most about 1.5 GB of memory; never run more than one heavy job at a time;
- no git commands at all; write files only inside research/squads/d13D7_r1/<your card>/;
- time box: about 20 minutes in total.
Output: append ONE line of JSON to research/squads/d13D7_r1/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <m from oppcheck>, "valid": true|false, "file": "<path of your best set>", "next": "<one line>"}
and reply in at most 5 lines.
