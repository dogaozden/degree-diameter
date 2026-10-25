# Squad hexfam_r1 (project hexagon-family, Opus lead), 2026-10-25

## The problem
H(q) = split Cayley hexagon. Its points are ALL points of the parabolic quadric Q(6,q):
x0x4 + x1x5 + x2x6 - x3^2 = 0 in PG(6,q). Two points are OPPOSITE in H(q) iff B(x,y) != 0, where
B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 (in characteristic 2 the x3 term vanishes).
So we want LARGE PARTIAL OVOIDS of Q(6,q): sets of points, every two non-orthogonal (B != 0).
Every extra point is worth graph vertices in our degree-diameter records. An ovoid (q^3+1 points) does not exist
for q prime > 3 or q even, so the targets below are the real game.

| q | current best | ovoid size q^3+1 | file (point ids in our indexing) |
|---|---|---|---|
| 5 | 72 | 126 | research/d10D7/sets/P5_c6_72.txt |
| 7 | 288 | 344 | research/d10D7/sets/P7_c5_288.txt |
| 8 | 217 | 513 | research/d10D7/sets/P8_r5c4_217.txt |
| 11 | 756 | 1332 | research/d10D7/sets/P11_r6c7_756.txt (W(E7) mod 11 orbits) |
| 13 | 792 | 2198 | research/d10D7/sets/P13_E7sub_E6_792.txt (W(E6) orbits, 72 + 720) |

q = 9 is different (H(9) is self-dual): there we want a large set of points with NO TWO ON A COMMON LINE of H(9)
(pairs at distance 4 are allowed). Current best 4291 (research/d10D7/sets/P9_r6c4_4291.txt); Hoffman bound 6643.

Value per extra point: q = 11: 12 vertices; q = 13: 4; q = 5, 7, 8, 9: 2. So q = 11 and q = 13 matter most.
All five sets above are maximal (no point can be added), so improvements need new structure or swaps.

## Tools (all paths absolute under /home/user/degree-diameter/research/projects/hexagon-family/)
- hex/hex_q{5,7,8,9,11,13}.bin: H(q) (points in a fixed order; coordinates; lines). Point ids = row numbers.
- tools/q6lib.py (read its docstring): `from q6lib import Geo; G = Geo(11)`; G.C (coords), G.B(X,Y) (polar form,
  any q), G.ids_of(vectors), G.perm(7x7 matrix) (permutation of point ids for an isometry), G.to_std(Gram) (q odd
  prime: matrix T taking an abstract 7-dim quadratic space with Gram matrix Gram to our coordinates; conjugate your
  group generators g -> T g T^-1 mod q), G.check_opp(ids), orbits(N, perms).
- tools/mwc.py: exact max-weight clique (Python bitset branch and bound, `max_weight_clique(w, adj, tlimit)`).
- research/d10D7/ovoid/e7/: the code that made the 756 and 792 sets (W(E7) reflection groups mod q).
- **Scorer (the only thing that counts):**
  `/home/user/degree-diameter/research/projects/hexagon-family/tools/povcheck /home/user/degree-diameter/research/projects/hexagon-family/hex/hex_qQ.bin SETFILE`
  (append ` ncol` for q = 9). SETFILE = point ids separated by whitespace. Last line `SCORE n VALID`.

## Machine rules (shared with 8 others: 4 cores, 15 GB)
- One process at a time, single-threaded: `export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1`.
- Heavy runs: `timeout 1200 nice -n 10 <cmd>`; at most 1.5 GB memory.
- Work only inside your card folder research/squads/hexfam_r1/<card>/. No git commands. Don't edit other files.
- Time box: about 30 minutes in total. Save your best set as <card>/best_q<Q>_<size>.txt.

## Report
Append ONE line of JSON per q you improved or tried to research/squads/hexfam_r1/scoreboard.jsonl:
{"card": "c5", "q": 11, "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <size>,
 "valid": true|false, "file": "<path of the set>", "next": "<one line>"}
Then reply in at most 5 lines.
