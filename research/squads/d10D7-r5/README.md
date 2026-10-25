# d10D7 squad round 5: a bigger partial ovoid of H(8) = more vertices at (10,7)

Our (10,7) record 224,962 = 3·74,898 + 2·134 frees K = 134 pairs (research/d10D7/checks/B2_hubs_CHECK.md). K is the
size of a set of **pairwise opposite points of the generalized hexagon H(8)** (lines are not a constraint: a spread of
513 opposite lines exists). **Every extra point = +2 vertices.** The current best set is `best134.txt` here (from round 4,
card c1, k-fixed tabu search; other seeds of the same search gave 80-98, so 134 was a lucky run).

Equivalent problem. Points of H(8) = points of Q(6,8): X0X4 + X1X5 + X2X6 = X3^2 over GF(8) (x^3 = x+1, element
a0 + 2a1 + 4a2). Two points are opposite iff B(x,y) != 0, B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2 (char 2: the X3 term
vanishes). Projecting from the nucleus (0,0,0,1,0,0,0), this is a **partial ovoid of the symplectic space W(5,8)**:
points of PG(5,8) pairwise non-orthogonal. W(5,q) has no ovoid (q^3+1 points), so the maximum is below 513. Each
point is "orthogonal" (= in conflict) with 4,680 others. For comparison H(7) (q = 7) reached 288 = (q-1)(q^2-1) of
344, H(5) 72 of 126.

## Tools
- research/d10D7/hex/hex_q8.bin: int32 q, N=37449, N; N*9 int32 point ids per line; then N*7 uint8 coordinates
  (normalised, first nonzero = 1).
- Scorer (the only thing that counts): `research/squads/d10D7-r4/tools/setcheck research/d10D7/hex/hex_q8.bin FILE
  points opposite` → "VALID size S".
- Prior code you may copy into your folder: research/squads/d10D7-r4/c1/pov.c (k-fixed tabu, uint16 neighbour lists,
  351 MB; usage in its header), research/squads/d10D7-r4/c2/ (torus orbits + exact max clique over orbit graphs,
  85), research/squads/d10D7-r4/c3/tabu.c, sa.c (lines and points).

## Rules
4 cores and 15 GB shared by Opus and the cards. Heavy commands `timeout <=1700 nice -n 10 ...`, ONE process at a
time, < 1.5 GB RAM. Work only in research/squads/d10D7-r5/<card>/, no git commits. Save your best set as a plain id
file. Append ONE JSON line to research/squads/d10D7-r5/scoreboard.jsonl: {"card": "cN", "idea": "<one line>", "code":
"<path>", "file": "<best set>", "command": "<exact>", "score": <size>, "metric": "partial_ovoid_H8", "valid":
true|false, "next": "<one line>"} and reply in at most 5 lines.
