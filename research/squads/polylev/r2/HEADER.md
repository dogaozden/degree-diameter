# Squad polylev r2 (director: Opus, job thm-polygon-levels, 2026-10-28)

Read this header, then your card. Work ONLY in `research/squads/polylev/r2/<card>/` (create it). No git commits, no
edits outside your folder. Machine: 4 cores shared with the director and 15 other cards: one thread; heavy commands
as `timeout <WALL> nice -n 10 <cmd>` where WALL is a WALL-CLOCK limit (programs that count CPU seconds run about 3-4
times slower than their budget under this load, so give them a wall timeout 4x their CPU budget, or better, make
your programs stop on wall-clock time and write their best result periodically). At most 1.5 GB of memory. Time box:
about 30 minutes.

## Goal of this round: first values for NEW cells (Delta, 11), Delta = 11..20, and the records (9,11), (10,11)

H(q) = split Cayley hexagon on the parabolic quadric Q(6,q): Q(x) = x0x4 + x1x5 + x2x6 - x3^2 in PG(6,q), polar form
b(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3. N = (q^6-1)/(q-1) points, N lines. Two points of H(q) are at distance
<= 4 in the incidence graph iff they are orthogonal (b = 0); opposite (distance 6) iff b != 0.

**D = 11 ball lift (proved by the director).** Point classes A_0..A_{K-1}: pairwise disjoint sets of points, each
meeting the 4-ball of every point; line classes B_0..B_{K-1}: pairwise disjoint sets of lines, each meeting the 4-ball
of every line (lines at distance <= 4); |A_i| = |B_i|. Then for every r >= 1 there is a bipartite (q+1+r)-regular graph
of diameter <= 11 with 2N(2rK+1) vertices. Known good classes:
- **points:** the q+1 points of ANY totally singular line of Q(6,q) (not only hexagon lines): for a point p, the line
  meets the hyperplane p^perp, i.e. contains a point orthogonal to p. So K_points = number of pairwise disjoint
  totally singular lines of Q(6,q) (a partial line spread of the quadric; bound N/(q+1) = q^4+q^2+1). Two points
  x, y of Q(6,q) span a totally singular line iff b(x,y) = 0; its points are x and y + l*x (l in F_q), normalised.
  Cheap candidates: from a point p, a random walk of length 2 or 4 in the incidence graph (point -> line -> point ->
  line -> point) ends at a point orthogonal to p.
- **lines:** the pencil (q+1 lines) through a point z; disjoint pencils = pairwise NON-COLLINEAR points z (a partial
  distance-2 ovoid; bound q^4+q^2+1). K_lines = number of pairwise non-collinear points found.
- K = min(K_points, K_lines); classes of size q+1 on both sides, so they are balanced.

Thresholds: (9,11) record needs q=7 K >= 1,852 (bound 2,451); (10,11) needs q=8 K >= 2,975 (bound 4,161). For
Delta >= 11 the lab has NO value at D = 11, so any K gives a first value: (q, r) = (11,1)->(13,11), (11,2)->(14,11),
(13,1)->(15,11), (13,2)->(16,11), (13,3)->(17,11), (16,1)->(18,11), (16,2)->(19,11), (16,3)->(20,11). Already found by
round 1: q=7 1,619 disjoint hexagon lines / 1,618 non-collinear points (ILS); q=8 2,701 / 2,701 (Singer-73 orbit
quotient + ILS); q=3 78 disjoint singular lines (greedy, 85.7%) with the duality for the line side; the director is
running q = 9 (duality) now: do not do q = 9.

## Tools (research/theorems/polylev/; hexagons in hex/hex_q{2,3,4,5,7,8,9,11,13,16}.bin)

- `hexlib.py`: `H = Hex(path)`: H.N, H.q, H.lines (N x (q+1) point ids), H.PL (lines through each point),
  H.coord (N x 7 coordinates, field elements as integers 0..q-1), H.ADD/H.MUL/H.NEG/H.INV (field tables, the same
  encoding as the files), H.point_ids(X) (ids of the rows of X, normalised), g2.gram_row(H, x) (row y with y.z = b(x,z)).
  Loading q = 16 (N = 1.1M) takes a few minutes in Python; for q >= 13 consider C (file format: int32 q, N, L, then
  L*(q+1) int32 point ids, then N*7 uint8 coordinates; field: research/d10D7/hexgen2.c has the GF(p^e) tables).
- `qspread.py HEX SEED OUT [PHI]`: greedy disjoint singular lines (vectorised b over all points per step: fine for
  q <= 9, too slow beyond; write a random-walk version for larger q).
- research/gh6/ils_mis.c (bit-matrix ILS for max independent set, n <= ~40k);
  research/squads/polylev/r1/c12/{mis.c,mis2.c,mkquot.py,expand_verify.py} (ILS with adjacency lists; orbit quotient
  by a semiregular group: classes made of whole orbits); grp/*.pperm/.lperm (semiregular groups: S7_q11, S19_q11,
  S61_q13, S91_q16, S13_q16, S7_q16, T_q7 (order 43), T_q9, S13_q9, S7_q9); `singer_perms.py HEX e OUT` (Singer element
  of SL(3,q), writes perms of g^e).
- `bin/apsp EDGES Delta D` (all-pairs check), `lift9.py HEX PCOL LCOL K r seed OUT.edges` (builds the lift from colour
  files: int32 per element, class index or -1), `domcheck.py HEX PCOL LCOL 4` (scorer: counts classes meeting every
  4-ball, small q only).

## Scorer for this round

Your sets must be checked by an independent short script (written by you, separate from the search): disjoint lines
are totally singular (all q+1 points on Q, pairwise orthogonal) and pairwise disjoint; non-collinear points share no
line of H(q). Score = the number K of classes you certify (for a one-side card, that side's count).

## Report

Append ONE line of JSON to `research/squads/polylev/r2/scoreboard.jsonl`:
`{"card": "eNN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <K>, "valid": true|false,
"files": "<paths of the sets>", "next": "<one line>"}` and reply in at most 5 lines.
