# Relaxed friendly surgery: collinear pairs in a freed set (job cell-15-7, 2026-10-25)

Setting: the typed-level construction of research/squads/cells/d16D7.md (levels = copies of the incidence graph I of a
generalized hexagon H of order (q, q), q >= 3; in an H level the A-class is the points, in an H^D level the lines), a
friendly transition j -> j' (H level j, H^D level j') with the identity matching (p, j) ~ (p, j') for points p, and a
freed set R of points: the edges (r, j) ~ (r, j') for r in R are deleted. Every freed r leaves a free A-slot at (r, j)
(class A of level j, colour 0) and a free B-slot at (r, j') (class B of level j', colour 1). Line-side hubs (colour 1)
take one free colour-0 slot in every level, point-side hubs (colour 0) one free colour-1 slot in every level.

The one-transition theorem needs R non-collinear. Here R may contain collinear pairs.

## Statement

Suppose
- (R1) every point of R is collinear with at most one other point of R (the collinearity graph on R is a matching);
- (R2) for every pair {r, x} of collinear points of R, and for each of its two ordered versions (r with partner x):
  - (a) the point-side hub attached to the free B-slot of (r, j') has its level-j slot at a line through x;
  - (b) the line-side hub attached to the free A-slot of (r, j) has its level-j' slot at a line through x
    (a line of H, the A-class of the H^D level j').
Then every pair of vertices in levels j and j' is within distance 7. (Hubs are handled as before: each reaches every level
through its slot there; same-side hub pairs are checked by BFS.)

The dual statement holds for a friendly transition H^D -> H with a freed set of lines: pairs of concurrent lines
{l, l'} are allowed when the point-side hub at (l, target level) has its source-level slot at a point on l', and the
line-side hub at (l, source level) has its target-level slot at a point on l' (apply the statement to H^D).

## Proof

Write d for distance in I (in either level, the same graph). Facts about a generalized hexagon used below: for
d(u, v) < 6 the geodesic from u to v is unique; if v is a line with d(r, v) = 5 (r a point) and y the first line of
the geodesic r - y - x - ..., then x is the only point collinear with r at distance 3 from v.

Only routes that pass through the deleted edges of a freed point r with a partner x change; the proof of the one-
transition theorem (d16D7.md, cases 1-6) is re-run for such r. Non-freed points and freed points without a partner are as
before (their cases only use that their own Gamma_2 contains no freed point, which still holds for r without partner:
a freed point collinear with r would be a partner).

- Case 1 (a not in R, any target in level j'): unchanged.
- Case 2 (a line b in level j, an A-element a' = a line of level j'): a' has q + 1 >= 4 points, at most two of them in
  R (two only if a' is the line rx of a pair); take m on a' not in R: (b, j) ... (m, j) - (m, j') - (a', j'), <= 5 + 2.
- Case 3 (b in level j, b' = a point not in R in level j'): unchanged.
- Case 4 (b a line in level j, b' = r in level j'): the route (r, j') - y' - (L, j') - (L, j) - ... - (b, j) needs a point
  L collinear with r, L not in R, d(L, b) <= 3 (length 2 + 1 + 3). d(r, b) is 1, 3 or 5.
  d(r, b) = 1: take L on b, L != r, x (q >= 3).  d(r, b) = 3, geodesic r - y' - w - b: if w != x take L = w; if w = x
  take L any other point of y' = rx (then d(L, b) = 3 via x), not in R by (R1).  d(r, b) = 5 with geodesic
  r - y' - w - ...: if w != x take L = w (d(w, b) = 3).  If w = x the only candidate is x, which is in R; then use
  (R2a): the point-side hub P of (r, j') is adjacent to (beta, j) with beta a line through x, and d(beta, b) <= 4
  (b is at distance 3 from x, beta passes through x), so (r, j') - P - (beta, j) ... (b, j) has length <= 2 + 4.
- Case 5 (a = r in level j, a' a line = A-element of level j'): the route (r, j) - y' - (u, j) - (u, j') - ... - a'
  needs u collinear with r, u not in R, d(u, a') <= 3 (length 2 + 1 + 3); the same three sub-cases as in case 4, and
  when the only candidate is x, (R2b): the line-side hub h of (r, j) is adjacent to (alpha, j') with alpha a line
  through x, d(alpha, a') <= 4, length <= 2 + 4.
- Case 6 (a = r in level j, b' a point of level j'): route (r, j) - (u, j) - (u, j') - ... - b' with u collinear with r,
  u not in R, d(u, b') <= 4 (length 2 + 1 + 4 = 7). d(r, b') = 0: any u != x (then u - y' - r in level j': length 5).
  d(r, b') = 2: u = b' if b' != x; if b' = x take u another point of the line rx (d(u, x) = 2). d(r, b') = 4, geodesic
  r - y' - w - z - b': every point of y' other than r is within 4 of b'; at most one of them (x) is in R. d(r, b') = 6:
  each of the q + 1 lines through r has exactly one point at distance 4 from b' (its projection); at most one of these
  q + 1 points is x.
- The same cases with x in place of r (its partner is r).
Every pair of a level-j vertex and a level-j' vertex is covered; pairs inside a level and pairs between other levels
are unchanged. QED.

## Cost

Every collinear pair costs four hub constraints (two point-side hubs, two line-side hubs, each with a prescribed pair of
slots in levels j and j'). A hub has one slot per level, so a hub can serve one such constraint per pair of levels it
links. In the (15,7) construction the four bottleneck friendly sets are R_H at 0->2 and 1->2 and R_L at 2->3 and 2->4,
all touching level 2, so the number of constrained elements in all four sets together is at most the number of hubs of
each colour (about 10,000).
