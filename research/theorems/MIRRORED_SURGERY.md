# Mirrored surgery on hexagon covers (job cell-14-7, 2026-10-25)

Statement and proof of the construction behind (14,7) 1,774,632 and the other new D = 7 values in
research/cell147/mirror/README.md. It relaxes the theorem of research/d13D7/REPORT.md §2 (pairwise opposite R).

## Setting

H a generalized hexagon of order (q, q), q >= 3, with incidence graph of diameter 6; Gamma_2(x) = the q(q+1) points
collinear with a point x, Gamma_2(l) = the q(q+1) lines meeting a line l. sigma: points -> lines a bijection, r >= 1,
L = 2r + 1. The graph G(H, sigma, R, r) has vertices (y, i) for every point or line y and i in Z_L, the hexagon's
incidences inside every level, matching edges (p, i) ~ (sigma(p), i + k) for k = 1..r and every point p not in R, and
for every x in R: r "line-side" hubs joined to (x, i) for all i, up to r "point-side" hubs joined to (sigma(x), i) for
all i, plus a bipartite hub graph between line-side and point-side hubs. Max degree q + 1 + r when the hub graph has
degree <= q - r. Order L·2|P| + (number of hubs) = (2r+1)·|incidence graph| + 2r|R| with all hubs.

## Theorem

G has diameter <= 7 if
- (N1) no two points of R are collinear;
- (N2) no two lines of sigma(R) meet;
- (L) for every x in R, sigma(Gamma_2(x)) = Gamma_2(sigma(x));
- (H) any two line-side hubs, and any two point-side hubs, are within distance 6 in the hub graph.

(L) at two points x, y of R at distance 4 (midpoint m) forces sigma(m) to meet both sigma(x) and sigma(y), so sigma(x),
sigma(y) are at distance 4 with connecting line sigma(m); and points of R at distance 6 must go to lines at distance 6.
So (N1)-(L) say exactly: **sigma(R) mirrors the distance-4 structure of R** (midpoints to connecting lines), and sigma
is a local duality around every point of R. With R pairwise opposite this is the theorem of REPORT.md §2.

## Proof

Two vertices in one level are within 6 (the hexagon is untouched). Take (a, i) and (b, i + k), 1 <= k <= r (every other
pair of levels is the same up to symmetry), and use only the k-th matching.
1. a a point not in R: (a, i) - (sigma(a), i+k) - ... - b, length <= 1 + 6.
2. a a line, b a point: by (N2) at most one line of sigma(R) passes through b; take a line m through b not in sigma(R):
   (a, i) - ... - (sigma^-1(m), i) - (m, i+k) - (b, i+k), length <= 5 + 1 + 1.
3. a a line, b a line not in sigma(R): (a, i) - ... - (sigma^-1(b), i) - (b, i+k), length <= 5 + 1.
4. a = x in R, b a point: every point is within distance 3 of some line of Gamma_2(sigma(x)) (take the line of
   Gamma_2(sigma(x)) on a shortest path from sigma(x) to b). By (L) that line is sigma(p') with p' in Gamma_2(x), and p'
   is not in R by (N1), so its matching edge exists: (x, i) - (p', i) - (sigma(p'), i+k) - ... - b, length <= 2 + 1 + 3.
5. a = x in R, b a line: (x, i) - hub - (x, i+k) - ... - b, length <= 2 + 5.
6. b = sigma(x) with x in R, a a line: dually every line is within 3 of some point of Gamma_2(x); by (L) that point is
   sigma^-1(l') with l' in Gamma_2(sigma(x)), and l' is not in sigma(R) by (N2): (sigma(x), i+k) - (l', i+k) -
   (sigma^-1(l'), i) - ... - a, length <= 2 + 1 + 3.
   (b = sigma(x) and a a point not in R is case 1; a = x in R and b = sigma(y) is case 5.)
7. Hubs: a line-side hub of x reaches level j through (x, j): <= 1 + 6; a point-side hub of x through (sigma(x), j):
   <= 1 + 6; a line-side hub of x and a point-side hub of y through one level: 2 + d(x, sigma(y)) <= 2 + 5; two hubs of
   the same side: (H).
Every pair is covered; the graph is bipartite (points and line-side hubs on one side). QED.

## Use

R = a pairwise-opposite base set (in H(q) = split Cayley hexagon: points pairwise non-orthogonal in Q(6,q)) plus extra
points X, sigma(R) = lines of a spread plus one line per extra point, with the distance-4 relations matched type by
type (research/cell147/mirror/README.md). Checked instances (apsp_orb / apsp_mt all sources): (14,7) 1,774,632,
1,774,628, 1,774,588; (13,7) 1,064,472; (7,7) 23,598; (9,7) 118,238; (10,7) 225,152.
