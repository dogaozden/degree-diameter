# c16: explicit partial ovoids of W(q), q odd

Setting: W(q) on PG(3,q), x ~ y iff w(x,y) = x0*y2 + x1*y3 - x2*y0 - x3*y1 = 0. A partial ovoid = pairwise non-collinear points.
Script: `research/squads/gqd5-r1/c16/family.py` (run `python3 family.py 3 5 7 9 11 13`; gqlib check for q <= 11, numpy check for all q).

## Explicit family L (valid for every odd q, size q+1)

  L_q = {(0,1,0,0), (0,0,0,1)} u {(1,t,0,t^2) : t in F_q^*}

Proof of pairwise non-collinearity (w is the form above):
- (1,t,0,t^2) vs (1,u,0,u^2), t != u, both nonzero: w = t*u^2 - t^2*u = tu(u-t) != 0.
- (0,1,0,0) vs (1,t,0,t^2): w = 1*t^2 = t^2 != 0.
- (0,0,0,1) vs (1,t,0,t^2): w = -t != 0.
- (0,1,0,0) vs (0,0,0,1): w = 1 != 0.
So L_q is a partial ovoid of size q+1 for all odd q. It is the only explicit family here that is valid for every tested q with a formula.

## Measured sizes (q = 3..13)

| q | L_q (q+1) | cone (1,a,b,a^2) tabu | tabu max (all of W(q)) | Tallini q^2-q+1 |
|---|---|---|---|---|
| 3 | 4 | 4 | 7 (exact) | 7 |
| 5 | 6 | 10 | 18 (tabu, 30k its) | 21 |
| 7 | 8 | 21 | 33 (tabu) | 43 |
| 9 | 10 | 22 | - | 73 |
| 11 | 12 | 30 | - | 111 |
| 13 | 14 | 52 | - | 157 |

The cone column is a heuristic subset of the cone x0*x3 = x1^2 (points (1,a,b,a^2)); it is valid for each q but has no formula
(it is far from q(q-1)/2 for q >= 9, so the q(q-1)/2 coincidence at q = 5, 7 does not hold).

## Other candidates tested (negative or not uniform)

(i) Elliptic quadrics E relative to w.
- Random symmetric quadrics and quadrics Q(x) = w(x, Fx), F in GL(4,q), with q^2+1 points.
  Best partial ovoid inside E: q=3: 5 (= (q^2+1)/2) in most samples; q=5: 13 (= (q^2+1)/2) in about 10 of 200 samples, most samples 9-11.
  At q=7 (4000-iteration search, random symmetric quadrics) the sampled maxima were <= 13, far below (q^2+1)/2 = 25.
  The q=7 stronger-search run did not finish with captured output, so treat q=7 as unresolved. Not a formula.
- Hermitian model E = {P(t) = (N(t),1,t0,t1): t in F_{q^2}} u {(1,0,0,0)} (x0*x1 = x2^2 - nu x3^2): the halves
  {t : t square}, {t : t nonsquare}, {t : N(t) square}, {t : N(t) nonsquare} (with or without infinity) all contain
  collinear pairs for q = 3, 5, 7. Relative to w, w(P(t),P(s)) = N(t) s0 - N(s) t0 + s1 - t1, which is not a trace form.

(iii) Orbits of a cyclic subgroup of PSp(4,q). Random products of transvections give elements of projective order
(q^2+1)/2 (not q^2+1: -1 acts trivially on points). Orbits of size (q^2+1)/2 are partial ovoids only for some subgroups:
q=3: 4 of 8 orbits (size 5); q=5: 2 of 12 orbits (size 13); q=7, 9, 11, 13: 0 of 16, 20, 24, 28 orbits in 30-40 sampled subgroups.
So this route is not uniform in q.

(ii) Graph-type sets (1,a,b,f(a,b)) with f = a^i b^j: tabu gives 10 (q=5) and 21 (q=7) for the families a^2 b^j, which are
the cone family above (points (1,a,b,a^2)). A quadratic-character rule for the cone (B_a = {b: chi(b - k a^m) = s},
all k, m, s) gives no valid set for q = 3..11.

(iv) Not done.

## Status
Score (size at q = 11 of the best construction valid for all tested q, with a formula): 12 = q+1 from L_q.
Open: a formula of size near (q^2+1)/2 or q^2-q+1 for all odd q. Best leads: the (q^2+1)/2 half-elliptic-quadric
sets at q = 3, 5 (not extended), and exact/strong search inside E for q = 7, 9 to see whether a point-set pattern (e.g. E minus a
point, halved by a quadratic character of F_{q^2} in the Hermitian model with a different w-coordinatization) appears.
