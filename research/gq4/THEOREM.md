# Diameter 4 from the quadrangle Q(4,q): copies of an ovoid and of a line multiset

## Prior art (novelty check by novelty-sonnet, 2026-10-18)
- Vertex duplication is Delorme & Farhi (IEEE Trans. Comput. C-33, 1984, 857-860). Delorme, "Grands graphes de degre
  et diametre donnes", Europ. J. Combin. 6 (1985) 291-302, Sec. 7 (nested duplication, kept bipartite) and Sec. 8(a)
  (generalized quadrangles, duplicating an ovoid-type set of points at mutual distance 4) give exactly the table
  values 346, 1734, 3064, 4946 and 5134. So **the ovoid-copy part is Delorme's (1985)**.
- New here (no prior art found): adding copies of a line multiset with every point on at most j entries (partial
  spreads larger than the q+3 extra vertices Delorme gets, partial 2-covers, j-covers via Bamberg-Law-Penttila
  m-ovoids), and the AS(q) construction (research/gq4x/), which no degree-diameter paper uses.
- Earlier wording here said the table values "are the case s = q+3". That is a count match only: Delorme's q+3 extra
  vertices are not a partial spread. Read "same order as Delorme's", not "equal to".
- Related: Araujo-Pardo, Dalfo, Fiol, Lopez, arXiv 2103.11443, Sec. 4 (Thm 4.3, 4.5(ii)): duplicating every line of
  a GQ ("semi-double graph"), biregular [r,2r;4]. Cage papers (arXiv 2310.12137, 1111.3279) delete GQ substructures;
  none adds copies. Araujo-Pardo & Lopez, arXiv 2005.02427, Problem 4 asks to generalize their diameter-3
  construction to diameters 4 and 6; the AS(q) result is a diameter-4 answer.
- Not read (paywalled): Delorme, J. Graph Theory 9 (1985) 325-334; Bond-Delorme, Ars Combin. 25C (1988).

Draft, 2026-10-18. Proof complete; the size of the line multiset is the open input (see the last section).

## Setting

Q(4,q) is the generalized quadrangle of order (q,q) (points and lines of a non-singular quadric in PG(4,q)).
It has (q+1)(q²+1) points and as many lines; every line has q+1 points, every point is on q+1 lines, and
(GQ axiom) for a point x not on a line L there is exactly one point of L collinear with x.

Its incidence graph G is bipartite, (q+1)-regular, of girth 8 and diameter 4. Distances in G:
- two distinct points: 2 if collinear, 4 if not;
- two distinct lines: 2 if they meet, 4 if disjoint;
- a point and a line: 1 if incident, 3 if not (by the GQ axiom).

An ovoid O of Q(4,q) is a set of q²+1 points meeting every line in exactly one point (Q(4,q) has ovoids for
every q, e.g. an elliptic quadric section).

## Construction

Fix j ≥ 1. Let M be a multiset of lines in which every point lies on at most j lines (counted with
multiplicity); call t = |M|. Build H from G by adding
- j copies of each point of O, each copy adjacent to exactly the lines through its point;
- one copy of each entry of M, each copy adjacent to exactly the points of its line.

## Theorem

H is bipartite, has maximum degree q+1+j, diameter 4, and order

    n(H) = 2(q+1)(q²+1) + j(q²+1) + t.

## Proof

Bipartite: point copies are adjacent only to lines, line copies only to points.

Degrees: a copy has degree q+1. An original line gains exactly j neighbours (the j copies of the one point of
O on it). An original point gains one neighbour per entry of M through it, at most j.

Diameter: H contains G, so distances between original vertices are at most 4. A copy v′ of v has N(v′) = N(v),
so for every vertex w other than v′, any walk from v to w can be started at v′ instead; hence
d(v′, w) ≤ max(d(v, w), 2) ≤ 4, with d(v′, v) = 2. Applying this to both ends handles two copies. So diameter ≤ 4,
and it equals 4: two non-collinear points of G have no common neighbour in H either (every new line has the
point set of an old line), so they stay at distance 4. ∎

## Which multisets

- j = 1: M is a partial spread (pairwise disjoint lines), t = s ≤ q²+1, with t = q²+1 a spread (exists iff q is
  even). For q odd, s ≤ q²−q+1 (Tallini; dual partial ovoids of W(q)).
- j = 2: every point on at most 2 entries; t ≤ 2(q²+1), with equality exactly for a 2-cover of Q(4,q), dually a
  2-ovoid of W(q). A doubled partial spread gives t = 2s, but larger t may exist.

## Against the table (bipartite degree–diameter, diameter 4)

The table entries at degrees 7, 11, 13, 15 have the same order as the case j = 1, s = q+3, q odd (Delorme 1985,
Sec. 8(a); a count match, not the same graph): 346 (q = 5), 1734 (q = 9), 3064 (q = 11), 4946 (q = 13). The degree-16 entry 5134 equals the case
j = 2, q = 13, t = 34. So any partial spread with more than q+3 lines beats the table at degree q+2. (Whether
other degrees fit the same pattern is being checked against the full table.)

Records from this construction (all checked by scripts/verify_record.py):

| cell | q | j | t | order | table |
|---|---|---|---|---|---|
| (7,4) | 5 | 1 | 21 | 359 | 346 |
| (11,4) | 9 | 1 | 52 | 1774 | 1734 |
| (13,4) | 11 | 1 | 72 | 3122 | 3064 |
| (15,4) | 13 | 1 | 92 | 5022 | 4946 |
| (16,4) | 13 | 2 | 340 | 5440 | 5134 |

(The (16,4) row uses a partial 2-cover of 257 lines found by annealing, 2026-10-18; the earlier 184 was a doubled
partial spread. Since then AS(q)-based graphs (research/gq4x/) give (11,4) 1782, (13,4) 3146, (15,4) 5070.)
(The (7,4) and (11,4) graphs were found by Haiku islands on 2026-10-10 and fit this shape after the fact.)

## Corollary for even j (2026-10-18, from the literature)

Bamberg, Law, Penttila, "Tight sets and m-ovoids of generalised quadrangles", Combinatorica 29 (2009) 1-17, construct
m-ovoids of W(3,q) for q odd and every even m. W(3,q) is dual to Q(4,q), so an m-ovoid of W(3,q) is an m-cover of
Q(4,q): a set of m(q^2+1) lines with every point on exactly m of them. Taking M = a j-cover (j even) gives

    for q odd and j even:  n_b(q+1+j, 4) >= 2(q^2+1)(q+1+j).

j = 2, q = 13: (16,4) >= 5440 (table 5134). Explicit since 2026-10-18 (twocover-opus, research/gq4y/): in PG(3,q) =
GF(q^4)*/GF(q)* with B(x,y) = Tr(d x y^(q^2)), d = g^((q^2+1)/2), the shift by g^(q+1) preserves W(3,q); its orbits are
the residue classes mod q+1, and classes a and q-a together form a 2-ovoid (checked by computer for q = 3,5,7,11,13;
no general proof written). Mapped to Q(4,13) by the Klein correspondence: 340 lines, every point on exactly 2.
This meets the construction's ceiling 2(q^2+1)(q+3) at (16,4).
Proposition C (writeup-opus, 2026-10-18; full proof in research/NOTE.md): the pairing a <-> q-a gives a 2-ovoid of W(3,q)
for every odd prime power q (the classes are Ebert's partition of PG(3,q) into elliptic quadrics; a discriminant
identity D(h nu^q) = N(h) D(nu) with N(h) a non-square makes the two counts 1+chi and 1-chi). Computer check also
for q = 9, 25, 27 (research/gq4y/w3_singer_pp.py). Also: the cells covered by the construction in the
table are exactly the diameter-4 degrees with Δ-1 not a prime power (7, 11, 13, 15, 16); every other degree up to
16 has a generalized quadrangle incidence graph, which meets the Moore bound and cannot be beaten.

Partial spreads for all odd q: Tallini ("Fibrations through lines in a nonsingular quadric Q(4,q) of PG(4,q)", Atti Accad. Peloritana
Pericolanti 66 (1988) 127-146, as cited in arXiv 2203.04553) constructs a maximal partial ovoid of
W(3,q), q odd, of size 2q+1 (cited in Ceria-De Beule-Pavese-Smaldore, arXiv 2203.04553, Section 1; the
construction itself not yet seen). So for every odd q >= 5 the j = 1 case beats Delorme's family
(order of s = q+3) by at least q-2.

## Open inputs (being checked)

1. A construction of a partial spread of Q(4,q) with more than q+3 lines for every odd q (Tallini's 2q+1 is
   reported; source being confirmed). With it, the theorem beats Delorme's 1985 family for all odd q ≥ 5 by at
   least q−2.
2. j = 2, q = 13: a 2-cover of Q(4,13) (2-ovoid of W(13)) would give (16,4) ≥ 5440. Literature and a computer
   search are running.
3. What the table holds at degrees 3–16 for diameter 4 (check that no other cell fits the shape).
