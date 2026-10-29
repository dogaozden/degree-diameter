# c5 review of research/synthetic/CONICS.md, sections 0.1, 2, 3 (and 0.2)

Method: web sources (listed per claim), a brute-force check of W(2) (code: check_w2.py in this directory),
and counting arguments. SYNTHETIC.md, which defines (L0) and (C) in Theorem D, is not in this repo, so those
conditions and the rest of Theorem D could not be checked.

## Claims (a)-(i)

(a) CONFIRMED. W(q) has a polarity iff q = 2^(2e+1); absolute points form a Suzuki-Tits ovoid (e >= 1); absolute
lines form a spread.
  - Tits; a 1994 Philippine master's thesis (https://animorepository.dlsu.edu.ph/etd_masteral/1641) states the
    e >= 1 form. Did not check Payne-Thas directly.
  - The spread claim follows from the ovoid property: the absolute lines through x correspond to the absolute
    points on theta(x), and an ovoid meets every line once.
  - Nit: for e = 0 (q = 2) the absolute points form an elliptic quadric, not a Suzuki-Tits ovoid. Brute force
    on W(2): 36 involutive dualities, 5 absolute points, 5 absolute lines, ovoid and spread verified.

(b) WRONG in part.
  - "H(q) has a polarity iff q = 3^(2e+1)": the existence part is supported by https://arxiv.org/pdf/0909.3211
    (Ree hexagon has a polarity). I did not find a source for the "only if" part. Could not check the "only if".
  - "absolute points form the Ree-Tits ovoid": CONFIRMED (same source: an ovoid; the Ree group acts 2-transitively
    on them, so there are q^3+1 of them).
  - "absolute lines form a spread": WRONG. The absolute lines are theta(O), so there are q^3+1 of them. A spread of
    H(q) has (q+1)(q^4+q^2+1)/(q+1) = q^4+q^2+1 lines. Counting shows the absolute lines cannot cover all points:
    each point x lies on at most one absolute line (absolute lines through x correspond to absolute points on
    theta(x), and pairwise opposite points are not collinear), and the absolute lines cover (q^3+1)(q+1) points,
    fewer than (q+1)(q^4+q^2+1). Correct statement: the absolute lines form an ovoid of the dual hexagon H(q)^D
    (q^3+1 pairwise opposite lines, one per "star"). The same error appears in the table of 0.1 and in the word
    "absolute spread" in 3.2.

(c) CONFIRMED in substance, with a caveat on the exponent.
  - Thas: H(q) has an ovoid iff Q(6,q) does; H(q) has no ovoid for q even. Source: the Thas abstract,
    https://springerlink.bibliotecabuap.elogim.com/content/pdf/10.1007/BF01447417.pdf
  - BGS06 (abstract): no ovoid of Q(6,q) for prime q > 3 (DOI 10.1007/s10623-005-5666-0; abstract only, as seen in
    search results).
  - Existence for q = 3^h: Bartoli-Durante report "two families of ovoids for Q(6,3^h)". The Thas abstract snippet
    gives 3^(2h+1) for Q(6,q). The sources disagree on the family, so I could not settle the exact exponent.

(d) CONFIRMED with a caveat. Distance-2 ovoids of H(q) are known for q = 2, 3, 4 (Bishnoi-Ihringer,
https://arxiv.org/pdf/1606.07288). "Only" describes the known examples; nonexistence for other q is not proved.

(e) CONFIRMED in substance. Partial ovoids of W(q), q odd, have at most q^2-q+1 points. Klein-Metsch (Innovations
in Incidence Geometry, 2005) prove that a partial spread of Q(4,q) with more than q^2-q+1 lines lies in a spread.
Q(4,q) has no spread for q odd, and W(q) is dual to Q(4,q). Tallini (1991) is the attribution given by De Winter
and Thas. I did not see Tallini's paper itself. Sanity check: W(3) has maximum partial ovoid 7 = 9-3+1.

(f) CONFIRMED. Every ovoid of Q(4,p), p prime, is an elliptic quadric (Ball-Govaerts-Storme, DCC 38 (2006) 131-145;
abstract only, DOI 10.1007/s10623-005-5666-0).

(g) WRONG as stated (the definition). The hyperplane H of PG(6,q) with H cap Q(6,q) = Q^-(5,q) contains only
(q+1)(q^3+1) of the (q+1)(q^4+q^2+1) points of H(q). Every line of H(q) inside H covers only points of H, so the
lines of H(q) in Q^-(5,q) cannot be a spread of H(q). Example: q = 2 gives 27 of 63 points. What they form is a
spread of the quadric Q^-(5,q), which has q^3+1 lines. The "Hermitian spread of H(q)" is a different object (q^4+q^2+1
lines, locally Hermitian). Existence "for every q" with the attribution to Thas 1980 could not be checked; the
search found the 1980 JCTA paper but not its statement. The sentence in 3.1 should be rewritten.

(h) PARTLY CONFIRMED, partly WRONG.
  - Folding lemma 0.1: proof checked line by line (degree = lines through p minus [p absolute]; adjacency symmetric
    since p I theta(r) iff r I theta(p); for p != r the parities of d(p,r) and d(p,theta(r)) differ, so the minimum
    is <= D-1). Brute force on W(2), j = 0: 15 vertices, max degree 3, diameter 3. CONFIRMED.
  - Prop 2.2 (W(2^(2e+1)) with j clones and j shadows): theta' swaps clone i of p with shadow i over theta(p) and
    original points with original lines. Incidence is preserved in every case (checked for point-line, clone-line,
    point-shadow, clone-shadow; points-points never incident). Brute force on W(2), j = 1, 2: self-polar, 20 and 25
    vertices, max degree 4 and 5, diameter 3. Formula (q+1+j)(q^2+1) checked at q = 2. CONFIRMED.
  - Self-polar doubling (3.2): the component count "q^3+1 flags (p, theta(p))" is correct only if Sigma = theta(O)
    has q^3+1 lines. It does (see (b)), so the proof works, but the word "absolute spread" is wrong. The conditions
    (L0) and (C) cannot be checked (SYNTHETIC.md missing). Diameter 6, max degree q+m and element count could not be
    checked. The arithmetic 364+28 = 392 for q = 3, m = 2 is correct, and 392 < 650 is correct.

(i) NUMBERS.
  - (15,2) = 190 (Wikipedia, footnote Yugeswardeenoo 2026): CONFIRMED.
  - (15,2) = 187 (Canale 2012, UPC table): could not check (the table is not in the search results).
  - (9,3) 585, (10,3) 650, (11,3) 715: CONFIRMED (Wikipedia, footnote Delorme 1985). The note's expectation that
    these are polarity graphs of W(8) is consistent with that attribution; I did not check the construction.
  - (12,3) 810: CONFIRMED (Wikipedia, Yugeswardeenoo 2026).
  - (5,5) 650: CONFIRMED (Wikipedia, Rithwik Gupta 2026).
  Source: https://en.wikipedia.org/wiki/Table_of_the_largest_known_graphs_of_a_given_diameter_and_maximal_degree

## Other statements in 0.1, 2, 3

- 0.1 table: Hexagon "distance-3 ovoid, pairwise opposite, q^3+1": CONFIRMED (opposite = non-perpendicular in Q(6,q),
  counted: q^5 opposite points). Plane row: CONFIRMED (conic = oval for q odd; Segre). Hermitian-curve row: CONFIRMED.
- 0.1 table: "Q(6,q) elliptic sections Q^-(3,q) are partial ovoids (q^2+1)": CONFIRMED (no lines in Q^-(3,q);
  points pairwise opposite in H(q)).
- 2.1: "W(q) and Q(4,q) are dual and not isomorphic for q odd": CONFIRMED (W(q) ovoid iff q even).
- 2.2: "for q odd, W(q) has no ovoid and Q(4,q) no spread": CONFIRMED.
- 2.2: "at most q^2-q+2" (Tallini + 1): consistent with (e).
- 2.2: "CDPS22 partial ovoids are far smaller": could not check.
- 2.2: lab searches 52, 72, 92 and 61, 97, 141; (7,4)=359; 2.3 Theorem A details: lab-internal, could not check.
- 2.4: "At q=8: 585, 650, 715 for j=0,1,2; j=3 gives 780 < 810": arithmetic and the Wikipedia values CONFIRMED.
- 3.3: "1+11*29 = 320" and "1+5*7 = 36": arithmetic CONFIRMED. "the point set of a spread ... is the largest one": UNCLEAR
  (a spread covers every point, so "point set of a spread" needs a definition).
- 3.2: "q^2-1 further Hermitian spreads through v": could not check.

## Summary

Score (number of wrong claims among (a)-(i)): 3.
  1. (b) "absolute lines form a spread" (and "absolute spread" in 3.2 and the 0.1 table): wrong; they are q^3+1 lines
     forming a dual ovoid.
  2. (g) "the lines of H(q) in an elliptic hyperplane Q^-(5,q) form the Hermitian spread of H(q)": wrong as stated.
  3. (h) self-polar doubling: "absolute spread" label wrong; the proof works with the dual ovoid.
Could not check: (b) "only if" for polarities, (c) exponent family, (g) existence for every q, (i) 187 (Canale), and the
rest of Theorem D (L0), (C).
