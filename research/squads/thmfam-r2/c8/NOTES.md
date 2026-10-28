# Card c8 (round thmfam-r2): numerical audit of HAAR_FAMILIES.md sections 1.2, 2, 3 (+ Prop 4.1, Cor 3.4, item 7)

Arithmetic: own Python only (qlib.py, test_a.py ... test_f.py). The lab's C tools were not used for arithmetic.
Exception as the card asks: item (7) runs the lab's component_edges.py, haar_ecc and apsp.c (apsp compiled from
coordinator_check/apsp.c into this folder). The note was edited by the director while this audit ran; the version
checked is the 567-line file read at 2026-10-28 00:00 UTC.

## Discrepancies (score counts these)

1. Sentence (Appendix B, paragraph after the table): "At odd D the largest q reached equals the limit of Theorem 3.2
   in 6 of the 10 unlimited odd cells and is the prime just below it in the other 4 ((6,9): 29 against 31;
   (8,11): 173 against 181; (14,7): 59 against 61; (14,9): 233 against 239)."
   Computed (test_f.py, scan/lps_p*.txt, limit = largest prime q with q^2 < 2p^floor(D/2)):
   the unlimited odd cells with Delta >= 6 are (6,7),(6,9),(6,11),(8,7),(8,9),(8,11),(12,7),(12,9),(14,7),(14,9) (10 cells).
   Equality with the limit holds in 5 of them: (6,7) 13, (8,7) 23, (8,9) 67, (12,7) 47, (12,9) 167. Not 6.
   The 4 named cells are right (29/31, 173/181, 59/61, 233/239). The other exception is (6,11): limit 79
   (79^2 = 6241 < 6250), largest scanned q with diameter <= 11 is 67, and q = 71, 73, 79 have diameter 12
   (scan/lps_p5.txt lines 17-19). So 67 is not "the prime just below" 79 (73 is). Including Delta = 4 (all equal there)
   gives 8 of 13, still not 6.

## Unverified or defects (not counted in the score)

- Appendix B table has a header and separator row only, no data rows; the line "Scan limits: ." is empty. The summary
  item 2 ("2.5 to 19 times below the 2013 table at D = 8-10 (Appendix B)") cites this empty table.
- Same summary sentence, the upper end "19": from the scan logs and the 2013 table values in the brief, table/LPS
  ratios at D = 8-10 for the cells with table entries are 2.45 (6,8), 3.04 (6,10), 3.63 (8,9), 3.77 (4,9), 4.82 (6,9),
  5.38 (4,10), 5.66 (8,10), 6.44 (12,9), 6.50 (4,8), 6.77 (8,8), 7.52 (14,9), 10.94 (14,8), 12.99 (12,8) (test_e.py).
  No cell gives 19. The brief does not give table values for (12,10) or (14,10), so the upper end is unverified.
- Section 4.2 table cell "(8,9) | [[C7_89]]": unfilled placeholder.
- Appendix A line "[[SQUADS]]": unfilled placeholder.
- Section 3.5: "The eccentricity of (I, A) exceeds L0 by 0, 1, 2 or 3 (in 76, 151, 22 and 2 of the 251 cases)".
  Partly checked: p in {3,5,7,13}, q <= 41 (37 cases, own BFS): excess 0 in 16, 1 in 18, 2 in 2, 3 in 1 (p=13, q=17,
  ecc 7, L0 = 4). Consistent with the sentence; the full 251 cases (q up to 160, p = 11, 17, 19, 29) were not re-run.
- Example 2.8 in the earlier version of the note read "(x = 2, y = 3)", which does not satisfy x^2 + y^2 + 1 = 0 mod 13
  (value 1). With it the component of (I,A) has 312 vertices, ecc 9. The current text uses (x, y) = (0, 5), which is valid,
  and gives 2184 vertices and diameter 7 (own all-pairs BFS, allpairs_py.py 5 13). Fixed in the current version, not counted.

## Checks that passed (no discrepancy)

- (1) Lemma 2.3, all (q, x, y) with q in {5,...,23} and every solution x^2+y^2+1=0: I_^2 = J^2 = K^2 = -I, I_J = K, JK = I_,
  K I_ = J; displayed psi equals a0 + a1 I_ + a2 J + a3 K; psi multiplicative; det psi = N; adj psi(alpha) = psi(conj alpha);
  psi onto M2(F_q) and kernel = qH(Z) for q <= 7 (exhaustive). S_p has p+1 elements for p in {3,5,7,11,13,17}; the p+1 points
  are distinct and closed under inversion; det psi(alpha) = p mod q; PSL coset iff p is a square mod q (Lemma 2.4, 2.5(a)).
- (2) Theorem 2.6: h = psi(1+i+j+k) equals the explicit matrix of Example 2.8; det h = 4; h^3 = -8I; h psi(alpha) h^-1 =
  psi(sigma alpha) as exact matrices for all alpha with coordinates in [-2,2] and several q; zeta i zbar = 4j; cycle
  types on psi(S_p) are 1+3 (p=3), 3+3 (5), 1+1+3+3 (7), 3^4 (11), 1+1+3^4 (13), 3^6 (17), 1+1+3^6 (19); fixed points are
  exactly the a1=a2=a3 ones, with count 1, 0, 2 as stated. Example 2.8 cycle claims 1+2i -> 1+2j -> 1+2k -> 1+2i and the
  -2 version hold for q in {13,17,19,23}.
- (3) Example 2.8 neighbourhood formulas (A-side and B-side, literal signs) equal the generator-edge neighbours for every
  vertex of H(PGL(2,q), psi(S_5)) for q = 11 and 13 (valid (x,y)); 2184 vertices and diameter 7 for (0,5) at q = 13.
- Section 1.2 counts: PG(3,q) has (q+1)(q^2+1) points, the quadric (q+1)^2, PGL q(q^2-1), PSL q(q^2-1)/2 (q = 3, 5, 7).
- Lemma 3.1 (3600 random walks: p in {3,5,7,13}, 3 primes q each, 300 walks each): endpoint = psi(beta), N(beta) = p^L, beta = 1 mod 2H.
- Theorem 3.2 (a) and (b), for p in {3,5,7,13} and all primes q in (p, 41]: d((I,A), psi(i)), d(psi(j)), d(psi(k)) >= L0 for
  all, with equality for p = 5, 13 (dist = L0 in every case). Corollary 3.3 inequalities hold.
- Item (6), Corollary 3.4 (test_d.py): all 214 lines of scan/lps_p*.txt satisfy n < sqrt(2) p^(1-D/4) M^b(p+1, D),
  q^2 < 2p^floor(D/2), n < 2^(3/2) p^(3 floor(D/2)/2) and n < 2^(3/2) p^(3D/4), with M^b(p+1,D) = 2 sum_{j<D} p^j.
  Largest n/bound = 0.565 (p=3, q=7, D=6, n=336). All scan vertex counts equal q(q^2-1) m.
- Item (7) (q = 7, 11, 19, 23, p = 5, generator lines from our own psi): component_edges.py + apsp.c, haar_ecc and the
  scan diameters all agree: 6, 7, 8, 8. Own all-pairs BFS agrees for q = 7 (6) and q = 11 (7).
- Section 2.2 remark: component of (I,A) has q(q^2-1) vertices for p in {3,5,7,13}, q <= 41 (own BFS), and in all scan lines.
