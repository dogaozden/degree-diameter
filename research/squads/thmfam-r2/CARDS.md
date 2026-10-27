# Round thmfam-r2 (2026-10-28): LPS x Z_m covers - uniform label rules, and how far covers go

Kept from round 1: LPS x Z_m (c6, c7; 95-99% of the table with searched labels). Dropped: integer lifts, q-dependent
formulas, conic, torus orbits, larger symmetry (all at the random-draw level or worse).

- c1 Label rules, p = 5 (Delta 6). Grid q in {13,17,19,23,29}, m in primes = 1 mod 3 up to 61 (and a few composites
  like 49, 91). Rules: arith; cyc (1, t2) with t2 a fixed function of (m, r): 2, -1, -2, r+1, r-1, 2r, (m-1)/2, r^2+2,
  3, 5, ... (at least 12 rules); both --rk. Baseline: one random t2 per (q,m) (3 seeds). Score = best rule's mean
  excess over the FULL grid cells (lower is better); report also its vs_table at D = 8, 9, 10.
- c2 Label rules, p = 7 (Delta 8: two fixed letters, two 3-cycles). Grid q in {11,13,17,19,23}, m primes = 1 mod 3 up
  to 61 and |G| <= 1e7. Same protocol as c1.
- c3 Label rules, p = 11 (Delta 12, four 3-cycles) and p = 13 (Delta 14, two fixed, four 3-cycles). Grid q in
  {13,17,19,23} for p = 11 and {17,19,23,29} for p = 13 (q > p), m small primes = 1 mod 3 with |G| <= 1e7. Rules for
  (t1..t4): arith; (1,2,3,4); (1,r+1,2,2r+1); powers (1,g,g^2,g^3) of a fixed g mod m; etc., at least 10. Baseline:
  random labels (3 seeds). Score = best mean excess (report both p).
- c4 Push p = 5 covers past the 2013 table. Per-(q,m) search is allowed, any labels (free, non-equivariant too), any m
  (also composite, also without order-3 elements). Targets: (6,8) 29790 (e.g. q = 13 needs m >= 14, q = 11 needs
  m >= 23, q = 17 needs m >= 7), (6,9) 117360, (6,10) 452032 (q = 23 needs m >= 38, q = 19 m >= 66, q = 29 m >= 19).
  Hill-climb or sample labels; diameter must be <= D and the component FULL. Score = best vertices/table over the three
  cells (higher is better).
- c5 Push p = 7 covers past the 2013 table at (8,8) 201480 (q = 11 needs m >= 153; q = 13 m >= 93; q = 17 m >= 42;
  q = 19 m >= 30; q = 23 m >= 17) and (8,9) 1091232. Round 1 got q = 11, m = 151, labels cyc 1 57, diameter 8
  (98.9%). Free or equivariant labels, any m. Score = best vertices/table (higher is better).
- c6 Delta = 4 (p = 3, cycle type 1+3): LPS(3) x Z_m covers at the cells the lab does NOT beat: (4,8) 2184 and
  (4,9) 4970, and also (4,10) (table 11748, lab 12416). q in {5, 7, 11, 13, 17} (q > 3; q = 5 has |PGL| = 120), any m,
  free labels (4 of them: exhaustive search is cheap). Score = best vertices/table over (4,8), (4,9) (higher is better).
  A FULL graph beating 2184 at diameter <= 8 or 4970 at <= 9 would be a new lab record: re-check it with
  verify_cover.py AND with apsp (python3 component_edges.py pgl q m e.txt < lines; cc -O2 -o apsp
  /home/user/degree-diameter/research/lifts/coordinator_check/apsp.c; ./apsp e.txt 4 D).
- c7 Larger Delta: LPS(11) and LPS(13) covers at (12,9) 30001152 / (12,8) 4650100 and (14,9) 95087738 / (14,8) 14172480.
  This card may go to 4e7 vertices (one haar_ecc run then takes about a minute). Per-(q,m) label search allowed but
  budget about 25 evaluations. Score = best vertices/table over the four cells (higher is better). Also report how
  close plain LPS (m = 1) gets.
- c8 Audit the note numerically. Read research/theorems/HAAR_FAMILIES.md sections 1.2, 2 and 3 and test every
  displayed formula and identity on small primes with your own code: the relations of Lemma 2.3 (psi(i)psi(j) = psi(k),
  det, adjugate), Theorem 2.6(b) h psi(alpha) h^-1 = psi(sigma alpha) as matrices up to scalar, the neighbourhood
  formulas of Example 2.8 against the edges of the graph, Lemma 2.5(c) (ecc(I,A) = ecc(c,B)), Proposition 4.1 in one
  cover, and Corollary 3.4's inequality against research/theorems/haar_families/scan/lps_p*.txt. Also run apsp on four
  LPS graphs with q = 3 mod 4. Score = number of discrepancies (0 is good); list each in NOTES.md with the exact
  sentence of the note it concerns.
- c9 Wildcard: another definite quaternion algebra. Take the algebra with i^2 = -1, j^2 = -3 (norm a0^2 + a1^2 +
  3 a2^2 + 3 a3^2 on the order spanned by 1, i, j, k = ij), a set S of elements of norm p (choose a normalisation that
  gives p+1 classes, or just take all elements of norm p up to sign and units), map to PGL(2,q) by a splitting
  (find matrices I, J with I^2 = -1, J^2 = -3, IJ = -JI mod q), and measure: is the graph connected, its diameter, and
  is there a far vertex like psi(i) (distance about 4 log_p q)? Compare with Hamilton LPS at the same p. Score = the
  measured ratio d(far vertex)/log_p q at the largest q you can run (Hamilton's is 4).
- c10 Baselines for covers. For p = 5 and p = 7, on the grids of c1 and c2, the mean excess of ONE random label
  assignment per (q,m) (equivariant cyc with random t's, 5 seeds; and free random labels, 5 seeds), and of the best
  label per (q,m) where you can afford an exhaustive t2 search (p = 5 only). Score = p = 5 equivariant random mean.
- c11 Wildcard: nonlinear arithmetic labels. Labels z(alpha) computed from the quaternion alpha = (a0,a1,a2,a3) by a
  rule that is equivariant (z(sigma alpha) = r z(alpha)), e.g. z = f(a1) + f(a2) r + f(a3) r^2 with f(a) = a^2, a^3,
  sign(a), a mod 3, (a0 * a1), ..., or rules mixing a0. At least 10 rules, p in {5, 7, 13}, scored with cover_score.py
  on small grids. Score = best mean excess for p = 5 (and report p = 7, 13).
