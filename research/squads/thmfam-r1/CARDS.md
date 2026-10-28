# Round thmfam-r1 (2026-10-27): uniform families in the records' shape

Common preamble: PREAMBLE.md. Score = mean_excess of family_score.py over primes q in [23,113] (lower is better) unless
the card says otherwise.

- c1 Integer lifts, Delta = 6, type 3+3. S = O(X) u O(Y), O(X) = {X, wXw^-1, w^2Xw^-2}, w = [[0,-1],[1,-1]], X, Y in
  SL(2,Z) with entries in [-3,3], reduced mod q, group psl. Screen all pairs up to symmetry on --qs 29,41,53, full-score
  the 10 best. Question: do bounded-height (fixed integer) families beat a random draw (3.2-3.5) or lose like LPS (4.0)?
  Report the excess against max entry size.
- c2 Integer lifts, Delta = 7, type 1+3+3. Fixed letter in {I, w, w^2}, two orbits of small integer matrices (entries
  in [-3,3]). Same protocol as c1; run gen_random_orb.py q 1 2 seed (5 seeds) for the Delta = 7 random baseline.
- c3 Integer lifts, Delta = 8 (1+1+3+3, two fixed letters from {I,w,w^2}) and Delta = 10 (1+3+3+3). Entries in [-2,2]
  (search is larger); random baselines with gen_random_orb.py for both.
- c4 Integer lifts with a cyclic factor: G = PSL(2,q) x Z_m, alpha(x,z) = (w x w^-1, r z), m prime = 1 mod 3 in
  {7,13,19,31,37}, r of order 3 mod m. Delta = 7: letters (I,0), orbits of (X,t) and (Y,u):
  (X,t),(wXw^-1, r t),(w^2Xw^-2, r^2 t). Search small X, Y and t, u; score with --m m for each m. Does the cyclic factor
  lower the excess (excess uses |G| = |PSL|*m)?
- c5 Transport the records. Take research/frontier/sols/d7D8_psl_19_14_orb3_s1.txt, d6D9_sl_17_13_orb3f0_s2.txt and two
  more record files of your choice (sl/psl, prime q). Lift every matrix to SL(2,Z) with small entries (a matrix congruent
  to it mod p with determinant exactly 1), keep the z labels and m, and test the lifted set as a family over other primes
  q (group sl or psl as in the file, --m the file's n). Does a record stay good at other q? Report the excess per record.
- c6 LPS x Z_m, p = 5 (Delta = 6, type 3+3 under i->j->k). Labels must be equivariant: on each 3-cycle of the LPS set
  under the order-3 map (find the cycles from the quaternions printed by lps_haar -v), labels (t, r t, r^2 t) with r of
  order 3 mod m. For q in {13,17,23,29} and m prime = 1 mod 3 (7, 13, 19, 31, ...), search t1, t2 (this card MAY optimise
  per q) to maximise |PSL(2,q)| * m * 2 with diameter <= D for D = 8, 9, 10. Use haar_ecc pgl q m on lines from
  lps_haar -v with your z labels. Score = best vertices/table at D = 8, 9, 10 (report all three; higher is better here).
- c7 Same as c6 for p = 7 (Delta = 8, type 1+1+3+3) and p = 13 (Delta = 14, q in {17, 29, 37}). Fixed letters get z = 0.
- c8 Verify two theorems on small cases. (A) For p in {3,5,7,11,13,17,19,23,29} and q prime <= 61, q != p: psi(S_p) is
  closed under conjugation by psi(1+i+j+k) (compute it in PGL(2,q)), with cycle type 1+1+3^((p-1)/3) if p = 1 mod 3,
  3^((p+1)/3) if p = 2 mod 3, 1+3 if p = 3. (B) For q = 1 mod 4: d((e,A),(psi(i),A)) >= 4 log_p q - 2 log_p 2 (lps_haar
  prints both), and test whether it equals the least even L with 2 p^(L/2) >= q^2 - 1. (C) apsp.c all-pairs on 6 small
  LPS graphs (component_edges.py) vs haar_ecc. Score = number of failures (0 is good).
- c9 The far vertices of LPS graphs. For p in {5,7,13} and three primes q = 1 mod 4 each, list the A-vertices at
  distance >= ecc - 1 from (e,A) and identify each as psi(gamma) for a primitive integral quaternion gamma of least norm
  (search gamma with norm <= 200, compare in PGL(2,q)). Conjecture to test: the far vertices are psi(gamma) for pure
  quaternions gamma (a0 = 0) of small norm. Score = fraction of far vertices explained by pure gamma of norm <= 50.
- c10 Non-liftable families, Delta = 7 (1+3+3). Formulas using q-dependent field elements: a primitive root g mod q, a
  cube root of unity, a square root of -1 or of 2, inverses like 1/2, (q+1)/4, ... e.g. X = [[g,1],[0,g^-1]],
  Y = [[1,g],[g,1+g^2]], alpha = conjugation by w, fixed letter I. Try at least 12 formula variants; score each.
- c11 Non-liftable families, Delta = 6 (3+3) and Delta = 8 (1+1+3+3): formulas built from Dickson polynomials, the trace
  map, Legendre symbols or discrete logs (e.g. entries t, t^3, t^-1 with t a fixed power of a primitive root). At least 12
  variants, different from c10's primitive-root matrices.
- c12 Large-alpha families with Delta growing (D fixed). S = {I} u {t^i x t^-i : i} for a torus T = <t> of PSL(2,q)
  (split, order (q-1)/2, or non-split, order (q+1)/2), x generic, so Delta ~ q/2. For q <= 61 record the diameter and
  |G| / W(Delta, D), W(Delta,D) = sum_{j<D} (Delta-1)^j. Is the diameter constant in q (4? 5?)? Also try unions of 2-3
  T-orbits. Score = best |G|/W(Delta,diam) over q >= 31 (higher is better); flag loudly any family with diameter <= 4.
- c13 Random baselines (calibration). Delta = 6, 7, 8 (types 3+3, 1+3+3, 1+1+3+3): mean_excess of single random
  alpha-closed draws (gen_random_orb.py, 8 seeds each, psl and sl) and of random S without symmetry (write a generator,
  8 seeds), q in [23,113]. Report mean and standard deviation per (Delta, group, symmetric or not). Score = the Delta = 7
  psl symmetric mean.
- c14 Larger q. LPS p = 5 and the random alpha-closed baseline (Delta = 6, psl, 3 seeds): q primes in [113, 199] (|G| up
  to 3.9M; one run takes up to a minute; stay within 20 minutes total). Fit excess against log_5|G| for both: LPS should
  grow like (1/3) log_5|G|; random like log_5 log|G|. Score = fitted slope of LPS minus slope of random.
- c15 Single-orbit families with larger alpha. alpha = conjugation by an element of order k in PSL(2,q) with k = 5 or 6
  (needs k | (q-1)/2 or k | (q+1)/2), S = {I} u O(x) (Delta = k+1) or O(x) u O(y) (Delta = 2k), x, y fixed small
  integer matrices or formula-defined. q restricted to the admissible primes in [23,113]. Compare with the k = 3 families
  at the same Delta (random baseline via your own generator). Is a larger symmetry better or worse for uniform families?
- c16 Wildcard. Find a uniform family (S by a formula in q, maybe m) of a kind none of c1-c15 uses (their one-line
  summaries are above). Score it. Examples of directions not taken: the conic/orthogonal model (PSL(2,q) = SO(3,q)),
  unipotent-and-torus mixtures, Galois-invariant sets in SL(2,q^2) restricted, Kloosterman-type sets.
- c17 Wildcard, different from c16: families in SL(2,q) x Z_m where m grows with q (e.g. m = q or (q-1)/2) with labels
  given by a formula (discrete log, trace). Score with --m equal to your m(q) (run family_score once per q, or write a
  small loop). Look at excess with |G| = |SL| * m.
- c18 Wildcard, different from c16 and c17: "repair" the LPS family. Its far vertices are few (special tori). Add one or
  two extra letters given by a formula in q (keeping alpha-closure if you can) and see whether the excess drops below the
  random baseline at the new Delta. Compare with LPS at the same Delta where one exists.
