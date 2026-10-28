# c7: LPS x Z_m (p=7, p=13), PGL(2,q) with labels

Construction. Generators from `lps_haar p q -v` (quaternion -> matrix). The cyclic shift
(a0,a1,a2,a3) -> (a0,a3,a1,a2) is verified to be conjugation by a PGL(2,q) element
(check_alpha.py), so S is alpha-closed. Orbits: p=7 gives 1+1+3+3; p=13 gives 1+1+3+3+3+3.
Fixed generators get z=0. A 3-cycle (g, ag, a^2 g) gets labels (t, r t, r^2 t), r^2+r+1=0 mod m,
with r-1 a unit mod m (valid m: products of primes = 1 mod 3). Sample for p=7: t1=1, t2 varied
(normalised by unit scaling). Graph = component of (e,A) of H(PGL x Z_m, S'); n = compA = |PGL| m.
Diameter = max(ecc(e,A), ecc(e,B)) from haar_ecc (valid by right-translation transitivity).

Files: c7lib.py (generators, orbits, labels), scan.py (per m scan), bis.py (largest valid m for given D,
K random label choices), check_alpha.py (automorphism check), batch.sh and batch.jsonl (results).
Sanity: p=7, q=11, m=1 gives n=1320, diam 6, matching lps_haar.
