# c9: quaternion algebra (-1,-3), Haar graphs on PGL(2,q)

Files: gen_c9.py (S, splitting psi, generators), haar_dist.c (BFS, distances to targets, last layer), run_c9.py (sweep),
farnorm.py (min quaternion-norm lift of far-layer vertices), pybfs_check.py (independent python BFS), results_units.tsv,
results_sign.tsv, work/ (generators, targets, last layers).

Setup: psi(a0+a1 i+a2 j+a3 k) = a0 + a1 I + a2 J + a3 IJ, I=[[0,-1],[1,0]], J=[[x,y],[y,-x]], x^2+y^2=-3 mod q.
Start vertex = identity (e,A) (the card's "(I,A)" read as the identity, since psi(i)=I would make it trivial).

Count of norm-p elements of Z<1,i,j,k>: 2(p+1) classes up to sign (12, 16, 24 for p=5,7,11); (p+1) classes up to units
{+-1,+-i} (6, 8, 12). Units: the order has unit group of order 4, so the sign-only set contains alpha and alpha*i.
Consequence: the sign-only S makes psi(i) = psi(alpha)^{-1} psi(alpha i) at distance 2 for every q (degenerate). The
units (p+1) set is the intended graph and is reported as the main result.

Results (units, p+1 classes):
- Component of (e,A) has q(q^2-1) vertices for every q tested (q <= 97, p in {5,7,11}); = |PGL|, i.e. one PSL-coset pair.
- diam = max(ecc) = 12 (p=5, q=97), 10 (p=7, q=97), 8 (p=11, q=97).
- d((e,A),(psi(i),A)) = 12, 10, 8 at q=97: same as the Hamilton threshold formula (least even L with 2p^(L/2) > q^2).
  Matches the formula for 65 of 66 (p,q) pairs; exception (p,q)=(5,61): measured 12, formula 10.
- psi(i) is itself a far vertex (distance = diam) at p=5, q=61, 83, 97; far layers at other q are psi(j)-type
  (norm 3) or small-norm elements (norms 1, 2, 3, 10, ...), and some far layers are dominated by many norm 40-300 classes.
- psi(j), psi(k) (norm 3) lie in the other PSL-coset when (3/q) differs from the square class needed; the distance is
  -1 when unreachable (-1 in the tsv).
- Score: d(psi(i))/log_5 q at q=97 = 12/2.842 = 4.22 (Hamilton formula gives the same 12 at q=97).
Cross-check: python BFS (pybfs_check.py) agrees at (5,7), (5,11), (7,13).
