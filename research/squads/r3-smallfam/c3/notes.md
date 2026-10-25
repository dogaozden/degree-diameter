# c3 referee notes: SMALL_DEGREE_FAMILIES.md sections 2.2-2.3 and smallfam/cyclobound.py

Verdict: no error found in the Z_p fibre bound, or in the code's universal group, BFS, fibre count or unit and
admissibility reductions. One real gap (the squarefree-m remark, proof not valid as stated). Three smaller items.

## Proof, step by step

Conventions. (g,A)~(sg,B) and (g,B)~(s^-1 g,A) match the write-up and cyclocheck.py:39.

Normal form (section 2.2, md:139-145).
- H(G,S) = H(G,xSy) = H(G,sigma S): checked by hand. Left-translating S: map (g,B) to (xg,B). For y: (g,A) to (y^-1 g y, A) and (h,B) to (hy,B), which gives h g^-1 y in Sy. Automorphisms act on both sides.
- With e in S, H(G,S) is connected iff <S> = G.
- Conjugation by (c,0) sends (a,j) to (a + c(1 - r^j), j) (checked). For r^j != 1 in F_p, 1 - r^j is a unit, so the a-part can be killed (md:143). This step is the one that gives u_1 = (0;j1).
- The scaling a -> ua (md:145) is a correct automorphism, but the bound never uses a_2 = 1. psi(eps_0) = a_2 for any a_2, and the test below used unnormalised a_2. So the scaling is superfluous.

Universal group (section 2.3, md:175-190).
- (P;J)(Q;L) = (P + zeta^J Q; J+L) is associative. Inverse is (-zeta^-J P; -J).
- ev: Z[zeta] -> F_p, zeta -> r, is a ring map because Phi_o(r) = 0 mod p (o = ord r, p prime, so r is a primitive o-th root in F_p). Hence psi(P;J) = (sum_f ev(P_f) a_{f+2}, J) is a homomorphism, with psi(u_i) = s_i.
- phi(ball_U(start)) = ball_G(start) exactly, both directions: a G-walk with label sequence L lifts to the U-walk with the same labels.
- Diameter <= D iff both start balls are full (right translation is an automorphism). With the exact image equality, "each W_J maps onto F_p" is an exact characterisation, as md:183 says.
- Fibre bound: p <= |W_J| for each (start, side, J), so N = pk <= k min_J |W_J|. Valid.
- Unit reduction (md:191): Theta(P;J) = (sigma_u P; uJ), with sigma_u: zeta -> zeta^u a ring automorphism of Z[zeta_o] (gcd(u,o) = 1 because o | k and u is a unit mod k). Theta is an isomorphism U_j -> U_{uj} sending generators to generators, so fibre counts are permuted. Valid.
- Admissibility (md:190): gcd(j's, k) = 1 is a genuine connectivity necessity. "o does not divide j1" is a normal-form property (the element with non-trivial j is chosen so), not a disconnection criterion. The wording is loose; the bound is unaffected.

## Code (cyclobound.py) against the universal group
- zeta_powers (l.46-58): companion matrix of Phi_o, M[t] = C^t. Correct.
- cyclotomic (l.24-43): correct division of x^n - 1 by the proper-divisor cyclotomics.
- Generators (l.67-72): eps_{i-2} for i >= 2, zero for i < 2. Correct for F = Delta-2 slots.
- Side A step (l.94-95): (zeta^{j_i} P + eps_i; J + j_i) = u_i (P;J). Correct.
- Side B step (l.97-98): (zeta^{-j_i}(P - eps_i); J - j_i) = u_i^-1 (P;J). Correct.
- BFS with the keep filter (l.88-117): correct on a bipartite graph, since same-parity filtering matches BFS.
- Fibre count (l.118-126): k * min_J over each (start, side), then min over starts. Correct.
- Non-fibre (l.127-129): N <= min |ball on a side|. Valid.
- admissible_js (l.136-152): enumerates each unit-orbit of admissible j exactly once (checked, below).
- bound (l.155-164): maximum over admissible j. Correct except for the cache issue below.

## Tests run (all passed)

1. cyclocheck.py 3 5 10 (run with PYTHONDONTWRITEBYTECODE=1): 10 (group, S) pairs, 0 violations. Caveat: the
   U-side (cyclocheck.py l.52-101) reuses cyclobound.zeta_powers (l.55) and duplicates the BFS, so it does not test the
   universal group independently. It checks only the inequality G-count <= U-count. The G-side (l.14-49) is independent.
2. check_c3.py (this folder, pure Python, about 8 s). Independent Z[zeta]/Phi_o arithmetic (Phi_o from numerical roots,
   own reduction), own group tables, unnormalised random a_2, Delta = 3 and 4, D = 4-5, seven groups
   (p,k,r,o) = (7,6,2,3), (7,12,2,3), (7,6,6,2), (13,12,5,4), (11,10,2,10), (11,5,3,5), (19,9,4,9):
   - psi is a homomorphism (random pairs) and psi(u_i) = s_i: passed.
   - psi(ball_U) equals ball_G exactly, per start, side and fibre (set equality): passed.
   - cyclobound.ball_bound with FIBER on and off equals the values computed here: passed on every sample.
   - Soundness: 47 connected Haar graphs, each with exact diameter D0 (BFS from all vertices). ball_bound(Delta, D0, k, o, j) >= N in every case.
   - admissible_js equals brute-force unit-orbit classes (2,799 classes over k in {4,6,8,9,10,12}, o | k, Delta in {3,4}), with no duplicate yields.
   - ball_bound (fibre) is invariant under j -> u j.

## Findings

1. GAP, squarefree remark (md:226-227): "For squarefree m, replace Z[zeta_o] by Z[x]/(product of the distinct Phi_{o_i})
   ... The same argument works." This is not justified by the argument given.
   - The normal form needs conjugation to kill a-parts, which requires 1 - r^j to be a unit. For composite m this fails.
   - Counterexample to the step: m = 15, r = 7, o = 4. Since 7 = 1 mod 3, 1 - 7^j = 0 mod 3 for all j
     (computed: [0,0,0,0] for j = 0..3). Conjugation by translations never changes the mod-3 part of a. For (a,j) = (10,1)
     no c in Z_15 gives a + c(1-7) = 0 mod 15 (computed: no solutions).
   - So S need not contain (0,j1) with zero a-part, and the Delta-2 universal group of cyclobound.py is not justified for composite m.
   - Also Phi_4(7) = 50 = 5 mod 15, so Z[zeta_4] -> Z_15 is not a ring map. The product ring is needed: f(7) = (6)(50) = 300 = 0 mod 15 (computed).
   - What does go through (by the section-2.4 argument, not tested here): Delta-1 formal slots with no normal form, psi(P) = sum_i ev(P_i) a_i.
   - Consumer: recordbound_sqf.py monkeypatches zeta_powers and uses Delta-2 slots for composite m, so it inherits the gap. I did not check what it is used to exclude.
   - I did not find a Haar graph that violates the Delta-2 bound for composite m. The gap is in the proof, not a demonstrated counterexample.
2. Docstring bug, cyclobound.py l.6: "u_i = (eps_{i-1}; j_i) for i >= 2". It should be eps_{i-2}. The code (l.71) and md:175 use i-2, and that is the correct one for F = Delta-2 slots. Documentation only.
3. Latent cache bug, cyclobound.py l.155-156: bound()'s cache key (Delta, D, k, o) ignores the global FIBER. Mixing FIBER=False and FIBER=True in one process would return stale values. No current script does this: cyclotable.py l.7-9, jfibre.py l.8, cyclotable4.py l.6 and recordbound*.py set FIBER before use. Fix: add FIBER to the key.
4. Provenance, not the proof itself: frob_scan.py l.103 now reads `range(a.kmin, min(a.nmax // p, p) + 1)`, i.e. k <= p. runs/frob_d3D7.txt contains 41 rows with k > p (e.g. "7 12 2 3 84 168 ..."), so the Delta=3 runs predate the current script and cannot be regenerated with it. The write-up's Delta=3 completeness claim (md:241-244) rests on those runs. The k-range does reach the Moore bound (p=3 up to k=42; 3*42 = 126 <= 127). Worth one sentence in the write-up.
5. Wording, md:190: see Admissibility above.

## Not checked
- The numerical tables (cycloindex, cyclotable, cyclosummary outputs) and the 1,639-group scan contents.
- Literature (c1's job).
- recordbound_sqf.py beyond the monkeypatch.
