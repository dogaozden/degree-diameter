# c16 (wildcard): Cayley-transform / conic model families

Family: S = C(O(X)) u ... with C(X) = ((1+n)I - 2X)/(1-n), X = [[x,y],[z,-x]] integer trace-zero, n = x^2+yz.
C is the Cayley transform of the conic/SO(3) model: C(X) = (1-X)(1+X)^-1, det 1, entries rational of height ~ |X|^2.
O(X) = {C(X), C(wXw^-1), C(w^2Xw^-2)}, w = [[0,-1],[1,-1]] (C is equivariant, checked). Fixed letters: I; C(X0) = w^2
for X0 = [[1,-2],[2,-1]] (checked mod 23). Generator: gen_c16.py. Screen: screen.py, run_screen_*.py.

Full-range scores (family_score, psl, q in [23,113], 22 primes; random = gen_random_orb.py, seed 1 unless noted):
- Delta 6, conic O(-1,-1,-1)+O(1,1,-1): 3.586   | random (0 fixed, 2 orbits, seed 1): 3.177
- Delta 7, conic I+O(-1,-1,-1)+O(-1,1,1): 3.372 | random (1 fixed): 3.054 (seed 1), 3.236 (seed 2)
- Delta 8, conic I+C(X0)+O(1,-1,-1)... see command: 3.344 | random (2 fixed): 3.253 (seed 1), 3.299 (seed 2)
Screens on q in {29,41,53} ranked the conic pairs at 3.23 (D6), 2.89 (D7), 3.01 (D8), but full range did not confirm.

Other variants (screen q = 29,41,53, mean_excess): Kloosterman T(a) sets {a} (Delta 6: 5.7-7.0; Delta 7: 5.9; Delta 8: 5.1),
continuant words T(a)T(b) (Delta 6: 6.2-9.9), unsymmetric Cayley 6-sets (Delta 6: 3.23-3.57, same as conic).

Conclusion: no conic/Cayley family beats the random alpha-closed baseline at the same Delta on the full range.
Kloosterman and continuant sets are clearly worse (their products stay in a thin set of small height).
