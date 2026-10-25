# Numerical sanity check of the proved identities/rules on the known k=5 incidence matrix (N[point, line]).
import sys, itertools
import numpy as np
N = np.load('/home/user/degree-diameter/research/projects/optimal-sat/defect4/N_k5.npy')
n = N.shape[0]; k = N.sum(axis=0)[0]
C = N @ N.T                      # C[p,q] = common lines (diag = k)
L = N.T @ N                      # L[l,m] = common points (diag = k)
R = C - np.eye(n, dtype=int)*0   # off-diagonal repeats: c-1
ok = True
# exact-2 identity per point and per line
for p in range(n):
    s = sum(C[p, q] - 1 for q in range(n) if q != p)
    ok &= (s == 2)
    s2 = sum(L[p, q] - 1 for q in range(n) if q != p)
    ok &= (s2 == 2)
print('exact-2 identity holds:', ok)
# rule A*: |l ∩ l'| >= 2  =>  every point a on l has b on l', b != a, with c(a,b) >= 2
rA = True; cnt = 0
for l in range(n):
    for l2 in range(n):
        if l == l2 or L[l, l2] < 2: continue
        cnt += 1
        for a in np.nonzero(N[:, l])[0]:
            if not any(N[b, l2] and b != a and C[a, b] >= 2 for b in range(n)): rA = False
print('rule A* holds:', rA, 'pairs with m>=2:', cnt)
# dual rule: c(p,q) >= 2 => every line L through p has L' through q, L' != L, |L ∩ L'| >= 2
rD = True; cnt = 0
for p in range(n):
    for q in range(n):
        if p == q or C[p, q] < 2: continue
        cnt += 1
        for l in np.nonzero(N[p, :])[0]:
            if not any(N[q, l2] and l2 != l and L[l, l2] >= 2 for l2 in range(n)): rD = False
print('dual rule holds:', rD, 'pairs with c>=2:', cnt)
# identity check: sum_{b in l'} c(a,b) = sum_{L∋a} |L∩l'|
idok = all(sum(C[a, b] for b in range(n) if N[b, l2]) == sum(L[l, l2] for l in range(n) if N[a, l]) for a in range(n) for l2 in range(n))
print('double-count identity holds:', idok)
