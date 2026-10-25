import sys, numpy as np, itertools
sys.path.insert(0, '../tools'); import hexlib
from f9 import *
q, lines, coord = hexlib.load('../hex/hex_q9.bin'); P = coord.astype(np.int64); N = len(P)
pairs = list(itertools.combinations(range(7), 2))
def plucker(x, y):
    return np.array([sub(M[x[i], y[j]], M[x[j], y[i]]) for i, j in pairs], np.int64)
rng = np.random.default_rng(0)
sample = rng.choice(N, 300, replace=False)
PL = np.array([plucker(P[lines[l][0]], P[lines[l][1]]) for l in sample])
R, piv = rref(PL)
print('rank of line Plucker vectors (300 lines):', len(R))
Wb = R  # basis of W (rows, length 21)
# form <u^v, x^y> = B(u,x)B(v,y) - B(u,y)B(v,x) on Lambda^2 V, in the pair basis e_i^e_j
G21 = np.zeros((21, 21), np.int64)
E = np.eye(7, dtype=np.int64)
for a, (i, j) in enumerate(pairs):
    for b, (k, l) in enumerate(pairs):
        G21[a, b] = sub(M[Bf(E[i], E[k]), Bf(E[j], E[l])], M[Bf(E[i], E[l]), Bf(E[j], E[k])])
# Gram on W
def bil(u, v):
    s = 0
    for a in range(21):
        if u[a] == 0: continue
        for b in range(21):
            if v[b]: s = A[s, M[M[u[a], G21[a, b]], v[b]]]
    return s
k = len(Wb)
GW = np.array([[bil(Wb[i], Wb[j]) for j in range(k)] for i in range(k)], np.int64)
rad = nullspace(GW)
print('dim W =', k, ' dim radical of the form on W =', len(rad))
np.save('Wbasis.npy', Wb); np.save('Wrad.npy', rad); np.save('G21.npy', G21)
