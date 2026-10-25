# The hyperplanes holding q^2 points of a flag set: normals n (B(n, x) = 0), Q(n), and how the set meets them.
import sys, itertools
import numpy as np
fl, q, C, target = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rows = np.loadtxt(f'/home/user/degree-diameter/research/cell147/data/E{q}.map', dtype=np.int64)
pos = {int(r[0]): i for i, r in enumerate(rows)}
S = [pos[int(l.split()[0])] for l in open(fl)]
X = rows[S][:, 2:9] % q
# V coords u = (x0,x1,x2,x3,x5,x6); B(u,w) = u^T M w with x4 = -C x0
M = np.zeros((6, 6), dtype=np.int64)
M[0, 0] = (-2 * C) % q; M[1, 4] = M[4, 1] = 1; M[2, 5] = M[5, 2] = 1; M[3, 3] = (-2) % q
U = X[:, [0, 1, 2, 3, 5, 6]]
allv = np.array(list(itertools.product(range(q), repeat=6)), dtype=np.int64)
nz = allv[np.any(allv != 0, axis=1)]
first = np.argmax(nz != 0, axis=1)
nrm = nz[nz[np.arange(len(nz)), first] == 1]
cnt = ((nrm @ U.T) % q == 0).sum(axis=1)
H = nrm[cnt == target]
print(len(H), "hyperplanes with", target, "points")
# hyperplane {u : f.u = 0}; its pole n w.r.t. B: M n = f  ->  n = M^-1 f
Minv = np.round(np.linalg.inv(M) * np.linalg.det(M)).astype(np.int64) % q
d = int(round(np.linalg.det(M))) % q; dinv = pow(d, q - 2, q)
Mi = (Minv * dinv) % q
assert np.array_equal((M @ Mi) % q, np.eye(6, dtype=np.int64))
poles = (H @ Mi.T) % q
for f, n in zip(H, poles):
    Qn = int((n @ M @ n) % q) * pow(2, q - 2, q) % q
    inside = np.where((U @ f) % q == 0)[0]
    print("normal", f.tolist(), "pole", n.tolist(), "Q(pole) =", Qn, "| set points inside:", len(inside))
# incidence: how many of these hyperplanes contain each set point
inc = ((U @ H.T) % q == 0).sum(axis=1)
print("hyperplanes per set point:", np.bincount(inc).tolist())
# Gram matrix of the centers (poles) and the 4-subset pattern of each set point
G = (poles @ M @ poles.T) % q
print("center Gram (0 = collinear):"); print(G)
from collections import Counter
pat = Counter(tuple(np.where((U[i] @ H.T) % q == 0)[0].tolist()) for i in range(len(U)))
print(len(pat), "patterns; sizes", sorted(Counter(pat.values()).items()))
for k_, v_ in sorted(pat.items()): print(k_, v_)
def rank(A):
    A = A.copy() % q; r = 0
    for c in range(A.shape[1]):
        piv = next((i for i in range(r, A.shape[0]) if A[i, c]), None)
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]; A[r] = (A[r] * pow(int(A[r, c]), q - 2, q)) % q
        for i in range(A.shape[0]):
            if i != r and A[i, c]: A[i] = (A[i] - A[i, c] * A[r]) % q
        r += 1
    return r
print("rank of the centers:", rank(poles))
for k_ in range(3, 9):
    print(k_, "first centers rank", rank(poles[:k_]))
