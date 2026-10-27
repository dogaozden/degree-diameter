import sys, numpy as np, time
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo, orbits, inv_mod
q = 11
G = Geo(q)
Y = np.zeros((7, 7), dtype=np.int64)
for i in range(7): Y[i, (i + 1) % 7] = 1
Z = np.array([[-3,2,-1,-1,-3,-1,-3],[-2,1,1,3,1,3,3],[-1,-1,-3,-1,-3,-3,2],[-1,-3,-1,-3,-3,2,-1],
              [-3,-1,-3,-3,2,-1,-1],[1,3,3,-2,1,1,3],[3,3,-2,1,1,3,1]]) % q

def order(M):
    P = np.eye(7, dtype=np.int64)
    for k in range(1, 10000):
        P = (P @ M) % q
        if (P == np.eye(7, dtype=np.int64)).all(): return k
    return None
def sym_invariant(gens):
    # unknowns: X symmetric, 28 entries (i<=j). Equations g^T X g - X = 0 mod q.
    idx = {}
    k = 0
    for i in range(7):
        for j in range(i, 7):
            idx[(i, j)] = k; k += 1
    rows = []
    for g in gens:
        # for each (a,b) entry of equation: sum_{i,j} g[i,a] X[i,j] g[j,b] - X[a,b] = 0
        for a in range(7):
            for b in range(a, 7):
                row = np.zeros(28, dtype=np.int64)
                for i in range(7):
                    for j in range(7):
                        c = g[i, a] * g[j, b] % q
                        if c == 0: continue
                        key = (min(i, j), max(i, j))
                        row[idx[key]] = (row[idx[key]] + c) % q
                row[idx[(a, b)]] = (row[idx[(a, b)]] - 1) % q
                rows.append(row)
    M = np.array(rows, dtype=np.int64) % q
    # nullspace
    from q6lib import nullspace_mod
    ns = nullspace_mod(M, q)
    out = []
    for v in ns:
        X = np.zeros((7, 7), dtype=np.int64)
        for (i, j), kk in idx.items():
            X[i, j] = v[kk]; X[j, i] = v[kk]
        out.append(X)
    return out
if __name__ == '__main__':
    print('orders Y', order(Y), 'Z', order(Z))
    print('ZY order', order(Z @ Y % q))
    ns = sym_invariant([Y, Z])
    print('invariant sym forms dim', len(ns))
    for X in ns:
        print(X)
        print('det', round(np.linalg.det(X.astype(float))) % q if False else 'skip')
