"""Test candidate nu = Tr_{K/F}(lam * xi / eta), K = F[w], w^2 = w + d, for several coordinate embeddings:
is nu constant on S-lines, and is there h with nu(X_p(z)) + h(z) affine on every A_p (consistency of the h-system)?
EVENQ_DELTA=d python3 test_nu.py q"""
import itertools, sys
import numpy as np
import affine as A
q = int(sys.argv[1])
A.setup(q, 'lines')
F, Fr, P = A.F, A.Fr, A.P
ADD, MUL, INV = F.ADD, F.MUL, F.INV
d = Fr.delta
def kmul(x, y):
    a, b = x; c, e = y
    return (ADD[MUL[a, c], MUL[d, MUL[b, e]]], ADD[ADD[MUL[a, e], MUL[b, c]], MUL[b, e]])
def kconj(x):
    a, b = x; return (ADD[a, b], b)
def knorm(x):
    a, b = x; return ADD[ADD[MUL[a, a], MUL[a, b]], MUL[d, MUL[b, b]]]
def kdiv(x, y):
    n = knorm(y); c = kconj(y); t = kmul(x, c); return (MUL[t[0], INV[n]], MUL[t[1], INV[n]])
EMB = {  # name -> function X -> (a, b) meaning a + b w
    'X0+X4w': lambda X: (X[0], X[4]), 'X4+X0w': lambda X: (X[4], X[0]), 'X3+X4w': lambda X: (X[3], X[4]),
    'X4+X3w': lambda X: (X[4], X[3]), 'X0+dX4w': lambda X: (X[0], MUL[d, X[4]]), 'X3+dX4w': lambda X: (X[3], MUL[d, X[4]]),
}
ETA = {'X5+X2w': lambda X: (X[5], X[2]), 'X2+X5w': lambda X: (X[2], X[5]), 'X5+dX2w': lambda X: (X[5], MUL[d, X[2]]),
       'dX2+X5w': lambda X: (MUL[d, X[2]], X[5])}
inv_k = {i: s for s, i in A.kidx.items()}
def h_consistent(nu):
    nz = A.nz; rows, rhs = [], []
    for p in Fr.free[:: max(1, len(Fr.free) // 3000)]:
        pr, _ = A.params[int(p)]
        for t in range(2, q):
            r = np.zeros(nz, np.int64); b = 0
            for coef, tt in ((1, t), (int(ADD[1, t]), 0), (t, 1)):
                k, z = pr[tt]; r[z] = ADD[r[z], coef]; b ^= int(MUL[coef, nu[k]])
            rows.append(r); rhs.append(b)
    M = np.concatenate([np.array(rows), np.array(rhs)[:, None]], axis=1)
    piv, r = [], 0
    for c in range(nz):
        nzr = np.nonzero(M[r:, c])[0]
        if len(nzr) == 0: continue
        i = r + nzr[0]; M[[r, i]] = M[[i, r]]; M[r] = MUL[M[r], INV[M[r, c]]]
        f = M[:, c].copy(); f[r] = 0; rr = np.nonzero(f)[0]
        if len(rr): M[rr] = ADD[M[rr], MUL[f[rr][:, None], M[r][None, :]]]
        piv.append(c); r += 1
    return not np.any(M[r:, nz])
for (en, ef), (hn, hf) in itertools.product(EMB.items(), ETA.items()):
    for lam in [(1, 0), (0, 1)]:
        nu = np.zeros(A.nk, np.int64); const = True
        for s, i in A.kidx.items():
            vals = set()
            for x in A.lines[s]:
                X = P[x]
                vals.add(int(kmul(lam, kdiv(ef(X), hf(X)))[1]))
            const &= len(vals) == 1
            nu[i] = min(vals)
        if const:
            print(f'xi={en:8s} eta={hn:8s} lam={lam}: constant on S-lines; affine-h consistent: {h_consistent(nu)}', flush=True)
