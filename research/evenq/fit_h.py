"""With nu(X) = (X2X3 + X2X4 + X4X5)/(d X2^2 + X2X5 + X5^2) (q even, Pi: X3 = X0 + d X4), check nu is constant
on S-lines, solve for h with nu(X_p(z)) + h(z) affine on every A_p, then fit h = C(a,b)/N'(a,b) + affine.

python3 fit_h.py q [delta]
"""
import itertools
import sys

import numpy as np

import affine as A
import frame

q = int(sys.argv[1])
if len(sys.argv) > 2:
    _orig = frame.Frame.__init__
    frame.Frame.__init__ = lambda self, q, delta=None, log=print: _orig(self, q, int(sys.argv[2]), log)
A.setup(q, 'lines')
F, Fr = A.F, A.Fr
ADD, MUL, INV = F.ADD, F.MUL, F.INV
d = Fr.delta
d2 = int(MUL[d, d])
print('q', q, 'delta', d)
P = A.P


def nu_pt(X):
    num = ADD[ADD[MUL[X[2], X[3]], MUL[X[2], X[4]]], MUL[X[4], X[5]]]
    den = ADD[ADD[MUL[d, MUL[X[2], X[2]]], MUL[X[2], X[5]]], MUL[X[5], X[5]]]
    assert den != 0
    return int(MUL[num, INV[den]])


nu = np.zeros(A.nk, np.int64)
const_ok = True
for s, i in A.kidx.items():
    vals = {nu_pt(P[x]) for x in A.lines[s]}
    const_ok &= len(vals) == 1
    nu[i] = vals.pop()
print('nu constant on every S-line:', const_ok, '; value counts', np.unique(nu, return_counts=True)[1].tolist())
# solve for h
nz = A.nz
rows, rhs = [], []
for p in Fr.free:
    pr, _ = A.params[int(p)]
    for t in range(2, q):
        r = np.zeros(nz, np.int64)
        b = 0
        for coef, tt in ((1, t), (int(ADD[1, t]), 0), (t, 1)):
            k, z = pr[tt]
            r[z] = ADD[r[z], coef]
            b ^= int(MUL[coef, nu[k]])
        rows.append(r); rhs.append(b)
M = np.concatenate([np.array(rows), np.array(rhs)[:, None]], axis=1)
# rref
piv, r = [], 0
for c in range(nz):
    nzr = np.nonzero(M[r:, c])[0]
    if len(nzr) == 0:
        continue
    i = r + nzr[0]
    M[[r, i]] = M[[i, r]]
    M[r] = MUL[M[r], INV[M[r, c]]]
    f = M[:, c].copy(); f[r] = 0
    rr = np.nonzero(f)[0]
    if len(rr):
        M[rr] = ADD[M[rr], MUL[f[rr][:, None], M[r][None, :]]]
    piv.append(c); r += 1
consistent = not np.any(M[r:, nz])
print('h system rank', len(piv), 'of', nz, 'consistent', consistent)
h = np.zeros(nz, np.int64)
for i, pc in enumerate(piv):
    h[pc] = M[i, nz]
# fit h(z) N'(z) = C(z) + (k + c0 a + c1 b) N'(z), N'(a,b) = b^2 + d2 a b + d2 a^2  (and try other N')
zs = A.zs
Za = np.array([z[0] for z in zs]); Zb = np.array([z[1] for z in zs])
cub = [(3, 0), (2, 1), (1, 2), (0, 3)]


def pw(x, k):
    out = np.ones_like(x)
    for _ in range(k):
        out = MUL[out, x]
    return out


for (u, w, x) in itertools.product(range(q), repeat=3):
    Nn = ADD[ADD[MUL[u, pw(Za, 2)], MUL[w, MUL[Za, Zb]]], MUL[x, pw(Zb, 2)]]
    if np.any(Nn == 0):
        continue
    cols = [MUL[pw(Za, i), pw(Zb, j)][:, None] for i, j in cub]
    cols += [Nn[:, None], MUL[Nn, Za][:, None], MUL[Nn, Zb][:, None], MUL[Nn, h][:, None]]
    Mx = np.concatenate(cols, axis=1)
    # nullspace with last coefficient nonzero
    piv, r = [], 0
    Mx = Mx.copy()
    for c in range(Mx.shape[1]):
        nzr = np.nonzero(Mx[r:, c])[0]
        if len(nzr) == 0:
            continue
        i = r + nzr[0]
        Mx[[r, i]] = Mx[[i, r]]
        Mx[r] = MUL[Mx[r], INV[Mx[r, c]]]
        f = Mx[:, c].copy(); f[r] = 0
        rr = np.nonzero(f)[0]
        if len(rr):
            Mx[rr] = ADD[Mx[rr], MUL[f[rr][:, None], Mx[r][None, :]]]
        piv.append(c); r += 1
        if r == Mx.shape[0]:
            break
    if (Mx.shape[1] - 1) not in piv:
        y = np.zeros(Mx.shape[1], np.int64); y[-1] = 1
        for i, pc in enumerate(piv):
            y[pc] = Mx[i, -1]
        print("N'(a,b) =", (u, w, x), 'cubic a^3,a^2b,ab^2,b^3:', y[:4].tolist(), 'affine k,c0,c1:', y[4:7].tolist())
