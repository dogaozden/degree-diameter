"""Compute J_z (J^2 + J + d = 0, Jx on the S_z-line of x) for every z and fit entries as polynomials in (a, b).
EVENQ_DELTA=d python3 fitJ.py q"""
import itertools, sys
import numpy as np
from frame import Frame
q = int(sys.argv[1])
Fr = Frame(q); H = Fr.H; F = H.F; ADD, MUL, INV = F.ADD, F.MUL, F.INV; d = Fr.delta
C = [0, 1, 2, 4, 5, 6]
def nullspace(M):
    M = M.copy(); piv, r = [], 0
    for c in range(M.shape[1]):
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]; M[[r, i]] = M[[i, r]]; M[r] = MUL[M[r], INV[M[r, c]]]
        f = M[:, c].copy(); f[r] = 0; rr = np.nonzero(f)[0]
        if len(rr): M[rr] = ADD[M[rr], MUL[f[rr][:, None], M[r][None, :]]]
        piv.append(c); r += 1
        if r == M.shape[0]: break
    out = []
    for fc in [c for c in range(M.shape[1]) if c not in piv]:
        y = np.zeros(M.shape[1], np.int64); y[fc] = 1
        for i, pc in enumerate(piv): y[pc] = M[i, fc]
        out.append(y)
    return out
def mm(A, B):
    out = np.zeros((6, 6), np.int64)
    for i in range(6):
        for j in range(6):
            acc = 0
            for k in range(6): acc ^= int(MUL[A[i, k], B[k, j]])
            out[i, j] = acc
    return out
I6 = np.eye(6, dtype=np.int64)
Js = {}
for a, b in itertools.product(range(q), repeat=2):
    rows = []
    for s in Fr.Sz(a, b)[:40]:
        pts = H.P[H.lines[s]][:, C]
        fs = nullspace(pts[:2].copy())
        for x in pts[:3]:
            for f in fs:
                rows.append(MUL[f[:, None], x[None, :]].ravel())
    sol = nullspace(np.array(rows)); assert len(sol) == 2
    good = []
    for u, w in itertools.product(range(q), repeat=2):
        J = ADD[MUL[u, sol[0].reshape(6, 6)], MUL[w, sol[1].reshape(6, 6)]]
        if np.all(ADD[ADD[mm(J, J), J], MUL[d, I6]] == 0):
            good.append(J)
    assert len(good) == 2
    # choose the root whose (x5' , x2) entry ... normalise: entry [1,1] (x1' coefficient of x1) as in J_0 = 1 ... pick J with J[4,1]==0? just pick the one with J[5,1] == d (x6' = d x1 at z=0)
    J = min(good, key=lambda J: (J[1, 1] != 1, J.tolist()))
    Js[(a, b)] = J
names = ['x0', 'x1', 'x2', 'x4', 'x5', 'x6']
mons = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]
mn = ['1', 'a', 'b', 'a^2', 'ab', 'b^2']
zs = list(Js)
def mono(z, e):
    return int(MUL[F.exp[(F.log[z[0]] * e[0]) % (q - 1)] if z[0] else int(e[0] == 0), F.exp[(F.log[z[1]] * e[1]) % (q - 1)] if z[1] else int(e[1] == 0)])
Mm = np.array([[mono(z, e) for e in mons] for z in zs])
for i in range(6):
    terms = []
    for j in range(6):
        vals = np.array([Js[z][i, j] for z in zs])
        ns = nullspace(np.concatenate([Mm, vals[:, None]], axis=1))
        ns = [y for y in ns if y[-1]]
        assert ns, (i, j)
        y = MUL[ns[0], INV[ns[0][-1]]]
        coef = [int(c) for c in y[:-1]]
        if any(coef):
            terms.append('(' + ' + '.join(f'{c}*{m}' for c, m in zip(coef, mn) if c) + f')*{names[j]}')
    print(f"{names[i]}' =", ' + '.join(terms))
