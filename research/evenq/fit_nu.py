"""Fit nu (affine solution, on S-lines) as R(X)/N(X2, X5) with R a quadratic form on Pi and N an anisotropic binary
quadratic form; fit h(z) as a rational function.  q even.

python3 fit_nu.py q
"""
import itertools
import sys

import numpy as np

import affine as A

q = int(sys.argv[1])
A.setup(q, 'lines')
F, Fr = A.F, A.Fr
ADD, MUL, INV = F.ADD, F.MUL, F.INV
import os
basis = np.load(f'runs/affine_basis_q{q}_lines' + os.environ.get('EVENQ_DELTA', '') + '.npy')
nk = A.nk
# reduce basis: find the 2 directions with nonconstant nu
nus = [b[:nk] for b in basis]
nontriv = [i for i, nu in enumerate(nus) if len(set(nu.tolist())) > 1]
print('nontrivial nu basis vectors', nontriv)
Pidx = [int(x) for x in np.nonzero(Fr.inPi)[0] if x not in A.onv]
X = A.P[Pidx]
VARS = [0, 1, 2, 4, 5, 6]
MON = list(itertools.combinations_with_replacement(VARS, 2))


def nullspace(M):
    M = M.copy()
    piv, r = [], 0
    for c in range(M.shape[1]):
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0:
            continue
        i = r + nz[0]
        M[[r, i]] = M[[i, r]]
        M[r] = MUL[M[r], INV[M[r, c]]]
        f = M[:, c].copy(); f[r] = 0
        rr = np.nonzero(f)[0]
        if len(rr):
            M[rr] = ADD[M[rr], MUL[f[rr][:, None], M[r][None, :]]]
        piv.append(c); r += 1
        if r == M.shape[0]:
            break
    out = []
    for fc in [c for c in range(M.shape[1]) if c not in piv]:
        y = np.zeros(M.shape[1], np.int64); y[fc] = 1
        for i, pc in enumerate(piv):
            y[pc] = M[i, fc]
        out.append(y)
    return out


monvals = np.stack([MUL[X[:, i], X[:, j]] for i, j in MON], axis=1)
sidx = np.array([A.kidx[int(Fr.Sline_of[x])] for x in Pidx])
# anisotropic N = a X2^2 + X2 X5 + c X5^2 (char 2, b = 1 wlog up to scaling)  or X2^2 + ... try all (a,b,c)
found = 0
for a in range(q):
    for b in range(q):
        for c in range(q):
            if (a, b, c) == (0, 0, 0):
                continue
            # anisotropic on GF(q)^2
            Nv = ADD[ADD[MUL[a, MUL[X[:, 2], X[:, 2]]], MUL[b, MUL[X[:, 2], X[:, 5]]]], MUL[c, MUL[X[:, 5], X[:, 5]]]]
            if np.any(Nv == 0):
                continue
            cols = [monvals] + [MUL[Nv, nus[i][sidx]][:, None] for i in nontriv] + [Nv[:, None]]
            M = np.concatenate(cols, axis=1)
            ns = nullspace(M)
            good = [y for y in ns if np.any(y[len(MON):len(MON) + len(nontriv)]) and np.any(y[:len(MON)])]
            if good:
                found += 1
                if found <= 6:
                    for y in good:
                        R = {f'X{i}X{j}': int(y[k]) for k, (i, j) in enumerate(MON) if y[k]}
                        print('N =', (a, b, c), 'nu coeffs', y[len(MON):].tolist(), 'R =', R)
print('N forms with a fit:', found)
