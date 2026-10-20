"""Find nu (on S-lines, or on Pi-points) and h (on z != 0) such that, for every free point p, the function
z -> nu(X_p(z)) + h(z) is GF(q)-affine on the affine line A_p.  Linear algebra over GF(q), q even.

python3 affine.py q [lines|points] [NROWS]
"""
import sys
import time

import numpy as np

from frame import Frame

t0 = time.time()

def setup(q, where='lines'):
    global Fr, H, N, lines, F, ADD, MUL, INV, zs, zidx, zof, keys, kidx, nk, nz, ncol, P, params, key_of_X, onv, Pidx, rows_for
    Fr = Frame(q)
    H, N, lines, F = Fr.H, Fr.N, Fr.H.lines, Fr.H.F
    ADD, MUL, INV = F.ADD, F.MUL, F.INV
    zs = [(a, b) for a in range(q) for b in range(q) if (a, b) != (0, 0)]
    zidx = {z: i for i, z in enumerate(zs)}
    # for every candidate line m: z(m), X(m)
    zof = {}
    for (a, b) in zs:
        for m in Fr.Sz(a, b):
            if m != Fr.v:
                zof[int(m)] = (a, b)
    Pidx = np.nonzero(Fr.inPi)[0]
    onv = set(lines[Fr.v].tolist())
    if where == 'lines':
        keys = [int(s) for s in Fr.S if s != Fr.v]
        key_of_X = lambda X: int(Fr.Sline_of[X])
    else:
        keys = [int(x) for x in Pidx if x not in onv]
        key_of_X = lambda X: int(X)
    kidx = {k: i for i, k in enumerate(keys)}
    nk, nz = len(keys), len(zs)
    ncol = nk + nz
    P = H.P


    def param(p):
        """for free p: list over t in GF(q) of (key, z) along A_p, z(t) = z0 + t (p5, p2), normalised L0(p) = 1"""
        L = int(Fr.L0[p])
        p2, p5 = int(MUL[INV[L], P[p, 2]]), int(MUL[INV[L], P[p, 5]])
        # z0: a p2 + b p5 = 1
        z0 = (int(INV[p2]), 0) if p2 else (0, int(INV[p5]))
        out = []
        lp = {zof[int(m)]: int(m) for m in H.through[p] if int(m) in zof}
        for t in range(q):
            z = (int(ADD[z0[0], MUL[t, p5]]), int(ADD[z0[1], MUL[t, p2]]))
            m = lp[z]
            X = [y for y in lines[m] if Fr.inPi[y]][0]
            out.append((kidx[key_of_X(X)], zidx[z]))
        return out, (p2, p5)


    params = {}
    for p in Fr.free:
        params[int(p)] = param(int(p))
    print(f'[{time.time()-t0:.0f}s] params done; unknowns', ncol, flush=True)


    def rows_for_(p):
        out = []
        pr, _ = params[p]
        for t in range(2, q):
            r = np.zeros(ncol, np.int64)
            for coef, tt in ((1, t), (int(ADD[1, t]), 0), (t, 1)):
                k, z = pr[tt]
                r[k] = ADD[r[k], coef]
                r[nk + z] = ADD[r[nk + z], coef]
            out.append(r)
        return out
    rows_for = rows_for_
    return params


if __name__ == '__main__':
    q, where = int(sys.argv[1]), (sys.argv[2] if len(sys.argv) > 2 else 'lines')
    nrows = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    setup(q, where)
    rng = np.random.default_rng(1)
    free = [int(p) for p in Fr.free]
    sample = rng.choice(len(free), size=min(len(free), nrows), replace=False)
    A = np.array([r for i in sample for r in rows_for(free[i])])
    print(f'[{time.time()-t0:.0f}s] sample rows', len(A), flush=True)


    def rref(A):
        A = A.copy()
        piv = []
        r = 0
        for c in range(A.shape[1]):
            nz = np.nonzero(A[r:, c])[0]
            if len(nz) == 0:
                continue
            i = r + nz[0]
            A[[r, i]] = A[[i, r]]
            A[r] = MUL[A[r], INV[A[r, c]]]
            f = A[:, c].copy()
            f[r] = 0
            rowsnz = np.nonzero(f)[0]
            if len(rowsnz):
                A[rowsnz] = ADD[A[rowsnz], MUL[f[rowsnz][:, None], A[r][None, :]]]
            piv.append(c)
            r += 1
            if r == A.shape[0]:
                break
        return A[:r], piv


    R, piv = rref(A)
    freecols = [c for c in range(ncol) if c not in piv]
    print(f'[{time.time()-t0:.0f}s] rank', len(piv), 'nullity', len(freecols), flush=True)
    basis = []
    for fc in freecols:
        y = np.zeros(ncol, np.int64)
        y[fc] = 1
        for i, pc in enumerate(piv):
            y[pc] = R[i, fc]  # char 2: -x = x
        basis.append(y)
    # verify on all rows
    bad = 0
    for p in free:
        for r in rows_for(p):
            for y in basis:
                acc = 0
                for k in np.nonzero(r)[0]:
                    acc ^= int(MUL[r[k], y[k]])
                if acc:
                    bad += 1
    print('violations on all rows', bad)
    import os; np.save(f'runs/affine_basis_q{q}_{where}' + os.environ.get('EVENQ_DELTA', '') + '.npy', np.array(basis))
    for y in basis:
        nu = y[:nk]
        h = y[nk:]
        print('nu distinct', len(set(nu.tolist())), 'h distinct', len(set(h.tolist())), 'h', h.tolist() if q <= 4 else '')
