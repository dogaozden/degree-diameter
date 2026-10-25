"""c6 step 1: stabiliser of R756 inside the normaliser of <h>, h = research/cell147/ovoid/g15.txt.

Eigen-structure of h over F_11: eigenvalues 1, 3, 9, 5, 4 (the 5th roots of unity, each on a 1-dim rational line)
and the 2-dim anisotropic plane A = ker(h^2+h+1).  In the eigenbasis P = [v1, v3, v9, v5, v4, a1, a2]:
  H = diag(1,3,9,5,4) + C2 on A.  Centraliser C(h) = diagonal scalings on the lines + F_11[C2]^* on A (similitudes).
  Normaliser elements g with g h g^-1 = h^k permute the rational lines by lambda -> lambda^m (m = k^-1 mod 15).
Output: all projective similitudes g with g R756 = R756 that normalise <h>, saved to stab_R756.json
(standard coordinates, the lists 'elements').
"""
import os, sys, json, itertools, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

HERE = os.path.dirname(os.path.abspath(__file__))
LAM = [1, 3, 9, 5, 4]          # eigenvalues of h on the rational lines (LAM[i] pairs with its inverse)


def mm(A, B):
    return (A @ B) % Q


def matpow(A, e):
    R = np.eye(A.shape[0], dtype=np.int64)
    for _ in range(e):
        R = mm(R, A)
    return R


def inv_mod(A):
    n = A.shape[0]
    M = np.concatenate([A % Q, np.eye(n, dtype=np.int64)], axis=1)
    for c in range(n):
        p = c + np.nonzero(M[c:, c])[0][0]
        M[[c, p]] = M[[p, c]]
        M[c] = M[c] * INV[M[c, c]] % Q
        for i in range(n):
            if i != c and M[i, c]:
                M[i] = (M[i] - M[i, c] * M[c]) % Q
    return M[:, n:]


def nullspace(A):
    A = np.array(A, dtype=np.int64) % Q
    m, n = A.shape
    M = A.copy(); piv = []; r = 0
    for c in range(n):
        if r == m: break
        rows = np.nonzero(M[r:, c])[0]
        if len(rows) == 0: continue
        p = r + rows[0]
        M[[r, p]] = M[[p, r]]
        M[r] = M[r] * INV[M[r, c]] % Q
        for i in range(m):
            if i != r and M[i, c]:
                M[i] = (M[i] - M[i, c] * M[r]) % Q
        piv.append(c); r += 1
    out = []
    for f in [c for c in range(n) if c not in piv]:
        v = np.zeros(n, dtype=np.int64); v[f] = 1
        for i, c in enumerate(piv):
            v[c] = (-M[i, f]) % Q
        out.append(v)
    return out


def proj_key(M):
    """projective class of a matrix: scale so that the first nonzero entry is 1."""
    flat = M.reshape(-1) % Q
    lead = flat[np.argmax(flat != 0)]
    return tuple(int(x) for x in (flat * INV[lead]) % Q)


def code_of_rows(X):
    return X @ (Q ** np.arange(7, dtype=np.int64))


def setup():
    h = np.array(L.read_gens(G15_PATH)[0], dtype=np.int64)
    G = np.array(L.std_gram(Q), dtype=np.int64)
    assert np.all(mm(mm(h.T, G), h) == G), 'h is not an isometry'
    I7 = np.eye(7, dtype=np.int64)
    ev = {}
    for lam in range(Q):
        ns = nullspace((h - lam * I7) % Q)
        if ns: ev[lam] = ns
    A = nullspace((mm(h, h) + h + I7) % Q)
    assert sorted(ev) == sorted(LAM) and all(len(v) == 1 for v in ev.values()), sorted(ev)
    assert len(A) == 2
    P = np.stack([ev[l][0] for l in LAM] + [A[0], A[1]], axis=1) % Q
    Pinv = inv_mod(P)
    H = mm(mm(Pinv, h), P)
    Ge = mm(mm(P.T, G), P)
    assert np.all(H[:5, 5:] == 0) and np.all(H[5:, :5] == 0)
    assert np.all(H[:5, :5] == np.diag(LAM))
    return dict(h=h, G=G, P=P, Pinv=Pinv, H=H, Ge=Ge)


def centraliser_sims(S):
    """all similitudes of C(h) in standard coordinates: list of (matrix, multiplier)."""
    H, Ge, P, Pinv = S['H'], S['Ge'], S['P'], S['Pinv']
    C2 = H[5:, 5:]
    assert np.all((mm(C2, C2) + C2 + np.eye(2, dtype=np.int64)) % Q == 0)
    GA = Ge[5:, 5:]
    Ys = []   # Y = a I + b C2 (commutes with C2) with Y^T GA Y = mu GA
    for a, b in itertools.product(range(Q), repeat=2):
        Y = (a * np.eye(2, dtype=np.int64) + b * C2) % Q
        if (Y[0, 0] * Y[1, 1] - Y[0, 1] * Y[1, 0]) % Q == 0: continue
        T = mm(mm(Y.T, GA), Y)
        for mu in range(1, Q):
            if np.all((T - mu * GA) % Q == 0):
                Ys.append((Y, mu))
    Gr = Ge[:5, :5]
    nz = [(i, j) for i in range(5) for j in range(5) if Gr[i, j] % Q]
    grid = np.array(list(itertools.product(range(1, Q), repeat=5)), dtype=np.int64)
    i0, j0 = nz[0]
    mu_arr = grid[:, i0] * grid[:, j0] % Q
    ok = np.ones(len(grid), dtype=bool)
    for (i, j) in nz:
        ok &= (grid[:, i] * grid[:, j] % Q == mu_arr)
    sims = []
    for t in np.nonzero(ok)[0]:
        d, mu = grid[t], int(mu_arr[t])
        for Y, muY in Ys:
            if muY != mu: continue
            X = np.zeros((7, 7), dtype=np.int64)
            X[:5, :5] = np.diag(d)
            X[5:, 5:] = Y
            sims.append((mm(mm(P, X), Pinv), mu))
    return sims


def weyl_elements(S):
    """for each m in (Z/15)^*, one similitude g (standard coordinates) with g h g^-1 = h^k, k = m^-1 mod 15."""
    H, Ge, P, Pinv = S['H'], S['Ge'], S['P'], S['Pinv']
    C2 = H[5:, 5:]
    GA = Ge[5:, 5:]
    Gr = Ge[:5, :5]
    grid = np.array(list(itertools.product(range(1, Q), repeat=5)), dtype=np.int64)
    out = {}
    for m in [x for x in range(1, 15) if np.gcd(x, 15) == 1]:
        k = pow(m, -1, 15)
        Hk = matpow(H, k)
        sigma = [pow(l, m, Q) for l in LAM]           # eigenvalue l goes to l^m
        idx = [LAM.index(s) for s in sigma]
        Ys = [np.array([[a, b], [c, d]], dtype=np.int64)
              for a, b, c, d in itertools.product(range(Q), repeat=4)
              if np.all(mm(np.array([[a, b], [c, d]]), C2) % Q == mm(matpow(C2, k), np.array([[a, b], [c, d]])) % Q)]
        Gs = Gr[np.ix_(idx, idx)]
        found = None
        for Y in Ys:
            if (Y[0, 0] * Y[1, 1] - Y[0, 1] * Y[1, 0]) % Q == 0: continue
            T = mm(mm(Y.T, GA), Y)
            for mu in range(1, Q):
                if not np.all((T - mu * GA) % Q == 0): continue
                ok = np.ones(len(grid), dtype=bool)
                for l in range(5):
                    for n_ in range(5):
                        lhs = grid[:, l] * grid[:, n_] % Q * Gs[l, n_] % Q
                        ok &= (lhs == mu * Gr[l, n_] % Q)
                if ok.any():
                    found = (grid[np.nonzero(ok)[0][0]], Y, mu)
                    break
            if found: break
        assert found is not None, ('no similitude for m', m)
        c, Y, mu = found
        g = np.zeros((7, 7), dtype=np.int64)
        for l in range(5):
            g[idx[l], l] = c[l]      # e_l -> c_l e_{sigma(l)}
        g[5:, 5:] = Y
        assert np.all(mm(g, H) == mm(Hk, g)), ('intertwiner check failed', m)
        out[m] = (mm(mm(P, g), Pinv), mu, k)
    return out


def mm_rows(X, M):
    return (X @ M.T) % Q


def main():
    t0 = time.time()
    S = setup()
    G, h = S['G'], S['h']
    R = load_points(R756_PATH)
    tbl = np.zeros(Q ** 7, dtype=bool); tbl[code_of_rows(R)] = True

    def stab(M):
        img = normalize_rows(mm_rows(R, M))
        return bool(tbl[code_of_rows(img)].all())

    sims = centraliser_sims(S)
    print('C(h) similitudes (matrices):', len(sims), flush=True)
    for M, mu in sims[:20]:
        assert np.all(mm(M, h) == mm(h, M))
        assert np.all(mm(mm(M.T, G), M) == mu * G % Q)
    seen = {}
    for M, mu in sims:
        seen.setdefault(proj_key(M), M)
    print('C(h) projective elements:', len(seen), flush=True)
    wes = weyl_elements(S)
    for m, (g, mu, k) in sorted(wes.items()):
        assert np.all(mm(mm(g.T, G), g) == mu * G % Q)
        assert np.all(mm(g, np.linalg.matrix_power(h, 1)) % Q == mm(g, h))
    print('weyl representatives for m:', sorted(wes), flush=True)
    stabN = {}
    stabC = 0
    for key, M in seen.items():
        if stab(M):
            stabC += 1
            stabN.setdefault(key, M)
    print('stabiliser of R756 inside C(h) (projective):', stabC, flush=True)
    for m, (g, mu, k) in sorted(wes.items()):
        cnt = 0
        for key, M in seen.items():
            X = mm(g, M)
            if stab(X):
                cnt += 1
                stabN.setdefault(proj_key(X), X)
        print(f'  m={m} k={k}: stabilising elements in this coset = {cnt}', flush=True)
    print('stabiliser of R756 inside the normaliser of <h> (projective, incl. C(h) part):', len(stabN),
          'time %.1fs' % (time.time() - t0), flush=True)
    out = {'h': h.tolist(), 'elements': [M.tolist() for M in stabN.values()]}
    with open(os.path.join(HERE, 'stab_R756.json'), 'w') as f:
        json.dump(out, f)
    print('saved to', os.path.join(HERE, 'stab_R756.json'), flush=True)


if __name__ == '__main__':
    main()
