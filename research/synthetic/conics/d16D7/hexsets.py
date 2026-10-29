"""H(q) from hexgen's .bin, the torus T = <g>, g = diag(1, b, 1/b) in SL(3,q) acting as (v, a, w) -> (g v, a, g^-T w),
the Hermitian spread point set R_H (hyperplane X0 + c X4 = 0) and the dual segment set R_L = (lines meeting v) + exact
whiskers (POLISHED.md Theorem 6.5) for odd q; T preserves both (it scales z -> b z in Pi_z, nu -> b nu, F(bz) = b F(z))."""
import numpy as np

PARAMS = {11: (1, 1, 3), 13: (2, 1, 1), 5: (2, 1, 0), 7: (1, 1, 0), 3: (1, 1, 2)}   # q: (c, c0, c1), POLISHED.md


def load(fn):
    b = open(fn, 'rb').read()
    q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32))
    Q1 = q + 1
    LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
    X = np.frombuffer(b[12 + 4 * Lc * Q1:], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
    order = np.lexsort((flat_l, flat_p)); PL = flat_l[order].reshape(N, Q1)
    return q, N, LP, PL, X


def torus_perms(q, N, LP, PL, X, bgen):
    """permutations of points and lines induced by diag(1, b, 1/b, 1, 1, 1/b, b)."""
    d = np.array([1, bgen, pow(bgen, q - 2, q), 1, 1, pow(bgen, q - 2, q), bgen], dtype=np.int64)
    code = X @ (q ** np.arange(7, dtype=np.int64))
    assert np.all(np.diff(code) > 0)
    Y = (X * d) % q
    lead = np.argmax(Y != 0, axis=1)
    inv = np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)
    Y = (Y * inv[Y[np.arange(N), lead]][:, None]) % q
    pp = np.searchsorted(code, Y @ (q ** np.arange(7, dtype=np.int64)))
    assert np.array_equal(code[pp], Y @ (q ** np.arange(7, dtype=np.int64))), 'g does not map points to points'
    a0, b0 = pp[LP[:, 0]], pp[LP[:, 1]]
    hit = (PL[a0][:, :, None] == PL[b0][:, None, :]).reshape(len(LP), -1)
    assert np.all(hit.sum(axis=1) == 1), 'g does not map lines to lines'
    pl = PL[a0, hit.argmax(axis=1) // (q + 1)]
    # incidence preserved
    assert np.all(np.sort(pp[LP], axis=1) == np.sort(LP[pl], axis=1))
    return pp, pl


def sets(q, N, LP, PL, X):
    c, c0, c1 = PARAMS[q]
    assert pow(-c % q, (q - 1) // 2, q) == q - 1
    inv = [0] + [pow(a, q - 2, q) for a in range(1, q)]
    inPi = (X[:, 0] + c * X[:, 4]) % q == 0
    S = np.nonzero(inPi[LP].all(1))[0]
    assert len(S) == q ** 3 + 1
    RH = np.zeros(N, bool); RH[LP[S].reshape(-1)] = True
    assert RH.sum() == (q + 1) * (q ** 3 + 1)
    e1 = np.nonzero((X == np.array([0, 1, 0, 0, 0, 0, 0])).all(1))[0][0]
    e6 = np.nonzero((X == np.array([0, 0, 0, 0, 0, 0, 1])).all(1))[0][0]
    (v,) = set(PL[e1].tolist()) & set(PL[e6].tolist())
    W = set()
    for a in range(q):
        for bb in range(q):
            if (a, bb) == (0, 0):
                continue
            inPz = (X[:, 0] + c * X[:, 4] + a * X[:, 2] + bb * X[:, 5]) % q == 0
            Sz = np.nonzero(inPz[LP].all(1))[0]
            assert len(Sz) == q ** 3 + 1 and v in Sz
            G = ((c0 * a + c1 * bb) * (a * a + c * bb * bb) - bb ** 3) % q
            assert G != 0
            F = G * inv[(a * a + c * bb * bb) % q] % q
            for l in Sz:
                if l == v:
                    continue
                (p,) = LP[l][inPi[LP[l]]]
                x = X[p]
                den = (c * x[2] * x[2] + x[5] * x[5]) % q
                if (x[2] * x[3] - x[4] * x[5]) * inv[den] % q == F:
                    W.add(int(l))
    W = np.array(sorted(W), dtype=np.int64)
    near = (X[:, 2] % q == 0) & (X[:, 5] % q == 0)
    free = ~inPi & ~near
    cnt = np.zeros(N, np.int64); np.add.at(cnt, LP[W].reshape(-1), 1)
    assert len(W) == q * q * (q * q - 1) and (cnt[free] == 1).all(), 'exact whisker set check failed'
    Lv = sorted(set(PL[LP[v]].reshape(-1).tolist()) - {int(v)})
    RL = np.zeros(N, bool); RL[Lv] = True; RL[W] = True
    assert RL.sum() == q * (q + 1) * (q * q - q + 1)
    # segment / dual segment checks
    cntL = RH[LP].sum(1)
    assert ((cntL[PL] >= 2).sum(1)[RH] <= 1).all(), 'R_H not a segment set'
    cntP = RL[PL].sum(1)
    assert ((cntP[LP] >= 2).sum(1)[RL] <= 1).all(), 'R_L not a dual segment set'
    return RH, RL, int(v)


def orbits(perm):
    """orbit id and position for a permutation of order dividing |T|; returns (orb, pos, reps, sizes)."""
    n = len(perm)
    orb = -np.ones(n, np.int64); pos = np.zeros(n, np.int64); reps = []; sizes = []
    for x in range(n):
        if orb[x] >= 0:
            continue
        k = len(reps); reps.append(x); y = x; t = 0
        while orb[y] < 0:
            orb[y] = k; pos[y] = t; y = perm[y]; t += 1
        sizes.append(t)
    return orb, pos, np.array(reps), np.array(sizes)


if __name__ == '__main__':
    import sys, collections, time
    t0 = time.time()
    q, N, LP, PL, X = load(sys.argv[1])
    bgen = 2
    assert all(pow(bgen, k, q) != 1 for k in range(1, q - 1))
    pp, pl = torus_perms(q, N, LP, PL, X, bgen)
    RH, RL, v = sets(q, N, LP, PL, X)
    assert np.array_equal(RH[pp], RH) and np.array_equal(RL[pl], RL), 'sets not T-invariant'
    print(f'q={q}: |R_H|={RH.sum()} |R_L|={RL.sum()} both T-invariant ({time.time()-t0:.0f}s)')
    for name, perm, S in (('points', pp, None), ('lines', pl, None), ('R_H', pp, RH), ('R_L', pl, RL)):
        orb, pos, reps, sizes = orbits(perm)
        if S is not None:
            ids = np.unique(orb[S]); sz = sizes[ids]
        else:
            sz = sizes
        print(f'  {name}: orbit sizes', dict(sorted(collections.Counter(sz.tolist()).items())))
