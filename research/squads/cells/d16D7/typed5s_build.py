#!/usr/bin/env python3
"""typed5s_build.py: independent rebuild (numpy) of the edge list of a typed5s .sol file; it writes the same lines in the
same order as `typed5s edges`, so the two outputs must be byte-identical. cell-16-7 session, 2026-10-25.

The graph (see typed5s.c / research/squads/cells/d16D7.md): levels j of types T[j] in {H, D}; class A of level j is the
points of H(q) for H, the lines for D. Vertex (point p, level j) = 2Nj + p, (line l, level j) = 2Nj + N + l.
Edges, in this order:
  1. incidence: for each level j, line l, k-th point p of l (hexgen order): (p,j) ~ (l,j);
  2. matchings: for j, k = 1..r, element x of kind A_j: friendly (A_j and B_{j+k} of the same kind) -> (x,j) ~ (x,j+k)
     unless x is freed (x in R_H for points, R_L for lines); otherwise (x,j) ~ (sigma(x), j+k) with the equivariant map
     of the "unf j k" block: sigma(g^t s) = g^(t+off) d;
  3. line-side hubs (k,t) = 2NL + mk + t ~ (g^(t+off_j) rep_j, j) for each level j (one free A-slot per level);
  4. point-side hubs (k,t) = 2NL + m KB + mk + t, the same with B-slots;
  5. hub graph: hub B (kB,t) ~ hub A (kA, t+c) for each "kB kA c".
g acts on a point x = (v, a, w) (v = x0..x2, a = x3, w = x4..x6) as (g v, a, g^-T w), on lines through their points.
usage: typed5s_build.py HEXBIN SOL OUT.edges"""
import sys
import numpy as np


def main():
    hexfn, solfn, outfn = sys.argv[1:4]
    b = open(hexfn, 'rb').read()
    q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32))
    Q1 = q + 1
    LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
    X = np.frombuffer(b[12 + 4 * Lc * Q1:], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    # lines through each point, in increasing line order (as typed5s builds PL)
    flat_p = LP.reshape(-1)
    flat_l = np.repeat(np.arange(Lc), Q1)
    order = np.lexsort((flat_l, flat_p))
    PL = flat_l[order].reshape(N, Q1)
    tok = open(solfn).read().split()

    class Tok:
        def __init__(self, t):
            self.t, self.i = t, 0
        def __next__(self):
            self.i += 1
            return self.t[self.i - 1]
        def peek(self):
            return self.t[self.i] if self.i < len(self.t) else None
    it = Tok(tok)
    assert next(it) == 'typed5s'
    qq, NN, L, T, m, n = int(next(it)), int(next(it)), int(next(it)), next(it), int(next(it)), int(next(it))
    assert qq == q and NN == N and len(T) == L
    R = (L - 1) // 2
    ty = [1 if c == 'D' else 0 for c in T]
    assert next(it) == 'gmat'
    g = np.array([int(next(it)) for _ in range(9)], dtype=np.int64).reshape(3, 3)
    # inverse of g mod q
    det = int(round(np.linalg.det(g))) % q
    adjg = np.array([[((g[(j + 1) % 3][(i + 1) % 3] * g[(j + 2) % 3][(i + 2) % 3] - g[(j + 1) % 3][(i + 2) % 3] * g[(j + 2) % 3][(i + 1) % 3])) % q
                      for j in range(3)] for i in range(3)], dtype=np.int64)
    gi = (adjg * pow(det, q - 2, q)) % q
    assert np.array_equal((g @ gi) % q, np.eye(3, dtype=np.int64))
    # point action
    code = X @ (q ** np.arange(7, dtype=np.int64))
    assert np.all(np.diff(code) > 0)
    Y = np.zeros_like(X)
    Y[:, 0:3] = (X[:, 0:3] @ g.T) % q
    Y[:, 3] = X[:, 3]
    Y[:, 4:7] = (X[:, 4:7] @ gi) % q       # (g^-T w)_i = sum_k gi[k][i] w_k
    lead = np.argmax(Y != 0, axis=1)
    inv = np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)
    Y = (Y * inv[Y[np.arange(N), lead]][:, None]) % q
    yc = Y @ (q ** np.arange(7, dtype=np.int64))
    pp = np.searchsorted(code, yc)
    assert np.all(code[pp] == yc)
    perm = [pp, None]
    a0, b0 = pp[LP[:, 0]], pp[LP[:, 1]]
    eq = PL[a0][:, :, None] == PL[b0][:, None, :]
    hit = eq.reshape(Lc, -1)
    assert np.all(hit.sum(axis=1) == 1)
    perm[1] = PL[a0, hit.argmax(axis=1) // Q1]
    for k in range(Q1):        # every image point lies on the image line
        assert np.all((PL[pp[LP[:, k]]] == perm[1][:, None]).any(axis=1))
    # orbits: rep = smallest element, pos = power of g from the rep
    orb, pos, orbel = [], [], []
    for kd in range(2):
        pm = perm[kd]
        mn = np.arange(N)
        cur = np.arange(N)
        for _ in range(m):
            cur = pm[cur]
            mn = np.minimum(mn, cur)
        assert np.array_equal(cur, np.arange(N)), 'orbit length does not divide m'
        reps = np.unique(mn)
        assert len(reps) * m == N
        oid = np.searchsorted(reps, mn)
        ps = np.zeros(N, dtype=np.int64)
        c = reps.copy()
        el = np.zeros((len(reps), m), dtype=np.int64)
        for t in range(m):
            ps[c] = t
            el[:, t] = c
            c = pm[c]
        assert np.array_equal(c, reps)
        orb.append(oid); pos.append(ps); orbel.append(el)
    def elem(kd, o, t):
        return orbel[kd][o, np.mod(t, m)]
    inR = [np.zeros(N, bool), np.zeros(N, bool)]
    for kd, name in ((0, 'RH'), (1, 'RL')):
        assert next(it) == name
        k = int(next(it))
        xs = np.array([int(next(it)) for _ in range(k)], dtype=np.int64)
        os_ = orb[kd][xs]
        inR[kd][orbel[kd][os_].reshape(-1)] = True
    VID = lambda j, kind, x: j * 2 * N + kind * N + x
    out = []
    lines_p = LP.reshape(-1)
    lines_l = np.repeat(np.arange(Lc), Q1)
    for j in range(L):
        out.append(np.stack([VID(j, 0, lines_p), VID(j, 1, lines_l)], axis=1))
    for j in range(L):
        for k in range(1, R + 1):
            j2 = (j + k) % L
            a, bk = ty[j], 1 - ty[j2]
            x = np.arange(N)
            if a == bk:
                keep = ~inR[a]
                out.append(np.stack([VID(j, a, x[keep]), VID(j2, bk, x[keep])], axis=1))
            else:
                assert next(it) == 'unf'
                jj, kk, c = int(next(it)), int(next(it)), int(next(it))
                assert jj == j and kk == k and c == N // m
                arr = np.array([int(next(it)) for _ in range(3 * c)], dtype=np.int64).reshape(c, 3)
                s, d, off = arr[:, 0], arr[:, 1], arr[:, 2]
                os_, od = orb[a][s], orb[bk][d]
                assert len(np.unique(os_)) == c and len(np.unique(od)) == c
                udst = np.zeros(c, dtype=np.int64); uoff = np.zeros(c, dtype=np.int64)
                udst[os_] = od
                uoff[os_] = np.mod(off + pos[bk][d] - pos[a][s], m)
                ox = orb[a][x]
                y = elem(bk, udst[ox], pos[a][x] + uoff[ox])
                keep = np.ones(N, bool)
                if it.peek() == 'unfR':   # freed orbits of this non-friendly transition (local duality surgery)
                    next(it)
                    cr = int(next(it))
                    fo = orb[a][np.array([int(next(it)) for _ in range(cr)], dtype=np.int64)]
                    keep = ~np.isin(ox, fo)
                out.append(np.stack([VID(j, a, x[keep]), VID(j2, bk, y[keep])], axis=1))
    NV0 = 2 * N * L
    hubs = {}
    for side, name in ((0, 'hubB'), (1, 'hubA')):
        assert next(it) == name
        K = int(next(it))
        arr = np.array([int(next(it)) for _ in range(2 * L * K)], dtype=np.int64).reshape(K, L, 2)
        hubs[side] = (K, arr)
    KB, KA = hubs[0][0], hubs[1][0]
    assert n == NV0 + m * (KB + KA)
    for side in (0, 1):
        K, arr = hubs[side]
        base = NV0 + (0 if side == 0 else m * KB)
        kk = np.repeat(np.arange(K), m * L)
        tt = np.tile(np.repeat(np.arange(m), L), K)
        jj = np.tile(np.arange(L), K * m)
        kinds = np.array([ty[j] if side == 0 else 1 - ty[j] for j in range(L)])
        xs = arr[kk, jj, 0]; offs = arr[kk, jj, 1]
        kind = kinds[jj]
        o = np.where(kind == 0, orb[0][xs], orb[1][xs])
        p0 = np.where(kind == 0, pos[0][xs], pos[1][xs])
        e0 = orbel[0][np.minimum(o, N // m - 1), np.mod(tt + offs + p0, m)]
        e1 = orbel[1][np.minimum(o, N // m - 1), np.mod(tt + offs + p0, m)]
        e = np.where(kind == 0, e0, e1)
        out.append(np.stack([base + m * kk + tt, jj * 2 * N + kind * N + e], axis=1))
    assert next(it) == 'hg'
    ne = int(next(it))
    arr = np.array([int(next(it)) for _ in range(3 * ne)], dtype=np.int64).reshape(ne, 3)
    ee = np.repeat(np.arange(ne), m); tt = np.tile(np.arange(m), ne)
    out.append(np.stack([NV0 + m * arr[ee, 0] + tt, NV0 + m * (KB + arr[ee, 1]) + np.mod(tt + arr[ee, 2], m)], axis=1))
    E = np.concatenate(out)
    with open(outfn, 'w') as f:
        f.write('%d\n' % n)
        CH = 1 << 21
        for i in range(0, len(E), CH):
            blk = E[i:i + CH]
            f.write('\n'.join('%d %d' % (u, v) for u, v in blk.tolist()))
            f.write('\n')
    print('wrote %s: n=%d edges=%d' % (outfn, n, len(E)))


if __name__ == '__main__':
    main()
