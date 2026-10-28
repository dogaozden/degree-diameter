"""g2.py: collineations of H(q) beyond SL(3,q), and a cyclic group T of order k = q^2 - q + 1 acting semiregularly.

A linear collineation is found by mapping the coordinate apartment (e0, e5, e2, e4, e1, e6) onto a random apartment
(a0..a5) of H(q): g(e_j) = lambda_j a_pi(j), g(e3) = mu u' with u' orthogonal to the a_i (q odd) or u' = e3 (the
nucleus, q even); the lambdas are tried over F_q* subject to the similitude conditions and kept when g maps all lines of
H(q) to lines. Products of two such maps and their powers give an element h of projective order k (tested), and the
orbits of <h> on points and lines are checked to have size k.
Usage: python3 g2.py HEXBIN OUTPREFIX [seed]   writes OUTPREFIX.h (7x7 matrix), OUTPREFIX.pperm, OUTPREFIX.lperm
"""
import sys
import numpy as np
from hexlib import Hex


class F7:
    def __init__(self, H):
        self.H = H

    def mul(self, A, B):
        H = self.H
        n = A.shape[0]
        C = np.zeros((n, B.shape[1]), dtype=np.int64)
        for i in range(n):
            for j in range(B.shape[1]):
                acc = 0
                for t in range(A.shape[1]):
                    acc = H.ADD[acc, H.MUL[A[i, t], B[t, j]]]
                C[i, j] = acc
        return C

    def pw(self, A, e):
        R = np.eye(A.shape[0], dtype=np.int64)
        B = A.copy()
        while e:
            if e & 1:
                R = self.mul(R, B)
            B = self.mul(B, B)
            e >>= 1
        return R

    @staticmethod
    def is_scalar(A):
        d = A[0, 0]
        return d != 0 and (A == d * np.eye(A.shape[0], dtype=np.int64)).all()


def bform(H, x, y):
    """polar form x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3."""
    A, M, Ng = H.ADD, H.MUL, H.NEG
    s = 0
    for i, j in ((0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)):
        s = A[s, M[x[i], y[j]]]
    t = M[x[3], y[3]]
    s = A[s, Ng[A[t, t]]]
    return int(s)


def qform(H, x):
    A, M, Ng = H.ADD, H.MUL, H.NEG
    s = 0
    for i, j in ((0, 4), (1, 5), (2, 6)):
        s = A[s, M[x[i], x[j]]]
    return int(A[s, Ng[M[x[3], x[3]]]])


def nullvec(H, rows):
    """a nonzero vector orthogonal (dot product) to the given rows (6 x 7 of rank 6)."""
    M = rows.copy()
    r, piv = 0, []
    for c in range(7):
        p = next((i for i in range(r, M.shape[0]) if M[i, c]), None)
        if p is None:
            continue
        M[[r, p]] = M[[p, r]]
        M[r] = H.MUL[H.INV[M[r, c]], M[r]]
        for i in range(M.shape[0]):
            if i != r and M[i, c]:
                M[i] = H.ADD[M[i], H.MUL[H.NEG[M[i, c]], M[r]]]
        piv.append(c)
        r += 1
    free = [c for c in range(7) if c not in piv][0]
    v = np.zeros(7, dtype=np.int64)
    v[free] = 1
    for i, c in enumerate(piv):
        v[c] = H.NEG[M[i, free]]
    return v


def gram_row(H, x):
    """row vector y with y.z = b(x, z)."""
    A, M, Ng = H.ADD, H.MUL, H.NEG
    y = np.zeros(7, dtype=np.int64)
    for i, j in ((0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)):
        y[j] = A[y[j], x[i]]
    y[3] = Ng[A[x[3], x[3]]]
    return y


def maps_lines(H, g, lines_to_test):
    X = H.coord[H.lines[lines_to_test].ravel()]
    Y = H.matvec(g, X)
    try:
        ids = H.point_ids(Y).reshape(len(lines_to_test), H.q + 1)
    except ValueError:
        return False
    for row in ids:
        s = sorted(row.tolist())
        l = H.line_key.get((s[0], s[1]))
        if l is None or sorted(H.lines[l].tolist()) != s:
            return False
    return True


def random_apartment(H, rng):
    N = H.N
    a0 = int(rng.integers(N))
    d0 = H.bfs(a0)
    opp = np.where(d0[:N] == 6)[0]
    a3 = int(rng.choice(opp))
    d3 = H.bfs(a3)
    adj = H._adj
    # geodesics a0 -> a3: the points at distance 2 from a0 and 4 from a3, then continue
    paths = []
    for L1 in adj[a0]:
        for x in adj[L1]:
            if d0[x] == 2 and d3[x] == 4:
                for L2 in adj[x]:
                    if d3[L2] != 3:
                        continue
                    for y in adj[L2]:
                        if d3[y] == 2:
                            paths.append((x, y))
    i, j = rng.choice(len(paths), size=2, replace=False)
    (a1, a2), (a5, a4) = paths[i], paths[j]
    return [a0, a1, a2, a3, a4, a5]


def apartment_map(H, A, rng):
    """linear collineation sending (e0, e5, e2, e4, e1, e6) to the points A[0..5]."""
    q = H.q
    src = [0, 5, 2, 4, 1, 6]
    vec = {src[i]: H.coord[A[i]] for i in range(6)}
    rows = np.array([gram_row(H, vec[j]) for j in src])
    u = vec_e3 = None
    if q % 2:
        u = nullvec(H, rows)
    else:
        u = np.zeros(7, dtype=np.int64)
        u[3] = 1
    b04 = bform(H, vec[0], vec[4])
    b15 = bform(H, vec[1], vec[5])
    b26 = bform(H, vec[2], vec[6])
    Qu = qform(H, u)
    test = rng.choice(H.L, size=min(30, H.L), replace=False)
    for l1 in range(1, q):
        for l2 in range(1, q):
            for nu in range(1, q):
                lam = {0: 1, 1: l1, 2: l2}
                lam[4] = H.MUL[nu, H.INV[H.MUL[lam[0], b04]]]
                lam[5] = H.MUL[nu, H.INV[H.MUL[lam[1], b15]]]
                lam[6] = H.MUL[nu, H.INV[H.MUL[lam[2], b26]]]
                # mu^2 Q(u) = nu Q(e3) = -nu
                target = H.MUL[H.NEG[nu], H.INV[Qu]] if Qu else None
                if target is None:
                    continue
                mus = [m for m in range(1, q) if H.MUL[m, m] == target]
                for mu in mus:
                    g = np.zeros((7, 7), dtype=np.int64)
                    for j in src:
                        g[:, j] = H.MUL[lam[j], vec[j]]
                    g[:, 3] = H.MUL[mu, u]
                    if maps_lines(H, g, test) and maps_lines(H, g, np.arange(H.L)):
                        return g
    return None


def factor(n):
    f, d = [], 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1
    if n > 1:
        f.append(n)
    return f


def proj_order(F, g, E):
    """projective order of g, given an exponent E with g^E scalar."""
    o = E
    for p in sorted(set(factor(E))):
        while o % p == 0 and F.is_scalar(F.pw(g, o // p)):
            o //= p
    return o


def main():
    hexbin, out = sys.argv[1], sys.argv[2]
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = np.random.default_rng(seed)
    H = Hex(hexbin)
    H.bfs(0)
    q = H.q
    k = q * q - q + 1
    F = F7(H)
    gens = []
    while len(gens) < 2:
        A = random_apartment(H, rng)
        g = apartment_map(H, A, rng)
        if g is not None:
            gens.append(g)
            print('collineation found from apartment', A, flush=True)
    G2 = q ** 6 * (q ** 6 - 1) * (q ** 2 - 1)
    E = G2 * (q - 1)                          # g^E is scalar for every similitude (scalars have order | q-1)
    kf = factor(k)
    for trial in range(400):
        w = rng.integers(0, 2, size=6)
        g = np.eye(7, dtype=np.int64)
        for b in w:
            g = F.mul(g, gens[b])
        g = F.mul(g, F.mul(gens[0], gens[1]))
        o = proj_order(F, g, E)
        if o % k:
            continue
        h = F.pw(g, o // k)
        print(f'trial {trial}: order {o}, h = g^{o // k} has projective order {proj_order(F, h, k)}', flush=True)
        pm = H.point_ids(H.matvec(h, H.coord))
        lm = H.line_map(pm)
        ok = True
        for perm, name in ((pm, 'points'), (lm, 'lines')):
            seen = np.zeros(len(perm), dtype=bool)
            sizes = []
            for s in range(len(perm)):
                if seen[s]:
                    continue
                x, c = s, 0
                while not seen[x]:
                    seen[x] = True
                    x = perm[x]
                    c += 1
                sizes.append(c)
            print(f'  {name}: {len(sizes)} orbits, sizes {sorted(set(sizes))}')
            ok &= set(sizes) == {k}
        if ok:
            np.savetxt(out + '.h', h, fmt='%d')
            pm.astype(np.int32).tofile(out + '.pperm')
            lm.astype(np.int32).tofile(out + '.lperm')
            print('semiregular cyclic group of order', k, 'written to', out)
            return
    print('not found')


if __name__ == '__main__':
    main()
