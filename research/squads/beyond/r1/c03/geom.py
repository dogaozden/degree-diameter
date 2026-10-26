"""Q(4,q), q odd prime power: points, totally singular lines, elliptic-quadric ovoid.
Points of x0^2 + x1*x2 + x3*x4 = 0 in PG(4,q). Field GF(q) built from tables (q = p^k, k <= 2 used here).
Usage: python3 geom.py q  -> writes inst_q{q}.txt (N, m, lines as point lists, ovoid) and prints checks."""
import itertools
import sys
import numpy as np


def make_field(q):
    p = next(x for x in range(2, q + 1) if q % x == 0)
    k = 0
    t = q
    while t > 1:
        assert t % p == 0
        t //= p
        k += 1
    if k == 1:
        ADD = np.array([[(a + b) % p for b in range(q)] for a in range(q)])
        MUL = np.array([[(a * b) % p for b in range(q)] for a in range(q)])
    else:
        assert k == 2, 'only k<=2 implemented'
        # find monic irreducible x^2 + c1 x + c0 over GF(p)
        for c1 in range(p):
            for c0 in range(p):
                if all((x * x + c1 * x + c0) % p for x in range(p)):
                    break
            else:
                continue
            break
        def dec(a):
            return (a % p, a // p)  # a = c0 + c1*p  (coefficient of 1, of x)
        def enc(c0, c1):
            return (c0 % p) + p * (c1 % p)
        ADD = np.zeros((q, q), dtype=np.int64)
        MUL = np.zeros((q, q), dtype=np.int64)
        for a in range(q):
            a0, a1 = dec(a)
            for b in range(q):
                b0, b1 = dec(b)
                ADD[a, b] = enc(a0 + b0, a1 + b1)
                # (a0 + a1 x)(b0 + b1 x) = a0b0 + (a0b1+a1b0) x + a1b1 x^2, x^2 = -c1 x - c0
                s0 = a0 * b0
                s1 = a0 * b1 + a1 * b0
                s2 = a1 * b1
                MUL[a, b] = enc(s0 - c0 * s2, s1 - c1 * s2)
    NEG = np.array([int(np.where(ADD[a] == 0)[0][0]) for a in range(q)])
    INV = np.zeros(q, dtype=np.int64)
    for a in range(1, q):
        INV[a] = int(np.where(MUL[a] == 1)[0][0])
    return ADD, MUL, NEG, INV


def build(q):
    ADD, MUL, NEG, INV = make_field(q)
    F_ = range(q)
    two = int(ADD[1, 1])
    sq = lambda x: int(MUL[x, x])
    # enumerate projective points of Q
    pts = []
    seen = set()
    for v in itertools.product(F_, repeat=5):
        if not any(v):
            continue
        # quadric
        t = int(ADD[ADD[sq(v[0]), MUL[v[1], v[2]]], MUL[v[3], v[4]]])
        if t != 0:
            continue
        # normalize: first nonzero coordinate -> 1
        i0 = next(i for i in range(5) if v[i])
        iv = int(INV[v[i0]])
        nv = tuple(int(MUL[iv, x]) for x in v)
        if nv not in seen:
            seen.add(nv)
            pts.append(nv)
    pts.sort()
    N = len(pts)
    assert N == (q + 1) * (q * q + 1), N
    idx = {p: i for i, p in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)

    def Bvec(u, V):  # polar form B(u,V) for vector u and array V (rows)
        terms = [MUL[two, MUL[u[0], V[:, 0]]],
                 MUL[u[1], V[:, 2]], MUL[u[2], V[:, 1]],
                 MUL[u[3], V[:, 4]], MUL[u[4], V[:, 3]]]
        s = terms[0]
        for t_ in terms[1:]:
            s = ADD[s, t_]
        return s

    def normalize(v):
        i0 = next(i for i in range(5) if v[i])
        iv = int(INV[v[i0]])
        return tuple(int(MUL[iv, x]) for x in v)

    seen_pairs = np.zeros((N, N), dtype=bool)
    lines = []
    for i in range(N):
        Bi = Bvec(pts[i], P)
        js = np.nonzero(Bi == 0)[0]
        for j in js:
            j = int(j)
            if j <= i or seen_pairs[i, j]:
                continue
            pj = pts[j]
            lp = {i, j}
            for a in F_:
                if a == 0:
                    continue
                v = tuple(int(ADD[pts[i][k], MUL[a, pj[k]]]) for k in range(5))
                lp.add(idx[normalize(v)])
            assert len(lp) == q + 1
            lp = sorted(lp)
            for x in lp:
                for y in lp:
                    seen_pairs[x, y] = True
            lines.append(lp)
    m = len(lines)
    assert m == N, (m, N)
    # ovoid: x4 = lam*x3 with -lam a non-square
    squares = {sq(x) for x in range(1, q)}
    lam = next(l for l in range(1, q) if int(NEG[l]) not in squares)
    ovoid = [i for i, p in enumerate(pts) if p[4] == int(MUL[lam, p[3]])]
    assert len(ovoid) == q * q + 1, len(ovoid)
    O = set(ovoid)
    assert all(len(set(L) & O) == 1 for L in lines), 'not an ovoid'
    return pts, lines, ovoid


if __name__ == '__main__':
    q = int(sys.argv[1])
    pts, lines, ovoid = build(q)
    here = __file__.rsplit('/', 1)[0]
    with open(f'{here}/inst_q{q}.txt', 'w') as f:
        f.write(f'{len(pts)} {len(lines)} {len(ovoid)}\n')
        f.write(' '.join(map(str, ovoid)) + '\n')
        for L in lines:
            f.write(' '.join(map(str, L)) + '\n')
    print(f'q={q}: points {len(pts)}, lines {len(lines)}, ovoid {len(ovoid)} written')
