"""ksym.py: subgroups K of Aut(H(q)) given by 7x7 matrices, their orbits on points/lines/flags, and the
K-invariant Z2-voltage classes coming from H^1 of the orbit graph (strictly invariant voltages).
usage: python3 ksym.py q GROUP   (GROUP: sl3 | torus)"""
import sys, itertools, random
sys.path.insert(0, '.')
import dmio

def mat_apply(M, x, q):
    return tuple(sum(M[i][j] * x[j] for j in range(7)) % q for i in range(7))

def normalize(v, q):
    for c in v:
        if c % q:
            s = pow(c, q - 2, q)
            return tuple(s * a % q for a in v)
    raise ValueError

def embed_sl3(A, q):
    """x012 -> A x012, x456 -> A^{-T} x456, x3 fixed"""
    # inverse transpose mod q
    import copy
    det = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
           + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])) % q
    inv = pow(det, q - 2, q)
    cof = [[0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            m = [[A[r][c] for c in range(3) if c != j] for r in range(3) if r != i]
            cof[i][j] = ((-1) ** (i + j)) * (m[0][0] * m[1][1] - m[0][1] * m[1][0]) % q
    # A^{-1} = adj / det, adj = cof^T ; A^{-T} = cof / det
    AmT = [[cof[i][j] * inv % q for j in range(3)] for i in range(3)]
    M = [[0] * 7 for _ in range(7)]
    for i in range(3):
        for j in range(3):
            M[i][j] = A[i][j] % q
            M[4 + i][4 + j] = AmT[i][j]
    M[3][3] = 1
    return M

def gens(q, kind):
    G = []
    if kind == 'sl3':
        for i in range(3):
            for j in range(3):
                if i != j:
                    A = [[int(r == c) for c in range(3)] for r in range(3)]
                    A[i][j] = 1
                    G.append(embed_sl3(A, q))
    elif kind == 'torus':
        g = next(x for x in range(2, q) if all(pow(x, (q - 1) // p, q) != 1 for p in range(2, q) if (q - 1) % p == 0 and all(p % d for d in range(2, p))))
        for (a, b) in [(g, 1), (1, g)]:
            c = pow(a * b, q - 2, q)
            d = [a, b, c, 1, pow(a, q - 2, q), pow(b, q - 2, q), pow(c, q - 2, q)]
            G.append([[d[i] if i == j else 0 for j in range(7)] for i in range(7)])
    return G

def perms(H, G):
    q = H.q
    idx = {c: i for i, c in enumerate(H.coords)}
    lineidx = {frozenset(L): l for l, L in enumerate(H.lines)}
    out = []
    for M in G:
        pp = [idx[normalize(mat_apply(M, x, q), q)] for x in H.coords]
        lp = []
        for L in H.lines:
            img = frozenset(pp[p] for p in L)
            if img not in lineidx:
                return None
            lp.append(lineidx[img])
        out.append((pp, lp))
    return out

class UF:
    def __init__(s, n): s.p = list(range(n))
    def f(s, x):
        while s.p[x] != x:
            s.p[x] = s.p[s.p[x]]; x = s.p[x]
        return x
    def u(s, a, b):
        a, b = s.f(a), s.f(b)
        if a != b: s.p[a] = b

if __name__ == '__main__':
    q, kind = int(sys.argv[1]), sys.argv[2]
    H = dmio.load(q)
    P = perms(H, gens(q, kind))
    if P is None:
        print('generators do NOT preserve the hexagon'); sys.exit(1)
    N, Q1 = H.N, q + 1
    up, ul = UF(N), UF(N)
    for pp, lp in P:
        for x in range(N): up.u(x, pp[x]); ul.u(x, lp[x])
    # flags: index l*Q1+k ; image of flag (p,l): (pp[p], lp[l]) -> index
    pos = {}
    for l, L in enumerate(H.lines):
        for k, p in enumerate(L): pos[(p, l)] = l * Q1 + k
    uf = UF(N * Q1)
    for pp, lp in P:
        for l, L in enumerate(H.lines):
            for k, p in enumerate(L):
                uf.u(l * Q1 + k, pos[(pp[p], lp[l])])
    po = {up.f(x) for x in range(N)}; lo = {ul.f(x) for x in range(N)}; fo = {uf.f(i) for i in range(N * Q1)}
    print(f'q={q} K={kind}: point orbits {len(po)}, line orbits {len(lo)}, flag orbits {len(fo)}')
    from collections import Counter
    print(' point orbit sizes', sorted(Counter(up.f(x) for x in range(N)).values()))
    print(' line orbit sizes', sorted(Counter(ul.f(x) for x in range(N)).values()))
    print(' flag orbit sizes', sorted(Counter(uf.f(i) for i in range(N * Q1)).values()))
