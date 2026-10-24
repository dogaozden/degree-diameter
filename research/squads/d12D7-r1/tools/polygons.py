"""Generalized polygon incidence graphs over GF(q), q any prime power (field tables from build_haar2.Field).

  pg q : PG(2,q): points/lines = normalized vectors of GF(q)^3, incidence x.y = 0.          diameter 3, girth 6
  gq q : W(q): points of PG(3,q), lines = totally isotropic lines of x0y1-x1y0+x2y3-x3y2.  diameter 4, girth 8
  gh q : split Cayley hexagon H(q): points of X0X4+X1X5+X2X6 = X3^2 in PG(6,q), lines = lines of the quadric
         satisfying Tits' equations p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.   diameter 6, girth 12
write(kind, q, path): file "P\\n" then one line per polygon line with its q+1 point ids.
"""
import itertools, sys, os
from collections import deque
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'frontier'))
from build_haar2 import Field

POLY = {4: 'x^2+x+1', 8: 'x^3+x+1', 9: 'x^2+1', 16: 'x^4+x+1', 25: 'x^2+2', 27: 'x^3+2x+1', 32: 'x^5+x^2+1',
        49: 'x^2+1'}


class F:
    def __init__(self, q):
        self.q = q
        f = Field(q, POLY.get(q))
        self.add = [[int(x) for x in r] for r in f.add]
        self.mul = [[int(x) for x in r] for r in f.mul]
        self.neg = [int(x) for x in f.neg]
        self.inv = [int(x) for x in f.inv]

    def sub(self, a, b): return self.add[a][self.neg[b]]


def normalize(F_, v):
    for x in v:
        if x:
            s = F_.inv[x]
            return tuple(F_.mul[s][c] for c in v)
    raise ValueError


def span_points(F_, x, y, index):
    """points of the projective line through x, y"""
    q = F_.q
    mem = {index[x], index[y]}
    for a in range(q):
        v = tuple(F_.add[x[k]][F_.mul[a][y[k]]] for k in range(len(x)))
        mem.add(index[normalize(F_, v)])
    return frozenset(mem)


def pg(q):
    Fq = F(q)
    pts = [v for v in itertools.product(range(q), repeat=3) if next((c for c in v if c), 0) == 1]
    lines = []
    for l in pts:
        lines.append([i for i, x in enumerate(pts)
                      if Fq.add[Fq.add[Fq.mul[x[0]][l[0]]][Fq.mul[x[1]][l[1]]]][Fq.mul[x[2]][l[2]]] == 0])
    return len(pts), lines


def gq(q):
    Fq = F(q)
    A, M, S = Fq.add, Fq.mul, Fq.sub
    pts = [v for v in itertools.product(range(q), repeat=4) if next((c for c in v if c), 0) == 1]
    index = {v: i for i, v in enumerate(pts)}

    def form(x, y):
        return A[S(M[x[0]][y[1]], M[x[1]][y[0]])][S(M[x[2]][y[3]], M[x[3]][y[2]])]
    lines = set()
    for i, x in enumerate(pts):
        for j in range(i + 1, len(pts)):
            if form(x, pts[j]) == 0:
                lines.add(span_points(Fq, x, pts[j], index))
    L = [sorted(s) for s in lines]
    assert len(pts) == len(L) == (q + 1) * (q * q + 1), (len(pts), len(L))
    return len(pts), L


def gh(q):
    Fq = F(q)
    A, M, S = Fq.add, Fq.mul, Fq.sub
    def Qf(v):
        return S(A[A[M[v[0]][v[4]]][M[v[1]][v[5]]]][M[v[2]][v[6]]], M[v[3]][v[3]])
    pts = [v for v in itertools.product(range(q), repeat=7) if next((c for c in v if c), 0) == 1 and Qf(v) == 0]
    N = len(pts)
    assert N == (q ** 6 - 1) // (q - 1), N
    index = {v: i for i, v in enumerate(pts)}
    def pl(x, y, a, b): return S(M[x[a]][y[b]], M[x[b]][y[a]])
    def B(x, y):  # polar form of Q
        two = A[1][1]
        t = A[A[A[M[x[0]][y[4]]][M[x[4]][y[0]]]][A[M[x[1]][y[5]]][M[x[5]][y[1]]]]][A[M[x[2]][y[6]]][M[x[6]][y[2]]]]
        return S(t, M[two][M[x[3]][y[3]]])
    lines = set()
    for i, x in enumerate(pts):
        for j in range(i + 1, N):
            y = pts[j]
            if B(x, y): continue
            if pl(x, y, 1, 2) != pl(x, y, 3, 4) or pl(x, y, 5, 4) != pl(x, y, 3, 2) or pl(x, y, 2, 0) != pl(x, y, 3, 5) \
               or pl(x, y, 6, 5) != pl(x, y, 3, 0) or pl(x, y, 0, 1) != pl(x, y, 3, 6) or pl(x, y, 4, 6) != pl(x, y, 3, 1):
                continue
            lines.add(span_points(Fq, x, y, index))
    L = [sorted(s) for s in lines]
    assert len(L) == N and all(len(l) == q + 1 for l in L), (len(L), N)
    return N, L


def check(P, L, n):
    """incidence graph regular, diameter n, girth 2n"""
    V = 2 * P
    adj = [[] for _ in range(V)]
    for k, l in enumerate(L):
        for p in l:
            adj[p].append(P + k); adj[P + k].append(p)
    deg = {len(a) for a in adj}
    ecc = 0
    for s in (0, P):
        dist = [-1] * V; dist[s] = 0; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = dist[u] + 1; dq.append(w)
        ecc = max(ecc, max(dist))
        assert min(dist) >= 0
    return deg, ecc


def write(kind, q, path):
    P, L = {'pg': pg, 'gq': gq, 'gh': gh}[kind](q)
    with open(path, 'w') as f:
        f.write(f"{P}\n")
        for l in L:
            f.write(' '.join(map(str, l)) + '\n')
    return P, L


if __name__ == '__main__':
    kind, q = sys.argv[1], int(sys.argv[2])
    out = sys.argv[3]
    P, L = write(kind, q, out)
    n = {'pg': 3, 'gq': 4, 'gh': 6}[kind]
    deg, ecc = check(P, L, n)
    print(kind, q, 'points', P, 'lines', len(L), 'degrees', deg, 'diameter (ecc from a point and a line)', ecc)
