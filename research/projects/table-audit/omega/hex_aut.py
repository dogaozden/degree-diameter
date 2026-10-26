"""Automorphisms of the split Cayley hexagon H(q) as built by tools/moore_build.c (Q(6,q): X0X4+X1X5+X2X6 = X3^2,
Tits' equations), from SL(3,q) <= G_2(q) acting as x = (u | x3 | w) -> (A u | x3 | A^-T w) (the same embedding as
research/d12D8/omega/haut.py, rewritten for moore_build's coordinates and fields).  Every map is checked to send every
hexagon line to a hexagon line.  Output: a text file with one automorphism per line, as a permutation of the 2n
incidence-graph vertices (points 0..n-1, lines n..2n-1), and its point/line orbit counts.
usage: hex_aut.py H_EDGES H_COORDS q OUT singer|singerpow:K|trans|rand:SEED [...]
  singer: a companion matrix of order q^2+q+1 (a Singer cycle of SL(3,q)); singerpow:K its K-th power."""
import sys, random
sys.path.insert(0, __file__.rsplit('/', 2)[0] + '/tools')
from gf import GF

hpath, cpath, q, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
F = GF(q)
with open(hpath) as f:
    nv = int(f.readline()); E = [tuple(map(int, l.split())) for l in f if l.strip()]
n = nv // 2
pts = {}
coords = [None] * n
with open(cpath) as f:
    for l in f:
        a = list(map(int, l.split()))
        coords[a[0]] = tuple(a[1:]); pts[tuple(a[1:])] = a[0]
lines = [[] for _ in range(n)]
for u, v in E:
    lines[v - n].append(u)
lkey = {tuple(sorted(L)): i for i, L in enumerate(lines)}


def norm(x):
    for a in x:
        if a:
            s = F.inv[a]; return tuple(F.mul[s][b] for b in x)


def mmul(A, B):
    return [[F.dot(A[i], [B[k][j] for k in range(len(B))]) for j in range(len(B[0]))] for i in range(len(A))]


def minv(A):
    m = len(A); M = [list(A[i]) + [int(i == j) for j in range(m)] for i in range(m)]
    for c in range(m):
        r = next(r for r in range(c, m) if M[r][c]); M[c], M[r] = M[r], M[c]
        s = F.inv[M[c][c]]; M[c] = [F.mul[s][x] for x in M[c]]
        for r in range(m):
            if r != c and M[r][c]:
                f = M[r][c]; M[r] = [F.sub(x, F.mul[f][y]) for x, y in zip(M[r], M[c])]
    return [row[m:] for row in M]


def det3(A):
    a = A
    t1 = F.mul[a[0][0]][F.sub(F.mul[a[1][1]][a[2][2]], F.mul[a[1][2]][a[2][1]])]
    t2 = F.mul[a[0][1]][F.sub(F.mul[a[1][0]][a[2][2]], F.mul[a[1][2]][a[2][0]])]
    t3 = F.mul[a[0][2]][F.sub(F.mul[a[1][0]][a[2][1]], F.mul[a[1][1]][a[2][0]])]
    return F.add[F.sub(t1, t2)][t3]


def order(A):
    I = [[int(i == j) for j in range(3)] for i in range(3)]; B = [r[:] for r in A]; k = 1
    while B != I:
        B = mmul(B, A); k += 1
        if k > q ** 3: return -1
    return k


def perm_of(A):
    Ai = minv(A); AT = [[Ai[j][i] for j in range(3)] for i in range(3)]
    pp = [0] * n
    for i, x in enumerate(coords):
        u = [F.dot(A[r], x[0:3]) for r in range(3)]
        w = [F.dot(AT[r], x[4:7]) for r in range(3)]
        y = norm(tuple(u) + (x[3],) + tuple(w))
        pp[i] = pts[y]
    lp = [lkey.get(tuple(sorted(pp[p] for p in L)), -1) for L in lines]
    assert min(lp) >= 0, "a line is not mapped to a line"
    assert len(set(pp)) == n and len(set(lp)) == n
    return pp + [n + x for x in lp]


def orbits(perm, lo, hi):
    seen = set(); sizes = []
    for x in range(lo, hi):
        if x in seen: continue
        s = 0; y = x
        while y not in seen:
            seen.add(y); s += 1; y = perm[y]
        sizes.append(s)
    return sizes


def companion():
    for a in range(q):
        for b in range(q):
            A = [[0, 0, 1], [1, 0, F.neg[b]], [0, 1, F.neg[a]]]
            if det3(A) == 1 and order(A) == q * q + q + 1:
                return A


res = []
for spec in sys.argv[5:]:
    if spec.startswith('singer'):
        A = companion(); K = int(spec.split(':')[1]) if ':' in spec else 1
        B = A
        for _ in range(K - 1): B = mmul(B, A)
        res.append((spec, perm_of(B)))
    elif spec == 'trans':
        res.append((spec, perm_of([[1, 1, 0], [0, 1, 0], [0, 0, 1]])))
    elif spec.startswith('rand'):
        rng = random.Random(int(spec.split(':')[1]))
        while True:
            A = [[rng.randrange(q) for _ in range(3)] for _ in range(3)]
            if det3(A) == 1: break
        res.append((spec, perm_of(A)))
with open(out, 'w') as f:
    for spec, p in res:
        po, lo = orbits(p, 0, n), orbits(p, n, 2 * n)
        print(spec, 'point orbits', len(po), 'sizes', sorted(set(po)), 'line orbits', len(lo), 'sizes', sorted(set(lo)))
        f.write(' '.join(map(str, p)) + '\n')
