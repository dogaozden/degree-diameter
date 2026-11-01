# Find base automorphisms (symplectic collineations of W(3)) of a given prime order acting freely on the 80 vertices;
# write the orbit structure used by w3rep (SYM=file): edge orbits and vertex orbits.
import random, sys, itertools
from itertools import product
sys.setrecursionlimit(10000)
def B(x, y):
    return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % 3
def norm(v):
    i = next(k for k in range(4) if v[k]); return tuple(v) if v[i] == 1 else tuple((2*c) % 3 for c in v)
pts = sorted({norm(v) for v in product(range(3), repeat=4) if any(v)})
assert len(pts) == 40
def span(a, b):
    s = set()
    for c1, c2 in product(range(3), repeat=2):
        w = tuple((c1*a[k] + c2*b[k]) % 3 for k in range(4))
        if any(w): s.add(norm(w))
    return frozenset(s)
lines = sorted({span(a, b) for a, b in itertools.combinations(pts, 2) if B(a, b) == 0}, key=lambda L: sorted(L))
assert len(lines) == 40
pidx = {p: i for i, p in enumerate(pts)}
lidx = {L: i for i, L in enumerate(lines)}
edges = [(pidx[p], 40 + lidx[L]) for L in lines for p in L]
def transv(v, a):
    # matrix of x -> x + a B(v,x) v
    cols = []
    for j in range(4):
        e = [0]*4; e[j] = 1
        bx = B(v, e)
        cols.append(tuple((e[k] + a*bx*v[k]) % 3 for k in range(4)))
    return cols  # columns: images of basis vectors
def apply(M, x):  # M given as list of images of basis vectors
    return tuple(sum(x[j]*M[j][k] for j in range(4)) % 3 for k in range(4))
def mat_mul(M1, M2):  # (M1 * M2)(x) = M1(M2(x)); columns of M2 are images of basis
    return [apply(M1, M2[j]) for j in range(4)]
def perm_of(M):
    pp = [pidx[norm(apply(M, p))] for p in pts]
    ll = [lidx[frozenset(norm(apply(M, p)) for p in L)] for L in lines]
    return pp, ll
def order_of_perm(p):
    seen = [0]*len(p); from math import lcm; o = 1
    for i in range(len(p)):
        if not seen[i]:
            c = 0; j = i
            while not seen[j]: seen[j] = 1; j = p[j]; c += 1
            o = lcm(o, c)
    return o
def cyc_lengths_ok(p, k):
    seen = [0]*len(p)
    for i in range(len(p)):
        if not seen[i]:
            c = 0; j = i
            while not seen[j]: seen[j] = 1; j = p[j]; c += 1
            if c != k: return False
    return True
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
target = int(sys.argv[2]) if len(sys.argv) > 2 else 5
out = sys.argv[3] if len(sys.argv) > 3 else 'sym.txt'
vecs = pts
found = None
for trial in range(20000):
    M = [(1 if j == 0 else 0, 0, 0, 0) for j in range(4)]
    M = [tuple(1 if k == j else 0 for k in range(4)) for j in range(4)]
    for _ in range(random.randint(3, 12)):
        v = random.choice(vecs); a = random.choice([1, 2])
        M = mat_mul(transv(v, a), M)
    pp, ll = perm_of(M)
    if order_of_perm(pp) == target and cyc_lengths_ok(pp, target) and cyc_lengths_ok(ll, target):
        found = (pp, ll); break
assert found, 'no element found'
pp, ll = found
sig = pp + [40 + x for x in ll]   # vertex permutation
# check automorphism
E = set(map(tuple, edges)) | set((v, u) for u, v in edges)
assert all((sig[u], sig[v]) in E for u, v in edges)
# vertex orbits
vo = [-1]*80; reps = []; wts = []
for v in range(80):
    if vo[v] < 0:
        k = len(reps); x = v; c = 0
        while vo[x] < 0: vo[x] = k; x = sig[x]; c += 1
        reps.append(v); wts.append(c)
# edge orbits
eo = {}; eorb = [-1]*len(edges); K = 0
ed_index = {(u, v): i for i, (u, v) in enumerate(edges)}
for i, (u, v) in enumerate(edges):
    if eorb[i] < 0:
        x, y = u, v; 
        while True:
            j = ed_index[(x, y)]
            if eorb[j] >= 0: break
            eorb[j] = K; x, y = sig[x], sig[y]
        K += 1
with open(out, 'w') as f:
    f.write("%d %d\n" % (len(edges), K))
    f.write(" ".join(str(eorb[i]) for i in range(len(edges))) + "\n")
    f.write("%d\n" % len(reps))
    f.write(" ".join("%d %d" % (r, w) for r, w in zip(reps, wts)) + "\n")
print('order', target, 'vertex orbits', len(reps), 'edge orbits', K, 'written', out)
