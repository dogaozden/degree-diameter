"""Independent check of Corollary 2 (distance layers) on thick buildings over GF(2), built from scratch:
PG(3,2), PG(4,2) (type A), Sp(6,2) and O^-(8,2) (type C3, the latter with parameters (2,2,4)).
Prediction uses my own Weyl-group enumeration (thin_check.group) and Theorem 2 (corrected form)."""
import itertools, random, sys
from collections import deque, defaultdict
import numpy as np
sys.path.insert(0, '/tmp/claude-0/-home-user-degree-diameter/bca0bf0f-5904-53d7-a35c-bf89127b664f/scratchpad/review')
from thin_check import coxeter_matrix, group, colour, parabolic

def predict(t, n, params):
    M = coxeter_matrix(t, n); S, elems, length, key = group(M); I = colour(M)
    # per-element weight q_w: BFS again tracking product of params along a reduced word (left mult)
    e = np.eye(n); wt = {key(e): 1}; fr = [e]
    while fr:
        nf = []
        for A in fr:
            ka = key(A)
            for i, s in enumerate(S):
                B = s @ A; kb = key(B)
                if kb not in wt and length[kb] == length[ka] + 1:
                    wt[kb] = wt[ka] * params[i]; nf.append(B)
                elif kb in wt and length[kb] == length[ka] + 1:
                    assert wt[kb] == wt[ka] * params[i], "q_w not well defined"
        fr = nf
    WI = [parabolic(S, I[0], n), parabolic(S, I[1], n)]
    P = [1, 1]
    for K in (0, 1):
        for i in I[K]: P[K] *= 1 + params[i]
    out = {}
    for J in (0, 1):
        level = {}; X = {key(u): u for u in WI[J]}
        for kk in X: level[kk] = 1
        mm = 1
        while len(level) < len(elems):
            Jm = J if mm % 2 == 0 else 1 - J
            newX = {}
            for kk, A in X.items():
                for u in WI[Jm]:
                    B = A @ u; newX[key(B)] = B
            mm += 1
            for kb in newX:
                if kb not in level: level[kb] = mm
            X = newX
        for K in (0, 1):
            cnt = defaultdict(int)
            for k in elems:
                mJ = level[k]; Jm1 = J if (mJ - 1) % 2 == 0 else 1 - J
                cnt[mJ - (1 if Jm1 == K else 0)] += wt[k]
            assert all(c % P[K] == 0 for c in cnt.values())
            out[(J, K)] = {d: c // P[K] for d, c in sorted(cnt.items())}
    return I, P, out

def span(vs):
    sp = {0}
    for v in vs:
        sp |= {x ^ v for x in sp}
    return frozenset(sp - {0})

def subspaces_pg(dim):
    """all subspaces of GF(2)^dim, by dimension, as frozensets of nonzero vectors"""
    vecs = list(range(1, 2 ** dim))
    by = {0: {frozenset()}}
    for k in range(1, dim):
        new = set()
        for U in by[k - 1]:
            for v in vecs:
                if v not in U:
                    new.add(span(list(U) + [v]))
        by[k] = new
    return by

def flags_graph(by_dim, ranks, I):
    """ranks = list of subspace dimensions corresponding to nodes 1..r; chambers = chains; I = colour classes (0-based nodes)"""
    r = len(ranks)
    # enumerate chambers
    chambers = [()]
    for k in range(r):
        new = []
        for ch in chambers:
            prev = ch[-1] if ch else frozenset()
            for U in by_dim[ranks[k]]:
                if prev <= U:
                    new.append(ch + (U,))
        chambers = new
    # vertex of 'residue type I[K]' = flag of type S \ I[K] = I[1-K]
    adj = defaultdict(set)
    for ch in chambers:
        a = (0, tuple(ch[i] for i in I[1]))   # residue of type I1 = flag of type I2
        b = (1, tuple(ch[i] for i in I[0]))   # residue of type I2 = flag of type I1
        adj[a].add(b); adj[b].add(a)
    return chambers, adj

def bfs_layers(adj, src):
    dist = {src: 0}; dq = deque([src])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if y not in dist: dist[y] = dist[x] + 1; dq.append(y)
    lay = {(0,): defaultdict(int), (1,): defaultdict(int)}
    res = {0: defaultdict(int), 1: defaultdict(int)}
    for v, d in dist.items(): res[v[0]][d] += 1
    return {K: dict(sorted(res[K].items())) for K in (0, 1)}, len(dist)

def check(name, by_dim, ranks, t, n, params, nsrc=3):
    I, P, out = predict(t, n, params)
    chambers, adj = flags_graph(by_dim, ranks, I)
    nv = len(adj)
    ok = True
    random.seed(1)
    for J in (0, 1):
        side = [v for v in adj if v[0] == J]
        for src in random.sample(side, min(nsrc, len(side))):
            lay, reach = bfs_layers(adj, src)
            assert reach == nv
            for K in (0, 1):
                if lay[K] != out[(J, K)]:
                    ok = False; print("  MISMATCH", name, J, K, lay[K], out[(J, K)])
    degs = sorted({len(adj[v]) for v in adj})
    print(f"{name}: chambers={len(chambers)} vertices={nv} degrees={degs} P={P} layers I1->(I1,I2) {out[(0,0)]} {out[(0,1)]}  {'MATCH' if ok else 'FAIL'}")
    sys.stdout.flush()

# PG(3,2), PG(4,2)
for dim in (4, 5):
    by = subspaces_pg(dim)
    check(f"PG({dim-1},2)", by, list(range(1, dim)), 'A', dim - 1, [2] * (dim - 1))

# polar spaces over GF(2) in GF(2)^8 / GF(2)^6
def polar(dim, Q):
    pts = [v for v in range(1, 2 ** dim) if Q(v) == 0]
    ptset = set(pts)
    by = {1: {frozenset([v]) for v in pts}}
    k = 1
    while True:
        new = set()
        for U in by[k]:
            for v in pts:
                if v in U: continue
                W = span(list(U) + [v])
                if all(x in ptset for x in W): new.add(W)
        if not new: break
        k += 1; by[k] = new
    return by

def bits(v, dim): return [(v >> i) & 1 for i in range(dim)]
def Qsp(v):   # O(7,2)?  use Sp(6,2) via its O(7,2)~Sp(6,2) iso? simpler: symplectic: all points, totally isotropic subspaces
    return 0
def Qell8(v):
    x = bits(v, 8)
    return (x[0]*x[1] + x[2]*x[3] + x[4]*x[5] + x[6] + x[6]*x[7] + x[7]) % 2

by = polar(8, Qell8)
print({k: len(v) for k, v in by.items()})
check("O-(8,2)", by, [1, 2, 3], 'B', 3, [2, 2, 4])

# Sp(6,2): totally isotropic subspaces for the symplectic form
def symp(u, v, dim=6):
    a = bits(u, dim); b = bits(v, dim)
    return (a[0]*b[1] + a[1]*b[0] + a[2]*b[3] + a[3]*b[2] + a[4]*b[5] + a[5]*b[4]) % 2
pts = list(range(1, 64))
bysp = {1: {frozenset([v]) for v in pts}}
for k in (2, 3):
    new = set()
    for U in bysp[k - 1]:
        for v in pts:
            if v in U: continue
            if all(symp(u, v) == 0 for u in U):
                new.add(span(list(U) + [v]))
    bysp[k] = new
print({k: len(v) for k, v in bysp.items()})
check("Sp(6,2)", bysp, [1, 2, 3], 'B', 3, [2, 2, 2])
