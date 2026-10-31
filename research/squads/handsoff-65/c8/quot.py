# quotient of H(5) incidence graph by a permutation group; score = far pairs of the quotient (dist > 5)
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from g2grp import *
from collections import deque
import math
NV = P + L
def orbits_of_perms(perms):
    par = list(range(NV))
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for pr in perms:
        for v in range(NV):
            a, b = f(v), f(pr[v])
            if a != b: par[a] = b
    roots = {}
    orb = [0]*NV
    for v in range(NV):
        r = f(v)
        if r not in roots: roots[r] = len(roots)
        orb[v] = roots[r]
    return orb, len(roots)
def quotient_graph(orb, n):
    adjs = [set() for _ in range(n)]
    for k, l in enumerate(lines):
        lo = orb[P + k]
        for z in l:
            zo = orb[z]
            if zo != lo:
                adjs[zo].add(lo); adjs[lo].add(zo)
            else:
                return None  # orbit contains point and line: impossible
    return adjs
def far_pairs(adjs, D=5):
    n = len(adjs); bad = 0; diam = 0
    for s in range(n):
        d = [-1]*n; d[s] = 0; q = deque([s])
        while q:
            u = q.popleft()
            for w in adjs[u]:
                if d[w] < 0: d[w] = d[u]+1; q.append(w)
        for t in range(n):
            if d[t] < 0: bad += 10**9; diam = 99
            else:
                diam = max(diam, d[t])
                if d[t] > D and t > s: bad += 1
    return bad // 1 if bad < 10**9 else bad, diam
def write_edges(adjs, path):
    n = len(adjs)
    with open(path, 'w') as f:
        f.write(f"{n}\n")
        for u in range(n):
            for w in adjs[u]:
                if u < w: f.write(f"{u} {w}\n")
def cycles_of(perm):
    seen = [False]*NV; cyc = []
    for v in range(NV):
        if not seen[v]:
            c = []; x = v
            while not seen[x]:
                seen[x] = True; c.append(x); x = perm[x]
            cyc.append(c)
    return cyc
def order_of(perm):
    m = 1
    for c in cycles_of(perm):
        m = m*len(c)//math.gcd(m, len(c))
    return m
def perm_power(perm, k):
    res = list(range(NV))
    base = perm[:]
    while k:
        if k & 1: res = [base[x] for x in res]
        base = [base[x] for x in base]
        k >>= 1
    return res
def rand_elem(E, rng, m=30):
    g = [[int(i == j) for j in range(N)] for i in range(N)]
    for _ in range(m):
        e = rng.choice(E)
        c = rng.randrange(1, p)
        g = mat_mul(g, unip([[(c*x) % p for x in r] for r in e]))
    return g
