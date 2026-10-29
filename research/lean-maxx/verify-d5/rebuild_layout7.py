#!/usr/bin/env python3
"""Independent rebuild of the seven-level graph HHHDHHD of Corollary 10.3 (c = 0, complete bipartite hub graph) over W(3,q), q = 5.
Shares no code with the Lean files or with the note's d5gq tools. Builds W(3,5) from the F_25-trace symplectic form,
the regular spread from the F_25-lines, a greedy maximal partial ovoid, a RANDOM bijection P -> L, the level graph
(Definitions 2.1/3.1 of research/theorems/D5_QUADRANGLE.md), and checks bipartite, max degree <= q+4, diameter <= 5 by BFS from every vertex."""
import itertools, random, sys
from collections import deque

q = 5
K = int(sys.argv[1]) if len(sys.argv) > 1 else 2
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
random.seed(seed)

# F_25 = F_5[x]/(x^2 - 2); element (a,b) = a + b x
def fadd(u, v): return ((u[0]+v[0]) % q, (u[1]+v[1]) % q)
def fmul(u, v): return ((u[0]*v[0] + 2*u[1]*v[1]) % q, (u[0]*v[1] + u[1]*v[0]) % q)
def fneg(u): return ((-u[0]) % q, (-u[1]) % q)
def trace(u): return (2*u[0]) % q  # Tr(a+bx) = 2a in F_5 (x conjugates to -x)
F25 = [(a, b) for a in range(q) for b in range(q)]
ZERO, ONE = (0, 0), (1, 0)
# vectors of F_25^2 viewed as F_5^4; symplectic form B(u,v) = Tr(u1 v2 - u2 v1)
vecs = [(x1, x2) for x1 in F25 for x2 in F25 if (x1, x2) != (ZERO, ZERO)]
def B(u, v):
    return trace(fadd(fmul(u[0], v[1]), fneg(fmul(u[1], v[0]))))
def smul(c, u):  # F_5 scalar c
    return (((c*u[0][0]) % q, (c*u[0][1]) % q), ((c*u[1][0]) % q, (c*u[1][1]) % q))
def normal(u):  # canonical F_5-projective rep
    best = min(smul(c, u) for c in range(1, q))
    return best
points = sorted({normal(u) for u in vecs})
assert len(points) == (q**4 - 1)//(q-1) == 156
pid = {p: i for i, p in enumerate(points)}
# totally isotropic lines: pairs of perpendicular distinct points, spanning subspace
def span_points(u, v):
    s = set()
    for a in range(q):
        for b in range(q):
            if a == 0 and b == 0: continue
            w = (fadd(smul(a, u)[0], smul(b, v)[0]), fadd(smul(a, u)[1], smul(b, v)[1]))
            s.add(pid[normal(w)])
    return frozenset(s)
lines = set()
for i, u in enumerate(points):
    for v in points[i+1:]:
        if B(u, v) == 0:
            lines.add(span_points(u, v))
lines = sorted(lines, key=lambda s: sorted(s))
assert len(lines) == (q+1)*(q*q+1) == 156 and all(len(l) == q+1 for l in lines)
# GQ axioms check
inc = [[] for _ in points]
for j, l in enumerate(lines):
    for p in l: inc[p].append(j)
assert all(len(x) == q+1 for x in inc)
for j, l in enumerate(lines):
    for p in range(len(points)):
        if p in l: continue
        cnt = sum(1 for p2 in l if any(p2 in lines[m] and p in lines[m] for m in inc[p]))
        assert cnt == 1
# regular spread: the F_25-lines {lam*u}
spread = set()
for u in vecs:
    s = frozenset(pid[normal((fmul(lam, u[0]), fmul(lam, u[1])))] for lam in F25 if lam != ZERO)
    spread.add(s)
lid = {l: j for j, l in enumerate(lines)}
S = sorted(lid[s] for s in spread)
assert len(S) == q*q+1
# S is a spread: partition of points, each a line of the GQ
cov = sorted(p for j in S for p in lines[j]); assert cov == list(range(156))
# greedy maximal partial ovoid
col = [set() for _ in points]
for l in lines:
    for p in l:
        col[p] |= set(l) - {p}
Z = []
order = list(range(156)); random.shuffle(order)
for p in order:
    if all(p not in col[z] for z in Z): Z.append(p)
if len(sys.argv) > 3 and sys.argv[3] == "bad":  # negative control: add a point collinear with Z[0] to the freed set
    extra = sorted(col[Z[0]] - set(Z))[0]; Z.append(extra); print("NEGATIVE CONTROL: added collinear point", extra)
print("partial ovoid size", len(Z), "spread size", len(S), "K", K)
assert 1 <= K <= min(len(S), len(Z)) and K + 3 <= q
sp = S[:K]; zz = Z[:K]
e = list(range(156)); random.shuffle(e)  # random bijection P -> L
einv = {l: p for p, l in enumerate(e)}

# elements: ('p', i) or ('l', j); colour: points False, lines True
tau = [True, True, True, False, True, True, False]
def T(i, j): return 1 <= (j - i) % 7 <= 3
def M(i, j, x):
    t, a = x
    if tau[i] == tau[j]:  # Phi e
        return ('l', e[a]) if t == 'p' else ('p', einv[a])
    return x
adj_lvl = {}
def nbrs_level(x):
    t, a = x
    if t == 'p': return [('l', j) for j in inc[a]]
    return [('p', p) for p in lines[a]]
def freed(i, j, x):
    if not (T(i, j) and tau[i] != tau[j]): return False
    t, a = x
    if tau[i]:  # lines in S
        return t == 'l' and a in sp_all
    return t == 'p' and a in Z_all
sp_all = set(S); Z_all = set(Z)
# vertices
V = {}
def vid(key):
    if key not in V: V[key] = len(V)
    return V[key]
edges = set()
def add(a, b):
    a, b = vid(a), vid(b)
    if a != b: edges.add((min(a, b), max(a, b)))
allel = [('p', a) for a in range(156)] + [('l', j) for j in range(156)]
for i in range(7):
    for x in allel:
        vid((x, i))
for i in range(7):
    for x in allel:
        for y in nbrs_level(x): add((x, i), (y, i))
for i in range(7):
    for j in range(7):
        if not T(i, j): continue
        for x in allel:
            if (x[0] == 'l') == tau[i] and not freed(i, j, x):  # x in A_i (lines iff tau true)
                add((x, i), (M(i, j, x), j))
# hubs
for v in range(K):
    for i in range(7):
        slot = ('l', sp[v]) if tau[i] else ('p', zz[v])
        add(('V', v), (slot, i))
for u in range(K):
    for i in range(7):
        slot = ('p', zz[u]) if tau[i] else ('l', sp[u])
        add(('U', u), (slot, i))
for v in range(K):
    for u in range(K):
        add(('V', v), ('U', u))
n = len(V)
adj = [[] for _ in range(n)]
for a, b in edges: adj[a].append(b); adj[b].append(a)
print("n =", n, "expected", 14*156 + 2*K, "edges", len(edges), "maxdeg", max(map(len, adj)))
# bipartite check
colr = [-1]*n
ok = True
for s in range(n):
    if colr[s] != -1: continue
    colr[s] = 0; dq = deque([s])
    while dq:
        a = dq.popleft()
        for b in adj[a]:
            if colr[b] == -1: colr[b] = 1 - colr[a]; dq.append(b)
            elif colr[b] == colr[a]: ok = False
print("bipartite:", ok)
diam = 0
for s in range(n):
    dist = [-1]*n; dist[s] = 0; dq = deque([s])
    while dq:
        a = dq.popleft()
        for b in adj[a]:
            if dist[b] < 0: dist[b] = dist[a] + 1; dq.append(b)
    assert min(dist) >= 0, "disconnected"
    diam = max(diam, max(dist))
print("diameter:", diam)
