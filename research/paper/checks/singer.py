# Spot check of Section 4.3 of joint.tex (q = p prime): the cyclic model, Proposition 4.10, the spread {yK}, Corollary 4.12.
import itertools, sys
from collections import deque
p = int(sys.argv[1]); q = p
def mul(a, b, poly):
    r = [0] * 7
    for i in range(4):
        for j in range(4): r[i + j] = (r[i + j] + a[i] * b[j]) % p
    for k in range(6, 3, -1):  # reduce x^k, poly = x^4 + poly[3]x^3+...+poly[0]
        c = r[k]
        if c:
            r[k] = 0
            for t in range(4): r[k - 4 + t] = (r[k - 4 + t] - c * poly[t]) % p
    return tuple(r[:4])
one = (1, 0, 0, 0); X = (0, 1, 0, 0)
for poly in itertools.product(range(p), repeat=4):
    if poly[0] == 0: continue
    e = one; order = None
    for k in range(1, p**4):
        e = mul(e, X, poly)
        if e == one: order = k; break
    if order == p**4 - 1: break
g = X
pw = [one]
for k in range(p**4 - 2): pw.append(mul(pw[-1], g, poly))
log = {v: i for i, v in enumerate(pw)}
Q1 = p**4 - 1
def gp(i): return pw[i % Q1]
def frob(y, k):  # y^(q^k)
    if y == (0, 0, 0, 0): return y
    return gp(log[y] * q**k)
add = lambda a, b: tuple((x + y) % p for x, y in zip(a, b))
sc = lambda s, a: tuple(s * x % p for x in a)
def Tr(x):  # Tr_{E/F}, result in prime field: an element (c,0,0,0)
    t = (0, 0, 0, 0)
    for k in range(4): t = add(t, frob(x, k))
    assert t[1:] == (0, 0, 0)
    return t[0]
d = gp((q * q + 1) // 2)
def mulE(a, b):
    if a == (0,0,0,0) or b == (0,0,0,0): return (0,0,0,0)
    return gp(log[a] + log[b])
b = lambda y, z: Tr(mulE(d, mulE(y, frob(z, 2))))
NP = (q + 1) * (q * q + 1)
pts = list(range(NP))  # point <g^i>
vec = lambda i: gp(i)
def ptindex(v):
    return log[v] % NP
# all lines of PG(3,q)
lines = set()
for i in range(NP):
    for j in range(i + 1, NP):
        L = frozenset(ptindex(add(sc(s, vec(i)), sc(t, vec(j)))) for s in range(q) for t in range(q) if (s, t) != (0, 0))
        lines.add(L)
lines = list(lines)
assert len(lines) == (q*q + 1) * (q*q + q + 1)
cls = lambda i: i % (q + 1)
for L in lines:
    for a in range(q + 1): assert sum(1 for i in L if cls(i) == a) <= 2
ti = []
for L in lines:
    l = sorted(L)
    if b(vec(l[0]), vec(l[1])) == 0: ti.append(L)
assert len(ti) == (q + 1) * (q * q + 1)
for a in range(q + 1):
    good = all(sum(1 for i in L if cls(i) in (a, (q - a) % (q + 1))) == 2 for L in ti)
    assert good, a
pairs = [(a, bb) for a in range(q + 1) for bb in range(a, q + 1) if a != bb and all(sum(1 for i in L if cls(i) in (a, bb)) == 2 for L in ti)]
print("q =", q, "2-ovoid pairs:", pairs)
spread = {frozenset((i + (q*q + 1) * j) % NP for j in range(q + 1)) for i in range(NP)}
assert len(spread) == q*q + 1 and all(Lsp in set(ti) for Lsp in spread)
# Corollary 4.12 with a = 0
O = [i for i in pts if cls(i) in (0, q % (q + 1))]
adj = {}
def addE(u, v): adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
for k, L in enumerate(ti):
    for i in L:
        addE(('p', i), ('l', k))
        if i in O: addE(('c', i), ('l', k))
for k, Lsp in enumerate(spread):
    for i in Lsp: addE(('p', i), ('s1', k)); addE(('p', i), ('s2', k))
n = len(adj); assert n == 2 * (q*q + 1) * (q + 3), n
assert max(len(v) for v in adj.values()) == q + 3
def diam(A):
    best = 0
    for s in A:
        dist = {s: 0}; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in A[u]:
                if w not in dist: dist[w] = dist[u] + 1; dq.append(w)
        assert len(dist) == len(A); best = max(best, max(dist.values()))
    return best
d1 = diam(adj)
clones = sorted(v for v in adj if v[0] == 'c'); shadows = sorted(v for v in adj if v[0] in ('s1', 's2'))
B = len(shadows)
for i, cl in enumerate(clones):
    for y in (shadows[(2 * i) % B], shadows[(2 * i + 1) % B]):
        assert y not in adj[cl]; addE(cl, y)
assert all(len(v) == q + 3 for v in adj.values())
print("Corollary 4.12: order", n, "diameter", d1, "; regular completion diameter", diam(adj))
