# Spot check of Section 5 of joint.tex (odd prime q): H(q) from (2.1), Lemma 5.1(d), Theorem 5.5 (exact whiskers),
# Theorem 5.3 (doubling with whiskers) with m = 2, all written from the paper's formulas.
import itertools, sys
from collections import deque
q = int(sys.argv[1]); c, c0, c1 = map(int, sys.argv[2:5]); m = 2
inv = lambda x: pow(x % q, q - 2, q)
def norm(v):
    for x in v:
        if x % q:
            i = inv(x); return tuple(y * i % q for y in v)
Q = lambda X: (X[0]*X[4] + X[1]*X[5] + X[2]*X[6] - X[3]*X[3]) % q
b = lambda X, Y: (Q([x + y for x, y in zip(X, Y)]) - Q(X) - Q(Y)) % q
pts = sorted({norm(v) for v in itertools.product(range(q), repeat=7) if any(v) and Q(v) == 0})
N = (q + 1) * (q**4 + q**2 + 1); assert len(pts) == N
def tits(x, y):
    p = lambda i, j: (x[i]*y[j] - x[j]*y[i]) % q
    return (p(1,2) == p(3,4) and p(5,4) == p(3,2) and p(2,0) == p(3,5) and p(6,5) == p(3,0) and p(0,1) == p(3,6) and p(4,6) == p(3,1))
lines = set()
for i, x in enumerate(pts):
    for y in pts[i+1:]:
        if b(x, y) == 0 and tits(x, y):
            lines.add(frozenset(norm([(s*xx + t*yy) % q for xx, yy in zip(x, y)]) for s in range(q) for t in range(q) if (s, t) != (0, 0)))
lines = list(lines); assert len(lines) == N, len(lines)
on = {p: [] for p in pts}
for i, L in enumerate(lines):
    for p in L: on[p].append(i)
assert all(len(v) == q + 1 for v in on.values())
e1 = norm((0,1,0,0,0,0,0)); e6 = norm((0,0,0,0,0,0,1))
v = next(i for i, L in enumerate(lines) if e1 in L and e6 in L)
inPi = lambda X, al, be: (X[0] + c*X[4] + al*X[2] + be*X[5]) % q == 0
# Lemma 5.1(d) check via BFS distances from v
adj = {}
for i, L in enumerate(lines):
    for p in L:
        adj.setdefault(('l', i), []).append(('p', p)); adj.setdefault(('p', p), []).append(('l', i))
def bfs(s, A):
    d = {s: 0}; dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in A[u]:
            if w not in d: d[w] = d[u] + 1; dq.append(w)
    return d
dv = bfs(('l', v), adj)
for p in pts: assert (dv[('p', p)] <= 3) == (p[2] == 0 and p[5] == 0)
free = [p for p in pts if not inPi(p, 0, 0) and dv[('p', p)] == 5]
assert len(free) == q**3 * (q*q - 1)
nu = lambda X: (X[2]*X[3] - X[4]*X[5]) * inv(c*X[2]*X[2] + X[5]*X[5]) % q
G = lambda a, bb: ((c0*a + c1*bb) * (a*a + c*bb*bb) - bb**3) % q
assert all(G(a, bb) for a in range(q) for bb in range(q) if (a, bb) != (0, 0))
W = set()
for al in range(q):
    for be in range(q):
        if (al, be) == (0, 0): continue
        Fz = G(al, be) * inv(al*al + c*be*be) % q
        for i, L in enumerate(lines):
            if i != v and all(inPi(p, al, be) for p in L):
                X = [p for p in L if inPi(p, 0, 0)]; assert len(X) == 1
                if nu(X[0]) == Fz: W.add(i)
assert len(W) == q*q*(q*q - 1), len(W)
for p in free: assert sum(1 for i in on[p] if i in W) == 1
print("q =", q, ": |W| =", len(W), "and every free point is on exactly one whisker")
# Theorem 5.3 doubling, m = 2
S = {i for i, L in enumerate(lines) if all(inPi(p, 0, 0) for p in L)}
assert len(S) == q**3 + 1 and v in S
Pv = set(lines[v]); Lv = {i for p in Pv for i in on[p] if i != v}
PPi = {p for p in pts if inPi(p, 0, 0)}
lev = {}
for x in [('p', p) for p in PPi] + [('l', i) for i in Lv | W]: lev[x] = 0
for x in [('p', p) for p in Pv] + [('l', i) for i in S]: lev[x] = 1
lev[('l', v)] = 2
level = lambda x: lev.get(x, -1)
words = lambda k: list(itertools.product(range(m), repeat=k + 1)) if k >= 0 else [()]
comparable = lambda w, u: w[:len(u)] == u[:len(w)]
V = [(x, w) for x in adj for w in words(level(x))]
idx = {vv: i for i, vv in enumerate(V)}
A2 = [[] for _ in V]
for (x, w) in V:
    for y in adj[x]:
        for u in words(level(y)):
            if comparable(w, u): A2[idx[(x, w)]].append(idx[(y, u)])
n = len(V)
formula = 2*N + (m - 1)*(q**4 + 2*q**3 + q*q + 2*q + 2 + len(W) + m*(q**3 + q + 2) + m*m)
assert n == formula, (n, formula)
assert max(len(a) for a in A2) == q + m
best = 0
for s in range(n):
    d = [-1]*n; d[s] = 0; dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in A2[u]:
            if d[w] < 0: d[w] = d[u] + 1; dq.append(w)
    assert min(d) >= 0
    best = max(best, max(d))
print("doubling with whiskers, m = 2: order", n, "max degree", q + m, "diameter", best)
