# q = 2: the 12 whiskers listed in joint.tex (Corollary 5.15) checked from the paper's even-q model, and the doubling
# of Theorem 5.3 with m = 2 (order 208, maximum degree 4, diameter 6).
import itertools
from collections import deque
q = 2
Q = lambda X: (X[0]*X[4] + X[1]*X[5] + X[2]*X[6] + X[3]*X[3]) % 2
pts = [v for v in itertools.product(range(2), repeat=7) if any(v) and Q(v) == 0]
N = len(pts); assert N == 63
def tits(x, y):
    p = lambda i, j: (x[i]*y[j] - x[j]*y[i]) % 2
    return (p(1,2) == p(3,4) and p(5,4) == p(3,2) and p(2,0) == p(3,5) and p(6,5) == p(3,0) and p(0,1) == p(3,6) and p(4,6) == p(3,1))
add = lambda x, y: tuple((a + b) % 2 for a, b in zip(x, y))
lines = set()
for i, x in enumerate(pts):
    for y in pts[i+1:]:
        z = add(x, y)
        if Q(z) == 0 and tits(x, y): lines.add(frozenset((x, y, z)))
lines = list(lines); assert len(lines) == 63
W_txt = """(0010000)(0000110)
(1010000)(0000010)
(0110000)(0000111)
(1110000)(0000011)
(0010100)(0111010)
(0110100)(0011011)
(1011100)(0010010)
(1111100)(0110011)
(1000010)(0011001)
(0101010)(1010101)
(1111010)(0111001)
(1011110)(1110101)"""
W = []
for row in W_txt.split('\n'):
    a, b = [tuple(int(c) for c in t) for t in row.strip('()').split(')(')]
    W.append(frozenset((a, b, add(a, b))))
assert all(w in lines for w in W) and len(set(W)) == 12
inPi = lambda X: (X[3] - X[0] - X[4]) % 2 == 0   # delta = 1, z = 0
e1 = (0,1,0,0,0,0,0); e6 = (0,0,0,0,0,0,1)
v = next(L for L in lines if e1 in L and e6 in L)
S = [L for L in lines if all(inPi(p) for p in L)]; assert len(S) == q**3 + 1
adj = {}
for L in lines:
    for p in L: adj.setdefault(('p', p), []).append(('l', L)); adj.setdefault(('l', L), []).append(('p', p))
def bfs(s):
    d = {s: 0}; dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if w not in d: d[w] = d[u] + 1; dq.append(w)
    return d
dv = bfs(('l', v))
free = [p for p in pts if not inPi(p) and dv[('p', p)] == 5]
assert len(free) == q**3 * (q*q - 1)
for w in W: assert dv[('l', w)] == 6 and w not in S
for p in free: assert sum(1 for w in W if p in w) == 1
print("q = 2: the 12 listed lines form an exact whisker set")
# doubling, m = 2
m = 2
Pv = set(v); Lv = {L for p in Pv for L in lines if p in L and L != v}
lev = {}
for p in pts:
    if inPi(p): lev[('p', p)] = 0
for L in Lv | set(W): lev[('l', L)] = 0
for p in Pv: lev[('p', p)] = 1
for L in S: lev[('l', L)] = 1
lev[('l', v)] = 2
words = lambda k: list(itertools.product(range(m), repeat=k + 1)) if k >= 0 else [()]
comp = lambda w, u: w[:len(u)] == u[:len(w)]
V = [(x, w) for x in adj for w in words(lev.get(x, -1))]
idx = {x: i for i, x in enumerate(V)}
A = [[idx[(y, u)] for y in adj[x] for u in words(lev.get(y, -1)) if comp(w, u)] for (x, w) in V]
n = len(V); best = 0
for s in range(n):
    d = [-1]*n; d[s] = 0; dq = deque([s])
    while dq:
        u = dq.popleft()
        for t in A[u]:
            if d[t] < 0: d[t] = d[u] + 1; dq.append(t)
    assert min(d) >= 0; best = max(best, max(d))
print("doubling, m = 2: order", n, "max degree", max(len(a) for a in A), "diameter", best)
