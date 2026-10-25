"""c8: exact reach of new vertices in the quotient graph (base H(q) + matchings with unit deletions + hubs + super-hubs).
A new vertex w reaches every copy (y,g) at quotient distance d(w,y), so checking quotient BFS from each new vertex is
the same test as uhcheck's new-vertex sources. Prints, per new vertex, the number of base points beyond 6, base lines
beyond 7, and new vertices beyond their limit (same side 6, opposite 7).
Usage: python3 c8_qbfs.py GHFILE STATE UNITS EXTRAS [SOURCES...]  (SOURCES = new-vertex indices, default all)"""
import sys, collections
GH, STATE, UNITS, EXT = sys.argv[1:5]
srcs_arg = [int(x) for x in sys.argv[5:]]
tok = open(GH).read().split(); P, q = int(tok[0]), int(tok[1]); Q1 = q + 1
lineP = [[int(x) for x in tok[2 + l * Q1: 2 + (l + 1) * Q1]] for l in range(P)]
pl = [[] for _ in range(P)]
for l in range(P):
    for p in lineP[l]: pl[p].append(l)
st = open(STATE).read().split(); J = int(st[2])
idx = 7; sig = [[0] * P for _ in range(J)]
for p in range(P):
    for t in range(J):
        sig[t][p] = int(st[idx]); idx += 2
units = [(int(a[0]), int(a[1]) - 1) for a in (l.split() for l in open(UNITS)) if len(a) >= 2]
NU = len(units); deleted = set(units)
ex = open(EXT).read().split(); NS = int(ex[0])
NX = 2 * NU + NS
N = 2 * P + NX
adj = [[] for _ in range(N)]
def add(a, b): adj[a].append(b); adj[b].append(a)
for l in range(P):
    for p in lineP[l]: add(p, P + l)
for p in range(P):
    for t in range(J):
        if (p, t) not in deleted: add(p, P + sig[t][p])
for i, (p, t) in enumerate(units):
    l = sig[t][p]; h = 2 * P + 2 * i; hp = h + 1
    add(h, p); add(hp, P + l)
vals = list(map(int, ex[1:])); 
for k in range(0, len(vals), 2):
    a, b = vals[k], vals[k + 1]; add(2 * P + a, 2 * P + b)
side = [None] * NX
for i in range(NU): side[2 * i] = 1; side[2 * i + 1] = 0
for s in range(NS): side[2 * NU + s] = None
for _ in range(4):
    for k in range(0, len(vals), 2):
        a, b = vals[k], vals[k + 1]
        if side[a] is None and side[b] is not None: side[a] = 1 - side[b]
        if side[b] is None and side[a] is not None: side[b] = 1 - side[a]
def new_side(v):  # side of node index (base side: point 0, line 1)
    return side[v]
def bfs(s):
    d = [-1] * N; d[s] = 0; dq = collections.deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    return d
sources = srcs_arg if srcs_arg else list(range(NX))
worst = 0; total_bad = 0
for v in sources:
    s = 2 * P + v; d = bfs(s)
    sv = side[v]
    bad_pts = sum(1 for y in range(P) if d[y] < 0 or d[y] > (6 if sv == 0 else 7))
    bad_lines = sum(1 for y in range(P, 2 * P) if d[y] < 0 or d[y] > (6 if sv == 1 else 7))
    bad_new = 0
    for u in range(NX):
        if u == v: continue
        lim = 6 if side[u] == sv else 7
        du = d[2 * P + u]
        if du < 0 or du > lim: bad_new += 1
    total_bad += bad_pts + bad_lines + bad_new
    if bad_pts + bad_lines + bad_new: print('new vertex %d (side %s): points beyond 6 %d, lines beyond 7 %d, new beyond limit %d' % (v, sv, bad_pts, bad_lines, bad_new))
print('total unmet (new-vertex sources to all targets):', total_bad)
