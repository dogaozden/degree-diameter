# Bipartite base graphs for Z_m voltage lifts. Output: "V0 n0 NE" then edges "u v" with u < n0 <= v.
import itertools, sys, collections
def write(name, edges, n0, V0):
    with open(name + '.base', 'w') as f:
        f.write(f"{V0} {n0} {len(edges)}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
    deg = collections.Counter()
    for u, v in edges: deg[u] += 1; deg[v] += 1
    print(name, 'V0', V0, 'E', len(edges), 'degrees', sorted(set(deg.values())))
def inc(points, lines):
    # points/lines as lists of frozensets, incidence -> bipartite edges (points = side A)
    edges = []
    for i, P in enumerate(points):
        for j, L in enumerate(lines):
            if P in L: edges.append((i, len(points) + j))
    return edges
def pg(q):
    # PG(2,q) for prime q: points = normalized triples
    pts = []
    for a, b, c in itertools.product(range(q), repeat=3):
        if (a, b, c) == (0, 0, 0): continue
        first = next(x for x in (a, b, c) if x)
        if first == 1: pts.append((a, b, c))
    lines = pts[:]
    P = [frozenset(j for j, p in enumerate(pts) if sum(x*y for x, y in zip(p, l)) % q == 0) for l in lines]
    return [frozenset([i]) for i in range(len(pts))], P
# Heawood = PG(2,2) incidence; represent as points on lines via sets
pts = []
q = 2
pl = pg(2)
# build incidence directly
def pg_edges(q):
    pts = []
    for a, b, c in itertools.product(range(q), repeat=3):
        if (a, b, c) == (0, 0, 0): continue
        first = next(x for x in (a, b, c) if x)
        if first == 1: pts.append((a, b, c))
    n = len(pts)
    edges = [(i, n + j) for i, p in enumerate(pts) for j, l in enumerate(pts)
             if sum(x*y for x, y in zip(p, l)) % q == 0]
    return edges, n
e, n = pg_edges(2); write('heawood', e, n, 2*n)
e, n = pg_edges(3); write('pg23', e, n, 2*n)
# Tutte-Coxeter (GQ(2,2) incidence) from LCF [-13,-9,7,-7,9,13]^5 on 30 vertices
lcf = [-13, -9, 7, -7, 9, 13] * 5
N = 30
E = set()
for i in range(N):
    E.add(tuple(sorted((i, (i+1) % N))))
    j = (i + lcf[i]) % N
    E.add(tuple(sorted((i, j))))
# bipartition by parity of vertex: check bipartite
col = {0: 0}; stack = [0]; adj = collections.defaultdict(list)
for u, v in E: adj[u].append(v); adj[v].append(u)
ok = True
while stack:
    x = stack.pop()
    for y in adj[x]:
        if y not in col: col[y] = 1 - col[x]; stack.append(y)
        elif col[y] == col[x]: ok = False
A = sorted(v for v in col if col[v] == 0); B = sorted(v for v in col if col[v] == 1)
ren = {v: i for i, v in enumerate(A + B)}
edges = [(ren[u], ren[v]) if col[u] == 0 else (ren[v], ren[u]) for u, v in E]
print('tutte8 bipartite', ok, len(A), len(B))
write('tc8', edges, len(A), N)
# PG(2,4) over GF(4): elements 0,1,2=w,3=w+1 ; add = xor on 2-bit labels; mult table
mul = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def gf4_points():
    pts = []
    for t in itertools.product(range(4), repeat=3):
        if t == (0,0,0): continue
        f = next(x for x in t if x)
        if f == 1: pts.append(t)
    return pts
pts4 = gf4_points()
n4 = len(pts4)
edges4 = []
for i, p in enumerate(pts4):
    for j, l in enumerate(pts4):
        s = 0
        for x, y in zip(p, l): s ^= mul[x][y]
        if s == 0: edges4.append((i, n4 + j))
write('pg24', edges4, n4, 2*n4)
# GQ W(3): points of PG(3,3), totally isotropic lines of symplectic form
pts3 = []
for t in itertools.product(range(3), repeat=4):
    if t == (0,0,0,0): continue
    f = next(x for x in t if x)
    if f == 1: pts3.append(t)
def B(x, y): return (x[0]*y[1]-x[1]*y[0]+x[2]*y[3]-x[3]*y[2]) % 3
lines = set()
for p, q_ in itertools.combinations(pts3, 2):
    if B(p, q_) == 0:
        span = set()
        for a, b in itertools.product(range(3), repeat=2):
            v = tuple((a*p[k]+b*q_[k]) % 3 for k in range(4))
            if v != (0,0,0,0):
                f = next(x for x in v if x)
                if f == 1: span.add(v)
        lines.add(frozenset(pts3.index(v) for v in span))
lines = sorted(lines, key=lambda s: sorted(s))
print('W3 lines', len(lines))
n = len(pts3)
edgesw = [(i, n + j) for j, L in enumerate(lines) for i in L]
write('gq33', edgesw, n, n + len(lines))
