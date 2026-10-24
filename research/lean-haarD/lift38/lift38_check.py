# Lift38: the voltage lift of the 4-vertex cubic base graph over G = Z3^2 x|_M Z8, M = [[0,2],[1,0]].
# Vertices (u, g), g in G, index u*72 + code(g) with code(x,y,j) = x + 3y + 9j (as in Formula288.lean).
# Edge (u,g) ~ (w, g*alpha) for each base edge u-w with voltage alpha. Product: (v,j)(w,l) = (v + M^j w, j + l).
# Checks: simple, cubic, bipartite (colour = base side), eccentricity <= 8 everywhere.
# `python3 lift38_check.py dump` prints the sorted neighbour lists, which were diffed against Formula288.adjL (equal).
import sys
from collections import deque

P, M, MM = 3, (0, 2, 1, 0), 8   # M = [[0,2],[1,0]] row-major
BASE_EDGES = [(0, 2, (0, 0, 0)), (0, 2, (2, 0, 3)), (0, 3, (0, 0, 0)),
              (1, 2, (0, 0, 0)), (1, 3, (1, 1, 3)), (1, 3, (1, 1, 2))]
# Inverse voltages used by Formula288.lean's backward edges.
INV = {(0, 0, 0): (0, 0, 0), (2, 0, 3): (0, 1, 5), (1, 1, 3): (1, 2, 5), (1, 1, 2): (1, 1, 6)}
NB = 4
G = [(x, y, j) for j in range(MM) for y in range(P) for x in range(P)]  # code x + 3y + 9j, as in Formula288.lean
GI = {g: i for i, g in enumerate(G)}
NG = len(G)  # 72
IDENT = (0, 0, 0)

def mv(Mj, v):
    return ((Mj[0]*v[0] + Mj[1]*v[1]) % P, (Mj[2]*v[0] + Mj[3]*v[1]) % P)

def mm(A, B):
    return ((A[0]*B[0]+A[1]*B[2]) % P, (A[0]*B[1]+A[1]*B[3]) % P,
            (A[2]*B[0]+A[3]*B[2]) % P, (A[2]*B[1]+A[3]*B[3]) % P)

POW = [(1, 0, 0, 1)]
for _ in range(MM):
    POW.append(mm(POW[-1], M))
assert POW[MM] == (1, 0, 0, 1)

def gmul(g, h):
    a, b = mv(POW[g[2]], h[:2])
    return ((g[0] + a) % P, (g[1] + b) % P, (g[2] + h[2]) % MM)

def vid(u, g):
    return u * NG + GI[g]

for al, ai in INV.items():
    assert gmul(al, ai) == IDENT and gmul(ai, al) == IDENT, (al, ai)

N = NB * NG
adj = [set() for _ in range(N)]
for (u, w, al) in BASE_EDGES:
    for g in G:
        a, b = vid(u, g), vid(w, gmul(g, al))
        assert a != b
        adj[a].add(b)
        adj[b].add(a)

# Count directed incidences to check the lift is cubic as a multigraph too.
mult = {}
for (u, w, al) in BASE_EDGES:
    for g in G:
        k = (min(vid(u, g), vid(w, gmul(g, al))), max(vid(u, g), vid(w, gmul(g, al))))
        mult[k] = mult.get(k, 0) + 1
assert all(c == 1 for c in mult.values()), "multi-edge in lift"

deg = [len(s) for s in adj]
assert min(deg) == 3 and max(deg) == 3, (min(deg), max(deg))
side = [0 if (v // NG) in (0, 1) else 1 for v in range(N)]
for v in range(N):
    for w in adj[v]:
        assert side[v] != side[w]
assert sum(deg) // 2 == 432

def ecc(s):
    dist = [-1] * N
    dist[s] = 0
    q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                q.append(y)
    assert min(dist) >= 0, "disconnected"
    return max(dist)

diam = max(ecc(s) for s in range(N))
print("n", N, "edges", sum(deg)//2, "degree", min(deg), max(deg), "bipartite yes", "diameter", diam)
assert diam <= 8

if len(sys.argv) > 1 and sys.argv[1] == 'dump':
    for v in range(N):
        print(v, sorted(adj[v]))
