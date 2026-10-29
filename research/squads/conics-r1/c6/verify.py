# Independent check (card c6) of a self-polar extension of PG(2,q) by k new points and k new lines.
# Usage: python3 -I verify.py <json file> <q>
# Builds PG(2,q) and the conic polarity from scratch (no code from the search), then checks:
# old incidences kept, every pair of points and of lines shares a line / point, max degree <= q+2,
# self-polarity of the whole structure, and the diameter of the point-line incidence graph.
import json, sys, itertools
from collections import deque
import numpy as np

path, q = sys.argv[1], int(sys.argv[2])
data = json.load(open(path))
k = len(data["lines_on_h"])
Y = np.array(data["Y"], dtype=int)
assert Y.shape == (k, k) and (Y == Y.T).all(), "Y must be symmetric k x k"

def norm(v):
    v = tuple(x % q for x in v)
    for x in v:
        if x:
            inv = pow(x, q - 2, q)
            return tuple((y * inv) % q for y in v)
    raise ValueError("zero vector")

pts = sorted({norm(v) for v in itertools.product(range(q), repeat=3) if any(v)})
N = len(pts)
assert N == q * q + q + 1
idx = {p: i for i, p in enumerate(pts)}          # old points and old lines use the same list
inv2 = pow(2, q - 2, q)

def polar_line_of_point(p):                     # point (x,y,z) -> line [z, -2y, x]
    x, y, z = pts[p]
    return idx[norm((z, -2 * y, x))]

def pole_point_of_line(L):                      # line [a,b,c] -> point (c, -b/2, a)
    a, b, c = pts[L]
    return idx[norm((c, -b * inv2, a))]

assert all(pole_point_of_line(polar_line_of_point(p)) == p for p in range(N))

# old incidence I0[p, L] = 1 iff p lies on L
I0 = np.zeros((N, N), dtype=int)
for p in range(N):
    for L in range(N):
        a, b, c = pts[L]
        x, y, z = pts[p]
        if (a * x + b * y + c * z) % q == 0:
            I0[p, L] = 1
assert (I0.sum(axis=0) == q + 1).all() and (I0.sum(axis=1) == q + 1).all()

# S[i] = old lines through new point h_i (given as normalized triples in the JSON)
S = []
for lst in data["lines_on_h"]:
    S.append(sorted({idx[norm(tuple(t))] for t in lst}))
    assert len(S[-1]) == len(lst), "repeated line in a list"

# extended structure: points 0..N-1 old, N..N+k-1 new h_i; lines 0..N-1 old, N..N+k-1 new K_i
n = N + k
I = np.zeros((n, n), dtype=int)                 # I[point, line]
I[:N, :N] = I0
for i in range(k):
    for L in S[i]:
        I[N + i, L] = 1                         # h_i on old line L
    for p in range(N):                          # K_i = theta(h_i) contains p iff h_i on theta0(p)
        if I[N + i, polar_line_of_point(p)]:
            I[p, N + i] = 1
    for j in range(k):
        I[N + i, N + j] = Y[i, j]               # h_i on K_j

# the polarity theta on the extended structure (involution: point <-> line)
th_pt = {}   # theta applied to a point -> line index
th_ln = {}   # theta applied to a line -> point index
for p in range(N):
    th_pt[p] = polar_line_of_point(p)
    th_ln[p] = pole_point_of_line(p)
for i in range(k):
    th_pt[N + i] = N + i                        # h_i -> K_i
    th_ln[N + i] = N + i                        # K_i -> h_i

# 1. self-polarity: (u on v) iff (theta(v) on theta(u))
self_polar = all(I[u, v] == I[th_ln[v], th_pt[u]] for u in range(n) for v in range(n))

# 2. every pair of points shares a line; every pair of lines shares a point
M = I @ I.T
np.fill_diagonal(M, 1)
noncollinear_pts = int((M == 0).sum() // 2)
M2 = I.T @ I
np.fill_diagonal(M2, 1)
noncollinear_lines = int((M2 == 0).sum() // 2)

# 3. degrees
maxdeg = int(max(I.sum(axis=1).max(), I.sum(axis=0).max()))

# 4. diameter of the point-line incidence graph
adj = [[] for _ in range(2 * n)]
for u in range(n):
    for v in range(n):
        if I[u, v]:
            adj[u].append(n + v)
            adj[n + v].append(u)
diam = 0
for s in range(2 * n):
    dist = [-1] * (2 * n)
    dist[s] = 0
    dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                dq.append(y)
    if min(dist) < 0:
        diam = -1
        break
    diam = max(diam, max(dist))

ok = self_polar and noncollinear_pts == 0 and noncollinear_lines == 0 and maxdeg <= q + 2 and diam <= 3
print(json.dumps({"q": q, "k": k, "self_polar": bool(self_polar),
                  "noncollinear_point_pairs": noncollinear_pts,
                  "noncollinear_line_pairs": noncollinear_lines,
                  "max_degree": maxdeg, "q_plus_2": q + 2,
                  "incidence_diameter": diam, "PASS": bool(ok)}))
