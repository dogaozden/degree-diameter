# Independent check of a meta solution file (haar_gen3 format): H(G,S), G = Z_m x|_r Z_k, (g,A) ~ (s g,B).
import re, sys
from collections import deque
f = sys.argv[1]
lines = open(f).read().split('\n')
hdr = lines[0].split()
d, D = int(hdr[0]), int(hdr[1]); m, k, r = int(hdr[3]), int(hdr[4]), int(hdr[5]); N = int(hdr[hdr.index('N') + 1])
assert pow(r, k, m) == 1 and m * k == N
S = []
for ln in lines[1:]:
    mt = re.search(r'meta\(a=(\d+),j=(\d+)\)', ln)
    if mt: S.append((int(mt.group(1)), int(mt.group(2))))
assert len(S) == d and len(set(S)) == d, (len(S), d)
rp = [pow(r, j, m) for j in range(k)]
def mul(x, y):  # (a,j)(b,l) = (a + r^j b, j + l)
    return ((x[0] + rp[x[1]] * y[0]) % m, (x[1] + y[1]) % k)
def idx(x): return x[0] * k + x[1]
def el(i): return (i // k, i % k)
# A-vertex g adjacent to B-vertex s*g; B-vertex h adjacent to A-vertex s^-1 h
nbA = [None] * N; nbB = [[] for _ in range(N)]
for g in range(N):
    gg = el(g); row = []
    for s in S:
        h = idx(mul(s, gg)); row.append(h); nbB[h].append(g)
    nbA[g] = row
assert all(len(x) == d for x in nbB), "degree mismatch"
def bfs(src_side, src):
    # vertices: ('A',i) encoded as i, ('B',i) encoded as N+i
    dist = [-1] * (2 * N)
    start = src if src_side == 'A' else N + src
    dist[start] = 0; q = deque([start])
    while q:
        v = q.popleft(); dv = dist[v]
        if v < N:
            nb = [N + h for h in nbA[v]]
        else:
            nb = nbB[v - N]
        for w in nb:
            if dist[w] < 0:
                dist[w] = dv + 1; q.append(w)
    return dist
ok = True; diam = 0
for side in ('A', 'B'):
    dist = bfs(side, idx((0, 0)))
    if min(dist) < 0: ok = False; print("disconnected from", side)
    diam = max(diam, max(dist))
print(("VALID" if ok and diam <= D else "INVALID"), f"d={d} D={D} N={N} vertices={2*N} max_dist_from_e={diam}")
