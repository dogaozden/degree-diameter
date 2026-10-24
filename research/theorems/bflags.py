"""Generic bipartite flag graph of a classical building over GF(2) (vectors = bitmasks):
  A_n : all subspaces of GF(2)^(n+1), types 1..n (vector dimensions)
  C_n : totally isotropic subspaces of GF(2)^(2n) for the standard symplectic form, types 1..n
Bipartition of the path diagram: odd types | even types.  Vertices: partial flags of odd type and of even type,
adjacent iff together a chamber.  Prints degrees, order, and the eccentricity from one vertex of each side
(the group is transitive on each side), to test the claim diameter = Coxeter number (A_n: n+1, C_n: 2n).
usage: python3 bflags.py A|C n"""
import sys, itertools
from collections import deque

kind, n = sys.argv[1], int(sys.argv[2])
dim = n + 1 if kind == 'A' else 2 * n
N = 1 << dim
def B(x, y):
    s = 0
    for k in range(0, dim, 2):
        s ^= (((x >> k) & 1) & ((y >> (k + 1)) & 1)) ^ (((x >> (k + 1)) & 1) & ((y >> k) & 1))
    return s
def iso(x, y): return kind == 'A' or B(x, y) == 0
def span_add(S, z): return frozenset(S | {s ^ z for s in S} | {z})
def ext(S):
    cand = [z for z in range(1, N) if z not in S and all(iso(s, z) for s in S)] if S else list(range(1, N))
    return {span_add(S, z) for z in cand}
# chambers: chains of subspaces of dims 1..n
levels = [ {frozenset(): None} ]
ch = [[frozenset()]]
chambers = [()]
for t in range(1, n + 1):
    new = []
    cache = {}
    for c in chambers:
        last = c[-1] if c else frozenset()
        if last not in cache: cache[last] = ext(last)
        for W in cache[last]:
            new.append(c + (W,))
    chambers = new
odd, even, edges = {}, {}, []
for c in chambers:
    o = tuple(c[i] for i in range(0, n, 2))      # types 1,3,5,...
    e = tuple(c[i] for i in range(1, n, 2))      # types 2,4,...
    oi = odd.setdefault(o, len(odd)); ei = even.setdefault(e, len(even)); edges.append((oi, ei))
No = len(odd); nv = No + len(even)
adj = [[] for _ in range(nv)]
for a, b in edges: adj[a].append(No + b); adj[No + b].append(a)
degs = sorted({len(x) for x in adj})
ecc = []
for s in (0, No):
    dist = [-1] * nv; dist[s] = 0; dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if dist[w] < 0: dist[w] = dist[u] + 1; dq.append(w)
    ecc.append(max(dist))
h = n + 1 if kind == 'A' else 2 * n
print(f"{kind}{n}(2): chambers {len(chambers)}, vertices {nv} (odd {No}, even {len(even)}), degrees {degs}, "
      f"ecc from each side {ecc}, Coxeter number {h}")
