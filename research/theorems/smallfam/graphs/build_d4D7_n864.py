"""(4,7): a 4-regular bipartite graph of diameter 7 on 864 vertices (table: 840, Bond-Delorme).

Haar graph H(G, S) of G = Heis(F_9) x| C_16 (= SmallGroup(432, 233) = ((C3 x C3) : C3) : C16):
  F_9 = F_3[i]/(i^2 + 1), v = a + b i;  omega(v, w) = a b' - b a'.
  Heis(F_9) = {(v, z) : v in F_9, z in F_3},  (v, z)(w, z') = (v + w, z + z' + 2 omega(v, w)).
  y of order 16 acts by phi(v, z) = ((1 + i) v, -z)   (1 + i has order 8 in F_9^*, norm -1).
  G = {(v, z, j)},  (v, z, j)(w, z', l) = ((v, z) phi^j(w, z'), j + l mod 16).
  S = {(0, 0, 0), (2i, 0, 9), (2 + i, 0, 8), (1 + 2i, 2, 14)}.
  Vertices (g, A), (g, B); edges (g, A) ~ (s g, B) for s in S.
Pure Python, no symmetry assumed: BFS from every vertex.  Usage: python3 build_d4D7_n864.py [EDGES_OUT]
"""
import hashlib
import sys
from collections import deque


def fadd(v, w):
    return ((v[0] + w[0]) % 3, (v[1] + w[1]) % 3)


def fmul(v, w):
    return ((v[0] * w[0] - v[1] * w[1]) % 3, (v[0] * w[1] + v[1] * w[0]) % 3)


def omega(v, w):
    return (v[0] * w[1] - v[1] * w[0]) % 3


LPOW = [(1, 0)]
for _ in range(15):
    LPOW.append(fmul(LPOW[-1], (1, 1)))


def mul(x, y):
    (v, z, j), (w, zz, l) = x, y
    w2 = fmul(LPOW[j], w)
    zz2 = zz if j % 2 == 0 else (-zz) % 3
    return (fadd(v, w2), (z + zz2 + 2 * omega(v, w2)) % 3, (j + l) % 16)


ELS = [((a, b), z, j) for a in range(3) for b in range(3) for z in range(3) for j in range(16)]
IDX = {e: n for n, e in enumerate(ELS)}
N = len(ELS)
S = [((0, 0), 0, 0), ((0, 2), 0, 9), ((2, 1), 0, 8), ((1, 2), 2, 14)]   # (a, b) means a + b i

edges = sorted({(IDX[g], N + IDX[mul(s, g)]) for g in ELS for s in S})
adj = [[] for _ in range(2 * N)]
for u, v in edges:
    adj[u].append(v)
    adj[v].append(u)
assert len(edges) == 4 * N, 'repeated edge'
assert all(len(a) == 4 for a in adj), 'not 4-regular'
diam = 0
for src in range(2 * N):
    dist = [-1] * (2 * N)
    dist[src] = 0
    q = deque([src])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if dist[w] < 0:
                dist[w] = dist[u] + 1
                q.append(w)
    assert min(dist) >= 0, 'disconnected'
    diam = max(diam, max(dist))
    assert all((dist[w] % 2) == ((w >= N) != (src >= N)) for w in range(2 * N)), 'not bipartite'
text = f'{2 * N}\n' + ''.join(f'{u} {v}\n' for u, v in edges)
print(f'n={2 * N} edges={len(edges)} 4-regular bipartite diameter={diam} sha256(edge list)='
      f'{hashlib.sha256(text.encode()).hexdigest()}')
if len(sys.argv) > 1:
    open(sys.argv[1], 'w').write(text)
print('VALID' if diam <= 7 else 'INVALID')
