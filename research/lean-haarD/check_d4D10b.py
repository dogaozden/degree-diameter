# Independent check of the (4,10) record on 12416 vertices, from the sol file only.
# Haar graph of G = Z_97 x|_19 Z_64 with S from the sol file: inl g ~ inr h iff h * g^-1 in S.
# Right multiplication by G is an automorphism, so the diameter is max(ecc(inl 1), ecc(inr 1)).
from collections import deque
import sys

SOL = "/home/user/degree-diameter/research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt"
m, k, r = 97, 64, 19
S = []
for ln in open(SOL):
    ln = ln.strip()
    if ln.startswith("group "):
        assert ln.split() == ["group", "meta", "97", "64", "19"], ln
    if ln.startswith("e 0 1 = "):
        a, j = ln[len("e 0 1 = "):].split(",")
        S.append((int(a), int(j)))
assert len(S) == 4 and len(set(S)) == 4
assert pow(r, k, m) == 1

def mul(x, y):
    return ((x[0] + pow(r, x[1], m) * y[0]) % m, (x[1] + y[1]) % k)

def inv(x):
    l = (-x[1]) % k
    return ((-pow(r, l, m) * x[0]) % m, l)

N = m * k
els = [(a, j) for a in range(m) for j in range(k)]
idx = {g: i for i, g in enumerate(els)}
# vertices: A-side index i (g = els[i]) and B-side index N + i (h = els[i])
adj = [[] for _ in range(2 * N)]
for g in els:
    for s in S:
        h = mul(s, g)                      # inl g ~ inr (s g), since (s g) g^-1 = s
        adj[idx[g]].append(N + idx[h])
        adj[N + idx[h]].append(idx[g])
assert all(len(a) == 4 for a in adj), "degree"
# bipartite by construction (edges only between A and B); check no duplicate neighbours
assert all(len(set(a)) == 4 for a in adj)

def ecc(src):
    dist = [-1] * (2 * N)
    dist[src] = 0
    q = deque([src])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if dist[v] < 0:
                dist[v] = dist[u] + 1
                q.append(v)
    assert min(dist) >= 0, "disconnected"
    return max(dist)

eA, eB = ecc(idx[(0, 0)]), ecc(N + idx[(0, 0)])
print("vertices", 2 * N, "degree 4 bipartite; ecc A", eA, "ecc B", eB, "diameter", max(eA, eB))
sys.exit(0 if max(eA, eB) <= 10 else 1)
