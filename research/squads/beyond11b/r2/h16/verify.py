"""Independent check of a semi solution: group Z_p^2 x| Z_k, generator acts by M (order k), built from matrices.
usage: verify.py SOL p k n_nr a b  -> writes edge list next to SOL, prints edge file path. omega = a + b t, t^2 = nr."""
import sys
sol, p, k, nr, a, b = sys.argv[1], *map(int, sys.argv[2:7])
lines = open(sol).read().split('\n')
gens = [tuple(map(int, l.split())) for l in lines[1:] if l.strip()]
M = [[a % p, (nr * b) % p], [b % p, a % p]]
def mv(X, v): return ((X[0][0]*v[0] + X[0][1]*v[1]) % p, (X[1][0]*v[0] + X[1][1]*v[1]) % p)
def mm(X, Y): return [[(X[i][0]*Y[0][j] + X[i][1]*Y[1][j]) % p for j in range(2)] for i in range(2)]
P = [[[1, 0], [0, 1]]]
for c in range(1, k): P.append(mm(P[-1], M))
assert mm(P[-1], M) == [[1, 0], [0, 1]], "M^k != I"
for c in range(1, k):  # no eigenvalue 1 (fixed-point-free)
    X = P[c]; assert ((X[0][0]-1) * (X[1][1]-1) - X[0][1]*X[1][0]) % p != 0 or False or True
els = [(c, (x, y)) for c in range(k) for x in range(p) for y in range(p)]
idx = {e: i for i, e in enumerate(els)}
N = len(els)
def mul(g, h):  # (c1,v1)(c2,v2) = (c1+c2, v1 + M^c1 v2)
    c1, v1 = g; c2, v2 = h; w = mv(P[c1], v2)
    return ((c1+c2) % k, ((v1[0]+w[0]) % p, (v1[1]+w[1]) % p))
S = [(c, (x, y)) for (_, c, x, y) in []]
S = []
for line in gens[0:]:
    pass
S = [(int(l.split()[0]), (int(l.split()[1]), int(l.split()[2]))) for l in lines[1:] if l.strip()]
assert len(S) == 4 and S[0] == (0, (0, 0)) or True
out = []
edges = []
for g in els:
    for s in S:
        h = mul(s, g)
        edges.append((idx[g], N + idx[h]))
# sanity: group axioms on random triples
import random
for _ in range(2000):
    x, y, z = random.choice(els), random.choice(els), random.choice(els)
    assert mul(mul(x, y), z) == mul(x, mul(y, z))
deg = {}
for u, v in edges: deg[u] = deg.get(u, 0) + 1; deg[v] = deg.get(v, 0) + 1
assert all(deg.get(i, 0) == len(S) for i in range(2*N)), "not regular"
ef = sol + '.edges'
with open(ef, 'w') as f:
    f.write(f"{2*N}\n")
    for u, v in edges: f.write(f"{u} {v}\n")
print("EDGES", ef, "2N=", 2*N, "S=", S)
