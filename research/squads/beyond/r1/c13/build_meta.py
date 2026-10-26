import sys, itertools
# Independent builder for Haar graph H(G,S), G = Z_m x| Z_n with (a,b)(c,d) = (a + r^b c mod m, b+d mod n).
# usage: build_meta.py m n r "a1,b1;a2,b2;a3,b3;a4,b4" out.edges
m, n, r = map(int, sys.argv[1:4])
S = [tuple(map(int, p.split(','))) for p in sys.argv[4].split(';')]
out = sys.argv[5]
assert pow(r, n, m) == 1 % m, "r^n != 1 mod m"
def mul(x, y):
    a, b = x; c, d = y
    return ((a + pow(r, b, m) * c) % m, (b + d) % n)
G = [(a, b) for a in range(m) for b in range(n)]
idx = {g: i for i, g in enumerate(G)}
N = len(G)
# associativity spot check
import random
for _ in range(2000):
    x, y, z = (random.choice(G) for _ in range(3))
    assert mul(mul(x, y), z) == mul(x, mul(y, z))
edges = []
for g in G:
    for s in S:
        h = mul(g, s)
        edges.append((idx[g], N + idx[h]))
# check the 4 neighbours of each vertex are distinct and no duplicate edges
assert len(set(edges)) == len(edges) == 4 * N
with open(out, 'w') as f:
    f.write(f"{2*N}\n")
    for u, v in edges:
        f.write(f"{u} {v}\n")
print("wrote", out, "vertices", 2*N, "edges", len(edges))
