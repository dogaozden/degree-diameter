#!/usr/bin/env python3
"""meta2edges.py SOL OUT.edges: edge list of a Haar graph of a metacyclic group from a haar_gen3 solution file
("d D meta m k r n 1 N .." then lines "<idx> meta(a=A,j=J) z=0"). Own group code: G = Z_m x|_r Z_k with
(a,j)(b,l) = (a + r^j b mod m, j + l mod k), r^k = 1 mod m. Vertices (g,A) = g, (g,B) = N + g, g = a*k + j;
edges (g,A) ~ (s g, B). Checks r^k = 1, the identity, associativity on random triples, distinct generators."""
import sys, re, numpy as np
lines = open(sys.argv[1]).read().split('\n')
h = lines[0].split(); d, D = int(h[0]), int(h[1]); assert h[2] == 'meta'
m, k, r = int(h[3]), int(h[4]), int(h[5]); assert h[6] == 'n' and h[7] == '1'
N = m * k; assert pow(r, k, m) == 1 % m
R = [pow(r, j, m) for j in range(k)]
S = []
for L in lines[1:1 + d]:
    a, j = map(int, re.search(r'meta\(a=(\d+),j=(\d+)\)', L).groups()); S.append((a % m, j % k))
assert len(set(S)) == d, "generators not distinct"
def mul(x, y): return ((x[0] + R[x[1]] * y[0]) % m, (x[1] + y[1]) % k)
rng = np.random.default_rng(2)
for _ in range(20000):
    x, y, z = [(int(rng.integers(m)), int(rng.integers(k))) for _ in range(3)]
    assert mul(mul(x, y), z) == mul(x, mul(y, z))
a = np.repeat(np.arange(m), k); j = np.tile(np.arange(k), m)      # g = a*k + j
with open(sys.argv[2], 'w') as o:
    o.write(f"{2 * N}\n")
    for (sa, sj) in S:
        na = (sa + R[sj] * a) % m; nj = (sj + j) % k
        tgt = na * k + nj
        assert len(np.unique(tgt)) == N
        o.write(''.join(f"{g} {N + t}\n" for g, t in zip(range(N), tgt.tolist())))
print(f"meta {m} {k} {r}: N={N}, {d} generators {S}; wrote {2*N} vertices, {d*N} edges")
