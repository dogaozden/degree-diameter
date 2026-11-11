#!/usr/bin/env python3
"""mk_edges.py SOL OUT.edges: edge list of Haar graph H(G,S), G = Z_m x|_r Z_k (x Z_n), from a hmeta/haar_gen3 solution
file. Group product written directly here: (a,j)(b,l) = (a + r^j b mod m, j + l mod k); vertex (g,A)=g, (g,B)=N+g,
edges (g,A) ~ (s g, B). Output for apsp."""
import sys, re
L = open(sys.argv[1]).read().split('\n'); h = L[0].split()
d = int(h[0]); m, k, r = int(h[3]), int(h[4]), int(h[5]); i = h.index('n'); n = int(h[i + 1]); assert n == 1
N = m * k
S = []
for line in L[1:1 + d]:
    a, j = map(int, re.search(r'meta\(a=(\d+),j=(\d+)\)', line).groups()); S.append((a, j))
assert pow(r, k, m) == 1 % m
rp = [pow(r, j, m) for j in range(k)]
def idx(a, j): return a * k + j
with open(sys.argv[2], 'w') as o:
    o.write(f"{2 * N}\n")
    for s in S:
        for a in range(m):
            for j in range(k):
                # s * g with g=(a,j): (sa + r^sj * a, sj + j)
                ga = (s[0] + rp[s[1]] * a) % m; gj = (s[1] + j) % k
                o.write(f"{idx(a, j)} {N + idx(ga, gj)}\n")
print("wrote", 2 * N, "vertices", d * N, "edges")
