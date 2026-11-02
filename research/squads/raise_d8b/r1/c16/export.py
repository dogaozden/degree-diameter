# export a 2+2 / Haar SL(2,p) voltage lift solution (from lift2) as an edge list for apsp.c
# usage: python3 -I export.py SOL OUT_EDGES
import sys
sol, out = sys.argv[1], sys.argv[2]
hdr = open(sol).readline().split()
m = int(hdr[1].split('=')[1]); k = int(hdr[2].split('=')[1]); p = int(hdr[3].split('=')[1])
V = {}
for line in open(sol):
    if line.startswith('V '):
        f = list(map(int, line.split()[1:]))
        V.setdefault((f[0], f[1]), []).append(tuple(f[2:6]))
els = []
idx = {}
for a in range(p):
    for b in range(p):
        for c in range(p):
            for d in range(p):
                if (a * d - b * c) % p == 1:
                    idx[(a, b, c, d)] = len(els); els.append((a, b, c, d))
G = len(els)
def mul(x, y):
    a, b, c, d = x; e, f, g, h = y
    return ((a*e+b*g) % p, (a*f+b*h) % p, (c*e+d*g) % p, (c*f+d*h) % p)
n = 2 * m * G
edges = []
for (i, j), vs in V.items():
    for v in vs:
        for gi, g in enumerate(els):
            u = i * G + gi
            w = (m + j) * G + idx[mul(g, v)]
            edges.append((u, w))
# simple check of distinct edges
with open(out, 'w') as fo:
    fo.write(f"{n}\n")
    for u, w in edges:
        fo.write(f"{u} {w}\n")
print("n", n, "edges", len(edges), "degree", 2*len(edges)/n)
