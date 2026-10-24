"""(2k+1)-copy version: copies Z_(2k+1) of the incidence graph of H(q), cross edges (p, c) ~ (phi(p), c+t) for
t = 1..k, phi a perfect matching of Gamma. Max degree q+1+k, diameter 7 (same first/last-step proof).
usage: python3 kcopy.py q k OUT.edges"""
import sys
from hexagon import build
from threecopy import perfect_matching
q, k = int(sys.argv[1]), int(sys.argv[2])
P, pl, lp = build(q)
M = perfect_matching(P, lp, pl)
m = 2 * k + 1
E = []
for c in range(m):
    base = c * 2 * P
    for l, ln in enumerate(pl):
        for p in ln:
            E.append((base + p, base + P + l))
    for t in range(1, k + 1):
        nb = ((c + t) % m) * 2 * P
        for p in range(P):
            E.append((base + p, nb + P + M[p]))
with open(sys.argv[3], 'w') as f:
    f.write('%d\n' % (m * 2 * P))
    f.write(''.join('%d %d\n' % e for e in E))
print('n=%d edges=%d copies=%d max degree %d' % (m * 2 * P, len(E), m, q + 1 + k))
