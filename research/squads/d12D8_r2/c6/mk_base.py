"""Build affine-lift base for bipartite degree-(q+3) lifts. Base = incidence graph of H(q) (4 edges/vertex at q=3)
plus extra edges. Writes affcheck format: "NP NL m aff" then "p l a b" per edge.
usage: mk_base.py q m seed out [mode]
  mode 'rand'  : all base edges get random affine labels (a unit mod m, b random); extra edges = 2 random perfect matchings
  mode 'dl'    : Delorme-like: incidence edges label mu (colour 0) or mu^-1; extras = colour 0 (x+1, x-1)"""
import sys, os, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools')
from hexlib import load_hex
q, m, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
random.seed(seed)
n, lines = load_hex(q)
units = [a for a in range(1, m) if np.gcd(a, m) == 1] if m > 1 else [0]
E = []  # (p, l)
for l in range(n):
    for k in range(q + 1):
        E.append((int(lines[l][k]), l))
# two extra random perfect matchings
for _ in range(2):
    P = list(range(n)); random.shuffle(P)
    for p in range(n):
        E.append((p, P[p]))
with open(out, 'w') as f:
    f.write(f"{n} {n} {m} aff\n")
    for (p, l) in E:
        a = random.choice(units); b = random.randrange(m)
        f.write(f"{p} {l} {a} {b}\n")
