"""Simple (no parallel edges) 6-regular bipartite base for affine lifts at q: H(q) incidence graph plus (q+3-(q+1)) = 2
random perfect matchings avoiding incidences and each other. Random initial labels (a unit mod m, b random).
Writes affcheck format "NP NL m aff" + "p l a b" lines. usage: mk_simple_base.py q m seed out"""
import sys, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools')
from hexlib import load_hex
q, m, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed)
n, lines = load_hex(q)
forb = [set() for _ in range(n)]
E = []
for l in range(n):
    for k in range(q + 1):
        p = int(lines[l][k]); E.append((p, l)); forb[p].add(l)
for _ in range(2):
    while True:
        P = list(range(n)); rng.shuffle(P)
        if all(P[p] not in forb[p] for p in range(n)): break
    for p in range(n):
        forb[p].add(P[p]); E.append((p, P[p]))
units = [a for a in range(1, m) if np.gcd(a, m) == 1]
with open(out, 'w') as f:
    f.write(f"{n} {n} {m} aff\n")
    for (p, l) in E:
        f.write(f"{p} {l} {rng.choice(units)} {rng.randrange(m)}\n")
