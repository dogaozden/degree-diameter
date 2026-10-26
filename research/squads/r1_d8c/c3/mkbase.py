"""mkbase.py: write lifteval base graph for H(q) + one matching (Delta = q+2), Z_m lift.
usage: python3 mkbase.py q m seed out [hexvolt_mode]
hexvolt_mode: zero (default) | rand. Matching: random permutation sigma, random voltages."""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
import numpy as np
from hexlib import load
q, m, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
out = sys.argv[4]
mode = sys.argv[5] if len(sys.argv) > 5 else 'zero'
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
L = LP.shape[0]
edges = []
for l in range(L):
    for p in LP[l]:
        v = 0 if mode == 'zero' else int(rng.integers(m))
        edges.append((int(p), l, v))
perm = rng.permutation(N)
for p in range(N):
    edges.append((p, int(perm[p]), int(rng.integers(m))))
with open(out, 'w') as f:
    f.write(f'{N} {N} {m}\n')
    for a, b, v in edges:
        f.write(f'{a} {b} {v}\n')
print(N, len(edges))
