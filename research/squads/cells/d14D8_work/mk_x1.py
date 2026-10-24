"""H(q) + k random matchings, zero hexagon voltages, random extra voltages psi_j(p) uniform in Z_m.
python3 mk_x1.py q m seed k out"""
import sys, numpy as np
from hexlib import load, write_base, hex_edges
q, m, seed, k, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
E = [hex_edges(LP)]
for j in range(k):
    M = rng.permutation(N)
    E.append(np.stack([np.arange(N), M, rng.integers(0, m, N)], axis=1))
write_base(out, N, m, np.concatenate(E))
