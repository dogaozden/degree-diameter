"""X-type base: zero hexagon voltages, k random bijections M_j: points -> lines with shifts s_j. Usage:
python3 mk_x0.py q m seed s1,s2,... out.txt"""
import sys, numpy as np
from hexlib import load, write_base, hex_edges
q, m, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
shifts = [int(x) for x in sys.argv[4].split(',')]
out = sys.argv[5]
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
E = [hex_edges(LP)]
for s in shifts:
    M = rng.permutation(N)
    E.append(np.stack([np.arange(N), M, np.full(N, s)], axis=1))
write_base(out, N, m, np.concatenate(E))
