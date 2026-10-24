"""H(q) * C_m (Delorme-style star product with rotations): vertices (v, k), hexagon edges (p,k)~(l,k+phi(p,l)) with phi
even, cycle edges (v,k)~(v,k+-1). Lift colouring col = side(v) + k (MIX = 1). phi modes:
  rand: phi uniform even;  zero: phi = 0.
python3 mk_star.py q m seed mode out"""
import sys, numpy as np
from hexlib import load, hex_edges
q, m, seed, mode, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
H = hex_edges(LP)
if mode == 'rand':
    H[:, 2] = 2 * rng.integers(0, m // 2, len(H))
H[:, 1] += N  # lines are base vertices N..2N-1
loops = np.stack([np.arange(2 * N), np.arange(2 * N), np.ones(2 * N, dtype=np.int64)], axis=1)
with open(out, 'w') as f:
    f.write(f'{2 * N} {m} 1\n')
    f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
    np.savetxt(f, np.concatenate([H, loops]) % [2 * N + 1, 2 * N + 1, m], fmt='%d')
