"""c6: H(q) + k extra matchings (perfect matchings points->lines, one per matching), cyclic lift Z_m.
Usage: python3 mk_c6.py q m seed k hmode out.txt [dummy]
  hmode 0: zero hexagon voltages; 1: uniform random hexagon voltages in Z_m.
Extra voltages: uniform random in Z_m (unless overridden by a structured generator importing build()).
"""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, write_base, hex_edges


def build(q, m, seed, k, hmode, rng=None, extra_volt=None, hex_volt=None, matchings=None):
    N, LP, PL, coord = load(q)
    if rng is None:
        rng = np.random.default_rng(seed)
    if hex_volt is None:
        hv = rng.integers(0, m, size=(N, q + 1)) if hmode == 1 else np.zeros((N, q + 1), dtype=np.int64)
    else:
        hv = hex_volt
    E = [hex_edges(LP, hv)]
    Ms = []
    for j in range(k):
        if matchings is not None:
            M = matchings[j]
        else:
            M = rng.permutation(N)
        Ms.append(M)
        if extra_volt is None:
            vv = rng.integers(0, m, N)
        else:
            vv = extra_volt[j]
        E.append(np.stack([np.arange(N), M, vv], axis=1))
    return N, LP, PL, np.concatenate(E), Ms


if __name__ == '__main__':
    q, m, seed, k, hmode, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    N, LP, PL, E, Ms = build(q, m, seed, k, hmode)
    write_base(out, N, m, E)
    print('wrote', out, 'N', N, 'edges', len(E))
