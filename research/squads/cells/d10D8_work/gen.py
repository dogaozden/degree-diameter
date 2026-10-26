"""gen.py: base graphs for glift.c (own-d8-compound job, 2026-10-26).

Base vertices: points 0..N-1 (colour 0), lines N..2N-1 (colour 1) of H(q).
Families:
  lev  q m seed [phi]   : Z_m lift of H(q) + two matchings p -> phi(p) with voltages 1 and 2 on the matchings
                           (the D = 7 level graph when m = 5), zero hexagon voltages.
  T    q n seed mode     : dihedral D_n lift of H(q) with two semi-edges per element (reflections (o1,1), (o2,1));
                           mode rand: o1, o2 uniform; mode diff: o1 != o2 uniform.  Zero hexagon voltages.
  Trot q n seed          : as T rand, plus uniform random rotation voltages on the hexagon flags.
Usage: python3 gen.py FAMILY args... OUT
"""
import sys
import numpy as np
from hexlib import load


def header(f, gt, gp, N):
    f.write(f'{gt} {gp}\n{2 * N}\n')
    f.write(' '.join(['0'] * N + ['1'] * N) + '\n')


def flags(LP, N):
    L, Q1 = LP.shape
    ls = np.repeat(np.arange(L), Q1) + N
    ps = LP.reshape(-1)
    return ps, ls


def main():
    fam = sys.argv[1]
    q = int(sys.argv[2])
    N, LP, PL, coord = load(q)
    ps, ls = flags(LP, N)
    out = sys.argv[-1]
    rows = []
    if fam == 'lev':
        m, seed = int(sys.argv[3]), int(sys.argv[4])
        rng = np.random.default_rng(seed)
        phi = rng.permutation(N) + N
        for p, l in zip(ps, ls):
            rows.append((p, l, 0))
        for p in range(N):
            rows.append((p, phi[p], 1 % m))
            rows.append((p, phi[p], 2 % m))
        with open(out, 'w') as f:
            header(f, 'Z', m, N)
            for r in rows:
                f.write('%d %d %d\n' % r)
    elif fam in ('T', 'Trot'):
        n, seed, mode = int(sys.argv[3]), int(sys.argv[4]), sys.argv[5] if fam == 'T' else 'rand'
        rng = np.random.default_rng(seed)
        with open(out, 'w') as f:
            header(f, 'D', n, N)
            rot = rng.integers(0, n, len(ps)) if fam == 'Trot' else np.zeros(len(ps), dtype=int)
            for p, l, a in zip(ps, ls, rot):
                f.write('%d %d %d\n' % (p, l, a))
            for e in range(2 * N):
                o1 = rng.integers(0, n)
                o2 = rng.integers(0, n)
                if mode == 'diff':
                    while o2 == o1:
                        o2 = rng.integers(0, n)
                f.write('%d %d %d\n' % (e, e, o1 + n))
                f.write('%d %d %d\n' % (e, e, o2 + n))
    else:
        raise SystemExit('unknown family')


if __name__ == '__main__':
    main()
