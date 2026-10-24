#!/usr/bin/env python3
"""Lift a clique K of the coset graph (offset file: 'a b c e f' per line, or '0 b c s f' with a=0, e=s) to a set R of
points of H(11) for oppcheck:  R = 11 points per coset line (e4 dropped) + one point at infinity per direction d of E
such that some offset z is not hit by n_d . K (x = dir_point(n_d, z)).  Prints |R| and writes the index file.
usage: lift_cov.py OFFSETS OUT_IDX [OUT_COORDS]"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from common import *
def read_offsets(path):
    V = []
    for line in open(path):
        t = line.split()
        if not t or t[0].startswith('#'): continue
        a, b, c, e, f = [int(z) for z in t[:5]]
        V.append((((e + 2 * a) % Q), b % Q, c % Q, f % Q))
    return sorted(set(V))
def build(V, D):
    pts = []
    for v in V:
        pts += coset_lift_points(*v)
    free = []
    for n in D:
        vals = {int((n[0]*s + n[1]*b + n[2]*c + n[3]*f) % Q) for (s, b, c, f) in V}
        z = [z for z in range(Q) if z not in vals]
        if z:
            pts.append(dir_point(n, z[0]))
            free.append(tuple(n))
    return pts, free
if __name__ == '__main__':
    V = read_offsets(sys.argv[1])
    coord, code = load_hex()
    D = directions()
    pts, free = build(V, D)
    idx = sorted({point_index(code, x) for x in pts})
    assert len(idx) == len(pts), 'duplicate points'
    with open(sys.argv[2], 'w') as f:
        f.write(f'# {len(idx)} points: {len(V)} cosets (11 points each, e4 dropped) + {len(free)} points at infinity\n')
        f.write('\n'.join(map(str, idx)) + '\n')
    if len(sys.argv) > 3:
        with open(sys.argv[3], 'w') as f:
            for j in idx: f.write(' '.join(map(str, coord[j].tolist())) + '\n')
    print(f'{len(V)} cosets, {11*len(V)} line points + {len(free)} infinity points = {len(idx)} written to {sys.argv[2]}')
