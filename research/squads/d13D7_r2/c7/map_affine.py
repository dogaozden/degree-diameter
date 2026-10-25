#!/usr/bin/env python3
"""Map affine points (a b c e f) of the fiber-line search to H(11) point indices (plus e4) for oppcheck.
usage: map_affine.py AFFINE_FILE OUT_IDX"""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import numpy as np
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
code = coord @ (q ** np.arange(7))
assert np.all(np.diff(code) > 0)
def index_of(x):
    x = [int(t) % q for t in x]
    nz = next(i for i, t in enumerate(x) if t)
    inv = pow(x[nz], q - 2, q)
    x = [(t * inv) % q for t in x]
    k = sum(t * q ** i for i, t in enumerate(x))
    j = int(np.searchsorted(code, k))
    assert j < len(code) and code[j] == k, ('not a point', x)
    return j
pts = [index_of([0, 0, 0, 0, 1, 0, 0])]  # e4, opposite every affine point
rows = []
for s in open(sys.argv[1]):
    s = s.strip()
    if not s or s.startswith('#'):
        continue
    a, b, c, e, f = (int(t) % q for t in s.split())
    rows.append((a, b, c, e, f))
    pts.append(index_of([1, a, b, c, (c * c - a * e - b * f) % q, e, f]))
pts = sorted(set(pts))
with open(sys.argv[2], 'w') as g:
    g.write(f'# {len(pts)} points (e4 + {len(rows)} affine points), mapped from {sys.argv[1]}\n')
    g.write('\n'.join(map(str, pts)) + '\n')
print(len(pts), 'points written to', sys.argv[2])
