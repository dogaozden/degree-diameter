#!/usr/bin/env python3
"""Lift a multi-direction line set (clq_multi output) to H(11) point indices for oppcheck (card c2).
usage: multilift.py DIRFILE LINES OUT_IDX   (LINES lines: 'i t0 t1 t2 t3 t4'; plus e4 is added)"""
import sys, os, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
code = coord @ (q ** np.arange(7))
dirs = [[int(t) for t in s.split()] for s in open(sys.argv[1]) if s.strip()]
pts = [np.array([0, 0, 0, 0, 1, 0, 0])]
nl = 0
for s in open(sys.argv[2]):
    if not s.strip() or s.startswith('#'):
        continue
    v = [int(t) for t in s.split()]
    i, t = v[0], np.array(v[1:6]) % q
    u = np.array(dirs[i]) % q
    nl += 1
    for lam in range(q):
        a, b, c, e, f = (t + lam * u) % q
        pts.append(np.array([1, a, b, c, (c * c - a * e - b * f) % q, e, f]))
idx = []
for x in pts:
    nz = np.nonzero(x)[0][0]
    x = (x * pow(int(x[nz]), q - 2, q)) % q
    k = int(x @ (q ** np.arange(7)))
    j = int(np.searchsorted(code, k))
    assert code[j] == k, 'not a point of Q(6,11)'
    idx.append(j)
idx = sorted(set(idx))
with open(sys.argv[3], 'w') as f:
    f.write(f'# {len(idx)} points from {nl} lines (+e4), directions from {sys.argv[1]}\n' + '\n'.join(map(str, idx)) + '\n')
print(f'{len(idx)} points written to {sys.argv[3]}')
