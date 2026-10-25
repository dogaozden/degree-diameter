#!/usr/bin/env python3
"""Hermitian spread of H(p), p prime: the q^3+1 lines of H(p) inside n^perp, n = (1,0,0,0,c,0,0), for the first c that
gives q^3+1 lines (elliptic section).  usage: hspread.py HEXFILE OUT_IDX"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); import hexlib
q, lines, coord = hexlib.load(sys.argv[1])
for c in range(1, q):
    n = np.array([1, 0, 0, 0, c, 0, 0])
    inp = hexlib.bilinear(coord, n[None, :], q) == 0
    sp = np.nonzero(inp[lines].all(axis=1))[0]
    if len(sp) == q ** 3 + 1:
        open(sys.argv[2], 'w').write(f'# {len(sp)} lines of H({q}) inside n^perp, n = {n.tolist()}\n' + '\n'.join(map(str, sp.tolist())) + '\n')
        print(f'q={q} c={c}: {len(sp)} lines -> {sys.argv[2]}'); break
