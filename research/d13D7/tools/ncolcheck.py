#!/usr/bin/env python3
"""Check that a point set of H(q) is pairwise NON-COLLINEAR (no line of the hexagon file holds two of its points).
usage: ncolcheck.py HEXFILE FILE   -> RESULT VALID noncollinear m"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); import hexlib
q, lines, coord = hexlib.load(sys.argv[1]); N = len(coord)
R = [int(s.split()[0]) for s in open(sys.argv[2]) if s.strip() and not s.startswith('#')]
ok = len(R) == len(set(R)) and all(0 <= r < N for r in R)
inR = np.zeros(N, bool); inR[R] = True
per_line = inR[lines].sum(axis=1)
bad = int((per_line > 1).sum())
print(f'{len(R)} points, {bad} lines with two or more of them')
print(f'RESULT {"VALID" if ok and bad == 0 else "INVALID"} noncollinear {len(R)}')
