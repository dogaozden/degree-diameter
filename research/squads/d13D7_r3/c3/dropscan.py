#!/usr/bin/env python3
"""Card c3 (squad round 3): single-singleton removals from the 397 configuration of the Eichler class.
Removing singleton b frees the cosets it alone blocked; total = (122 - 1) + 11 * clique.  usage: dropscan.py"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import orbl as L
import liftscan as S
from collections import Counter
idx397 = np.loadtxt(os.path.join(HERE, 'seed397_r2c6_idx.txt'), comments='#', dtype=np.int64).reshape(-1)
fixed_all = np.flatnonzero((L.P[:, 0] == 0) & ((L.P[:, 1] + 5 * L.P[:, 5]) % 11 == 0))
Sg = np.intersect1d(idx397, fixed_all)
m, k = S.base_data(Sg)
codes, T = S.all_cosets()
res = []
for b in range(len(k)):
    keep = np.ones(len(k), bool); keep[b] = False
    cand = S.candidates(m[keep], k[keep], T)
    w, cl, opt = S.clique_on(cand, 3, 0, 1, 'drop')
    res.append((w, cand.size, b, opt))
res.sort(reverse=True)
print('top single removals (clique, candidates, base, optimal):', res[:6])
print('histogram:', sorted(Counter(r[0] for r in res).items()))
print('best total after removing one singleton:', 121 + 11 * res[0][0])
