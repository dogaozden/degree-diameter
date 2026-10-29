#!/usr/bin/env python3
"""Best type patterns for the typed level layouts (D7_HEXAGON.md Section 6) with given freed-set sizes.
Levels j in Z_L (L = 2r+1), transitions j -> j+k (1 <= k <= r). A friendly transition (types differ) frees R_H points
(source H) or R_L lines (source D); a non-friendly one frees m elements. alpha_j / beta_j = free slots out of / into
level j; hubs per side <= min alpha (line-side) and min beta (point-side).
usage: patterns.py L RH RL m"""
import sys, itertools
L, RH, RL, m = (int(a) for a in sys.argv[1:5])
r = (L - 1) // 2
best = []
for T in itertools.product('HD', repeat=L):
    if T[0] != 'H':
        continue
    al = [0] * L; be = [0] * L
    for j in range(L):
        for k in range(1, r + 1):
            j2 = (j + k) % L
            f = (RH if T[j] == 'H' else RL) if T[j] != T[j2] else m
            al[j] += f; be[j2] += f
    best.append((min(al) + min(be), min(al), min(be), ''.join(T), al, be))
best.sort(reverse=True)
for b in best[:6]:
    print(b[0], b[1], b[2], b[3], b[4], b[5])
