#!/usr/bin/env python3
# checkperm.py KIND: verifies the data assumptions for the orbit graph of KIND (pts|lines).
import sys, numpy as np
kind = sys.argv[1]
BASE = '/home/user/degree-diameter/research/squads/d16D7_r2/'
g = np.fromfile(BASE + f'data/g13o61_{kind}.bin', dtype='<i4').astype(np.int64)
h = np.fromfile(BASE + f'data/g13o183_{kind}.bin', dtype='<i4').astype(np.int64)
N = len(g)
print('N', N, 'perm g', np.array_equal(np.sort(g), np.arange(N)), 'perm h', np.array_equal(np.sort(h), np.arange(N)))
print('h g == g h:', np.array_equal(h[g], g[h]))
# order of g and h
def power(p, k):
    r = np.arange(N)
    b = p.copy()
    while k:
        if k & 1: r = b[r]
        b = b[b]; k >>= 1
    return r
print('g^61 = id:', np.array_equal(power(g, 61), np.arange(N)))
print('h^183 = id:', np.array_equal(power(h, 183), np.arange(N)))
h3 = power(h, 3)
ks = [k for k in range(61) if np.array_equal(h3, power(g, k))]
print('h^3 in <g> with exponent', ks)
# g-orbit sizes
p = g.tolist(); seen = bytearray(N); sizes = {}
for s in range(N):
    if seen[s]: continue
    c = 0; x = s
    while not seen[x]:
        seen[x] = 1; c += 1; x = p[x]
    sizes[c] = sizes.get(c, 0) + 1
print('g orbit size histogram', sizes)
