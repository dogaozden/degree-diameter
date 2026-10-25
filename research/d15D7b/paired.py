#!/usr/bin/env python3
"""paired.py: the elements of a relaxed set that have a partner (collinear points, mode P; concurrent lines, mode L).
usage: paired.py HEXBIN P|L SET.txt OUT.txt"""
import sys, numpy as np
hexfn, mode, sf, out = sys.argv[1:5]
b = open(hexfn, 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
PL = flat_l[np.lexsort((flat_l, flat_p))].reshape(N, Q1)
inc = LP if mode == 'P' else PL           # cell -> its elements
s = np.zeros(N, bool); s[np.loadtxt(sf, dtype=np.int64).reshape(-1)] = True
two = s[inc].sum(1) >= 2
m = inc[two].reshape(-1); m = np.unique(m[s[m]])
np.savetxt(out, m, fmt='%d'); print(f'{len(m)} paired elements')
