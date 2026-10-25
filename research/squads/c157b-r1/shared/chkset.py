#!/usr/bin/env python3
"""chkset.py: scorer for the cell-15-7 squad. Checks a set of points (mode P: no two on a common line of H(11),
i.e. a partial distance-2 ovoid) or of lines (mode L: no two through a common point) and prints the size.
usage: python3 chkset.py P|L SET.txt [HEXBIN]     (SET: ids 0..177155, one per line; prints 'VALID P 8645' or 'INVALID ...')"""
import sys, os, numpy as np
mode, fn = sys.argv[1], sys.argv[2]
hexfn = sys.argv[3] if len(sys.argv) > 3 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'hex_q11.bin')
b = open(hexfn, 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
PL = flat_l[np.lexsort((flat_l, flat_p))].reshape(N, Q1)
ids = np.loadtxt(fn, dtype=np.int64).reshape(-1)
if len(ids) == 0 or ids.min() < 0 or ids.max() >= N or len(np.unique(ids)) != len(ids):
    print('INVALID ids out of range or repeated'); sys.exit(1)
s = np.zeros(N, bool); s[ids] = True
cells = LP if mode == 'P' else PL          # P: every line has <= 1 chosen point; L: every point <= 1 chosen line
bad = int((s[cells].sum(1) > 1).sum())
if bad: print(f'INVALID {mode} {len(ids)} ({bad} {"lines" if mode == "P" else "points"} with two or more)'); sys.exit(1)
print(f'VALID {mode} {len(ids)}')
