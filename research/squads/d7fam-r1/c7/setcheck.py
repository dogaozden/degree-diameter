#!/usr/bin/env python3
"""setcheck.py HEXBIN P|L FILE [DEFECT]: size and validity of a freed set of H(q).
P: FILE = point ids; valid iff no two points are collinear (DEFECT=1: every point collinear with at most one other).
L: FILE = line ids; valid iff no two lines meet (DEFECT=1: every line meets at most one other).
Prints one line: 'size S valid True|False pairs K'."""
import sys, numpy as np
b = open(sys.argv[1], 'rb').read(); kind = sys.argv[2]; ids = np.loadtxt(sys.argv[3], dtype=np.int64, comments='#').reshape(-1)
dfc = int(sys.argv[4]) if len(sys.argv) > 4 else 0
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
fp = LP.reshape(-1); fl = np.repeat(np.arange(Lc), Q1); o = np.lexsort((fl, fp)); PL = fl[o].reshape(N, Q1)
s = np.zeros(N, bool); s[ids] = True
ok = len(np.unique(ids)) == len(ids) and ids.min() >= 0 and ids.max() < N
inc = LP if kind == 'P' else PL            # for each line (P) / point (L): the elements of this kind on it
c = s[inc].sum(1)
pairs = int((c == 2).sum())
if dfc == 0: ok = ok and c.max() <= 1
else:
    deg = np.zeros(N, np.int64)
    for r in np.nonzero(c == 2)[0]:
        m = inc[r][s[inc[r]]]; deg[m] += 1
    ok = ok and c.max() <= 2 and deg.max() <= 1
print(f'size {len(ids)} valid {bool(ok)} pairs {pairs}')
