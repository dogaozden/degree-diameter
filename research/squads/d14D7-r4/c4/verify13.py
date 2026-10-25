#!/usr/bin/env python3
# r4 c4: independent check of a flag file "point spread_line" for q = 13 (points of E13 = E13.map rows).
# Checks: each point is on E13; its spread line matches E13.map; points distinct; pairwise non-orthogonal.
import sys, numpy as np
D = '/home/user/degree-diameter/research/cell147/data/'
rows = np.loadtxt(D + 'E13.map', dtype=np.int64)
pid = rows[:, 0]; sl = rows[:, 1]; X = rows[:, 2:9] % 13
where = {int(p): i for i, p in enumerate(pid)}
bad_pt = bad_line = 0; idx = []
for line in open(sys.argv[1]):
    if not line.strip(): continue
    p, l = map(int, line.split()[:2])
    if p not in where: bad_pt += 1; continue
    i = where[p]; idx.append(i)
    if int(sl[i]) != l: bad_line += 1
n = len(idx); distinct = len(set(idx)) == n
Y = X[idx]
B = (np.outer(Y[:, 0], Y[:, 4]) + np.outer(Y[:, 4], Y[:, 0]) + np.outer(Y[:, 1], Y[:, 5]) + np.outer(Y[:, 5], Y[:, 1])
     + np.outer(Y[:, 2], Y[:, 6]) + np.outer(Y[:, 6], Y[:, 2]) - 2 * np.outer(Y[:, 3], Y[:, 3])) % 13
np.fill_diagonal(B, 1)
orth = int(np.sum(B == 0)) // 2
print(f"flags {n} off-E {bad_pt} wrong-line {bad_line} distinct {distinct} orthogonal-pairs {orth} -> {'OK' if (bad_pt == 0 and bad_line == 0 and distinct and orth == 0) else 'FAIL'}")
