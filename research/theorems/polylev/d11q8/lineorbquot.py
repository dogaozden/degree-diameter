"""lineorbquot.py: line orbits of a cyclic collineation group of H(q) (generator given by its point permutation) and
the quotient of the concurrency graph of the lines: an orbit is admissible when no two of its lines meet; two orbits
conflict when a line of one meets a line of the other. An independent set of the quotient is a set of pairwise
disjoint hexagon lines (point classes for Corollary 5.2). Writes OUT (wmis format), OUT.keep and OUT.lorb.
Usage: python3 lineorbquot.py HEXBIN PPERM OUT"""
import sys
sys.path.insert(0, '..')
import numpy as np
from hexlib import Hex
H = Hex(sys.argv[1]); pm = np.fromfile(sys.argv[2], dtype=np.int32).astype(np.int64); out = sys.argv[3]
lm = H.line_map(pm)
lorb = -np.ones(H.L, dtype=np.int64); no = 0
for s in range(H.L):
    if lorb[s] >= 0:
        continue
    x = s
    while lorb[x] < 0:
        lorb[x] = no; x = lm[x]
    no += 1
O = lorb[H.PL]                                     # orbit of each line through each point
bad = np.zeros(no, dtype=bool); edges = set()
for row in O:
    u = np.unique(row)
    if len(u) < len(row):
        vals, cnts = np.unique(row, return_counts=True); bad[vals[cnts > 1]] = True
    for i in range(len(u)):
        for j in range(i + 1, len(u)):
            edges.add((int(u[i]), int(u[j])))
keep = [o for o in range(no) if not bad[o]]
idx = {o: i for i, o in enumerate(keep)}
size = np.bincount(lorb, minlength=no)
E = [(idx[a], idx[b]) for a, b in edges if a in idx and b in idx]
with open(out, 'w') as f:
    f.write(f'{len(keep)}\n' + ' '.join(str(int(size[o])) for o in keep) + f'\n{len(E)}\n')
    f.write('\n'.join(f'{a} {b}' for a, b in E) + '\n')
np.savetxt(out + '.keep', np.array(keep), fmt='%d'); lorb.astype(np.int32).tofile(out + '.lorb')
hist = np.bincount(size)
print(f'{no} line orbits (sizes {dict((i, int(c)) for i, c in enumerate(hist) if c)}), {len(keep)} admissible, '
      f'{len(E)} conflicts; admissible weight {int(size[keep].sum())}')
