"""orbquot.py: quotient of the collinearity graph of H(q) by a partition of the points into orbits (file: int32 orbit id
per point). Orbits containing two collinear points are dropped; two orbits conflict when a line of H(q) meets both.
Writes the weighted graph for wmis.c (weights = orbit sizes) and the list of kept orbit ids.
Usage: python3 orbquot.py HEXBIN PORB OUT"""
import sys
sys.path.insert(0, '..')
import numpy as np
from hexlib import Hex
H = Hex(sys.argv[1]); porb = np.fromfile(sys.argv[2], dtype=np.int32).astype(np.int64); out = sys.argv[3]
no = porb.max() + 1
O = porb[H.lines]                                  # orbit of each point of each line
bad = np.zeros(no, dtype=bool)
edges = set()
for row in O:
    u = np.unique(row)
    if len(u) < len(row):
        vals, cnts = np.unique(row, return_counts=True); bad[vals[cnts > 1]] = True
    for i in range(len(u)):
        for j in range(i + 1, len(u)):
            edges.add((int(u[i]), int(u[j])))
keep = [o for o in range(no) if not bad[o]]
idx = {o: i for i, o in enumerate(keep)}
size = np.bincount(porb, minlength=no)
E = [(idx[a], idx[b]) for a, b in edges if a in idx and b in idx]
with open(out, 'w') as f:
    f.write(f'{len(keep)}\n' + ' '.join(str(int(size[o])) for o in keep) + f'\n{len(E)}\n')
    f.write('\n'.join(f'{a} {b}' for a, b in E) + '\n')
np.savetxt(out + '.keep', np.array(keep), fmt='%d')
print(f'{no} orbits, {len(keep)} admissible, {len(E)} conflicts; admissible weight {int(size[keep].sum())}')
