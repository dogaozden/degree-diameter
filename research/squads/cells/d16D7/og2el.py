#!/usr/bin/env python3
"""og2el.py GRAPH PERM.bin SOL OUT: expand an orbit-graph solution (one vertex index per line) into the element list
(all members of each orbit: rep, g(rep), g(g(rep)), ...) for typed5s make. GRAPH: og_pts.txt / og_lines.txt
("M E", then "idx rep deg nbrs..."); PERM.bin: int32 permutation of the elements (g13o61_pts.bin / _lines.bin)."""
import sys
import numpy as np
g, permf, solf, outf = sys.argv[1:5]
rep = {}
with open(g) as f:
    f.readline()
    for line in f:
        a = line.split(None, 3)
        rep[int(a[0])] = int(a[1])
perm = np.fromfile(permf, dtype=np.int32)
out = []
for line in open(solf):
    line = line.strip()
    if not line or line.startswith('#'):
        continue
    x = rep[int(line)]
    y = x
    while True:
        out.append(y)
        y = int(perm[y])
        if y == x:
            break
with open(outf, 'w') as f:
    f.write('# %d elements from %s\n' % (len(out), solf))
    f.write('\n'.join(map(str, sorted(out))) + '\n')
print(len(out), 'elements')
