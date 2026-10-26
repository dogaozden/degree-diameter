# usage: mkgraph.py KIND Q OUTFILE   (KIND = Q4 or W); writes graph file: n m / lines / col lists / con lists
import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import Q4, W
kind, q, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
t = time.time()
G = Q4(q) if kind == 'Q4' else W(q)
G.check()
n, m = G.np, G.nl
assert n == m
with open(out, 'w') as f:
    f.write(f"{n} {m}\n")
    for l in range(m):
        f.write(' '.join(map(str, G.lines[l])) + '\n')
    for p in range(n):
        c = np.nonzero(G.col[p])[0]
        f.write(str(len(c)) + ' ' + ' '.join(map(str, c)) + '\n')
    for l in range(m):
        c = np.nonzero(G.con[l])[0]
        f.write(str(len(c)) + ' ' + ' '.join(map(str, c)) + '\n')
print(G.name, n, m, 'order', (G.s, G.t), 'built in %.1fs' % (time.time() - t))
