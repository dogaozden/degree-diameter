import sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import Q4
G = Q4(5)
n, m = G.np, G.nl
out = open('/home/user/degree-diameter/research/squads/gqd5-r1/c4/q45.txt', 'w')
out.write(f"{n} {m}\n")
# lines: 6 points each
for l in range(m):
    out.write(' '.join(map(str, G.lines[l])) + '\n')
# col: 30 points each, con: 30 lines each
for p in range(n):
    c = np.nonzero(G.col[p])[0]
    out.write(str(len(c)) + ' ' + ' '.join(map(str, c)) + '\n')
for l in range(m):
    c = np.nonzero(G.con[l])[0]
    out.write(str(len(c)) + ' ' + ' '.join(map(str, c)) + '\n')
out.close()
print(n, m, G.s, G.t, G.col.sum(1)[:3], G.con.sum(1)[:3])
