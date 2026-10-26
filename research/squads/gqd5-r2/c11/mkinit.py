# usage: mkinit.py KIND Q SEED OUTFILE [mode]
# mode 'ld': M = 2-point local duality on random non-collinear x,y (non-concurrent images), R = {x,y,z}, z random
# non-collinear with x,y. Writes "R r1 r2 r3" and "M ..." lines for sa_gen.
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import Q4, W
from localdual import local_duality_pair
kind, q, seed, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
G = Q4(q) if kind == 'Q4' else W(q)
rng = random.Random(seed)
n = G.np
while True:
    x, y = rng.sample(range(n), 2)
    if not G.col[x, y]: break
while True:
    l, m = rng.sample(range(n), 2)
    if not G.con[l, m]: break
M = local_duality_pair(G, x, y, l, m)
cands = [z for z in range(n) if z not in (x, y) and not G.col[x, z] and not G.col[y, z]]
z = rng.choice(cands)
with open(out, 'w') as f:
    f.write('R %d %d %d\n' % (x, y, z))
    f.write('M ' + ' '.join(map(str, M)) + '\n')
print('x,y,z', x, y, z, 'lines', l, m)
