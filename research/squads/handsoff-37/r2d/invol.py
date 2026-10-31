# r2d/invol.py: list colour-preserving involutions of C168.1 (from c5/out/aut168.txt) and their fixed structure.
import sys
from collections import Counter
n = 168; m = 84
perms = []
for line in open(sys.argv[1]):
    p = list(map(int, line.split()))
    if len(p) == n: perms.append(p)
def ident(p): return all(p[i] == i for i in range(n))
def order(p):
    q = p[:]; k = 1
    while not all(q[i] == i for i in range(n)):
        q = [p[x] for x in q]; k += 1
    return k
res = []
for p in perms:
    if ident(p): continue
    if order(p) != 2: continue
    colour = all((p[x] < m) == (x < m) for x in range(n))
    fixed_v = [x for x in range(n) if p[x] == x]
    fixed_e = [(x, y) for x in range(n) for y in range(x + 1, n) if p[x] == y and p[y] == x]
    # neighbours info below uses the edge list
    res.append((colour, len(fixed_v), len(fixed_e), p))
print('involutions', len(res), 'colour-preserving', sum(1 for r in res if r[0]))
print(Counter((r[0], r[1], r[2]) for r in res))
import pickle
pickle.dump([r for r in res if r[0]], open('/home/user/degree-diameter/research/squads/handsoff-37/r2d/out/c168_colour_invols.pkl', 'wb'))
