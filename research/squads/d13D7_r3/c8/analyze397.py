import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
idx = [int(l) for l in open('/home/user/degree-diameter/research/squads/d13D7_r2/c6/best_idx.txt') if l.strip() and not l.startswith('#')]
P = coord[idx]
print('size', len(idx), 'distinct', len(set(idx)))
x0 = P[:, 0]
print('x0 counts: x0=0 (infinity):', int((x0 == 0).sum()), ' x0=1 (affine):', int((x0 == 1).sum()))
e4 = np.array([0, 0, 0, 0, 1, 0, 0])
print('contains e4:', any((P == e4).all(axis=1)))
inf = P[x0 == 0]
print('points at infinity:')
for r in inf: print('  ', r.tolist())
# affine coords
A = P[x0 == 1]
print('affine count', len(A))
# check direction structure: for each affine point, the fibre under u=(1,0,0,9,0) in (a,b,c,e,f)
u = np.array([1, 0, 0, 9, 0])
# affine (a,b,c,e,f) = (x1,x2,x3,x5,x6)
T = np.stack([A[:, 1], A[:, 2], A[:, 3], A[:, 5], A[:, 6]], axis=1)
# quotient by <u>: canonical key: move each point along u to make a=0 (a + lam*1 => lam = -a)
def key(t):
    a, b, c, e, f = t
    lam = (-a) % q
    t2 = (t + lam * u) % q
    return tuple(t2)
keys = {}
for t in T:
    keys.setdefault(key(t), []).append(tuple(t))
sizes = [len(v) for v in keys.values()]
from collections import Counter
print('fibres (by direction u) occupied:', len(keys), 'size histogram:', Counter(sizes))
