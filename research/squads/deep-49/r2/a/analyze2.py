"""Missed elements (side, order, class) of the given cost-4 hit files of SL(2,5) x F21."""
import sys, collections
import numpy as np
TAB = '/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/SL25x_C7C3.tab'
f = open(TAB, 'rb'); N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
MT = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N).astype(np.int64); f.close()
INV = np.array([int(np.where(MT[a] == 0)[0][0]) for a in range(N)])
cls = np.load('/home/user/degree-diameter/research/squads/deep-49/r2/a/cls.npy')
order = np.zeros(N, dtype=int)
for a in range(N):
    x, k = a, 1
    while x != 0:
        x = MT[x, a]; k += 1
    order[a] = k
def missed(T):
    T = np.unique(T); P2 = np.unique(MT[np.ix_(T, T)]); P4 = np.unique(MT[np.ix_(P2, P2)])
    m = np.ones(N, bool); m[P4] = False; return np.where(m)[0]
def tag(a):
    return 'o%d/c%d' % (order[a], cls[a])
tot = collections.Counter()
for fn in sys.argv[1:]:
    for line in open(fn):
        c, x, y, zz = map(int, line.split())
        S = [0, x, y, zz]
        mA = missed(np.array([MT[S[i], INV[S[j]]] for i in range(4) for j in range(4)]))
        mB = missed(np.array([MT[INV[S[i]], S[j]] for i in range(4) for j in range(4)]))
        print('S={0,%d,%d,%d} cost %d  A: %s  B: %s' % (x, y, zz, len(mA) + len(mB), [tag(a) for a in mA], [tag(a) for a in mB]))
