"""Describe the cost-4 Haar sets of SL(2,5) x F21 (r1/c1 hits): missed elements per side, by conjugacy class and order."""
import sys, collections
import numpy as np
TAB = '/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/SL25x_C7C3.tab'
HITS = ['/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/SL25x_C7C3_L4a.hits',
        '/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/SL25x_C7C3_L4b.hits',
        '/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/SL25x_C7C3_L4c.hits']
f = open(TAB, 'rb'); N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
MT = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N).astype(np.int64); f.close()
INV = np.array([int(np.where(MT[a] == 0)[0][0]) for a in range(N)])
ar = np.arange(N)
order = np.zeros(N, dtype=int)
for a in range(N):
    x, k = a, 1
    while x != 0:
        x = MT[x, a]; k += 1
    order[a] = k
cls = -np.ones(N, dtype=int); csize = []; corder = []
for h in range(N):
    if cls[h] >= 0: continue
    c = np.unique(MT[MT[ar, h], INV])
    cls[c] = len(csize); csize.append(len(c)); corder.append(int(order[h]))
central = [a for a in range(N) if np.all(MT[a] == MT[:, a])]
z = [a for a in central if order[a] == 2]
print('N', N, 'classes', len(csize), 'central elements', central, 'central involution', z)
def name(a):
    return 'c%d(o%d,|C|=%d)' % (cls[a], order[a], csize[cls[a]])
sets = []
for fn in HITS:
    for line in open(fn):
        p = line.split()
        if len(p) == 4: sets.append(tuple(int(v) for v in p))
print('cost-4 sets read:', len(sets), 'costs', collections.Counter(s[0] for s in sets))
def missed(T):
    T = np.unique(T)
    P2 = np.unique(MT[np.ix_(T, T)])
    P4 = np.unique(MT[np.ix_(P2, P2)])
    m = np.ones(N, bool); m[P4] = False
    return np.where(m)[0]
rows = []
cnt_side = collections.Counter(); cnt_cls = collections.Counter()
for (c, x, y, zz) in sets:
    S = [0, x, y, zz]
    T1 = np.array([MT[S[i], INV[S[j]]] for i in range(4) for j in range(4)])
    T2 = np.array([MT[INV[S[i]], S[j]] for i in range(4) for j in range(4)])
    mA = missed(T1); mB = missed(T2)
    assert len(mA) + len(mB) == c, (c, len(mA), len(mB))
    rows.append((S, mA, mB))
    for side, m in (('A', mA), ('B', mB)):
        for a in m:
            cnt_side[(side, int(a))] += 1; cnt_cls[(side, int(cls[a]))] += 1
print('missed-element counts (side, element index, class, order): count over the 48 sets')
for (side, a), k in sorted(cnt_side.items(), key=lambda t: -t[1])[:12]:
    print('  side', side, 'elem', a, name(a), 'hits', k, 'central' if a in central else '')
print('missed by class (side, class id, order, size): count')
for (side, c), k in sorted(cnt_cls.items(), key=lambda t: -t[1]):
    print('  side', side, 'class', c, 'order', corder[c], 'size', csize[c], 'count', k)
print('sets missing the central involution', sum(1 for S, mA, mB in rows if any(a in central for a in mA) or any(a in central for a in mB)))
print('sets missing an element of order 2 on either side', sum(1 for S, mA, mB in rows if any(order[a] == 2 for a in list(mA) + list(mB))))
print('per-set missed element classes (first 48):')
for S, mA, mB in rows:
    print(S, 'A:', [name(int(a)) for a in mA], 'B:', [name(int(a)) for a in mB])
np.save('/home/user/degree-diameter/research/squads/deep-49/r2/a/cls.npy', cls)
