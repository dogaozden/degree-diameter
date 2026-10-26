import numpy as np, collections, sys
D = np.loadtxt(sys.argv[1])
far = D[:, 0]; cls = D[:, 4:7].astype(int); feat = D[:, 7:].astype(int)
dab = feat[:, 6:]; daa = feat[:, :3]; dbb = feat[:, 3:6]
n1 = (dab == 1).sum(1)
print('mean far by n1 (# cross pairs at distance 1):')
for v in sorted(set(n1)): 
    m = n1 == v; print('  n1=%d count=%d mean=%.1f min=%d' % (v, m.sum(), far[m].mean(), far[m].min()))
# min distance among all 6 cross + 6 same-side pairs
mind = np.minimum(dab.min(1), np.minimum(daa.min(1), dbb.min(1)))
print('mean by #distance-2 among same side pairs:')
n2 = ((daa == 2).sum(1) + (dbb == 2).sum(1))
for v in sorted(set(n2)):
    m = n2 == v; print('  n2=%d count=%d mean=%.1f min=%d' % (v, m.sum(), far[m].mean(), far[m].min()))
# class-type effect controlling for n1
cm = collections.defaultdict(list)
for f, c, k in zip(far, cls, n1): cm[(tuple(sorted(c)), k)].append(f)
print('class multiset x n1: (count, mean, min)')
for key in sorted(cm, key=lambda k: np.mean(cm[k]))[:20]:
    v = cm[key]; print('  ', key, len(v), round(np.mean(v), 1), min(v))
# stats on the best 1%
best = far <= np.percentile(far, 2)
print('bottom 2 percent: n1 hist', collections.Counter(n1[best]), ' class count hist', collections.Counter(tuple(sorted(c)) for c in cls[best]).most_common(6))
print('bottom 2 percent: daa=2 frac', (daa[best]==2).mean().round(2), 'dbb=2 frac', (dbb[best]==2).mean().round(2), 'overall', (daa==2).mean().round(2), (dbb==2).mean().round(2))
print('bottom 2 percent: dist-by-class-sets', collections.Counter(tuple(sorted(c)) for c in cls[best]).most_common(3))
