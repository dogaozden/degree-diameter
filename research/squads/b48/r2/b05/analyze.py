import numpy as np, collections, sys
D = np.loadtxt(sys.argv[1] if len(sys.argv) > 1 else 'samples.txt')
far = D[:, 0]
cls = D[:, 4:7].astype(int)
feat = D[:, 7:]
names = ['daa12','daa13','daa23','dbb12','dbb13','dbb23','dab12','dab21','dab13','dab31','dab23','dab32']
print('N', len(far), 'far min/mean/max', far.min(), far.mean().round(1), far.max())
print('corr with each seed-distance feature:')
for i, nm in enumerate(names):
    c = np.corrcoef(feat[:, i], far)[0, 1]
    vals = collections.Counter(feat[:, i].astype(int))
    print(f'  {nm}: corr={c:+.3f}  mean-by-value', {v: round(far[feat[:, i] == v].mean(), 1) for v in sorted(vals)})
# class multiset
print('by class multiset (count, mean far, min far):')
ms = collections.defaultdict(list)
for f, c in zip(far, cls):
    ms[tuple(sorted(c))].append(f)
rows = sorted(ms.items(), key=lambda kv: np.mean(kv[1]))
for k, v in rows[:12]:
    print('  ', k, len(v), round(np.mean(v), 1), min(v))
print('  ...'); 
for k, v in rows[-4:]:
    print('  ', k, len(v), round(np.mean(v), 1), min(v))
# distinct classes vs repeated
rep = np.array([len(set(c)) for c in cls])
for r in (1, 2, 3):
    if (rep == r).any(): print('distinct classes', r, 'mean far', far[rep == r].mean().round(1), 'n', (rep == r).sum(), 'min', far[rep == r].min())
# linear regression on one-hot of dab and daa/dbb
X = [np.ones(len(far))]
for i in range(12):
    X.append(feat[:, i])
X = np.column_stack(X)
beta, *_ = np.linalg.lstsq(X, far, rcond=None)
res = far - X @ beta
print('linear fit R2', round(1 - res.var() / far.var(), 3))
print('coef', dict(zip(['c']+names, np.round(beta, 2))))
# top 20 triples
idx = np.argsort(far)[:15]
print('best 15 rows: far e1 e2 e3 classes | daa dbb dab')
for i in idx:
    print(int(far[i]), D[i,1:4].astype(int), cls[i], feat[i].astype(int))
