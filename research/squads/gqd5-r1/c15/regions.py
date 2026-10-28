import sys, pickle, random, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c15')
import numpy as np, slots, slots2
n = int(sys.argv[1]); r = (n - 1) // 2
d = pickle.load(open('res_%d.pkl' % n, 'rb')); T = d['tournaments']
OUTa, INa, tida, typa, types = slots2.build(n, T)
rng = np.random.default_rng(0)
# directions in the cone a>=b>=c>=0 (homogeneous): sample a=1, 0<=c<=b<=1
pts = []
for _ in range(int(sys.argv[2]) if len(sys.argv) > 2 else 1500):
    b, c = sorted(rng.random(2), reverse=True)  # b>=c
    pts.append((1.0, b, c))
pts += [(1.0, 1.0, 0.0), (1.0, 0.0, 0.0), (1.0, 1.0, 1.0)]
P = np.array(pts)
best = np.full(len(P), -1e9)
for s in range(0, len(OUTa), 5000):
    best = np.maximum(best, slots2.values(OUTa[s:s+5000], INa[s:s+5000], P).max(axis=0))
forms = [f for f in itertools.product(range(2 * r + 1), repeat=3) if sum(f) == 2 * r]
cnt = {}
for g in range(len(P)):
    fs = tuple(f for f in forms if abs(np.dot(f, P[g]) - best[g]) < 1e-6)
    cnt[fs] = cnt.get(fs, 0) + 1
print('n=%d r=%d: best-formula sets over 1503 directions (formula sets with counts):' % (n, r))
for fs, k in sorted(cnt.items(), key=lambda kv: -kv[1])[:10]:
    print('  %4d  %s' % (k, ' '.join('%d*a+%d*b+%d*c' % f for f in fs)))
