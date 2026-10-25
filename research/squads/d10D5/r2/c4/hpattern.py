"""hpattern.py FLAGSFREE SOL: for a flag set, search H in {1,2}^k (max sum H) under the demand model:
per flag sum_m e(i,m) <= 8 H_i (4 spare per hub, 2 sides), e(i,m) = max/min/0 as in model.py."""
import sys, itertools
sys.path.insert(0, '.')
from model import demand, flags_from, collinear, concurrent
from model import N
free = list(map(int, open(sys.argv[1]).read().split()))
rows = [ln.split() for ln in open(sys.argv[2]) if ln.strip()]
sig = list(map(int, [r for r in rows if r[0] not in ('7', 'cyc') and len(r) == N][0]))
flags = flags_from(free, sig); k = len(flags)
P = [[collinear(flags[i][0], flags[j][0]) if i != j else True for j in range(k)] for i in range(k)]
C = [[concurrent(flags[i][1], flags[j][1]) if i != j else True for j in range(k)] for i in range(k)]
def ok(H):
    for i in range(k):
        s = 0
        for m in range(k):
            if m == i: continue
            nA = not P[i][m]; nB = not C[i][m]; hi, hm = H[i], H[m]
            s += (max(hi, hm) if nA and nB else (min(hi, hm) if (nA or nB) else 0))
        if s > 8 * H[i]: return False
    return True
best = None
for b in range(0, k + 1):
    for ones in itertools.combinations(range(k), b):
        H = [2] * k
        for i in ones: H[i] = 1
        if ok(H):
            tot = sum(H)
            if best is None or tot > best[0]: best = (tot, H)
    if best and best[0] >= 2 * k - b: break
print('k', k, 'best sum H (model, per-flag caps)', best[0] if best else None, 'gain', 2 * best[0] if best else None,
      'H', ' '.join(map(str, best[1])) if best else '-')
