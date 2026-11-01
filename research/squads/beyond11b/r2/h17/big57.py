import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/r2/h17')
from frob import Frob, covers
from analyse import coset_nb_dp
p, k, r = 21589, 7, 17486
G = Frob(p, k, r); N = G.N; d = 5; h = 5; D = 11
W = d * (d - 1) ** (2 * h - 1)
print('N', N, 'W/N', round(W / N, 3), 'size law per side', round(N * np.exp(-W / N), 2))
rng = np.random.default_rng(int(sys.argv[1])); t0 = time.time(); out = []
jj = np.arange(N) % k
while time.time() - t0 < 80:
    S = [0] + [int(x) for x in rng.choice(np.arange(1, N), size=d - 1, replace=False)]
    labels = [s % k for s in S]
    if len(set(labels)) < 3: continue
    XA, XB = covers(G, S, D)
    hA = (~XA); hB = (~XB)
    Wj = coset_nb_dp(labels)
    out.append((int(hA.sum()), int(hB.sum()), float(Wj.max() / max(Wj.min(), 1e-9)), sorted(labels), int(hA.sum() - hA[jj==0].sum())))
print('samples', len(out), 'time', round(time.time() - t0, 1))
a = np.array([o[0] for o in out]); b = np.array([o[1] for o in out])
print('holes A: min', a.min(), 'median', np.median(a), 'mean', a.mean().round(1), '| B median', np.median(b))
print('wratio median', np.median([o[2] for o in out]).round(3))
for o in sorted(out)[:5]: print('best A/B', o[0], o[1], 'labels', o[3], 'wratio', round(o[2], 3))
