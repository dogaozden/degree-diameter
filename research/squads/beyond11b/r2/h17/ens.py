import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/r2/h17')
from frob import Frob, covers, nb_counts
from analyse import coset_nb_dp
p, k, r, h, D = 761, 19, 25, 5, 11
G = Frob(p, k, r); N = G.N; d = 4; W = d * (d - 1) ** (2 * h - 1)
seed, trials = int(sys.argv[1]), int(sys.argv[2])
rng = np.random.default_rng(seed)
res = []
t0 = time.time()
jj = np.arange(N) % k
for tr in range(trials):
    others = rng.choice(np.arange(1, N), size=d - 1, replace=False)
    S = [0] + [int(x) for x in others]
    XA, XB = covers(G, S, D)
    hA = ~XA; hB = ~XB
    labels = [s % k for s in S]
    Wj = coset_nb_dp(labels)
    # coset-level Poisson prediction (per side), pair-free units
    pred_jensen = float(sum(p * np.exp(-Wj[j] / p) for j in range(k)))
    res.append(dict(hA=int(hA.sum()), hB=int(hB.sum()),
                    hA_ker=int(hA[jj == 0].sum()), hB_ker=int(hB[jj == 0].sum()),
                    cosets_empty_A=int(sum(1 for j in range(k) if hA[jj == j].all())),
                    labels_distinct=len(set(labels)), Wj_min=float(Wj.min()), Wj_max=float(Wj.max()),
                    pred_jensen=pred_jensen, labels=labels, S=S))
    if time.time() - t0 > 90: break
hA = np.array([x['hA'] for x in res]); hB = np.array([x['hB'] for x in res])
print('trials', len(res), 'time', round(time.time() - t0, 1))
print('N e^{-W/N} (size law, per side, element units) =', round(N * np.exp(-W / N), 2))
print('mean holes per side A/B:', hA.mean().round(2), hB.mean().round(2), ' median', np.median(hA), np.median(hB))
print('frac exact-cover (both sides 0):', np.mean((hA == 0) & (hB == 0)).round(3))
print('mean holes in kernel j=0 (A,B):', np.mean([x['hA_ker'] for x in res]).round(3), np.mean([x['hB_ker'] for x in res]).round(3))
print('mean coset-level Jensen prediction:', np.mean([x['pred_jensen'] for x in res]).round(2))
print('mean (Wj max/min):', np.mean([x['Wj_max'] / max(x['Wj_min'], 1e-9) for x in res]).round(4))
print('mean #cosets fully uncovered (A):', np.mean([x['cosets_empty_A'] for x in res]).round(3))
print('distinct-label counts:', np.bincount([x['labels_distinct'] for x in res]))
import json
json.dump(res, open(f'ens_seed{seed}.json', 'w'))
