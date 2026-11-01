# (4) non-degenerate S (>=3 distinct labels): holes vs coset-level Poisson law, and hole placement by coset type
import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/r2/h17')
from frob import Frob, covers
from analyse import coset_nb_dp
p, k, r, h, D = 761, 19, 25, 5, 11
G = Frob(p, k, r); N = G.N; d = 4; W = d * (d - 1) ** (2 * h - 1)
seed, want = int(sys.argv[1]), int(sys.argv[2])
rng = np.random.default_rng(seed)
jj = np.arange(N) % k
rows = []; hole_coset = np.zeros(k); t0 = time.time()
while len(rows) < want and time.time() - t0 < 85:
    others = rng.choice(np.arange(1, N), size=d - 1, replace=False)
    S = [0] + [int(x) for x in others]
    labels = [s % k for s in S]
    if len(set(labels)) < 3:
        continue
    XA, XB = covers(G, S, D)
    hA = ~XA
    Wj = coset_nb_dp(labels)
    pred = float(sum(p * np.exp(-Wj[j] / p) for j in range(k)))
    hc = np.bincount(jj[hA], minlength=k)
    hole_coset += hc
    rows.append(dict(hA=int(hA.sum()), hB=int(((~XB)).sum()), pred=pred, ker=int(hc[0]),
                     wratio=float(Wj.max() / Wj.min()), S=S, labels=labels))
hA = np.array([x['hA'] for x in rows]); pred = np.array([x['pred'] for x in rows])
print('samples', len(rows), 'time', round(time.time() - t0, 1))
print('size law N e^{-W/N} =', round(N * np.exp(-W / N), 2), '| mean coset-level law (per side) =', pred.mean().round(2))
print('actual holes per side (A): mean', hA.mean().round(2), 'median', np.median(hA), 'pct 10/25/75/90', np.percentile(hA, [10, 25, 75, 90]))
print('actual B mean', np.mean([x['hB'] for x in rows]).round(2))
print('ratio actual/pred: median', np.median(hA / pred).round(3), ' log-corr', np.corrcoef(np.log1p(hA), np.log1p(pred))[0, 1].round(3))
print('share of holes in kernel coset j=0:', (hole_coset[0] / hole_coset.sum()).round(4), ' uniform would be', round(1 / k, 4))
print('holes per coset (A, summed):', hole_coset.astype(int).tolist())
print('samples with A-holes <= 10:', int((hA <= 10).sum()), 'of', len(rows), '; <=6:', int((hA <= 6).sum()))
print('mean wratio (max/min NB coset count):', np.mean([x['wratio'] for x in rows]).round(3), 'median', np.median([x['wratio'] for x in rows]).round(3))
import json
json.dump(rows, open(f'ens2_seed{seed}.json', 'w'))
