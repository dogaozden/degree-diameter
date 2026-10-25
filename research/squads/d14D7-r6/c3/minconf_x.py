#!/usr/bin/env python3
"""c3: min-conflicts search for a pairwise-opposite set X of size K with every base point in <= 2 neighbourhoods
N(x) (no base point at distance 4 from three extra points).  usage: minconf_x.py K SEED STEPS OUT.npy [--init XS.npy]"""
import numpy as np, sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
K = int(sys.argv[1]); seed = int(sys.argv[2]); steps = int(sys.argv[3]); out = sys.argv[4]
rng = np.random.default_rng(seed); t0 = time.time()
H = Hex(SP + 'hex_q11.bin'); N = H.N
R = np.load(SP + 'R756idx.npy')
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]; nc = len(cand)
NRb = np.zeros((nc, len(R)), bool)
for a in range(0, nc, 8192):
    NRb[a:a + 8192] = (H.Bmat(cand[a:a + 8192], R) == 0)
NRf = NRb.astype(np.float32)
Xi = list(rng.choice(nc, size=K, replace=False))
if len(sys.argv) > 6 and sys.argv[5] == '--init':
    init = np.load(sys.argv[6]); cidx = {int(c): i for i, c in enumerate(cand)}
    Xi = [cidx[int(p)] for p in init][:K]
    while len(Xi) < K: Xi.append(int(rng.integers(nc)))
def viol_of(X):
    c = NRb[X].sum(0); return int(np.maximum(0, c - 2).sum())
def opp_ok_all(X):
    ok = np.ones(nc, bool)
    for x in X: ok &= (H.Bmat(cand, cand[x:x + 1])[:, 0] != 0)
    return ok
tabu = np.zeros(nc, np.int64)
cov = NRb[Xi].sum(0).astype(np.float32)
V = viol_of(Xi); best = V; bestX = list(Xi)
print(f'K={K} start violations {V} [{time.time()-t0:.1f}s]', flush=True)
it = 0
while V > 0 and it < steps:
    it += 1
    cov = NRb[Xi].sum(0)
    # choose a point to remove among those contributing to a violated base point
    viol_r = cov >= 3
    contrib = [j for j, x in enumerate(Xi) if (NRb[x] & viol_r).any()]
    j = int(rng.choice(contrib)) if contrib and rng.random() < 0.9 else int(rng.integers(K))
    rest = [x for t, x in enumerate(Xi) if t != j]
    cm = NRb[rest].sum(0)
    sat = (cm >= 2).astype(np.float32)
    dV = NRf @ sat                                  # violation increase if y is added
    ok = opp_ok_all(rest)
    ok &= (tabu <= it)
    ok[rest] = False
    dV = np.where(ok, dV + rng.random(nc) * 0.5, np.inf)
    y = int(np.argmin(dV))
    tabu[Xi[j]] = it + 5 + int(rng.integers(5))
    Xi[j] = y
    V = viol_of(Xi)
    if V < best: best = V; bestX = list(Xi)
    if it % 200 == 0: print(f'  it {it} V {V} best {best} [{time.time()-t0:.0f}s]', flush=True)
print(f'K={K} final best violations {best} after {it} steps [{time.time()-t0:.0f}s]', flush=True)
if True:
    np.save(out, cand[np.array(bestX, dtype=np.int64)]); print('saved', out, 'violations', best)
