#!/usr/bin/env python3
"""c3: line-only annealing for FIXED extra points X.  cost = number of base points that must be dropped
(sum over types of max(0, base count - usable spread-line count)); F = k - cost.  Lines are drawn from a random pool
of non-spread lines; moves replace one line by the best of M proposals (pairwise-opposite lines enforced).
usage: lines_sa.py XFILE.npy SEED OUTDIR [--secs S] [--pool P] [--T T] [--M M] [--init STATE.npz]"""
import numpy as np, sys, os, time, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
ap = argparse.ArgumentParser(); ap.add_argument('xfile'); ap.add_argument('seed', type=int); ap.add_argument('outdir')
ap.add_argument('--secs', type=float, default=600); ap.add_argument('--pool', type=int, default=20000)
ap.add_argument('--T', type=float, default=0.3); ap.add_argument('--M', type=int, default=24)
ap.add_argument('--init', default='')
a = ap.parse_args(); rng = np.random.default_rng(a.seed); os.makedirs(a.outdir, exist_ok=True)
t0 = time.time()
H = Hex(SP + 'hex_q11.bin'); N = H.N
R = np.load(SP + 'R756idx.npy'); S = np.load(SP + 'S_herm.npy'); nS = len(S)
Xs = np.load(a.xfile).astype(np.int64); k = len(Xs)
NR = (H.Bmat(Xs, R) == 0)                               # k x 756 : base points at distance 4 from each x
Sline = -np.ones(N, dtype=np.int64)
for j, l in enumerate(S): Sline[H.lp[l]] = j
Sset = np.zeros(N, bool); Sset[S] = True
pool = rng.choice(np.nonzero(~Sset)[0], size=a.pool, replace=False)
init_pool = None
if a.init:
    st = np.load(a.init); init_pool = st['L']
    pool = np.concatenate([init_pool, pool[~np.isin(pool, init_pool)]])
npool = len(pool)
LS4 = np.zeros((npool, nS), bool); LS2 = np.zeros((npool, nS), bool)
Csorted = np.zeros((npool, 1728), dtype=np.int64)
for c0 in range(0, npool, 2000):
    P = H.lp[pool[c0:c0 + 2000]]                        # (b,12) points of each pool line
    conc = Sline[P]; C = H.lp[H.pl[P]].reshape(len(P), -1)
    near = Sline[C]
    rows = np.repeat(np.arange(len(P)), conc.shape[1]); ok = conc.reshape(-1) >= 0
    LS2[c0 + rows[ok], conc.reshape(-1)[ok]] = True
    rows = np.repeat(np.arange(len(P)), near.shape[1]); ok = near.reshape(-1) >= 0
    LS4[c0 + rows[ok], near.reshape(-1)[ok]] = True
    Csorted[c0:c0 + len(P)] = np.sort(C, axis=1)
LS4 &= ~LS2
Ppts = H.lp[pool]
print(f'pool {npool}, k={k} [{time.time()-t0:.1f}s]', flush=True)

def line_opp(i, js):
    for j in js:
        pj = Ppts[j]
        pos = np.searchsorted(Csorted[i], pj); pos[pos >= Csorted.shape[1]] = 0
        if (Csorted[i][pos] == pj).any(): return False
    return True

# base type masks (fixed, since X is fixed)
mR = np.zeros(len(R), np.int64)
for j in range(k): mR |= NR[j].astype(np.int64) << j
ub, cb = np.unique(mR, return_counts=True)

def supply(mask, exc):
    u = (exc == 0)
    us, cs = np.unique(mask[u], return_counts=True)
    return us, cs

def cost_of(mask, exc):
    us, cs = supply(mask, exc)
    pos = np.searchsorted(us, ub); pos[pos >= len(us)] = 0
    have = np.where(us[pos] == ub, cs[pos], 0)
    return int(np.maximum(0, cb - have).sum())

# initial lines
if init_pool is not None:
    ls = list(range(k))
else:
    ls = []
    while len(ls) < k:
        i = int(rng.integers(npool))
        if i in ls: continue
        if line_opp(i, ls): ls.append(i)
def state_arrays(ls):
    mask = np.zeros(nS, np.int64); exc = np.zeros(nS, np.int64)
    for j, i in enumerate(ls):
        mask |= LS4[i].astype(np.int64) << j; exc += LS2[i]
    return mask, exc
mask, exc = state_arrays(ls)
cur = cost_of(mask, exc); best = cur; bestls = list(ls)
np.savez(os.path.join(a.outdir, 'best.npz'), X=Xs, L=pool[np.array(bestls)], R=R)
print(f'initial cost {cur} (F={k-cur}) [{time.time()-t0:.1f}s]', flush=True)
it = 0; T = a.T
while time.time() - t0 < a.secs and best > 0:
    it += 1
    j = int(rng.integers(k)); bit = np.int64(1) << j
    props = []
    cand_ids = rng.integers(npool, size=a.M)
    base_mask = mask & ~bit; base_exc = exc - LS2[ls[j]]
    for c in cand_ids:
        c = int(c)
        if c in ls: continue
        others = ls[:j] + ls[j + 1:]
        if not line_opp(c, others): continue
        m2 = base_mask | (bit * LS4[c].astype(np.int64))
        e2 = base_exc + LS2[c]
        props.append((cost_of(m2, e2), c, m2, e2))
    if not props: continue
    props.sort(key=lambda p: p[0])
    cc, c, m2, e2 = props[0]
    if cc <= cur or rng.random() < np.exp(-(cc - cur) / T):
        ls[j] = c; mask, exc, cur = m2, e2, cc
        if cur < best:
            best = cur; bestls = list(ls)
            np.savez(os.path.join(a.outdir, 'best.npz'), X=Xs, L=pool[np.array(bestls)], R=R)
            print(f'  best cost {best} (F={k-best}) it {it} [{time.time()-t0:.0f}s]', flush=True)
    if it % 1000 == 0: print(f'  it {it} cur {cur} best {best} [{time.time()-t0:.0f}s]', flush=True)
print(f'final best cost {best} => F = {k-best}; iterations {it} [{time.time()-t0:.0f}s]', flush=True)
