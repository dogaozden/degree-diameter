#!/usr/bin/env python3
"""Annealing search for mirrored extensions, v3: maximise F = k - deficit (unmatched base points are dropped).  See mirror_build.py for the conditions.
State: k pairs (x_j, L_j); x_j pairwise opposite points non-collinear with R; L_j pairwise opposite lines not in S.
Cost = sum_t max(0, #R of type t - #usable S lines of type t).  Cost 0 = feasible: save, add a pair, continue.
usage: mirror_sa2.py SEED OUTDIR [--init STATE.npz] [--pool 20000] [--secs 1500] [--T 0.5]"""
import numpy as np, sys, os, time, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
ap = argparse.ArgumentParser(); ap.add_argument('seed', type=int); ap.add_argument('outdir')
ap.add_argument('--init', default=''); ap.add_argument('--pool', type=int, default=20000)
ap.add_argument('--secs', type=float, default=1500); ap.add_argument('--T', type=float, default=0.5)
ap.add_argument('--k0', type=int, default=9); ap.add_argument('--m', type=int, default=8); ap.add_argument('--rfile', default=SP + 'R756idx.npy')
a = ap.parse_args(); rng = np.random.default_rng(a.seed); os.makedirs(a.outdir, exist_ok=True)
t0 = time.time()
H = Hex(SP + 'hex_q11.bin'); N = H.N; q = 11
R = np.load(a.rfile); nR = len(R); S = np.load(SP + 'S_herm.npy'); nS = len(S)
Sline = -np.ones(N, dtype=np.int64)
for j, l in enumerate(S): Sline[H.lp[l]] = j
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]; nc = len(cand)
NR = (H.Bmat(cand, R) == 0)
Sset = np.zeros(N, bool); Sset[S] = True
pool = rng.choice(np.nonzero(~Sset)[0], size=a.pool, replace=False)
init = None
if a.init:
    st = np.load(a.init); init = (st['X'], st['L'])
    pool = np.concatenate([st['L'], pool[~np.isin(pool, st['L'])]])
npool = len(pool)
P = H.lp[pool]; conc = Sline[P]
C = H.lp[H.pl[P]].reshape(npool, -1)              # points at distance <= 3 from the line (with repeats)
near = Sline[C]
LS4 = np.zeros((npool, nS), bool); LS2 = np.zeros((npool, nS), bool)
rows = np.repeat(np.arange(npool), near.shape[1]); ok = near.reshape(-1) >= 0
LS4[rows[ok], near.reshape(-1)[ok]] = True
rows2 = np.repeat(np.arange(npool), conc.shape[1]); ok2 = conc.reshape(-1) >= 0
LS2[rows2[ok2], conc.reshape(-1)[ok2]] = True
LS4 &= ~LS2
Csorted = np.sort(C, axis=1)
print(f'candidates {nc}, line pool {npool} [{time.time()-t0:.1f}s]', flush=True)


def line_opp(i, js):
    """pool[i] opposite to every pool[j]: no point of pool[j] within distance 3 of pool[i]."""
    for j in js:
        pj = P[j]
        pos = np.searchsorted(Csorted[i], pj); pos[pos >= Csorted.shape[1]] = 0
        if (Csorted[i][pos] == pj).any(): return False
    return True


def pts_opp(i, js):
    if len(js) == 0: return True
    return bool((H.Bmat(cand[[i]], cand[np.array(js)]) != 0).all())


W = (1 << np.arange(62, dtype=np.int64))


def cost(xs, ls):
    k = len(xs)
    tR = NR[xs].T.astype(np.int64) @ W[:k]
    tS = LS4[ls].T.astype(np.int64) @ W[:k]
    ex = LS2[ls].any(axis=0)
    ur, cr = np.unique(tR, return_counts=True)
    us, cs = np.unique(tS[~ex], return_counts=True)
    pos = np.searchsorted(us, ur); pos[pos >= len(us)] = 0
    have = np.where(us[pos] == ur, cs[pos], 0)
    return int(np.maximum(0, cr - have).sum())


def rand_x(xs, skip=None):
    others = [x for j, x in enumerate(xs) if j != skip]
    for _ in range(5000):
        i = int(rng.integers(nc))
        if i in others: continue
        if pts_opp(i, others): return i
    return None


def rand_l(ls, skip=None):
    others = [l for j, l in enumerate(ls) if j != skip]
    for _ in range(5000):
        i = int(rng.integers(npool))
        if i in others: continue
        if line_opp(i, others): return i
    return None


if init is not None:
    cidx = {int(c): i for i, c in enumerate(cand)}
    xs = [cidx[int(x)] for x in init[0]]; ls = list(range(len(init[1])))
else:
    xs, ls = [], []
    for _ in range(a.k0): xs.append(rand_x(xs)); ls.append(rand_l(ls))
def F(xs, ls): return len(xs) - cost(xs, ls)
cur = F(xs, ls); best = -10**9; it = 0; T = a.T
print(f'k={len(xs)} initial F {cur}', flush=True)
while time.time() - t0 < a.secs:
    it += 1
    u = rng.random(); cands = []
    for _ in range(a.m):
        if u < 0.15:                                   # add a pair
            nx = rand_x(xs); nl = rand_l(ls)
            if nx is None or nl is None: continue
            xs3, ls3 = xs + [nx], ls + [nl]
        elif u < 0.25 and len(xs) > 1:                 # remove a pair
            j = int(rng.integers(len(xs))); xs3 = xs[:j] + xs[j + 1:]; ls3 = ls[:j] + ls[j + 1:]
        else:
            j = int(rng.integers(len(xs)))
            if rng.random() < 0.5:
                nx = rand_x(xs, skip=j)
                if nx is None: continue
                xs3 = xs.copy(); xs3[j] = nx; ls3 = ls
            else:
                nl = rand_l(ls, skip=j)
                if nl is None: continue
                ls3 = ls.copy(); ls3[j] = nl; xs3 = xs
        cands.append((F(xs3, ls3), xs3, ls3))
    if not cands: continue
    f2, xs2, ls2 = max(cands, key=lambda c: c[0])
    if f2 >= cur or rng.random() < np.exp((f2 - cur) / T):
        xs, ls, cur = xs2, ls2, f2
    if cur > best:
        best = cur
        np.savez(os.path.join(a.outdir, f'best.npz'), X=cand[xs], L=pool[ls], R=R)
        print(f'F={cur} (k={len(xs)}, deficit {len(xs) - cur}) it {it} [{time.time()-t0:.0f}s]', flush=True)
    if it % 1000 == 0: print(f'  it {it} k={len(xs)} F {cur} [{time.time()-t0:.0f}s]', flush=True)
print('best F =', best, 'iterations', it)
