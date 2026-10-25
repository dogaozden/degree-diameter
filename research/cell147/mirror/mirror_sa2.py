#!/usr/bin/env python3
"""Annealing search for mirrored extensions, v2 (fast opposition tests).  See mirror_build.py for the conditions.
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
cur = cost(xs, ls); best_k = 0; it = 0; T = a.T
print(f'k={len(xs)} initial cost {cur}', flush=True)
while time.time() - t0 < a.secs:
    if cur == 0:
        k = len(xs)
        if k > best_k:
            best_k = k
            np.savez(os.path.join(a.outdir, f'state_k{k}.npz'), X=cand[xs], L=pool[ls], R=R)
            print(f'feasible k={k} (it {it}) [{time.time()-t0:.0f}s]', flush=True)
        nx = rand_x(xs); nl = rand_l(ls)
        if nx is None or nl is None: break
        xs = xs + [nx]; ls = ls + [nl]; cur = cost(xs, ls)
        continue
    it += 1
    j = int(rng.integers(len(xs)))
    best2 = None
    for _ in range(a.m):
        if rng.random() < 0.5:
            nx = rand_x(xs, skip=j)
            if nx is None: continue
            xs3 = xs.copy(); xs3[j] = nx; ls3 = ls
        else:
            nl = rand_l(ls, skip=j)
            if nl is None: continue
            ls3 = ls.copy(); ls3[j] = nl; xs3 = xs
        c3 = cost(xs3, ls3)
        if best2 is None or c3 < best2[0]: best2 = (c3, xs3, ls3)
    if best2 is None: continue
    c2, xs2, ls2 = best2
    if c2 <= cur or rng.random() < np.exp(-(c2 - cur) / T):
        xs, ls, cur = xs2, ls2, c2
    if it % 500 == 0: print(f'  it {it} k={len(xs)} cost {cur} [{time.time()-t0:.0f}s]', flush=True)
print('best feasible k =', best_k, 'iterations', it)
