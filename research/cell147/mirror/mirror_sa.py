#!/usr/bin/env python3
"""Annealing search for mirrored extensions (see mirror_build.py for the conditions).
State: k pairs (x_j, L_j), x_j pairwise opposite points non-collinear with R, L_j pairwise opposite lines not in S.
Cost = total type deficit sum_t max(0, #R of type t - #usable S of type t).  At cost 0 the state is feasible: save it,
add a random pair (k+1) and continue.  usage: mirror_sa.py SEED OUTDIR [--k0 9] [--pool 20000] [--secs 1500]"""
import numpy as np, sys, os, time, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
ap = argparse.ArgumentParser(); ap.add_argument('seed', type=int); ap.add_argument('outdir')
ap.add_argument('--k0', type=int, default=9); ap.add_argument('--pool', type=int, default=20000)
ap.add_argument('--secs', type=float, default=1500); ap.add_argument('--T', type=float, default=0.6)
ap.add_argument('--rfile', default=SP + 'R756idx.npy')
a = ap.parse_args(); rng = np.random.default_rng(a.seed); os.makedirs(a.outdir, exist_ok=True)
t0 = time.time()
H = Hex(SP + 'hex_q11.bin'); N = H.N; q = 11
R = np.load(a.rfile); nR = len(R); S = np.load(SP + 'S_herm.npy'); nS = len(S)
X = H.X; inE = (X[:, 0] + X[:, 4]) % q == 0
Sline = -np.ones(N, dtype=np.int64)
for j, l in enumerate(S): Sline[H.lp[l]] = j
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]; nc = len(cand)
NR = (H.Bmat(cand, R) == 0)                          # nc x nR
Sset = np.zeros(N, bool); Sset[S] = True
pool = rng.choice(np.nonzero(~Sset)[0], size=a.pool, replace=False)
P = H.lp[pool]; conc = Sline[P]
C = H.lp[H.pl[P]].reshape(len(pool), -1); near = Sline[C]
LS4 = np.zeros((len(pool), nS), bool); LS2 = np.zeros((len(pool), nS), bool)
rows = np.repeat(np.arange(len(pool)), near.shape[1]); ok = near.reshape(-1) >= 0
LS4[rows[ok], near.reshape(-1)[ok]] = True
rows2 = np.repeat(np.arange(len(pool)), conc.shape[1]); ok2 = conc.reshape(-1) >= 0
LS2[rows2[ok2], conc.reshape(-1)[ok2]] = True
LS4 &= ~LS2
print(f'candidates {nc}, line pool {len(pool)} [{time.time()-t0:.1f}s]', flush=True)
def line_opp(i, j):
    d2, d4 = H.line_ball(int(pool[i])); l = int(pool[j]); return l not in d2 and l not in d4
def pts_opp(i, js):
    if len(js) == 0: return True
    return bool((H.Bmat(cand[[i]], cand[np.array(js)]) != 0).all())
W = (1 << np.arange(63, dtype=np.int64))
def cost(xs, ls):
    k = len(xs)
    tR = (NR[xs].T.astype(np.int64) * W[:k]).sum(axis=1)
    tS = (LS4[ls].T.astype(np.int64) * W[:k]).sum(axis=1)
    ex = LS2[ls].any(axis=0)
    ur, cr = np.unique(tR, return_counts=True)
    us, cs = np.unique(tS[~ex], return_counts=True)
    d = dict(zip(us.tolist(), cs.tolist()))
    return int(sum(max(0, c - d.get(t, 0)) for t, c in zip(ur.tolist(), cr.tolist())))
def rand_x(xs, skip=None):
    for _ in range(2000):
        i = int(rng.integers(nc))
        others = [x for j, x in enumerate(xs) if j != skip]
        if i in others: continue
        if pts_opp(i, others): return i
    return None
def rand_l(ls, skip=None):
    for _ in range(2000):
        i = int(rng.integers(len(pool)))
        others = [l for j, l in enumerate(ls) if j != skip]
        if i in others: continue
        if all(line_opp(i, l) for l in others): return i
    return None
xs, ls = [], []
for _ in range(a.k0):
    xs.append(rand_x(xs)); ls.append(rand_l(ls))
cur = cost(xs, ls); best_k = 0; it = 0; T = a.T
print(f'k={len(xs)} initial cost {cur}', flush=True)
while time.time() - t0 < a.secs:
    it += 1
    j = int(rng.integers(len(xs)))
    if rng.random() < 0.5:
        nx = rand_x(xs, skip=j)
        if nx is None: continue
        xs2 = xs.copy(); xs2[j] = nx; ls2 = ls
    else:
        nl = rand_l(ls, skip=j)
        if nl is None: continue
        ls2 = ls.copy(); ls2[j] = nl; xs2 = xs
    c2 = cost(xs2, ls2)
    if c2 <= cur or rng.random() < np.exp(-(c2 - cur) / T):
        xs, ls, cur = xs2, ls2, c2
    if cur == 0:
        k = len(xs)
        if k > best_k:
            best_k = k
            np.savez(os.path.join(a.outdir, f'state_k{k}.npz'), X=cand[xs], L=pool[ls], R=R)
            print(f'feasible k={k} (it {it}) [{time.time()-t0:.0f}s]', flush=True)
        nx = rand_x(xs); nl = rand_l(ls)
        if nx is None or nl is None: break
        xs = xs + [nx]; ls = ls + [nl]; cur = cost(xs, ls)
print('best feasible k =', best_k, 'iterations', it)
