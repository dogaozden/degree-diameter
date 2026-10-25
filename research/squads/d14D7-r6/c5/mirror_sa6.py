#!/usr/bin/env python3
"""OPTIMISTIC union bound for mixing spreads: the image pool is the union of several dual ovoids (each given as a .npy
of line ids, repeat --spread).  Every usable column (line of one spread not concurrent with any L_j) counts as a free
image, so this ignores the pairwise-opposite constraint between different spreads and is an UPPER BOUND on what a
conflict-free mixed f(R) could reach.  Same moves and cost as mirror_sa5.py otherwise.
usage: mirror_sa6.py SEED OUTDIR --spread A.npy --spread B.npy [--secs S] [--T 0.15]"""
import numpy as np, sys, os, time, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
ap = argparse.ArgumentParser(); ap.add_argument('seed', type=int); ap.add_argument('outdir')
ap.add_argument('--spread', action='append', default=[])
ap.add_argument('--pool', type=int, default=12000)
ap.add_argument('--secs', type=float, default=1500); ap.add_argument('--T', type=float, default=0.15)
ap.add_argument('--m', type=int, default=8); ap.add_argument('--sample', type=int, default=150)
ap.add_argument('--rfile', default=SP + 'R756idx.npy')
a = ap.parse_args(); rng = np.random.default_rng(a.seed); os.makedirs(a.outdir, exist_ok=True)
spreads = [np.load(f) for f in (a.spread or [SP + 'S_herm.npy'])]
t0 = time.time()
H = Hex(SP + 'hex_q11.bin'); N = H.N; q = 11
R = np.load(a.rfile)
Sset = np.zeros(N, bool)
for S in spreads: Sset[S] = True
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]; nc = len(cand)
NR = (H.Bmat(cand, R) == 0)
NRf = NR.astype(np.float32)
pool = rng.choice(np.nonzero(~Sset)[0], size=a.pool, replace=False)
npool = len(pool)
P = H.lp[pool]
C = H.lp[H.pl[P]].reshape(npool, -1)
Csorted = np.sort(C, axis=1)
LS4s, LS2s = [], []
for S in spreads:
    Sline = -np.ones(N, dtype=np.int64)
    for j, l in enumerate(S): Sline[H.lp[l]] = j
    conc = Sline[P]; near = Sline[C]
    LS4 = np.zeros((npool, len(S)), bool); LS2 = np.zeros((npool, len(S)), bool)
    rows = np.repeat(np.arange(npool), near.shape[1]); ok = near.reshape(-1) >= 0
    LS4[rows[ok], near.reshape(-1)[ok]] = True
    rows2 = np.repeat(np.arange(npool), conc.shape[1]); ok2 = conc.reshape(-1) >= 0
    LS2[rows2[ok2], conc.reshape(-1)[ok2]] = True
    LS4 &= ~LS2
    LS4s.append(LS4); LS2s.append(LS2)
LS4 = np.concatenate(LS4s, axis=1); LS2 = np.concatenate(LS2s, axis=1); del LS4s, LS2s
nS = LS4.shape[1]
LS4f = LS4.astype(np.float32)
print(f'spreads {len(spreads)} columns {nS}, candidates {nc}, line pool {npool} [{time.time()-t0:.1f}s]', flush=True)


def line_opp(i, js):
    for j in js:
        pj = P[j]
        pos = np.searchsorted(Csorted[i], pj); pos[pos >= Csorted.shape[1]] = 0
        if (Csorted[i][pos] == pj).any(): return False
    return True


def pts_opp_many(ids, js):
    if len(js) == 0: return np.ones(len(ids), bool)
    return (H.Bmat(cand[ids], cand[np.array(js)]) != 0).all(axis=1)


W = (1 << np.arange(62, dtype=np.int64))


def cost(xs, ls):
    k = len(xs)
    if k == 0: return 0
    tR = NR[xs].T.astype(np.int64) @ W[:k]
    tS = LS4[ls].T.astype(np.int64) @ W[:k]
    ex = LS2[ls].any(axis=0)
    ur, cr = np.unique(tR, return_counts=True)
    us, cs = np.unique(tS[~ex], return_counts=True)
    pos = np.searchsorted(us, ur); pos[pos >= len(us)] = 0
    have = np.where(us[pos] == ur, cs[pos], 0)
    return int(np.maximum(0, cr - have).sum())


def F(xs, ls): return len(xs) - cost(xs, ls)


def good_x(xs, skip=None, n=4):
    others = [x for j, x in enumerate(xs) if j != skip]
    ids = rng.integers(nc, size=a.sample)
    ids = ids[pts_opp_many(ids, others)]
    ids = np.array([i for i in ids if i not in others], dtype=np.int64)
    if len(ids) == 0: return []
    if others:
        cov = NRf[others].sum(axis=0)
        ov = NRf[ids] @ cov
        ids = ids[np.argsort(ov + rng.random(len(ids)) * 3)]
    return ids[:n].tolist()


def good_l(ls, skip=None, n=4):
    others = [l for j, l in enumerate(ls) if j != skip]
    ids = rng.integers(npool, size=a.sample)
    ids = [int(i) for i in ids if int(i) not in others]
    if others:
        cov = LS4f[others].sum(axis=0) + 3 * LS2[others].any(axis=0)
        ov = LS4f[ids] @ cov
        ids = [ids[i] for i in np.argsort(ov + rng.random(len(ids)) * 3)]
    out = []
    for i in ids:
        if line_opp(i, others): out.append(i)
        if len(out) >= n: break
    return out


xs, ls = [], []
cur = F(xs, ls); best = cur; it = 0; T = a.T
np.savez(os.path.join(a.outdir, 'best.npz'), X=cand[xs], L=pool[ls], R=R)
while time.time() - t0 < a.secs:
    it += 1
    u = rng.random(); props = []
    k = len(xs)
    if u < 0.2 or k == 0:
        for nx in good_x(xs, n=3):
            for nl in good_l(ls, n=3):
                props.append((xs + [nx], ls + [nl]))
    elif u < 0.27 and k > 1:
        j = int(rng.integers(k)); props.append((xs[:j] + xs[j + 1:], ls[:j] + ls[j + 1:]))
    else:
        j = int(rng.integers(k))
        if rng.random() < 0.5:
            for nx in good_x(xs, skip=j, n=a.m):
                xs3 = xs.copy(); xs3[j] = nx; props.append((xs3, ls))
        else:
            for nl in good_l(ls, skip=j, n=a.m):
                ls3 = ls.copy(); ls3[j] = nl; props.append((xs, ls3))
    if not props: continue
    scored = [(F(x3, l3), x3, l3) for x3, l3 in props]
    f2, xs2, ls2 = max(scored, key=lambda c: c[0])
    if f2 >= cur or rng.random() < np.exp((f2 - cur) / T):
        xs, ls, cur = xs2, ls2, f2
    if cur > best:
        best = cur
        np.savez(os.path.join(a.outdir, 'best.npz'), X=cand[xs], L=pool[ls], R=R)
        print(f'F={cur} (k={len(xs)}) it {it} [{time.time()-t0:.0f}s]', flush=True)
    if it % 500 == 0: print(f'  it {it} k={len(xs)} F {cur} best {best} [{time.time()-t0:.0f}s]', flush=True)
print('optimistic best F =', best, 'iterations', it, flush=True)
