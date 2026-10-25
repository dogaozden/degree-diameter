#!/usr/bin/env python3
"""Annealing for mirrored extensions, v6 (any q, including characteristic 2: point distances by BFS in the
incidence graph instead of the bilinear form; --hex, --rfile, --sfile): maximise F = k - deficit (deficit = base points dropped because their type
has too few spread lines).  Moves: add a pair, remove a pair, replace a point, replace a line; additions and
replacements are biased towards points whose R-neighbourhood overlaps little with the current ones and lines whose
spread neighbourhood overlaps little with the current lines, and the best of several proposals is taken.
usage: mirror_sa4.py SEED OUTDIR [--init STATE.npz] [--pool 20000] [--secs 1500] [--T 0.15]"""
import numpy as np, sys, os, time, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
ap = argparse.ArgumentParser(); ap.add_argument('seed', type=int); ap.add_argument('outdir')
ap.add_argument('--init', default=''); ap.add_argument('--pool', type=int, default=20000)
ap.add_argument('--secs', type=float, default=1500); ap.add_argument('--T', type=float, default=0.15)
ap.add_argument('--m', type=int, default=8); ap.add_argument('--cmax', type=int, default=10**6); ap.add_argument('--sample', type=int, default=150)
ap.add_argument('--rfile', default=SP + 'R756idx.npy'); ap.add_argument('--hex', default=SP + 'hex_q11.bin'); ap.add_argument('--sfile', default=SP + 'S_herm.npy')
a = ap.parse_args(); rng = np.random.default_rng(a.seed); os.makedirs(a.outdir, exist_ok=True)
t0 = time.time()
H = Hex(a.hex); N = H.N; q = H.q
R = np.load(a.rfile); nR = len(R); S = np.load(a.sfile); nS = len(S)
Sline = -np.ones(N, dtype=np.int64)
for j, l in enumerate(S): Sline[H.lp[l]] = j
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]; nc = len(cand)
# distance-4 relation by BFS (valid in every characteristic)
cpos = -np.ones(N, dtype=np.int64); cpos[cand] = np.arange(len(cand))
NR = np.zeros((len(cand), nR), bool)
for j, r in enumerate(R):
    p2, p4 = H.point_ball(int(r))
    ids = cpos[np.fromiter(p4, dtype=np.int64)]; ids = ids[ids >= 0]; NR[ids, j] = True
_ball = {}
def near_pts(x):
    """points at distance <= 4 from point x (excluding x)."""
    if x not in _ball:
        p2, p4 = H.point_ball(int(x)); _ball[x] = p2 | p4
    return _ball[x]
keep = NR.sum(1) <= a.cmax
cand = cand[keep]; NR = NR[keep]; nc = len(cand)
NRf = NR.astype(np.float32)
Sset = np.zeros(N, bool); Sset[S] = True
pool = rng.choice(np.nonzero(~Sset)[0], size=a.pool, replace=False)
init = None
if a.init:
    st = np.load(a.init); init = (st['X'], st['L'])
    pool = np.concatenate([st['L'], pool[~np.isin(pool, st['L'])]])
npool = len(pool)
P = H.lp[pool]; conc = Sline[P]
C = H.lp[H.pl[P]].reshape(npool, -1)
near = Sline[C]
LS4 = np.zeros((npool, nS), bool); LS2 = np.zeros((npool, nS), bool)
rows = np.repeat(np.arange(npool), near.shape[1]); ok = near.reshape(-1) >= 0
LS4[rows[ok], near.reshape(-1)[ok]] = True
rows2 = np.repeat(np.arange(npool), conc.shape[1]); ok2 = conc.reshape(-1) >= 0
LS2[rows2[ok2], conc.reshape(-1)[ok2]] = True
LS4 &= ~LS2
LS4f = LS4.astype(np.float32)
Csorted = np.sort(C, axis=1)
print(f'candidates {nc}, line pool {npool} [{time.time()-t0:.1f}s]', flush=True)


def line_opp(i, js):
    for j in js:
        pj = P[j]
        pos = np.searchsorted(Csorted[i], pj); pos[pos >= Csorted.shape[1]] = 0
        if (Csorted[i][pos] == pj).any(): return False
    return True


def pts_opp_many(ids, js):
    if len(js) == 0: return np.ones(len(ids), bool)
    bad = set()
    for j in js: bad |= near_pts(int(cand[j]))
    return np.array([int(cand[i]) not in bad for i in ids], dtype=bool)


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
    """n candidate points opposite to the others, chosen among a random sample by least R-overlap."""
    others = [x for j, x in enumerate(xs) if j != skip]
    ids = rng.integers(nc, size=a.sample)
    ids = ids[pts_opp_many(ids, others)]
    ids = np.array([i for i in ids if i not in others], dtype=np.int64)
    if len(ids) == 0: return []
    if others:
        cov = NRf[others].sum(axis=0)                 # how many current points each R point is near
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


if init is not None:
    cidx = {int(c): i for i, c in enumerate(cand)}
    xs = [cidx[int(x)] for x in init[0]]; ls = list(range(len(init[1])))
else:
    xs, ls = [], []
cur = F(xs, ls); best = cur; it = 0; T = a.T
np.savez(os.path.join(a.outdir, 'best.npz'), X=cand[xs], L=pool[ls], R=R)
print(f'k={len(xs)} initial F {cur}', flush=True)
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
        print(f'F={cur} (k={len(xs)}, deficit {len(xs) - cur}) it {it} [{time.time()-t0:.0f}s]', flush=True)
    if it % 500 == 0: print(f'  it {it} k={len(xs)} F {cur} best {best} [{time.time()-t0:.0f}s]', flush=True)
print('best F =', best, 'iterations', it)
