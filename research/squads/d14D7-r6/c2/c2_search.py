#!/usr/bin/env python3
"""c2 (round d14D7-r6): coordinate descent with exact best responses over random samples of 20,000 candidate points and
20,000 lines per step (plus the current element), for the mirrored-extension selection problem.
State: k pairs (x_j, L_j).  R-type of r = bits j with d(r, x_j) = 4.  S-type of spread line s = bits j with
d(s, L_j) = 4; spread lines concurrent with some L_j are unusable.  D = sum_t max(0, #R of type t - #usable S of
type t) (= number of dropped base points), F = k - D.  Coordinate steps: best x_j for fixed others (over a sample
of candidates), best L_j for fixed others (over a sample of lines), both exact on the sample.
Iterated local search at target k = best_F + 1.
usage: c2_search.py [--init STATE.npz] [--secs S] [--seed N] [--sx 20000] [--sl 20000]"""
import numpy as np, sys, os, time, argparse
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
WD = SP + 'r6_c2/'
os.makedirs(WD, exist_ok=True)
ap = argparse.ArgumentParser()
ap.add_argument('--init', default='/home/user/degree-diameter/research/cell147/mirror/configs/state_k11_sa4.npz')
ap.add_argument('--out', default=WD + 'best.npz')
ap.add_argument('--secs', type=float, default=900)
ap.add_argument('--seed', type=int, default=1)
ap.add_argument('--sx', type=int, default=20000)
ap.add_argument('--sl', type=int, default=20000)
ap.add_argument('--ils', type=int, default=40)
a = ap.parse_args()
rng = np.random.default_rng(a.seed)
T0 = time.time()
def log(*x): print(f'[{time.time()-T0:7.1f}s]', *x, flush=True)

H = Hex(SP + 'hex_q11.bin'); N = H.N
R = np.load(SP + 'R756idx.npy'); S = np.load(SP + 'S_herm.npy'); nS = len(S)
Sline_pt = -np.ones(N, np.int64)
for j, l in enumerate(S): Sline_pt[H.lp[l]] = j
inS = np.zeros(N, bool); inS[S] = True
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]; ncand = len(cand)
posof = -np.ones(N, np.int64); posof[cand] = np.arange(ncand)


def gather(ptr, idx, ids):
    st = ptr[ids]; ln = ptr[ids + 1] - st
    tot = int(ln.sum())
    rows = np.repeat(np.arange(len(ids), dtype=np.int64), ln)
    offs = np.arange(tot, dtype=np.int64) - np.repeat(np.cumsum(ln) - ln, ln)
    return rows, idx[np.repeat(st, ln) + offs]


def line_lists():
    A_ptr = np.zeros(N + 1, np.int64); E_ptr = np.zeros(N + 1, np.int64)
    A_list, E_list = [], []; ta = te = 0; CH = 4000
    for s0 in range(0, N, CH):
        lines = np.arange(s0, min(N, s0 + CH)); c = len(lines)
        P = H.lp[lines]
        near = Sline_pt[H.lp[H.pl[P]].reshape(c, -1)]
        conc = Sline_pt[P]
        LS2 = np.zeros((c, nS), bool)
        r2, c2 = np.nonzero(conc >= 0); LS2[r2, conc[r2, c2]] = True
        LS4 = np.zeros((c, nS), bool)
        rr, cc = np.nonzero(near >= 0); LS4[rr, near[rr, cc]] = True
        LS4 &= ~LS2
        ra, sa = np.nonzero(LS4); re, se = np.nonzero(LS2)
        A_list.append(sa.astype(np.int16)); E_list.append(se.astype(np.int16))
        ca = np.bincount(ra, minlength=c); ce = np.bincount(re, minlength=c)
        A_ptr[s0 + 1:s0 + c + 1] = ta + np.cumsum(ca); E_ptr[s0 + 1:s0 + c + 1] = te + np.cumsum(ce)
        ta += int(ca.sum()); te += int(ce.sum())
    return A_ptr, np.concatenate(A_list), E_ptr, np.concatenate(E_list)


cache = WD + 'lists.npz'
if os.path.exists(cache) and os.path.exists(WD + 'NR.npy'):
    z = np.load(cache); NR = np.load(WD + 'NR.npy')
    A_ptr, A_idx, E_ptr, E_idx = z['A_ptr'], z['A_idx'], z['E_ptr'], z['E_idx']
else:
    NR = np.zeros((ncand, len(R)), bool)
    for s0 in range(0, ncand, 4096):
        NR[s0:s0 + 4096] = H.Bmat(cand[s0:s0 + 4096], R) == 0
    np.save(WD + 'NR.npy', NR)
    A_ptr, A_idx, E_ptr, E_idx = line_lists()
    np.savez(cache, A_ptr=A_ptr, A_idx=A_idx, E_ptr=E_ptr, E_idx=E_idx)
rr_, cc_ = np.nonzero(NR)
NRp = np.zeros(ncand + 1, np.int64); NRp[1:] = np.cumsum(np.bincount(rr_, minlength=ncand)); NRi = cc_.astype(np.int64)
del rr_, cc_
log(f'candidates {ncand}, lines {N}, A-entries {len(A_idx)}, E-entries {len(E_idx)}')


def line_sets(L):
    return A_idx[A_ptr[L]:A_ptr[L + 1]].astype(np.int64), E_idx[E_ptr[L]:E_ptr[L + 1]].astype(np.int64)


def state_stats(Xp, Lg):
    k = len(Lg); bits = np.left_shift(1, np.arange(k, dtype=np.int64))
    mR = (NR[np.array(Xp)].astype(np.int64) * bits[:, None]).sum(0)
    mS = np.zeros(nS, np.int64); unus = np.zeros(nS, bool)
    for j, L in enumerate(Lg):
        aa, ee = line_sets(L); mS[aa] |= bits[j]; unus[ee] = True
    return mR, mS, unus


def deficit(mR, mS, unus, k):
    K = 1 << k
    return int(np.maximum(np.bincount(mR, minlength=K) - np.bincount(mS[~unus], minlength=K), 0).sum())


def bad_lines(Lg_others):
    bad = inS.copy()
    for L in Lg_others:
        d2, d4 = H.line_ball(L)
        bad[list(d2)] = True; bad[list(d4)] = True; bad[L] = True
    return bad


def x_step(Xp, Lg, j, mR, mS, unus):
    """costs of all candidate points for slot j (others fixed); exact."""
    k = len(Lg); K = 1 << k; bit = 1 << j
    cS = np.bincount(mS[~unus], minlength=K)
    mb = mR & ~bit
    Bz = np.bincount(mb, minlength=K)
    Dbase = int(np.maximum(Bz - cS, 0).sum())
    others = [Xp[i] for i in range(k) if i != j]
    pool = rng.choice(ncand, size=min(a.sx, ncand), replace=False)
    pool = np.unique(np.append(pool, Xp[j]))
    if others:
        ok = (H.Bmat(cand[pool], cand[np.array(others)]) != 0).all(1)
        pool = pool[ok]
    P = len(pool)
    rows, rv = gather(NRp, NRi, pool)
    m0 = mb[rv]
    keys = rows * K + m0
    uk, cnt = np.unique(keys, return_counts=True)
    urow = uk // K; um = uk % K
    aa = cnt.astype(np.int64)
    new = np.maximum(Bz[um] - aa - cS[um], 0) + np.maximum(aa - cS[um | bit], 0)
    old = np.maximum(Bz[um] - cS[um], 0)
    costs = Dbase + np.rint(np.bincount(urow, weights=(new - old).astype(float), minlength=P)).astype(np.int64)
    return pool, costs


def L_step(Xp, Lg, j, mR):
    """costs of candidate lines for slot j (others fixed); exact. Current line is always in the pool."""
    k = len(Lg); K = 1 << k; bit = 1 << j
    cR = np.bincount(mR, minlength=K)
    mSo = np.zeros(nS, np.int64); unso = np.zeros(nS, bool)
    for i, L in enumerate(Lg):
        if i == j: continue
        aa, ee = line_sets(L); mSo[aa] |= (1 << i); unso[ee] = True
    G = np.bincount(mSo[~unso], minlength=K)
    D_L0 = int(np.maximum(cR - G, 0).sum())
    bad = bad_lines([L for i, L in enumerate(Lg) if i != j])
    pool = rng.choice(N, size=a.sl, replace=False)
    pool = np.unique(np.append(pool, Lg[j]))
    pool = pool[~bad[pool]]
    P = len(pool)
    ra, va = gather(A_ptr, A_idx, pool); va = va.astype(np.int64)
    keep = ~unso[va]; ra = ra[keep]; va = va[keep]
    re, ve = gather(E_ptr, E_idx, pool); ve = ve.astype(np.int64)
    keep = ~unso[ve]; re = re[keep]; ve = ve[keep]
    rows = np.concatenate([ra, re]); bins = np.concatenate([mSo[va], mSo[ve]])
    isA = np.concatenate([np.ones(len(ra)), np.zeros(len(re))])
    keys = rows * K + bins
    uk, inv = np.unique(keys, return_inverse=True)
    t_cnt = np.bincount(inv, minlength=len(uk)).astype(np.int64)
    a_cnt = np.rint(np.bincount(inv, weights=isA, minlength=len(uk))).astype(np.int64)
    urow = uk // K; um = uk % K
    g0 = cR[um] - G[um]
    d0 = np.maximum(g0 + t_cnt, 0) - np.maximum(g0, 0)
    m1 = um | bit
    d1 = np.maximum(cR[m1] - a_cnt, 0) - np.maximum(cR[m1], 0)
    costs = D_L0 + np.rint(np.bincount(urow, weights=(d0 + d1).astype(float), minlength=P)).astype(np.int64)
    return pool, costs


def pick(pool, costs):
    m = costs.min(); return m, int(rng.choice(pool[costs == m]))


def descend(Xp, Lg, max_sweeps=40):
    k = len(Lg)
    for sw in range(max_sweeps):
        improved = False
        for j in rng.permutation(k):
            mR, mS, unus = state_stats(Xp, Lg); D = deficit(mR, mS, unus, k)
            pool, costs = x_step(Xp, Lg, j, mR, mS, unus)
            m, newx = pick(pool, costs)
            if m < D: improved = True
            if m <= D: Xp[j] = newx
            mR, mS, unus = state_stats(Xp, Lg); D = deficit(mR, mS, unus, k)
            pool, costs = L_step(Xp, Lg, j, mR)
            m, newL = pick(pool, costs)
            if m < D: improved = True
            if m <= D: Lg[j] = newL
        if not improved: break
    mR, mS, unus = state_stats(Xp, Lg)
    return deficit(mR, mS, unus, k)


def random_pair(Xp, Lg):
    """random allowed (x, L) to append or to replace slot (Xp, Lg as lists, slot index not used here)."""
    others = list(Xp)
    while True:
        pool = rng.choice(ncand, size=3000, replace=False)
        if others:
            pool = pool[(H.Bmat(cand[pool], cand[np.array(others)]) != 0).all(1)]
        if len(pool): x = int(rng.choice(pool)); break
    bad = bad_lines(Lg)
    while True:
        Ls = rng.choice(N, size=2000, replace=False); Ls = Ls[~bad[Ls]]
        if len(Ls): L = int(rng.choice(Ls)); break
    return x, L


def save(Xp, Lg, path):
    np.savez(path, X=cand[np.array(Xp)], L=np.array(Lg, np.int64), R=R)


st = np.load(a.init)
Xp = [int(posof[p]) for p in st['X']]; Lg = [int(l) for l in st['L']]
assert min(Xp) >= 0
k0 = len(Xp)
mR, mS, unus = state_stats(Xp, Lg); D0 = deficit(mR, mS, unus, k0)
log(f'init k={k0} D={D0} F={k0 - D0}')
best_F = k0 - D0; best = (list(Xp), list(Lg)); save(*best, a.out)
# sanity: the x/L steps must reproduce the current cost at the current element
pool, costs = x_step(Xp, Lg, 0, *state_stats(Xp, Lg)); log('x-step sanity: cost at current x', costs[pool == Xp[0]], 'min', costs.min())
pool, costs = L_step(Xp, Lg, 0, state_stats(Xp, Lg)[0]); log('L-step sanity: cost at current L', costs[pool == Lg[0]], 'min', costs.min())

while time.time() - T0 < a.secs:
    kt = best_F + 1
    Xs, Ls = list(best[0]), list(best[1])
    x, L = random_pair(Xs, Ls); Xs.append(x); Ls.append(L)
    D = descend(Xs, Ls)
    log(f'target k={kt}: start D={D}')
    it = 0
    while D > 0 and it < a.ils and time.time() - T0 < a.secs:
        Xn, Ln = list(Xs), list(Ls)
        j = int(rng.integers(kt))
        if rng.random() < 0.5:
            others = Xn[:j] + Xn[j + 1:]
            pool = rng.choice(ncand, size=3000, replace=False)
            pool = pool[(H.Bmat(cand[pool], cand[np.array(others)]) != 0).all(1)] if others else pool
            Xn[j] = int(rng.choice(pool))
        else:
            bad = bad_lines(Ln[:j] + Ln[j + 1:])
            Ls_ = rng.choice(N, size=2000, replace=False); Ls_ = Ls_[~bad[Ls_]]
            Ln[j] = int(rng.choice(Ls_))
        Dn = descend(Xn, Ln)
        it += 1
        if Dn <= D:
            Xs, Ls, D = Xn, Ln, Dn
        if D == 0: break
    log(f'target k={kt}: ILS iters {it}, best D {D}')
    if D == 0:
        best = (list(Xs), list(Ls)); best_F = kt; save(*best, a.out)
        log(f'NEW BEST F={best_F} (k={kt}, D=0) saved {a.out}')
    else:
        # no D=0 found at this k: keep trying with a fresh start from the best state
        pass
log(f'done: best F={best_F}')
