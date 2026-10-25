#!/usr/bin/env python3
"""c7 (wildcard): weighted assignment (Hungarian) local search for sigma on the non-freed points.
Each iteration linearises the coverage of the current state: a pair (x, L) gains every uncovered linear target it covers
(point side: x collinear with freed p and u on L; line side: y on m and sigma(y) concurrent with freed line l), and
moving x away loses the targets x alone covers.  scipy linear_sum_assignment solves the full 390 x 390 permutation for
that linear score (all points at once).  Exact cover (lns.cover) decides acceptance; uncovered targets get breakout
weights each iteration.  usage: hung.py IN.sol OUTPREFIX   env SECS, SEED, TEMP.
"""
import sys, os, time, math, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import numpy as np
import lns
from scipy.optimize import linear_sum_assignment

N = lns.N; PTS = lns.PTS; LOF = lns.LOF; PM = lns.PM; LM = lns.LM; INC = lns.INC.astype(np.int64)
S0 = lns.read_sol(sys.argv[1]); out = sys.argv[2]
F = S0['F']; hubadj = S0['hubadj']; k = len(F)
F_arr = np.array(F)
isfree = np.zeros(N, bool); isfree[F] = True
sig0 = S0['sig'].copy()
isfreeL = np.zeros(N, bool); isfreeL[sig0[F]] = True
var_pts = np.nonzero(~isfree)[0]; var_lines = np.nonzero(~isfreeL)[0]
Lf = sig0[F]  # freed lines

# constant (per freed flag) structure
pm_rows = np.array([PM[p] for p in F])                         # k x N, collinear with p
opp_pt = ~pm_rows; opp_pt[np.arange(k), F_arr] = False          # opposite points (target side 0)
a_pt = pm_rows & ~isfree[None, :]                               # variable collinear points of p
ell = np.array([LM[l] for l in Lf]) & ~isfreeL[None, :]         # line side candidate lines e_i(M)
opp_ln = ~np.array([LM[l] for l in Lf]); opp_ln[np.arange(k), Lf] = False
ell_full = np.array([LM[l] for l in Lf])
ell_full[np.arange(k), Lf] = False


def state(sig):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    INCS = INC[:, sig]                                          # INCS[u, x] = u on sig(x)
    lin_pt = a_pt.astype(np.int64) @ INCS.T                     # k x N (point targets)
    E = (ell[:, sig] & ~isfree[None, :]).astype(np.int64)       # E[i,y]: sig(y) concurrent with l_i, y variable
    lin_ln = E @ INC                                            # k x N (line targets)
    HP = np.zeros((k, N), bool); HL = np.zeros((k, N), bool)
    for i in range(k):
        for j in range(k):
            if hubadj[i, j]: HP[i, PTS[sig[F[j]]]] = True
            if hubadj[j, i]: HL[i, LOF[F[j]]] = True
    qp = np.zeros((k, N), bool); ql = np.zeros((k, N), bool)
    for i, p in enumerate(F):
        for w in LOF[p]:
            if isfreeL[w]: continue
            z = sinv[w]; us = sinv[LOF[z]]; qp[i, us[~isfree[us]]] = True
        l = sig[p]
        for y in PTS[l]:
            if isfree[y]: continue
            zs = PTS[sig[y]]; zs = zs[~isfree[zs]]; ql[i, sig[zs]] = True
    cp = (lin_pt > 0) | HP | qp
    cl = (lin_ln > 0) | HL | ql
    up = opp_pt & ~cp; ul = opp_ln & ~cl
    cost = int(up.sum() + ul.sum())
    return dict(lin_pt=lin_pt, lin_ln=lin_ln, HP=HP, HL=HL, qp=qp, ql=ql, up=up, ul=ul, cost=cost)


def score_matrix(sig, st, Wpt, Wln):
    # gains (x, L): targets uncovered now that (x, L) would linearly cover
    bp = (Wpt * st['up']) @ INC                                    # k x N over lines
    G = a_pt.astype(np.float64).T @ bp                              # N x N  (x, L)
    d = (Wln * st['ul']) @ INC.T                                    # k x N over points y
    G += d.T @ ell.astype(np.float64)                               # N x N  (y, M)
    # losses: x leaves its line, targets it alone covers
    solo_p = (st['lin_pt'] == 1) & ~st['HP'] & ~st['qp'] & opp_pt
    bl1 = (Wpt * solo_p) @ INC                                      # k x N over lines
    Lo = (a_pt * bl1[:, sig]).sum(axis=0).astype(np.float64)        # per point x: sum_i a_i(x) bl1[i, sig x]
    solo_l = (st['lin_ln'] == 1) & ~st['HL'] & ~st['ql'] & opp_ln
    W2 = (Wln * solo_l) @ INC.T                                     # k x N over points
    Lo += (ell[:, sig] * W2).sum(axis=0)
    S = G - Lo[:, None]
    EPS = float(os.environ.get('EPS', 0.01))          # moving a point costs a little: ties keep the current line
    S = S - EPS
    S[np.arange(N), sig] = G[np.arange(N), sig]
    return S


def main():
    secs = float(os.environ.get('SECS', 600)); seed = int(os.environ.get('SEED', 1))
    T = float(os.environ.get('TEMP', 0.3)); bump = float(os.environ.get('BUMP', 1.0))
    rng = random.Random(seed); np.random.seed(seed)
    sig = sig0.copy()
    cost_ref, _ = lns.cover(F, sig, hubadj, listing=True)
    st = state(sig)
    print('start exact', cost_ref, 'state', st['cost'], flush=True)
    assert cost_ref == st['cost']
    Wpt = np.ones((k, N)); Wln = np.ones((k, N))
    best = st['cost']; cur = st['cost']; t0 = time.time(); it = 0; acc = 0
    while time.time() - t0 < secs and cur > 0:
        it += 1
        st = state(sig)
        Wpt += bump * st['up']; Wln += bump * st['ul']        # breakout: uncovered targets get heavier
        S = score_matrix(sig, st, Wpt, Wln)
        Ssub = S[np.ix_(var_pts, var_lines)]
        r, c = linear_sum_assignment(Ssub, maximize=True)
        new = sig.copy(); new[var_pts[r]] = var_lines[c]
        c2, _ = lns.cover(F, new, hubadj, listing=True)
        moved = int((new != sig).sum())
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            sig = new; cur = c2; acc += 1
            if cur < best:
                best = cur; lns.write_sol(out + '.sol', S0, sig, cur)
                print('it %d new best %d (moved %d)' % (it, best, moved), flush=True)
        if it % 50 == 0:
            print('it %d cur %d best %d acc %d weight_max %.0f t %.0fs' % (it, cur, best, acc, Wpt.max(), time.time() - t0), flush=True)
    lns.write_sol(out + '.final.sol', S0, sig, cur)
    print('final cur', cur, 'best', best, 'iters', it, flush=True)


if __name__ == '__main__':
    main()
