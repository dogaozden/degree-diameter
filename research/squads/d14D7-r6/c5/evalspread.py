#!/usr/bin/env python3
"""Score a fixed configuration (X, L) of the mirror construction against several spreads T (dual ovoids).
Same cost as mirror_sa4.py: F = k - sum_type max(0, #R-points of type - #usable T-lines of type).
usage: evalspread.py STATE.npz [T.npy ...]   (default: S_herm and all saved S(n) in scratchpad r6_c5/spreads/)"""
import numpy as np, sys, os, glob, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
H = Hex(SP + 'hex_q11.bin'); N = H.N; lp = H.lp; q = 11


def line_types(T, Ls):
    """LS2[j, i]: T-line i concurrent with L_j; LS4[j, i]: T-line i at distance 4 from L_j."""
    T = np.asarray(T); cover = -np.ones(N, dtype=np.int64)
    cover[lp[T].ravel()] = np.repeat(np.arange(len(T)), q + 1)
    k = len(Ls); LS2 = np.zeros((k, len(T)), bool); LS4 = np.zeros((k, len(T)), bool)
    for j, l in enumerate(Ls):
        pts = lp[l]
        conc = cover[pts]; conc = conc[conc >= 0]; LS2[j, conc] = True
        near = cover[lp[H.pl[pts]].ravel()]; near = near[near >= 0]; LS4[j, near] = True
    LS4 &= ~LS2
    return LS2, LS4


def score(R, Xs, Ls, T):
    """returns (F, cost, number of L_j lying in T, number of excluded T-lines)."""
    T = np.asarray(T); k = len(Xs)
    inT = np.isin(np.asarray(Ls), T).sum()
    NR = (H.Bmat(np.asarray(Xs), np.asarray(R)) == 0)                 # k x |R|
    W = (1 << np.arange(k, dtype=np.int64))
    tR = NR.T.astype(np.int64) @ W
    LS2, LS4 = line_types(T, Ls)
    ex = LS2.any(axis=0)
    tS = LS4.T.astype(np.int64) @ W
    ur, cr = np.unique(tR, return_counts=True)
    us, cs = np.unique(tS[~ex], return_counts=True)
    pos = np.searchsorted(us, ur); pos[pos >= len(us)] = 0
    have = np.where(us[pos] == ur, cs[pos], 0)
    cost = int(np.maximum(0, cr - have).sum())
    return k - cost, cost, int(inT), int(ex.sum())


if __name__ == '__main__':
    st = np.load(sys.argv[1]); R = st['R']; Xs = st['X']; Ls = st['L']
    files = sys.argv[2:] or ([SP + 'S_herm.npy'] + sorted(glob.glob(SP + 'r6_c5/spreads/T_*.npy')))
    res = []
    for f in files:
        T = np.load(f)
        F, cost, inT, nex = score(R, Xs, Ls, T)
        res.append((F, os.path.basename(f)))
        print(f'{os.path.basename(f):24s} F={F:3d} cost={cost:3d} L-in-T={inT} excluded={nex}', flush=True)
    print('max F over spreads:', max(res)[0], 'mean', round(sum(r[0] for r in res) / len(res), 2))
