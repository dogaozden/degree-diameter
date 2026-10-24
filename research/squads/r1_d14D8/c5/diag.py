"""Diagnostics: exact coverage of the lift from one source point a (walks of length 7, all residues), grouped by
hexagon distance d(a, line). Usage: python3 diag.py FILE_OR_none m seedF seedM hexmode psimode src [tag]"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d14D8/c5')
import mkd
from hexlib import dist_from_point

def read_edges(fn):
    with open(fn) as f:
        N, _, m = map(int, f.readline().split())
        E = np.loadtxt(f, dtype=np.int64, ndmin=2)
    return N, m, E

def coverage(N, m, E, a, D=8):
    p_ = E[:, 0]; l_ = E[:, 1]; v_ = E[:, 2] % m
    IDX = (np.arange(m)[None, :] - v_[:, None]) % m        # newL[l, h] |= Rp[p, (h - v) % m]
    ordL = np.argsort(l_, kind='stable'); startsL = np.searchsorted(l_[ordL], np.arange(N))
    ordP = np.argsort(p_, kind='stable'); startsP = np.searchsorted(p_[ordP], np.arange(N))
    Rp = np.zeros((N, m), bool); Rp[a, 0] = True
    cur_points = True
    for step in range(D - 1):
        if cur_points:
            contrib = Rp[p_[:, None], IDX]                   # (E, m)
            Rl = np.maximum.reduceat(contrib[ordL], startsL, axis=0)
            cur_points = False
        else:
            contrib = Rl[l_[:, None], (np.arange(m)[None, :] + v_[:, None]) % m]   # newP[p,g] |= Rl[l, (g + v)%m]
            Rp = np.maximum.reduceat(contrib[ordP], startsP, axis=0)
            cur_points = True
    return Rl if not cur_points else Rp

if __name__ == '__main__':
    fn = sys.argv[1]; m_arg = int(sys.argv[2]); a = int(sys.argv[3])
    N, m, E = read_edges(fn)
    R = coverage(N, m, E, a)
    unc = ~R
    N_, LP, PL, coord = mkd.get_N_LP_PL_coord()
    dp, dl = dist_from_point(a, LP, PL, maxd=6)
    print('source', a, 'uncovered total', unc.sum(), 'lines with any uncovered', (unc.any(axis=1)).sum())
    for d in (1, 3, 5):
        sel = dl == d
        print(f'  d={d}: lines {sel.sum()}  uncovered {unc[sel].sum()}  per-level {unc[sel].sum(axis=0).tolist()}')
    # residues covered per distance class: average number of distinct residues
    for d in (1, 3, 5):
        sel = dl == d
        print(f'  d={d}: mean covered levels {R[sel].sum(axis=1).mean():.3f}, min {R[sel].sum(axis=1).min()}')
