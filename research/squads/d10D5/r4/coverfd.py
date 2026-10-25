#!/usr/bin/env python3
"""coverfd.py: lns.cover with the FLAGDEL correction: for a flag i in FD (own edge p_i - l_i deleted) the point side
may not use x on l_i (route p - l - x needs the deleted edge) and the line side may not use lines M through p_i."""
import numpy as np, lns
N = lns.N; PTS = lns.PTS; LOF = lns.LOF; PM = lns.PM; LM = lns.LM
def cover(F, sig, hubadj, FD=(), listing=False):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    k = len(F); isfree = np.zeros(N, bool); isfree[F] = True
    isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
    tot = 0; unc = []
    for i, p in enumerate(F):
        l = int(sig[p]); mark = np.zeros(N, bool)
        okx = PM[p] & ~isfree
        if i in FD: okx[PTS[l]] = False
        xs = np.nonzero(okx)[0]; mark[PTS[sig[xs]].ravel()] = True
        for w in LOF[p]:
            if isfreeL[w]: continue
            z = sinv[w]; us = sinv[LOF[z]]; mark[us[~isfree[us]]] = True
        for j in range(k):
            if hubadj[i, j]: mark[PTS[sig[F[j]]]] = True
        opp = ~PM[p]; opp[p] = False
        bad = np.nonzero(opp & ~mark)[0]; tot += len(bad)
        if listing: unc += [(i, 0, int(t)) for t in bad]
        markl = np.zeros(N, bool)
        okM = LM[l] & ~isfreeL
        if i in FD: okM[LOF[p]] = False
        Ms = np.nonzero(okM)[0]; markl[LOF[sinv[Ms]].ravel()] = True
        for y in PTS[l]:
            if isfree[y]: continue
            zs = PTS[sig[y]]; zs = zs[~isfree[zs]]; markl[sig[zs]] = True
        for j in range(k):
            if hubadj[j, i]: markl[LOF[F[j]]] = True
        oppl = ~LM[l]; oppl[l] = False
        badl = np.nonzero(oppl & ~markl)[0]; tot += len(badl)
        if listing: unc += [(i, 1, int(t)) for t in badl]
    return (tot, unc) if listing else tot
def hubA(S, FD):
    hg = [int(x) for x in S['rows']['hubgraph']]; k = len(S['F']); A = np.zeros((k, k), bool)
    for e in range(0, len(hg), 2):
        a, b = hg[e], hg[e + 1]
        if (a % 3 < 2 or a // 3 in FD) and (b % 3 < 2 or b // 3 in FD): A[a // 3, b // 3] = True
    return A
if __name__ == '__main__':
    import sys
    S = lns.read_sol(sys.argv[1]); FD = set(int(x) for x in sys.argv[2].split())
    sig = S['sig']
    if len(sys.argv) > 3:
        tok = open(sys.argv[3]).read().split(); sig = np.array([int(x) for x in tok[7:7 + N]])
    A = hubA(S, FD) if S['H'] == 3 else S['hubadj']
    print('old', lns.cover(S['F'], sig, A), 'corrected', cover(S['F'], sig, A, FD, listing=True))
