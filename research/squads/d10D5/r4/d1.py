#!/usr/bin/env python3
"""d1.py X.sol: per-flag counts of FLAGDEL "D1" holes (mirror of dmhub2.c d1_cost) and ordinary coverage holes."""
import sys, numpy as np, lns
N = lns.N; PTS = lns.PTS; LOF = lns.LOF; PM = lns.PM; LM = lns.LM
def d1(F, sig, per=False):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    isfree = np.zeros(N, bool); isfree[F] = True; isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
    out = []
    for i, p in enumerate(F):
        l = int(sig[p]); cp = cl = 0; holes = []
        for L in LOF[p]:
            if L == l or isfreeL[L]: continue
            v = int(sinv[L])
            if v in PTS[l]: continue
            mark = np.zeros(N, bool)
            xs = np.nonzero(PM[v] & ~isfree)[0]; mark[PTS[sig[xs]].ravel()] = True
            for L2 in LOF[v]:
                if isfreeL[L2]: continue
                z = sinv[L2]; us = sinv[LOF[z]]; mark[us[~isfree[us]]] = True
            for u in PTS[l]:
                if u == p: continue
                if isfree[u] and PM[u, v]: continue
                if not mark[u]: cp += 1; holes.append(('pt', v, int(u)))
        for y in PTS[l]:
            if y == p or isfree[y]: continue
            sl = int(sig[y])
            if sl in LOF[p]: continue
            markl = np.zeros(N, bool)
            Ms = np.nonzero(LM[sl] & ~isfreeL)[0]; markl[LOF[sinv[Ms]].ravel()] = True
            for y2 in PTS[sl]:
                if isfree[y2]: continue
                zs = PTS[sig[y2]]; zs = zs[~isfree[zs]]; markl[sig[zs]] = True
            for t in LOF[p]:
                if t == l: continue
                if isfreeL[t] and LM[t, sl]: continue
                if not markl[t]: cl += 1; holes.append(('ln', sl, int(t)))
        out.append((p, l, cp, cl, holes))
    return out
if __name__ == '__main__':
    S = lns.read_sol(sys.argv[1]); F = S['F']; sig = S['sig']
    c, unc = lns.cover(F, sig, S['hubadj'], listing=True)
    import collections; cu = collections.Counter(i for i, _, _ in unc)
    tot = 0
    for i, (p, l, cp, cl, h) in enumerate(d1(F, sig)):
        print('flag', i, p, l, 'D1 pts', cp, 'D1 lines', cl, 'coverage holes', cu[i]); tot += cp + cl
    print('total D1', tot, 'coverage', c)
