#!/usr/bin/env python3
"""c4: coverage model for freed flags (p, sigma(p)) of the DM lift of W(7).

Coset-1 walks of length 4 from a freed point p (no jump at p or at freed points, none at freed lines):
  (i)   p - L - x - sigma(x) - u, x in P(p)\\{p} non-freed, u opposite p (u on sigma(x))
  (ii)  p - w - sigma^-1(w) - sigma(u) - u, w non-freed line through p, u non-freed opposite p
  (iii) p -> a_p (point-side hub) -> c_j (line-side hub of freed flag j) -> (l_j) -> u on l_j,
        needs hub edge HG[i][j] (point-side hub of i ~ line-side hub of j)
Dually for freed lines l = sigma(p), coset-2 walks (the coset-1 ones are automatic via {4} except <=8 lines):
  (i*)  l - x - M - y - m, M concurrent with l, M non-freed, y = sigma^-1(M), m opposite l, m through y
  (ii*) l - x - sigma(x) - y - sigma(y), x in l non-freed, y in sigma(x) non-freed, m = sigma(y) opposite l
  (iii*) l -> c_i -> a_j -> p_j -> m through p_j, needs HG[j][i]
Non-freed target coset-2 (points) and coset-1 (lines) are automatic; freed targets are not modelled here.
"""
import sys, os, math, time, random
from collections import deque
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from gq import load, perp, lperp
import numpy as np

GQ = '/home/user/degree-diameter/research/d10D7/gq/gq_q7.bin'
STATES = '/home/user/degree-diameter/research/squads/d10D5/r3/states/'
q, N, LINES, LOF = load(GQ)
PTS = np.array(LINES, dtype=np.int64)
LPT = np.array(LOF, dtype=np.int64)
PM = np.zeros((N, N), bool)   # PM[p,u]: u == p or u collinear with p
LM = np.zeros((N, N), bool)   # LM[l,m]: m == l or m concurrent with l
for a in range(N):
    for u in perp(LINES, LOF, a): PM[a, u] = True
    for m in lperp(LINES, LOF, a): LM[a, m] = True

def read_sol(name):
    r = {}
    for ln in open(STATES + name + '.sol'):
        t = ln.split()
        if t: r.setdefault(t[0], t[1:])
    F = list(map(int, r['free'])); sig = list(map(int, r['sigma']))
    H = int(r['dmhub'][3]); hg = list(map(int, r.get('hubgraph', [])))
    pairs = [(hg[e], hg[e + 1]) for e in range(0, len(hg), 2)]
    return dict(F=F, sig=sig, H=H, pairs=pairs, mv0=list(map(int, r['mv0'])), mv1=list(map(int, r['mv1'])),
                nu=list(map(int, r['nu'])))

def hub_matrix(k, pairs, H=2):
    """HG[i][j] = True if point-side hub of flag i is adjacent to line-side hub of flag j"""
    HG = np.zeros((k, k), bool)
    for a, b in pairs: HG[a // H, b // H] = True
    return HG

def core(F, sig, HG=None):
    """Return per freed flag: boolean masks of uncovered non-freed opposite points (coset-1 model)
    and uncovered non-freed opposite lines (dual coset-2 model), plus capacity counts."""
    k = len(F); sig = np.asarray(sig, dtype=np.int64)
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    Fa = np.asarray(F, dtype=np.int64); fz = np.zeros(N, bool); fz[Fa] = True
    Ls = sig[Fa]; lz = np.zeros(N, bool); lz[Ls] = True
    out = []
    for i in range(k):
        p = F[i]; l = int(Ls[i])
        # ---- points: (i), (ii), (iii)
        Oo = ~PM[p] & ~fz
        cov = np.zeros(N, bool)
        A = np.nonzero(PM[p])[0]; A = A[A != p]; xs = A[~fz[A]]
        cap_i = int(np.count_nonzero(Oo[sig[xs]][:0]) ) # placeholder (replaced below)
        inc_i = PTS[sig[xs]]                                  # (x, 8 points of sigma(x))
        cov[inc_i.ravel()] = True
        cap_i = int(np.count_nonzero(~PM[p][inc_i] & ~fz[inc_i]))   # incidences (i) landing on non-freed opposite pts
        S1 = LPT[p]; S1 = S1[~lz[S1]]; x0 = sinv[S1]
        us_all = sinv[LPT[x0].ravel()]
        ok2 = ~fz[us_all] & ~PM[p][us_all]
        cap_ii = int(np.count_nonzero(ok2))
        cov[us_all[ok2]] = True
        cap_iii = 0
        if HG is not None:
            for j in range(k):
                if j != i and HG[i, j]:
                    pl = PTS[int(Ls[j])]; cov[pl] = True; cap_iii += 7
        unc_p = Oo & ~cov
        # ---- lines (dual): (i*), (ii*), (iii*)
        Lo = ~LM[l] & ~lz
        covl = np.zeros(N, bool)
        Ms = np.nonzero(LM[l])[0]; Ms = Ms[(Ms != l) & ~lz[Ms]]
        ys = sinv[Ms]
        thr = LPT[ys].ravel()
        covl[thr] = True
        cap_is = int(np.count_nonzero(~LM[l][thr] & ~lz[thr]))
        xs2 = PTS[l]; xs2 = xs2[~fz[xs2]]
        Mx = sig[xs2]; ys2 = PTS[Mx].ravel(); ys2 = ys2[~fz[ys2]]
        mm = sig[ys2]; ok3 = ~LM[l][mm]
        cap_iis = int(np.count_nonzero(ok3))
        covl[mm[ok3]] = True
        cap_iiis = 0
        if HG is not None:
            for j in range(k):
                if j != i and HG[j, i]:
                    th = LPT[F[j]]; covl[th] = True; cap_iiis += 7
        unc_l = Lo & ~covl
        out.append(dict(p=p, l=l, unc_p=unc_p, unc_l=unc_l, cap_i=cap_i, cap_ii=cap_ii, cap_iii=cap_iii,
                        cap_is=cap_is, cap_iis=cap_iis, cap_iiis=cap_iiis,
                        ncov_p=int(np.count_nonzero(Oo & cov)), ncov_l=int(np.count_nonzero(Lo & covl))))
    return out

def crowding(F, sig):
    k = len(F); rows = []
    Ls = [sig[p] for p in F]
    for i, p in enumerate(F):
        kap = sum(1 for j, f in enumerate(F) if j != i and PM[p][f])          # freed points collinear with p
        conc = sum(1 for j, m in enumerate(Ls) if j != i and LM[Ls[i]][m])    # freed lines concurrent with l_i
        # mu: lines M through p, M != sigma(p), whose preimage is a non-freed point collinear with p
        mu = 0
        for M in LOF[p]:
            if M == Ls[i]: continue
            x = None
            # sigma^-1(M)
            x = sinv_global[M]
            if x not in F and PM[p][x] and x != p: mu += 1
        rows.append((kap, mu, conc))
    return rows

sinv_global = None

def bfs_all(F, sig, mv0, mv1, nu, pairs, H=2, sources=None):
    base = 2 * N * 6
    fs = set(F); k = len(F)
    nv = base + 2 * H * k
    adj = [[] for _ in range(nv)]
    def add(a, b): adj[a].append(b); adj[b].append(a)
    for l in range(N):
        for kk, p in enumerate(LINES[l]):
            v = nu[l * 8 + kk]
            for h in range(6): add(p * 6 + h, (N + l) * 6 + (h + v) % 6)
    for p in range(N):
        if p in fs: continue
        for h in range(6):
            add(p * 6 + h, (N + sig[p]) * 6 + (h + mv0[p]) % 6)
            add(p * 6 + h, (N + sig[p]) * 6 + (h + mv1[p]) % 6)
    hub = base
    for i, p in enumerate(F):
        for x in (p, N + sig[p]):
            for _ in range(H):
                for h in range(6): add(hub, x * 6 + h)
                hub += 1
    for a, b in pairs:
        add(base + (a // H) * 2 * H + a % H, base + (b // H) * 2 * H + H + b % H)
    return adj, nv

def dists(adj, s):
    d = [-1] * len(adj); d[s] = 0; dq = deque([s])
    while dq:
        v = dq.popleft()
        for w in adj[v]:
            if d[w] < 0: d[w] = d[v] + 1; dq.append(w)
    return d

if __name__ == '__main__':
    pass
