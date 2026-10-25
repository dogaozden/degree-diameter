#!/usr/bin/env python3
"""surgery.py STATE.sol C0.lift2.sol "FDSET" OUT.lift2.sol: finish coset-0 by route surgery.  Coset-0 bad pair = opposite
same-colour pair whose geodesics (deleted flag edges removed) all have one nu-parity and that has no route
(points a, b: sigma(a), sigma(b) concurrent; lines s, t: sinv(s), sinv(t) collinear; freed ends have no route).
For each bad pair, try every sigma swap that creates its route; evaluate the exact change of the bad-pair count
(only pairs at the two swapped points / lines change) and keep swaps that leave coverage (lns.cover) and the FLAGDEL
D1 holes (d1.py) at 0.  Greedy, then pairs of swaps if needed."""
import sys, itertools
import numpy as np
import lns, d1

st, c0, fds, out = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
S = lns.read_sol(st); F = S['F']; k = len(F); FD = set(int(x) for x in fds.split())
tok = open(c0).read().split(); N = lns.N
head = tok[:7]
sig = np.array([int(x) for x in tok[7:7 + N]]); nu = np.array([int(x) for x in tok[7 + 4 * N:7 + 4 * N + N * 8]]) // 3
PTS, LOF, PM, LM = lns.PTS, lns.LOF, lns.PM, lns.LM
hg = [int(x) for x in S['rows']['hubgraph']]
A = np.zeros((k, k), bool)
for e in range(0, len(hg), 2):
    a, b = hg[e], hg[e + 1]
    if (a % 3 < 2 or a // 3 in FD) and (b % 3 < 2 or b // 3 in FD): A[a // 3, b // 3] = True
isfree = np.zeros(N, bool); isfree[F] = True
# flag parities and collinearity via a given line
fp = {}
for l in range(N):
    for kk in range(8): fp[int(PTS[l][kk]), l] = int(nu[l * 8 + kk])
Pp = np.zeros((N, N), np.int32); Cp = np.zeros((N, N), np.int32)   # points: 2-paths a - L - c
Pl = np.zeros((N, N), np.int32); Cl = np.zeros((N, N), np.int32)   # lines: 2-paths s - y - t
dele = set((F[i], int(sig[F[i]])) for i in FD)
for l in range(N):
    pl = [int(x) for x in PTS[l]]
    for a in pl:
        for c in pl:
            if a == c or (a, l) in dele or (c, l) in dele: continue
            Cp[a, c] = 1; Pp[a, c] = fp[a, l] ^ fp[c, l]
for y in range(N):
    ls = [int(x) for x in LOF[y]]
    for s_ in ls:
        for t in ls:
            if s_ == t or (y, s_) in dele or (y, t) in dele: continue
            Cl[s_, t] = 1; Pl[s_, t] = fp[y, s_] ^ fp[y, t]
def unmixed(P, C, opp):
    PC = P * C
    odd = PC @ C + C @ PC - 2 * (PC @ PC)
    ng = C @ C
    return opp & ((odd == 0) | (odd == ng))
oppP = ~PM; np.fill_diagonal(oppP, False); oppL = ~LM; np.fill_diagonal(oppL, False)
UP = unmixed(Pp, Cp, oppP); UL = unmixed(Pl, Cl, oppL)

def badcount(sig):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    nf = ~isfree
    routeP = LM[sig][:, sig] & nf[:, None] & nf[None, :]
    nfl = nf[sinv]
    routeL = PM[sinv][:, sinv] & nfl[:, None] & nfl[None, :]
    bP = UP & ~routeP; bL = UL & ~routeL
    return int(bP.sum() // 2 + bL.sum() // 2), np.argwhere(np.triu(bP)), np.argwhere(np.triu(bL))

def holes(sig):
    c = lns.cover(F, sig, A)
    dd = sum(cp + cl for i, (p, l, cp, cl, h) in enumerate(d1.d1(F, sig)) if i in FD)
    return c + dd

cur, bp, bl = badcount(sig); h0 = holes(sig)
print('start: coset-0 bad pairs', cur, 'points', bp.tolist(), 'lines', bl.tolist(), 'coverage+D1', h0, flush=True)
def candidates(sig, bp, bl):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    out = []
    for a, b in bp:
        for x, o in ((a, b), (b, a)):
            if isfree[x]: continue
            for y_ in PTS[sig[o]]:
                for M in LOF[y_]:
                    w = int(sinv[M])
                    if w != x and not isfree[w]: out.append((int(x), w))
    for s_, t in bl:
        for x, o in ((s_, t), (t, s_)):
            px = int(sinv[x]); po = int(sinv[o])
            if isfree[px] or isfree[po]: continue
            for w in np.nonzero(PM[po])[0]:
                w = int(w)
                if w != px and not isfree[w]: out.append((px, w))
    return list(dict.fromkeys(out))
it = 0
while cur > 0 and it < 50:
    it += 1; best = None; cands = candidates(sig, bp, bl)
    for x, w in cands:
        s2 = sig.copy(); s2[x], s2[w] = s2[w], s2[x]
        c2, _, _ = badcount(s2)
        if c2 >= cur: continue
        hh = holes(s2)
        if hh <= h0 and (best is None or (c2, hh) < best[0]): best = ((c2, hh), s2)
    if best is None:
        print('no single swap improves (%d candidates); trying pairs' % len(cands), flush=True)
        firsts = []
        for x, w in cands:
            s2 = sig.copy(); s2[x], s2[w] = s2[w], s2[x]
            c2, bp2, bl2 = badcount(s2)
            if c2 <= cur + 1: firsts.append((c2, x, w, s2, bp2, bl2))
        firsts.sort(key=lambda t: t[0]); print('  first swaps within +1:', len(firsts), flush=True)
        for c2, x, w, s2, bp2, bl2 in firsts:
            for x2, w2 in candidates(s2, bp2, bl2):
                s3 = s2.copy(); s3[x2], s3[w2] = s3[w2], s3[x2]
                c3, _, _ = badcount(s3)
                if c3 >= cur: continue
                hh = holes(s3)
                if hh <= h0 and (best is None or (c3, hh) < best[0]): best = ((c3, hh), s3)
            if best is not None and best[0][0] == 0: break
        if best is None: print('no pair of swaps improves', flush=True); break
    (cur, h0), sig = best; _, bp, bl = badcount(sig)
    print('swap -> coset-0 bad pairs', cur, 'coverage+D1', h0, flush=True)
with open(out, 'w') as f:
    f.write(' '.join(head[:4]) + ' %d\n' % cur + ' '.join(head[5:7]) + '\n')
    f.write(' '.join(map(str, sig)) + '\n' + ' '.join(map(str, sig)) + '\n')
    f.write(' '.join(tok[7 + 2 * N:7 + 3 * N]) + '\n' + ' '.join(tok[7 + 3 * N:7 + 4 * N]) + '\n')
    f.write(' '.join(str(3 * v) for v in nu) + '\n')
print('final coset-0', cur, 'coverage+D1', h0)
