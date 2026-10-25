#!/usr/bin/env python3
"""hubfix.py STATE.sol C0.lift2.sol "FDSET" OUT.sol: repair hub-sourced distance failures of a FLAGDEL graph by
rewiring hub edges.  The graph is rebuilt as in build_fd.py with sigma/nu from C0 (lift2 format) and the hub graph of
STATE.  Greedy: for a failing hub, try every new edge to an enabled hub of the other side (dropping one existing
inter-flag edge at a full end); accept the change that lowers (hub-source failures, then coverage holes of lns.cover)
the most; repeat.  Writes OUT.sol = STATE with the new hubgraph line and C0's sigma and nu."""
import sys, collections
from collections import deque
import numpy as np
import lns

st, c0, fds, out = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
S = lns.read_sol(st); F = S['F']; k = len(F); H = 3; FD = set(int(x) for x in fds.split())
tok = open(c0).read().split()
N = lns.N; Q1 = 8; M = 6
sig = [int(x) for x in tok[7:7 + N]]; mv0 = [int(x) for x in tok[7 + 2 * N:7 + 3 * N]]; mv1 = [int(x) for x in tok[7 + 3 * N:7 + 4 * N]]
nu = [int(x) for x in tok[7 + 4 * N:7 + 4 * N + N * Q1]]
hg = [int(x) for x in S['rows']['hubgraph']]
E = set((hg[e], hg[e + 1]) for e in range(0, len(hg), 2))
on = lambda h: h % H < 2 or h // H in FD
PTS = lns.PTS
isfree = set(F); fdflag = {(F[i], sig[F[i]]) for i in FD}
base = [[] for _ in range(2 * N * M)]
def add(a, b): base[a].append(b); base[b].append(a)
for l in range(N):
    for kk in range(Q1):
        p = int(PTS[l][kk])
        if (p, l) in fdflag: continue
        for h in range(M): add(p * M + h, (N + l) * M + (h + nu[l * Q1 + kk]) % M)
for p in range(N):
    if p in isfree: continue
    for h in range(M):
        add(p * M + h, (N + sig[p]) * M + (h + mv0[p]) % M); add(p * M + h, (N + sig[p]) * M + (h + mv1[p]) % M)
hubv = {}; nv = 2 * N * M; fib = {}
for i, p in enumerate(F):
    for side, x in (('A', p), ('B', N + sig[p])):
        for t in range(H):
            if t < 2 or i in FD: hubv[side, H * i + t] = nv; fib[nv] = x; nv += 1

def graph(Eset):
    adj = [list(a) for a in base] + [[] for _ in range(nv - 2 * N * M)]
    for v, x in fib.items():
        for h in range(M): adj[v].append(x * M + h); adj[x * M + h].append(v)
    for a, b in Eset:
        if ('A', a) in hubv and ('B', b) in hubv:
            u, v = hubv['A', a], hubv['B', b]; adj[u].append(v); adj[v].append(u)
    return adj

def hubfails(Eset):
    adj = graph(Eset); tot = 0; per = collections.Counter()
    for s in range(2 * N * M, nv):
        d = [-1] * nv; d[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            if d[x] == 5: continue
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x] + 1; q.append(y)
        f = sum(1 for t in range(nv) if d[t] < 0); tot += f
        if f: per[s] = f
    return tot, per

def coverage(Eset):
    A = np.zeros((k, k), bool)
    for a, b in Eset:
        if on(a) and on(b): A[a // H, b // H] = True
    return lns.cover(F, np.array(sig), A)

def deg(Eset, h, side): return sum(1 for a, b in Eset if (a if side == 'A' else b) == h)
inv = {v: key for key, v in hubv.items()}
def bfs_from(Eset, s):
    adj = graph(Eset); d = [-1] * nv; d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        if d[x] == 5: continue
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; q.append(y)
    return sum(1 for t in range(nv) if d[t] < 0)
cur = (hubfails(E)[0], coverage(E)); print('start: hub-source failures', cur[0], 'coverage', cur[1], flush=True)
harm = {}
def harmless_drops(Eset, h, side):
    """inter-flag edges at hub h whose removal creates no hub failure and no coverage hole"""
    res = []
    for x in [x for x in Eset if (x[0] if side == 'A' else x[1]) == h and x[0] // H != x[1] // H]:
        if x not in harm:
            E2 = set(Eset); E2.discard(x); harm[x] = (hubfails(E2)[0], coverage(E2))
        res.append(x)
    return res
while cur[0] > 0:
    _, per = hubfails(E); best = None
    for s in per:
        side, h = inv[s]; other = 'B' if side == 'A' else 'A'
        for (side2, h2) in hubv:
            if side2 != other: continue
            e = (h, h2) if side == 'A' else (h2, h)
            if e in E: continue
            E1 = set(E); E1.add(e)
            if bfs_from(E1, s) >= per[s]: continue
            dA = [None] if deg(E, e[0], 'A') < 4 else harmless_drops(E, e[0], 'A')
            dB = [None] if deg(E, e[1], 'B') < 4 else harmless_drops(E, e[1], 'B')
            for xa in dA:
                for xb in dB:
                    E2 = set(E1)
                    if xa: E2.discard(xa)
                    if xb: E2.discard(xb)
                    v = (hubfails(E2)[0], coverage(E2))
                    if v < cur and (best is None or v < best[0]): best = (v, E2)
            if best and best[0][0] == 0: break
        if best: break
    if not best: print('no improving rewiring'); break
    cur, E = best; harm = {}; print('hub-source failures', cur[0], 'coverage', cur[1], flush=True)
rows = dict(S['rows']); rows['hubgraph'] = [str(x) for ab in sorted(E) for x in ab]
rows['nu'] = [str(x) for x in nu]; rows['mv0'] = [str(x) for x in mv0]; rows['mv1'] = [str(x) for x in mv1]
S['rows'] = rows
lns.write_sol(out, S, np.array(sig), cur[0])
