#!/usr/bin/env python3
"""rewire.py STATE.sol "FDSET" OUT.sol [C0.lift2.sol]: single hub-edge moves (drop one edge at a line-side hub a, add
a -> b' at a point-side hub b' with a free slot, or the dual) minimising corrected coverage + D1 for sigma of C0 (or of
STATE).  Writes the best state (hub distances must still be checked exactly: dmhub2_f ITERS=0 'hub src')."""
import sys, collections, numpy as np, lns, d1, coverfd
st, fds, out = sys.argv[1], sys.argv[2], sys.argv[3]
S = lns.read_sol(st); FD = set(int(x) for x in fds.split()); F = S['F']; k = len(F); N = lns.N
sig = S['sig']
if len(sys.argv) > 4:
    tok = open(sys.argv[4]).read().split(); sig = np.array([int(x) for x in tok[7:7 + N]])
hg = [int(x) for x in S['rows']['hubgraph']]; E = set((hg[e], hg[e + 1]) for e in range(0, len(hg), 2))
on = lambda h: h % 3 < 2 or h // 3 in FD
def A_of(E):
    A = np.zeros((k, k), bool)
    for a, b in E:
        if on(a) and on(b): A[a // 3, b // 3] = True
    return A
dd = sum(cp + cl for i, (p, l, cp, cl, h) in enumerate(d1.d1(F, sig)) if i in FD)
def cost(E): return coverfd.cover(F, sig, A_of(E), FD) + dd
c0 = cost(E); print('start', c0, 'D1', dd, flush=True)
dA = collections.Counter(a for a, b in E if on(a) and on(b)); dB = collections.Counter(b for a, b in E if on(a) and on(b))
hubs = [h for h in range(3 * k) if on(h)]
res = []
for (a, b) in sorted(E):
    if not (on(a) and on(b)): continue
    for a2 in hubs:
        for b2 in hubs:
            if a2 // 3 == b2 // 3 and not (a2 // 3 == a // 3 and b2 // 3 == b // 3): pass
            if (a2, b2) in E: continue
            # move: drop (a,b), add (a2,b2); degrees after the move
            da = dA[a2] - (a2 == a); db = dB[b2] - (b2 == b)
            if da >= 4 or db >= 4: continue
            E2 = set(E); E2.discard((a, b)); E2.add((a2, b2))
            # keep own-flag hub pairs of FLAGDEL flags (needed for the deleted edge reroute)
            okown = all(any(x == 3 * i + t and y // 3 == i for x, y in E2) and any(y == 3 * i + t and x // 3 == i for x, y in E2) for i in FD for t in range(3))
            if not okown: continue
            res.append((cost(E2), (a, b), (a2, b2)))
res.sort()
print('best moves', res[:10])
if res and res[0][0] < c0:
    E2 = set(E); E2.discard(res[0][1]); E2.add(res[0][2])
    rows = S['rows']; rows['hubgraph'] = [str(x) for ab in sorted(E2) for x in ab]
    S2 = dict(S); S2['rows'] = rows; lns.write_sol(out, S2, sig, -1); print('wrote', out, res[0])
