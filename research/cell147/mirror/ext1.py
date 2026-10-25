#!/usr/bin/env python3
"""Exhaustive one-pair extension of a zero-deficit mirrored state (R, X, L) at q = 11 (types as in mirror_build.py).
For every extra point x (non-collinear with R, opposite to every X_j) and every line l (not in the spread S, opposite to
every L_j): does (X + x, L + l) still have deficit 0?  Per base type t with c_R(t) base points and c_S(t) usable spread
lines, x hits a(t) base points of type t and l is at distance 4 from b(t) spread lines of type t and concurrent with
e(t) in {0, 1}; deficit 0 iff a(t) <= b(t) <= a(t) + c_S(t) - c_R(t) - e(t) for every t.  Types without slack force
b = a and e = 0, so x and l are joined on that signature and every joined pair is then checked in full.
usage: ext1.py STATE.npz OUT.npz"""
import numpy as np, sys, os, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
t0 = time.time()
H = Hex(SP + 'hex_q11.bin'); N = H.N
st = np.load(sys.argv[1]); R = st['R'].astype(np.int64); X = st['X'].astype(np.int64); L = st['L'].astype(np.int64)
k = len(X); S = np.load(SP + 'S_herm.npy').astype(np.int64); nS = len(S)
Sline = -np.ones(N, dtype=np.int64); Sline[H.lp[S].reshape(-1)] = np.repeat(np.arange(nS), H.q + 1)
Sset = np.zeros(N, bool); Sset[S] = True

def rel(lines):
    """for each line: one-hot of the concurrent spread lines (M2) and of the spread lines at distance 4 (M4)"""
    P = H.lp[lines]; b = len(lines)
    conc = Sline[P]; near = Sline[H.lp[H.pl[P]].reshape(b, -1)]
    M2 = np.zeros((b, nS), bool); M4 = np.zeros((b, nS), bool)
    r, c = np.nonzero(conc >= 0); M2[r, conc[r, c]] = True
    r, c = np.nonzero(near >= 0); M4[r, near[r, c]] = True
    return M2, M4 & ~M2

# old types
mR = ((H.Bmat(X, R) == 0).astype(np.int64) << np.arange(k)[:, None]).sum(0)
M2, M4 = rel(L)
excl = M2.any(0)
mS = (M4.astype(np.int64) << np.arange(k)[:, None]).sum(0)
types, cR = np.unique(mR, return_counts=True); nT = len(types); tid = {int(t): i for i, t in enumerate(types)}
tS = np.array([tid.get(int(m), -1) if not excl[s] else -1 for s, m in enumerate(mS)])
cS = np.bincount(tS[tS >= 0], minlength=nT)
slack = cS - cR
print(f'k={k} base types {nT}, deficit {int(np.maximum(0, -slack).sum())}, tight types {int((slack == 0).sum())}, '
      f'slack histogram {sorted(collections.Counter(slack.tolist()).items())[:12]} [{time.time()-t0:.1f}s]', flush=True)
assert (slack >= 0).all(), 'state does not have deficit 0'
tight = np.nonzero(slack == 0)[0]

# candidate points
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]
cand = cand[(H.Bmat(cand, X) != 0).all(1)]
TR = np.zeros((len(R), nT), np.float32); TR[np.arange(len(R)), [tid[int(m)] for m in mR]] = 1
A = np.zeros((len(cand), nT), np.int16)
for a in range(0, len(cand), 4096):
    A[a:a + 4096] = ((H.Bmat(cand[a:a + 4096], R) == 0).astype(np.float32) @ TR).astype(np.int16)
print(f'points: {len(cand)} candidates [{time.time()-t0:.1f}s]', flush=True)

# candidate lines: not in S, opposite to every L_j
bad = Sset.copy()
for l in L:
    d2, d4 = H.line_ball(int(l)); bad[list(d2)] = True; bad[list(d4)] = True; bad[int(l)] = True
lines = np.nonzero(~bad)[0]
TS = np.zeros((nS, nT), np.float32); ok = tS >= 0; TS[np.nonzero(ok)[0], tS[ok]] = 1
B = np.zeros((len(lines), nT), np.int16); E = -np.ones(len(lines), np.int64)
for a in range(0, len(lines), 2000):
    m2, m4 = rel(lines[a:a + 2000])
    B[a:a + 2000] = (m4.astype(np.float32) @ TS).astype(np.int16)
    e = (m2.astype(np.float32) @ TS)
    has = e.sum(1) > 0; E[a:a + 2000][has] = e[has].argmax(1)
print(f'lines: {len(lines)} candidates [{time.time()-t0:.1f}s]', flush=True)

# join on the tight signature
okL = ~np.isin(E, tight)
sigP = collections.defaultdict(list)
for i in range(len(cand)): sigP[A[i, tight].tobytes()].append(i)
found = []; joined = 0; best = None
for j in np.nonzero(okL)[0]:
    lst = sigP.get(B[j, tight].tobytes())
    if not lst: continue
    for i in lst:
        joined += 1
        D = B[j].astype(np.int64) - A[i]
        hi = slack.copy()
        if E[j] >= 0: hi[E[j]] -= 1
        viol = int(np.maximum(0, -D).sum() + np.maximum(0, D - hi).sum())
        if best is None or viol < best[0]: best = (viol, int(cand[i]), int(lines[j]))
        if viol == 0: found.append((int(cand[i]), int(lines[j])))
print(f'tight-signature classes: points {len(sigP)}; joined pairs {joined}; zero-deficit extensions {len(found)}; '
      f'best joined pair violation {best[0] if best else None} [{time.time()-t0:.1f}s]', flush=True)
if found:
    x, l = found[0]
    np.savez(sys.argv[2], R=R, X=np.append(X, x), L=np.append(L, l))
    print('wrote', sys.argv[2], 'x', x, 'l', l)
