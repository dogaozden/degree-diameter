"""probe3.py (job d7-family): usage probe3.py HEXBIN STATE.npz SPREAD.npy OUT.npy.
 partner points for a mirrored configuration (state npz: base R, extras X, lines L; spread S), by types.
A partner y of a base point a: y collinear with a and with no other point of R' = R + X, at distance 4 or 6 from every
other point; its line M: not in S, meets no L_j, d(M, L_j) = d(y, x_j) for every extra; M meets exactly one spread
line s_M, which becomes sigma(a) (type of a must equal type of s_M, s_M usable). Feasible when for every old type t the
base points of type t (a excluded) at distance 4 / 6 from y are at most the usable spread lines of type t at distance
4 / 6 from M (s_M and lines meeting M excluded). Prints the feasible (a, y, M) count and the first ones."""
import sys, os, numpy as np, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'cell147', 'mirror'))   # hexmod.py (branch claude/cell-14-7-record-5d03gb)
from hexmod import Hex
H = Hex(sys.argv[1]); st = np.load(sys.argv[2]); S = np.load(sys.argv[3]); N = H.N
R = st['R'].astype(int); X = st['X'].astype(int); L = st['L'].astype(int)
def pball(p):
    l1 = H.pl[p]; p2 = set(H.lp[l1].ravel().tolist()) - {p}
    l3 = set(H.pl[list(p2)].ravel().tolist()) - set(l1.tolist()); p4 = set(H.lp[list(l3)].ravel().tolist()) - p2 - {p}
    return p2, p4
def lball(l): return H.line_ball(l)
# point-distance-4 matrix rows we need via BFS
Rp = list(R) + list(X)
pbR = [pball(int(r)) for r in Rp]
k = len(X)
# old types
tR = [frozenset(j for j in range(k) if X[j] in pbR[i][1]) for i in range(len(R))]
lbL = [lball(int(l)) for l in L]
excl = set(); tS = {}
for s in S:
    t = set()
    for j, (d2, d4) in enumerate(lbL):
        if s in d2: excl.add(int(s))
        elif s in d4: t.add(j)
    tS[int(s)] = frozenset(t)
types = sorted(set(tR) | set(tS.values()), key=lambda t: sorted(t))
tid = {t: i for i, t in enumerate(types)}; T = len(types)
Sus = [int(s) for s in S if int(s) not in excl]
Sidx = {s: i for i, s in enumerate(Sus)}
tSv = np.array([tid[tS[s]] for s in Sus]); tRv = np.array([tid[t] for t in tR])
print(f'q={H.q} |R|={len(R)} k={k} types={T} usable spread {len(Sus)}')
# spread line of each point (points on spread lines)
Sline = -np.ones(N, np.int64)
for s in S: Sline[H.lp[s]] = s
inS = np.zeros(N, bool); inS[S] = True
# candidate lines M: not in S, not meeting any L_j, with bit vectors over usable spread lines (distance 4) and meets
cand = []
for M in range(N):
    if inS[M]: continue
    d2, d4 = lball(M)
    if any(int(l) in d2 for l in L) or M in set(L.tolist()): continue
    sm = [s for s in d2 if inS[s]]
    if len(sm) != 1: continue
    sm = sm[0]
    if sm in excl: continue
    b4 = np.zeros(len(Sus), bool); bad = np.zeros(len(Sus), bool)
    for s in d4:
        if s in Sidx: b4[Sidx[s]] = True
    for s in d2:
        if s in Sidx: bad[Sidx[s]] = True
    bad[Sidx[sm]] = True
    dl = np.array([1 if int(L[j]) in d4 else 0 for j in range(k)])
    c1 = np.bincount(tSv[b4 & ~bad], minlength=T); c0 = np.bincount(tSv[~b4 & ~bad], minlength=T)
    cand.append((M, sm, dl, c1, c0))
print('candidate lines M', len(cand))
CM = np.array([c[0] for c in cand]); CSM = np.array([c[1] for c in cand]); CDL = np.array([c[2] for c in cand]).reshape(len(cand), k)
C1 = np.array([c[3] for c in cand]); C0 = np.array([c[4] for c in cand]); CST = np.array([tid[tS[int(c[1])]] for c in cand])
inRp = np.zeros(N, bool); inRp[Rp] = True
collc = np.zeros(N, np.int64)
for p2, _ in pbR:
    for p in p2: collc[p] += 1
feas = []; ny = 0
for i, a in enumerate(R):
    a = int(a)
    for y in pbR[i][0]:
        if inRp[y] or collc[y] != 1: continue
        ny += 1
        p2y, p4y = pball(y)
        bits = np.array([1 if int(r) in p4y else 0 for r in R]); bits[i] = 0
        dx = np.array([1 if int(x) in p4y else 0 for x in X])
        msk = np.ones(len(R), bool); msk[i] = False
        need1 = np.bincount(tRv[msk & (bits == 1)], minlength=T); need0 = np.bincount(tRv[msk & (bits == 0)], minlength=T)
        ok = (CST == tRv[i]) & (CDL == dx).all(1) & (C1 >= need1).all(1) & (C0 >= need0).all(1)
        for j in np.nonzero(ok)[0]: feas.append((a, y, int(CM[j]), int(CSM[j])))
print(f'partner candidates y {ny}; feasible (a, y, M): {len(feas)}')
print(feas[:20])
np.save(sys.argv[4], np.array(feas, dtype=np.int64).reshape(-1, 4))
