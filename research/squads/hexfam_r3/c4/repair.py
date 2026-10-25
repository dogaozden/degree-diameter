"""Destroy-and-repair from a pairs file (base R + added x's), built on extend5.py.
Removes NREM randomly chosen added pairs, replays the rest exactly (same state as extend5 after those commits),
then re-adds greedily (same feasibility test and score as extend5) for at most TLIM seconds.
usage: python3 repair.py q RFILE SPREAD BESTPAIRS OUT seed nsample nrem tlim"""
import sys, time, collections, numpy as np
from scipy.special import gammaln
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
q = int(sys.argv[1]); G = Geo(q); N = G.N; L = G.L
R = np.array([int(x) for x in open(sys.argv[2]).read().split()])
Sp = np.array([int(x) for x in open(sys.argv[3]).read().split()])
best = [tuple(map(int, l.split())) for l in open(sys.argv[4]) if l.strip()]
out = sys.argv[5]; seed = int(sys.argv[6]); nsample = int(sys.argv[7]); nrem = int(sys.argv[8]); tlim = float(sys.argv[9])
rng = np.random.default_rng(seed); LP = G.LP; PL = G.PL; nR = len(R); nS = len(Sp); t0 = time.time()
inR = np.zeros(N, bool); inR[R] = True; inSp = np.zeros(L, bool); inSp[Sp] = True
spos = -np.ones(L, dtype=np.int64); spos[Sp] = np.arange(nS)
collR = np.zeros(N, bool); collR[LP[PL[R].ravel()].ravel()] = True
def near(s):
    M = PL[LP[s]].ravel(); M = M[M != s]
    l4 = np.zeros(L, bool); l4[PL[LP[M].ravel()].ravel()] = True; return l4, M
nonspread = np.nonzero(~inSp)[0]
samp = rng.choice(nonspread, size=min(nsample, len(nonspread)), replace=False)
P = np.zeros((len(samp), nS), dtype=np.float32); conc = -np.ones(len(samp), dtype=np.int64)
for a, s in enumerate(samp):
    l4, M = near(int(s)); cm = M[inSp[M]]
    if len(cm) == 1: conc[a] = spos[cm[0]]
    elif len(cm) > 1: conc[a] = -2
    P[a] = l4[Sp]
    if conc[a] >= 0: P[a, conc[a]] = 0
valid = conc != -2
Rset = set(R.tolist())
base = [p for p in best if p[0] in Rset]; added = [p for p in best if p[0] not in Rset]
assert len(base) == nR, (len(base), nR)
# destroy: remove nrem random added pairs
drop = set(rng.choice(len(added), size=min(nrem, len(added)), replace=False).tolist()) if nrem > 0 else set()
kept = [p for i, p in enumerate(added) if i not in drop]
print('removed %d added pairs, kept %d [%.0fs]' % (len(drop), len(kept), time.time() - t0), flush=True)
nx = np.zeros(N, dtype=np.int64)
for a in range(0, N, 20000): nx[a:a + 20000] = (G.B(G.C[a:a + 20000], G.C[R]) == 0).sum(1)
cand = np.nonzero(~inR & ~collR)[0]; rng.shuffle(cand); cand = cand[np.argsort(nx[cand], kind='stable')]
candok = np.ones(len(cand), bool)
cellR = np.zeros(nR, dtype=np.int64); cellS = np.zeros(nS, dtype=np.int64); ncell = 1
free = np.ones(nS, bool); X, Sx = [], []
def pattern(s):
    l4, M = near(s); cm = M[inSp[M]]
    c = -1
    if len(cm) == 1: c = spos[cm[0]]
    pat = l4[Sp].copy()
    if c >= 0: pat[c] = False
    return c, pat, l4
def commit(x, s, bR, c, pat, l4):
    global cellR, cellS, ncell, valid, candok
    X.append(x); Sx.append(s)
    if c >= 0: free[c] = False
    valid &= ~l4[samp]
    candok &= (G.B(G.C[cand], G.C[[x]])[:, 0] != 0)
    newR = cellR * 2 + bR.astype(np.int64); newS = cellS * 2 + pat.astype(np.int64)
    u, inv = np.unique(np.concatenate([newR, newS]), return_inverse=True)
    cellR = inv[:nR]; cellS = inv[nR:]; ncell = len(u)
# replay kept pairs (the order of additions is the file order)
for x, s in kept:
    bR = (G.B(G.C[[x]], G.C[R])[0] == 0).astype(np.float32)
    c, pat, l4 = pattern(s)
    commit(x, s, bR, c, pat, l4)
print('replayed; cells %d [%.0fs]' % (ncell, time.time() - t0), flush=True)
OH = None
def refresh():
    global OH, A1, cntS, cntR
    OH = np.zeros((nS, ncell), dtype=np.float32); OH[np.arange(nS)[free], cellS[free]] = 1
    A1 = P @ OH; cntS = OH.sum(0); cntR = np.bincount(cellR, minlength=ncell).astype(np.float32)
refresh()
def write_pairs():
    bycell = collections.defaultdict(list)
    for k in range(nS):
        if free[k]: bycell[cellS[k]].append(int(Sp[k]))
    pairs = []
    for j in range(nR): pairs.append((int(R[j]), bycell[cellR[j]].pop()))
    pairs += list(zip(X, Sx))
    open(out, 'w').write('\n'.join('%d %d' % p for p in pairs) + '\n')
    return pairs
write_pairs()
for ps in range(2):
    for ci in range(len(cand)):
        if time.time() - t0 > tlim: break
        if not candok[ci]: continue
        x = int(cand[ci])
        bR = (G.B(G.C[[x]], G.C[R])[0] == 0).astype(np.float32)
        c1 = np.bincount(cellR, weights=bR, minlength=ncell); c0 = cntR - c1
        cc = np.zeros((len(samp), ncell), dtype=np.float32)
        okc = conc >= 0
        cc[np.nonzero(okc)[0], cellS[conc[okc]]] = free[conc[okc]]
        A0 = cntS[None, :] - A1 - cc
        feas = valid & (A1 >= c1[None, :]).all(1) & (A0 >= c0[None, :]).all(1)
        if not feas.any(): continue
        idx = np.nonzero(feas)[0]; a1 = A1[idx]; a0 = A0[idx]
        sc = (gammaln(a1 + 1) - gammaln(c1 + 1) - gammaln(a1 - c1 + 1) + gammaln(a0 + 1) - gammaln(c0 + 1) - gammaln(a0 - c0 + 1)).sum(1)
        b = idx[int(np.argmax(sc))]; s = int(samp[b])
        c, pat, l4 = pattern(s)
        commit(x, s, bR, c, pat, l4)
        refresh(); write_pairs()
        print('re-added x=%d s=%d: |X| = %d [%.0fs]' % (x, s, len(X), time.time() - t0), flush=True)
    if time.time() - t0 > tlim: break
pairs = write_pairs()
print('RESULT q=%d |R|=%d + |X|=%d = %d [%.0fs]' % (q, nR, len(X), len(pairs), time.time() - t0), flush=True)
