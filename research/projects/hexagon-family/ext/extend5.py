"""Fast pure + mixed extension (THEOREM.md Proposition 6).
Precompute, for a random sample of non-spread lines s, the pattern Gamma_4(s) ∩ Sp and the spread line meeting s.
State: cells of R (by pattern over the added x's) and of the free spread lines. For a candidate point x every sampled
line is tested at once: feasible iff for every cell T, #R-points of T in / not in N(x) <= #free spread lines of T in /
not in Gamma_4(s). Among feasible s keep the one maximising log #(choices of S) = sum_T log C(a_T, c_T).
usage: python3 extend5.py q RFILE SPREADFILE OUTPAIRS seed nsample maxadd [passes]"""
import sys, random, collections, time, numpy as np
from scipy.special import gammaln
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
q = int(sys.argv[1]); G = Geo(q); N = G.N; L = G.L
R = np.array([int(x) for x in open(sys.argv[2]).read().split()])
Sp = np.array([int(x) for x in open(sys.argv[3]).read().split()])
out = sys.argv[4]; seed = int(sys.argv[5]); nsample = int(sys.argv[6]); maxadd = int(sys.argv[7])
passes = int(sys.argv[8]) if len(sys.argv) > 8 else 2
rng = np.random.default_rng(seed); LP = G.LP; PL = G.PL; nR = len(R); nS = len(Sp)
t0 = time.time()
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
    elif len(cm) > 1: conc[a] = -2          # meets two spread lines: impossible for a partial spread, skip
    P[a] = l4[Sp]
    if conc[a] >= 0: P[a, conc[a]] = 0       # the concurrent line is at distance 2, not 4
valid = conc != -2
print('precomputed %d sample lines in %.0fs' % (len(samp), time.time() - t0), flush=True)
# candidates
nx = np.zeros(N, dtype=np.int64)
for a in range(0, N, 20000): nx[a:a + 20000] = (G.B(G.C[a:a + 20000], G.C[R]) == 0).sum(1)
cand = np.nonzero(~inR & ~collR)[0]; rng.shuffle(cand); cand = cand[np.argsort(nx[cand], kind='stable')]
candok = np.ones(len(cand), bool)
cellR = np.zeros(nR, dtype=np.int64); cellS = np.zeros(nS, dtype=np.int64); ncell = 1
free = np.ones(nS, bool)
X, Sx = [], []
def refresh():
    global OH, A1, cntS, cntR
    OH = np.zeros((nS, ncell), dtype=np.float32); OH[np.arange(nS)[free], cellS[free]] = 1
    A1 = P @ OH                                            # (sample, cells): free lines of cell T in Gamma_4(s)
    cntS = OH.sum(0); cntR = np.bincount(cellR, minlength=ncell).astype(np.float32)
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
for ps in range(passes):
    for ci in range(len(cand)):
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
        idx = np.nonzero(feas)[0]
        a1 = A1[idx]; a0 = A0[idx]
        sc = (gammaln(a1 + 1) - gammaln(c1 + 1) - gammaln(a1 - c1 + 1) + gammaln(a0 + 1) - gammaln(c0 + 1) - gammaln(a0 - c0 + 1)).sum(1)
        b = idx[int(np.argmax(sc))]; s = int(samp[b])
        # commit
        X.append(x); Sx.append(s)
        if conc[b] >= 0: free[conc[b]] = False
        l4, M = near(s)
        valid &= ~l4[samp]                                  # future s must be opposite to s
        candok &= (G.B(G.C[cand], G.C[[x]])[:, 0] != 0)     # future x opposite to x
        pat = P[b] > 0
        newR = cellR * 2 + bR.astype(np.int64); newS = cellS * 2 + pat.astype(np.int64)
        u, inv = np.unique(np.concatenate([newR, newS]), return_inverse=True)
        cellR = inv[:nR]; cellS = inv[nR:]; ncell = len(u)
        refresh()
        write_pairs()
        print('added x=%d (|N(x)|=%d) s=%d score %.1f: |X| = %d, cells %d [%.0fs]' % (x, bR.sum(), s, sc.max(), len(X), ncell, time.time() - t0), flush=True)
        if len(X) >= maxadd: break
    if len(X) >= maxadd: break
pairs = write_pairs()
print('RESULT q=%d |R|=%d + |X|=%d = %d [%.0fs]' % (q, nR, len(X), len(pairs), time.time() - t0))
