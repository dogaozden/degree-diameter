"""c2: extend5.py with the relaxation 'added points may be at distance 4 from each other' (Lemma 3, card c2).
Added pair (x_j, s_j) and new pair (x, s) at distance 4 need: s, s_j at distance 4; midpoint m of (x, x_j) not collinear
with R and not a midpoint of another pair; midline M of (s, s_j) meets no other added line; the spread line meeting M
(if any) is removed from the free spread lines. Lines/points at distance 2 are never allowed.
usage: python3 extend5r.py q RFILE SPREADFILE OUTPAIRS seed nsample maxadd [passes] [TRY]"""
import sys, collections, time, numpy as np
from scipy.special import gammaln
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
q = int(sys.argv[1]); G = Geo(q); N = G.N; L = G.L
R = np.array([int(x) for x in open(sys.argv[2]).read().split()])
Sp = np.array([int(x) for x in open(sys.argv[3]).read().split()])
out = sys.argv[4]; seed = int(sys.argv[5]); nsample = int(sys.argv[6]); maxadd = int(sys.argv[7])
passes = int(sys.argv[8]) if len(sys.argv) > 8 else 1
TRY = int(sys.argv[9]) if len(sys.argv) > 9 else 40
rng = np.random.default_rng(seed); LP = G.LP; PL = G.PL; nR = len(R); nS = len(Sp)
t0 = time.time()
inR = np.zeros(N, bool); inR[R] = True; inSp = np.zeros(L, bool); inSp[Sp] = True
spos = -np.ones(L, dtype=np.int64); spos[Sp] = np.arange(nS)
collR = np.zeros(N, bool); collR[LP[PL[R].ravel()].ravel()] = True
def pts_col(p):                      # points collinear with point p (not p)
    a = LP[PL[p]].ravel(); return np.unique(a[a != p])
def lines_meet(l):                   # lines meeting line l (not l)
    a = PL[LP[l]].ravel(); return np.unique(a[a != l])
def meet_bool(l):
    m = np.zeros(L, bool); m[lines_meet(l)] = True; return m
def l4_bool(l):                      # lines at distance <= 4 from l (incl. l)
    M = lines_meet(l); m = np.zeros(L, bool); m[PL[LP[M]].ravel()] = True; m[l] = True; return m
nonspread = np.nonzero(~inSp)[0]
samp = rng.choice(nonspread, size=min(nsample, len(nonspread)), replace=False); ns = len(samp)
P = np.zeros((ns, nS), dtype=np.float32); conc = -np.ones(ns, dtype=np.int64)
for a, s in enumerate(samp):
    s = int(s); l4 = l4_bool(s); cm = lines_meet(s); cm = cm[inSp[cm]]
    if len(cm) == 1: conc[a] = spos[cm[0]]
    elif len(cm) > 1: conc[a] = -2
    P[a] = l4[Sp]
    if conc[a] >= 0: P[a, conc[a]] = 0
print('precomputed %d sample lines in %.0fs' % (ns, time.time() - t0), flush=True)
nx = np.zeros(N, dtype=np.int64)
for a in range(0, N, 20000): nx[a:a + 20000] = (G.B(G.C[a:a + 20000], G.C[R]) == 0).sum(1)
cand = np.nonzero(~inR & ~collR)[0]; rng.shuffle(cand); cand = cand[np.argsort(nx[cand], kind='stable')]
maxcols = maxadd + 2
D2S = np.zeros((ns, maxcols), bool); D4S = np.zeros((ns, maxcols), bool)   # sample s vs added line j
valid = conc != -2
X, Sx = [], []; Um = set(); Ul = set()
removed = np.zeros(nS, bool); collX = np.zeros(N, bool)
cellR = np.zeros(nR, dtype=np.int64); cellS = np.zeros(nS, dtype=np.int64); ncell = 1
def refresh():
    global A1, A0, cntS, cntR
    free = ~removed
    OH = np.zeros((nS, ncell), dtype=np.float32); OH[np.nonzero(free)[0], cellS[free]] = 1
    A1 = P @ OH; cntS = OH.sum(0)
    CC = np.zeros((ns, ncell), dtype=np.float32); okc = np.nonzero(conc >= 0)[0]
    CC[okc, cellS[conc[okc]]] = free[conc[okc]]
    A0 = cntS[None, :] - A1 - CC
    cntR = np.bincount(cellR, minlength=ncell).astype(np.float32)
refresh()
def write_pairs():
    free = ~removed; bycell = collections.defaultdict(list)
    for k in np.nonzero(free)[0]: bycell[cellS[k]].append(int(Sp[k]))
    pairs = [(int(R[j]), bycell[cellR[j]].pop()) for j in range(nR)] + list(zip(X, Sx))
    open(out, 'w').write('\n'.join('%d %d' % p for p in pairs) + '\n')
    return pairs
nrelax = 0
for ps in range(passes):
    for ci in range(len(cand)):
        x = int(cand[ci]); nX = len(X)
        if collX[x] or inR[x]: continue
        bR = (G.B(G.C[[x]], G.C[R])[0] == 0)
        c1 = np.bincount(cellR, weights=bR.astype(np.float32), minlength=ncell); c0 = cntR - c1
        if nX:
            tx = (G.B(G.C[[x]], G.C[np.array(X)])[0] == 0); Jl = np.nonzero(tx)[0]
        else:
            tx = np.zeros(0, bool); Jl = np.zeros(0, dtype=np.int64)
        mids = []; ok = True; px = pts_col(x)
        for j in Jl:
            m = np.intersect1d(px, pts_col(X[j]))
            if len(m) != 1: ok = False; break
            m = int(m[0])
            if collR[m] or m in Um or any(m == mm for _, mm in mids): ok = False; break
            mids.append((int(j), m))
        if not ok: continue
        vS = valid.copy()
        if nX:
            vS &= ~D2S[:, :nX].any(1)
            vS &= (D4S[:, :nX] == tx[None, :]).all(1)
        idx = np.nonzero(vS)[0]
        if len(idx) == 0: continue
        a1 = A1[idx]; a0 = A0[idx]
        f = (a1 >= c1[None, :]).all(1) & (a0 >= c0[None, :]).all(1)
        idx = idx[f]
        if len(idx) == 0: continue
        a1 = A1[idx]; a0 = A0[idx]
        sc = (gammaln(a1 + 1) - gammaln(c1 + 1) - gammaln(a1 - c1 + 1) + gammaln(a0 + 1) - gammaln(c0 + 1) - gammaln(a0 - c0 + 1)).sum(1)
        for b in idx[np.argsort(-sc)][:TRY]:
            s = int(samp[b]); Ms = []; ells = []; good = True
            for j, m in mids:
                MM = np.intersect1d(lines_meet(s), lines_meet(Sx[j]))
                if len(MM) != 1: good = False; break
                M = int(MM[0])
                if M in Ul or any(M == mm for _, mm in Ms): good = False; break
                cM = meet_bool(M)
                if [kk for kk in range(nX) if cM[Sx[kk]]] != [j]: good = False; break
                cmm = lines_meet(M); ell = cmm[inSp[cmm]]
                if len(ell) > 1: good = False; break
                Ms.append((j, M)); ells += [int(spos[e]) for e in ell]
            if not good: continue
            nrem = removed.copy(); cb = conc[b]
            if cb >= 0: nrem[cb] = True
            for e in ells: nrem[e] = True
            inGb = P[b] > 0; nfree = ~nrem
            e1 = np.bincount(cellS[nfree & inGb], minlength=ncell); e0 = np.bincount(cellS[nfree & ~inGb], minlength=ncell)
            if not ((e1 >= c1).all() and (e0 >= c0).all()): continue
            # commit
            if mids: nrelax += 1
            X.append(x); Sx.append(s); k = len(X) - 1
            Um.update(m for _, m in mids); Ul.update(M for _, M in Ms)
            removed = nrem; collX[pts_col(x)] = True; collX[x] = True
            D2S[:, k] = meet_bool(s)[samp]; D4S[:, k] = l4_bool(s)[samp] & ~D2S[:, k]
            valid &= samp != s
            newR = cellR * 2 + bR.astype(np.int64); newS = cellS * 2 + inGb.astype(np.int64)
            u, inv = np.unique(np.concatenate([newR, newS]), return_inverse=True)
            cellR = inv[:nR]; cellS = inv[nR:]; ncell = len(u); refresh()
            write_pairs()
            print('added x=%d |N(x)|=%d J=%s s=%d score %.1f: |X| = %d (relaxed so far %d), cells %d [%.0fs]' % (
                x, bR.sum(), [j for j, _ in mids], s, sc.max(), len(X), nrelax, ncell, time.time() - t0), flush=True)
            break
        if len(X) >= maxadd: break
    if len(X) >= maxadd: break
pairs = write_pairs()
print('RESULT q=%d |R|=%d + |X|=%d = %d relaxed-pairs-used=%d [%.0fs]' % (q, nR, len(X), len(pairs), nrelax, time.time() - t0), flush=True)
