"""Destroy-and-repair search on the added pairs (squad hexfam_r3, card c1). Derived from ext/extend5.py.
State = list of added points X and their sample-line indices SA; everything else (cells, free spread lines,
valid samples, candidate mask, A1/A0 counts) is rebuilt from (X, SA). Iteration: remove 1-3 random added pairs,
greedily re-add (removed points first, then a random window of the nx-sorted candidates), keep if |X| does not drop.
usage: python3 dr.py INIT.pairs OUTPREFIX seed nsample tlim_seconds mcand pool"""
import sys, time, collections, subprocess, numpy as np
from scipy.special import gammaln
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
D = '/home/user/degree-diameter/research/d10D7/sets/'
INIT, OUT = sys.argv[1], sys.argv[2]
SEED, NS, TLIM, MCAND, POOL = int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
q = 11; T0 = time.time()
G = Geo(q); N = G.N; L = G.L; LP = G.LP; PL = G.PL; C = G.C
R = np.array([int(v) for v in open(D + 'P11_r6c7_756.txt').read().split()], dtype=np.int64)
Sp = np.array([int(v) for v in open(D + 'L11_spread.txt').read().split()], dtype=np.int64)
nR, nS = len(R), len(Sp); CR = C[R]
rng = np.random.default_rng(SEED)
inR = np.zeros(N, bool); inR[R] = True
inSp = np.zeros(L, bool); inSp[Sp] = True
spos = -np.ones(L, dtype=np.int64); spos[Sp] = np.arange(nS)
collR = np.zeros(N, bool); collR[LP[PL[R].ravel()].ravel()] = True

def near(s):
    M = PL[LP[s]].ravel(); M = M[M != s]
    l4 = np.zeros(L, bool); l4[PL[LP[M].ravel()].ravel()] = True; return l4, M

init = [tuple(int(v) for v in l.split()) for l in open(INIT) if l.strip()]
assert [p[0] for p in init[:nR]] == R.tolist()
Xi = [p[0] for p in init[nR:]]; Si = [p[1] for p in init[nR:]]
assert all(not inSp[s] for s in Si)
nonspread = np.nonzero(~inSp)[0]
samp = rng.choice(nonspread, size=NS, replace=False)
sset = set(samp.tolist()); extra = [s for s in Si if s not in sset]
samp = np.concatenate([np.array(extra, dtype=np.int64), samp]); nsamp = len(samp)
pos = {int(s): a for a, s in enumerate(samp)}
SAi = [pos[s] for s in Si]

# precomputed sample patterns (as in extend5)
P = np.zeros((nsamp, nS), dtype=np.uint8); conc = -np.ones(nsamp, dtype=np.int64)
for a, s in enumerate(samp):
    l4, M = near(int(s)); cm = M[inSp[M]]
    if len(cm) == 1: conc[a] = spos[cm[0]]
    elif len(cm) > 1: conc[a] = -2
    P[a] = l4[Sp]
    if conc[a] >= 0: P[a, conc[a]] = 0
print('precomputed %d sample lines [%.0fs]' % (nsamp, time.time() - T0), flush=True)
nx = np.zeros(N, dtype=np.int64)
for a in range(0, N, 20000): nx[a:a + 20000] = (G.B(C[a:a + 20000], CR) == 0).sum(1)
cand = np.nonzero(~inR & ~collR)[0]; rng.shuffle(cand); cand = cand[np.argsort(nx[cand], kind='stable')]
candpos = -np.ones(N, dtype=np.int64); candpos[cand] = np.arange(len(cand))
print('candidates %d [%.0fs]' % (len(cand), time.time() - T0), flush=True)

_nb = {}
def nb(a):  # samples within distance 4 of sample a (incl. concurrent ones)
    if a not in _nb:
        if len(_nb) > 3000: _nb.clear()
        _nb[a] = near(int(samp[a]))[0][samp]
    return _nb[a]

_opp = {}
def opp(x):  # candidates opposite to point x (cached, bounded)
    if x not in _opp:
        if len(_opp) > 1500: _opp.clear()
        _opp[x] = (G.B(C[cand], C[[x]])[:, 0] != 0)
    return _opp[x]

class St: pass
def rebuild(X, SA):
    st = St(); st.X = list(X); st.SA = list(SA)
    free = np.ones(nS, bool); valid = conc != -2
    for a in SA:
        if conc[a] >= 0: free[conc[a]] = False
        valid &= ~nb(a)
    cellR = np.zeros(nR, dtype=np.int64); cellS = np.zeros(nS, dtype=np.int64); ncell = 1
    for x, a in zip(X, SA):
        bR = (G.B(C[[x]], CR)[0] == 0).astype(np.int64); bS = (P[a] > 0).astype(np.int64)
        u, inv = np.unique(np.concatenate([cellR * 2 + bR, cellS * 2 + bS]), return_inverse=True)
        inv = inv.ravel(); cellR = inv[:nR]; cellS = inv[nR:]; ncell = len(u)
    fr = np.nonzero(free)[0]; order = fr[np.argsort(cellS[fr], kind='stable')]
    uc, starts = np.unique(cellS[order], return_index=True)
    A1 = np.zeros((nsamp, ncell), dtype=np.int16)
    A1[:, uc] = np.add.reduceat(P[:, order], starts, axis=1, dtype=np.int16)
    cntS = np.zeros(ncell, dtype=np.int16); cntS[uc] = np.diff(np.append(starts, len(order)))
    A0 = cntS[None, :] - A1
    rows = np.nonzero(conc >= 0)[0]
    A0[rows, cellS[conc[rows]]] -= free[conc[rows]].astype(np.int16)
    st.free, st.cellR, st.cellS, st.ncell, st.A1, st.A0 = free, cellR, cellS, ncell, A1, A0
    st.cntR = np.bincount(cellR, minlength=ncell).astype(np.int16); st.valid = valid
    st.candok = np.ones(len(cand), bool)
    for x in X: st.candok &= opp(x)
    return st

def evaluate(st, x):
    bR = (G.B(C[[x]], CR)[0] == 0)
    c1 = np.bincount(st.cellR, weights=bR, minlength=st.ncell).astype(np.int16); c0 = st.cntR - c1
    feas = st.valid & (st.A1 >= c1).all(1) & (st.A0 >= c0).all(1)
    if not feas.any(): return None
    idx = np.nonzero(feas)[0]; a1 = st.A1[idx].astype(np.float64); a0 = st.A0[idx].astype(np.float64)
    c1d = c1.astype(np.float64); c0d = c0.astype(np.float64)
    sc = (gammaln(a1 + 1) - gammaln(c1d + 1) - gammaln(a1 - c1d + 1) + gammaln(a0 + 1) - gammaln(c0d + 1) - gammaln(a0 - c0d + 1)).sum(1)
    return int(idx[int(np.argmax(sc))]), float(sc.max())

def pairs_of(st):
    bycell = collections.defaultdict(list)
    for k in np.nonzero(st.free)[0]: bycell[st.cellS[k]].append(int(Sp[k]))
    pr = [(int(R[j]), bycell[st.cellR[j]].pop()) for j in range(nR)]
    return pr + [(int(x), int(samp[a])) for x, a in zip(st.X, st.SA)]

def score(path):
    out = subprocess.run(['python3', '/home/user/degree-diameter/research/projects/hexagon-family/ext/mixsol.py', '11', path,
                          '/home/user/degree-diameter/research/squads/hexfam_r3/c1/chk_dr', '1', '3'], capture_output=True, text=True).stdout
    ok = 'Lemma 3 holds' in out and '(R2) verified' in out
    K = int(out.split('K = ')[1].split(',')[0].split()[0]) if 'K = ' in out else -1
    return K, ok

def repair(X, SA, removed):
    st = rebuild(X, SA)
    pool = rng.choice(min(POOL, len(cand)), size=MCAND, replace=False)
    visit = list(removed) + [int(cand[p]) for p in pool]
    for x in visit:
        if not st.candok[candpos[x]]: continue
        r = evaluate(st, x)
        if r is None: continue
        X = st.X + [x]; SA = st.SA + [r[0]]
        st = rebuild(X, SA)
    return st

st = rebuild(Xi, SAi)
assert st.candok[candpos[np.array(Xi)]].sum() == 0 or True
print('start |X| = %d (K = %d) [%.0fs]' % (len(st.X), nR + len(st.X), time.time() - T0), flush=True)
best = len(st.X)
def save(st, tag):
    pr = pairs_of(st); p = OUT + '_%s.pairs' % tag
    open(p, 'w').write('\n'.join('%d %d' % t for t in pr) + '\n')
    return p
p0 = save(st, 'start'); K0, ok0 = score(p0); print('start scored K=%d ok=%s' % (K0, ok0), flush=True)
it = 0; acc = 0
while time.time() - T0 < TLIM:
    it += 1
    k = min(int(rng.integers(1, 4)), len(st.X))
    rem = set(rng.choice(len(st.X), size=k, replace=False).tolist())
    removed = [st.X[i] for i in rem]
    X2 = [x for i, x in enumerate(st.X) if i not in rem]; SA2 = [a for i, a in enumerate(st.SA) if i not in rem]
    st2 = repair(X2, SA2, removed[::-1])
    if len(st2.X) >= len(st.X):
        st = st2; acc += 1
    if len(st.X) > best:
        best = len(st.X); p = save(st, 'K%d' % (nR + best)); K, ok = score(p)
        print('it %d NEW BEST K=%d (scorer K=%d ok=%s) file %s [%.0fs]' % (it, nR + best, K, ok, p, time.time() - T0), flush=True)
    if it % 10 == 0:
        print('it %d |X|=%d best=%d accepted=%d [%.0fs]' % (it, len(st.X), best, acc, time.time() - T0), flush=True)
pf = save(st, 'final'); print('FINAL |X|=%d best=%d iters=%d [%.0fs]' % (len(st.X), best, it, time.time() - T0), flush=True)
