"""Destroy-and-repair on top of ext_all.py (same state, feasibility test and score). Starts from a pairs file
(R points with their lines, then the added pairs), removes NREM random added pairs (1..3), rebuilds the state,
re-runs the greedy (order ovl, random ties) until it stalls, keeps the result if it is not smaller (plateau moves
allowed) and writes OUTPREFIX.pairs whenever a strictly larger set is found.
usage: python3 ext_lns.py q RFILE SPREADFILE STARTPAIRS OUTPREFIX seed timelimit_seconds

Original header of ext_all.py follows.
c3 (hexfam_r3): greedy extension over ALL non-spread lines (no sampling), THEOREM.md Proposition 6.
Same feasibility rule and objective as ext/extend5.py, with:
 - every non-spread line is tested (175,824 for q = 11), not a random sample;
 - the spread pattern (spread lines k at distance 4 from s) is stored as CSR (about 21M ones, int16 columns);
   A1[s,T] = #free spread lines of cell T at distance 4 from s is rebuilt by bincount, in chunks of 20000 lines,
   after each commit (rows are lines, so a chunk is a row range of the CSR);
 - candidate orders: rand | nx (|N(x)| ascending) | nxd (|N(x)| descending) | ovl (fewer R-points of N(x) already
   in some earlier N(x_i); re-ranked after every commit).
 Monotonicity: a candidate infeasible in some state stays infeasible after any commit (free lines only shrink, cells
 only refine, valid lines and candidates only shrink), so each candidate is tested once and then dropped.
usage: python3 ext_all.py q RFILE SPREADFILE OUTPREFIX seed order maxadd timelimit_seconds"""
import sys, time, collections, numpy as np
from scipy.special import gammaln
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo

q = int(sys.argv[1]); RF, SF, START, OUT = sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5]
seed = int(sys.argv[6]); TL = float(sys.argv[7]); ORDER = 'ovl'; MAXADD = 10 ** 6
t0 = time.time()
def log(*a): print('[%6.0fs]' % (time.time() - t0), *a, flush=True)
rng = np.random.default_rng(seed)
G = Geo(q); N, L = G.N, G.L; LP, PL, C = G.LP, G.PL, G.C
R = np.array([int(x) for x in open(RF).read().split()]); Sp = np.array([int(x) for x in open(SF).read().split()])
nR, nS = len(R), len(Sp)
inR = np.zeros(N, bool); inR[R] = True
inSp = np.zeros(L, bool); inSp[Sp] = True
spos = -np.ones(L, np.int64); spos[Sp] = np.arange(nS)
ns = np.nonzero(~inSp)[0]; Ln = len(ns)
nidx = -np.ones(L, np.int64); nidx[ns] = np.arange(Ln)
collR = np.zeros(N, bool); collR[LP[PL[R].ravel()].ravel()] = True
log('geometry loaded: N=%d L=%d |R|=%d |Sp|=%d non-spread=%d' % (N, L, nR, nS, Ln))

# ---- spread pattern: for spread line k, D4(k) = lines at distance exactly 4 (non-spread); C1(k) = concurrent lines
conc_sp = -np.ones(Ln, np.int64)          # spread index of the unique spread line meeting each non-spread line
rows_l, cols_l = [], []
for a in range(nS):
    k = int(Sp[a])
    C1 = np.unique(PL[LP[k]].ravel()); C1 = C1[C1 != k]
    inner = np.append(C1, k)
    D = np.unique(PL[LP[inner]].ravel())
    D4 = np.setdiff1d(D, inner, assume_unique=True)
    assert (nidx[D4] >= 0).all() and (nidx[C1] >= 0).all()
    assert (conc_sp[nidx[C1]] < 0).all(), 'a non-spread line meets two spread lines'
    conc_sp[nidx[C1]] = a
    rows_l.append(nidx[D4].astype(np.int32)); cols_l.append(np.full(len(D4), a, np.int16))
assert (conc_sp >= 0).all()
rows = np.concatenate(rows_l); cols = np.concatenate(cols_l); del rows_l, cols_l
o = np.argsort(rows, kind='stable')
indices = cols[o]; del o, cols
counts = np.bincount(rows, minlength=Ln); del rows
indptr = np.zeros(Ln + 1, np.int64); indptr[1:] = np.cumsum(counts)
log('spread pattern CSR built: nnz=%d (mean %.1f per line)' % (len(indices), len(indices) / Ln))

# ---- candidates: points not in R and not collinear with R; NM[c, j] = (x not opposite to R_j) i.e. R_j in N(x)
cand = np.nonzero(~inR & ~collR)[0]; nc = len(cand)
NM = np.zeros((nc, nR), bool)
for a in range(0, nc, 10000):
    NM[a:a + 10000] = (G.B(C[cand[a:a + 10000]], C[R]) == 0)
nx = NM.sum(1).astype(np.int64)
log('candidates %d, |N(x)| range %d..%d' % (nc, nx.min(), nx.max()))

# ---- state
def reset():
    global free, cellS, cellR, ncell, valid, alive, covR, overlap, X, Sx
    free = np.ones(nS, bool); cellS = np.zeros(nS, np.int64); cellR = np.zeros(nR, np.int64); ncell = 1
    valid = np.ones(Ln, bool)      # non-spread lines still opposite to every committed s
    alive = np.ones(nc, bool)      # candidates neither committed nor proven infeasible, and opposite to committed x's
    covR = np.zeros(nR, bool); overlap = np.zeros(nc, np.int64)
    X, Sx = [], []
reset()
cpos = -np.ones(N, np.int64); cpos[cand] = np.arange(nc)
if ORDER == 'rand': perm = rng.permutation(nc)
elif ORDER == 'nx': perm = np.lexsort((rng.random(nc), nx))
elif ORDER == 'nxd': perm = np.lexsort((rng.random(nc), -nx))

def refresh():
    global A1T, cntS, cntR, ccfree, cc_cell, vi, maxA1, minA1
    cm = np.where(free, cellS, ncell)
    A1T = np.zeros((ncell, Ln), np.int16)
    CH = 20000
    for a in range(0, Ln, CH):
        b = min(Ln, a + CH)
        rr = np.repeat(np.arange(b - a, dtype=np.int64), counts[a:b])
        keys = rr * (ncell + 1) + cm[indices[indptr[a]:indptr[b]]]
        h = np.bincount(keys, minlength=(b - a) * (ncell + 1)).reshape(b - a, ncell + 1)
        A1T[:, a:b] = h[:, :ncell].T
    cntS = np.bincount(cellS[free], minlength=ncell).astype(np.int64)
    cntR = np.bincount(cellR, minlength=ncell).astype(np.int64)
    ccfree = free[conc_sp]; cc_cell = cellS[conc_sp]
    vi = np.nonzero(valid)[0]
    mx = np.zeros(ncell, np.int64); mn = np.full(ncell, nS + 1, np.int64)
    for a in range(0, len(vi), 20000):
        sub = A1T[:, vi[a:a + 20000]]
        mx = np.maximum(mx, sub.max(1)); mn = np.minimum(mn, sub.min(1))
    maxA1, minA1 = mx.astype(np.int64), mn.astype(np.int64)

def test(ci):
    """None if no valid non-spread line s works for candidate x; else (line index, score, #feasible lines)."""
    bR = NM[ci]
    c1 = np.bincount(cellR[bR], minlength=ncell).astype(np.int64)
    c0 = cntR - c1
    if (c1 > maxA1).any() or (c0 > cntS - minA1).any(): return None
    T1 = np.nonzero(c1)[0]
    T1 = T1[np.argsort(cntS[T1], kind='stable')]
    idx = vi
    for T in T1:                       # A1[s,T] >= c1[T] for all cells with R-points in N(x)
        idx = idx[A1T[T, idx] >= c1[T]]
        if idx.size == 0: return None
    sub = A1T[:, idx].astype(np.int64)                  # ncell x m
    mk = ccfree[idx]
    cc = np.zeros_like(sub); cc[cc_cell[idx][mk], np.nonzero(mk)[0]] = 1   # concurrent free line is not counted
    A0 = cntS[:, None] - sub - cc                        # free lines of cell T not at distance 4 from s
    ok = (A0 >= c0[:, None]).all(0)
    if not ok.any(): return None
    idx = idx[ok]; a1 = sub[:, ok].astype(np.float64); a0 = A0[:, ok].astype(np.float64)
    c1f = c1[:, None].astype(np.float64); c0f = c0[:, None].astype(np.float64)
    sc = (gammaln(a1 + 1) - gammaln(c1f + 1) - gammaln(a1 - c1f + 1)
          + gammaln(a0 + 1) - gammaln(c0f + 1) - gammaln(a0 - c0f + 1)).sum(0)
    b = int(np.argmax(sc))
    return int(idx[b]), float(sc[b]), int(idx.size)

def write_pairs():
    bycell = collections.defaultdict(list)
    for a in np.nonzero(free)[0]: bycell[int(cellS[a])].append(int(Sp[a]))
    pairs = [(int(R[j]), bycell[int(cellR[j])].pop()) for j in range(nR)] + list(zip(X, Sx))
    open(OUT + '.pairs', 'w').write('\n'.join('%d %d' % p for p in pairs) + '\n')
    return len(pairs)

def commit(ci, res, quiet=False):
    global cellR, cellS, ncell, covR, overlap, alive
    bl, sc, nf = res
    x = int(cand[ci]); s = int(ns[bl]); k = int(conc_sp[bl])
    free[k] = False
    patS = np.zeros(nS, np.int64); patS[indices[indptr[bl]:indptr[bl + 1]]] = 1   # spread lines at distance 4 from s
    bR = NM[ci].astype(np.int64)
    M = PL[LP[s]].ravel(); M = M[M != s]
    l4 = np.unique(PL[LP[M]].ravel())              # lines at distance <= 4 from s (incl. s)
    ii = nidx[l4]; valid[ii[ii >= 0]] = False
    newR = cellR * 2 + bR; newS = cellS * 2 + patS
    u, inv = np.unique(np.concatenate([newR, newS]), return_inverse=True)
    cellR = inv[:nR]; cellS = inv[nR:]; ncell = len(u)
    X.append(x); Sx.append(s)
    newly = NM[ci] & ~covR
    if newly.any(): overlap += NM[:, newly].sum(1)
    covR |= NM[ci]
    alive &= (G.B(C[cand], C[[x]])[:, 0] != 0)
    alive[ci] = False
    if quiet: return
    refresh()
    log('added x=%d |N(x)|=%d s=%d (conc spread %d, free %d) score %.1f feasible-lines %d | |X|=%d cells=%d, K=%d'
        % (x, nx[ci], s, int(Sp[k]), int(free.sum()), sc, nf, len(X), ncell, nR + len(X)))


def greedy():
    """Run the ovl greedy from the current state until no candidate is feasible."""
    while True:
        act = np.nonzero(alive)[0]
        if act.size == 0: return
        seq = act[np.lexsort((rng.random(len(act)), nx[act], overlap[act]))]
        committed = False
        for ci in seq:
            if not alive[ci]: continue
            res = test(int(ci)); alive[ci] = False
            if res is None: continue
            commit(int(ci), res); committed = True; break
        if not committed: return

def rebuild(pairs):
    reset()
    for x, s in pairs:
        ci = int(cpos[x]); bl = int(nidx[s]); assert ci >= 0 and bl >= 0
        commit(ci, (bl, 0.0, 0), quiet=True)
    refresh()

rs = set(R.tolist())
start = [tuple(map(int, l.split())) for l in open(START) if l.strip()]
cur = [p for p in start if p[0] not in rs]
assert len(cur) + nR == len(start)
rebuild(cur)
best = len(cur); log('start: |R|=%d + |X|=%d = %d' % (nR, best, nR + best))
it = 0
while time.time() - t0 < TL:
    it += 1
    k = int(rng.integers(1, 4)); drop = set(rng.choice(len(cur), size=min(k, len(cur)), replace=False).tolist())
    keep = [p for i, p in enumerate(cur) if i not in drop]
    rebuild(keep)
    greedy()
    new = list(zip(X, Sx))
    log('iter %d: removed %d, now |X|=%d (best %d)' % (it, k, len(new), best))
    if len(new) >= len(cur): cur = new
    if len(new) > best:
        best = len(new); n_out = write_pairs(); log('IMPROVED: K=%d written to %s.pairs' % (n_out, OUT))
log('RESULT lns seed=%d best |X|=%d K=%d iterations=%d' % (seed, best, nR + best, it))
