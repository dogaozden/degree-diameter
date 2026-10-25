"""c6: destroy-and-repair ILS over added pairs (x, s) of Proposition 6 (extension of a pure set R).
State: added points Xp (pairwise opposite, not collinear with R) and lines Xl (pairwise opposite, not in Sp).
Feasibility per candidate (x, s): cell counts of R (by pattern over added points) vs free spread lines (same pattern),
exactly as ext/extend5.py. Repair = greedy completion in random candidate order, best line by entropy (+noise).
Accept a destroy-repair move if the size does not drop. Writes the best pairs file and prints the scorer check command.
usage: python3 ils.py q RFILE SPFILE OUTPREFIX [--init PAIRS] [--seed s] [--time sec] [--kmax k] [--noise x]"""
import sys, time, random, collections, argparse
import numpy as np
from scipy.special import gammaln
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo

ap = argparse.ArgumentParser()
ap.add_argument('q', type=int); ap.add_argument('rfile'); ap.add_argument('spfile'); ap.add_argument('out')
ap.add_argument('--init', default=''); ap.add_argument('--seed', type=int, default=1)
ap.add_argument('--time', type=float, default=300); ap.add_argument('--kmax', type=int, default=3)
ap.add_argument('--noise', type=float, default=0.0); ap.add_argument('--nlines', type=int, default=0)
ap.add_argument('--target', type=int, default=10**9)
a = ap.parse_args()
rng = np.random.default_rng(a.seed); pr = random.Random(a.seed)
t0 = time.time()
G = Geo(a.q); N, L, LP, PL, C = G.N, G.L, G.LP, G.PL, G.C
R = np.array([int(x) for x in open(a.rfile).read().split()])
Sp = np.array([int(x) for x in open(a.spfile).read().split()])
nR, nS = len(R), len(Sp)
inR = np.zeros(N, bool); inR[R] = True
inSp = np.zeros(L, bool); inSp[Sp] = True
spos = -np.ones(L, np.int64); spos[Sp] = np.arange(nS)
collR = np.zeros(N, bool); collR[LP[PL[R].ravel()].ravel()] = True

def l4_of(s):  # boolean over lines: distance <= 4 from s (includes s)
    M = PL[LP[s]].ravel(); M = M[M != s]
    l4 = np.zeros(L, bool); l4[PL[LP[M]].ravel()] = True; l4[s] = True
    return l4, M

nonsp = np.nonzero(~inSp)[0]
if a.nlines and a.nlines < len(nonsp): rows_lines = np.sort(np.random.default_rng(a.seed + 7).choice(nonsp, a.nlines, replace=False))
else: rows_lines = nonsp
nrow = len(rows_lines)
P = np.zeros((nrow, nS), np.float32); conc = -np.ones(nrow, np.int64); okline = np.ones(nrow, bool)
for k, s in enumerate(rows_lines):
    l4, M = l4_of(int(s)); cm = M[inSp[M]]
    if len(cm) == 1: conc[k] = spos[cm[0]]
    elif len(cm) > 1: okline[k] = False
    row = l4[Sp].astype(np.float32)
    if conc[k] >= 0: row[conc[k]] = 0
    P[k] = row
rowof = -np.ones(L, np.int64); rowof[rows_lines] = np.arange(nrow)
print('lines precomputed %d rows (%d spread) in %.0fs' % (nrow, nS, time.time() - t0), flush=True)

cand = np.nonzero(~inR & ~collR)[0]
bRc = np.zeros((len(cand), nR), bool)
for st_ in range(0, len(cand), 20000):
    blk = cand[st_:st_ + 20000]; bRc[st_:st_ + len(blk)] = (G.B(C[blk], C[R]) == 0)
print('candidates %d' % len(cand), flush=True)
cand_pos = -np.ones(N, np.int64); cand_pos[cand] = np.arange(len(cand))
L4cache = {}
def l4c(s):
    if s not in L4cache: L4cache[s] = l4_of(s)[0]
    return L4cache[s]

def build(Xp, Xl):
    """state for the added set: cell ids of R and of spread lines, and the valid line rows for further additions."""
    cR = np.zeros(nR, np.int64); cS = np.zeros(nS, np.int64); free = np.ones(nS, bool)
    valid = okline.copy()
    for i, (x, s) in enumerate(zip(Xp, Xl)):
        bR = (G.B(C[[x]], C[R])[0] == 0)
        cR |= bR.astype(np.int64) << i
        rw = rowof[s]
        if rw >= 0:
            cS |= (P[rw] > 0).astype(np.int64) << i
            cn = conc[rw]
        else:  # line outside the sampled rows (init pairs): compute its pattern directly
            l4_, M_ = l4_of(s); cm_ = M_[inSp[M_]]
            pat_ = l4_[Sp].copy(); cn = -1
            if len(cm_) == 1: cn = int(spos[cm_[0]]); pat_[cn] = False
            cS |= pat_.astype(np.int64) << i
        if cn >= 0: free[cn] = False
        valid &= ~l4c(s)[rows_lines]
    u, inv = np.unique(np.concatenate([cR, cS]), return_inverse=True)
    cellR = inv[:nR]; cellS = inv[nR:]; ncell = len(u)
    OH = np.zeros((nS, ncell), np.float32); fi = np.nonzero(free)[0]; OH[fi, cellS[fi]] = 1
    cntS = OH.sum(0); cntR = np.bincount(cellR, minlength=ncell).astype(np.float32)
    vrows = np.nonzero(valid)[0]
    cc = np.zeros((len(vrows), ncell), np.float32)
    cv = conc[vrows]; okc = (cv >= 0)
    okc[okc] = free[cv[okc]]
    rr = np.nonzero(okc)[0]; cc[rr, cellS[cv[rr]]] = 1
    A1 = P[vrows] @ OH                       # state-only: free lines of each cell at distance 4 from the candidate line
    A0 = cntS[None, :] - A1 - cc
    return dict(cellR=cellR, cellS=cellS, free=free, OH=OH, cntS=cntS, cntR=cntR, ncell=ncell,
                vrows=vrows, A1=A1, A0=A0)

def best_line(ci, st):
    """best feasible line row for candidate point index ci, or None."""
    vrows = st['vrows']
    if len(vrows) == 0: return None
    bRx = bRc[ci].astype(np.float32)
    c1 = np.bincount(st['cellR'], weights=bRx, minlength=st['ncell']).astype(np.float32)
    c0 = st['cntR'] - c1
    A1 = st['A1']; A0 = st['A0']
    feas = (A1 >= c1[None, :]).all(1) & (A0 >= c0[None, :]).all(1)
    if not feas.any(): return None
    idx = np.nonzero(feas)[0]
    a1 = A1[idx].astype(np.float64); a0 = A0[idx].astype(np.float64)
    sc = (gammaln(a1 + 1) - gammaln(c1 + 1) - gammaln(a1 - c1 + 1) + gammaln(a0 + 1) - gammaln(c0 + 1) - gammaln(a0 - c0 + 1)).sum(1)
    if a.noise: sc = sc + a.noise * rng.random(len(sc))
    return int(vrows[idx[int(np.argmax(sc))]])

def complete(Xp, Xl):
    Xp = list(Xp); Xl = list(Xl)
    st = build(Xp, Xl)
    while True:
        added = 0
        order = rng.permutation(len(cand))
        for ci in order:
            x = int(cand[ci])
            if Xp:
                if (G.B(C[[x]], C[Xp])[0] == 0).any(): continue
            rw = best_line(int(ci), st)
            if rw is None: continue
            s = int(rows_lines[rw]); Xp.append(x); Xl.append(s); st = build(Xp, Xl); added += 1
        if added == 0: break
    return Xp, Xl

def write_pairs(Xp, Xl, path):
    st = build(Xp, Xl)
    bycell = collections.defaultdict(list)
    for k in np.nonzero(st['free'])[0]: bycell[st['cellS'][k]].append(int(Sp[k]))
    pairs = [(int(R[j]), bycell[st['cellR'][j]].pop()) for j in range(nR)]
    pairs += list(zip(Xp, Xl))
    open(path, 'w').write('\n'.join('%d %d' % p for p in pairs) + '\n')
    return len(pairs)

# initial state
if a.init:
    pairs = [tuple(map(int, l.split())) for l in open(a.init) if l.strip()]
    Xp = [p[0] for p in pairs[nR:]]; Xl = [p[1] for p in pairs[nR:]]
    print('init: %d added pairs' % len(Xp), flush=True)
    def cells_ok(xp, xl):
        st_ = build(xp, xl); return bool((st_['cntR'] <= st_['cntS']).all())
    n0 = len(Xp)
    while Xp and not cells_ok(Xp, Xl):
        Xp.pop(); Xl.pop()
    print('init kept %d of %d added pairs (cell-feasible)' % (len(Xp), n0), flush=True)
else:
    Xp, Xl = [], []
Xp, Xl = complete(Xp, Xl)
cur = (Xp, Xl); best = len(Xp); best_pairs = nR + best
print('start greedy: |X| = %d (total %d) [%.0fs]' % (len(Xp), nR + len(Xp), time.time() - t0), flush=True)
write_pairs(Xp, Xl, a.out + '_best.pairs')
it = 0
while time.time() - t0 < a.time and nR + best < a.target:
    it += 1
    cXp, cXl = cur
    k = int(rng.integers(1, a.kmax + 1)); k = min(k, len(cXp))
    keep = sorted(rng.choice(len(cXp), len(cXp) - k, replace=False)) if k else list(range(len(cXp)))
    nXp, nXl = complete([cXp[i] for i in keep], [cXl[i] for i in keep])
    if len(nXp) >= len(cXp):
        cur = (nXp, nXl)
        if len(nXp) > best:
            best = len(nXp); write_pairs(nXp, nXl, a.out + '_best.pairs')
            print('it %d: NEW BEST |X| = %d total %d [%.0fs]' % (it, best, nR + best, time.time() - t0), flush=True)
    if it % 20 == 0: print('it %d cur %d best %d [%.0fs]' % (it, len(cur[0]), best, time.time() - t0), flush=True)
print('DONE q=%d it=%d best total %d [%.0fs]' % (a.q, it, nR + best, time.time() - t0), flush=True)
