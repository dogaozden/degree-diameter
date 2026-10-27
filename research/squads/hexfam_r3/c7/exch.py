#!/usr/bin/env python3
"""c7 (squad hexfam_r3): exchange search at q=11. Remove one R-point r*, then greedily add (x, s) pairs
using the Prop. 6 cell counts (cell = pattern of distance-4 relations to the added points).
usage: exch.py PAIRS OUTPAIRS M SEED CH TLIM NTRY
M: sampled non-spread lines (candidate s), CH: chunk size, TLIM: seconds, NTRY: number of r* tried."""
import sys, time, collections, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo

PAIRS, OUT = sys.argv[1], sys.argv[2]
M, SEED, CH, TLIM, NTRY = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7])
T0 = time.time()
def log(*a): print('[%5.0fs]' % (time.time() - T0), *a, flush=True)

G = Geo(11); N, L = G.N, G.L; LP, PL, C = G.LP, G.PL, G.C
rng = np.random.default_rng(SEED)
Sp = np.array([int(x) for x in open('/home/user/degree-diameter/research/d10D7/sets/L11_spread.txt').read().split()])
nS = len(Sp); inSp = np.zeros(L, bool); inSp[Sp] = True
spos = -np.ones(L, np.int64); spos[Sp] = np.arange(nS)
pairs = [tuple(map(int, l.split())) for l in open(PAIRS) if l.strip()]
R0 = np.array([r for r, s in pairs if inSp[s]], dtype=np.int64)
X0 = [(r, s) for r, s in pairs if not inSp[s]]
log('R', len(R0), 'X', len(X0))

def conc(s):
    a = PL[LP[s]].ravel(); return a[a != s]
def near4(s):  # bool mask over lines: distance 2 or 4 from s (s excluded)
    cn = conc(s); m = np.zeros(L, bool); m[PL[LP[cn]].ravel()] = True; m[cn] = True; m[s] = False; return m

nonsp = np.nonzero(~inSp)[0]
samp = rng.choice(nonsp, M, replace=False)
Pd = np.zeros((M, nS), np.float32); sj = -np.ones(M, np.int64); svalid = np.ones(M, bool)
for a, s in enumerate(samp):
    cn = conc(s); cs = cn[inSp[cn]]
    if len(cs) >= 2: svalid[a] = False; continue
    m4 = near4(s)[Sp].astype(np.float32)
    if len(cs) == 1: sj[a] = spos[cs[0]]; m4[sj[a]] = 0
    Pd[a] = m4
log('samples ready, invalid', int((~svalid).sum()))

def build(Rarr, Xl):
    nR = len(Rarr)
    patR = np.zeros(nR, np.int64); patS = np.zeros(nS, np.int64); freeS = np.ones(nS, bool)
    for i, (x, s) in enumerate(Xl):
        bR = (G.B(C[[x]], C[Rarr])[0] == 0)
        patR |= bR.astype(np.int64) << i
        cn = conc(s); cs = cn[inSp[cn]]
        n4 = near4(s)[Sp]
        if len(cs) == 1:
            j = spos[cs[0]]; freeS[j] = False; n4[j] = False
        patS |= n4.astype(np.int64) << i
    uniq = np.unique(np.concatenate([patR, patS[freeS]]))
    ncell = len(uniq)
    cidR = np.searchsorted(uniq, patR); cidS = np.searchsorted(uniq, patS)
    OHR = np.zeros((nR, ncell), np.float32); OHR[np.arange(nR), cidR] = 1
    OHS = np.zeros((nS, ncell), np.float32); fi = np.nonzero(freeS)[0]; OHS[fi, cidS[fi]] = 1
    cntR = OHR.sum(0); cntS = OHS.sum(0)
    A1 = (Pd * freeS[None, :].astype(np.float32)) @ OHS              # free lines at distance 4 from sample s, per cell
    CC = np.zeros((M, ncell), np.float32)
    for m in range(M):
        if sj[m] >= 0 and freeS[sj[m]]: CC[m, cidS[sj[m]]] = 1        # concurrent free spread line is removed
    bout = cntS[None, :] - A1 - CC                                    # free lines of the cell not at distance 4
    return dict(R=Rarr, X=Xl, cidR=cidR, OHR=OHR, cntR=cntR, A1=A1, bout=bout, cidS=cidS, freeS=freeS, ncell=ncell)

def evalV(xs, st, sv):
    """xs: candidate points (non-collinear with R, opposite to X). returns Vmin, argmin over valid sample lines."""
    Rarr = st['R']; Vmin = np.zeros(len(xs)); arg = np.zeros(len(xs), np.int64)
    for c0 in range(0, len(xs), CH):
        xx = xs[c0:c0 + CH]
        NB = (G.B(C[xx], C[Rarr]) == 0).astype(np.float32)
        ain = NB @ st['OHR']; aout = st['cntR'][None, :] - ain
        V = np.maximum(ain[:, None, :] - st['A1'][None], 0).sum(2) + np.maximum(aout[:, None, :] - st['bout'][None], 0).sum(2)
        V[:, ~sv] = 1e9
        Vmin[c0:c0 + CH] = V.min(1); arg[c0:c0 + CH] = V.argmin(1)
    return Vmin, arg

def collinear_counts(Rarr):
    cc = np.zeros(N, np.int32); P1 = {}
    for r in Rarr:
        a = np.unique(LP[PL[r]].ravel()); a = a[a != r]; cc[a] += 1
    return cc

def pool_for(Rarr, Xl, cc, only_r=None):
    inR = np.zeros(N, bool); inR[Rarr] = True
    ok = (cc == 0) & ~inR
    if only_r is not None:  # points collinear only with only_r (cc==1 and collinear with that r)
        a = np.unique(LP[PL[only_r]].ravel()); a = a[a != only_r]
        extra = a[(cc[a] == 1) & ~inR[a]]
        ok[extra] = True
    pool = np.nonzero(ok)[0]
    for x, s in Xl:
        pool = pool[G.B(C[pool], C[[x]])[:, 0] != 0]
    return pool

def write_pairs(st, path):
    freeS, cidS, cidR = st['freeS'], st['cidS'], st['cidR']
    byc = collections.defaultdict(list)
    for j in np.nonzero(freeS)[0]: byc[cidS[j]].append(int(Sp[j]))
    out = [(int(r), byc[cidR[i]].pop()) for i, r in enumerate(st['R'])]
    out += [(int(x), int(s)) for x, s in st['X']]
    open(path, 'w').write('\n'.join('%d %d' % p for p in out) + '\n')
    return len(out)

def sv_after(sv, s):
    sv = sv & ~near4(s)[samp]; sv[samp == s] = False; return sv

sv0 = svalid.copy()
for x, s in X0: sv0 = sv_after(sv0, s)
cc0 = collinear_counts(R0)
pool0 = pool_for(R0, X0, cc0)
log('pool0 (non-collinear with R, opposite to X):', len(pool0))
st0 = build(R0, X0)
log('cells', st0['ncell'], 'R-cells max count', int(st0['cntR'].max()))

# ---- scan the full pool at the current state
Vmin0, arg0 = evalV(pool0, st0, sv0)
log('scan done: min V over pool =', Vmin0.min(), ' #V=0:', int((Vmin0 == 0).sum()), ' #V=1:', int((Vmin0 == 1).sum()), ' #V=2:', int((Vmin0 == 2).sum()))

# ---- which R-points fix candidates with one violation unit
score = collections.Counter(); fixers = {}
cand1 = pool0[Vmin0 <= 1.0]
for i, x in enumerate(pool0):
    if Vmin0[i] != 1: continue
    m = arg0[i]
    NB = (G.B(C[[x]], C[R0])[0] == 0)
    ain = np.bincount(st0['cidR'][NB], minlength=st0['ncell'])
    aout = st0['cntR'] - ain
    cin = np.nonzero(ain > st0['A1'][m])[0]; cout = np.nonzero(aout > st0['bout'][m])[0]
    fx = set()
    for c in cin: fx.update(np.nonzero(NB & (st0['cidR'] == c))[0].tolist())
    for c in cout: fx.update(np.nonzero((~NB) & (st0['cidR'] == c))[0].tolist())
    fixers[int(x)] = fx
    for r in fx: score[r] += 1
log('fixer scores: top', score.most_common(5))

def greedy_after_removal(rstar):
    """remove rstar (None = keep R), then add pairs greedily. returns (R1, X1, st1)."""
    if rstar is None: R1 = R0
    else: R1 = R0[R0 != rstar]
    X1 = list(X0); sv = sv0.copy()
    pool = pool_for(R1, X1, cc0, only_r=rstar)
    st = build(R1, X1)
    added = 0
    while time.time() - T0 < TLIM:
        V, arg = evalV(pool, st, sv)
        feas = np.nonzero(V == 0)[0]
        log('  r*=%s |R1|=%d |X|=%d pool %d feasible-now %d' % (rstar, len(R1), len(X1), len(pool), len(feas)))
        if len(feas) == 0: break
        i = feas[0]; x = int(pool[i]); s = int(samp[arg[i]])
        X1.append((x, s)); sv = sv_after(sv, s)
        pool = pool[pool != x]
        pool = pool[G.B(C[pool], C[[x]])[:, 0] != 0]
        st = build(R1, X1); added += 1
    return R1, X1, st

best = (0, None)
tried = [None] + [r for r, _ in score.most_common(NTRY)]
for rs in tried:
    if time.time() - T0 > TLIM: break
    R1, X1, st = greedy_after_removal(rs)
    total = len(R1) + len(X1)
    log('RESULT removed=%s  |R|=%d |X|=%d total=%d' % (rs, len(R1), len(X1), total))
    if total > best[0]:
        best = (total, rs)
        n = write_pairs(st, OUT)
        log('wrote', OUT, n, 'lines')
log('best total', best[0], 'removed', best[1])
