#!/usr/bin/env python3
"""Greedy mirrored extension of a pairwise-opposite point set R of H(11) (research/cell147/mirror/README.md).
Adds points X (pairwise opposite, non-collinear with R) and lines Lx (pairwise opposite, not in the Hermitian spread S)
such that a bijection f: R -> S (minus lines concurrent with some Lx) exists with d(f(r), Lx_j) = 4 iff d(r, X_j) = 4
(else 6).  Then R' = R + X, sigma(R') = f(R) + Lx satisfy the relaxed surgery theorem (local duality with mirrored
midpoints).  The feasibility of f is a per-type count condition (type = set of j adjacent).
usage: mirrork.py SEED OUTDIR [--xc 300] [--lc 4000] [--kmax 200]"""
import numpy as np, sys, os, random, argparse, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
ap = argparse.ArgumentParser(); ap.add_argument('seed', type=int); ap.add_argument('outdir')
ap.add_argument('--xc', type=int, default=300); ap.add_argument('--lc', type=int, default=4000)
ap.add_argument('--kmax', type=int, default=200); ap.add_argument('--rfile', default=SP + 'R756idx.npy')
a = ap.parse_args(); rng = np.random.default_rng(a.seed); os.makedirs(a.outdir, exist_ok=True)
t0 = time.time()
H = Hex(SP + 'hex_q11.bin'); N = H.N; q = 11
R = np.load(a.rfile); nR = len(R)
S = np.load(SP + 'S_herm.npy'); nS = len(S)
X = H.X
inE = (X[:, 0] + X[:, 4]) % q == 0
Sline = -np.ones(N, dtype=np.int64)            # index into S of the spread line through an E point
for j, l in enumerate(S): Sline[H.lp[l]] = j
assert (Sline[inE] >= 0).all()
# collinearity with R
colR = np.zeros(N, bool)
pts = H.lp[H.pl[R]].reshape(-1); colR[pts] = True; colR[R] = True
cand = np.nonzero(~colR)[0]
print(f'candidates {len(cand)} [{time.time()-t0:.1f}s]', flush=True)
def orth(I, J):
    return H.Bmat(np.asarray(I), np.asarray(J)) == 0
NR = orth(cand, R)                             # candidate x -> R points at distance 4 (bool matrix)
cR = NR.sum(1)
# candidate lines (not in S) with their S profiles
Sset = np.zeros(N, bool); Sset[S] = True
def line_profile(ls):
    ls = np.asarray(ls)
    P = H.lp[ls]                                # (n, 12)
    conc = Sline[P]                             # (n, 12), -1 if not in E
    C = H.lp[H.pl[P]].reshape(len(ls), -1)      # (n, 1728) points collinear with points of the line (incl. themselves)
    near = Sline[C]
    out = []
    for i in range(len(ls)):
        c2 = set(conc[i][conc[i] >= 0].tolist())
        c4 = set(near[i][near[i] >= 0].tolist()) - c2
        out.append((c2, c4))
    return out
lines = rng.choice(np.nonzero(~Sset)[0], size=a.lc, replace=False)
prof = line_profile(lines)
print(f'line pool {len(lines)} profiles [{time.time()-t0:.1f}s]', flush=True)
def lines_opposite(l1, l2):
    d2, d4 = H.line_ball(int(l1)); return int(l2) not in d2 and int(l2) not in d4 and l1 != l2
typeR = np.zeros(nR, dtype=object); typeR[:] = 0
typeS = np.zeros(nS, dtype=object); typeS[:] = 0
excl = np.zeros(nS, bool)
Xs, Ls = [], []
used_x = np.zeros(len(cand), bool); used_l = np.zeros(len(lines), bool)
def feasible(tR, tS, ex):
    cr = collections.Counter(tR.tolist()); cs = collections.Counter(tS[~ex].tolist())
    return all(cs.get(t, 0) >= n for t, n in cr.items())
def slack(tR, tS, ex):
    cr = collections.Counter(tR.tolist()); cs = collections.Counter(tS[~ex].tolist())
    return min(cs.get(t, 0) - n for t, n in cr.items())
k = 0
while k < a.kmax:
    bit = 1 << k
    # candidate x: opposite to all X, unused
    ok = ~used_x
    if Xs:
        ok &= ~orth(cand, Xs).any(axis=1)
    xi_all = np.nonzero(ok)[0]
    if len(xi_all) == 0: print('no x candidates'); break
    xs = rng.choice(xi_all, size=min(a.xc, len(xi_all)), replace=False)
    # candidate lines: unused, opposite to all chosen lines (checked lazily)
    li_all = np.nonzero(~used_l)[0]
    best = None
    crS = collections.Counter(typeS[~excl].tolist()); crR = collections.Counter(typeR.tolist())
    for li in rng.permutation(li_all)[:600]:
        c2, c4 = prof[li]
        if any(excl[j] for j in []): pass
        # new exclusion
        ex2 = excl.copy(); ex2[list(c2)] = True
        if Ls and not all(lines_opposite(lines[li], L2) for L2 in Ls): continue
        c4l = np.array(sorted(c4)); 
        tS2 = typeS.copy()
        if len(c4l): tS2[c4l] = tS2[c4l] + bit
        csn = collections.Counter(tS2[~ex2].tolist())
        for xi in xs:
            adj = NR[xi]
            tR2 = typeR.copy(); tR2[adj] = tR2[adj] + bit
            crn = collections.Counter(tR2.tolist())
            sl = min(csn.get(t, 0) - n for t, n in crn.items())
            if sl >= 0:
                score = sl
                if best is None or score > best[0]: best = (score, xi, li, tR2, tS2, ex2)
        if best is not None and best[0] >= 2: break
    if best is None:
        print(f'k={k}: no feasible (x, line) pair found; stop'); break
    sc, xi, li, typeR, typeS, excl = best
    Xs.append(int(cand[xi])); Ls.append(int(lines[li])); used_x[xi] = True; used_l[li] = True
    k += 1
    print(f'k={k}: x={cand[xi]} c={cR[xi]} line={lines[li]} slack={sc} [{time.time()-t0:.1f}s]', flush=True)
    np.savez(os.path.join(a.outdir, 'state.npz'), X=np.array(Xs), L=np.array(Ls), R=R)
print('final k =', k)
