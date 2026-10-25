#!/usr/bin/env python3
"""c8 (wildcard): the extra points X are the 12 points of a plane section of the quadric Q(6,11) that is a
nondegenerate conic (pairwise opposite; every point non-collinear with R756).  Every base point then has a type that is
the set of conic points on one line of the plane (so types have size <= 2).  The k = 12 partner lines L_j (pairwise
opposite, not in S) are annealed to minimise the type deficit D (base points dropped); F = 12 - D.
usage: conic_sa.py SEED OUTDIR [--secs 300] [--pool 20000] [--prop 40] [--T0 1.0] [--T1 0.05]"""
import numpy as np, sys, os, time, argparse, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/cell147/mirror')
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
ap = argparse.ArgumentParser()
ap.add_argument('seed', type=int); ap.add_argument('outdir')
ap.add_argument('--secs', type=float, default=300); ap.add_argument('--pool', type=int, default=20000)
ap.add_argument('--prop', type=int, default=40); ap.add_argument('--T0', type=float, default=1.0)
ap.add_argument('--T1', type=float, default=0.05); ap.add_argument('--k', type=int, default=12)
ap.add_argument('--sel', type=int, default=40); ap.add_argument('--sel_secs', type=float, default=60)
a = ap.parse_args()
rng = np.random.default_rng(a.seed); os.makedirs(a.outdir, exist_ok=True)
t0 = time.time(); q = 11; k = a.k
H = Hex(SP + 'hex_q11.bin'); N = H.N
R = np.load(SP + 'R756idx.npy').astype(np.int64); S = np.load(SP + 'S_herm.npy').astype(np.int64); nS = len(S)
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
candmask = ~colR
Sset = np.zeros(N, bool); Sset[S] = True
Sline = -np.ones(N, np.int64); Sline[H.lp[S].reshape(-1)] = np.repeat(np.arange(nS), H.lp.shape[1])
# ---- conic search: plane W spanned by 3 random candidate points, nondegenerate for the polar form
M = np.zeros((7, 7), np.int64)
for i, j in [(0, 4), (1, 5), (2, 6)]: M[i, j] = M[j, i] = 1
M[3, 3] = (-2) % q
coefs = np.array([v for v in itertools.product(range(q), repeat=3) if any(v) and v[[i for i in range(3) if v[i]][0]] == 1])
assert len(coefs) == q * q + q + 1
def try_plane(c):
    V = H.X[c]
    G = (V @ M @ V.T) % q
    if int(round(np.linalg.det(G.astype(float)))) % q == 0: return None
    P = (coefs @ V) % q
    Qv = (P[:, 0] * P[:, 4] + P[:, 1] * P[:, 5] + P[:, 2] * P[:, 6] - P[:, 3] * P[:, 3]) % q
    cp = P[Qv == 0]
    if len(cp) != q + 1: return None
    idx = H.index_of(cp)
    return idx if candmask[idx].all() else None
nc = len(cand := np.nonzero(candmask)[0])
Rsub = R
valid = []; tries = 0; t_sel = time.time()
while len(valid) < a.sel and tries < 2000000 and time.time() - t_sel < a.sel_secs:
    c = cand[rng.integers(nc, size=3)]; tries += 1
    if len(set(c.tolist())) < 3: continue
    cc = try_plane(c)
    if cc is not None and len(set(cc.tolist())) == len(cc): valid.append(cc)
assert valid, 'no conic found'
Ttot = [int((H.Bmat(R, cc) == 0).sum()) for cc in valid]
order = np.argsort(Ttot)
print('valid conics', len(valid), 'after', tries, 'tries; sum|N| min/median', Ttot[order[0]], int(np.median(Ttot)), flush=True)
conic = valid[order[0]]
Bc = H.Bmat(conic, conic); np.fill_diagonal(Bc, 1); assert (Bc != 0).all(), 'conic not pairwise opposite'
print(f'conic found after {tries} tries: points {conic.tolist()}', flush=True)
# ---- base types: bit j of a base point = conic point j is at distance 4 (orthogonal, non-collinear)
w = (1 << np.arange(k)).astype(np.int64)
rbits = ((H.Bmat(R, conic) == 0).astype(np.int64) * w).sum(1)
rb, rc = np.unique(rbits, return_counts=True)
print('base types (pattern: count) sizes:', {int(p): (int(c), bin(int(p)).count('1')) for p, c in zip(rb, rc)} if len(rb) < 40 else f'{len(rb)} distinct patterns', flush=True)
# ---- pool of candidate partner lines and their spread neighbourhoods
pool = rng.choice(np.nonzero(~Sset)[0], size=a.pool, replace=False); npool = len(pool)
LS4 = np.zeros((npool, nS), bool); LS2 = np.zeros((npool, nS), bool)
CH = 1000
for c0 in range(0, npool, CH):
    Lc = pool[c0:c0 + CH]; P = H.lp[Lc]
    conc = Sline[P]
    C = H.lp[H.pl[P]].reshape(len(Lc), -1)
    near = Sline[C]
    r1 = np.repeat(np.arange(c0, c0 + len(Lc)), near.shape[1]); v1 = near.reshape(-1); ok = v1 >= 0
    LS4[r1[ok], v1[ok]] = True
    r2 = np.repeat(np.arange(c0, c0 + len(Lc)), conc.shape[1]); v2 = conc.reshape(-1); ok2 = v2 >= 0
    LS2[r2[ok2], v2[ok2]] = True
LS4 &= ~LS2
print(f'pool ready [{time.time()-t0:.0f}s]', flush=True)
def opp_to(l, others):
    """True if line l is opposite (distance 6) to every line in others (none equal to l)."""
    Cs = np.unique(H.lp[H.pl[H.lp[l]]].reshape(-1))
    for o in others:
        if np.isin(H.lp[o], Cs).any(): return False
    return True
def D_of(pos):
    ex = LS2[pos].any(axis=0)
    bits = LS4[pos].T.astype(np.int64) @ w[:len(pos)]
    ub, cs = np.unique(bits[~ex], return_counts=True)
    p = np.searchsorted(ub, rb); p[p >= len(ub)] = 0
    have = np.where(ub[p] == rb, cs[p], 0)
    return int(np.maximum(0, rc - have).sum())
# ---- anneal the partner lines (positions in pool)
pos = []
while len(pos) < k:
    i = int(rng.integers(npool))
    if i not in pos and opp_to(pool[i], pool[pos]): pos.append(i)
cur = D_of(pos); best = cur; bestpos = list(pos)
def save(p):
    np.savez(os.path.join(a.outdir, 'best.npz'), X=conic, L=pool[np.array(p)], R=R)
save(bestpos)
print(f'start D={cur} F={k-cur} [{time.time()-t0:.0f}s]', flush=True)
ts = time.time(); span = max(1.0, a.secs - (ts - t0)); it = 0
while time.time() - t0 < a.secs:
    it += 1
    frac = min(1.0, (time.time() - ts) / span)
    T = a.T0 * (a.T1 / a.T0) ** frac
    j = int(rng.integers(k)); others = [pool[p] for n_, p in enumerate(pos) if n_ != j]
    cands = []
    for i in rng.integers(npool, size=a.prop):
        i = int(i)
        if i in pos: continue
        if opp_to(pool[i], others): cands.append(i)
    if not cands: continue
    scored = []
    for i in cands:
        p2 = list(pos); p2[j] = i; scored.append((D_of(p2), i))
    dmin = min(s[0] for s in scored)
    dn, i = [s for s in scored if s[0] == dmin][int(rng.integers(sum(1 for s in scored if s[0] == dmin)))]
    if dn <= cur or rng.random() < np.exp(-(dn - cur) / T):
        pos[j] = i; cur = dn
    if cur < best:
        best = cur; bestpos = list(pos); save(bestpos)
        print(f'D={best} F={k-best} it {it} T={T:.3f} [{time.time()-t0:.0f}s]', flush=True)
    if it % 2000 == 0: print(f'  it {it} cur D {cur} best {best} T {T:.3f} [{time.time()-t0:.0f}s]', flush=True)
print(f'final best D={best} F={k-best} iterations {it}; state {os.path.join(a.outdir, "best.npz")}', flush=True)
