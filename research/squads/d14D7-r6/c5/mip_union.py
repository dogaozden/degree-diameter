#!/usr/bin/env python3
"""Exact-ish selection of image lines for a FIXED configuration (X, L) from the union of several spreads (dual ovoids).
Variables: x_a in {0,1} for every pool line a that is not concurrent with any L_j (usable); pairwise opposition of the
chosen lines is enforced by x_a + x_b <= 1 for every pair of pool lines that are not opposite (concurrent or at
distance 4); per base type tau: sum_{a of type tau} x_a + y_tau >= demand(tau); minimise sum y (= base points dropped).
F = k - sum y.  The selected lines are saved as a spread file for mirror_build_g.py (which re-checks everything).
usage: mip_union.py STATE.npz OUT.npy --spread A.npy [--spread B.npy] [--secs 200]"""
import numpy as np, sys, os, time, argparse
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
ap = argparse.ArgumentParser(); ap.add_argument('state'); ap.add_argument('out')
ap.add_argument('--spread', action='append', default=[]); ap.add_argument('--secs', type=float, default=200)
a = ap.parse_args()
t0 = time.time()
sys.path.append(SP + 'r6_c5/pylib')          # scratch-only install of highspy (appended, so system numpy wins)
import highspy
H = Hex(SP + 'hex_q11.bin'); N = H.N; lp = H.lp
st = np.load(a.state); R = st['R']; Xs = st['X']; Ls = st['L']; k = len(Xs)
spreads = [np.load(f) for f in a.spread]
pool = np.unique(np.concatenate(spreads)); npl = len(pool); P = lp[pool]
assert not np.isin(pool, Ls).any()
pp = -np.ones((N, 2), dtype=np.int64)
for i in range(npl):
    for p in P[i]:
        if pp[p, 0] < 0: pp[p, 0] = i
        else:
            assert pp[p, 1] < 0, 'point on three pool lines'; pp[p, 1] = i
conc_bad = np.zeros(npl, bool); typ = [set() for _ in range(npl)]
for j, l in enumerate(Ls):
    pts = lp[l]
    cc = pp[pts].ravel(); cc = np.unique(cc[cc >= 0]); conc_bad[cc] = True
    C = np.unique(lp[H.pl[pts]].ravel())
    d4 = pp[C].ravel(); d4 = np.unique(d4[d4 >= 0])
    for i in d4: typ[i].add(j)
usable = np.nonzero(~conc_bad)[0]; uid = -np.ones(npl, dtype=np.int64); uid[usable] = np.arange(len(usable))
nx = len(usable)
# conflicts (non-opposite pairs) among usable pool lines
edges = set()
for i in usable:
    C = np.unique(lp[H.pl[P[i]]].ravel())
    b = pp[C].ravel(); b = np.unique(b[b >= 0])
    for j in b:
        if j != i and uid[j] >= 0 and i < j: edges.add((int(uid[i]), int(uid[j])))
edges = sorted(edges)
inS = np.isin(pool, np.concatenate([spreads[0]]))
ss = sum(1 for (u, v) in edges if inS[usable[u]] and inS[usable[v]])
print(f'pool {npl} usable {nx} conflict edges {len(edges)} (inside first spread: {ss}) [{time.time()-t0:.0f}s]', flush=True)
# base types and supply
NR = (H.Bmat(Xs, R) == 0)
tR = [frozenset(np.nonzero(NR[:, r])[0].tolist()) for r in range(len(R))]
dem = Counter(tR)
supply = {}
for u, i in enumerate(usable):
    supply.setdefault(frozenset(typ[i]), []).append(u)
types = list(dem.keys()); ny = len(types)
print('base types', ny, 'with supply', sum(1 for t in types if t in supply), flush=True)
# model: columns x (nx binaries), y (ny integers)
h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('time_limit', float(a.secs))
ncol = nx + ny
lo = np.zeros(ncol); hi = np.ones(ncol)
hi[nx:] = np.array([dem[t] for t in types], dtype=float)
h.addVars(ncol, lo, hi)
cost = np.zeros(ncol); cost[nx:] = 1.0
h.changeColsCost(ncol, np.arange(ncol, dtype=np.int32), cost)
kint = highspy.HighsVarType.kInteger
h.changeColsIntegrality(ncol, np.arange(ncol, dtype=np.int32), np.array([kint] * ncol))
# rows
rl, ru, starts, idx, val = [], [], [], [], []
def addrow(ids, vals, low, up):
    starts.append(len(idx)); idx.extend(ids); val.extend(vals); rl.append(low); ru.append(up)
for (u, v) in edges: addrow([u, v], [1.0, 1.0], -highspy.kHighsInf, 1.0)
for ti, t in enumerate(types):
    ids = list(supply.get(t, [])) + [nx + ti]
    vals = [1.0] * (len(ids) - 1) + [1.0]
    addrow(ids, vals, float(dem[t]), highspy.kHighsInf)
starts = np.array(starts, dtype=np.int32); idx = np.array(idx, dtype=np.int32); val = np.array(val, dtype=np.float64)
h.addRows(len(rl), np.array(rl, dtype=np.float64), np.array(ru, dtype=np.float64), len(idx), starts, idx, val)
print(f'model: {ncol} columns, {len(rl)} rows [{time.time()-t0:.0f}s]; solving', flush=True)
h.run()
sol = np.array(h.getSolution().col_value)
obj = h.getInfo().objective_function_value
dropped = int(round(sum(sol[nx + ti] for ti in range(ny))))
sel = pool[usable[np.nonzero(sol[:nx] > 0.5)[0]]]
# independence re-check of the selection
selset = set(int(u) for u in np.nonzero(sol[:nx] > 0.5)[0])
bad = sum(1 for (u, v) in edges if u in selset and v in selset)
np.save(a.out, sel.astype(np.int64))
print(f'status {h.getModelStatus()} objective (drops) {obj} -> F = {k} - {dropped} = {k - dropped}; selected {len(sel)} lines; '
      f'conflicting pairs in selection {bad} [{time.time()-t0:.0f}s]', flush=True)
