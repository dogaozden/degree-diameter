"""Hermitian spreads through a fixed line v of H(q) (q prime): elliptic hyperplanes containing v, and families of
them whose spreads minus v are pairwise point-disjoint. Usage: pencil.py q"""
import itertools, sys, collections
import numpy as np
from hexbin import load

q = int(sys.argv[1])
_, N, lines, crd = load(q)
lines = np.array(lines); crd = np.array(crd, dtype=np.int64)
S = [int(x) for x in open(f'runs/S_q{q}_s1.txt').read().split()]
v = S[0]
V = crd[lines[v]]                       # (q+1) x 7
# dual vectors a with a.x = 0 for all points of v: nullspace of V mod q
def nullspace(M):
    M = M.copy() % q; r = 0; piv = []
    rows, cols = M.shape
    for c in range(cols):
        s = next((i for i in range(r, rows) if M[i, c]), None)
        if s is None: continue
        M[[r, s]] = M[[s, r]]; M[r] = M[r] * pow(int(M[r, c]), q - 2, q) % q
        for i in range(rows):
            if i != r and M[i, c]: M[i] = (M[i] - M[i, c] * M[r]) % q
        piv.append(c); r += 1
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        b = np.zeros(cols, dtype=np.int64); b[f] = 1
        for i, c in enumerate(piv): b[c] = (-M[i, f]) % q
        basis.append(b)
    return np.array(basis)
Bas = nullspace(V)
print('dual space dim', len(Bas))
spreads = []
for coef in itertools.product(range(q), repeat=len(Bas)):
    if next((c for c in coef if c), 0) != 1: continue
    a = (np.array(coef) @ Bas) % q
    inH = (crd @ a) % q == 0
    cont = np.nonzero(inH[lines].all(axis=1))[0]
    if len(cont) == q**3 + 1:
        spreads.append(frozenset(int(k) for k in cont) - {v})
print('elliptic hyperplanes through v:', len(spreads))
pts = [frozenset(int(p) for k in sp for p in lines[k]) for sp in spreads]
inter = collections.Counter()
nsp = len(spreads)
comp = [[j for j in range(nsp) if j != i and not (pts[i] & pts[j])] for i in range(nsp)]
print('disjoint-pair degree distribution', collections.Counter(len(c) for c in comp))
# pairwise shared-line structure
sh = collections.Counter(len(spreads[0] & spreads[j]) for j in range(1, nsp))
print('lines shared with spread 0:', sh)
shp = collections.Counter(len(pts[0] & pts[j]) for j in range(1, nsp))
print('points shared with spread 0:', shp)
# greedy/clique: find q pairwise disjoint
best = []
def ext(cl, cand):
    global best
    if len(cl) > len(best): best = cl[:]
    if len(best) >= q: return
    for i in cand:
        ext(cl + [i], [j for j in cand if j > i and j in set(comp[i])])
        if len(best) >= q: return
ext([], list(range(nsp)))
print('largest pairwise point-disjoint family found:', len(best))
import json
json.dump({'v': v, 'family': [sorted(spreads[i]) for i in best]}, open(f'runs/pencil_q{q}.json', 'w'))
