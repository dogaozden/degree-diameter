"""Explicit form of the reduced whisker problem on one full S-line l0, for guessing a formula.
X_j = A + jB (j in GF(q)), X_inf = B, with kappa(X_j) = j. Candidate whiskers at X_j: y = y*_j + u Y0, u != 0,
where y*_j is the blocked point of n_{X_j} scaled to L = 1 (u = 0 is n_X), Y0 = B (or A for j = inf).
Prints mu_k(j, u) = alpha u + beta for each pair (j, k).  python3 whisk_formula.py q"""
import sys
from collections import Counter

import numpy as np

q = int(sys.argv[1])
sys.argv = ['hexbig_gf.py', str(q), '60', 'nobuild', '--load']
src = open('hexbig_gf.py').read()
exec(compile(src.split('if build and okfree and okX:')[0], 'hexbig_gf.py', 'exec'))


def f(x):
    return [int(t) for t in x]


def lin(a, x, b, y):  # a x + b y
    return [int(ADD[MUL[a, s], MUL[b, t]]) for s, t in zip(x, y)]


def Lf(x):
    return int(ADD[x[0], MUL[c, x[4]]])


def kap(x):
    return 'inf' if x[5] == 0 else int(MUL[x[2], INV[x[5]]])


def mu(x):
    I = int(ADD[MUL[x[2], x[3]], NEG[MUL[x[4], x[5]]]])
    d = x[5] if x[5] else x[2]
    return int(MUL[I, INV[MUL[d, Lf(x)]]])


full_set = sorted({int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]]) for k in W})
l0 = full_set[int(sys.argv[2]) if len(sys.argv) > 2 else 0]
pts0 = [f(P[p]) for p in lines[l0]]
A = next(x for x in pts0 if x[2] == 0)
B = next(x for x in pts0 if x[5] == 0)
B = [int(MUL[MUL[A[5], INV[B[2]]], t]) for t in B]  # scale so B2 = A5, then kappa(A + jB) = j
Wset = set(W)
alpha, beta, chosen = {}, {}, {}
for j in list(range(q)) + ['inf']:
    X = B if j == 'inf' else lin(1, A, j, B)
    Xi = int(index_of(np.array([X]))[0])
    assert kap(X) == j
    Y0 = A if j == 'inf' else B
    nX = next(int(k) for k in through[Xi] if dist[N + int(k)] == 4)
    Yb = next(f(P[p]) for p in lines[nX] if int(p) != Xi)
    ys = [int(MUL[INV[Lf(Yb)], t]) for t in Yb]
    for u in range(q):
        y = lin(1, ys, u, Y0)
        line_k = int(line_index(np.array([[int(index_of(np.array([lin(1, y, lam, X)]))[0]) for lam in range(q)] + [Xi]]))[0])
        if line_k in Wset:
            chosen[j] = u
        for lam in range(q):
            p = lin(1, y, lam, X)
            beta.setdefault((j, kap(p)), {})[u] = mu(p)
beta = {jk: d for jk, d in beta.items() if jk[0] != jk[1]}
b0 = {}
for (j, k), d in sorted(beta.items(), key=str):
    a = int(ADD[d[2], NEG[d[1]]])
    b = int(ADD[d[1], NEG[a]])
    assert all(d[u] == int(ADD[b, MUL[a, u]]) for u in range(1, q)), 'not affine'
    alpha[(j, k)] = a
    b0[(j, k)] = b
print('chosen u_j:', chosen)
print('alpha[j][k]:')
for j in list(range(q)) + ['inf']:
    print(' j=%s' % j, [alpha.get((j, k), '-') for k in list(range(q)) + ['inf']])
print('beta[j][k] (value at u = 0):')
for j in list(range(q)) + ['inf']:
    print(' j=%s' % j, [b0[(j, k)] if (j, k) in b0 else '-' for k in list(range(q)) + ['inf']])
J = list(range(q)) + ['inf']


def ok(assign):
    for k in J:
        vals = [int(ADD[b0[(j, k)], MUL[alpha[(j, k)], assign[j]]]) for j in J if j != k]
        if len(set(vals)) != q:
            return False
    return True


import itertools
total = sum(1 for us in itertools.product(range(1, q), repeat=q + 1) if ok(dict(zip(J, us)))) if q <= 7 else None
print('number of solutions of the reduced problem:', total, 'of', (q - 1) ** (q + 1))
const = [u for u in range(1, q) for ui in range(1, q) if ok({**{j: u for j in range(q)}, 'inf': ui})]
print('constant u_j (finite j) solutions:', const)
aff = [(a, b, ui) for a in range(q) for b in range(q) for ui in range(1, q)
       if all(int(ADD[MUL[a, j], b]) != 0 for j in range(q)) and ok({**{j: int(ADD[MUL[a, j], b]) for j in range(q)}, 'inf': ui})]
print('affine u_j = a j + b solutions (a, b, u_inf):', aff[:10], len(aff))
sols = [dict(zip(J, us)) for us in itertools.product(range(1, q), repeat=q + 1) if ok(dict(zip(J, us)))] if q <= 7 else []
for s_ in sols[:3]:
    print('solution', s_)
    for j in J:
        print('   j=%-3s' % j, [int(ADD[b0[(j, k)], MUL[alpha[(j, k)], s_[j]]]) if j != k else '-' for k in J])
