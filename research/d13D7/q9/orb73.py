#!/usr/bin/env python3
"""Find an ovoid of Q(6,9) as a union of 10 orbits of an element g of order 73 of O(7,9) (side quest, (11,7)).
F_9 = F_3[al], al^2 = 2, index a + 3b (as hexgen.c).  Q(x) = x0x4 + x1x5 + x2x6 - x3^2, B(x,y) its polar form.
usage: orb73.py HEX_Q9_BIN OUT_IDX [seed]"""
import sys, numpy as np, itertools, random
sys.path.insert(0, '../tools')
import hexlib
q, lines, coord = hexlib.load(sys.argv[1]); N = len(coord)
assert q == 9
A = np.zeros((9, 9), int); M = np.zeros((9, 9), int)
for x in range(9):
    for y in range(9):
        a, b, c, d = x % 3, x // 3, y % 3, y // 3
        A[x, y] = (a + c) % 3 + 3 * ((b + d) % 3)
        M[x, y] = (a * c + 2 * b * d) % 3 + 3 * ((a * d + b * c) % 3)
NEG = np.array([[y for y in range(9) if A[x, y] == 0][0] for x in range(9)])
INV = np.array([0] + [[y for y in range(9) if M[x, y] == 1][0] for x in range(1, 9)])
def vadd(u, v): return A[u, v]
def dot(u, v):  # sum of products
    s = 0
    for a, b in zip(u, v): s = A[s, M[a, b]]
    return s
J = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]
def Bf(x, y):
    s = 0
    for i, j in J: s = A[s, M[x[i], y[j]]]
    m2 = M[2, M[x[3], y[3]]]   # 2 x3 y3
    return A[s, NEG[m2]]
def Qf(x):
    s = A[A[M[x[0], x[4]], M[x[1], x[5]]], M[x[2], x[6]]]
    return A[s, NEG[M[x[3], x[3]]]]
def matmul(P, R):
    out = np.zeros((7, 7), int)
    for i in range(7):
        for j in range(7):
            s = 0
            for k in range(7): s = A[s, M[P[i, k], R[k, j]]]
            out[i, j] = s
    return out
def reflection(v):
    qv = Qf(v); iq = INV[qv]
    # r(x) = x - B(x,v)/Q(v) v ; matrix columns = images of basis vectors
    R = np.zeros((7, 7), int)
    for j in range(7):
        e = [0] * 7; e[j] = 1
        c = M[Bf(e, v), iq]
        R[:, j] = [A[e[i], NEG[M[c, v[i]]]] for i in range(7)]
    return R
I7 = np.eye(7, dtype=int)
def order(g, cap=20000):
    h = g.copy()
    for k in range(1, cap):
        if (h == I7).all(): return k
        h = matmul(h, g)
    return None
def power(g, e):
    r = I7.copy(); b = g.copy()
    while e:
        if e & 1: r = matmul(r, b)
        b = matmul(b, b); e >>= 1
    return r
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
g73 = None
for trial in range(400):
    g = I7.copy()
    for _ in range(9):
        while True:
            v = [rng.randrange(9) for _ in range(7)]
            if Qf(v) != 0: break
        g = matmul(g, reflection(v))
    o = order(g)
    if o and o % 73 == 0:
        g73 = power(g, o // 73); print('trial', trial, 'element order', o); break
assert g73 is not None and order(g73) == 73
# act on points: x -> g x (column vectors), normalise
code = coord @ (9 ** np.arange(7))
P = coord.astype(int)
def act(X):
    Y = np.zeros_like(X)
    for i in range(7):
        s = np.zeros(len(X), int)
        for k in range(7): s = A[s, M[g73[i, k], X[:, k]]]
        Y[:, i] = s
    # normalise first nonzero to 1
    first = np.argmax(Y != 0, axis=1)
    lead = Y[np.arange(len(Y)), first]
    inv = INV[lead]
    Y = M[inv[:, None], Y]
    return Y
Y = act(P)
img = np.searchsorted(code, Y @ (9 ** np.arange(7)))
assert (code[img] == Y @ (9 ** np.arange(7))).all()
# orbits
seen = np.zeros(N, bool); orbits = []
for s in range(N):
    if seen[s]: continue
    orb = [s]; seen[s] = True; t = img[s]
    while t != s:
        orb.append(t); seen[t] = True; t = img[t]
    orbits.append(orb)
sizes = sorted({len(o) for o in orbits}); print('orbits', len(orbits), 'sizes', sizes)
# B as integer matrix ops: precompute coordinates
def gram(Xa, Xb):
    S = np.zeros((len(Xa), len(Xb)), int)
    for i, j in J: S = A[S, M[Xa[:, i][:, None], Xb[:, j][None, :]]]
    m2 = M[2, M[Xa[:, 3][:, None], Xb[:, 3][None, :]]]
    return A[S, NEG[m2]]
good = []
for o in orbits:
    G = gram(P[o], P[o]); np.fill_diagonal(G, 1)
    if (G != 0).all(): good.append(o)
print('good orbits (internally pairwise opposite):', len(good), 'sizes', sorted({len(o) for o in good}))
K = len(good)
comp = np.zeros((K, K), bool)
for i in range(K):
    Xi = P[good[i]]
    for j in range(i + 1, K):
        comp[i, j] = comp[j, i] = (gram(Xi, P[good[j]]) != 0).all()
print('compatibility edges:', comp.sum() // 2)
# max weight clique by simple branch and bound (weights = sizes; target 730)
w = np.array([len(o) for o in good])
best = [0, []]
order_ = sorted(range(K), key=lambda i: -comp[i].sum())
def bb(cand, cur, wt):
    if wt > best[0]: best[0] = wt; best[1] = cur[:]; print('  clique weight', wt, flush=True)
    if best[0] >= 730: return
    if wt + w[cand].sum() <= best[0]: return
    for idx, v in enumerate(cand):
        if wt + w[cand[idx:]].sum() <= best[0]: return
        nc = [u for u in cand[idx + 1:] if comp[v, u]]
        bb(np.array(nc, int), cur + [v], wt + w[v])
        if best[0] >= 730: return
bb(np.array(order_, int), [], 0)
pts = sorted(p for i in best[1] for p in good[i])
print('best union size', len(pts))
open(sys.argv[2], 'w').write(f'# {len(pts)} pairwise opposite points of H(9): union of orbits of an element of order 73\n' + '\n'.join(map(str, pts)) + '\n')
