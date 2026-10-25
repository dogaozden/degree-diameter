#!/usr/bin/env python3
"""Random isometries of E_q = {x in W : Q(x) = 0}, W = {x4 = -C x0} (dim 6), as permutations of the points of E_q.
Usage: orbit_perm.py Q SEED K TARGET_ORDER OUTPERM
 g = product of K random reflections r_v (v in W, Q(v) != 0), B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3, Q = B/2.
 Its power g^(o/t) has order t (o = order of g on E); OUTPERM gets one line per vertex of E_q (its image).
 Prints: order of g, order of the power, number of orbits, sizes of orbits."""
import sys, math, random
import numpy as np
q, seed, K, T = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); out = sys.argv[5]
C = {5: 2, 7: 1, 11: 1, 13: 11}[q]
rows = np.loadtxt(f'../data/E{q}.map', dtype=np.int64)
X = rows[:, 2:9] % q
N = len(X)
def norm(Y):
    Y = Y % q
    idx = np.argmax(Y != 0, axis=1)
    lead = Y[np.arange(len(Y)), idx]
    inv = np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)
    return (Y * inv[lead][:, None]) % q
Xn = norm(X)
assert np.all(Xn[:, 4] == (-C * Xn[:, 0]) % q), 'points not in W'
pw = q ** np.arange(7, dtype=np.int64)
key = Xn @ pw
order_idx = np.argsort(key); skey = key[order_idx]
def index_of(Y):
    k = norm(Y) @ pw
    pos = np.searchsorted(skey, k)
    assert np.all(skey[np.minimum(pos, N - 1)] == k), 'image not a point of E'
    return order_idx[pos]
M = np.zeros((7, 7), dtype=np.int64)
M[0, 4] = M[4, 0] = 1; M[1, 5] = M[5, 1] = 1; M[2, 6] = M[6, 2] = 1; M[3, 3] = -2
def Qf(v): return int((v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q)
rng = random.Random(seed)
def rand_refl():
    while True:
        v = np.array([rng.randrange(q) for _ in range(7)], dtype=np.int64)
        v[4] = (-C * v[0]) % q
        Qv = Qf(v)
        if Qv != 0: break
    inv = pow(Qv, q - 2, q)
    R = np.eye(7, dtype=np.int64) - np.outer(v, M @ v) * inv
    return R % q
def perm_of(g):
    img = index_of((g @ X.T).T)
    return img
def cycles(p):
    seen = np.zeros(len(p), bool); cyc = []
    for i in range(len(p)):
        if seen[i]: continue
        c = []; j = i
        while not seen[j]: seen[j] = True; c.append(j); j = p[j]
        cyc.append(c)
    return cyc
def order_of(p):
    o = 1
    for c in cycles(p): o = o * len(c) // math.gcd(o, len(c))
    return o
def pow_perm(p, e):
    r = np.arange(len(p)); b = p.copy()
    while e:
        if e & 1: r = b[r]
        b = b[b]; e >>= 1
    return r
g = np.eye(7, dtype=np.int64)
for _ in range(K): g = (g @ rand_refl()) % q
p = perm_of(g)
o = order_of(p)
# choose the power of order T (T must divide o)
if o % T != 0:
    print(f'order {o} not divisible by {T}'); sys.exit(3)
pt = pow_perm(p, o // T)
assert order_of(pt) == T
with open(out, 'w') as f:
    for v in pt: f.write(f'{int(v)}\n')
cyc = cycles(pt)
from collections import Counter
print(f'g order {o}; power order {order_of(pt)}; orbits {len(cyc)}; orbit sizes {dict(Counter(len(c) for c in cyc))}')
