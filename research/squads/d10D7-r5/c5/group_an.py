# c5: analyse the stabiliser group of the H(7) 288-set (matrices from stab7.c; projective normalisation: first nonzero entry = 1)
import numpy as np, sys, random
from collections import Counter
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c5')
from h7 import *
q = 7
INV = np.array([0, 1, 4, 5, 2, 3, 6])
def pnorm(M):
    M = M % q
    f = M.flatten(); nz = np.nonzero(f)[0][0]
    return ((M * INV[f[nz]]) % q)
mats = []
for l in open(sys.argv[1]):
    t = l.split()
    if len(t) == 49: mats.append(pnorm(np.array(list(map(int, t))).reshape(7, 7)))
keys = {}
for M in mats: keys[tuple(M.flatten())] = M
G = list(keys.values())
print('projective elements', len(G))
def key(M): return tuple(M.flatten())
def mul(A, B): return (A @ B) % q
# closure sample
rng = random.Random(5)
bad = 0
for _ in range(300):
    A = rng.choice(G); B = rng.choice(G)
    if key(pnorm(mul(A, B))) not in keys: bad += 1
print('closure failures in 300 random products:', bad)
# element orders
def order(M):
    P = M.copy(); k = 1; I = pnorm(np.eye(7, dtype=np.int64))
    while key(P) != key(I):
        P = pnorm(mul(P, M)); k += 1
        if k > 10000: return -1
    return k
oc = Counter(order(M) for M in G[:4000])
print('element orders (first 4000):', sorted(oc.items()))
