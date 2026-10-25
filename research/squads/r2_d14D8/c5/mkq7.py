#!/usr/bin/env python3
"""c5 setup: Sigma-invariant quotient structure of H(7) (Sigma = <g>, |g| = 19) with 2 Sigma-equivariant matchings.
Degree 10 = (q+1) hexagon slots + 2 matching slots per point orbit.

Usage: python3 mkq7.py SEED [level M K]
  writes qstruct_SEED.txt : "NP S D" then NP*D lines "k t" (slot e = D*i + s; s < 8 hexagon, s = 8, 9 matchings)
  with the optional 'level' argument it also writes init_level_SEED.txt : NP*D lines "k t w", voltages in Z_M with
  w = 0 (mod 5) on hexagon slots, 1 / 2 (mod 5) on matchings 1 / 2, and random sub-voltages mod K (CRT, M = 5K).
Base graph for the exact checker: mkbase7.py (same folder) turns (qstruct, voltages) into a lifteval file.
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load

q = 7
HERE = '/home/user/degree-diameter/research/squads/r2_d14D8/c5'
Z = np.load('/home/user/degree-diameter/research/squads/cells/d14D8_work/hex/sym_q7.npz')
S = int(Z['S'])
orbP, shP, repP = Z['orbP'], Z['shP'], Z['repP']
orbL, shL, repL = Z['orbL'], Z['shL'], Z['repL']
N, LP, PL, coord = load(q)
NP = len(repP)
D = q + 3
H = q + 1
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = np.random.default_rng(seed)

K = np.zeros((NP, D), dtype=np.int64)
T = np.zeros((NP, D), dtype=np.int64)
for i in range(NP):
    R = repP[i]
    for j in range(H):
        l = PL[R, j]
        K[i, j] = orbL[l]
        T[i, j] = shL[l]
# matchings: Sigma-equivariant, M_j(g^a R_i) = g^(a+u) R_{pi(i)}; re-draw until no multi-edge inside an orbit
for j in range(2):
    while True:
        pi = rng.permutation(NP)
        u = rng.integers(0, S, NP)
        K2 = K.copy(); T2 = T.copy()
        K2[:, H + j] = pi; T2[:, H + j] = u
        ok = all(len(set(zip(K2[i, :H + j + 1].tolist(), T2[i, :H + j + 1].tolist()))) == H + j + 1 for i in range(NP))
        if ok:
            break
    K, T = K2, T2
assert all(len(set(zip(K[i].tolist(), T[i].tolist()))) == D for i in range(NP))

with open(f'{HERE}/qstruct_{seed}.txt', 'w') as f:
    f.write(f'{NP} {S} {D}\n')
    for i in range(NP):
        for s in range(D):
            f.write(f'{K[i, s]} {T[i, s]}\n')
print(f'wrote qstruct_{seed}.txt: NP {NP}, S {S}, D {D}')

if len(sys.argv) > 2 and sys.argv[2] == 'level':
    M, KK = int(sys.argv[3]), int(sys.argv[4])
    assert M == 5 * KK
    lev = {}
    W = np.zeros((NP, D), dtype=np.int64)
    for i in range(NP):
        for s in range(D):
            lv = 0 if s < H else (1 if s == H else 2)
            sub = int(rng.integers(0, KK))
            # CRT: x = lv mod 5, x = sub mod KK (gcd(5, KK) = 1)
            x = next(x for x in range(M) if x % 5 == lv and x % KK == sub)
            W[i, s] = x
    with open(f'{HERE}/init_level_{seed}.txt', 'w') as f:
        for i in range(NP):
            for s in range(D):
                f.write(f'{K[i, s]} {T[i, s]} {W[i, s]}\n')
    print(f'wrote init_level_{seed}.txt (m={M})')
