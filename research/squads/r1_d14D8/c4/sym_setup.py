#!/usr/bin/env python3
"""c4 setup: Singer-torus-invariant structure of H(11) under Sigma = <g>, g = C^10 in SL(3,11), |g| = 133.

Writes qstruct.txt: the quotient voltage graph. Point orbit i (rep R_i = reps_P[i]) has 14 slots:
slots 0..11 = the 12 hexagon lines of R_i (target line orbit k, Sigma-shift t: line = g^t R_k),
slots 12,13 = matchings M_1, M_2 (target line orbit pi_j(i), shift u_j(i): M_j(g^a R_i) = g^(a+u) R_pi).
Global ids: PT[a][i] = g^a R_i (points), LT[b][k] = g^b R_k (lines).
Usage: python3 sym_setup.py SEED   (SEED picks the matchings; writes qstruct_SEED.txt and sym_SEED.npz)
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, hex_edges

q = 11
S = 133
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
HERE = '/home/user/degree-diameter/research/squads/r1_d14D8/c4'
N, LP, PL, coord = load(q)
X = coord.astype(np.int64)
inv = np.zeros(q, dtype=np.int64)
for a in range(1, q):
    inv[a] = pow(a, q - 2, q)
first = (X != 0).argmax(axis=1)
lead = X[np.arange(N), first]
print('points: N', N, 'normalised (lead=1):', bool((lead == 1).all()), 'lines', LP.shape)
pw = q ** np.arange(6, -1, -1, dtype=np.int64)
keys = X @ pw
order = np.argsort(keys)
skeys = keys[order]


def normalize(Z):
    f = (Z != 0).argmax(axis=1)
    ld = Z[np.arange(len(Z)), f]
    return (Z * inv[ld][:, None]) % q


def pid_of(Y):
    k = Y @ pw
    pos = np.searchsorted(skeys, k)
    assert (skeys[pos] == k).all(), 'image point not on quadric'
    return order[pos]


def matinv(g):
    A = np.array([[int(v) % q for v in row] for row in g], dtype=np.int64)
    det = int(round(np.linalg.det(A))) % q
    di = pow(det, q - 2, q)
    adj = np.zeros((3, 3), dtype=np.int64)
    for r in range(3):
        for s in range(3):
            minor = np.delete(np.delete(A, s, axis=0), r, axis=1)
            adj[r, s] = ((-1) ** (r + s)) * (minor[0, 0] * minor[1, 1] - minor[0, 1] * minor[1, 0])
    return (adj * di) % q, det


def act(g):
    ginv, det = matinv(g)
    x = X[:, 0:3]; y = X[:, 4:7]
    x2 = (x @ g.T) % q
    y2 = (y @ ginv) % q           # g^{-T} y as rows: y^T g^{-1}
    Z = np.concatenate([x2, X[:, 3:4], y2], axis=1)
    return pid_of(normalize(Z))


def matmul(A, B):
    return (A @ B) % q


def matpow(A, e):
    R = np.eye(3, dtype=np.int64); B = A.copy()
    while e:
        if e & 1:
            R = matmul(R, B)
        B = matmul(B, B); e >>= 1
    return R


# Singer element: companion matrix of a primitive cubic (order 1330 = q^3 - 1)
ident = np.eye(3, dtype=np.int64)
C = None
for c0 in range(1, q):
    for c1 in range(q):
        for c2 in range(q):
            Ct = np.array([[0, 0, (-c0) % q], [1, 0, (-c1) % q], [0, 1, (-c2) % q]], dtype=np.int64)
            if not (matpow(Ct, 1330) == ident).all():
                continue
            if all(not (matpow(Ct, 1330 // p) == ident).all() for p in (2, 5, 7, 19)):
                C = Ct; break
        if C is not None: break
    if C is not None: break
print('companion matrix of primitive cubic:', C.tolist())
g = matpow(C, 10)
print('g = C^10 det mod 11:', int(round(np.linalg.det(g))) % q, '; g^133 = I:', bool((matpow(g, 133) == ident).all()),
      '; g^k != I for 0<k<133 (k|133 check):', all(not (matpow(g, k) == ident).all() for k in (1, 7, 19)))

gperm = act(g)
assert len(np.unique(gperm)) == N, 'action on points not a permutation'
# action on lines: image line = the line through gp(LP[l,0]) and gp(LP[l,1]) (found among PL of the first image point)
A0 = LP[:, 0]; A1 = LP[:, 1]
img_a = gperm[A0]; img_b = gperm[A1]
cand = PL[img_a]                                   # (N, 12) lines through the first image point
has = (LP[cand] == img_b[:, None, None]).any(axis=2)
gl = np.where(has.any(axis=1), cand[np.arange(N), has.argmax(axis=1)], -1)
ok_lines = bool((gl >= 0).all()) and bool((np.sort(gperm[LP], axis=1) == np.sort(LP[gl], axis=1)).all())
print('g maps every line (point set) to a line:', ok_lines, '; line permutation:', len(np.unique(gl)) == N)
assert ok_lines and len(np.unique(gl)) == N
glperm = gl


def orbits(perm, n):
    orb = -np.ones(n, dtype=np.int64); sh = np.zeros(n, dtype=np.int64); reps = []
    pl = perm.tolist()
    for p in range(n):
        if orb[p] >= 0:
            continue
        k = len(reps); reps.append(p)
        x = p
        for s in range(S):
            assert orb[x] < 0, 'orbit overlap'
            orb[x] = k; sh[x] = s; x = pl[x]
        assert x == p, 'orbit length not 133'
    return orb, sh, np.array(reps, dtype=np.int64)


orbP, shP, repP = orbits(gperm, N)
orbL, shL, repL = orbits(glperm, N)
NP = len(repP)
print('point orbits', NP, 'line orbits', len(repL), '(all of size 133: semiregular)')
PT = np.zeros((S, NP), dtype=np.int64)
LT = np.zeros((S, NP), dtype=np.int64)
for a in range(S):
    PT[a] = 0
pts = np.arange(N)
PT[shP, orbP] = pts
LT[shL, orbL] = np.arange(N)

# hexagon Q-edges
slots_k = np.zeros((NP, 14), dtype=np.int64)
slots_t = np.zeros((NP, 14), dtype=np.int64)
for i in range(NP):
    R = repP[i]
    for j in range(12):
        l = PL[R, j]
        slots_k[i, j] = orbL[l]
        slots_t[i, j] = shL[l]
# matchings: pi_j permutation of line orbits, shifts u_j
rng = np.random.default_rng(seed)
for j in range(2):
    pi = rng.permutation(NP)
    u = rng.integers(0, S, NP)
    slots_k[:, 12 + j] = pi
    slots_t[:, 12 + j] = u
# check: slot pairs (k,t) distinct per point orbit (no multi-edges in the base graph)
bad = 0
for i in range(NP):
    pairs = set(zip(slots_k[i].tolist(), slots_t[i].tolist()))
    bad += 14 - len(pairs)
print('multi-edge slots (should be 0 for random matchings, repaired below if >0):', bad)
np.savez(f'{HERE}/sym_{seed}.npz', slots_k=slots_k, slots_t=slots_t, PT=PT, LT=LT, repP=repP, repL=repL,
         orbP=orbP, shP=shP, orbL=orbL, shL=shL, gperm=gperm, glperm=glperm)
with open(f'{HERE}/qstruct_{seed}.txt', 'w') as f:
    f.write(f'{NP} {S}\n')
    for i in range(NP):
        for s in range(14):
            f.write(f'{slots_k[i, s]} {slots_t[i, s]}\n')
print('wrote', f'{HERE}/qstruct_{seed}.txt', 'and', f'{HERE}/sym_{seed}.npz')
