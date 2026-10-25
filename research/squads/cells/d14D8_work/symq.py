"""symq.py q: the Singer-type cyclic group Sigma = <g>, |g| = q^2+q+1, inside SL(3,q) <= G_2(q), ((q^2+q+1)/3 when q = 1 mod 3) acting semiregularly on
the points and lines of H(q) (q prime). Generalizes squads/r1_d14D8/c4/sym_setup.py (q = 11 only).
Writes hex/sym_q{q}.npz with: S = |Sigma|; gperm, glperm (action of g on point ids and line ids);
orbP, shP (point p = g^shP[p] repP[orbP[p]]), repP; orbL, shL, repL likewise.
Use: z = np.load('hex/sym_q7.npz'); points of orbit i: g^a R_i has id PT[a, i] where PT[shP, orbP] = arange(N)."""
import sys
import numpy as np
from hexlib import load, HERE
q = int(sys.argv[1])
N, LP, PL, coord = load(q)
X = coord.astype(np.int64)
inv = np.zeros(q, dtype=np.int64)
for a in range(1, q): inv[a] = pow(a, q - 2, q)
pw = q ** np.arange(6, -1, -1, dtype=np.int64)
keys = X @ pw; order = np.argsort(keys); skeys = keys[order]
def normalize(Z):
    f = (Z != 0).argmax(axis=1); ld = Z[np.arange(len(Z)), f]
    return (Z * inv[ld][:, None]) % q
def pid_of(Y):
    k = Y @ pw; pos = np.searchsorted(skeys, k)
    assert (skeys[pos] == k).all(), 'image point not on quadric'
    return order[pos]
def matinv(A):
    det = int(round(np.linalg.det(A))) % q; di = pow(det, q - 2, q)
    adj = np.zeros((3, 3), dtype=np.int64)
    for r in range(3):
        for s in range(3):
            minor = np.delete(np.delete(A, s, axis=0), r, axis=1)
            adj[r, s] = ((-1) ** (r + s)) * (minor[0, 0] * minor[1, 1] - minor[0, 1] * minor[1, 0])
    return (adj * di) % q
def act(g):
    ginv = matinv(g)
    Z = np.concatenate([(X[:, 0:3] @ g.T) % q, X[:, 3:4], (X[:, 4:7] @ ginv) % q], axis=1)
    return pid_of(normalize(Z))
def matpow(A, e):
    R = np.eye(3, dtype=np.int64); B = A.copy()
    while e:
        if e & 1: R = (R @ B) % q
        B = (B @ B) % q; e >>= 1
    return R
def primes(n):
    out, d = [], 2
    while d * d <= n:
        while n % d == 0: out.append(d); n //= d
        d += 1
    if n > 1: out.append(n)
    return sorted(set(out))
O = q ** 3 - 1; I3 = np.eye(3, dtype=np.int64); C = None
for c0 in range(1, q):
    for c1 in range(q):
        for c2 in range(q):
            Ct = np.array([[0, 0, (-c0) % q], [1, 0, (-c1) % q], [0, 1, (-c2) % q]], dtype=np.int64)
            if (matpow(Ct, O) == I3).all() and all(not (matpow(Ct, O // p) == I3).all() for p in primes(O)):
                C = Ct; break
        if C is not None: break
    if C is not None: break
S = q * q + q + 1
g = matpow(C, q - 1)
if q % 3 == 1:  # the order-3 part of the torus is scalar there and has fixed points: use the index-3 subgroup
    S //= 3; g = matpow(C, 3 * (q - 1))
assert (matpow(g, S) == I3).all()
gperm = act(g)
assert len(np.unique(gperm)) == N
img_a = gperm[LP[:, 0]]; img_b = gperm[LP[:, 1]]
cand = PL[img_a]; has = (LP[cand] == img_b[:, None, None]).any(axis=2)
gl = np.where(has.any(axis=1), cand[np.arange(N), has.argmax(axis=1)], -1)
assert (gl >= 0).all() and (np.sort(gperm[LP], axis=1) == np.sort(LP[gl], axis=1)).all() and len(np.unique(gl)) == N
def orbits(perm):
    orb = -np.ones(N, dtype=np.int64); sh = np.zeros(N, dtype=np.int64); reps = []; pl = perm.tolist()
    for p in range(N):
        if orb[p] >= 0: continue
        k = len(reps); reps.append(p); x = p
        for s in range(S):
            assert orb[x] < 0; orb[x] = k; sh[x] = s; x = pl[x]
        assert x == p, 'orbit length not S'
    return orb, sh, np.array(reps, dtype=np.int64)
orbP, shP, repP = orbits(gperm); orbL, shL, repL = orbits(gl)
np.savez(HERE / 'hex' / f'sym_q{q}.npz', S=S, gperm=gperm, glperm=gl, orbP=orbP, shP=shP, repP=repP,
         orbL=orbL, shL=shL, repL=repL)
print(f'q={q}: Sigma order {S}, {len(repP)} point orbits, {len(repL)} line orbits (semiregular); wrote hex/sym_q{q}.npz')
