"""Group A = <tau, F> of order 93 acting on H(5): tau = Singer torus (as in d8/singer.py), F = Frobenius matrix.
Elements g(i,j) = tau^i F^j, i in 0..30, j in 0..2. Provides point/line permutations (0..N-1) for each element."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/bigcheck-dist/d8')
import hexspec as hs

H = hs.Hex('/tmp/bcdt/hex/hex_q5.bin', '/tmp/bcdt/hex/singer_q5.bin')
q, N = H.q, H.N
assert q == 5
# ---- field F_125 = F_5[x]/h, same choices as singer.py
def irreducible(a, b, c): return all((x**3 + a*x*x + b*x + c) % q for x in range(q))
h = next((a, b, c) for a in range(q) for b in range(q) for c in range(1, q) if irreducible(a, b, c))
def mul(u, v):
    r = [0]*5
    for i in range(3):
        for j in range(3): r[i+j] += u[i]*v[j]
    a, b, c = h
    for d in (4, 3):
        t = r[d]; r[d] = 0
        r[d-1] -= a*t; r[d-2] -= b*t; r[d-3] -= c*t
    return [x % q for x in r[:3]]
def pw(u, e):
    r = [1, 0, 0]
    while e:
        if e & 1: r = mul(r, u)
        u = mul(u, u); e >>= 1
    return r
Q3 = q**3 - 1
def order(u):
    e = Q3
    for pr in [2, 3, 31]:
        while e % pr == 0 and pw(u, e // pr) == [1, 0, 0]: e //= pr
    return e
gen = next(u for u in ([a, b, c] for a in range(q) for b in range(q) for c in range(q)) if any(u) and order(u) == Q3)
theta = pw(gen, q - 1)
M = np.array([mul(theta, [1 if i == j else 0 for i in range(3)]) for j in range(3)]).T % q
A = M.astype(object)
adj = np.array([[(A[(j+1)%3][(i+1)%3]*A[(j+2)%3][(i+2)%3] - A[(j+1)%3][(i+2)%3]*A[(j+2)%3][(i+1)%3]) for j in range(3)] for i in range(3)], dtype=np.int64) % q
assert ((M.astype(np.int64) @ adj) % q == np.eye(3, dtype=np.int64)).all()
# Frobenius x -> x^5: columns = coordinates of (basis_j)^5
F = np.array([pw([1 if i == j else 0 for i in range(3)], q) for j in range(3)]).T % q
Finv = None
# inverse of F mod q by brute Gauss
def inv_mod(X):
    n = X.shape[0]; Aug = np.concatenate([X % q, np.eye(n, dtype=np.int64)], axis=1)
    r = 0
    for c in range(n):
        piv = next(i for i in range(r, n) if Aug[i, c] % q)
        Aug[[r, piv]] = Aug[[piv, r]]
        Aug[r] = (Aug[r] * pow(int(Aug[r, c]), q - 2, q)) % q
        for i in range(n):
            if i != r and Aug[i, c]: Aug[i] = (Aug[i] - Aug[i, c] * Aug[r]) % q
        r += 1
    return Aug[:, n:]
Finv = inv_mod(F)
assert ((F @ Finv) % q == np.eye(3, dtype=np.int64)).all()
assert ((F @ M - (M_pow := np.linalg.matrix_power(M, 5)) @ F) % q == 0).all() or True
# F M F^-1 == M^5 (mod q)
M5 = np.eye(3, dtype=np.int64)
for _ in range(5): M5 = (M5 @ M) % q
assert ((F @ M - M5 @ F) % q == 0).all(), "F does not normalize the torus"
print("det F mod q =", int(round(np.linalg.det(F))) % q, " det M =", int(round(np.linalg.det(M))) % q)

X = H.coord
key = {tuple(c): i for i, c in enumerate(X)}
lkey = {tuple(sorted(l)): i for i, l in enumerate(H.lines)}
def norm(v):
    for x in v:
        if x % q:
            iv = pow(int(x), q - 2, q); return tuple(int(y) * iv % q for y in v)
def point_perm(Mx):
    """x -> Mx x on (X0..X2), y -> Mx^{-T} y on (X4..X6), X3 fixed; Mx in SL(3,q)"""
    Mi = inv_mod(Mx)
    img = np.concatenate([(X[:, 0:3] @ Mx.T) % q, X[:, 3:4], (X[:, 4:7] @ Mi) % q], axis=1)
    return np.array([key[norm(r)] for r in img], dtype=np.int64)
def line_perm(pp):
    return np.array([lkey[tuple(sorted(pp[l]))] for l in H.lines], dtype=np.int64)

tp = H.tp.copy(); tl = H.tl.copy()
pp_t = point_perm(M)
assert (pp_t == tp).all(), "singer reconstruction mismatch"
fp = point_perm(F); fl = line_perm(fp)
print("F maps lines to lines: ok (line_perm found every image)")

def compose(a, b):  # (a o b)[x] = a[b[x]]
    return a[b]
# tau^i, F^j as perms on points and lines
TP = [np.arange(N)]; TL = [np.arange(N)]
for _ in range(30):
    TP.append(tp[TP[-1]]); TL.append(tl[TL[-1]])
FP = [np.arange(N), fp, compose(fp, fp)]; FL = [np.arange(N), fl, compose(fl, fl)]
assert (compose(FP[2], fp) == np.arange(N)).all() and (compose(FL[2], fl) == np.arange(N)).all(), "F^3 != 1"
assert (compose(TP[30], tp) == np.arange(N)).all()
# normalizing check on permutations: F tau F^-1 = tau^5
assert (compose(fp, tp) == compose(TP[5], fp)).all() and (compose(fl, tl) == compose(TL[5], fl)).all()
ELEM = [(i, j) for j in range(3) for i in range(31)]          # index e -> (i, j)
EP = np.zeros((93, N), dtype=np.int64); EL = np.zeros((93, N), dtype=np.int64)
for e, (i, j) in enumerate(ELEM):
    EP[e] = compose(TP[i], FP[j]); EL[e] = compose(TL[i], FL[j])
ids = {(tuple(EP[e]), tuple(EL[e])) for e in range(93)}
assert len(ids) == 93, "group is not of order 93 on H(5)"
print("group A: order 93 verified as pairs of permutations")
# orbits
def orbit_info(P):
    """orbit id of each point, stabilizer (list of element indices) for orbit reps"""
    orb = -np.ones(N, dtype=np.int64); reps = []; stab = []
    for x in range(N):
        if orb[x] >= 0: continue
        o = len(reps); reps.append(x)
        imgs = P[:, x]
        orb[imgs] = o
        stab.append(tuple(int(e) for e in range(93) if imgs[e] == x) if True else None)
    return orb, reps, stab
porb, preps, pstab = orbit_info(EP)
lorb, lreps, lstab = orbit_info(EL)
