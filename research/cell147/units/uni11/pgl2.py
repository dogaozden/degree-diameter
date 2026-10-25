# PGL(2,q) on V' = Sym^4(F_q^2) (+) <n0>: binary quartics f = sum C(4,i) c_i x^(4-i) y^i with the invariant form
# B(f,h) = c0 h4 - 4 c1 h3 + 6 c2 h2 - 4 c3 h1 + c4 h0, and Q(n0) = kappa chosen so that the 6-dim form is elliptic.
# Computes the orbits of PGL(2,q) on the singular points E' and the largest union of pairwise compatible usable orbits
# (exhaustive over orbit subsets when few). Usage: python3 pgl2.py q
import sys, itertools
import numpy as np
q = int(sys.argv[1])
INV = [0] + [pow(a, q - 2, q) for a in range(1, q)]
binom = [1, 4, 6, 4, 1]
# Gram matrix in coordinates (c0..c4, t) where v = sum C(4,i) c_i x^(4-i) y^i + t n0
def gram(kappa):
    G = np.zeros((6, 6), dtype=np.int64)
    for i in range(5): G[i, 4 - i] = ((-1) ** i * binom[i]) % q
    G[5, 5] = (2 * kappa) % q
    return G
allv = np.array(list(itertools.product(range(q), repeat=6)), dtype=np.int64)
nz = allv[np.any(allv != 0, axis=1)]; first = np.argmax(nz != 0, axis=1); P = nz[nz[np.arange(len(nz)), first] == 1]
for kappa in range(1, q):
    G = gram(kappa)
    Qv = np.einsum('ij,jk,ik->i', P, G, P) % q          # = 2 Q(v)
    E = P[Qv == 0]
    if len(E) == (q ** 3 + 1) * (q + 1): break
print("q", q, "kappa", kappa, "points", len(E))
PW = q ** np.arange(6)
key = {int(v): i for i, v in enumerate(E @ PW)}
def normrows(A):
    f_ = np.argmax(A != 0, axis=1); lead = A[np.arange(len(A)), f_]
    return (A * np.array(INV)[lead][:, None]) % q
# action of g = [[a,b],[c,d]] on quartics by substitution f(x,y) -> f(a x + c y, b x + d y)
def quartic_matrix(a, b, c, d):
    # monomial x^(4-i) y^i -> (a x + c y)^(4-i) (b x + d y)^i ; in binomial-scaled coords c_i
    T = np.zeros((5, 5), dtype=np.int64)       # T[j, i]: coefficient of monomial j in image of monomial i
    for i in range(5):
        # expand (a x + c y)^(4-i) (b x + d y)^i
        poly = np.zeros(5, dtype=np.int64); poly[0] = 1
        for _ in range(4 - i): poly = (np.convolve(poly, [a, c])[:5]) % q
        for _ in range(i): poly = (np.convolve(poly, [b, d])[:5]) % q
        T[:, i] = poly
    # convert to binomial-scaled coordinates: monomial coefficient m_j = C(4,j) c_j
    Bm = np.diag(binom) % q; Bmi = np.diag([INV[b % q] for b in binom])
    return (Bmi @ T @ Bm) % q
def act(g):
    a, b, c, d = g
    T = quartic_matrix(a, b, c, d)
    det = (a * d - b * c) % q
    Gm = np.zeros((6, 6), dtype=np.int64); Gm[:5, :5] = T; Gm[5, 5] = det * det % q
    img = normrows((E @ Gm.T) % q)
    return np.array([key[int(v)] for v in img @ PW])
# check the similitude property on the generators and get orbits of PGL(2,q) = <[[1,1],[0,1]], [[w,0],[0,1]], [[0,1],[1,0]]>
w = next(x for x in range(2, q) if all(pow(x, (q - 1) // r, q) != 1 for r in range(2, q) if (q - 1) % r == 0 and all(r % s for s in range(2, r))))
gens = [(1, 1, 0, 1), (w, 0, 0, 1), (0, 1, 1, 0)]
G = gram(kappa)
for g in gens:
    a, b, c, d = g; T = quartic_matrix(a, b, c, d); det = (a * d - b * c) % q
    Gm = np.zeros((6, 6), dtype=np.int64); Gm[:5, :5] = T; Gm[5, 5] = det * det % q
    lhs = (Gm.T @ G @ Gm) % q; mult = pow(det, 4, q)
    assert np.array_equal(lhs, (mult * G) % q), ("not a similitude", g)
perms = [act(g) for g in gens]
N = len(E); par = list(range(N))
def find(x):
    while par[x] != x: par[x] = par[par[x]]; x = par[x]
    return x
for p_ in perms:
    for i in range(N):
        a_, b_ = find(i), find(int(p_[i]))
        if a_ != b_: par[a_] = b_
orbs = {}
for i in range(N): orbs.setdefault(find(i), []).append(i)
orbs = list(orbs.values())
print("orbit sizes:", sorted(len(o) for o in orbs))
Bmat = lambda A, B_: (A @ G @ B_.T) % q
usable = []
for o in orbs:
    A = E[o]; Bo = Bmat(A, A); np.fill_diagonal(Bo, 1)
    if np.all(Bo != 0): usable.append(o)
print("usable orbits:", [len(o) for o in usable])
k = len(usable)
comp = np.zeros((k, k), dtype=bool)
for i in range(k):
    for j in range(i + 1, k):
        comp[i, j] = comp[j, i] = bool(np.all(Bmat(E[usable[i]], E[usable[j]]) != 0))
best = (0, ())
for r in range(1, k + 1):
    for sub in itertools.combinations(range(k), r):
        if all(comp[a_, b_] for a_, b_ in itertools.combinations(sub, 2)):
            s = sum(len(usable[i]) for i in sub)
            if s > best[0]: best = (s, sub)
print("best union:", best[0], "orbits", [len(usable[i]) for i in best[1]])
np.save(f'pgl2_q{q}_E.npy', E); np.save(f'pgl2_q{q}_best.npy', np.concatenate([np.array(usable[i]) for i in best[1]]) if best[1] else np.array([]))
