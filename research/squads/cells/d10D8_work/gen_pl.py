"""gen_pl.py: Z_m lift of I(H(q)) (q prime) + two class-preserving matchings sigma_1, sigma_2 from points to lines.
Point pencil coordinate c(u) = [b(a,u) : b(a',u)] in PG(1,q); line pencil coordinate c'(L) = [A.p : A'.p] with p the
Pluecker vector (21 entries) of the line. Voltages on p -- sigma_t(p): f_t(c(p)).
Usage: python3 gen_pl.py q m seed OUT variant
variant: 'dual'  f1 = 1 + c, f2 = q+2 + c   (blocks B1 = [1,q+1], B2 = -B1 for m = 2q+3)
         'neg'   f1 = 1 + c, f2 = -(1 + c)  (same block family, other sign)
         'rand'  f1, f2 random injective maps PG(1,q) -> Z_m (first q+1 of a random permutation of Z_m minus 0)
sigma_2 is class preserving too (random bijection inside each class), so sigma_1 != sigma_2 generically.
"""
import sys
import itertools
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load

q, m, seed, out, variant = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
N, LP, PL, coord = load(q)
assert all(q == int(q) for _ in [0])
C = coord.astype(np.int64) % q
rng = np.random.default_rng(seed)

PAIRS = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]


def bform_vec(X, a):
    """b(a, x) for all rows x of X (q prime)."""
    s = np.zeros(X.shape[0], dtype=np.int64)
    for i, j in PAIRS:
        s += a[i] * X[:, j]
    s -= 2 * a[3] * X[:, 3]
    return s % q


def proj_class(V, a, a2):
    """(s:t) = (b(a,v) : b(a2,v)) style: here V already contains the values s and t columns."""
    raise NotImplementedError


def pencil(s, t):
    """class in 0..q (q = infinity, t==0) from numeric (s,t) columns; -1 if both zero."""
    cls = np.full(len(s), -1, dtype=np.int64)
    nz = t != 0
    inv = np.array([0] + [pow(int(x), q - 2, q) for x in range(1, q)], dtype=np.int64)
    cls[nz] = (s[nz] * inv[t[nz]]) % q
    cls[(~nz) & (s != 0)] = q
    return cls

# point pencil coordinate
a = rng.integers(0, q, 7); a2 = rng.integers(0, q, 7)
cP = pencil(bform_vec(C, a), bform_vec(C, a2))
# Pluecker coordinates of lines (span of two of its points)
X = C[LP[:, 0]]; Y = C[LP[:, 1]]
P21 = np.stack([(X[:, i] * Y[:, j] - X[:, j] * Y[:, i]) % q for i, j in itertools.combinations(range(7), 2)], axis=1)
A = rng.integers(0, q, 21); A2 = rng.integers(0, q, 21)
cL = pencil((P21 @ A) % q, (P21 @ A2) % q)
spP = (cP < 0); spL = (cL < 0)
cP = np.where(spP, rng.integers(0, q + 1, N), cP)
cL = np.where(spL, rng.integers(0, q + 1, N), cL)
print(f'q {q} m {m}: special points {spP.sum()}, special lines {spL.sum()}', file=sys.stderr)


def class_matching(cpt, cln, rng_):
    """bijection points -> lines, class kappa to class kappa as far as possible (random inside classes)."""
    sigma = np.full(N, -1, dtype=np.int64)
    used = np.zeros(N, dtype=bool)
    left_p = []
    for k in range(q + 1):
        P = rng_.permutation(np.where(cpt == k)[0])
        L = rng_.permutation(np.where(cln == k)[0])
        L = L[~used[L]]
        r = min(len(P), len(L))
        sigma[P[:r]] = L[:r]; used[L[:r]] = True
        left_p.extend(P[r:].tolist())
    free_l = rng_.permutation(np.where(~used)[0])
    for p, l in zip(left_p, free_l):
        sigma[p] = l
    assert len(set(sigma.tolist())) == N
    return sigma

sig1 = class_matching(cP, cL, rng)
sig2 = class_matching(cP, cL, rng)

if variant == 'dual':
    f1 = 1 + np.arange(q + 1); f2 = q + 2 + np.arange(q + 1)
elif variant == 'neg':
    f1 = 1 + np.arange(q + 1); f2 = (-(1 + np.arange(q + 1))) % m
elif variant == 'rand':
    perm = rng.permutation(np.arange(1, m))
    f1 = perm[:q + 1]; f2 = perm[q + 1:2 * (q + 1)]
else:
    raise SystemExit('bad variant')
f1 = np.asarray(f1) % m; f2 = np.asarray(f2) % m

with open(out, 'w') as f:
    f.write(f'Z {m}\n{2 * N}\n')
    f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
    for l in range(N):
        for p in LP[l]:
            f.write(f'{p} {N + l} 0\n')
    for p in range(N):
        cls = cP[p]
        f.write(f'{p} {N + sig1[p]} {f1[cls] % m}\n')
        f.write(f'{p} {N + sig2[p]} {f2[cls] % m}\n')
print(f'wrote {out}', file=sys.stderr)
