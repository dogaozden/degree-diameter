#!/usr/bin/env python3
"""genphi.py FAMILY SEED OUT : candidate list for the phi-graph approach of card c7.
Affine points x = (1, a, b, c, c^2 - a e - b f, e, f) with (e, f) = phi(a, b, c) for every (a,b,c) in F_11^3
(one point per s, 1331 points), plus all 16105 points with x0 = 0 (orthogonal to e4).
FAMILY: rand | lin_v (phi = (a,b)+v(c), random v(c)) | quad (random quadratic phi) | norm (F_121 norm/trace maps)"""
import sys, itertools, random, numpy as np
q = 11
fam, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
rng = random.Random(seed)
pts = []
def phi_rand():
    table = {}
    for a, b, c in itertools.product(range(q), repeat=3):
        table[(a, b, c)] = (rng.randrange(q), rng.randrange(q))
    return lambda a, b, c: table[(a, b, c)]
def phi_lin_v():
    # phi = (e,f) = (a, b) + v(c) with v(c) random per level (anisotropic M = identity, see notes)
    v = [(rng.randrange(q), rng.randrange(q)) for _ in range(q)]
    return lambda a, b, c: ((a + v[c][0]) % q, (b + v[c][1]) % q)
def phi_quad():
    # quadratic polynomial map with random coefficients
    coef = [[rng.randrange(q) for _ in range(10)] for _ in range(2)]
    def f(a, b, c):
        mons = [1, a, b, c, a * a, a * b, a * c, b * b, b * c, c * c]
        return tuple(sum(k * m for k, m in zip(coef[i], mons)) % q for i in range(2))
    return f
def phi_norm():
    # F_121 = F_11[i], i^2 = -1 (11 = 3 mod 4). (a,b) -> z = a + b i; (e,f) = (Re, Im) of z^k * lam_c for a random level constant lam_c
    lam = [(rng.randrange(q), rng.randrange(q)) for _ in range(q)]
    def mul(x, y): return ((x[0] * y[0] - x[1] * y[1]) % q, (x[0] * y[1] + x[1] * y[0]) % q)
    def f(a, b, c):
        z = (a, b); w = mul(z, z); w = mul(w, z)  # z^3
        r = mul(w, lam[c]); return r
    return f
fams = {'rand': phi_rand, 'lin_v': phi_lin_v, 'quad': phi_quad, 'norm': phi_norm}
phi = fams[fam]()
for a, b, c in itertools.product(range(q), repeat=3):
    e, f = phi(a, b, c)
    x4 = (c * c - a * e - b * f) % q
    pts.append([1, a, b, c, x4, e, f])
# points with x0 = 0 : x1 x5 + x2 x6 - x3^2 = 0 (x4 free); enumerate normalized
import numpy as np
allp = []
for p in range(1, 7):
    free = 6 - p
    if free == 0:
        g = np.zeros((1, 0), dtype=np.int64)
    else:
        g = np.indices((q,) * free).reshape(free, -1).T.astype(np.int64)
    X = np.zeros((g.shape[0], 7), dtype=np.int64); X[:, p] = 1; X[:, p + 1:] = g
    allp.append(X)
X = np.vstack(allp); X = X[X[:, 0] == 0]
# x0 = 0 normalized points with first nonzero coordinate at index >= 1
Qv = (X[:, 1] * X[:, 5] + X[:, 2] * X[:, 6] - X[:, 3] ** 2) % q
X = X[Qv == 0]
allpts = np.vstack([np.array(pts, dtype=np.int64), X])
np.savetxt(out, allpts, fmt='%d')
print(fam, seed, 'affine', len(pts), 'infinity', len(X), 'written', out)
