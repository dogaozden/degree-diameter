"""Hub graph for the (15,7) build: the Haar graph of PSL(2,p) on a set S of 8 elements (vectorized version of
psl_hubgraph.py). Line-side hub x ~ point-side hub x s (x in G, s in S). Same-side hub distances <= 6 iff
(S S^-1)^3 = G (line side) and (S^-1 S)^3 = G (point side); S is improved by hill climbing until both hold.
Output: first line K = |G|, then "a b" per edge (a line-side, b point-side index).
Usage: python psl_hubgraph2.py p SEED OUT"""
import sys
import itertools
import numpy as np

p, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
els = []
for a, b, c, d in itertools.product(range(p), repeat=4):
    if (a * d - b * c) % p == 1:
        els.append((a, b, c, d))
E = np.array(els, dtype=np.int64)


def canon(M):
    """normalize rows of M (k x 4) up to sign: first nonzero entry <= (p-1)/2."""
    M = M % p
    first = M[np.arange(len(M)), np.argmax(M != 0, axis=1)]
    flip = first > (p - 1) // 2
    M[flip] = (-M[flip]) % p
    return M


def code(M):
    return ((M[:, 0] * p + M[:, 1]) * p + M[:, 2]) * p + M[:, 3]


C = np.unique(code(canon(E)))
G = len(C)
assert G == p * (p * p - 1) // 2
EL = np.stack([C // p ** 3, (C // p ** 2) % p, (C // p) % p, C % p], axis=1)


def rmul(X, m):
    """rows of X times the matrix m (4-tuple), canonical indices."""
    a, b, c, d = m
    Y = np.stack([X[:, 0] * a + X[:, 1] * c, X[:, 0] * b + X[:, 1] * d, X[:, 2] * a + X[:, 3] * c,
                  X[:, 2] * b + X[:, 3] * d], axis=1)
    return np.searchsorted(C, code(canon(Y)))


def mat(i):
    return tuple(int(v) for v in EL[i])


def mulm(m, n):
    a, b, c, d = m; e, f, g, h = n
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


def invm(m):
    a, b, c, d = m
    return (d % p, (-b) % p, (-c) % p, a % p)


ident = int(np.searchsorted(C, code(canon(np.array([[1, 0, 0, 1]])))[0]))


def coverage(S):
    worst = G
    for side in (0, 1):
        D = {mulm(s, invm(t)) if side == 0 else mulm(invm(s), t) for s in S for t in S}
        perms = [rmul(EL, d) for d in D]
        reach = np.zeros(G, bool); reach[ident] = True
        for _ in range(3):
            idx = np.nonzero(reach)[0]
            new = reach.copy()
            for P in perms:
                new[P[idx]] = True
            reach = new
        worst = min(worst, int(reach.sum()))
    return worst


rng = np.random.default_rng(seed)
S = [mat(i) for i in rng.choice(G, size=8, replace=False)]
cov = coverage(S); it = 0
print(f'start coverage {cov} of {G}', flush=True)
while cov < G and it < 20000:
    it += 1
    T = list(S); T[rng.integers(8)] = mat(rng.integers(G))
    if len(set(T)) < 8:
        continue
    c = coverage(T)
    if c >= cov:
        if c > cov:
            print(f'  step {it}: coverage {c} of {G}', flush=True)
        S, cov = T, c
assert cov == G, f'coverage {cov} of {G}'
Sidx = [int(np.searchsorted(C, code(canon(np.array([s])))[0])) for s in S]
with open(out, 'w') as f:
    f.write(f'{G}\n')
    for s in S:
        img = rmul(EL, s)
        for x in range(G):
            f.write(f'{x} {int(img[x])}\n')
print(f'PSL(2,{p}): |G| = {G}; S = {S} after {it} steps; both sides reach all of G in 3 double steps; wrote {out}')
