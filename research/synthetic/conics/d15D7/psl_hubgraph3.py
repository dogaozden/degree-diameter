"""Hub graph for the (15,7) build: the Haar graph of PSL(2,p) on a set S of 8 elements (psl_hubgraph2.py with
targeted moves). Line-side hub x ~ point-side hub x s (x in G, s in S). Same-side hub distances <= 6 iff
(S S^-1)^3 = G (line side) and (S^-1 S)^3 = G (point side); S is improved by hill climbing until both hold.
Output: first line K = |G|, then "a b" per edge (a line-side, b point-side index).
When random replacement stalls, a missing element g of one side is written as a product of five factors from S and one
new generator x (g = s1 t1^-1 s2 t2^-1 s3 x^-1 on the line side, g = s1^-1 t1 s2^-1 t2 s3^-1 x on the point side), and x
replaces a generator not used in the product.
Usage: python psl_hubgraph3.py p SEED OUT [START_S_FILE]"""
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


def coverage(S, want_missing=False):
    worst = G; missing = []
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
        missing.append(np.nonzero(~reach)[0])
    return (worst, missing) if want_missing else worst


rng = np.random.default_rng(seed)
S = [mat(i) for i in rng.choice(G, size=8, replace=False)]
if len(sys.argv) > 4:                                      # start from a stored S (one "a b c d" per line)
    S = [tuple(int(v) % p for v in t.split()) for t in open(sys.argv[4]) if t.strip()]
cov = coverage(S); it = 0; last = 0
print(f'start coverage {cov} of {G}', flush=True)
while cov < G and it < 20000:
    it += 1
    T = list(S)
    if it - last < 100 or it % 2:                          # random replacement (always, until a stall)
        T[rng.integers(8)] = mat(rng.integers(G))
    else:                                                  # targeted move on a missing element
        _, miss = coverage(S, True)
        side = 0 if len(miss[0]) else 1
        g = mat(int(rng.choice(miss[side])))
        i1, i2, i3, j1, j2 = (int(v) for v in rng.integers(8, size=5))
        free = [k for k in range(8) if k not in (i1, i2, i3, j1, j2)]
        if not free:
            continue
        s1, s2, s3, t1, t2 = S[i1], S[i2], S[i3], S[j1], S[j2]
        if side == 0:                                      # g = s1 t1^-1 s2 t2^-1 s3 x^-1
            pre = mulm(mulm(mulm(mulm(s1, invm(t1)), s2), invm(t2)), s3)
            x = mulm(invm(g), pre)
        else:                                              # g = s1^-1 t1 s2^-1 t2 s3^-1 x
            pre = mulm(mulm(mulm(mulm(invm(s1), t1), invm(s2)), t2), invm(s3))
            x = mulm(invm(pre), g)
        T[free[rng.integers(len(free))]] = x
    if len({tuple(v) for v in canon(np.array(T))}) < 8:
        continue
    c = coverage(T)
    if c >= cov:
        if c > cov:
            print(f'  step {it}: coverage {c} of {G}', flush=True); last = it
        S, cov = T, c
print('S =', S, flush=True)
assert cov == G, f'coverage {cov} of {G}'
Sidx = [int(np.searchsorted(C, code(canon(np.array([s])))[0])) for s in S]
with open(out, 'w') as f:
    f.write(f'{G}\n')
    for s in S:
        img = rmul(EL, s)
        for x in range(G):
            f.write(f'{x} {int(img[x])}\n')
print(f'PSL(2,{p}): |G| = {G}; S = {S} after {it} steps; both sides reach all of G in 3 double steps; wrote {out}')
