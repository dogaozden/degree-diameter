# The 3-spaces of Lemma 6.2(a) as written in joint.tex: odd q: X1 = X5 = 0, X6 = -c X2 (-c a non-square);
# even q: X1 = X5 = 0, X6 = delta X2 + X3 (Tr(delta) = 1). Check: q^2+1 points of Q(6,q), pairwise non-perpendicular.
import itertools
def gf2k(k, poly):  # GF(2^k) multiplication table, poly given as int including x^k
    q = 1 << k; M = [[0]*q for _ in range(q)]
    for a in range(q):
        for b in range(q):
            r = 0; x = a; y = b
            while y:
                if y & 1: r ^= x
                y >>= 1; x <<= 1
                if x & q: x ^= poly
            M[a][b] = r
    return M
def check_odd(q):
    sq = {x*x % q for x in range(1, q)}
    c = next(c for c in range(1, q) if (-c) % q not in sq)
    Q = lambda X: (X[0]*X[4] + X[1]*X[5] + X[2]*X[6] - X[3]*X[3]) % q
    b = lambda X, Y: (Q([x+y for x, y in zip(X, Y)]) - Q(X) - Q(Y)) % q
    pts = set()
    for x0, x2, x3, x4 in itertools.product(range(q), repeat=4):
        X = (x0, 0, x2, x3, x4, 0, (-c*x2) % q)
        if any(X) and Q(X) == 0:
            i = next(t for t in X if t); inv = pow(i, q-2, q); pts.add(tuple(t*inv % q for t in X))
    pts = list(pts); assert len(pts) == q*q + 1, len(pts)
    assert all(b(x, y) for x, y in itertools.combinations(pts, 2))
    print("odd q =", q, "ok:", len(pts), "points, pairwise non-perpendicular")
def check_even(k, poly):
    q = 1 << k; M = gf2k(k, poly)
    tr = lambda x: (lambda t: t)(sum(0 for _ in [0]))  # placeholder
    def trace(x):
        t, y = 0, x
        for _ in range(k): t ^= y; y = M[y][y]
        return t
    delta = next(d for d in range(q) if trace(d) == 1)
    Q = lambda X: M[X[0]][X[4]] ^ M[X[1]][X[5]] ^ M[X[2]][X[6]] ^ M[X[3]][X[3]]
    b = lambda X, Y: M[X[0]][Y[4]] ^ M[X[4]][Y[0]] ^ M[X[1]][Y[5]] ^ M[X[5]][Y[1]] ^ M[X[2]][Y[6]] ^ M[X[6]][Y[2]]
    inv = {a: next(y for y in range(1, q) if M[a][y] == 1) for a in range(1, q)}
    pts = set()
    for x0, x2, x3, x4 in itertools.product(range(q), repeat=4):
        X = (x0, 0, x2, x3, x4, 0, M[delta][x2] ^ x3)
        if any(X) and Q(X) == 0:
            i = inv[next(t for t in X if t)]; pts.add(tuple(M[t][i] for t in X))
    pts = list(pts); assert len(pts) == q*q + 1, len(pts)
    assert all(b(x, y) for x, y in itertools.combinations(pts, 2))
    print("even q =", q, "ok:", len(pts), "points, pairwise non-perpendicular")
for q in (3, 5, 7, 11): check_odd(q)
check_even(2, 0b111); check_even(3, 0b1011)
