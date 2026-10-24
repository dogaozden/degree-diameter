"""Incidence structure of the symplectic generalized quadrangle W(q) (points of PG(3,q), totally isotropic lines of
x0y1 - x1y0 + x2y3 - x3y2), q = p^e <= 32. Output in the gh_build format: "P q" then P lines with their q+1 point
indices. Self-checks: P = (q+1)(q^2+1) points and lines, q+1 lines per point.
Usage: python3 gq_build.py q > gq_q.txt"""
import sys, itertools
def factor(q):
    for p in range(2, q + 1):
        if q % p == 0:
            e = 0; r = q
            while r % p == 0: r //= p; e += 1
            if r != 1: raise SystemExit('q must be a prime power')
            return p, e
def field(q):
    p, e = factor(q)
    if e == 1:
        add = [[(a + b) % p for b in range(q)] for a in range(q)]
        mul = [[(a * b) % p for b in range(q)] for a in range(q)]
        return add, mul
    # elements: integers with base-p digits = coefficients (low degree first); find a monic irreducible of degree e
    def digits(a): return [(a // p ** i) % p for i in range(e)]
    def num(d): return sum(c * p ** i for i, c in enumerate(d))
    def polymulmod(a, b, f):
        prod = [0] * (2 * e - 1)
        for i in range(e):
            for j in range(e): prod[i + j] = (prod[i + j] + a[i] * b[j]) % p
        for k in range(2 * e - 2, e - 1, -1):       # reduce by monic f (f[e] = 1)
            c = prod[k]
            if c:
                for i in range(e + 1): prod[k - e + i] = (prod[k - e + i] - c * f[i]) % p
        return prod[:e]
    for tail in itertools.product(range(p), repeat=e):
        f = list(tail) + [1]
        # irreducible iff no element of the extension... brute force: f has no factor of degree <= e/2 (check roots of
        # small-degree polys by trying the multiplicative order condition): simple test: x^(p^e) = x and x^(p^k) != x for k<e
        def powx(n):
            r = [1] + [0] * (e - 1); base = [0, 1] + [0] * (e - 2) if e > 1 else [0]
            while n:
                if n & 1: r = polymulmod(r, base, f)
                base = polymulmod(base, base, f); n >>= 1
            return r
        x = [0, 1] + [0] * (e - 2)
        if powx(p ** e) == x and all(powx(p ** k) != x for k in range(1, e)) and f[0] != 0:
            break
    add = [[num([(x + y) % p for x, y in zip(digits(a), digits(b))]) for b in range(q)] for a in range(q)]
    mul = [[num(polymulmod(digits(a), digits(b), f)) for b in range(q)] for a in range(q)]
    return add, mul
def main():
    q = int(sys.argv[1]); add, mul = field(q)
    p, e = factor(q)
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [None] + [next(b for b in range(q) if mul[a][b] == 1) for a in range(1, q)]
    def norm(v):
        for c in v:
            if c:
                s = inv[c]; return tuple(mul[s][x] for x in v)
    pts = [v for v in itertools.product(range(q), repeat=4) if any(v) and norm(v) == v]
    idx = {v: i for i, v in enumerate(pts)}
    def form(x, y):
        t1 = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        t2 = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t1][t2]
    lines = {}; out = []
    for i, x in enumerate(pts):
        perp = [y for y in pts if form(x, y) == 0 and y != x]
        seen = set()
        for y in perp:
            if y in seen: continue
            mem = {x}
            for a in range(q):
                z = norm(tuple(add[y[k]][mul[a][x[k]]] for k in range(4))); mem.add(z)
            seen |= mem
            key = frozenset(idx[z] for z in mem)
            assert len(key) == q + 1
            if key not in lines: lines[key] = len(out); out.append(sorted(key))
    P = len(pts)
    assert P == (q + 1) * (q * q + 1) and len(out) == P, (P, len(out))
    deg = [0] * P
    for L in out:
        for z in L: deg[z] += 1
    assert all(d == q + 1 for d in deg)
    print(P, q)
    for L in out: print(' '.join(map(str, L)))
    print('W(%d): %d points, %d lines, checks passed' % (q, P, len(out)), file=sys.stderr)
main()
