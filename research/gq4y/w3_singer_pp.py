"""Check the Singer-orbit 2-ovoids of W(3,q) for prime powers q = p^e (w3_singer.py only handles primes).

PG(3,q) = GF(q^4)*/GF(q)*, point g^i, i mod N = (q^4-1)/(q-1). B(x,y) = Tr_{q^4/q}(d x y^(q^2)), d = g^((q^2+1)/2).
Claim: classes a and q-a mod q+1 together meet every totally isotropic line in exactly 2 points.
Since x -> g^(q+1) x preserves W(3,q) and every class, it is enough to test the lines through g^0, ..., g^q.
Also prints, for every pair of classes {a,b}, whether it is a 2-ovoid (expect exactly the pairs a+b = q mod q+1).
Usage: python3 w3_singer_pp.py p e   (q = p^e). Passed 2026-10-18 for q = 3, 5, 7, 9, 25 (42 s), 27 (143 s).
Proof for all odd q: research/NOTE.md, Proposition C.
"""
import itertools
import sys

import numpy as np


def _mulmod(a, b, c, p):
    """a*b mod (x^n + c[n-1] x^(n-1) + ... + c[0]) over GF(p); polys as coefficient lists of length n."""
    n = len(c)
    r = [0] * (2 * n - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    for k in range(2 * n - 2, n - 1, -1):
        t = r[k]
        if t:
            for i in range(n):
                r[k - n + i] = (r[k - n + i] - t * c[i]) % p
    return r[:n]


def _powx(e, c, p):
    n = len(c)
    res, base = [1] + [0] * (n - 1), [0, 1] + [0] * (n - 2)
    while e:
        if e & 1:
            res = _mulmod(res, base, c, p)
        base = _mulmod(base, base, c, p)
        e >>= 1
    return res


def _primes(m):
    out, d = [], 2
    while d * d <= m:
        if m % d == 0:
            out.append(d)
            while m % d == 0:
                m //= d
        d += 1
    return out + ([m] if m > 1 else [])


def field(p, n):
    """exp table (order x n digits) of GF(p^n) for a primitive polynomial, and log table indexed by base-p code."""
    order = p ** n - 1
    one = [1] + [0] * (n - 1)
    for c in itertools.product(range(p), repeat=n):
        c = list(c)
        if c[0] == 0 or _powx(order, c, p) != one or any(_powx(order // r, c, p) == one for r in _primes(order)):
            continue
        v = one[:]
        exp = []
        for i in range(order):
            exp.append(v)
            top = v[-1]
            v = [(-top * c[0]) % p] + [(v[k - 1] - top * c[k]) % p for k in range(1, n)]
        assert v == one
        E = np.array(exp, dtype=np.int64)
        pw = p ** np.arange(n)
        log = np.full(p ** n, -1, dtype=np.int64)
        log[E @ pw] = np.arange(order)
        assert (log >= 0).sum() == order
        return E, log, pw
    raise RuntimeError


def main(p, e):
    q, n = p ** e, 4 * e
    E, log, pw = field(p, n)
    order = p ** n - 1
    N = order // (q - 1)
    dl = (q * q + 1) // 2
    sub = [N * k for k in range(q - 1)]          # logs of GF(q)*

    def is_zero_trace(m):
        s = sum(E[(m * q ** k) % order] for k in range(4)) % p
        return ~s.any(axis=-1)

    def point(v):
        return log[(v % p) @ pw] % N

    lines = set()
    js = np.arange(N)
    for c in range(q + 1):
        perp = js[is_zero_trace(dl + c + js * q * q)]
        perp = set(perp.tolist()) - {c}
        assert len(perp) == q * q + q
        while perp:
            j = perp.pop()
            L = {c, j} | {int(point(E[(c + s) % order] + E[j])) for s in sub}
            assert len(L) == q + 1
            perp -= L
            lines.add(frozenset(L))
    assert len(lines) <= (q + 1) ** 2
    good = []
    for a, b in itertools.combinations(range(q + 1), 2):
        if all(sum(1 for x in L if x % (q + 1) in (a, b)) == 2 for L in lines):
            good.append((a, b))
    expect = [(a, q - a) for a in range((q + 1) // 2)]
    print(f'q={q}: {len(lines)} line reps; 2-ovoid pairs {good}; matches a+b=q: {good == expect}')


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]))
