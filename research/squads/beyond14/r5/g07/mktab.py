#!/usr/bin/env python3
"""mktab.py OUT spec [spec ...]: write group multiplication tables in the own-small format ("G N id name", then N rows
of N indices; index 0 = identity) for groups built here from their definitions (no GAP):
  meta:m:k:r          Z_m x|_r Z_k, element (a,j) -> index a*k + j, (a,j)(b,l) = (a + r^j b mod m, j + l mod k)
  aff2:p:k            F_(p^2) x| Z_k (Frobenius, k | p^2-1): (v,j)(v',j') = (v + w^j v', j + j'), index (a p + b) k + j
  prod:SPEC1/SPEC2    direct product (meta factors only), index i1*N2 + i2
Each table is checked: identity row/column, every row and column a permutation, associativity on 20,000 random triples.
The id written is the running number of the spec on the command line (1, 2, ...)."""
import sys, random
def meta(m, k, r):
    assert pow(r, k, m) == 1 % m and r % m != 0, "need r^k = 1 mod m"
    R = [pow(r, j, m) for j in range(k)]
    N = m * k
    def mul(x, y):
        a, j = divmod(x, k); b, l = divmod(y, k)
        return ((a + R[j] * b) % m) * k + (j + l) % k
    return N, mul, f"Z{m}x|{r}Z{k}"
def aff2(p, k):
    """F_(p^2) x| Z_k: (v,j)(v',j') = (v + w^j v', j + j'), v in GF(p^2) = F_p[t]/(t^2 - c) (c a non-square),
    w of multiplicative order k (k | p^2 - 1). Element index (a p + b) k + j for v = a + b t. Frobenius when k > 1."""
    assert (p * p - 1) % k == 0 and p % 2 == 1
    c = next(x for x in range(2, p) if pow(x, (p - 1) // 2, p) == p - 1)
    def fm(x, y): return ((x[0] * y[0] + c * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)
    def fpow(x, e):
        r_ = (1, 0)
        while e:
            if e & 1: r_ = fm(r_, x)
            x = fm(x, x); e >>= 1
        return r_
    q1 = p * p - 1
    fac = [f for f in range(2, q1 + 1) if q1 % f == 0 and all(f % g for g in range(2, int(f ** .5) + 1))]
    gen = next(x for x in ((a, b) for a in range(p) for b in range(p) if (a, b) != (0, 0))
               if all(fpow(x, q1 // f) != (1, 0) for f in fac))
    w = fpow(gen, q1 // k); W = [fpow(w, j) for j in range(k)]
    N = p * p * k
    def mul(x, y):
        v, j = divmod(x, k); u, l = divmod(y, k)
        a, b = divmod(v, p); c2, d = divmod(u, p)
        wu = fm(W[j], (c2, d))
        return (((a + wu[0]) % p) * p + (b + wu[1]) % p) * k + (j + l) % k
    return N, mul, f"F{p}^2x|Z{k}"
def parse(s):
    if s.startswith('aff2:'):
        _, p, k = s.split(':'); return aff2(int(p), int(k))
    if s.startswith('prod:'):
        A, B = s[5:].split('/')
        N1, m1, n1 = parse(A); N2, m2, n2 = parse(B)
        return N1 * N2, (lambda x, y: m1(x // N2, y // N2) * N2 + m2(x % N2, y % N2)), f"({n1})x({n2})"
    t, m, k, r = s.split(':'); assert t == 'meta'
    return meta(int(m), int(k), int(r))
out = open(sys.argv[1], 'w')
for gid, spec in enumerate(sys.argv[2:], 1):
    N, mul, name = parse(spec)
    T = [[mul(x, y) for y in range(N)] for x in range(N)]
    assert all(T[0][x] == x and T[x][0] == x for x in range(N))
    for x in range(N): assert len(set(T[x])) == N and len(set(T[y][x] for y in range(N))) == N
    rnd = random.Random(1)
    for _ in range(20000):
        a, b, c = rnd.randrange(N), rnd.randrange(N), rnd.randrange(N)
        assert T[T[a][b]][c] == T[a][T[b][c]]
    out.write(f"G {N} {gid} {name}\n")
    for x in range(N): out.write(" ".join(map(str, T[x])) + "\n")
    print(f"G {N} {gid} {name}")
