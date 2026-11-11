#!/usr/bin/env python3
"""mkg.py OUT spec [spec ...]: own-small table format ("G N id name", N rows of N indices, index 0 = identity).
Specs (e04 extension of ownsmall/mktab.py):
  meta:m:k:r        Z_m x|_r Z_k
  aff2:p:k          F_(p^2) x| Z_k (Frobenius, p odd, k | p^2-1)
  psl2:q / sl2:q    PSL(2,q) / SL(2,q), q prime
  a5 / s5           alternating / symmetric group on 5 points
  A*B               direct product of any two specs (A, B may themselves be products; use parentheses-free nesting only
                    as A*B with A, B atomic names)
Every table is checked (identity, permutation rows/cols, associativity on 20000 random triples)."""
import sys, random, itertools
from math import gcd

def meta(m, k, r):
    assert pow(r, k, m) == 1 % m and r % m != 0
    R = [pow(r, j, m) for j in range(k)]
    N = m * k
    def mul(x, y):
        a, j = divmod(x, k); b, l = divmod(y, k)
        return ((a + R[j] * b) % m) * k + (j + l) % k
    return N, mul

def aff2(p, k):
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
    return N, mul

def matgroup(q, normalize):
    """SL(2,q) elements as tuples (a,b,c,d) mod q; if normalize, PSL(2,q): identify M with -M (canonical = min)."""
    def canon(M):
        if not normalize: return M
        Nm = tuple((-x) % q for x in M)
        return min(M, Nm)
    els = sorted({canon(M) for M in itertools.product(range(q), repeat=4) if (M[0]*M[3]-M[1]*M[2]) % q == 1})
    idx = {M: i for i, M in enumerate(els)}
    I = canon((1, 0, 0, 1)); i0 = idx[I]
    order = [I] + [M for M in els if M != I]          # identity at index 0
    idx = {M: i for i, M in enumerate(order)}
    def mul(x, y):
        a, b, c, d = order[x]; e, f, g, h = order[y]
        M = ((a*e + b*g) % q, (a*f + b*h) % q, (c*e + d*g) % q, (c*f + d*h) % q)
        return idx[canon(M)]
    return len(order), mul

def perm_group(n, even_only):
    P = [p for p in itertools.permutations(range(n))
         if (not even_only) or sum(1 for i in range(n) for j in range(i+1, n) if p[i] > p[j]) % 2 == 0]
    ident = tuple(range(n)); P.remove(ident); P = [ident] + P
    idx = {p: i for i, p in enumerate(P)}
    def mul(x, y):
        a, b = P[x], P[y]
        return idx[tuple(a[b[i]] for i in range(n))]
    return len(P), mul

def atom(s):
    t = s.split(':')
    if t[0] == 'meta': return meta(int(t[1]), int(t[2]), int(t[3]))
    if t[0] == 'aff2': return aff2(int(t[1]), int(t[2]))
    if t[0] == 'psl2': return matgroup(int(t[1]), True)
    if t[0] == 'sl2': return matgroup(int(t[1]), False)
    if t[0] == 'a5': return perm_group(5, True)
    if t[0] == 's5': return perm_group(5, False)
    raise ValueError(s)

def parse(s):
    if '*' in s:
        A, B = s.split('*', 1)
        N1, m1 = parse(A); N2, m2 = parse(B)
        return N1 * N2, (lambda x, y: m1(x // N2, y // N2) * N2 + m2(x % N2, y % N2))
    return atom(s)

if __name__ == '__main__':
    out = open(sys.argv[1], 'w')
    for gid, spec in enumerate(sys.argv[2:], 1):
        N, mul = parse(spec)
        T = [[mul(x, y) for y in range(N)] for x in range(N)]
        assert all(T[0][x] == x and T[x][0] == x for x in range(N))
        for x in range(N): assert len(set(T[x])) == N and len(set(T[y][x] for y in range(N))) == N
        rnd = random.Random(1)
        for _ in range(20000):
            a, b, c = rnd.randrange(N), rnd.randrange(N), rnd.randrange(N)
            assert T[T[a][b]][c] == T[a][T[b][c]], spec
        out.write(f"G {N} {gid} {spec}\n")
        for x in range(N): out.write(" ".join(map(str, T[x])) + "\n")
        print(f"G {N} {gid} {spec}", flush=True)
