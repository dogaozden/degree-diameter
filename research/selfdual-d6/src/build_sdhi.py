#!/usr/bin/env python3
"""Independent builder for the Haar graphs of sdhi.c, from the formula alone (no shared code with sdhi.c).

G = Q1 x Q2, each factor given as in sdhi: "sl q", "psl q", "pgl q" (2x2 matrices over GF(q), q = p^e), "meta m k r"
(C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r>, element (i,j) = x^i y^j, product (i,j)(a,b) = (i + r^j a, j + b)),
"cyc n" (Z_n).  Matrices [a b c d] have rows (a b), (c d); field elements of GF(p^e) are integers whose base-p digits
are the coefficients of 1, t, .., t^(e-1), with t^e reduced by the first monic irreducible polynomial
t^e + c_(e-1) t^(e-1) + .. + c_0 (c = sum c_i p^i in increasing order).  PSL: matrices modulo +-1, PGL: modulo
scalars.  H(G,S): (g,A) ~ (s g, B).

Vertex numbering (the same as sdhi's EDGES files): elements of a matrix factor are numbered with the identity first,
then the canonical representatives in lexicographic order of (a,b,c,d) (canonical: SL itself; PSL the
lexicographically smaller of M, -M; PGL scaled so that the first non-zero of (a, b) is 1); a meta element (i,j) is
i*k + j; g = (index in Q1) * |Q2| + (index in Q2); (g,A) is vertex g, (g,B) is vertex |G| + g.  Edges are written
for g = 0..|G|-1 and s in S in the given order: "g  |G| + index(s g)".

usage: build_sdhi.py D "FACTOR1" "FACTOR2" "S" OUT.edges [COMPARE.edges]
  S: elements separated by spaces, each "e1|e2" (e.g. "[1 0 0 1]|0 [1 2 3 2]|12" or "(3,8)|0").
Checks: S has distinct elements, the graph is simple and regular; BFS from (e,A) and from (e,B) (enough: right
multiplication by G is transitive on each side) gives the exact diameter; prints VALID iff it equals D.
"""
import sys
from collections import deque


class Field:
    def __init__(self, q):
        p = 2
        while q % p:
            p += 1
        e, t = 0, q
        while t % p == 0:
            t //= p
            e += 1
        assert t == 1, "q must be a prime power"
        self.q, self.p, self.e = q, p, e
        self.poly = None
        if e > 1:
            for c in range(q):
                if self._irreducible(c):
                    self.poly = [(c // p ** i) % p for i in range(e)]
                    break

    def digits(self, x):
        return [(x // self.p ** i) % self.p for i in range(self.e)]

    def undigits(self, d):
        return sum(v * self.p ** i for i, v in enumerate(d))

    def _irreducible(self, c):
        p, e = self.p, self.e
        f = [(c // p ** i) % p for i in range(e)] + [1]
        for dg in range(1, e // 2 + 1):
            for g0 in range(p ** dg):
                g = [(g0 // p ** i) % p for i in range(dg)] + [1]
                r = f[:]
                for i in range(e, dg - 1, -1):
                    t = r[i] % p
                    if t:
                        for j in range(dg + 1):
                            r[i - dg + j] = (r[i - dg + j] - t * g[j]) % p
                if all(r[i] % p == 0 for i in range(dg)):
                    return False
        return True

    def add(self, a, b):
        if self.e == 1:
            return (a + b) % self.p
        return self.undigits([(x + y) % self.p for x, y in zip(self.digits(a), self.digits(b))])

    def neg(self, a):
        if self.e == 1:
            return (-a) % self.p
        return self.undigits([(-x) % self.p for x in self.digits(a)])

    def mul(self, a, b):
        if self.e == 1:
            return a * b % self.p
        p, e = self.p, self.e
        da, db = self.digits(a), self.digits(b)
        pr = [0] * (2 * e - 1)
        for i in range(e):
            for j in range(e):
                pr[i + j] = (pr[i + j] + da[i] * db[j]) % p
        for i in range(2 * e - 2, e - 1, -1):
            c = pr[i]
            if c:
                pr[i] = 0
                for j in range(e):
                    pr[i - e + j] = (pr[i - e + j] - c * self.poly[j]) % p
        return self.undigits(pr[:e])

    def inv(self, a):
        for b in range(1, self.q):
            if self.mul(a, b) == 1:
                return b
        raise ZeroDivisionError


class MatrixGroup:
    def __init__(self, kind, q):
        self.F = F = Field(q)
        if F.p == 2:
            kind = 'sl'
        self.kind = kind
        self.mul_cache = {}
        elems = []
        I = (1, 0, 0, 1)
        for a in range(q):
            for b in range(q):
                for c in range(q):
                    for d in range(q):
                        A = (a, b, c, d)
                        dt = self.det(A)
                        if kind == 'pgl':
                            if dt == 0:
                                continue
                        elif dt != 1:
                            continue
                        if self.canon(A) != A or A == I:
                            continue
                        elems.append(A)
        self.elems = [I] + elems
        self.index = {A: i for i, A in enumerate(self.elems)}
        self.size = len(self.elems)

    def det(self, A):
        F = self.F
        return F.add(F.mul(A[0], A[3]), F.neg(F.mul(A[1], A[2])))

    def scale(self, l, A):
        return tuple(self.F.mul(l, x) for x in A)

    def canon(self, A):
        F = self.F
        if self.kind == 'psl':
            B = self.scale(F.neg(1), A)
            return min(A, B)
        if self.kind == 'pgl':
            s = A[0] if A[0] else A[1]
            return self.scale(F.inv(s), A)
        return A

    def mul(self, i, j):
        key = (i, j)
        r = self.mul_cache.get(key)
        if r is None:
            F = self.F
            A, B = self.elems[i], self.elems[j]
            C = (F.add(F.mul(A[0], B[0]), F.mul(A[1], B[2])), F.add(F.mul(A[0], B[1]), F.mul(A[1], B[3])),
                 F.add(F.mul(A[2], B[0]), F.mul(A[3], B[2])), F.add(F.mul(A[2], B[1]), F.mul(A[3], B[3])))
            r = self.index[self.canon(C)]
            self.mul_cache[key] = r
        return r

    def parse(self, s):
        A = tuple(int(t) for t in s.strip()[1:-1].split())
        return self.index[self.canon(A)]


class Meta:
    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, (r % m if k > 1 else 1 % m)
        assert m == 1 or pow(self.r, k, m) == 1
        self.rp = [pow(self.r, j, m) for j in range(k)]
        self.size = m * k

    def mul(self, g, h):
        i, j = divmod(g, self.k)
        a, b = divmod(h, self.k)
        return ((i + self.rp[j] * a) % self.m) * self.k + (j + b) % self.k

    def parse(self, s):
        s = s.strip()
        if self.k == 1:
            return int(s) % self.m
        i, j = (int(t) for t in s[1:-1].split(','))
        return (i % self.m) * self.k + j % self.k


def factor(spec):
    w = spec.split()
    if not w:
        return Meta(1, 1, 1)
    if w[0] in ('sl', 'psl', 'pgl'):
        return MatrixGroup(w[0], int(w[1]))
    if w[0] == 'meta':
        return Meta(int(w[1]), int(w[2]), int(w[3]))
    if w[0] == 'cyc':
        return Meta(int(w[1]), 1, 1)
    raise ValueError(spec)


def split_elems(s):
    out, cur, depth = [], '', 0
    for ch in s:
        if ch in '[(':
            depth += 1
        if ch in '])':
            depth -= 1
        if ch == ' ' and depth == 0:
            if cur:
                out.append(cur)
            cur = ''
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def main():
    D = int(sys.argv[1])
    Q1, Q2 = factor(sys.argv[2]), factor(sys.argv[3])
    n2 = Q2.size
    N = Q1.size * n2
    S = []
    for t in split_elems(sys.argv[4]):
        a, b = t.split('|')
        S.append(Q1.parse(a) * n2 + Q2.parse(b))
    assert len(set(S)) == len(S), "repeated element in S"
    K = len(S)

    def gmul(g, h):
        return Q1.mul(g // n2, h // n2) * n2 + Q2.mul(g % n2, h % n2)

    # left multiplication tables by the elements of S
    L = [[gmul(s, g) for g in range(N)] for s in S]
    edges = [(g, N + L[i][g]) for g in range(N) for i in range(K)]
    adj = [[] for _ in range(2 * N)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    with open(sys.argv[5], 'w') as f:
        f.write('%d\n' % (2 * N))
        for a, b in edges:
            f.write('%d %d\n' % (a, b))
    simple = all(len(set(x)) == len(x) for x in adj)
    regular = {len(x) for x in adj} == {K}
    diam = 0
    for src in (0, N):
        dist = [-1] * (2 * N)
        dist[src] = 0
        dq = deque([src])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = dist[u] + 1
                    dq.append(w)
        if min(dist) < 0:
            print('RESULT INVALID disconnected')
            return 1
        diam = max(diam, max(dist))
    same = ''
    if len(sys.argv) > 6:
        other = open(sys.argv[6]).read().split()
        mine = open(sys.argv[5]).read().split()
        same = ' edge list identical to %s: %s' % (sys.argv[6], 'yes' if other == mine else 'NO')
    ok = simple and regular and diam == D
    print('RESULT %s vertices %d degree %d simple %s diameter %d (BFS from (e,A) and (e,B))%s' %
          ('VALID' if ok else 'INVALID', 2 * N, K, simple, diam, same))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
