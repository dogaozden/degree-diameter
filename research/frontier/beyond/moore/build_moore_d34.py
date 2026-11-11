#!/usr/bin/env python3
"""Self-contained builders for the Moore graphs of the cells (17|18|20, 3) and (17|18|20, 4) (job beyond-small, 2026-11-01).

  pg  q : incidence graph of PG(2,q): points and lines = 1-spaces of F_q^3, p ~ l iff p.l = 0.
          (q+1)-regular, 2(q^2+q+1) vertices, diameter 3 (projective plane).
  w   q : incidence graph of the symplectic quadrangle W(q): points = 1-spaces of F_q^4, lines = totally isotropic
          2-spaces for B(x,y) = x0y1 - x1y0 + x2y3 - x3y2. (q+1)-regular, 2(q+1)(q^2+1) vertices, diameter 4.

q must be a prime or 16 (F_16 = F_2[x]/(x^4+x+1)). No imports from the repo.
usage: python3 build_moore_d34.py pg|w q OUT.edges     (apsp.c format: first line n, then "u v"; points 0..P-1, lines P..)
"""
import sys, itertools

def field(q):
    if q == 16:
        exp = [0] * 30; log = [0] * 16; x = 1
        for i in range(15):
            exp[i] = x; log[x] = i; x <<= 1
            if x & 16: x ^= 0b10011
        for i in range(15, 30): exp[i] = exp[i - 15]
        add = lambda a, b: a ^ b
        mul = lambda a, b: 0 if a == 0 or b == 0 else exp[log[a] + log[b]]
        inv = lambda a: exp[(15 - log[a]) % 15]
        neg = lambda a: a
        return add, mul, inv, neg
    assert all(q % d for d in range(2, int(q ** 0.5) + 1)), "q must be prime or 16"
    return (lambda a, b: (a + b) % q, lambda a, b: a * b % q, lambda a: pow(a, q - 2, q), lambda a: (-a) % q)

def points(q, dim, mul, inv):
    """normalised representatives (first nonzero coordinate 1) of the 1-spaces of F_q^dim"""
    out = []
    for v in itertools.product(range(q), repeat=dim):
        nz = [c for c in v if c]
        if nz and nz[0] == 1: out.append(v)
    return out

def build_pg(q):
    add, mul, inv, neg = field(q)
    P = points(q, 3, mul, inv); n = len(P); E = []
    for i, p in enumerate(P):
        for j, l in enumerate(P):
            s = 0
            for a, b in zip(p, l): s = add(s, mul(a, b))
            if s == 0: E.append((i, n + j))
    return 2 * n, E

def build_w(q):
    add, mul, inv, neg = field(q)
    P = points(q, 4, mul, inv); idx = {p: i for i, p in enumerate(P)}
    def B(x, y):
        s = 0
        for a, b, sg in ((0, 1, 1), (1, 0, -1), (2, 3, 1), (3, 2, -1)):
            t = mul(x[a], y[b]); s = add(s, t if sg == 1 else neg(t))
        return s
    def norm(v):
        f = next(c for c in v if c); fi = inv(f); return tuple(mul(fi, c) for c in v)
    n = len(P); lines = set()
    for i, p in enumerate(P):
        done = set([i])
        for r in P:
            if B(p, r) != 0: continue
            j = idx[r]
            if j in done: continue
            pts = set([i])
            for t in range(q): pts.add(idx[norm(tuple(add(mul(t, a), b) for a, b in zip(p, r)))])
            done |= pts; lines.add(frozenset(pts))
    L = sorted(sorted(s) for s in lines)
    n = len(P); E = [(pt, n + j) for j, l in enumerate(L) for pt in l]
    assert len(L) == n, (len(L), n)
    return 2 * n, E

if __name__ == '__main__':
    kind, q, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    n, E = build_pg(q) if kind == 'pg' else build_w(q)
    with open(out, 'w') as f:
        f.write(f"{n}\n"); f.writelines(f"{u} {v}\n" for u, v in E)
    print(kind, q, 'vertices', n, 'edges', len(E))
