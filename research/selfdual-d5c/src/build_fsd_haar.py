#!/usr/bin/env python3
"""Build the Haar graph H(G, S) of G = H x C_n3 from the formula alone (independent of fsd.c) and write its edge list.

H is  meta m k r : C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r>, x^i y^j = (i, j), (i,j)(a,b) = (i + r^j a, j + b)
      psl p      : PSL(2, p), a matrix [[a, b], [c, d]] up to sign, written a.b.c.d with the first nonzero of (a, b)
                   in 1..(p-1)/2
      sl p       : SL(2, p), [[a, b], [c, d]] written a.b.c.d
An element of G is (h, l), l in Z_n3, written "i,j,l" / "i,j" (meta) or "a.b.c.d,l" / "a.b.c.d" (psl, sl).
Vertex numbers: H-index h (meta: i*k + j; psl/sl: 0 = identity, then the other matrices in lexicographic order of
(a, b, c, d), for psl only the representatives above), element index e = h*n3 + l; vertex (g, A) = e(g),
(g, B) = |G| + e(g).  Edges (g, A) ~ (s g, B) for s in S.

usage: build_fsd_haar.py meta m k r n3 "S" OUT.edges     or     build_fsd_haar.py psl|sl p n3 "S" OUT.edges
Prints the vertex count, the degrees, and the eccentricities of (e, A) and (e, B) (BFS; G acts transitively on each
side, so these are the eccentricities of every vertex).  The all-pairs check is apsp_mt.c.
"""
import sys
from collections import deque


def main():
    kind = sys.argv[1]
    if kind == "meta":
        m, k, r, n3 = (int(t) for t in sys.argv[2:6])
        Sstr, out = sys.argv[6], sys.argv[7]
        assert pow(r, k, m) == 1 % m
        nh = m * k

        def hmul(g, h):
            return ((g[0] + pow(r, g[1], m) * h[0]) % m, (g[1] + h[1]) % k)

        hel = [(i, j) for i in range(m) for j in range(k)]          # index i*k + j

        def parse_h(t):
            v = [int(u) for u in t.split(",")]
            return (v[0] % m, v[1] % k), (v[2] if len(v) > 2 else 0)
    else:
        p, n3 = int(sys.argv[2]), int(sys.argv[3])
        Sstr, out = sys.argv[4], sys.argv[5]
        proj = kind == "psl"

        def canon(M):
            if not proj:
                return M
            a, b = M[0], M[1]
            first = a if a else b
            if first > (p - 1) // 2:
                return tuple((-v) % p for v in M)
            return M

        ident = (1, 0, 0, 1)
        mats = [ident]
        for a in range(p):
            for b in range(p):
                for c in range(p):
                    for d in range(p):
                        if (a * d - b * c) % p != 1 or (a, b, c, d) == ident:
                            continue
                        if canon((a, b, c, d)) != (a, b, c, d):
                            continue
                        mats.append((a, b, c, d))
        hel = mats
        nh = len(mats)

        def hmul(g, h):
            a, b, c, d = g
            e, f, gg, hh = h
            return canon(((a * e + b * gg) % p, (a * f + b * hh) % p, (c * e + d * gg) % p, (c * f + d * hh) % p))

        def parse_h(t):
            parts = t.split(",")
            M = tuple(int(u) % p for u in parts[0].split("."))
            assert (M[0] * M[3] - M[1] * M[2]) % p == 1, f"det != 1: {t}"
            return canon(M), (int(parts[1]) if len(parts) > 1 else 0)
    hidx = {h: i for i, h in enumerate(hel)}
    n = nh * n3
    S = [parse_h(t) for t in Sstr.split()]
    assert len(set(S)) == len(S), "repeated element in S"
    elems = [(h, l) for h in hel for l in range(n3)]                # index hidx[h]*n3 + l

    def idx(g):
        return hidx[g[0]] * n3 + g[1]

    def mul(g, h):
        return (hmul(g[0], h[0]), (g[1] + h[1]) % n3)

    adj = [[] for _ in range(2 * n)]
    edges = []
    for g in elems:
        a = idx(g)
        for s in S:
            b = n + idx(mul(s, g))
            edges.append((a, b))
            adj[a].append(b)
            adj[b].append(a)
    with open(out, "w") as f:
        f.write(f"{2 * n}\n")
        for a, b in edges:
            f.write(f"{a} {b}\n")
    for v in range(2 * n):
        assert len(set(adj[v])) == len(adj[v]), f"repeated edge at {v}"
    degs = sorted({len(a) for a in adj})
    ecc = []
    for s0 in (0, n):
        dist = [-1] * (2 * n)
        dist[s0] = 0
        q = deque([s0])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = dist[u] + 1
                    q.append(w)
        ecc.append(max(dist) if min(dist) >= 0 else -1)
    print(f"vertices {2 * n} edges {len(edges)} degrees {degs} ecc(e,A) {ecc[0]} ecc(e,B) {ecc[1]}")


if __name__ == "__main__":
    main()
