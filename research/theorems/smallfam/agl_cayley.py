"""Cubic Cayley graphs Cay(AGL(1,p), {t, t^-1, u}) with t: x -> g x (g a primitive root) and u: x -> -x + 1.
Up to conjugation in AGL(1,p) every element of order p-1 is x -> g x + b ~ x -> g x, and every involution
x -> -x + c with c != 0 can then be scaled... (we simply try every primitive root g and every c).  Prints the
diameter and girth.  Usage: python3 agl_cayley.py p1 p2 ..."""
import sys
import igraph as ig
for p in map(int, sys.argv[1:]):
    els = [(a, b) for a in range(1, p) for b in range(p)]
    idx = {e: i for i, e in enumerate(els)}
    def mul(x, y):   # (x y)(z) = x(y(z)): x=(a,b): z -> a z + b
        return ((x[0] * y[0]) % p, (x[0] * y[1] + x[1]) % p)
    prim = [g for g in range(2, p) if all(pow(g, (p - 1) // q, p) != 1 for q in range(2, p) if (p - 1) % q == 0 and all(q % s for s in range(2, q)))]
    best = None
    res = {}
    for g in prim:
        for c in range(1, p):
            t, ti, u = (g, 0), (pow(g, p - 2, p), 0), (p - 1, c)
            E = set()
            for x in els:
                for s in (t, ti, u):
                    y = mul(s, x)
                    E.add(tuple(sorted((idx[x], idx[y]))))
            G = ig.Graph(n=len(els), edges=list(E))
            d, gi, bip = G.diameter(), G.girth(), G.is_bipartite()
            res[(d, gi, bip)] = res.get((d, gi, bip), 0) + 1
    print(f'p={p} n={p*(p-1)}: (diameter, girth, bipartite) -> count over (g, c): {res}', flush=True)
