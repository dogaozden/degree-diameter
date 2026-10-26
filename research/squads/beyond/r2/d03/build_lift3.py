#!/usr/bin/env python3
"""Route-chart lift over F_3 of a controller edge list 'a b colour' (a: A-side id 0..m-1, b: B-side id 0..m-1).
usage: build_lift3.py CTRL CHART OUT.edges
Fibre F_3^4 (81 points), vertices: A (a,x) -> a*81+vid(x); B (b,y) -> m*81 + b*81 + vid(y).
Edge (a,x) ~ (b, A_c x + lam b_c), lam in F_3. Degree 18 (controller 6-regular)."""
import sys, itertools
P = 3
def load(path):
    v = [int(x) for x in open(path).read().split()]
    A = [[v[t*20 + 4*r: t*20 + 4*r + 4] for r in range(4)] for t in range(6)]
    b = [tuple(v[t*20 + 16: t*20 + 20]) for t in range(6)]
    return A, b
def mv(M, x):
    return tuple(sum(M[r][c]*x[c] for c in range(4)) % P for r in range(4))
def vid(x):
    return x[0] + 3*x[1] + 9*x[2] + 27*x[3]
def main():
    ctrl, chart, out = sys.argv[1:4]
    A, b = load(chart)
    rows = [tuple(map(int, l.split())) for l in open(ctrl) if l.strip()]
    hdr = rows[0]; rows = rows[1:]
    m = hdr[0]
    assert len(rows) == 6*m, 'controller must be 6-regular on m+m vertices'
    assert len(set((a, c) for a, b_, c in rows)) == len(rows)
    assert len(set((b_, c) for a, b_, c in rows)) == len(rows)
    fib = list(itertools.product(range(P), repeat=4))
    E = []
    for a, bb, c in rows:
        for x in fib:
            y0 = mv(A[c], x)
            for lam in range(P):
                y = tuple((p + lam*q) % P for p, q in zip(y0, b[c]))
                E.append((a*81 + vid(x), m*81 + bb*81 + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    with open(out, 'w') as f:
        f.write(f"{2*m*81}\n"); f.writelines(f"{u} {v}\n" for u, v in E)
    print('m', m, 'vertices', 2*m*81, 'edges', len(E))
main()
