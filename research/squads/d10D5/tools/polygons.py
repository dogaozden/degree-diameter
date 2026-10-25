"""Generalized polygon incidence graphs + j extra perfect matchings, written as lift.c base / solution files.

Usage:
  python3 polygons.py gq|gh|pg q j m MODE [--seed s] [--D D] > FILE
    pg q : PG(2,q), q prime: incidence graph (q+1)-regular, diameter 3, girth 6, 2(q^2+q+1) vertices.
    gq q : W(q), q prime: points of PG(3,q), lines = totally isotropic lines of x0y1 - x1y0 + x2y3 - x3y2.
           Incidence graph: (q+1)-regular, diameter 4, girth 8, 2(q+1)(q^2+1) vertices.
    gh q : split Cayley hexagon H(q), q prime (construction copied from research/gh6/gh_build.py: points of the
           quadric X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q), lines from Tits' equations). Diameter 6, girth 12.
    j    : number of extra perfect matchings point -> line (random, seeded; independent of the geometry)
    m    : order of the cyclic voltage group Z_m
    MODE : sol   all voltages fixed: polygon edges 0, matching t gets voltage t  (a lift.c solution file)
           free  polygon edges fixed 0, matching edges free  (a lift.c base file)
           allfree  every edge free (lift.c gauge-fixes a spanning tree)
Vertices: points 0..P-1, lines P..2P-1.
"""
import itertools
import random
import sys

import numpy as np


def normalize(v, q):
    for x in v:
        if x % q:
            s = pow(x, q - 2, q)
            return tuple((s * c) % q for c in v)
    raise ValueError("zero vector")


def wq(q):
    pts = [v for v in itertools.product(range(q), repeat=4) if next((c for c in v if c), 0) == 1]
    index = {v: i for i, v in enumerate(pts)}

    def form(x, y):
        return (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % q

    lines = {}
    for i, x in enumerate(pts):
        for j in range(i + 1, len(pts)):
            y = pts[j]
            if form(x, y):
                continue
            mem = {i, j}
            for a in range(q):
                mem.add(index[normalize(tuple((x[k] + a * y[k]) % q for k in range(4)), q)])
            lines.setdefault(frozenset(mem), None)
    L = [sorted(s) for s in lines]
    assert len(pts) == len(L) == (q + 1) * (q * q + 1)
    return len(pts), L


def pg(q):
    """PG(2,q), q prime: points = lines = normalized vectors of GF(q)^3, incidence x.y = 0"""
    pts = [v for v in itertools.product(range(q), repeat=3) if next((c for c in v if c), 0) == 1]
    lines = [[i for i, x in enumerate(pts) if (x[0] * l[0] + x[1] * l[1] + x[2] * l[2]) % q == 0] for l in pts]
    assert all(len(L) == q + 1 for L in lines)
    return len(pts), lines


def gh(q):
    P = [v for v in itertools.product(range(q), repeat=7)
         if next((c for c in v if c), 0) == 1 and (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0]
    N = len(P)
    assert N == (q ** 6 - 1) // (q - 1)
    index = {v: i for i, v in enumerate(P)}
    Pa = np.array(P, dtype=np.int64)
    lines = {}
    out = []
    for i in range(N):
        x = P[i]
        xa = Pa[i]

        def pl(a, b):
            return (xa[a] * Pa[:, b] - xa[b] * Pa[:, a]) % q

        polar = (xa[0] * Pa[:, 4] + xa[4] * Pa[:, 0] + xa[1] * Pa[:, 5] + xa[5] * Pa[:, 1]
                 + xa[2] * Pa[:, 6] + xa[6] * Pa[:, 2] - 2 * xa[3] * Pa[:, 3]) % q
        ok = polar == 0
        ok &= pl(1, 2) == pl(3, 4)
        ok &= pl(5, 4) == pl(3, 2)
        ok &= pl(2, 0) == pl(3, 5)
        ok &= pl(6, 5) == pl(3, 0)
        ok &= pl(0, 1) == pl(3, 6)
        ok &= pl(4, 6) == pl(3, 1)
        ok[i] = False
        for j in np.nonzero(ok)[0]:
            if j < i:
                continue
            y = P[j]
            mem = {i, int(j)}
            for a in range(q):
                mem.add(index[normalize(tuple((x[k] + a * y[k]) % q for k in range(7)), q)])
            assert len(mem) == q + 1
            key = frozenset(mem)
            if key not in lines:
                lines[key] = len(out)
                out.append(sorted(mem))
    assert len(out) == N
    return N, out


def main():
    kind, q, j, m, mode = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    seed = int(sys.argv[sys.argv.index("--seed") + 1]) if "--seed" in sys.argv else 1
    D = int(sys.argv[sys.argv.index("--D") + 1]) if "--D" in sys.argv else (5 if kind == "gq" else 7)
    P, lines = {"gq": wq, "gh": gh, "pg": pg}[kind](q)
    rng = random.Random(seed)
    w = sys.stdout.write
    n0 = 2 * P
    w(f"# {kind}({q}) incidence ({n0} vertices, degree {q + 1}) + {j} random perfect matchings (seed {seed}); Z_{m}\n")
    if mode == "sol":
        w(f"lift D {D} Delta {q + 1 + j} k {n0} N {m} n {n0 * m} cost -1\n")
        w(f"group cyc {m}\n")
    w(f"k {n0}\n")
    for li, L in enumerate(lines):
        for p in L:
            w(f"e {p} {P + li}" + (" = 0\n" if mode in ("sol", "free") else "\n"))
    for t in range(1, j + 1):
        perm = list(range(P))
        rng.shuffle(perm)
        for p in range(P):
            if mode == "sol":
                w(f"e {p} {P + perm[p]} = {t % m}\n")
            else:
                w(f"e {p} {P + perm[p]}\n")


if __name__ == "__main__":
    main()
