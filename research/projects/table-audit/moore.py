"""Moore-bound cells of the bipartite table: bipartite Moore graphs as incidence graphs of generalized polygons.

  D = 3: incidence graph of the projective plane PG(2,q)              n = 2(q^2+q+1)
  D = 4: incidence graph of the symplectic quadrangle W(q), GQ(q,q)   n = 2(q+1)(q^2+1)
  D = 6: incidence graph of the split Cayley hexagon H(q)             n = 2(q+1)(q^4+q^2+1)  (see hexq.py below)
Degree is q+1 = Delta. Each graph is an edge list: first line n, then "u v" per edge; points are 0..N-1, lines N..2N-1.

Usage: python3 moore.py D q OUT.edges      (D = 3 or 4; for D = 6 the lab's research/evenq/hexq.py writes the same format)
Checked afterwards with research/lifts/coordinator_check/apsp.c (see check_moore.sh).
"""
import itertools
import sys


def _irreducible(p, k):
    """Coefficients (c0..c_{k-1}) of a monic irreducible x^k + ... over GF(p), by brute force (k <= 3 here)."""
    for coeffs in itertools.product(range(p), repeat=k):
        if k == 1:
            return coeffs
        # k = 2 or 3: reducible iff it has a root in GF(p)
        if all((sum(c * x ** i for i, c in enumerate(coeffs)) + x ** k) % p for x in range(p)):
            return coeffs
    raise ValueError("no irreducible polynomial")


def field(q):
    """(ADD, MUL, NEG) tables of GF(q) for q = p^k, q <= 9. Elements are ints 0..q-1 (base-p digits)."""
    p = next(r for r in range(2, q + 1) if q % r == 0)
    k = 0
    t = q
    while t > 1:
        assert t % p == 0
        t //= p
        k += 1
    modpoly = _irreducible(p, k) if k > 1 else None

    def digits(x):
        return [(x // p ** i) % p for i in range(k)]

    def undigits(d):
        return sum(c * p ** i for i, c in enumerate(d))

    def mulpoly(a, b):
        r = [0] * (2 * k - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
        for d in range(2 * k - 2, k - 1, -1):  # x^k = -(modpoly), applied from the top degree down
            c = r[d]
            r[d] = 0
            for i in range(k):
                r[d - k + i] = (r[d - k + i] - c * modpoly[i]) % p
        return r[:k]

    ADD = [[undigits([(x + y) % p for x, y in zip(digits(a), digits(b))]) for b in range(q)] for a in range(q)]
    MUL = [[undigits(mulpoly(digits(a), digits(b))) if k > 1 else (a * b) % p for b in range(q)] for a in range(q)]
    NEG = [undigits([(-x) % p for x in digits(a)]) for a in range(q)]
    for a in range(1, q):
        assert any(MUL[a][b] == 1 for b in range(q)), "not a field: polynomial is reducible"
    return ADD, MUL, NEG


def normalized_points(q, n):
    """Projective points of PG(n-1, q) as tuples whose first nonzero coordinate is 1."""
    return [v for v in itertools.product(range(q), repeat=n) if next((x for x in v if x), 0) == 1]


def write(n, E, path):
    with open(path, "w") as f:
        f.write(f"{n}\n")
        f.writelines(f"{u} {v}\n" for u, v in E)


def pg2(q, path):
    ADD, MUL, NEG = field(q)
    P = normalized_points(q, 3)
    N = len(P)

    def dot(x, y):
        s = 0
        for a, b in zip(x, y):
            s = ADD[s][MUL[a][b]]
        return s

    E = [(i, N + j) for j, L in enumerate(P) for i, x in enumerate(P) if dot(x, L) == 0]
    write(2 * N, E, path)
    return 2 * N, len(E)


def w_q(q, path):
    """W(q): points of PG(3,q); lines = totally isotropic lines of B(x,y) = x0y1 - x1y0 + x2y3 - x3y2."""
    ADD, MUL, NEG = field(q)
    P = normalized_points(q, 4)
    idx = {v: i for i, v in enumerate(P)}
    N = len(P)

    def B(x, y):
        s = 0
        for a in (MUL[x[0]][y[1]], NEG[MUL[x[1]][y[0]]], MUL[x[2]][y[3]], NEG[MUL[x[3]][y[2]]]):
            s = ADD[s][a]
        return s

    def normal(v):
        nz = next(x for x in v if x)
        inv = next(b for b in range(q) if MUL[nz][b] == 1)
        return tuple(MUL[inv][x] for x in v)

    lines = set()
    for i, x in enumerate(P):
        for j in range(i + 1, N):
            y = P[j]
            if B(x, y) != 0:
                continue
            # the q+1 points of span(x, y): x + t y for t in GF(q), and y
            pts = set()
            for t in range(q):
                v = tuple(ADD[xi][MUL[t][yi]] for xi, yi in zip(x, y))
                if any(v):
                    pts.add(idx[normal(v)])
            pts.add(j)
            lines.add(frozenset(pts))
    lines = sorted(sorted(L) for L in lines)
    assert len(lines) == (q + 1) * (q * q + 1), len(lines)
    assert all(len(L) == q + 1 for L in lines)
    E = [(p, N + j) for j, L in enumerate(lines) for p in L]
    write(2 * N, E, path)
    return 2 * N, len(E)


if __name__ == "__main__":
    D, q, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    if D == 3:
        print("PG(2,%d) incidence graph (n, edges):" % q, pg2(q, out))
    elif D == 4:
        print("W(%d) incidence graph (n, edges):" % q, w_q(q, out))
    else:
        sys.exit("D must be 3 or 4 here; for D = 6 use research/evenq/hexq.py")
