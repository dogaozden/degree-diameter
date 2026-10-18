"""Singer difference set for PG(2,q), q prime: points Z_n (n = q^2+q+1), lines D + j."""
import itertools


def singer_plane(q):
    n = q * q + q + 1
    # find irreducible monic cubic x^3 + a x^2 + b x + c with x primitive in GF(q^3)
    for a, b, c in itertools.product(range(q), repeat=3):
        if c == 0 or any((r ** 3 + a * r * r + b * r + c) % q == 0 for r in range(q)):
            continue
        def mul(u, v):
            w = [0] * 5
            for i in range(3):
                for j in range(3):
                    w[i + j] += u[i] * v[j]
            for d in (4, 3):
                t = w[d]; w[d] = 0
                w[d - 1] -= a * t; w[d - 2] -= b * t; w[d - 3] -= c * t
            return [x % q for x in w[:3]]
        x = [0, 1, 0]; e = [1, 0, 0]; pw = []
        for i in range(q ** 3 - 1):
            pw.append(e); e = mul(e, x)
        if e != [1, 0, 0] or any(pw[i] == [1, 0, 0] for i in range(1, q ** 3 - 1)):
            continue
        # x primitive. Points: x^i for i mod n. Line: {i : coefficient of x^2 ... } use trace-like functional: third coord = 0
        D = sorted({i % n for i in range(q ** 3 - 1) if pw[i][2] == 0})
        assert len(D) == q + 1
        diffs = {(u - v) % n for u in D for v in D if u != v}
        assert len(diffs) == n - 1
        lines = [frozenset((d + j) % n for d in D) for j in range(n)]
        return list(range(n)), lines
    raise ValueError


if __name__ == '__main__':
    pts, L = singer_plane(13); print(len(pts), len(L), sorted(L[0]))
