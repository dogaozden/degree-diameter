"""Group specs (lift.c grammar) of a given order, from the families lift.c implements.

Usage: python3 groups.py N [--max M] [--rich]      prints one spec per line (--rich: also products of two
       non-abelian factors, e.g. meta 7 3 2 x meta 5 4 2, psl 5 x meta 7 3 2)
Families: cyc N; cyc a x cyc b (a | b, a > 1); meta m k r (Z_m x|_r Z_k, r != 1, one r per cyclic subgroup
<r> generated with a unit exponent); meta m k r x cyc c; sl/psl/pgl p (x cyc c); with --rich also
aff p a b c d k (Z_p^2 x|_M Z_k, incl. Heisenberg groups) x cyc c, and products of two non-abelian factors.
Isomorphic duplicates across families are possible (e.g. meta with r of small order); lift.c does not care.
"""
import math
import sys


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def is_prime(p):
    return p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))


def metas(m, k):
    """canonical r != 1 with r^k = 1 mod m"""
    out = set()
    if m < 3:
        return []
    for r in range(2, m):
        if math.gcd(r, m) != 1 or pow(r, k, m) != 1:
            continue
        canon = min(pow(r, j, m) for j in range(1, k + 1) if math.gcd(j, k) == 1)
        out.add(canon)
    return sorted(out)


def matrix_orders(limit):
    res = []
    for p in range(2, 200):
        if not is_prime(p):
            continue
        sl = p * (p * p - 1)
        if sl > limit:
            break
        res.append(("sl", p, sl))
        if p > 2:
            res.append(("psl", p, sl // 2))
        res.append(("pgl", p, sl))
    return res


def specs(N):
    out = [f"cyc {N}"]
    for a in divisors(N):
        b = N // a
        if 1 < a <= b and b % a == 0:
            out.append(f"cyc {a} x cyc {b}")
    for c in divisors(N):
        M = N // c
        for m in divisors(M):
            k = M // m
            if k < 2:
                continue
            for r in metas(m, k):
                out.append(f"meta {m} {k} {r}" + (f" x cyc {c}" if c > 1 else ""))
    for kind, p, o in matrix_orders(N):
        if N % o == 0:
            c = N // o
            out.append(f"{kind} {p}" + (f" x cyc {c}" if c > 1 else ""))
    return out


def nonabelian_small(limit):
    """(spec, order) of small non-abelian factors: metacyclic with r != 1 (k prime power free of repeats) and matrix groups"""
    out = []
    for o in range(6, limit + 1):
        for m in divisors(o):
            k = o // m
            if k < 2:
                continue
            for r in metas(m, k):
                if pow(r, k, m) == 1 and math.gcd(m, k) == 1:   # split extensions with coprime orders: Frobenius-like
                    out.append((f"meta {m} {k} {r}", o))
    out += [(f"{kind} {p}", o) for kind, p, o in matrix_orders(limit)]
    return out


def mat_order(M, p, cap):
    (a, b), (c, d) = M
    A = M
    for o in range(1, cap + 1):
        if A == ((1, 0), (0, 1)):
            return o
        (e, f), (g, h) = A
        A = (((e * a + f * c) % p, (e * b + f * d) % p), ((g * a + h * c) % p, (g * b + h * d) % p))
    return None


def affs(p, k):
    """aff p a b c d k: Z_p^2 x|_M Z_k, one M per conjugacy class of GL(2,p) with M^k = I and M != I
    (rational canonical forms: scalars and companion matrices), up to M -> M^j with gcd(j, k) = 1"""
    out, seen = [], set()
    cands = [((l, 0), (0, l)) for l in range(2, p)]
    cands += [((0, (-dd) % p), (1, t)) for t in range(p) for dd in range(1, p)]
    for M in cands:
        o = mat_order(M, p, k)
        if o is None or k % o or o == 1:
            continue
        # class key of <M> under unit powers: char polys (trace, det) of M^j, gcd(j, k) = 1
        keys = []
        A = ((1, 0), (0, 1))
        pw = [A]
        for _ in range(k):
            (e, f), (g, h) = pw[-1]
            (a, b), (c, d) = M
            pw.append((((e * a + f * c) % p, (e * b + f * d) % p), ((g * a + h * c) % p, (g * b + h * d) % p)))
        for j in range(1, k + 1):
            if math.gcd(j, k) == 1:
                (e, f), (g, h) = pw[j]
                scalar = f == 0 and g == 0 and e == h
                keys.append((scalar, (e + h) % p, (e * h - f * g) % p))
        key = min(keys)
        if key in seen:
            continue
        seen.add(key)
        (a, b), (c, d) = M
        out.append(f"aff {p} {a} {b} {c} {d} {k}")
    return out


def affs_ring(m, k):
    """aff m a b c d k for a composite modulus m: companion matrices [[0,-d],[1,t]] with gcd(d, m) = 1 and
    M^k = I mod m, M != I, one per <M> up to unit powers (keyed by (trace, det) of the powers)"""
    out, seen = [], set()
    for t in range(m):
        for dd in range(1, m):
            if math.gcd(dd, m) != 1:
                continue
            M = ((0, (-dd) % m), (1, t))
            o = mat_order(M, m, k)
            if o is None or k % o or o == 1:
                continue
            pw = [((1, 0), (0, 1))]
            for _ in range(k):
                (e, f), (g, h) = pw[-1]
                pw.append((((e * 0 + f * 1) % m, (e * ((-dd) % m) + f * t) % m), ((g * 0 + h * 1) % m, (g * ((-dd) % m) + h * t) % m)))
            key = min(((pw[j][0][0] + pw[j][1][1]) % m, (pw[j][0][0] * pw[j][1][1] - pw[j][0][1] * pw[j][1][0]) % m)
                      for j in range(1, k + 1) if math.gcd(j, k) == 1)
            if key in seen:
                continue
            seen.add(key)
            out.append(f"aff {m} 0 {(-dd) % m} 1 {t} {k}")
    return out


def affs3(p, k):
    """aff3 p M k with M the companion matrix of x^3 + c2 x^2 + c1 x + c0 (c0 != 0), M^k = I, M != I,
    one per <M> up to unit powers (keyed by the companion data of the powers' char. polys is too costly; we key by
    the set of matrices in <M> generated by unit powers)"""
    out, seen = [], set()
    for c0 in range(1, p):
        for c1 in range(p):
            for c2 in range(p):
                M = ((0, 0, (-c0) % p), (1, 0, (-c1) % p), (0, 1, (-c2) % p))
                pw = [tuple(tuple(int(r == c) for c in range(3)) for r in range(3))]
                for _ in range(k):
                    A = pw[-1]
                    pw.append(tuple(tuple(sum(A[r][u] * M[u][c] for u in range(3)) % p for c in range(3)) for r in range(3)))
                if pw[k] != pw[0] or pw[1] == pw[0]:
                    continue
                key = frozenset(pw[j] for j in range(1, k + 1) if math.gcd(j, k) == 1)
                if key in seen:
                    continue
                seen.add(key)
                out.append(f"aff3 {p} " + " ".join(str(x) for row in M for x in row) + f" {k}")
    return out


def aff_specs(N):
    out = []
    for m in range(4, 13):   # composite moduli
        if is_prime(m) or N % (m * m):
            continue
        rest = N // (m * m)
        for k in divisors(rest):
            if k >= 2:
                c = rest // k
                out += [s + (f" x cyc {c}" if c > 1 else "") for s in affs_ring(m, k)]
    for p in (2, 3):   # three-dimensional: Z_p^3 x| Z_k
        if N % (p ** 3) == 0:
            rest = N // p ** 3
            for k in divisors(rest):
                if k >= 2:
                    c = rest // k
                    out += [s + (f" x cyc {c}" if c > 1 else "") for s in affs3(p, k)]
    for p in range(2, int(N ** 0.5) + 1):
        if not is_prime(p) or N % (p * p):
            continue
        rest = N // (p * p)
        for k in divisors(rest):
            if k < 2:
                continue
            c = rest // k
            out += [s + (f" x cyc {c}" if c > 1 else "") for s in affs(p, k)]
    return out


def specs_rich(N, maxfactor=400):
    """specs(N) plus Z_p^2 x| Z_k (times cyclic) and direct products of two non-abelian factors (times cyclic)"""
    out = specs(N) + aff_specs(N)
    fac = nonabelian_small(min(maxfactor, N // 6))
    seen = set()
    for i, (s1, o1) in enumerate(fac):
        for s2, o2 in fac[i:]:
            if N % (o1 * o2):
                continue
            c = N // (o1 * o2)
            spec = f"{s1} x {s2}" + (f" x cyc {c}" if c > 1 else "")
            if spec not in seen:
                seen.add(spec)
                out.append(spec)
    return out


if __name__ == "__main__":
    N = int(sys.argv[1])
    mx = int(sys.argv[sys.argv.index("--max") + 1]) if "--max" in sys.argv else None
    s = specs_rich(N) if "--rich" in sys.argv else specs(N)
    print("\n".join(s[:mx] if mx else s))
