"""Group specs (lift.c grammar) of a given order, from the families lift.c implements.

Usage: python3 groups.py N [--max M]       prints one spec per line
Families: cyc N; cyc a x cyc b (a | b, a > 1); meta m k r (Z_m x|_r Z_k, r != 1, one r per cyclic subgroup
<r> generated with a unit exponent); meta m k r x cyc c; sl/psl/pgl p (x cyc c).
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


if __name__ == "__main__":
    N = int(sys.argv[1])
    mx = int(sys.argv[sys.argv.index("--max") + 1]) if "--max" in sys.argv else None
    s = specs(N)
    print("\n".join(s[:mx] if mx else s))
